/-!
# HAT's Read Committed algorithm: a G1c witness and a timestamp patch

Bailis et al., "Highly Available Transactions: Virtues and Limitations"
(VLDB 2014; arXiv 1302.0309), §5.1.1, claim that Read Committed, "Adya's PL-2
… formalized by prohibiting Adya's G1{a-c}", is achieved by the Read
Uncommitted mechanism ("marking each of a transaction's writes with the same
timestamp (unique across transactions; e.g., combining a client's ID with a
sequence number) and applying a 'last writer wins' conflict reconciliation
policy at each replica") together with buffering ("clients can buffer their
writes until they commit").

This file models that algorithm as App. B's pseudocode describes it,
restricted to Read Committed (no `pending`, `good`, or `required`), with any
number of clients, items and replicas:

* `BEGIN TRANSACTION`: `cur_txn = new txn ID // (e.g., clientID+logicalClock)`.
  A timestamp is the pair `(clock, clientID)`, ordered lexicographically
  (`tsLt`); this is the order of the paper's example format "the last 4
  digits are reserved for client ID".  The initial version has timestamp
  `(0,0)` and clocks start at `1`.
* `PUT(k,v)`: `write_buffer.put(k,v)`; a second write of `k` overwrites the
  buffered one, so only a transaction's final write of `k` is ever sent.
* `GET(k)`: the client's own buffered write if any; otherwise the chosen
  replica returns its highest-timestamped write of `k` (`ts_required = ⊥`).
* `COMMIT`: each buffered write, stamped with the transaction's timestamp, is
  sent to some replica of its key (`dest`), which adds it to its store.
  Keeping every write and answering with the highest timestamp is last writer
  wins.  `ABORT` clears the buffer.
* Anti-entropy (`sync r r'`): replica `r'` receives every write `r` holds.

Two timestamp disciplines (`Disc`):

* `atBegin`, the paper's: the timestamp is fixed at `BEGIN`;
* `lamport`, the patch: the client keeps a logical clock that each read
  advances past the returned version (`clock := max clock (v.clock + 1)`),
  and the timestamp `(clock, clientID)` is chosen at `COMMIT`.  It is still
  computed locally from versions the client has received, and writes are
  buffered until commit anyway, so no coordination or extra round trip is
  added.

The history (Adya): the committed transactions are the commit records, each
identified by its timestamp; the version order of each item is the
last-writer-wins (timestamp) order over its committed installers, with the
initial version first; reads-from is what `GET` returned (reads of one's own
buffered writes are not dependencies).  `ww a b`: `b` installs the next
version after `a`'s; `wr a b`: committed `b` read `a`'s version.  G0 is a
cycle of `ww` edges, G1a a committed read of a version no committed
transaction installed, G1c a cycle of `ww`/`wr` edges.  G1b (reading an
intermediate version) cannot be expressed: buffering means only final writes
are ever sent, so every stored version is final.

Results:

* `g1c_witness`: under `atBegin`, one item, one replica and two transactions
  produce G1c (and no G1a).
* `atBegin_noG1a_noG0`, `lamport_pl2`: under either discipline no history has
  G1a or G0; under `lamport` no history has G1c, and committed timestamps are
  unique and differ from the initial version's.  So the patched algorithm
  provides PL-2 for every schedule.
-/

namespace CC
namespace HATRC

/-- Timestamps `(clock, clientID)`, ordered lexicographically. -/
abbrev Ts := Nat × Nat

def tsLt (a b : Ts) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

instance (a b : Ts) : Decidable (tsLt a b) := by unfold tsLt; infer_instance

theorem tsLt_trans {a b c : Ts} (h₁ : tsLt a b) (h₂ : tsLt b c) : tsLt a c := by
  unfold tsLt at *; omega

theorem tsLt_irrefl (a : Ts) : ¬ tsLt a a := by unfold tsLt; omega

/-- The initial version's timestamp. -/
def tsInit : Ts := (0, 0)

/-- A stored write: key and timestamp. -/
structure W where
  key : Nat
  ts : Ts
  deriving DecidableEq

def tsMax (a b : Ts) : Ts := if tsLt a b then b else a

/-- Replica `GET(k)` with `ts_required = ⊥`: the highest timestamp among its
writes of `k`, or the initial version. -/
def get (store : List W) (k : Nat) : Ts :=
  (store.filter (fun w => w.key == k)).foldl (fun m w => tsMax m w.ts) tsInit

theorem foldl_tsMax (l : List W) (acc : Ts) :
    l.foldl (fun m w => tsMax m w.ts) acc = acc ∨
      ∃ w ∈ l, w.ts = l.foldl (fun m w => tsMax m w.ts) acc := by
  induction l generalizing acc with
  | nil => exact Or.inl rfl
  | cons w l ih =>
    simp only [List.foldl_cons]
    rcases ih (tsMax acc w.ts) with h | ⟨w', hw', h⟩
    · rw [h]; unfold tsMax; split
      · exact Or.inr ⟨w, List.mem_cons_self .., rfl⟩
      · exact Or.inl rfl
    · exact Or.inr ⟨w', List.mem_cons_of_mem _ hw', h⟩

/-- `GET` returns the initial version or a version the replica holds. -/
theorem get_mem (store : List W) (k : Nat) :
    get store k = tsInit ∨ ∃ w ∈ store, w.key = k ∧ w.ts = get store k := by
  rcases foldl_tsMax (store.filter (fun w => w.key == k)) tsInit with h | ⟨w, hw, h⟩
  · exact Or.inl h
  · rw [List.mem_filter] at hw
    exact Or.inr ⟨w, hw.1, by simpa using hw.2, h⟩

/-- Client state: logical clock, current transaction number, whether a
transaction is active, the timestamp fixed at `BEGIN` (`atBegin`), and the
buffered keys. -/
structure Client where
  clock : Nat
  seq : Nat
  active : Bool
  bts : Ts
  buf : List Nat

inductive Disc where
  | atBegin
  | lamport

inductive Step where
  | begin (c : Nat)
  | read (c k r : Nat)
  | write (c k : Nat)
  | commit (c : Nat) (dest : Nat → Nat)
  | abort (c : Nat)
  | sync (r r' : Nat)

/-- A read of transaction `(c, seq)` of key `key` that returned version `v`. -/
structure Rd where
  c : Nat
  seq : Nat
  key : Nat
  v : Ts
  deriving DecidableEq

/-- The commit of transaction `(c, seq)` with timestamp `ts`, installing `keys`. -/
structure Cm where
  c : Nat
  seq : Nat
  ts : Ts
  keys : List Nat
  deriving DecidableEq

structure St where
  store : Nat → List W
  cl : Nat → Client
  reads : List Rd
  commits : List Cm

def St.init : St := ⟨fun _ => [], fun _ => ⟨1, 0, false, tsInit, []⟩, [], []⟩

def setCl (f : Nat → Client) (c : Nat) (x : Client) : Nat → Client :=
  fun c' => if c' = c then x else f c'

def addW (store : Nat → List W) (r : Nat) (w : W) : Nat → List W :=
  fun r' => if r' = r then store r' ++ [w] else store r'

def commitTs : Disc → Client → Nat → Ts
  | .atBegin, cc, _ => cc.bts
  | .lamport, cc, c => (cc.clock, c)

def step (d : Disc) (s : St) : Step → St
  | .begin c =>
    let cc := s.cl c
    match d with
    | .atBegin =>
      { s with cl := setCl s.cl c ⟨cc.clock + 1, cc.seq + 1, true, (cc.clock, c), []⟩ }
    | .lamport =>
      { s with cl := setCl s.cl c ⟨cc.clock, cc.seq + 1, true, cc.bts, []⟩ }
  | .read c k r =>
    let cc := s.cl c
    if cc.active ∧ k ∉ cc.buf then
      let v := get (s.store r) k
      { s with reads := s.reads ++ [⟨c, cc.seq, k, v⟩],
               cl := match d with
                 | .atBegin => s.cl
                 | .lamport => setCl s.cl c { cc with clock := max cc.clock (v.1 + 1) } }
    else s
  | .write c k =>
    let cc := s.cl c
    if cc.active ∧ k ∉ cc.buf then { s with cl := setCl s.cl c { cc with buf := cc.buf ++ [k] } }
    else s
  | .commit c dest =>
    let cc := s.cl c
    if cc.active then
      let ts := commitTs d cc c
      { s with store := cc.buf.foldl (fun st k => addW st (dest k) ⟨k, ts⟩) s.store,
               commits := s.commits ++ [⟨c, cc.seq, ts, cc.buf⟩],
               cl := setCl s.cl c
                 { cc with active := false, buf := [],
                           clock := match d with | .atBegin => cc.clock | .lamport => cc.clock + 1 } }
    else s
  | .abort c =>
    let cc := s.cl c
    { s with cl := setCl s.cl c { cc with active := false, buf := [] } }
  | .sync r r' =>
    { s with store := fun x => if x = r' then s.store r' ++ s.store r else s.store x }

def run (d : Disc) (l : List Step) : St := l.foldl (step d) St.init

/-! ## Adya's history of a run -/

section History
variable (h : St)

/-- `t` installs a committed version of `k` (`tsInit` is `T_init`). -/
def Installs (k : Nat) (t : Ts) : Prop := t = tsInit ∨ ∃ cm ∈ h.commits, cm.ts = t ∧ k ∈ cm.keys

/-- `x_b` is the next version of `k` after `x_a` (last-writer-wins order). -/
def Next (k : Nat) (a b : Ts) : Prop :=
  Installs h k a ∧ Installs h k b ∧ tsLt a b ∧ ∀ c, Installs h k c → ¬ (tsLt a c ∧ tsLt c b)

def ww (a b : Ts) : Prop := ∃ k, Next h k a b

/-- Committed `b` read the version written by `a`. -/
def wr (a b : Ts) : Prop :=
  a ≠ b ∧ ∃ rd ∈ h.reads, ∃ cm ∈ h.commits, cm.c = rd.c ∧ cm.seq = rd.seq ∧ cm.ts = b ∧ rd.v = a

def dep (a b : Ts) : Prop := ww h a b ∨ wr h a b

def G0 : Prop := ∃ t, Relation.TransGen (ww h) t t
def G1a : Prop :=
  ∃ rd ∈ h.reads, (∃ cm ∈ h.commits, cm.c = rd.c ∧ cm.seq = rd.seq) ∧ ¬ Installs h rd.key rd.v
def G1c : Prop := ∃ t, Relation.TransGen (dep h) t t

end History

theorem no_cycle {R : Ts → Ts → Prop} (hR : ∀ a b, R a b → tsLt a b) {t : Ts}
    (h : Relation.TransGen R t t) : False := by
  have : ∀ {a b}, Relation.TransGen R a b → tsLt a b := by
    intro a b h
    induction h with
    | single h => exact hR _ _ h
    | tail _ h ih => exact tsLt_trans ih (hR _ _ h)
  exact tsLt_irrefl _ (this h)

/-! ## The witness: the paper's discipline produces G1c -/

/-- `T₁` (client 1) and `T₂` (client 2) begin; `T₂` writes `x` (key 0) and
commits to replica 0; `T₁` reads `x` from replica 0, writes `x` and commits. -/
def schedule : List Step :=
  [.begin 1, .begin 2, .write 2 0, .commit 2 (fun _ => 0), .read 1 0 0, .write 1 0,
    .commit 1 (fun _ => 0)]

def wfinal : St := run .atBegin schedule

theorem wfinal_commits : wfinal.commits = [⟨2, 1, (1, 2), [0]⟩, ⟨1, 1, (1, 1), [0]⟩] := by decide
theorem wfinal_reads : wfinal.reads = [⟨1, 1, 0, (1, 2)⟩] := by decide
theorem wfinal_store : get (wfinal.store 0) 0 = (1, 2) := by decide

theorem wfinal_installs (t : Ts) : Installs wfinal 0 t ↔ t = tsInit ∨ t = (1, 2) ∨ t = (1, 1) := by
  unfold Installs; rw [wfinal_commits]; simp [eq_comm]

/-- Under the paper's discipline: both transactions commit with
`ts(T₁) = (1,1) < ts(T₂) = (1,2)`; `T₁`'s read returned `T₂`'s version; the
replica's final value is `T₂`'s.  So `x₁ ≪ x₂` (`ww T₁ T₂`) and `T₁` read
`x₂` (`wr T₂ T₁`): a G1c cycle, with no G1a. -/
theorem g1c_witness :
    wfinal.commits = [⟨2, 1, (1, 2), [0]⟩, ⟨1, 1, (1, 1), [0]⟩] ∧
    wfinal.reads = [⟨1, 1, 0, (1, 2)⟩] ∧ get (wfinal.store 0) 0 = (1, 2) ∧
    ww wfinal (1, 1) (1, 2) ∧ wr wfinal (1, 2) (1, 1) ∧ G1c wfinal ∧ ¬ G1a wfinal := by
  have hww : ww wfinal (1, 1) (1, 2) := by
    refine ⟨0, (wfinal_installs _).2 (by simp), (wfinal_installs _).2 (by simp), by decide, ?_⟩
    intro c hc
    rcases (wfinal_installs c).1 hc with rfl | rfl | rfl <;> decide
  have hwr : wr wfinal (1, 2) (1, 1) := by
    refine ⟨by decide, ?_⟩
    rw [wfinal_reads, wfinal_commits]; decide
  refine ⟨wfinal_commits, wfinal_reads, wfinal_store, hww, hwr,
    ⟨(1, 1), .tail (.single (Or.inl hww)) (Or.inr hwr)⟩, ?_⟩
  rintro ⟨rd, hrd, -, hn⟩
  rw [wfinal_reads] at hrd
  simp only [List.mem_singleton] at hrd
  subst hrd
  exact hn ((wfinal_installs _).2 (by simp))

/-! ## Invariants -/

theorem setCl_eq (f : Nat → Client) (c : Nat) (x : Client) : setCl f c x c = x := by simp [setCl]
theorem setCl_ne (f : Nat → Client) {c c' : Nat} (x : Client) (h : c' ≠ c) : setCl f c x c' = f c' := by
  simp [setCl, h]

/-- Stores and reads hold only committed versions (either discipline). -/
def Inv1 (s : St) : Prop :=
  (∀ r, ∀ w ∈ s.store r, ∃ cm ∈ s.commits, cm.ts = w.ts ∧ w.key ∈ cm.keys) ∧
  (∀ rd ∈ s.reads, rd.v = tsInit ∨ ∃ cm ∈ s.commits, cm.ts = rd.v ∧ rd.key ∈ cm.keys)

theorem foldl_addW (buf : List Nat) (dest : Nat → Nat) (ts : Ts) (st : Nat → List W) (r : Nat) :
    ∀ w ∈ buf.foldl (fun st k => addW st (dest k) ⟨k, ts⟩) st r, w ∈ st r ∨ (w.ts = ts ∧ w.key ∈ buf) := by
  induction buf generalizing st with
  | nil => intro w hw; exact Or.inl hw
  | cons k buf ih =>
    intro w hw
    rcases ih _ w hw with h | ⟨h1, h2⟩
    · simp only [addW] at h
      split at h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · simp only [List.mem_singleton] at h; subst h; exact Or.inr ⟨rfl, List.mem_cons_self ..⟩
      · exact Or.inl h
    · exact Or.inr ⟨h1, List.mem_cons_of_mem _ h2⟩

theorem inv1_step (d : Disc) (s : St) (e : Step) (h : Inv1 s) : Inv1 (step d s e) := by
  obtain ⟨h1, h2⟩ := h
  cases e with
  | begin c => cases d <;> exact ⟨h1, h2⟩
  | read c k r =>
    simp only [step]
    split
    · refine ⟨h1, fun rd hrd => ?_⟩
      rcases List.mem_append.1 hrd with hrd | hrd
      · exact h2 rd hrd
      · simp only [List.mem_singleton] at hrd; subst hrd
        rcases get_mem (s.store r) k with h0 | ⟨w, hw, hk, hts⟩
        · exact Or.inl h0
        · obtain ⟨cm, hcm, e1, e2⟩ := h1 r w hw
          exact Or.inr ⟨cm, hcm, e1.trans hts, hk ▸ e2⟩
    · exact ⟨h1, h2⟩
  | write c k => simp only [step]; split <;> exact ⟨h1, h2⟩
  | commit c dest =>
    simp only [step]
    split
    · refine ⟨fun r w hw => ?_, fun rd hrd => ?_⟩
      · rcases foldl_addW _ _ _ _ _ w hw with hw | ⟨e1, e2⟩
        · obtain ⟨cm, hcm, e⟩ := h1 r w hw
          exact ⟨cm, List.mem_append_left _ hcm, e⟩
        · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), e1.symm, e2⟩
      · rcases h2 rd hrd with h0 | ⟨cm, hcm, e⟩
        · exact Or.inl h0
        · exact Or.inr ⟨cm, List.mem_append_left _ hcm, e⟩
    · exact ⟨h1, h2⟩
  | abort c => exact ⟨h1, h2⟩
  | sync r r' =>
    refine ⟨fun x w hw => ?_, h2⟩
    simp only [step] at hw
    split at hw
    · rcases List.mem_append.1 hw with hw | hw
      · exact h1 _ w hw
      · exact h1 _ w hw
    · exact h1 _ w hw

theorem inv1_run (d : Disc) (l : List Step) : Inv1 (run d l) := by
  have : ∀ s, Inv1 s → Inv1 (l.foldl (step d) s) := by
    induction l with
    | nil => exact fun _ h => h
    | cons e l ih => exact fun s h => ih _ (inv1_step d s e h)
  exact this _ ⟨fun _ _ h => (nomatch h), fun _ h => (nomatch h)⟩

/-- Invariants of the patched discipline. -/
def Inv2 (s : St) : Prop :=
  (∀ rd ∈ s.reads, ∀ cm ∈ s.commits, cm.c = rd.c → cm.seq = rd.seq → tsLt rd.v cm.ts) ∧
  (∀ rd ∈ s.reads, (s.cl rd.c).seq = rd.seq → rd.v.1 < (s.cl rd.c).clock) ∧
  (∀ rd ∈ s.reads, rd.seq ≤ (s.cl rd.c).seq) ∧
  (∀ c, (s.cl c).active = true → ∀ cm ∈ s.commits, cm.c = c → cm.seq ≠ (s.cl c).seq) ∧
  (∀ cm ∈ s.commits, cm.seq ≤ (s.cl cm.c).seq) ∧
  (∀ cm ∈ s.commits, cm.ts.2 = cm.c ∧ cm.ts.1 < (s.cl cm.c).clock ∧ 1 ≤ cm.ts.1) ∧
  (s.commits.map (·.ts)).Nodup ∧
  (∀ c, 1 ≤ (s.cl c).clock)

@[simp] theorem setCl_apply (f : Nat → Client) (c : Nat) (x : Client) (c' : Nat) :
    setCl f c x c' = if c' = c then x else f c' := rfl

theorem inv2_step (s : St) (e : Step) (h : Inv2 s) : Inv2 (step .lamport s e) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := h
  cases e with
  | begin c =>
    refine ⟨i1, ?_, ?_, ?_, ?_, ?_, i7, ?_⟩ <;> dsimp only [step]
    · intro rd hrd hs
      have h2 := i2 rd hrd; have h3 := i3 rd hrd
      by_cases hc : rd.c = c
      · simp [hc] at hs h3; omega
      · simp [hc] at hs ⊢; exact h2 hs
    · intro rd hrd
      have h3 := i3 rd hrd
      by_cases hc : rd.c = c
      · simp [hc] at h3 ⊢; omega
      · simp [hc]; exact h3
    · intro c' ha cm hcm hc'
      have h4 := i4 c'; have h5 := i5 cm hcm
      by_cases hc : c' = c
      · subst hc; subst hc'; simp; omega
      · simp [hc] at ha ⊢; exact h4 ha cm hcm hc'
    · intro cm hcm
      have h5 := i5 cm hcm
      by_cases hc : cm.c = c
      · simp [hc] at h5 ⊢; omega
      · simp [hc]; exact h5
    · intro cm hcm
      have h6 := i6 cm hcm
      by_cases hc : cm.c = c
      · simp [hc] at h6 ⊢; omega
      · simp [hc]; exact h6
    · intro c'
      have h8 := i8 c'
      by_cases hc : c' = c
      · subst hc; simp; exact h8
      · simp [hc]; exact h8
  | read c k r =>
    dsimp only [step]
    split
    · next hact =>
      have hact' := hact.1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, i7, ?_⟩ <;> dsimp only
      · intro rd hrd cm hcm e1 e2
        rcases List.mem_append.1 hrd with hrd | hrd
        · exact i1 rd hrd cm hcm e1 e2
        · simp only [List.mem_singleton] at hrd; subst hrd
          exact absurd e2 (i4 c hact' cm hcm e1)
      · intro rd hrd hs
        rcases List.mem_append.1 hrd with hrd | hrd
        · have h2 := i2 rd hrd
          by_cases hc : rd.c = c
          · simp [hc] at hs h2 ⊢; have := h2 hs; omega
          · simp [hc] at hs ⊢; exact h2 hs
        · simp only [List.mem_singleton] at hrd; subst hrd; simp; omega
      · intro rd hrd
        rcases List.mem_append.1 hrd with hrd | hrd
        · have h3 := i3 rd hrd
          by_cases hc : rd.c = c
          · simp [hc] at h3 ⊢; exact h3
          · simp [hc]; exact h3
        · simp only [List.mem_singleton] at hrd; subst hrd; simp
      · intro c' ha cm hcm hc'
        by_cases hc : c' = c
        · subst hc; simp at ha ⊢; exact i4 c' ha cm hcm hc'
        · simp [hc] at ha ⊢; exact i4 c' ha cm hcm hc'
      · intro cm hcm
        have h5 := i5 cm hcm
        by_cases hc : cm.c = c
        · simp [hc] at h5 ⊢; exact h5
        · simp [hc]; exact h5
      · intro cm hcm
        have h6 := i6 cm hcm
        by_cases hc : cm.c = c
        · simp [hc] at h6 ⊢; omega
        · simp [hc]; exact h6
      · intro c'
        have h8 := i8 c'
        by_cases hc : c' = c
        · subst hc; simp; omega
        · simp [hc]; exact h8
    · exact ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
  | write c k =>
    dsimp only [step]
    split
    · refine ⟨i1, ?_, ?_, ?_, ?_, ?_, i7, ?_⟩ <;> dsimp only
      · intro rd hrd hs
        have h2 := i2 rd hrd
        by_cases hc : rd.c = c
        · simp [hc] at hs h2 ⊢; exact h2 hs
        · simp [hc] at hs ⊢; exact h2 hs
      · intro rd hrd
        have h3 := i3 rd hrd
        by_cases hc : rd.c = c
        · simp [hc] at h3 ⊢; exact h3
        · simp [hc]; exact h3
      · intro c' ha cm hcm hc'
        by_cases hc : c' = c
        · subst hc; simp at ha ⊢; exact i4 c' ha cm hcm hc'
        · simp [hc] at ha ⊢; exact i4 c' ha cm hcm hc'
      · intro cm hcm
        have h5 := i5 cm hcm
        by_cases hc : cm.c = c
        · simp [hc] at h5 ⊢; exact h5
        · simp [hc]; exact h5
      · intro cm hcm
        have h6 := i6 cm hcm
        by_cases hc : cm.c = c
        · simp [hc] at h6 ⊢; exact h6
        · simp [hc]; exact h6
      · intro c'
        have h8 := i8 c'
        by_cases hc : c' = c
        · subst hc; simp; exact h8
        · simp [hc]; exact h8
    · exact ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
  | commit c dest =>
    dsimp only [step]
    split
    · next hact =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only [commitTs]
      · intro rd hrd cm hcm e1 e2
        rcases List.mem_append.1 hcm with hcm | hcm
        · exact i1 rd hrd cm hcm e1 e2
        · simp only [List.mem_singleton] at hcm; subst hcm
          simp only at e1 e2
          subst e1
          exact Or.inl (i2 rd hrd e2)
      · intro rd hrd hs
        have h2 := i2 rd hrd
        by_cases hc : rd.c = c
        · simp [hc] at hs h2 ⊢; have := h2 hs; omega
        · simp [hc] at hs ⊢; exact h2 hs
      · intro rd hrd
        have h3 := i3 rd hrd
        by_cases hc : rd.c = c
        · simp [hc] at h3 ⊢; exact h3
        · simp [hc]; exact h3
      · intro c' ha cm hcm hc'
        by_cases hc : c' = c
        · subst hc; simp at ha
        · simp [hc] at ha ⊢
          rcases List.mem_append.1 hcm with hcm | hcm
          · exact i4 c' ha cm hcm hc'
          · simp only [List.mem_singleton] at hcm; subst hcm; exact absurd hc'.symm hc
      · intro cm hcm
        rcases List.mem_append.1 hcm with hcm | hcm
        · have h5 := i5 cm hcm
          by_cases hc : cm.c = c
          · simp [hc] at h5 ⊢; exact h5
          · simp [hc]; exact h5
        · simp only [List.mem_singleton] at hcm; subst hcm; simp
      · intro cm hcm
        rcases List.mem_append.1 hcm with hcm | hcm
        · have h6 := i6 cm hcm
          by_cases hc : cm.c = c
          · simp [hc] at h6 ⊢; omega
          · simp [hc]; exact h6
        · simp only [List.mem_singleton] at hcm; subst hcm; have := i8 c; simp; omega
      · rw [List.map_append, List.nodup_append]
        refine ⟨i7, by simp, ?_⟩
        intro a ha b hb
        simp only [List.mem_map, List.mem_singleton] at ha hb
        obtain ⟨cm, hcm, rfl⟩ := ha
        obtain ⟨_, rfl, rfl⟩ := hb
        intro e
        obtain ⟨h2, h3, -⟩ := i6 cm hcm
        have e2 : cm.c = c := h2.symm.trans (congrArg Prod.snd e)
        have e1 : cm.ts.1 = (s.cl c).clock := congrArg Prod.fst e
        rw [e2] at h3; omega
      · intro c'
        have h8 := i8 c'
        by_cases hc : c' = c
        · subst hc; simp <;> omega
        · simp [hc]; exact h8
    · exact ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
  | abort c =>
    refine ⟨i1, ?_, ?_, ?_, ?_, ?_, i7, ?_⟩ <;> dsimp only [step]
    · intro rd hrd hs
      have h2 := i2 rd hrd
      by_cases hc : rd.c = c
      · simp [hc] at hs h2 ⊢; exact h2 hs
      · simp [hc] at hs ⊢; exact h2 hs
    · intro rd hrd
      have h3 := i3 rd hrd
      by_cases hc : rd.c = c
      · simp [hc] at h3 ⊢; exact h3
      · simp [hc]; exact h3
    · intro c' ha cm hcm hc'
      by_cases hc : c' = c
      · subst hc; simp at ha
      · simp [hc] at ha ⊢; exact i4 c' ha cm hcm hc'
    · intro cm hcm
      have h5 := i5 cm hcm
      by_cases hc : cm.c = c
      · simp [hc] at h5 ⊢; exact h5
      · simp [hc]; exact h5
    · intro cm hcm
      have h6 := i6 cm hcm
      by_cases hc : cm.c = c
      · simp [hc] at h6 ⊢; exact h6
      · simp [hc]; exact h6
    · intro c'
      have h8 := i8 c'
      by_cases hc : c' = c
      · subst hc; simp; exact h8
      · simp [hc]; exact h8
  | sync r r' => exact ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩


theorem inv2_run (l : List Step) : Inv2 (run .lamport l) := by
  have : ∀ s, Inv2 s → Inv2 (l.foldl (step .lamport) s) := by
    induction l with
    | nil => exact fun _ h => h
    | cons e l ih => exact fun s h => ih _ (inv2_step s e h)
  refine this _ ⟨fun _ h => (nomatch h), fun _ h => (nomatch h), fun _ h => (nomatch h),
    fun _ _ _ h => (nomatch h), fun _ h => (nomatch h), fun _ h => (nomatch h), List.nodup_nil,
    fun _ => Nat.le_refl 1⟩

/-! ## Results -/

theorem ww_lt {h : St} {a b : Ts} (e : ww h a b) : tsLt a b := let ⟨_, _, _, hl, _⟩ := e; hl

/-- Under either discipline, no run has G1a or G0: reads return only
committed versions (buffering), and write-dependencies follow timestamps
(last writer wins).  This is the paper's Read Uncommitted and the dirty-read
half of its Read Committed argument. -/
theorem noG1a_noG0 (d : Disc) (l : List Step) : ¬ G1a (run d l) ∧ ¬ G0 (run d l) := by
  obtain ⟨_, h2⟩ := inv1_run d l
  refine ⟨fun ⟨rd, hrd, _, hn⟩ => hn (h2 rd hrd), fun ⟨t, ht⟩ => no_cycle (fun _ _ e => ww_lt e) ht⟩

/-- **The patch.**  With Lamport timestamps chosen at commit, every run of
the algorithm (any clients, items, replicas, anti-entropy and schedule)
yields a history with distinct committed timestamps, none equal to the
initial version's, and no G1a, G0 or G1c: it is PL-2 (G1b cannot arise, see
the module docstring). -/
theorem lamport_pl2 (l : List Step) :
    ((run .lamport l).commits.map (·.ts)).Nodup ∧ (∀ cm ∈ (run .lamport l).commits, cm.ts ≠ tsInit) ∧
      ¬ G1a (run .lamport l) ∧ ¬ G0 (run .lamport l) ∧ ¬ G1c (run .lamport l) := by
  obtain ⟨i1, -, -, -, -, i6, i7, -⟩ := inv2_run l
  obtain ⟨n1, n0⟩ := noG1a_noG0 .lamport l
  refine ⟨i7, fun cm hcm e => ?_, n1, n0, fun ⟨t, ht⟩ => no_cycle ?_ ht⟩
  · have := (i6 cm hcm).2.2; rw [e] at this; exact absurd this (by decide)
  · rintro a b (e | ⟨-, rd, hrd, cm, hcm, e1, e2, rfl, rfl⟩)
    · exact ww_lt e
    · exact i1 rd hrd cm hcm e1 e2

end HATRC
end CC
