import CoordCriterion.Instances.HATRC
import CoordCriterion.Instances.InvariantConfluence
import CoordCriterion.CAP.AvailabilityFor

/-!
# Highly available transactions as a specification (Sec. `hat-instance`)

HAT (Bailis et al., VLDB 2014) under its own assumptions, with partial
replication, encoded as a specification with an availability relation, so
that Theorem `thm:complete-cap` (`CAP.complete_cap_for`) decides which
isolation levels stay available.

**Inputs** are event histories with happens-before (`IConf.Hist Ev`, ordered
by downward-closed expansion), as in the induced specifications of §6.5:
events received by servers, with each client's program order and each
replica's arrival order.  Events (`Ev`):

* `rd c n k r`: transaction `n` of client `c` reads item `k`, received by
  replica `r` of `k`;
* `cm c n ts ks`: the client commits transaction `(c,n)` with timestamp `ts`,
  writing the items `ks` (HAT: writes are buffered until commit and every
  transaction commits iff its client requests it, so the outcome is in the
  input);
* `dl c n k r`: replica `r` receives `(c,n)`'s write of `k` (from the client
  at commit, or by anti-entropy).

`WF` is the legality of inputs: one commit per transaction, unique
timestamps different from the initial version's, deliveries after the
commit, reads before the commit, and each replica's events totally ordered.
`Inp lam` adds, when `lam = true`, the **timestamp condition** (`Lamport`): a
transaction's timestamp exceeds that of every version delivered to a replica
before one of its reads there.  Since the read rule returns the highest such
version, this is the paper's "each transaction's timestamp exceeds that of
every version it reads".  The patched client of `Instances/HATRC.lean`
(clock advanced past each read version, timestamp chosen at commit)
guarantees it; the paper's pseudocode does not (`HATRC.g1c_witness`,
`timestamp_condition_needed`).  Of client program order the results use only
that reads precede their commit.

**Outputs** are sets of read answers `read(e, v)` (`Fact`): read event `e`
returned the version with timestamp `v`, ordered by inclusion.  A read event
names its transaction, operation, item and receiving server.

**Permitted** (`spec L`): the answers extend to a complete history of the
input (`CH`: every read returns the initial version or a version another
committed transaction installed) whose Adya phenomena include none that `L`
proscribes.  The version order is last writer wins (timestamp order), so it
is fixed by the input.  Phenomena: `G0`, `G1c`, `G2`, and HAT's Lost Update
(a cycle with an anti-dependency, all edges on one item).  G1a and G1b
cannot occur: every version is a committed transaction's final write.  The
levels are HAT's, item-only (predicate phenomena omitted): `RU` (G0), `RC`
(G0, G1), `SI` (G0, G1, Lost Update; HAT's PMP and OTV are predicate or
observation phenomena not modeled), `RR` (G0, G1, G2-item, which here is G2),
and `SER` (Adya's PL-3, here the same set as `RR`).

**The availability relation** `hatA` is HAT's server rule (App. B `GET` with
`ts_required = ⊥`), evaluated at the read's place in happens-before: answer
with the highest timestamp among the writes of `k` delivered to `r` before
the read, or the initial version.  It answers every read exactly once and
never changes an answer as the input grows.

Results: `hat_rule` (the rule answers every read once and never revises an
answer); `rc_available` (under the timestamp condition, RU and RC satisfy
Lifted Monotonicity for `hatA`, so some system has Availability for `hatA`
and Partition Consistency); `lostUpdate_unavailableP` (for any proscribed
set containing Lost Update, e.g. SI, RR, SER, no availability relation that
answers every read does, using HAT's pair of concurrent read-modify-writes at
two replicas); `timestamp_condition_needed` (without the condition, `hatA`
is not contained in `S_RC`).  `serial_clean` shows every input has a
permitted complete history (the serial history in timestamp order).
-/

namespace CC
namespace HATSpec
open HATRC (Ts tsLt tsInit tsLt_trans tsLt_irrefl no_cycle)
open IConf (Hist St)

/-! ## Events, inputs -/

inductive Ev where
  | rd (c n k r : Nat)
  | cm (c n : Nat) (ts : Ts) (ks : List Nat)
  | dl (c n k r : Nat)
  deriving DecidableEq

/-- The event is received by replica `r`. -/
def AtReplica : Option Ev → Nat → Prop
  | some (.rd _ _ _ r), r' => r = r'
  | some (.dl _ _ _ r), r' => r = r'
  | _, _ => False

/-- Legal inputs. -/
structure WF (h : Hist Ev) : Prop where
  cm_unique : ∀ {e e' c n t t' ks ks'}, h.lab e = some (.cm c n t ks) →
    h.lab e' = some (.cm c n t' ks') → e = e'
  ts_unique : ∀ {e e' c n c' n' t ks ks'}, h.lab e = some (.cm c n t ks) →
    h.lab e' = some (.cm c' n' t ks') → e = e'
  ts_ne : ∀ {e c n t ks}, h.lab e = some (.cm c n t ks) → t ≠ tsInit
  dl_after : ∀ {d c n k r}, h.lab d = some (.dl c n k r) →
    ∃ f t ks, h.lab f = some (.cm c n t ks) ∧ k ∈ ks ∧ h.lt f d
  rd_before : ∀ {e f c n k r t ks}, h.lab e = some (.rd c n k r) →
    h.lab f = some (.cm c n t ks) → h.lt e f
  replica : ∀ {e e' r}, AtReplica (h.lab e) r → AtReplica (h.lab e') r → e ≠ e' →
    h.lt e e' ∨ h.lt e' e

/-- The timestamp condition: a transaction's timestamp exceeds that of every
version delivered to a replica before one of its reads there (so, under the
read rule `A`, every version it reads). -/
def Lamport (h : Hist Ev) : Prop :=
  ∀ {e d f g c n k r c' n' t t' ks ks'}, h.lab e = some (.rd c n k r) →
    h.lab d = some (.dl c' n' k r) → h.lt d e → h.lab f = some (.cm c n t ks) →
    h.lab g = some (.cm c' n' t' ks') → tsLt t' t

/-- Inputs: legal event histories, ordered by downward-closed expansion; with
`lam = true`, satisfying the timestamp condition. -/
abbrev Inp (lam : Bool) := {h : Hist Ev // WF h ∧ (lam = true → Lamport h)}

variable {lam : Bool}

instance : PO (Inp lam) where
  le a b := a.1 ≼ b.1
  refl a := PO.refl a.1
  trans h₁ h₂ := PO.trans h₁ h₂
  antisymm h₁ h₂ := Subtype.ext (PO.antisymm h₁ h₂)

theorem lab_ev {h : Hist Ev} {e : Nat} {x : Ev} (hl : h.lab e = some x) : h.ev e := by
  unfold Hist.ev; rw [hl]; simp

theorem lab_sub {a b : Hist Ev} (hab : a ≼ b) {e : Nat} {x : Ev} (hl : a.lab e = some x) :
    b.lab e = some x := hab.1 e x hl

theorem lab_sup {a b : Hist Ev} (hab : a ≼ b) {e : Nat} {x : Ev} (he : a.ev e)
    (hl : b.lab e = some x) : a.lab e = some x := by
  rw [Hist.le_lab hab he]; exact hl

theorem lt_sub {a b : Hist Ev} (hab : a ≼ b) {x y : Nat} (h : a.lt x y) : b.lt x y :=
  ((hab.2 x y).1 h).1

theorem lt_sup {a b : Hist Ev} (hab : a ≼ b) {x y : Nat} (h : b.lt x y) (hy : a.ev y) : a.lt x y :=
  (hab.2 x y).2 ⟨h, hy⟩

/-- Inputs are closed under the order: a downward-closed sub-history of a
legal input is legal. -/
theorem wf_down {a b : Hist Ev} (hab : a ≼ b) (hb : WF b) : WF a where
  cm_unique h h' := hb.cm_unique (lab_sub hab h) (lab_sub hab h')
  ts_unique h h' := hb.ts_unique (lab_sub hab h) (lab_sub hab h')
  ts_ne h := hb.ts_ne (lab_sub hab h)
  dl_after {d c n k r} h := by
    obtain ⟨f, t, ks, hf, hk, hlt⟩ := hb.dl_after (lab_sub hab h)
    have hlt' := lt_sup hab hlt (lab_ev h)
    exact ⟨f, t, ks, lab_sup hab (Hist.ev_of_lt_left hlt') hf, hk, hlt'⟩
  rd_before h h' := lt_sup hab (hb.rd_before (lab_sub hab h) (lab_sub hab h')) (lab_ev h')
  replica {e e' r} h h' hne := by
    have ee : a.ev e := by
      unfold Hist.ev; intro hn; rw [hn] at h; exact h
    have ee' : a.ev e' := by
      unfold Hist.ev; intro hn; rw [hn] at h'; exact h'
    rw [Hist.le_lab hab ee] at h; rw [Hist.le_lab hab ee'] at h'
    rcases hb.replica h h' hne with hl | hl
    · exact Or.inl (lt_sup hab hl ee')
    · exact Or.inr (lt_sup hab hl ee)

theorem lamport_down {a b : Hist Ev} (hab : a ≼ b) (hb : Lamport b) : Lamport a :=
  fun h hd hlt hf hg => hb (lab_sub hab h) (lab_sub hab hd) (lt_sub hab hlt)
    (lab_sub hab hf) (lab_sub hab hg)

/-! ## Outputs, complete histories, phenomena -/

/-- `read(e, v)`: read event `e` returned the version with timestamp `v`. -/
inductive Fact where
  | read (e : Nat) (v : Ts)

def IsRd (j : Inp lam) (e : Nat) : Prop := ∃ c n k r, j.1.lab e = some (.rd c n k r)

/-- A version of `k` that transaction `(c,n)` may read: the initial one, or
one installed by another committed transaction. -/
def Ver (j : Inp lam) (c n k : Nat) (v : Ts) : Prop :=
  v = tsInit ∨ ∃ f c' n' ks, j.1.lab f = some (.cm c' n' v ks) ∧ k ∈ ks ∧ (c', n') ≠ (c, n)

/-- A complete history of the input: every read returns a version. -/
structure CH (j : Inp lam) where
  ans : Nat → Ts
  ok : ∀ e c n k r, j.1.lab e = some (.rd c n k r) → Ver j c n k (ans e)

def CH.facts {j : Inp lam} (H : CH j) : St Fact
  | .read e v => IsRd j e ∧ H.ans e = v

section Phen
variable (j : Inp lam)

/-- `t` installs a version of `k` (`tsInit` is `T_init`). -/
def Inst (k : Nat) (t : Ts) : Prop :=
  t = tsInit ∨ ∃ f c n ks, j.1.lab f = some (.cm c n t ks) ∧ k ∈ ks

/-- `(c,n)` commits with timestamp `t`. -/
def CTs (c n : Nat) (t : Ts) : Prop := ∃ f ks, j.1.lab f = some (.cm c n t ks)

/-- `x_b` is next after `x_a` in the last-writer-wins version order of `k`. -/
def Next (k : Nat) (a b : Ts) : Prop :=
  Inst j k a ∧ Inst j k b ∧ tsLt a b ∧ ∀ c, Inst j k c → ¬ (tsLt a c ∧ tsLt c b)

/-- Write-dependency on item `k`. -/
def wwI (k : Nat) (a b : Ts) : Prop := Next j k a b

def G0 : Prop := ∃ t, Relation.TransGen (fun a b => ∃ k, wwI j k a b) t t

variable {j} (H : CH j)
/-- Read-dependency on item `k`: committed `b` read `a`'s version of `k`. -/
def wrI (k : Nat) (a b : Ts) : Prop :=
  a ≠ b ∧ Inst j k a ∧ ∃ e c n r, j.1.lab e = some (.rd c n k r) ∧ CTs j c n b ∧ H.ans e = a
/-- Anti-dependency on item `k`: committed `a` read some version of `k`, and
`b` installs the next one. -/
def rwI (k : Nat) (a b : Ts) : Prop :=
  a ≠ b ∧ ∃ e c n r, j.1.lab e = some (.rd c n k r) ∧ CTs j c n a ∧ Next j k (H.ans e) b

def dep (a b : Ts) : Prop := (∃ k, wwI j k a b) ∨ (∃ k, wrI H k a b)
def dsg (a b : Ts) : Prop := dep H a b ∨ ∃ k, rwI H k a b
def onItem (k : Nat) (a b : Ts) : Prop := wwI j k a b ∨ wrI H k a b ∨ rwI H k a b

def G1c : Prop := ∃ t, Relation.TransGen (dep H) t t
def G2 : Prop := ∃ a b, (∃ k, rwI H k a b) ∧ (b = a ∨ Relation.TransGen (dsg H) b a)
/-- HAT's Lost Update: a cycle with an anti-dependency, all edges on one item. -/
def LostUpdate : Prop := ∃ k a b, rwI H k a b ∧ (b = a ∨ Relation.TransGen (onItem H k) b a)

end Phen

/-- HAT's isolation levels (item-only).  Without predicates, Adya's PL-3
(serializability) proscribes the same phenomena as HAT's repeatable read
(G0, G1, G2-item = G2). -/
inductive Level where
  | RU | RC | SI | RR | SER

def Proscribed : Level → (j : Inp lam) → CH j → Prop
  | .RU, j, _ => G0 j
  | .RC, j, H => G0 j ∨ G1c H
  | .SI, j, H => G0 j ∨ G1c H ∨ LostUpdate H
  | .RR, j, H => G0 j ∨ G1c H ∨ G2 H
  | .SER, j, H => G0 j ∨ G1c H ∨ G2 H

theorem tg_mono {R R' : Ts → Ts → Prop} (h : ∀ a b, R a b → R' a b) {a b : Ts}
    (hab : Relation.TransGen R a b) : Relation.TransGen R' a b := by
  induction hab with
  | single h' => exact .single (h _ _ h')
  | tail _ h' ih => exact .tail ih (h _ _ h')

/-- Lost Update is a G2 cycle. -/
theorem lostUpdate_G2 {j : Inp lam} {H : CH j} (h : LostUpdate H) : G2 H := by
  obtain ⟨k, a, b, hr, hc⟩ := h
  refine ⟨a, b, ⟨k, hr⟩, hc.imp id (tg_mono fun x y e => ?_)⟩
  rcases e with e | e | e
  · exact Or.inl (Or.inl ⟨k, e⟩)
  · exact Or.inl (Or.inr ⟨k, e⟩)
  · exact Or.inr ⟨k, e⟩

/-- Snapshot isolation, repeatable read and serializability proscribe Lost
Update. -/
theorem proscribes_lostUpdate (L : Level) (hL : L = .SI ∨ L = .RR ∨ L = .SER) {j : Inp lam} (H : CH j)
    (h : LostUpdate H) : Proscribed L j H := by
  rcases hL with rfl | rfl | rfl
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inr (lostUpdate_G2 h))
  · exact Or.inr (Or.inr (lostUpdate_G2 h))

/-! ## Timestamps -/

theorem tsLt_total {a b : Ts} (h : a ≠ b) : tsLt a b ∨ tsLt b a := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  unfold tsLt; simp only [ne_eq, Prod.mk.injEq] at h ⊢; omega

theorem not_lt_init (v : Ts) : ¬ tsLt v tsInit := by unfold tsLt tsInit; simp

theorem init_lt {v : Ts} (h : v ≠ tsInit) : tsLt tsInit v := by
  obtain ⟨a, b⟩ := v; unfold tsLt tsInit at *; simp only [ne_eq, Prod.mk.injEq] at h ⊢; omega

theorem max_unique {P : Ts → Prop} {m m' : Ts} (hm : P m ∧ ∀ v, P v → v = m ∨ tsLt v m)
    (hm' : P m' ∧ ∀ v, P v → v = m' ∨ tsLt v m') : m = m' := by
  rcases hm'.2 m hm.1 with h | h
  · exact h
  · rcases hm.2 m' hm'.1 with h' | h'
    · exact h'.symm
    · exact absurd (tsLt_trans h h') (tsLt_irrefl _)

/-- A nonempty set of timestamps inside a finite list has a maximum. -/
theorem exists_max (L : List Ts) : ∀ (P : Ts → Prop), (∃ x, P x) → (∀ v, P v → v ∈ L) →
    ∃ m, P m ∧ ∀ v, P v → v = m ∨ tsLt v m := by
  induction L with
  | nil => intro P ⟨x, hx⟩ hL; exact absurd (hL x hx) (List.not_mem_nil)
  | cons a L ih =>
    intro P hne hL
    classical
    by_cases hex : ∃ x, P x ∧ x ≠ a
    · obtain ⟨m, ⟨hm, hma⟩, hmax⟩ := ih (fun v => P v ∧ v ≠ a) hex
        (fun v ⟨hv, hva⟩ => (List.mem_cons.1 (hL v hv)).resolve_left hva)
      by_cases hPa : P a
      · rcases tsLt_total hma with hlt | hlt
        · refine ⟨a, hPa, fun v hv => ?_⟩
          by_cases hva : v = a
          · exact Or.inl hva
          · rcases hmax v ⟨hv, hva⟩ with rfl | h
            · exact Or.inr hlt
            · exact Or.inr (tsLt_trans h hlt)
        · refine ⟨m, hm, fun v hv => ?_⟩
          by_cases hva : v = a
          · subst hva; exact Or.inr hlt
          · exact hmax v ⟨hv, hva⟩
      · exact ⟨m, hm, fun v hv => hmax v ⟨hv, fun e => hPa (e ▸ hv)⟩⟩
    · obtain ⟨x, hx⟩ := hne
      have hall : ∀ v, P v → v = a := fun v hv => Classical.byContradiction fun h => hex ⟨v, hv, h⟩
      exact ⟨a, hall x hx ▸ hx, fun v hv => Or.inl (hall v hv)⟩

/-- All commit timestamps of an input, with the initial one. -/
noncomputable def allTs (h : Hist Ev) : List Ts :=
  tsInit :: (List.range (Classical.choose h.fin)).filterMap fun f =>
    match h.lab f with
    | some (.cm _ _ t _) => some t
    | _ => none

theorem mem_allTs {h : Hist Ev} {f c n : Nat} {t : Ts} {ks : List Nat}
    (hf : h.lab f = some (.cm c n t ks)) : t ∈ allTs h := by
  apply List.mem_cons_of_mem
  have hlt : f < Classical.choose h.fin := by
    apply Classical.byContradiction; intro hn
    have := Classical.choose_spec h.fin f (Nat.le_of_not_lt hn)
    rw [hf] at this; cases this
  rw [List.mem_filterMap]
  exact ⟨f, List.mem_range.2 hlt, by rw [hf]⟩

theorem cts_unique {j : Inp lam} {c n : Nat} {t t' : Ts} (h : CTs j c n t) (h' : CTs j c n t') : t = t' := by
  obtain ⟨f, ks, hf⟩ := h; obtain ⟨f', ks', hf'⟩ := h'
  have := j.2.1.cm_unique hf hf'; subst this
  rw [hf] at hf'; cases hf'; rfl

theorem cts_ne {j : Inp lam} {c n : Nat} {t : Ts} (h : CTs j c n t) : t ≠ tsInit :=
  let ⟨_, _, hf⟩ := h; j.2.1.ts_ne hf

theorem next_lt {j : Inp lam} {k : Nat} {a b : Ts} (h : Next j k a b) : tsLt a b := h.2.2.1

/-! ## Every input has a permitted complete history -/

/-- Candidates in the serial history in timestamp order: the initial version,
or a version of `k` installed before the reader's commit timestamp. -/
def SerCand (j : Inp lam) (e : Nat) (v : Ts) : Prop :=
  ∃ c n k r, j.1.lab e = some (.rd c n k r) ∧
    (v = tsInit ∨ (∃ f c' n' ks, j.1.lab f = some (.cm c' n' v ks) ∧ k ∈ ks) ∧
      ∃ t, CTs j c n t ∧ tsLt v t)

theorem serCand_max (j : Inp lam) {e c n k r : Nat} (he : j.1.lab e = some (.rd c n k r)) :
    ∃ m, SerCand j e m ∧ ∀ v, SerCand j e v → v = m ∨ tsLt v m := by
  refine exists_max (allTs j.1) _ ⟨tsInit, c, n, k, r, he, Or.inl rfl⟩ ?_
  rintro v ⟨_, _, _, _, _, rfl | ⟨⟨f, _, _, _, hf, _⟩, _⟩⟩
  · exact List.mem_cons_self ..
  · exact mem_allTs hf

/-- The serial history: each read returns the latest version of its item
installed before its transaction's commit timestamp. -/
noncomputable def serial (j : Inp lam) : CH j where
  ans e := @dite _ (∃ m, SerCand j e m ∧ ∀ v, SerCand j e v → v = m ∨ tsLt v m) (Classical.propDecidable _)
    (fun h => Classical.choose h) (fun _ => tsInit)
  ok e c n k r he := by
    have hx := serCand_max j he
    rw [dif_pos hx]
    obtain ⟨⟨c₁, n₁, k₁, r₁, he₁, hv⟩, -⟩ := Classical.choose_spec hx
    rw [he] at he₁; cases he₁
    rcases hv with hv | ⟨⟨f, c', n', ks, hf, hk⟩, t, ht, hlt⟩
    · exact Or.inl hv
    · refine Or.inr ⟨f, c', n', ks, hf, hk, fun e' => ?_⟩
      simp only [Prod.mk.injEq] at e'; obtain ⟨rfl, rfl⟩ := e'
      rw [cts_unique ⟨f, ks, hf⟩ ht] at hlt; exact tsLt_irrefl _ hlt

theorem serial_ans (j : Inp lam) {e c n k r : Nat} (he : j.1.lab e = some (.rd c n k r)) :
    SerCand j e ((serial j).ans e) ∧ ∀ v, SerCand j e v → v = (serial j).ans e ∨ tsLt v ((serial j).ans e) := by
  have hx := serCand_max j he
  show SerCand j e (@dite _ _ (Classical.propDecidable _) _ _) ∧ ∀ v, SerCand j e v →
    v = @dite _ _ (Classical.propDecidable _) _ _ ∨ tsLt v (@dite _ _ (Classical.propDecidable _) _ _)
  rw [dif_pos hx]; exact Classical.choose_spec hx

theorem tg_lt {R : Ts → Ts → Prop} (hR : ∀ a b, R a b → tsLt a b) {a b : Ts}
    (h : Relation.TransGen R a b) : tsLt a b := by
  induction h with
  | single h => exact hR _ _ h
  | tail _ h ih => exact tsLt_trans ih (hR _ _ h)

/-- A history whose edges all increase timestamps exhibits no phenomenon. -/
theorem clean_of_lt {j : Inp lam} (H : CH j) (hwr : ∀ k a b, wrI H k a b → tsLt a b)
    (hrw : ∀ k a b, rwI H k a b → tsLt a b) (L : Level) : ¬ Proscribed L j H := by
  have hww : ∀ a b, (∃ k, wwI j k a b) → tsLt a b := fun _ _ ⟨_, h⟩ => next_lt h
  have hdep : ∀ a b, dep H a b → tsLt a b :=
    fun a b h => h.elim (hww a b) fun ⟨k, h⟩ => hwr k a b h
  have hdsg : ∀ a b, dsg H a b → tsLt a b :=
    fun a b h => h.elim (hdep a b) fun ⟨k, h⟩ => hrw k a b h
  have n0 : ¬ G0 j := fun ⟨t, h⟩ => no_cycle hww h
  have n1 : ¬ G1c H := fun ⟨t, h⟩ => no_cycle hdep h
  have cyc : ∀ {R : Ts → Ts → Prop}, (∀ a b, R a b → tsLt a b) → ∀ a b, tsLt a b →
      (b = a ∨ Relation.TransGen R b a) → False := by
    intro R hR a b hab hc
    rcases hc with rfl | hc
    · exact tsLt_irrefl _ hab
    · exact tsLt_irrefl _ (tsLt_trans hab (tg_lt hR hc))
  have n2 : ¬ G2 H := fun ⟨a, b, ⟨k, h⟩, hc⟩ => cyc hdsg a b (hrw k a b h) hc
  have nlu : ¬ LostUpdate H := fun ⟨k, a, b, h, hc⟩ => cyc
    (fun x y h => h.elim (fun h => next_lt h) fun h => h.elim (hwr k x y) (hrw k x y)) a b (hrw k a b h) hc
  cases L with
  | RU => exact n0
  | RC => exact fun h => h.elim n0 n1
  | SI => exact fun h => h.elim n0 fun h => h.elim n1 nlu
  | RR => exact fun h => h.elim n0 fun h => h.elim n1 n2
  | SER => exact fun h => h.elim n0 fun h => h.elim n1 n2

theorem serial_clean (j : Inp lam) (L : Level) : ¬ Proscribed L j (serial j) := by
  apply clean_of_lt
  · rintro k a b ⟨hab, -, e, c, n, r, he, hb, rfl⟩
    obtain ⟨⟨c₁, n₁, k₁, r₁, he₁, hv⟩, -⟩ := serial_ans j he
    rw [he] at he₁; cases he₁
    rcases hv with hv | ⟨-, t, ht, hlt⟩
    · rw [hv]; exact init_lt (cts_ne hb)
    · rwa [cts_unique hb ht]
  · rintro k a b ⟨hab, e, c, n, r, he, ha, hn⟩
    obtain ⟨-, hmax⟩ := serial_ans j he
    rcases tsLt_total hab with h | h
    · exact h
    · exfalso
      have hb0 : b ≠ tsInit := fun e => not_lt_init _ (e ▸ next_lt hn)
      have hbI : ∃ f c' n' ks, j.1.lab f = some (.cm c' n' b ks) ∧ k ∈ ks :=
        hn.2.1.resolve_left hb0
      rcases hmax b ⟨c, n, k, r, he, Or.inr ⟨hbI, a, ha, h⟩⟩ with e' | e'
      · exact tsLt_irrefl _ (e' ▸ next_lt hn)
      · exact tsLt_irrefl _ (tsLt_trans e' (next_lt hn))

/-! ## The specification -/

/-- The specification for a set of proscribed phenomena `P` (a predicate on
complete histories) that the serial history avoids: at input `j`, any set of
read answers contained in a complete history of `j` exhibiting none of `P`. -/
def specP (P : (j : Inp lam) → CH j → Prop) (hP : ∀ j, ¬ P j (serial j)) : Spec (Inp lam) (St Fact) where
  S j F := ∃ H : CH j, F ≼ H.facts ∧ ¬ P j H
  total j := ⟨fun _ => False, serial j, fun _ h => h.elim, hP j⟩

/-- `spec L` (Def. `def:hat-spec`): `specP` for the phenomena level `L`
proscribes. -/
def spec (L : Level) : Spec (Inp lam) (St Fact) := specP (Proscribed L) fun j => serial_clean j L

/-! ## HAT's server rule as the availability relation -/

/-- Versions `GET` may see at read `e`: the initial one, or a write of `k`
delivered to `e`'s replica before `e`. -/
def Cand (j : Inp lam) (e : Nat) (v : Ts) : Prop :=
  ∃ c n k r, j.1.lab e = some (.rd c n k r) ∧
    (v = tsInit ∨ ∃ d c' n' f ks, j.1.lab d = some (.dl c' n' k r) ∧ j.1.lt d e ∧
      j.1.lab f = some (.cm c' n' v ks))

/-- HAT's `GET` answer: the highest candidate timestamp. -/
def Ans (j : Inp lam) (e : Nat) (v : Ts) : Prop := Cand j e v ∧ ∀ v', Cand j e v' → v' = v ∨ tsLt v' v

/-- The output HAT's servers produce at `j`: every read's `GET` answer. -/
def hatOut (j : Inp lam) : St Fact
  | .read e v => Ans j e v

/-- The availability relation: the rows `(j, hatOut j)`. -/
def hatA : Table (Inp lam) (St Fact) := fun j o => o = hatOut j

theorem ans_exists (j : Inp lam) {e : Nat} (he : IsRd j e) : ∃ v, Ans j e v := by
  obtain ⟨c, n, k, r, he⟩ := he
  refine exists_max (allTs j.1) _ ⟨tsInit, c, n, k, r, he, Or.inl rfl⟩ ?_
  rintro v ⟨_, _, _, _, _, rfl | ⟨_, _, _, f, _, _, _, hf⟩⟩
  · exact List.mem_cons_self ..
  · exact mem_allTs hf

theorem ans_unique {j : Inp lam} {e : Nat} {v v' : Ts} (h : Ans j e v) (h' : Ans j e v') : v = v' :=
  max_unique h h'

/-- Candidates are stable under expansion. -/
theorem cand_iff {i j : Inp lam} (hij : i ≼ j) {e : Nat} (he : i.1.ev e) (v : Ts) :
    Cand i e v ↔ Cand j e v := by
  constructor
  · rintro ⟨c, n, k, r, hr, hv⟩
    refine ⟨c, n, k, r, lab_sub hij hr, ?_⟩
    rcases hv with hv | ⟨d, c', n', f, ks, hd, hlt, hf⟩
    · exact Or.inl hv
    · exact Or.inr ⟨d, c', n', f, ks, lab_sub hij hd, lt_sub hij hlt, lab_sub hij hf⟩
  · rintro ⟨c, n, k, r, hr, hv⟩
    refine ⟨c, n, k, r, lab_sup hij he hr, ?_⟩
    rcases hv with hv | ⟨d, c', n', f, ks, hd, hlt, hf⟩
    · exact Or.inl hv
    · have hlt' := lt_sup hij hlt he
      have hdi := Hist.ev_of_lt_left hlt'
      obtain ⟨f', t, ks', hf', -, hfd⟩ := j.2.1.dl_after hd
      have := j.2.1.cm_unique hf hf'; subst this
      have hfi := Hist.ev_of_lt_left (lt_sup hij hfd hdi)
      exact Or.inr ⟨d, c', n', f, ks, lab_sup hij hdi hd, hlt', lab_sup hij hfi hf⟩

/-- HAT's answers never change as the input grows. -/
theorem hatOut_mono {i j : Inp lam} (hij : i ≼ j) : hatOut i ≼ hatOut j := by
  rintro (⟨e, v⟩) ⟨hc, hmax⟩
  have he : i.1.ev e := by
    obtain ⟨c, n, k, r, hr, -⟩ := hc; exact lab_ev hr
  exact ⟨(cand_iff hij he v).1 hc, fun v' h => hmax v' ((cand_iff hij he v').2 h)⟩

/-- The complete history HAT's answers determine. -/
noncomputable def hatHist (j : Inp lam) : CH j where
  ans e := @dite _ (∃ v, Ans j e v) (Classical.propDecidable _) (fun h => Classical.choose h)
    (fun _ => tsInit)
  ok e c n k r he := by
    have hx := ans_exists j ⟨c, n, k, r, he⟩
    rw [dif_pos hx]
    obtain ⟨⟨c₁, n₁, k₁, r₁, he₁, hv⟩, -⟩ := Classical.choose_spec hx
    rw [he] at he₁; cases he₁
    rcases hv with hv | ⟨d, c', n', f, ks, hd, hlt, hf⟩
    · exact Or.inl hv
    · obtain ⟨f', t, ks', hf', hk, hfd⟩ := j.2.1.dl_after hd
      have := j.2.1.cm_unique hf hf'; subst this
      rw [hf] at hf'; cases hf'
      refine Or.inr ⟨f, c', n', ks, hf, hk, fun e' => ?_⟩
      simp only [Prod.mk.injEq] at e'; obtain ⟨rfl, rfl⟩ := e'
      -- the read precedes its own commit, which precedes the delivery
      have h1 := j.1.lt_num (j.2.1.rd_before he hf)
      have h2 := j.1.lt_num hfd
      have h3 := j.1.lt_num hlt
      omega

theorem hatHist_ans (j : Inp lam) {e : Nat} (he : IsRd j e) : Ans j e ((hatHist j).ans e) := by
  have hx := ans_exists j he
  show Ans j e (@dite _ _ (Classical.propDecidable _) _ _)
  rw [dif_pos hx]; exact Classical.choose_spec hx

/-- HAT's answers (patched timestamps) are read committed: every read- and
write-dependency increases timestamps. -/
theorem hatOut_rc (j : Inp true) : (spec .RC).S j (hatOut j) := by
  refine ⟨hatHist j, ?_, ?_⟩
  · rintro (⟨e, v⟩) h
    have hr : IsRd j e := by obtain ⟨c, n, k, r, hr, -⟩ := h.1; exact ⟨c, n, k, r, hr⟩
    exact ⟨hr, ans_unique (hatHist_ans j hr) h⟩
  · have hwr : ∀ k a b, wrI (hatHist j) k a b → tsLt a b := by
      rintro k a b ⟨hab, -, e, c, n, r, he, ⟨f, ks, hf⟩, rfl⟩
      obtain ⟨⟨c₁, n₁, k₁, r₁, he₁, hv⟩, -⟩ := hatHist_ans j ⟨c, n, k, r, he⟩
      rw [he] at he₁; cases he₁
      rcases hv with hv | ⟨d, c', n', g, ks', hd, hlt, hg⟩
      · rw [hv]; exact init_lt (j.2.1.ts_ne hf)
      · exact j.2.2 rfl he hd hlt hf hg
    intro h
    rcases h with ⟨t, h⟩ | ⟨t, h⟩
    · exact no_cycle (fun _ _ ⟨_, h⟩ => next_lt h) h
    · exact no_cycle (fun a b h => h.elim (fun ⟨_, h⟩ => next_lt h) fun ⟨k, h⟩ => hwr k a b h) h

theorem hatOut_ru (j : Inp true) : (spec .RU).S j (hatOut j) := by
  obtain ⟨H, hF, hn⟩ := hatOut_rc j
  exact ⟨H, hF, fun h => hn (Or.inl h)⟩

/-- HAT's read rule answers every read exactly once and never revises an
answer as the input grows (with or without the timestamp condition). -/
theorem hat_rule :
    (∀ (j : Inp lam) e, IsRd j e → (∃ v, hatOut j (.read e v)) ∧
      ∀ v v', hatOut j (.read e v) → hatOut j (.read e v') → v = v') ∧
      ∀ i j : Inp lam, i ≼ j → hatOut i ≼ hatOut j :=
  ⟨fun j _ he => ⟨ans_exists j he, fun _ _ h h' => ans_unique h h'⟩, fun _ _ h => hatOut_mono h⟩

/-- **RU and RC are available** (Thm. `thm:hat-levels`, first part).  Under
the timestamp condition HAT's rows are permitted, so the specification
satisfies Lifted Monotonicity for `hatA`, and by Complete CAP some system has
Availability for `hatA` and Partition Consistency. -/
theorem rc_available (L : Level) (hL : L = .RU ∨ L = .RC) (D : Type) :
    (∀ i o, hatA i o → (spec (lam := true) L).S i o) ∧
      CAP.ConsistentOn (spec (lam := true) L) hatA ∧
      ∃ Sys : CAP.System (spec (lam := true) L) D,
        CAP.AvailabilityFor hatA Sys ∧ CAP.PartitionConsistencyAtEnd Sys := by
  have hS : ∀ i o, hatA i o → (spec (lam := true) L).S i o := by
    rintro i o rfl
    rcases hL with rfl | rfl
    · exact hatOut_ru i
    · exact hatOut_rc i
  have hC : CAP.ConsistentOn (spec (lam := true) L) hatA := by
    intro rows hrows j hj
    refine ⟨hatOut j, hS j _ rfl, fun r hr => ?_⟩
    rw [hrows r hr]; exact hatOut_mono (hj r hr)
  exact ⟨hS, hC, (CAP.complete_cap_for _ D hatA hS).2 hC⟩

/-! ## Lost Update: HAT's pair -/

/-- `T₁ = (1,1)` reads `x` (item 0) at replica 0 and commits with timestamp
`(1,1)` writing `x`; `T₂ = (2,1)` does the same at replica 1 with timestamp
`(1,2)`.  No write is delivered (a partition). -/
def luLab : Nat → Option Ev
  | 0 => some (.rd 1 1 0 0)
  | 1 => some (.cm 1 1 (1, 1) [0])
  | 2 => some (.rd 2 1 0 1)
  | 3 => some (.cm 2 1 (1, 2) [0])
  | _ => none

def luHist (keep : Nat → Prop) [DecidablePred keep] : Hist Ev where
  lab e := if keep e then luLab e else none
  lt a b := ((a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 3)) ∧ keep a ∧ keep b
  lt_ev {a b} h := by
    obtain ⟨hab, ha, hb⟩ := h
    simp only [ha, hb, if_true]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [luLab]
  lt_num {a b} h := by rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  lt_trans {a b c} h₁ h₂ := by
    rcases h₁.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h₂.1 with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
  fin := ⟨4, fun e he => by
    split
    · match e, he with
      | n + 4, _ => rfl
    · rfl⟩

theorem luLab_cases {e : Nat} {x : Ev} (h : luLab e = some x) :
    (e = 0 ∧ x = .rd 1 1 0 0) ∨ (e = 1 ∧ x = .cm 1 1 (1, 1) [0]) ∨
      (e = 2 ∧ x = .rd 2 1 0 1) ∨ (e = 3 ∧ x = .cm 2 1 (1, 2) [0]) := by
  match e, h with
  | 0, h => cases h; simp
  | 1, h => cases h; simp
  | 2, h => cases h; simp
  | 3, h => cases h; simp

def keepJ : Nat → Prop := fun _ => True
def keep1 : Nat → Prop := fun e => e = 0 ∨ e = 1
def keep2 : Nat → Prop := fun e => e = 2 ∨ e = 3

instance : DecidablePred keepJ := fun _ => isTrue trivial
instance : DecidablePred keep1 := fun e => by unfold keep1; infer_instance
instance : DecidablePred keep2 := fun e => by unfold keep2; infer_instance

def hJ : Hist Ev := luHist keepJ
theorem hk1 : ∀ e, keep1 (e + 1) → keep1 e ∨ e % 2 = 1 := fun e h => by unfold keep1 at *; omega
theorem hk2 : ∀ e, keep2 (e + 1) → keep2 e ∨ e % 2 = 1 := fun e h => by unfold keep2 at *; omega
def h1 : Hist Ev := luHist keep1
def h2 : Hist Ev := luHist keep2

theorem hJ_lab {e : Nat} {x : Ev} (h : hJ.lab e = some x) : luLab e = some x := h

theorem wf_hJ : WF hJ where
  cm_unique {e e' c n t t' ks ks'} h h' := by
    rcases luLab_cases (hJ_lab h) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases luLab_cases (hJ_lab h') with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> rfl
  ts_unique {e e' c n c' n' t ks ks'} h h' := by
    rcases luLab_cases (hJ_lab h) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases luLab_cases (hJ_lab h') with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> rfl
  ts_ne {e c n t ks} h := by
    rcases luLab_cases (hJ_lab h) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> decide
  dl_after {d c n k r} h := by
    rcases luLab_cases (hJ_lab h) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
  rd_before {e f c n k r t ks} h h' := by
    rcases luLab_cases (hJ_lab h) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases luLab_cases (hJ_lab h') with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      exact ⟨by simp, trivial, trivial⟩
  replica {e e' r} h h' hne := by
    have l1 : hJ.lab e = luLab e := rfl
    have l2 : hJ.lab e' = luLab e' := rfl
    rw [l1] at h; rw [l2] at h'
    match e, e', h, h' with
    | 0, 0, _, _ => exact absurd rfl hne
    | 2, 2, _, _ => exact absurd rfl hne
    | 0, 2, h, h' => simp only [luLab, AtReplica] at h h'; omega
    | 2, 0, h, h' => simp only [luLab, AtReplica] at h h'; omega
    | 1, _, h, _ => simp [luLab, AtReplica] at h
    | 3, _, h, _ => simp [luLab, AtReplica] at h
    | _, 1, _, h' => simp [luLab, AtReplica] at h'
    | _, 3, _, h' => simp [luLab, AtReplica] at h'
    | n + 4, _, h, _ => simp [luLab, AtReplica] at h
    | _, n + 4, _, h' => simp [luLab, AtReplica] at h'

theorem lam_hJ : Lamport hJ := by
  intro e d f g c n k r c' n' t t' ks ks' _ hd
  rcases luLab_cases (hJ_lab hd) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx

theorem le_hJ (keep : Nat → Prop) [DecidablePred keep]
    (hk : ∀ e, keep (e + 1) → keep e ∨ e % 2 = 1) : luHist keep ≼ hJ := by
  refine ⟨fun e x h => ?_, fun a b => ?_⟩
  · show (if keepJ e then luLab e else none) = some x
    have : (if keep e then luLab e else none) = some x := h
    split at this
    · simpa [keepJ] using this
    · cases this
  · show (((a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 3)) ∧ keep a ∧ keep b) ↔
      ((((a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 3)) ∧ keepJ a ∧ keepJ b) ∧ (if keep b then luLab b else none) ≠ none)
    constructor
    · rintro ⟨hab, ha, hb⟩
      refine ⟨⟨hab, trivial, trivial⟩, ?_⟩
      rw [if_pos hb]; rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [luLab]
    · rintro ⟨⟨hab, -, -⟩, hb⟩
      have hkb : keep b := by
        apply Classical.byContradiction; intro hn; rw [if_neg hn] at hb; exact hb rfl
      refine ⟨hab, ?_, hkb⟩
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases hk 0 hkb with h | h
        · exact h
        · simp at h
      · rcases hk 2 hkb with h | h
        · exact h
        · simp at h

def iJ : Inp lam := ⟨hJ, wf_hJ, fun _ => lam_hJ⟩
def i1 : Inp lam := ⟨h1, wf_down (le_hJ keep1 hk1) wf_hJ, fun _ => lamport_down (le_hJ keep1 hk1) lam_hJ⟩
def i2 : Inp lam := ⟨h2, wf_down (le_hJ keep2 hk2) wf_hJ, fun _ => lamport_down (le_hJ keep2 hk2) lam_hJ⟩

/-- In `i₁` the only version `T₁` may read is `x₀`. -/
theorem i1_ver {v : Ts} (h : Ver (i1 (lam := lam)) 1 1 0 v) : v = tsInit := by
  rcases h with h | ⟨f, c', n', ks, hf, -, hne⟩
  · exact h
  · have : (if keep1 f then luLab f else none) = some (.cm c' n' v ks) := hf
    split at this
    · next hk =>
        rcases luLab_cases this with ⟨he, hx⟩ | ⟨he, hx⟩ | ⟨he, hx⟩ | ⟨he, hx⟩ <;> cases hx
        · exact absurd rfl hne
        · subst he; simp [keep1] at hk
    · cases this

/-- In `i₂` the only version `T₂` may read is `x₀`. -/
theorem i2_ver {v : Ts} (h : Ver (i2 (lam := lam)) 2 1 0 v) : v = tsInit := by
  rcases h with h | ⟨f, c', n', ks, hf, -, hne⟩
  · exact h
  · have : (if keep2 f then luLab f else none) = some (.cm c' n' v ks) := hf
    split at this
    · next hk =>
        rcases luLab_cases this with ⟨he, hx⟩ | ⟨he, hx⟩ | ⟨he, hx⟩ | ⟨he, hx⟩ <;> cases hx
        · subst he; simp [keep2] at hk
        · exact absurd rfl hne
    · cases this

theorem iJ_inst (t : Ts) : Inst (iJ (lam := lam)) 0 t ↔ t = tsInit ∨ t = (1, 1) ∨ t = (1, 2) := by
  constructor
  · rintro (h | ⟨f, c, n, ks, hf, hk⟩)
    · exact Or.inl h
    · rcases luLab_cases (hJ_lab hf) with ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ <;> cases hx
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  · rintro (h | rfl | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨1, 1, 1, [0], rfl, by simp⟩
    · exact Or.inr ⟨3, 2, 1, [0], rfl, by simp⟩

/-- In every complete history of `j` in which both reads return `x₀`, the
anti-dependency `T₂ → T₁` and write-dependency `T₁ → T₂` on `x` form a Lost
Update cycle (hence also G2). -/
theorem lu_cycle (H : CH (iJ (lam := lam))) (h2' : H.ans 2 = tsInit) :
    LostUpdate H ∧ G2 H := by
  have hn1 : Next (iJ (lam := lam)) 0 tsInit (1, 1) := by
    refine ⟨(iJ_inst _).2 (Or.inl rfl), (iJ_inst _).2 (by simp), by decide, fun c hc => ?_⟩
    rcases (iJ_inst c).1 hc with rfl | rfl | rfl <;> decide
  have hn2 : Next (iJ (lam := lam)) 0 (1, 1) (1, 2) := by
    refine ⟨(iJ_inst _).2 (by simp), (iJ_inst _).2 (by simp), by decide, fun c hc => ?_⟩
    rcases (iJ_inst c).1 hc with rfl | rfl | rfl <;> decide
  have hrw : rwI H 0 (1, 2) (1, 1) := ⟨by decide, 2, 2, 1, 1, rfl, ⟨3, [0], rfl⟩, h2' ▸ hn1⟩
  refine ⟨⟨0, (1, 2), (1, 1), hrw, Or.inr (.single (Or.inl hn2))⟩,
    ⟨(1, 2), (1, 1), ⟨0, hrw⟩, Or.inr (.single (Or.inl (Or.inl ⟨0, hn2⟩)))⟩⟩

/-- **Lost Update is unavailable** (Thm. `thm:hat-levels`, second part).  For
any set of proscribed phenomena `P` that includes Lost Update (and that the
serial history avoids, so the specification is total), no availability
relation `A ⊆ S` that answers every read satisfies Lifted Monotonicity for
`A`; so by Complete CAP no system has Availability for `A` and Partition
Consistency.  This holds with or without the timestamp condition.  Witness:
HAT's pair of read-modify-writes of `x` at two replicas, `ts(T₁) < ts(T₂)`.
At `T₂`'s replica the only permitted answer is `x₀`; once `T₁` commits,
every complete history in which `T₂` read `x₀` has the anti-dependency
`T₂ → T₁` and the write-dependency `T₁ → T₂` on `x`, a Lost Update. -/
theorem lostUpdate_unavailableP (P : (j : Inp lam) → CH j → Prop) (hP : ∀ j, ¬ P j (serial j))
    (hLU : ∀ j (H : CH j), LostUpdate H → P j H) (D : Type)
    (A : Table (Inp lam) (St Fact)) (hAS : ∀ i o, A i o → (specP P hP).S i o) (htot : ∀ i, ∃ o, A i o)
    (hans : ∀ i o e, A i o → IsRd i e → ∃ v, o (.read e v)) :
    ¬ CAP.ConsistentOn (specP P hP) A ∧
      ¬ ∃ Sys : CAP.System (specP P hP) D, CAP.AvailabilityFor A Sys ∧ CAP.PartitionConsistencyAtEnd Sys := by
  have hn : ¬ CAP.ConsistentOn (specP P hP) A := by
    intro hC
    obtain ⟨o1, ho1⟩ := htot i1
    obtain ⟨o2, ho2⟩ := htot i2
    obtain ⟨v2, hv2⟩ := hans i2 o2 2 ho2 ⟨2, 1, 0, 1, rfl⟩
    have e2 : v2 = tsInit := by
      obtain ⟨H, hF, -⟩ := hAS _ _ ho2
      obtain ⟨-, hv⟩ := hF _ hv2
      rw [← hv]; exact i2_ver (H.ok 2 2 1 0 1 rfl)
    obtain ⟨u, ⟨H, hF, hPH⟩, hle⟩ := hC [(i1, o1), (i2, o2)]
      (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> assumption) iJ
      (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact le_hJ keep1 hk1
          · exact le_hJ keep2 hk2)
    have a2 : H.ans 2 = tsInit := by
      rw [← e2]; exact (hF _ (hle _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ hv2)).2
    exact hPH (hLU _ H (lu_cycle H a2).1)
  exact ⟨hn, fun h => hn ((CAP.complete_cap_for (specP P hP) D A hAS).1 h)⟩

/-- The named levels: snapshot isolation, repeatable read, serializability. -/
theorem lostUpdate_unavailable (L : Level) (hL : L = .SI ∨ L = .RR ∨ L = .SER) (D : Type)
    (A : Table (Inp lam) (St Fact)) (hAS : ∀ i o, A i o → (spec L).S i o) (htot : ∀ i, ∃ o, A i o)
    (hans : ∀ i o e, A i o → IsRd i e → ∃ v, o (.read e v)) :
    ¬ CAP.ConsistentOn (spec L) A ∧
      ¬ ∃ Sys : CAP.System (spec L) D, CAP.AvailabilityFor A Sys ∧ CAP.PartitionConsistencyAtEnd Sys :=
  lostUpdate_unavailableP (Proscribed L) _ (fun _ H h => proscribes_lostUpdate L hL H h) D A hAS htot hans

/-! ## The timestamp condition is needed -/

/-- `T₂ = (2,1)` commits `x` (item 0) with timestamp `(1,2)`; the write is
delivered to replica 0; `T₁ = (1,1)` then reads `x` at replica 0 and commits
`x` with the smaller timestamp `(1,1)` (fixed when it began). -/
def wLab : Nat → Option Ev
  | 0 => some (.cm 2 1 (1, 2) [0])
  | 1 => some (.dl 2 1 0 0)
  | 2 => some (.rd 1 1 0 0)
  | 3 => some (.cm 1 1 (1, 1) [0])
  | _ => none

theorem wLab_cases {e : Nat} {x : Ev} (h : wLab e = some x) :
    (e = 0 ∧ x = .cm 2 1 (1, 2) [0]) ∨ (e = 1 ∧ x = .dl 2 1 0 0) ∨
      (e = 2 ∧ x = .rd 1 1 0 0) ∨ (e = 3 ∧ x = .cm 1 1 (1, 1) [0]) := by
  match e, h with
  | 0, h => cases h; simp
  | 1, h => cases h; simp
  | 2, h => cases h; simp
  | 3, h => cases h; simp

def wHist : Hist Ev where
  lab := wLab
  lt a b := a < b ∧ b < 4
  lt_ev {a b} h := by
    obtain ⟨hab, hb⟩ := h
    constructor
    · match a, hab, hb with
      | 0, _, _ => simp [wLab]
      | 1, _, _ => simp [wLab]
      | 2, _, _ => simp [wLab]
      | _ + 3, h, h' => omega
    · match b, hab, hb with
      | 0, h, _ => omega
      | 1, _, _ => simp [wLab]
      | 2, _, _ => simp [wLab]
      | 3, _, _ => simp [wLab]
      | _ + 4, _, h' => omega
  lt_num h := h.1
  lt_trans h₁ h₂ := ⟨Nat.lt_trans h₁.1 h₂.1, h₂.2⟩
  fin := ⟨4, fun e he => by
    match e, he with
    | n + 4, _ => rfl⟩

theorem wHist_lab {e : Nat} {x : Ev} (h : wHist.lab e = some x) : wLab e = some x := h

theorem wf_wHist : WF wHist where
  cm_unique {e e' c n t t' ks ks'} h h' := by
    rcases wLab_cases (wHist_lab h) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases wLab_cases (wHist_lab h') with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> rfl
  ts_unique {e e' c n c' n' t ks ks'} h h' := by
    rcases wLab_cases (wHist_lab h) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases wLab_cases (wHist_lab h') with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> rfl
  ts_ne {e c n t ks} h := by
    rcases wLab_cases (wHist_lab h) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> decide
  dl_after {d c n k r} h := by
    rcases wLab_cases (wHist_lab h) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
    exact ⟨0, (1, 2), [0], rfl, by simp, by decide, by decide⟩
  rd_before {e f c n k r t ks} h h' := by
    rcases wLab_cases (wHist_lab h) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases wLab_cases (wHist_lab h') with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      exact ⟨by decide, by decide⟩
  replica {e e' r} h h' hne := by
    have he : e < 4 := by
      apply Classical.byContradiction; intro hn
      have : wHist.lab e = none := by
        show wLab e = none
        match e, hn with
        | n + 4, _ => rfl
      rw [this] at h; exact h
    have he' : e' < 4 := by
      apply Classical.byContradiction; intro hn
      have : wHist.lab e' = none := by
        show wLab e' = none
        match e', hn with
        | n + 4, _ => rfl
      rw [this] at h'; exact h'
    rcases Nat.lt_or_gt_of_ne hne with hl | hl
    · exact Or.inl ⟨hl, he'⟩
    · exact Or.inr ⟨hl, he⟩

/-- The input, legal except for the timestamp condition. -/
def wInp : Inp false := ⟨wHist, wf_wHist, fun h => nomatch h⟩

theorem wHist_not_lamport : ¬ Lamport wHist := fun h =>
  tsLt_irrefl _ (tsLt_trans (h (e := 2) (d := 1) (f := 3) (g := 0) rfl rfl ⟨by decide, by decide⟩ rfl rfl)
    (show tsLt (1, 1) (1, 2) by decide))

theorem wInp_inst (t : Ts) : Inst wInp 0 t ↔ t = tsInit ∨ t = (1, 2) ∨ t = (1, 1) := by
  constructor
  · rintro (h | ⟨f, c, n, ks, hf, hk⟩)
    · exact Or.inl h
    · rcases wLab_cases (wHist_lab hf) with ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ <;> cases hx
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  · rintro (h | rfl | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨0, 2, 1, [0], rfl, by simp⟩
    · exact Or.inr ⟨3, 1, 1, [0], rfl, by simp⟩

/-- **The timestamp condition is needed.**  Without it, HAT's read rule is
not contained in `S_RC`: `T₁`'s read returns `T₂`'s version `(1,2)` (a
read-dependency `T₂ → T₁`), and `T₁` then installs `x` with the smaller
timestamp `(1,1)` (a write-dependency `T₁ → T₂`), a G1c cycle in every
complete history extending HAT's answers. -/
theorem timestamp_condition_needed :
    ¬ Lamport wHist ∧ hatOut wInp (.read 2 (1, 2)) ∧ ¬ (spec .RC).S wInp (hatOut wInp) := by
  have hans : hatOut wInp (.read 2 (1, 2)) := by
    refine ⟨⟨1, 1, 0, 0, rfl, Or.inr ⟨1, 2, 1, 0, [0], rfl, ⟨by decide, by decide⟩, rfl⟩⟩, ?_⟩
    rintro v ⟨c, n, k, r, he, hv⟩
    cases he
    rcases hv with rfl | ⟨d, c', n', f, ks, hd, -, hf⟩
    · exact Or.inr (by decide)
    · rcases wLab_cases (wHist_lab hd) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
      rcases wLab_cases (wHist_lab hf) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
      exact Or.inl rfl
  refine ⟨wHist_not_lamport, hans, ?_⟩
  rintro ⟨H, hF, hP⟩
  have h2 : H.ans 2 = (1, 2) := (hF _ hans).2
  have hww : wwI wInp 0 (1, 1) (1, 2) := by
    refine ⟨(wInp_inst _).2 (by simp), (wInp_inst _).2 (by simp), by decide, fun c hc => ?_⟩
    rcases (wInp_inst c).1 hc with rfl | rfl | rfl <;> decide
  have hwr : wrI H 0 (1, 2) (1, 1) :=
    ⟨by decide, (wInp_inst _).2 (by simp), 2, 1, 1, 0, rfl, ⟨3, [0], rfl⟩, h2⟩
  exact hP (Or.inr ⟨(1, 1), .tail (.single (Or.inl ⟨0, hww⟩)) (Or.inr ⟨0, hwr⟩)⟩)

end HATSpec
end CC
