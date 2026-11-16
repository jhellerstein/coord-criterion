import CoordCriterion.Instances.HATTaxonomyWitness

/-!
# Monotonic Atomic View by the algorithm of App. B (Bailis et al., extended version)

App. B of the extended HAT paper gives pseudocode ("Algorithm HAT Read Atomic
Isolation") for Monotonic Atomic View.  This file takes that algorithm, as
written, as the explicit relation of the MAV specification of
`Instances/HATTaxonomy.lean` and derives, through Complete CAP for an explicit
relation, that MAV is highly available.  It also records two findings about
App. B and Def. 26.

## The algorithm

* Servers keep `pending` and `good`.  A write moves to `good` "if all acks
  received for all replicas for ts's sibs", i.e. once the replica has learned
  that the transaction is *pending stable* (`Stable`, every replica of every item
  it wrote has received its write).  Which acknowledgments a replica has
  received is not determined by the input, so it is a parameter `K : AckK reps`:
  `K.K h m c n` says that the replica serving read `m` holds `(c,n)`'s writes in
  `good`.  It must be sound (`K` implies `Stable` before `m`) and depend only on
  `m`'s past (`K.loc`).  `stableK` is the replica that has every acknowledgment
  that happened before the read.
* `GET(k, ts_required)`: with `ts_required = ⊥`, the highest-timestamped write of
  `k` in `good`; else a write of `k` in `good` with timestamp `≥ ts_required`
  (we take the highest one; App. B: "the highest-timestamped write is always a
  valid response candidate"); else the write in `pending` with timestamp
  `ts_required`.  The answer is therefore the largest of the good versions and
  the required timestamp (`BC`, `bAns`).
* The client's `required` map starts empty in each transaction (`CLEANUP`), and
  after each read of a write `w_ret` it is raised to `w_ret.ts` on every item of
  `w_ret.sibs`, the items its transaction wrote.  So the required timestamp of
  `k` at a read is the largest answer of the transaction's earlier reads whose
  transaction wrote `k` (third disjunct of `BC`).  A client's reads of its own
  write buffer are not reads in the model.  App. B does not treat predicate
  reads; a predicate read is answered item by item by the same rule, with the
  required timestamps of the transaction's earlier reads.
* The answers are defined by recursion on the event number (`bTab`): a
  transaction's earlier reads happen before, hence have smaller numbers.

## Results

* `bAns_stable`: every non-initial answer is a version of a transaction that is
  pending stable before the read.  A pending-write answer (`GET`'s third case)
  carries a required timestamp set by an earlier read of the same transaction,
  whose answer was already pending stable.  So every answer is visible at the
  reading replica (`outB_vis`).
* `outB_mono`: the answers depend only on the past of each read, so the rule is
  monotone.
* `bHist_OTV`: the rule exhibits no OTV (Def. 26, as in
  `Instances/HATTaxonomy.lean`); `bHist_G1c`: under the timestamp condition it
  exhibits no G1c.
* `mav_appB`: **for every acknowledgment schedule `K`, under the timestamp
  condition, MAV is highly available with App. B's algorithm as explicit
  relation** (through `highlyAvailable_iff`, i.e. `CAP.complete_cap_for`).
* `appB_not_rc` (finding F7): App. B fixes a transaction's timestamp at
  `BEGIN TRANSACTION`, and its clients "use the RC algorithm from Section 5.1.1".
  On an input without the timestamp condition (`w7`), App. B's answer contains a
  G1c cycle, so App. B as written does not provide Read Committed, hence not
  MAV.  This is the timestamp error of Theorem `thm:hat-levels`, carried over.
* `appB_OTVlit` (finding F5): read literally, Def. 26's "a set of edges by y
  containing at least one anti-dependency edge" admits any path of edges by `y`
  (`OTVlit`).  On `w5` (the timestamp condition holds), App. B's answers
  exhibit `OTVlit`: `Tj` writes `x` and `y`; `Tk` reads `y₀` before `Tj` is
  stable and then writes `y`; `Ti` reads `x` and `y` from `Tj`.  The cycle is
  `Tj →wr_x Ti →rw_y Tk →rw_y Tj`.  So App. B does not prevent OTV as Def. 26
  literally states it; it prevents the form of Def. 26's example (Fig. 9).
-/

namespace CC
namespace HATTax
open HATRC (Ts tsLt tsInit tsLt_trans tsLt_irrefl no_cycle)
open IConf (Hist St)
open HATSpec (Ev Inp WF Lamport Ver Inst Next CTs wwI lab_ev lab_sub lab_sup lt_sub lt_sup
  exists_max allTs mem_allTs max_unique tsLt_total not_lt_init init_lt cts_unique cts_ne next_lt)

variable {reps : Nat → List Nat} {lam : Bool}

/-! ## Acknowledgment knowledge -/

/-- Which transactions the replica serving read `m` holds in `good`. -/
structure AckK (reps : Nat → List Nat) where
  K : Hist Ev → Nat → Nat → Nat → Prop
  sound : ∀ {h m c n}, K h m c n → Stable reps h c n m
  loc : ∀ {a b : Hist Ev}, a ≼ b → ∀ {m}, a.ev m → ∀ c n, (K a m c n ↔ K b m c n)

/-- The replica has received every acknowledgment that happened before the read. -/
def stableK : AckK reps where
  K h m c n := Stable reps h c n m
  sound h := h
  loc hab _ hm _ _ := stable_iff hab hm

/-! ## The read rule -/

section Rule
variable (K : AckK reps) (h : Hist Ev)

/-- Candidates for `GET` of `k` at read `m`, given the answers `T` of earlier
reads: the initial version, a good version of `k`, or a required timestamp of `k`
(the answer of an earlier read of the same transaction, by a transaction that
wrote `k`). -/
def BC (T : Nat → Nat → Ts) (m k : Nat) (v : Ts) : Prop :=
  v = tsInit ∨
  (∃ f c' n' ks, h.lab f = some (.cm c' n' v ks) ∧ k ∈ ks ∧ K.K h m c' n') ∨
  (∃ c n e' k'' r'' f c' n' ks, IsRead h m c n ∧ h.lt e' m ∧ Acc h e' c n k'' r'' ∧ T e' k'' = v ∧
    h.lab f = some (.cm c' n' v ks) ∧ k ∈ ks)

theorem bc_max (T : Nat → Nat → Ts) (m k : Nat) : ∃ v, IsMax (BC K h T m k) v :=
  exists_max (allTs h) _ ⟨_, Or.inl rfl⟩ fun v hv => by
    rcases hv with rfl | ⟨f, c, n, ks, hf, -, -⟩ | ⟨c, n, e', k'', r'', f, c', n', ks, -, -, -, -, hf, -⟩
    · exact List.mem_cons_self ..
    · exact mem_allTs hf
    · exact mem_allTs hf

/-- `GET`'s answer from the earlier answers `T`. -/
noncomputable def bMax (T : Nat → Nat → Ts) (m k : Nat) : Ts := Classical.choose (bc_max K h T m k)

theorem bMax_spec (T : Nat → Nat → Ts) (m k : Nat) : IsMax (BC K h T m k) (bMax K h T m k) :=
  Classical.choose_spec (bc_max K h T m k)

/-- The answers of events below `m`. -/
noncomputable def bTab : Nat → Nat → Nat → Ts
  | 0 => fun _ _ => tsInit
  | m + 1 => fun e k => if e = m then bMax K h (bTab m) m k else bTab m e k

/-- App. B's answer to item `k` at read `e`. -/
noncomputable def bAns (e k : Nat) : Ts := bTab K h (e + 1) e k

theorem bTab_eq : ∀ m e k, e < m → bTab K h m e k = bAns K h e k
  | 0, _, _, he => absurd he (Nat.not_lt_zero _)
  | m + 1, e, k, he => by
    by_cases hem : e = m
    · subst hem; rfl
    · show (if e = m then _ else bTab K h m e k) = _
      rw [if_neg hem]; exact bTab_eq m e k (by omega)

/-- The candidates with the rule's own earlier answers. -/
def BCA (m k : Nat) (v : Ts) : Prop := BC K h (bAns K h) m k v

theorem bc_congr (m k : Nat) (v : Ts) : BC K h (bTab K h m) m k v ↔ BCA K h m k v := by
  unfold BCA BC
  constructor
  · rintro (h1 | h2 | ⟨c, n, e', k'', r'', f, c', n', ks, h1, h2, h3, h4, h5, h6⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨c, n, e', k'', r'', f, c', n', ks, h1, h2, h3,
        by rw [← bTab_eq K h m e' k'' (h.lt_num h2)]; exact h4, h5, h6⟩)
  · rintro (h1 | h2 | ⟨c, n, e', k'', r'', f, c', n', ks, h1, h2, h3, h4, h5, h6⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨c, n, e', k'', r'', f, c', n', ks, h1, h2, h3,
        by rw [bTab_eq K h m e' k'' (h.lt_num h2)]; exact h4, h5, h6⟩)

/-- The answer is the largest candidate. -/
theorem bAns_max (m k : Nat) : IsMax (BCA K h m k) (bAns K h m k) := by
  have hb := bMax_spec K h (bTab K h m) m k
  have he : bAns K h m k = bMax K h (bTab K h m) m k := by
    show (if m = m then _ else _) = _; rw [if_pos rfl]
  rw [he]
  exact ⟨(bc_congr K h m k _).1 hb.1, fun w hw => hb.2 w ((bc_congr K h m k w).2 hw)⟩

theorem bAns_eq {m k : Nat} {v : Ts} (hv : BCA K h m k v) (hmax : ∀ w, BCA K h m k w → w = v ∨ tsLt w v) :
    bAns K h m k = v :=
  isMax_unique (bAns_max K h m k) ⟨hv, hmax⟩

end Rule

/-! ## Properties on inputs -/

section Props
variable (K : AckK reps)

/-- Every non-initial answer is a version of `k` written by a transaction that
is pending stable before the read. -/
theorem bAns_stable (j : SInp reps lam) : ∀ m k, bAns K j.1 m k ≠ tsInit →
    ∃ f c' n' ks, j.1.lab f = some (.cm c' n' (bAns K j.1 m k) ks) ∧ k ∈ ks ∧
      Stable reps j.1 c' n' m := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro k hne
    rcases (bAns_max K j.1 m k).1 with h0 | ⟨f, c', n', ks, hf, hk, hK⟩ |
        ⟨c, n, e', k'', r'', f, c', n', ks, -, hl, -, hv, hf, hk⟩
    · exact absurd h0 hne
    · exact ⟨f, c', n', ks, hf, hk, K.sound hK⟩
    · have hne' : bAns K j.1 e' k'' ≠ tsInit := by rw [hv]; exact hne
      obtain ⟨g, d, m', ls, hg, -, hs⟩ := ih e' (j.1.lt_num hl) k'' hne'
      rw [hv] at hg
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hf hg
      exact ⟨f, c', n', ks, hf, hk, stable_mono hl hs⟩

/-- A pending-stable transaction committed before the point. -/
theorem stable_commit {j : SInp reps lam} {f c n p : Nat} {t : Ts} {ks : List Nat}
    (hf : j.1.lab f = some (.cm c n t ks)) (hs : Stable reps j.1 c n p) : j.1.lt f p := by
  obtain ⟨g, u, ls, hg, hl, -⟩ := hs
  have := j.2.1.1.cm_unique hf hg; subst this; exact hl

/-- A pending-stable transaction's write of `k` reached every replica of `k`. -/
theorem stable_dl {j : SInp reps lam} {f c n p k r : Nat} {t : Ts} {ks : List Nat}
    (hf : j.1.lab f = some (.cm c n t ks)) (hk : k ∈ ks) (hr : r ∈ reps k)
    (hs : Stable reps j.1 c n p) : ∃ d, j.1.lab d = some (.dl c n k r) ∧ j.1.lt d p := by
  obtain ⟨g, u, ls, hg, -, hall⟩ := hs
  have := j.2.1.1.cm_unique hf hg; subst this
  rw [hf] at hg; cases hg
  exact hall k hk r hr

/-- The complete history of App. B's answers. -/
noncomputable def bHist (j : SInp reps lam) : CH2 j where
  val e k := bAns K j.1 e k
  ok e c n k r ha := by
    by_cases h0 : bAns K j.1 e k = tsInit
    · exact Or.inl h0
    · obtain ⟨f, c', n', ks, hf, hk, hs⟩ := bAns_stable K j e k h0
      refine Or.inr ⟨f, c', n', ks, hf, hk, fun hcn => ?_⟩
      simp only [Prod.mk.injEq] at hcn; obtain ⟨rfl, rfl⟩ := hcn
      have h1 := j.1.lt_num (read_before ha.isRead hf)
      have h2 := j.1.lt_num (stable_commit hf hs)
      omega

/-- App. B's output: its answer to every read access. -/
def outB (j : SInp reps lam) : St Fact2
  | .rv e k v => IsAcc j e k ∧ bAns K j.1 e k = v

theorem outB_facts (j : SInp reps lam) : outB K j ≼ (bHist K j).facts := fun _ h => h

theorem outB_vis (j : SInp reps lam) : (vstore (reps := reps) (lam := lam)).P j (outB K j) := by
  rintro e k v ⟨⟨c, n, r, ha⟩, rfl⟩
  refine ⟨c, n, r, ha, ?_⟩
  by_cases h0 : bAns K j.1 e k = tsInit
  · exact Or.inl h0
  · obtain ⟨f, c', n', ks, hf, hk, hs⟩ := bAns_stable K j e k h0
    obtain ⟨d, hd, hdl⟩ := stable_dl hf hk (acc_rep ha) hs
    exact Or.inr ⟨d, c', n', f, ks, hd, hdl, hf⟩

theorem outB_answers (j : SInp reps lam) : AnswersAll j (outB K j) :=
  fun e c n k r ha => ⟨_, ⟨c, n, r, ha⟩, rfl⟩

/-- The answers depend only on each read's past. -/
theorem bAns_loc {i j : SInp reps lam} (hij : i ≼ j) : ∀ e k, i.1.ev e →
    bAns K i.1 e k = bAns K j.1 e k := by
  have hab : i.1 ≼ j.1 := hij
  intro e
  induction e using Nat.strongRecOn with
  | ind e ih =>
    intro k he
    have key : ∀ v, BCA K i.1 e k v ↔ BCA K j.1 e k v := by
      intro v
      constructor
      · rintro (h0 | ⟨f, c', n', ks, hf, hk, hK⟩ |
            ⟨c, n, e', k'', r'', f, c', n', ks, hr, hl, hacc, hv, hf, hk⟩)
        · exact Or.inl h0
        · exact Or.inr (Or.inl ⟨f, c', n', ks, lab_sub hab hf, hk, (K.loc hab he c' n').1 hK⟩)
        · refine Or.inr (Or.inr ⟨c, n, e', k'', r'', f, c', n', ks, isRead_sub hab hr,
            lt_sub hab hl, acc_sub hab hacc, ?_, lab_sub hab hf, hk⟩)
          rw [← ih e' (i.1.lt_num hl) k'' (IConf.Hist.ev_of_lt_left hl)]; exact hv
      · rintro (h0 | ⟨f, c', n', ks, hf, hk, hK⟩ |
            ⟨c, n, e', k'', r'', f, c', n', ks, hr, hl, hacc, hv, hf, hk⟩)
        · exact Or.inl h0
        · have hKi := (K.loc hab he c' n').2 hK
          have hfl := lt_sup hab (stable_commit hf (K.sound hK)) he
          exact Or.inr (Or.inl ⟨f, c', n', ks,
            lab_sup hab (IConf.Hist.ev_of_lt_left hfl) hf, hk, hKi⟩)
        · have hl' := lt_sup hab hl he
          have he' : i.1.ev e' := IConf.Hist.ev_of_lt_left hl'
          have hv' : bAns K i.1 e' k'' = v := by
            rw [ih e' (j.1.lt_num hl) k'' he']; exact hv
          have hne : v ≠ tsInit := j.2.1.1.ts_ne hf
          obtain ⟨g, d, m', ls, hg, -, hs⟩ := bAns_stable K j e' k'' (by rw [hv]; exact hne)
          rw [hv] at hg
          obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hf hg
          have hfl := lt_sup hab (stable_commit hf hs) he'
          exact Or.inr (Or.inr ⟨c, n, e', k'', r'', f, c', n', ks, isRead_sup hab he hr, hl',
            acc_sup hab he' hacc, hv', lab_sup hab (IConf.Hist.ev_of_lt_left hfl) hf, hk⟩)
    have h1 := bAns_max K i.1 e k
    have h2 := bAns_max K j.1 e k
    exact isMax_unique ⟨(key _).1 h1.1, fun w hw => h1.2 w ((key w).2 hw)⟩ h2

theorem outB_mono {i j : SInp reps lam} (hij : i ≼ j) : outB K i ≼ outB K j := by
  have hab : i.1 ≼ j.1 := hij
  rintro ⟨e, k, v⟩ ⟨⟨c, n, r, ha⟩, hv⟩
  exact ⟨⟨c, n, r, acc_sub hab ha⟩, by rw [← bAns_loc K hij e k (acc_ev ha)]; exact hv⟩

/-- App. B's rule exhibits no OTV. -/
theorem bHist_OTV (j : SInp reps lam) : ¬ OTV (bHist K j) := by
  rintro ⟨e₁, e₂, c, n, r₁, r₂, x, y, ti, tj, he₁, he₂, -, hl, hv₁, ⟨-, -, -⟩, hrw⟩
  obtain ⟨hlt, hiy⟩ := rwWw_lt hrw
  have hj0 : tj ≠ tsInit := fun h => not_lt_init _ (h ▸ hlt)
  obtain ⟨f, c', n', ks, hf, hy⟩ := inst_commit hiy hj0
  -- the earlier read of `x` raised the required timestamp of `y` to `tj`
  have hc : BCA K j.1 e₂ y tj :=
    Or.inr (Or.inr ⟨c, n, e₁, x, r₁, f, c', n', ks, Or.inl ⟨y, r₂, he₂⟩, hl, Or.inl he₁, hv₁, hf, hy⟩)
  exact not_le_lt ((bAns_max K j.1 e₂ y).2 _ hc) hlt

/-- Under the timestamp condition App. B's rule exhibits no G1c. -/
theorem bHist_G1c (j : SInp reps true) : ¬ G1c (bHist K j) := by
  have hwr : ∀ x a b, wr2 (bHist K j) x a b → tsLt a b := by
    rintro x a b ⟨-, -, e, c, n, r, he, ⟨f, ks, hf⟩, rfl⟩
    by_cases h0 : bAns K j.1 e x = tsInit
    · show tsLt (bAns K j.1 e x) b
      rw [h0]; exact init_lt (cts_ne (j := j.inp) ⟨f, ks, hf⟩)
    · obtain ⟨g, c', n', ls, hg, hx, hs⟩ := bAns_stable K j e x h0
      obtain ⟨d, hd, hdl⟩ := stable_dl hg hx (j.2.2.rd_rep he) hs
      exact j.2.1.2 rfl he hd hdl hf hg
  rintro ⟨t, h⟩
  exact no_cycle (fun a b h => h.elim (fun ⟨_, h⟩ => next_lt h) (fun ⟨k, h⟩ => hwr k a b h)) h

theorem outB_tax_MAV (j : SInp reps true) : (tax (reps := reps) .MAV).P j (outB K j) :=
  ⟨outB_vis K j, bHist K j, outB_facts K j,
    fun h => h.elim (g0_false j) fun h => h.elim (bHist_G1c K j) (bHist_OTV K j)⟩

end Props

/-- **Monotonic Atomic View is highly available, with App. B's algorithm as
explicit relation**, for every acknowledgment schedule and under the timestamp
condition.  The algorithm's answers are contained in the MAV specification,
answer every read, and are monotone; Complete CAP for an explicit relation
(`CAP.complete_cap_for`, through `highlyAvailable_iff`) gives a system with
Availability for them and Partition Consistency. -/
theorem mav_appB (K : AckK reps) (D : Type) : HighlyAvailable (reps := reps) (lam := true) (tax .MAV) D :=
  (highlyAvailable_iff _ D).2 ⟨fun i o => o = outB K i, fun i o h => h ▸ outB_tax_MAV K i,
    fun i => ⟨_, rfl⟩, fun i o h => h ▸ outB_answers K i, fun rows hrows j hj =>
      ⟨outB K j, outB_tax_MAV K j, fun r hr => by rw [hrows r hr]; exact outB_mono K (hj r hr)⟩⟩


/-! ## Literal OTV -/

section Lit
variable {j : SInp reps lam} (H : CH2 j)

/-- An edge by `y`: a write-, read- or anti-dependency by `y`. -/
def yedge (y : Nat) (a b : Ts) : Prop := wwI j.inp y a b ∨ wr2 H y a b ∨ rw2 H y a b

/-- OTV (Def. 26) as written: one read-dependency by `x` from `Tj` to `Ti`, and
a path of edges by `y` from `Ti` back to `Tj` containing at least one
anti-dependency, the first one from `Ti`'s later read of `y` (as in Def. 26's
example, Fig. 9, `Ti` reads `x` before `y`). -/
def OTVlit : Prop :=
  ∃ e₁ e₂ c n r₁ r₂ x y ti tj, j.1.lab e₁ = some (.rd c n x r₁) ∧
    j.1.lab e₂ = some (.rd c n y r₂) ∧ CTs j.inp c n ti ∧ j.1.lt e₁ e₂ ∧
    H.val e₁ x = tj ∧ wr2 H x tj ti ∧
    ∃ u, Next j.inp y (H.val e₂ y) u ∧ (u = tj ∨ Relation.TransGen (yedge H y) u tj)

/-- The form of Def. 26 that its example has (`OTV`, write-dependencies after the
anti-dependency) is a special case of the literal form. -/
theorem otv_lit (h : OTV H) : OTVlit H := by
  obtain ⟨e₁, e₂, c, n, r₁, r₂, x, y, ti, tj, he₁, he₂, hc, hl, hv, hwr, u, hn, hu⟩ := h
  refine ⟨e₁, e₂, c, n, r₁, r₂, x, y, ti, tj, he₁, he₂, hc, hl, hv, hwr, u, hn, ?_⟩
  rcases hu with rfl | hu
  · exact Or.inl rfl
  · refine Or.inr ?_
    clear hv hwr
    induction hu with
    | single h => exact .single (Or.inl h)
    | tail _ h ih => exact .tail ih (Or.inl h)

end Lit

/-! ## Witness histories with one replica -/

/-- Every item has the single replica `0`. -/
abbrev r0 : Nat → List Nat := fun _ => [0]

theorem r0_mem {k r : Nat} (h : r ∈ r0 k) : r = 0 := by simpa using h

/-! ### `w7`: App. B fixes timestamps at `BEGIN` (finding F7) -/

def w7L : List Ev := [.cm 2 1 (2, 5) [0], .dl 2 1 0 0, .rd 1 1 0 0, .cm 1 1 (1, 1) [0]]
def w7R : List (Nat × Nat) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

def w7H : Hist Ev := mkHist w7L w7R (by decide) (by decide)

theorem w7_cases {e : Nat} {x : Ev} (h : w7H.lab e = some x) :
    (e = 0 ∧ x = .cm 2 1 (2, 5) [0]) ∨ (e = 1 ∧ x = .dl 2 1 0 0) ∨ (e = 2 ∧ x = .rd 1 1 0 0) ∨
    (e = 3 ∧ x = .cm 1 1 (1, 1) [0]) := by
  have h' : w7L[e]? = some x := h
  match e, h' with
  | 0, h => cases h; simp
  | 1, h => cases h; simp
  | 2, h => cases h; simp
  | 3, h => cases h; simp

theorem w7_lt_iff {a b : Nat} : w7H.lt a b ↔ (a, b) ∈ w7R := Iff.rfl

theorem w7_wf : WF w7H where
  cm_unique h h' := by
    rcases w7_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w7_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> rfl
  ts_unique h h' := by
    rcases w7_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w7_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> rfl
  ts_ne h := by
    rcases w7_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> decide
  dl_after h := by
    rcases w7_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
    exact ⟨0, (2, 5), [0], rfl, by simp, show (0, 1) ∈ w7R by decide⟩
  rd_before h h' := by
    rcases w7_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w7_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
    show (2, 3) ∈ w7R; decide
  replica {e e' r} h h' hne := by
    cases he : w7H.lab e with
    | none => rw [he] at h; exact h.elim
    | some x =>
      cases he' : w7H.lab e' with
      | none => rw [he'] at h'; exact h'.elim
      | some x' =>
        rw [he] at h; rw [he'] at h'
        rcases w7_cases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases w7_cases he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp only [HATSpec.AtReplica] at h h' <;>
          first
            | exact absurd rfl hne
            | (left; rw [w7_lt_iff]; decide)
            | (right; rw [w7_lt_iff]; decide)

theorem w7_sess : Sess r0 w7H where
  rd_rep h := by
    rcases w7_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx; simp
  prd_rep h := by
    rcases w7_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
  prd_before h := by
    rcases w7_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
  txn_order {e e' c n} h h' hne := by
    rcases h with ⟨k, r, h⟩ | ⟨ks, r, h⟩ <;> rcases h' with ⟨k', r', h'⟩ | ⟨ks', r', h'⟩ <;>
      rcases w7_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w7_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      exact absurd rfl hne
  seq {f f' e c n n' t t' ks ks'} hf hf' hl he := by
    rcases w7_cases hf with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w7_cases hf' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      exact absurd hl (by rw [w7_lt_iff]; decide)
  sess_ts {f f' c n n' t t' ks ks'} hf hf' hl := by
    rcases w7_cases hf with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w7_cases hf' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      exact absurd hl (by rw [w7_lt_iff]; decide)

/-- `w7` violates the timestamp condition: `T₂` (timestamp `(1,1)`, fixed at
`BEGIN`) reads the version `(2,5)`. -/
def w7 : SInp r0 false := ⟨w7H, ⟨w7_wf, fun h => by cases h⟩, w7_sess⟩

theorem w7_inst0 (t : Ts) : Inst w7.inp 0 t ↔ t = tsInit ∨ t = (2, 5) ∨ t = (1, 1) := by
  constructor
  · rintro (h | ⟨f, c, n, ks, hf, hk⟩)
    · exact Or.inl h
    · rcases w7_cases hf with ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ <;> cases hx <;> simp
  · rintro (h | rfl | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨0, 2, 1, [0], rfl, by simp⟩
    · exact Or.inr ⟨3, 1, 1, [0], rfl, by simp⟩

/-- App. B's `GET(x, ⊥)` in `w7` returns `(2,5)`: it is pending stable. -/
theorem w7_ans : bAns (stableK (reps := r0)) w7H 2 0 = (2, 5) := by
  apply bAns_eq
  · refine Or.inr (Or.inl ⟨0, 2, 1, [0], rfl, by simp, 0, (2, 5), [0], rfl,
      show (0, 2) ∈ w7R by decide, fun k hk r hr => ?_⟩)
    have := r0_mem hr; subst this
    simp at hk; subst hk
    exact ⟨1, rfl, show (1, 2) ∈ w7R by decide⟩
  · intro w hw
    rcases hw with rfl | ⟨f, c', n', ks, hf, -, -⟩ | ⟨c, n, e', k'', r'', f, c', n', ks, -, -, -, -, hf, -⟩ <;>
      first
        | (right; decide)
        | (rcases w7_cases hf with ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ <;> cases hx <;>
            first | exact Or.inl rfl | (right; decide))

/-- **Finding F7: App. B as written does not provide Read Committed.**  Its
clients fix a transaction's timestamp at `BEGIN TRANSACTION`; in `w7` the
transaction `(1,1)` reads `x` from `(2,5)` and then writes `x`, so its write
precedes the version it read: the G1c cycle `(1,1) →ww_x (2,5) →wr_x (1,1)`.
App. B's answers are therefore in no RC (hence no MAV) specification. -/
theorem appB_not_rc : ¬ (tax (reps := r0) (lam := false) .RC).P w7 (outB (stableK (reps := r0)) w7) := by
  rintro ⟨-, H, hF, hcl⟩
  have hv : H.val 2 0 = (2, 5) := (hF (.rv 2 0 (2, 5)) ⟨⟨1, 1, 0, Or.inl rfl⟩, w7_ans⟩).2
  have hnext : Next w7.inp 0 (1, 1) (2, 5) := by
    refine ⟨(w7_inst0 _).2 (Or.inr (Or.inr rfl)), (w7_inst0 _).2 (Or.inr (Or.inl rfl)), by decide,
      fun c hc => ?_⟩
    rcases (w7_inst0 c).1 hc with rfl | rfl | rfl <;> decide
  have hwr : wr2 H 0 (2, 5) (1, 1) :=
    ⟨by decide, (w7_inst0 _).2 (Or.inr (Or.inl rfl)), 2, 1, 1, 0, rfl, ⟨3, [0], rfl⟩, hv⟩
  exact hcl (Or.inr ⟨(1, 1), .tail (.single (Or.inl ⟨0, hnext⟩)) (Or.inr ⟨0, hwr⟩)⟩)


/-! ### `w5`: App. B does not prevent OTV as Def. 26 writes it (finding F5) -/

/-- `Tj = (1,1)` writes `x = 0` and `y = 1`; `Tk = (3,1)` reads `y` at event 1,
before `Tj` is stable, and writes `y`; `Tj`'s writes arrive (events 3, 4); `Ti =
(2,1)` reads `x` and then `y`. -/
def w5L : List Ev :=
  [.cm 1 1 (1, 1) [0, 1], .rd 3 1 1 0, .cm 3 1 (1, 3) [1], .dl 1 1 0 0, .dl 1 1 1 0,
   .rd 2 1 0 0, .rd 2 1 1 0, .cm 2 1 (1, 2) []]
def w5R : List (Nat × Nat) :=
  [(0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7),
   (3, 4), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]

def w5H : Hist Ev := mkHist w5L w5R (by decide) (by decide)

theorem w5_cases {e : Nat} {x : Ev} (h : w5H.lab e = some x) :
    (e = 0 ∧ x = .cm 1 1 (1, 1) [0, 1]) ∨ (e = 1 ∧ x = .rd 3 1 1 0) ∨
    (e = 2 ∧ x = .cm 3 1 (1, 3) [1]) ∨ (e = 3 ∧ x = .dl 1 1 0 0) ∨ (e = 4 ∧ x = .dl 1 1 1 0) ∨
    (e = 5 ∧ x = .rd 2 1 0 0) ∨ (e = 6 ∧ x = .rd 2 1 1 0) ∨ (e = 7 ∧ x = .cm 2 1 (1, 2) []) := by
  have h' : w5L[e]? = some x := h
  match e, h' with
  | 0, h => cases h; simp
  | 1, h => cases h; simp
  | 2, h => cases h; simp
  | 3, h => cases h; simp
  | 4, h => cases h; simp
  | 5, h => cases h; simp
  | 6, h => cases h; simp
  | 7, h => cases h; simp

theorem w5_lt_iff {a b : Nat} : w5H.lt a b ↔ (a, b) ∈ w5R := Iff.rfl

theorem w5_wf : WF w5H where
  cm_unique h h' := by
    rcases w5_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w5_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> rfl
  ts_unique h h' := by
    rcases w5_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w5_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> rfl
  ts_ne h := by
    rcases w5_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> decide
  dl_after h := by
    rcases w5_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
    · exact ⟨0, (1, 1), [0, 1], rfl, by simp, show (0, 3) ∈ w5R by decide⟩
    · exact ⟨0, (1, 1), [0, 1], rfl, by simp, show (0, 4) ∈ w5R by decide⟩
  rd_before h h' := by
    rcases w5_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w5_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> (rw [w5_lt_iff]; decide)
  replica {e e' r} h h' hne := by
    cases he : w5H.lab e with
    | none => rw [he] at h; exact h.elim
    | some x =>
      cases he' : w5H.lab e' with
      | none => rw [he'] at h'; exact h'.elim
      | some x' =>
        rw [he] at h; rw [he'] at h'
        rcases w5_cases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases w5_cases he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp only [HATSpec.AtReplica] at h h' <;>
          first
            | exact absurd rfl hne
            | (left; rw [w5_lt_iff]; decide)
            | (right; rw [w5_lt_iff]; decide)
            | omega

theorem w5_lam : Lamport w5H := by
  intro e d f g c n k r c' n' t t' ks ks' he hd hl hf hg
  rcases w5_cases hd with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
    rcases w5_cases he with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
    rcases w5_cases hf with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
    rcases w5_cases hg with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
    first | decide | (exfalso; revert hl; rw [w5_lt_iff]; decide)

theorem w5_sess : Sess r0 w5H where
  rd_rep h := by
    rcases w5_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> simp
  prd_rep h := by
    rcases w5_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
  prd_before h := by
    rcases w5_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
  txn_order {e e' c n} h h' hne := by
    rcases h with ⟨k, r, h⟩ | ⟨ks, r, h⟩ <;> rcases h' with ⟨k', r', h'⟩ | ⟨ks', r', h'⟩ <;>
      rcases w5_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w5_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      first
        | exact absurd rfl hne
        | (left; rw [w5_lt_iff]; decide)
        | (right; rw [w5_lt_iff]; decide)
  seq {f f' e c n n' t t' ks ks'} hf hf' hl he := by
    rcases w5_cases hf with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w5_cases hf' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      exact absurd hl (by rw [w5_lt_iff]; decide)
  sess_ts {f f' c n n' t t' ks ks'} hf hf' hl := by
    rcases w5_cases hf with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w5_cases hf' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      exact absurd hl (by rw [w5_lt_iff]; decide)

/-- `w5` satisfies the timestamp condition. -/
def w5 : SInp r0 true := ⟨w5H, ⟨w5_wf, fun _ => w5_lam⟩, w5_sess⟩

theorem w5_cm {f c n : Nat} {t : Ts} {ks : List Nat} (h : w5H.lab f = some (.cm c n t ks)) :
    (f = 0 ∧ c = 1 ∧ n = 1 ∧ t = (1, 1) ∧ ks = [0, 1]) ∨ (f = 2 ∧ c = 3 ∧ n = 1 ∧ t = (1, 3) ∧ ks = [1]) ∨
    (f = 7 ∧ c = 2 ∧ n = 1 ∧ t = (1, 2) ∧ ks = []) := by
  rcases w5_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> simp

theorem w5_acc {e c n k r : Nat} (h : Acc w5H e c n k r) :
    (e = 1 ∧ c = 3 ∧ n = 1 ∧ k = 1) ∨ (e = 5 ∧ c = 2 ∧ n = 1 ∧ k = 0) ∨ (e = 6 ∧ c = 2 ∧ n = 1 ∧ k = 1) := by
  rcases h with h | ⟨ks, h, -⟩
  · rcases w5_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> simp
  · rcases w5_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx

theorem w5_stable_j (p : Nat) (hp : (3, p) ∈ w5R) (hp' : (4, p) ∈ w5R) (hp0 : (0, p) ∈ w5R) :
    Stable r0 w5H 1 1 p := by
  refine ⟨0, (1, 1), [0, 1], rfl, hp0, fun k hk r hr => ?_⟩
  have := r0_mem hr; subst this
  simp at hk; rcases hk with rfl | rfl
  · exact ⟨3, rfl, hp⟩
  · exact ⟨4, rfl, hp'⟩

/-- A transaction stable before `p` committed before `p`. -/
theorem w5_stable_lt {c n p : Nat} (h : Stable r0 w5H c n p) :
    ∃ f t ks, w5H.lab f = some (.cm c n t ks) ∧ (f, p) ∈ w5R := by
  obtain ⟨f, t, ks, hf, hl, -⟩ := h; exact ⟨f, t, ks, hf, hl⟩

theorem w5_ans1 : bAns (stableK (reps := r0)) w5H 1 1 = tsInit := by
  apply bAns_eq _ _ (Or.inl rfl)
  intro w hw
  rcases hw with rfl | ⟨f, c', n', ks, hf, -, hs⟩ | ⟨c, n, e', k'', r'', f, c', n', ks, -, hl, -, -, hf, -⟩
  · exact Or.inl rfl
  · obtain ⟨g, t, ls, -, hg⟩ := w5_stable_lt hs
    exfalso; simp [w5R] at hg
  · exfalso; have : (e', 1) ∈ w5R := hl
    simp [w5R] at this

theorem w5_ans5 : bAns (stableK (reps := r0)) w5H 5 0 = (1, 1) := by
  apply bAns_eq _ _ (Or.inr (Or.inl ⟨0, 1, 1, [0, 1], rfl, by simp,
    w5_stable_j 5 (by decide) (by decide) (by decide)⟩))
  intro w hw
  rcases hw with rfl | ⟨f, c', n', ks, hf, -, hs⟩ |
      ⟨c, n, e', k'', r'', f, c', n', ks, hr, hl, hacc, -, hf, -⟩
  · right; decide
  · obtain ⟨g, t, ls, hg, hgl⟩ := w5_stable_lt hs
    rcases w5_cm hf with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact Or.inl rfl
    · rcases w5_cm hg with ⟨-, h1, -⟩ | ⟨rfl, -⟩ | ⟨-, h1, -⟩
      · cases h1
      · exfalso; simp [w5R] at hgl
      · cases h1
    · rcases w5_cm hg with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | ⟨rfl, -⟩
      · cases h1
      · cases h1
      · exfalso; simp [w5R] at hgl
  · exfalso
    rcases w5_acc hacc with ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simp [IsRead, w5H, mkHist, w5L] at hr
    · exact absurd hl (by rw [w5_lt_iff]; decide)
    · exact absurd hl (by rw [w5_lt_iff]; decide)

theorem w5_ans6 : bAns (stableK (reps := r0)) w5H 6 1 = (1, 1) := by
  apply bAns_eq _ _ (Or.inr (Or.inl ⟨0, 1, 1, [0, 1], rfl, by simp,
    w5_stable_j 6 (by decide) (by decide) (by decide)⟩))
  intro w hw
  rcases hw with rfl | ⟨f, c', n', ks, hf, -, hs⟩ |
      ⟨c, n, e', k'', r'', f, c', n', ks, hr, hl, hacc, hv, hf, -⟩
  · right; decide
  · obtain ⟨g, t, ls, hg, hgl⟩ := w5_stable_lt hs
    rcases w5_cm hf with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact Or.inl rfl
    · rcases w5_cm hg with ⟨-, h1, -⟩ | ⟨rfl, -⟩ | ⟨-, h1, -⟩
      · cases h1
      · exfalso; simp [w5R] at hgl
      · cases h1
    · rcases w5_cm hg with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | ⟨rfl, -⟩
      · cases h1
      · cases h1
      · exfalso; simp [w5R] at hgl
  · rcases w5_acc hacc with ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, -, -, rfl⟩ | ⟨rfl, -⟩
    · simp [IsRead, w5H, mkHist, w5L] at hr
    · rw [← hv, w5_ans5]; exact Or.inl rfl
    · exact absurd hl (by rw [w5_lt_iff]; decide)

theorem w5_inst (k : Nat) (t : Ts) : Inst w5.inp k t ↔
    t = tsInit ∨ (t = (1, 1) ∧ k ∈ [0, 1]) ∨ (t = (1, 3) ∧ k ∈ [1]) ∨ (t = (1, 2) ∧ k ∈ []) := by
  constructor
  · rintro (h | ⟨f, c, n, ks, hf, hk⟩)
    · exact Or.inl h
    · rcases w5_cm hf with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, hk⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, hk⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, hk⟩))
  · rintro (h | ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, hk⟩)
    · exact Or.inl h
    · exact Or.inr ⟨0, 1, 1, [0, 1], rfl, hk⟩
    · exact Or.inr ⟨2, 3, 1, [1], rfl, hk⟩
    · exact Or.inr ⟨7, 2, 1, [], rfl, hk⟩

/-- **Finding F5: App. B does not prevent OTV as Def. 26 writes it.**  On `w5`,
which satisfies the timestamp condition, App. B's answers are in the MAV
specification (Def. 26 in the form of its example), yet every complete history
with those answers exhibits `OTVlit`: `Tj →wr_x Ti →rw_y Tk →rw_y Tj`. -/
theorem appB_OTVlit :
    (tax (reps := r0) (lam := true) .MAV).P w5 (outB (stableK (reps := r0)) w5) ∧
    ∀ H : CH2 w5, outB (stableK (reps := r0)) w5 ≼ H.facts → OTVlit H := by
  refine ⟨outB_tax_MAV _ w5, fun H hF => ?_⟩
  have v1 : H.val 1 1 = tsInit := (hF (.rv 1 1 tsInit) ⟨⟨3, 1, 0, Or.inl rfl⟩, w5_ans1⟩).2
  have v5 : H.val 5 0 = (1, 1) := (hF (.rv 5 0 (1, 1)) ⟨⟨2, 1, 0, Or.inl rfl⟩, w5_ans5⟩).2
  have v6 : H.val 6 1 = (1, 1) := (hF (.rv 6 1 (1, 1)) ⟨⟨2, 1, 0, Or.inl rfl⟩, w5_ans6⟩).2
  have hI1 : Inst w5.inp 1 (1, 1) := (w5_inst 1 _).2 (Or.inr (Or.inl ⟨rfl, by simp⟩))
  have hI3 : Inst w5.inp 1 (1, 3) := (w5_inst 1 _).2 (Or.inr (Or.inr (Or.inl ⟨rfl, by simp⟩)))
  have hbetween : ∀ a b, Inst w5.inp 1 a → Inst w5.inp 1 b → ∀ c, Inst w5.inp 1 c →
      ((a = tsInit ∧ b = (1, 1)) ∨ (a = (1, 1) ∧ b = (1, 3))) → ¬ (tsLt a c ∧ tsLt c b) := by
    intro a b _ _ c hc hab
    rcases (w5_inst 1 c).1 hc with rfl | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, hk⟩
    · rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · simp at hk
  have n13 : Next w5.inp 1 (1, 1) (1, 3) :=
    ⟨hI1, hI3, by decide, fun c hc => hbetween _ _ hI1 hI3 c hc (Or.inr ⟨rfl, rfl⟩)⟩
  have n01 : Next w5.inp 1 tsInit (1, 1) :=
    ⟨Or.inl rfl, hI1, by decide, fun c hc => hbetween _ _ (Or.inl rfl) hI1 c hc (Or.inl ⟨rfl, rfl⟩)⟩
  refine ⟨5, 6, 2, 1, 0, 0, 0, 1, (1, 2), (1, 1), rfl, rfl, ⟨7, [], rfl⟩,
    show (5, 6) ∈ w5R by decide, v5,
    ⟨by decide, (w5_inst 0 _).2 (Or.inr (Or.inl ⟨rfl, by simp⟩)), 5, 2, 1, 0, rfl, ⟨7, [], rfl⟩, v5⟩,
    (1, 3), by rw [v6]; exact n13, Or.inr (.single (Or.inr (Or.inr ⟨by decide, 1, 3, 1, 0, rfl,
      ⟨2, [1], rfl⟩, by rw [v1]; exact n01⟩)))⟩


/-! ## F1 in deployment form -/

section F1
open CC.Deploy

/-- A deployment lets each client's server answer that client's sticky reads:
participant `srv c` may emit an output answering every sticky read of `c`. -/
def StickyComplete {sp : Spec (SInp reps lam) (St Fact2)} {n : Nat} (Dp : Deployment sp n)
    (srv : Nat → Fin n) : Prop :=
  ∀ (j : SInp reps lam) (c : Nat), ∃ o, Dp.A (srv c) j o ∧
    ∀ e m k r, Acc j.1 e c m k r → Reflects (reps := reps) j.1 e c r → ∃ v, o (.rv e k v)

/-- The sticky deployment of `Instances/HATTaxonomyRules.lean` is sticky complete. -/
theorem stickyD_complete {g : Guar} (hg : StickyGuar g) {n : Nat} (srv : Nat → Fin n) :
    StickyComplete (stickyD (reps := reps) (lam := lam) hg srv) srv := by
  intro j c
  refine ⟨_, rfl, fun e m k r ha hst => ?_⟩
  obtain ⟨v, hv⟩ := outR_answersSticky j e c m k r ha hst
  exact ⟨v, hv, c, m, r, ha, rfl⟩

/-- **Finding F1 in deployment form.**  For MYR as Def. 34 writes it, no
deployment that lets clients `1` and `2` stick to different servers, each
answering its client's sticky reads, has a system with Deployment Availability
and Partition Consistency.  (For the single-item form, `stickyD_available`.)
In `w3` both clients' reads are sticky, each server's only visible answer is the
initial version, and the two answers together exhibit `MYRlit`; the necessity
half of the deployment form of Complete CAP (`Deploy.authorized_reconciled`)
would reconcile them. -/
theorem myrLit_not_sticky_deploy (h00 : 0 ∈ reps 0) (h01 : 0 ∈ reps 1) (h10 : 1 ∈ reps 0)
    {n : Nat} (hn : 2 ≤ n) (Dp : Deployment (tax (reps := reps) (lam := lam) .RYWlit) n)
    (srv : Nat → Fin n) (hsrv : srv 1 ≠ srv 2) (hst : StickyComplete Dp srv)
    {D : Type} (Sys : CAP.System (tax (reps := reps) (lam := lam) .RYWlit) D) :
    ¬ (DeploymentAvailability Sys Dp ∧ PartitionConsistencyAt Sys n) := by
  classical
  rintro ⟨hDA, hPC⟩
  let ja := w3a (lam := lam) h00 h01 h10
  let jb := w3b (lam := lam) h00 h01 h10
  obtain ⟨o₁, hA₁, ha₁⟩ := hst ja 1
  obtain ⟨o₂, hA₂, ha₂⟩ := hst jb 2
  have hacc₁ : Acc ja.1 3 1 2 1 0 := Or.inl (by
    show (w3H.restrict (· ≤ 4) w3_down1).lab 3 = _
    rw [restrict_lab' (by decide)]; rfl)
  have hacc₂ : Acc jb.1 5 2 1 0 1 := Or.inl (by
    show (w3H.restrict (5 ≤ ·) w3_down2).lab 5 = _
    rw [restrict_lab' (by decide)]; rfl)
  have hst₁ : Reflects (reps := reps) ja.1 3 1 0 := by
    intro f n' t ks k hf hl hk hr
    obtain ⟨-, hf'⟩ := restrict_lab (hP := w3_down1) hf
    rcases w3_cases hf' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx
    · simp at hk; subst hk
      refine ⟨1, ?_, ?_⟩
      · show (w3H.restrict (· ≤ 4) w3_down1).lab 1 = _
        rw [restrict_lab' (by decide)]; rfl
      · exact ⟨show (1, 3) ∈ w3R by decide, by decide⟩
    · exact absurd hl.1 (by rw [w3_lt_iff]; decide)
  have hst₂ : Reflects (reps := reps) jb.1 5 2 1 := by
    intro f n' t ks k hf hl
    obtain ⟨-, hf'⟩ := restrict_lab (hP := w3_down2) hf
    rcases w3_cases hf' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx
    exact absurd hl.1 (by rw [w3_lt_iff]; decide)
  obtain ⟨v₁, hv₁⟩ := ha₁ 3 2 1 0 hacc₁ hst₁
  obtain ⟨v₂, hv₂⟩ := ha₂ 5 1 0 1 hacc₂ hst₂
  have e₁ : v₁ = tsInit := by
    obtain ⟨c, n, r, ha', hvis⟩ := (Dp.sub _ _ _ hA₁).1 3 1 v₁ hv₁
    obtain ⟨-, -, rfl⟩ := acc_unique hacc₁ ha'
    rcases hvis with h | ⟨d, c', n', f, ks, hd, -⟩
    · exact h
    · obtain ⟨-, hd'⟩ := restrict_lab (hP := w3_down1) hd
      rcases w3_cases hd' with ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ <;>
        cases hx
  have e₂ : v₂ = tsInit := by
    obtain ⟨c, n, r, ha', hvis⟩ := (Dp.sub _ _ _ hA₂).1 5 0 v₂ hv₂
    obtain ⟨-, -, rfl⟩ := acc_unique hacc₂ ha'
    rcases hvis with h | ⟨d, c', n', f, ks, hd, -⟩
    · exact h
    · obtain ⟨hd5, hd'⟩ := restrict_lab (hP := w3_down2) hd
      rcases w3_cases hd' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
        ⟨rfl, hx⟩ <;> cases hx
  -- each server, alone on its side, emits its answers; Partition Consistency reconciles them
  let init : Fin n → SInp reps lam := fun p =>
    if p = srv 1 then ja else if p = srv 2 then jb else w3 (lam := lam) h00 h01 h10
  let o : Fin n → Option (St Fact2) := fun p =>
    if p = srv 1 then some o₁ else if p = srv 2 then some o₂ else none
  have ho : ∀ p v, o p = some v → Dp.A p (init p) v := by
    intro p v hv
    by_cases h1 : p = srv 1
    · subst h1; simp only [o, init, if_pos rfl] at hv ⊢; cases hv; exact hA₁
    · by_cases h2 : p = srv 2
      · subst h2; simp only [o, init, if_neg h1, if_pos rfl] at hv ⊢; cases hv; exact hA₂
      · simp [o, h1, h2] at hv
  have hj : ∀ p, init p ≼ w3 (lam := lam) h00 h01 h10 := by
    intro p
    by_cases h1 : p = srv 1
    · simp only [init, if_pos h1]; exact IConf.Hist.restrict_le _ _ w3_down1
    · by_cases h2 : p = srv 2
      · simp only [init, if_neg h1, if_pos h2]; exact IConf.Hist.restrict_le _ _ w3_down2
      · simp only [init, if_neg h1, if_neg h2]; exact PO.refl _
  obtain ⟨u, ⟨-, H, hF, hcl⟩, hle⟩ := authorized_reconciled hn Sys hDA hPC init o ho _ hj
  have hle₁ := hle (srv 1) o₁ (by simp [o])
  have hle₂ := hle (srv 2) o₂ (by simp [o, Ne.symm hsrv])
  have a₁ : H.val 3 1 = tsInit := by
    rw [← e₁]; exact (hF _ (hle₁ _ hv₁)).2
  have a₂ : H.val 5 0 = tsInit := by
    rw [← e₂]; exact (hF _ (hle₂ _ hv₂)).2
  exact hcl (w3_myrLit H a₁ a₂)

end F1


/-! ## No permitted answer: read your writes and recency -/

section NoAnswer

/-- In `w1`, client 1's write of `x` has not reached the replica of its next
read: the read is not sticky. -/
theorem w1_not_sticky (h0 : 0 ∈ reps 0) : ¬ Reflects (reps := reps) (w1 (lam := lam) h0).1 1 1 0 := by
  intro h
  obtain ⟨d, hd, -⟩ := h 0 1 (1, 1) [0] 0 rfl (show (0, 1) ∈ w1R by decide) (by simp) h0
  rcases w1_cases hd with ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ <;> cases hx

/-- In `w1`, no output that the read-your-writes specification permits answers
the client's read: the replica holds only the initial version, which the
guarantee rules out. -/
theorem ryw_no_answer (h0 : 0 ∈ reps 0) {o : St Fact2}
    (ho : (tax (reps := reps) (lam := lam) .RYW).P (w1 h0) o) (v : Ts) : ¬ o (.rv 1 0 v) := by
  intro hv
  obtain ⟨hvis, H, hF, hc⟩ := ho
  obtain ⟨c, n, r, -, hvis'⟩ := hvis 1 0 v hv
  have hv0 := w1_vis hvis'
  have hH : H.val 1 0 = tsInit := by rw [← hv0]; exact (hF _ hv).2
  exact hc (w1_myr H hH)

/-- In `w2`, no output that the recency specification permits answers the read,
which is sticky. -/
theorem recency_no_answer (h0 : 0 ∈ reps 0) {o : St Fact2}
    (ho : (tax (reps := reps) (lam := lam) .Rec).P (w2 h0) o) (v : Ts) : ¬ o (.rv 1 0 v) :=
  fun hv => w2_absurd h0 (fun i o' => i = w2 h0 ∧ o' = o)
    (by rintro i o' ⟨rfl, rfl⟩; exact ho) ⟨rfl, rfl⟩ hv

end NoAnswer

end HATTax
end CC
