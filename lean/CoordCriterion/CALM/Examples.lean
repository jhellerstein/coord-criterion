import CoordCriterion.CALM.Lemmas

/-!
# Examples for Sections 2–3 and Appendix B

Worked examples of `sections/functional-calm.tex`, `sections/complete-calm.tex`
and `appendices/proof-machinery.tex`:

* the `k`-set agreement example used for `app:pairs-suffice` (minimal-input
  rows do not suffice even `k` at a time): `KSet.proposal_row`,
  `KSet.any_k_compatible`, `KSet.not_all_compatible`,
  `KSet.not_commonExpansion`, `KSet.not_liftedMono`,
  `KSet.atomic_k_at_a_time` (the general-`k` version of
  `app:additional-applications` is in `Appendix/Applications.lean`);
* "the pairs must range over all rows of `S`, including those at `j`"
  (`rowsAtJ_needed`, on a four-input specification `In4`);
* Corollary state-by-input does not carry over to relational specifications
  (`state_by_input_fails_relationally`);
* the election (Section `sec:election-story`): `elec_monotone`,
  `elec_consistent`, `elecEq_not_monotone`, `elecEq_not_consistent`,
  `elec_panels_exposable`, `elec_panel_b_undetermined`,
  `elec_panel_c_determined`, `elecEq_bot_seals`, `elecEq_bot_single_row`,
  `elecEq_not_confluent` (the figure panels themselves are in `Figures.lean`);
* the directed fiber `{{a},{b},{a,b,c},{a,b,d},{a,b,c,d}}` of Section
  `sec:lifted-monotonicity` (`f5_directed`, `f5_common_refinements`,
  `f5_minimal_incomparable`, `f5_compatible`).

Modeling choice (`k`-set agreement): participants `p_r = r` and values
`v_r = r` for `r : Fin (k+1)`; inputs and outputs are partial maps ordered by
extension (`PMap`).  One instance suffices for the counterexample.
-/

namespace CC
namespace CALM

/-! ## 7. The `k`-set agreement example (`app:additional-applications`)

Instance: participants `p_r = r` and values `v_r = r` for `r : Fin (k+1)`
(the paper allows further participants and values; one instance suffices for
the counterexample).  An input is a finite set of proposals, at most one per
participant, i.e. a partial map `P ⇀ Val`, ordered by inclusion (= extension);
an output is a partial decision map ordered by extension.  Both are
`PMap (k+1)`.  "Range has at most `k` values" is stated literally: the range
is contained in a list of at most `k` values. -/

/-- Partial maps `Fin n ⇀ Fin n`, ordered by extension. -/
def PMap (n : Nat) := Fin n → Option (Fin n)

instance (n : Nat) : PO (PMap n) where
  le m m' := ∀ p v, m p = some v → m' p = some v
  refl _ _ _ h := h
  trans h1 h2 p v h := h2 p v (h1 p v h)
  antisymm {a b} h1 h2 := by
    funext p
    cases ha : a p with
    | none =>
      cases hb : b p with
      | none => rfl
      | some w => rw [h2 p w hb] at ha; cases ha
    | some v => exact (h1 p v ha).symm

namespace KSet
variable (k : Nat)

theorem le_def {n : Nat} (m m' : PMap n) : m ≼ m' ↔ ∀ p v, m p = some v → m' p = some v :=
  Iff.rfl

/-- At input `I`, `m` is permitted when it decides only participants that
propose in `I`, every value in its range is proposed in `I`, and its range has
at most `k` values. -/
def Perm (I m : PMap (k+1)) : Prop :=
  (∀ p v, m p = some v → ∃ w, I p = some w) ∧
  (∀ p v, m p = some v → ∃ q, I q = some v) ∧
  ∃ L : List (Fin (k+1)), L.length ≤ k ∧ ∀ p v, m p = some v → v ∈ L

/-- The `k`-set agreement specification (total: the empty map is permitted). -/
def spec : Spec (PMap (k+1)) (PMap (k+1)) where
  S := Perm k
  total _ := ⟨fun _ => none, by simp, by simp, [], by simp, by simp⟩

/-- The single proposal / single decision `{p ↦ v}`. -/
def atom {n : Nat} (p v : Fin n) : PMap n := fun q => if q = p then some v else none

/-- The union of the proposal inputs `{(p_r, v_r)}`. -/
def J (n : Nat) : PMap n := fun p => some p

/-- `J` minus participant `r₀`. -/
def allBut {n : Nat} (r₀ : Fin n) : PMap n := fun p => if p = r₀ then none else some p

theorem atom_some {n : Nat} {p v q w : Fin n} (h : atom p v q = some w) : q = p ∧ w = v := by
  unfold atom at h
  by_cases hq : q = p
  · simp only [hq, ↓reduceIte] at h; cases h; exact ⟨hq, rfl⟩
  · simp only [hq, ↓reduceIte] at h; cases h

theorem atom_le_J {n : Nat} (r : Fin n) : atom r r ≼ J n := by
  intro p v h
  obtain ⟨rfl, rfl⟩ := atom_some h
  rfl

/-- At `p_r`'s proposal input, `{p_r ↦ v_r}` is permitted (`k ≥ 1`). -/
theorem proposal_row (hk : 1 ≤ k) (r : Fin (k+1)) : (spec k).S (atom r r) (atom r r) := by
  refine ⟨fun p v h => ⟨v, h⟩, fun p v h => ⟨p, h⟩, [r], by simpa using hk, ?_⟩
  intro p v h
  obtain ⟨_, rfl⟩ := atom_some h
  simp

/-- The union of the proposal inputs is a common expansion. -/
theorem J_common (r : Fin (k+1)) : atom r r ≼ J (k+1) := atom_le_J r

/-- Pigeonhole: a list of fewer than `n` elements of `Fin n` misses one. -/
theorem missing {n : Nat} (L : List (Fin n)) (h : L.length < n) : ∃ x, x ∉ L := by
  apply Classical.byContradiction
  intro hc
  have hs : List.finRange n ⊆ L := fun x _ =>
    Classical.byContradiction fun hx => hc ⟨x, hx⟩
  have := List.Nodup.length_le_of_subset (List.nodup_finRange n) hs
  rw [List.length_finRange] at this
  omega

/-- `J` minus one participant is permitted at `J`. -/
theorem allBut_perm (r₀ : Fin (k+1)) : (spec k).S (J (k+1)) (allBut r₀) := by
  refine ⟨fun p _ _ => ⟨p, rfl⟩, ?_, (List.finRange (k+1)).erase r₀, ?_, ?_⟩
  · intro p v h
    unfold allBut at h
    by_cases hp : p = r₀
    · simp only [hp, ↓reduceIte] at h; cases h
    · simp only [hp, ↓reduceIte] at h; cases h; exact ⟨p, rfl⟩
  · rw [List.length_erase_of_mem (List.mem_finRange r₀), List.length_finRange]; omega
  · intro p v h
    unfold allBut at h
    by_cases hp : p = r₀
    · simp only [hp, ↓reduceIte] at h; cases h
    · simp only [hp, ↓reduceIte] at h; cases h
      exact (List.mem_erase_of_ne hp).2 (List.mem_finRange p)

/-- "Any `k` of these `k+1` rows have a common refinement there": any list of
at most `k` proposal rows is compatible in `S(J)`. -/
theorem any_k_compatible (L : List (Fin (k+1))) (hL : L.length ≤ k) :
    ∃ u, (spec k).S (J (k+1)) u ∧ ∀ r ∈ L, atom r r ≼ u := by
  obtain ⟨r₀, hr₀⟩ := missing L (by omega)
  refine ⟨allBut r₀, allBut_perm k r₀, fun r hr p v h => ?_⟩
  obtain ⟨hp, hv⟩ := atom_some h
  have : r ≠ r₀ := fun e => hr₀ (e ▸ hr)
  rw [hp, hv]
  simp [allBut, this]

/-- "All `k+1` do not, since it would have `k+1` values." -/
theorem not_all_compatible :
    ¬ ∃ u, (spec k).S (J (k+1)) u ∧ ∀ r : Fin (k+1), atom r r ≼ u := by
  rintro ⟨u, ⟨_, _, L, hL, hran⟩, hall⟩
  have hs : List.finRange (k+1) ⊆ L := fun r _ =>
    hran r r (hall r r r (by simp [atom]))
  have := List.Nodup.length_le_of_subset (List.nodup_finRange (k+1)) hs
  rw [List.length_finRange] at this
  omega

/-- "So the common-expansion condition fails" (`k ≥ 1`). -/
theorem not_commonExpansion (hk : 1 ≤ k) : ¬ (spec k).CommonExpansion := by
  intro hC
  obtain ⟨u, hu, hall⟩ := hC ((List.finRange (k+1)).map fun r => (atom r r, atom r r))
    (by
      intro x hx
      obtain ⟨r, _, rfl⟩ := List.mem_map.1 hx
      exact proposal_row k hk r)
    (J (k+1))
    (by
      intro x hx
      obtain ⟨r, _, rfl⟩ := List.mem_map.1 hx
      exact atom_le_J r)
  exact not_all_compatible k ⟨u, hu, fun r =>
    hall (atom r r, atom r r) (List.mem_map.2 ⟨r, List.mem_finRange r, rfl⟩)⟩

/-- "... and the specification is not monotone." -/
theorem not_liftedMono (hk : 1 ≤ k) : ¬ (spec k).LiftedMono := by
  rw [liftedMono_iff_commonExpansion]; exact not_commonExpansion k hk

/-- A permitted output at a single-proposal input is contained in it. -/
theorem perm_atom_le {p v : Fin (k+1)} {o : PMap (k+1)} (h : (spec k).S (atom p v) o)
    {q w : Fin (k+1)} (hq : o q = some w) : q = p ∧ w = v := by
  obtain ⟨h1, h2, _⟩ := h
  obtain ⟨w', hw'⟩ := h1 q w hq
  obtain ⟨hqp, _⟩ := atom_some hw'
  obtain ⟨q', hq'⟩ := h2 q w hq
  obtain ⟨_, hwv⟩ := atom_some hq'
  exact ⟨hqp, hwv⟩

open Classical in
/-- Paragraph `app:pairs-suffice`: "restricting the families to rows at
minimal inputs does not suffice, even `k` rows at a time".  In this
specification *every* family of at most `k` rows at single-proposal inputs
(the minimal nonempty inputs), with any common expansion `j`, is compatible
in `S(j)`; yet the common-expansion condition fails (`not_commonExpansion`).
(Rows at the least input `∅` carry only the empty map, which every output
refines, so adding them changes nothing.)  A row is `(p, v, o)`, at input
`{(p,v)}`. -/
theorem atomic_k_at_a_time (rows : List (Fin (k+1) × Fin (k+1) × PMap (k+1)))
    (hlen : rows.length ≤ k)
    (hS : ∀ r ∈ rows, (spec k).S (atom r.1 r.2.1) r.2.2)
    (j : PMap (k+1)) (hj : ∀ r ∈ rows, atom r.1 r.2.1 ≼ j) :
    ∃ u, (spec k).S j u ∧ ∀ r ∈ rows, r.2.2 ≼ u := by
  let u : PMap (k+1) := fun q =>
    if ∃ r ∈ rows, (r.2.2 q).isSome then j q else none
  -- each decided coordinate of a row output is that row's proposal, present in `j`
  have key : ∀ r ∈ rows, ∀ q w, r.2.2 q = some w → q = r.1 ∧ w = r.2.1 ∧ j q = some w := by
    intro r hr q w hq
    obtain ⟨hq1, hw1⟩ := perm_atom_le k (hS r hr) hq
    refine ⟨hq1, hw1, hj r hr q w ?_⟩
    rw [hq1, hw1]
    simp [atom]
  have hu : ∀ q w, u q = some w → j q = some w ∧ ∃ r ∈ rows, w = r.2.1 := by
    intro q w h
    simp only [u] at h
    by_cases hc : ∃ r ∈ rows, (r.2.2 q).isSome
    · simp only [hc, ↓reduceIte] at h
      obtain ⟨r, hr, hs⟩ := hc
      cases hq : r.2.2 q with
      | none => rw [hq] at hs; cases hs
      | some w' =>
        obtain ⟨_, hw', hjq⟩ := key r hr q w' hq
        rw [hjq] at h; cases h
        exact ⟨hjq, r, hr, hw'⟩
    · simp only [hc, ↓reduceIte] at h; cases h
  refine ⟨u, ⟨?_, ?_, rows.map (fun r => r.2.1), by simpa using hlen, ?_⟩, ?_⟩
  · intro q w h; exact ⟨w, (hu q w h).1⟩
  · intro q w h; exact ⟨q, (hu q w h).1⟩
  · intro q w h
    obtain ⟨_, r, hr, rfl⟩ := hu q w h
    exact List.mem_map.2 ⟨r, hr, rfl⟩
  · intro r hr q w hq
    obtain ⟨_, _, hjq⟩ := key r hr q w hq
    have hc : ∃ r ∈ rows, (r.2.2 q).isSome := ⟨r, hr, by simp [hq]⟩
    show (if ∃ r ∈ rows, (r.2.2 q).isSome then j q else none) = some w
    simp [hc, hjq]

end KSet

/-! ## 8. "The pairs must range over all rows of `S`, including those at `j`"

A four-input specification: three incomparable inputs `a, b, c` below `top`.
At `a, b, c` the only output is the corresponding singleton; at `top` the
permitted outputs are the sub-maps of `J` that omit some participant.  Every
two rows *not at the common expansion* are compatible there, but the
common-expansion condition fails. -/

inductive In4 | a | b | c | top
  deriving DecidableEq

instance : PO In4 where
  le x y := x = y ∨ y = In4.top
  refl _ := Or.inl rfl
  trans := by
    intro x y z h1 h2
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp
  antisymm := by
    intro x y h1 h2
    rcases h1 with rfl | rfl
    · rfl
    · rcases h2 with h | h <;> simp_all

def In4.idx : In4 → Fin 3
  | .a => 0 | .b => 1 | .c => 2 | .top => 0

def spec4 : Spec In4 (PMap 3) where
  S i o := match i with
    | .top => (∀ p v, o p = some v → v = p) ∧ ∃ w, o w = none
    | i => o = KSet.atom i.idx i.idx
  total i := by
    cases i
    case top => exact ⟨fun _ => none, by simp, 0, rfl⟩
    all_goals exact ⟨_, rfl⟩

/-- The pair condition restricted to rows whose inputs differ from the common
expansion `j` holds. -/
theorem spec4_pairs_off_j :
    ∀ i₁ o₁ i₂ o₂ j, i₁ ≠ j → i₂ ≠ j → spec4.S i₁ o₁ → spec4.S i₂ o₂ → i₁ ≼ j → i₂ ≼ j →
      ∃ u, spec4.S j u ∧ o₁ ≼ u ∧ o₂ ≼ u := by
  intro i₁ o₁ i₂ o₂ j n1 n2 h1 h2 l1 l2
  have hj : j = .top := by
    rcases l1 with h | h
    · exact absurd h n1
    · exact h
  subst hj
  have ht1 : i₁ ≠ .top := n1
  have ht2 : i₂ ≠ .top := n2
  -- the third participant, omitted by `u`
  have hw : ∃ w : Fin 3, w ≠ i₁.idx ∧ w ≠ i₂.idx := by
    cases i₁ <;> cases i₂ <;> first
      | exact absurd rfl ht1 | exact absurd rfl ht2
      | exact ⟨2, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩
      | exact ⟨0, by decide, by decide⟩
  obtain ⟨w, hw1, hw2⟩ := hw
  have e1 : o₁ = KSet.atom i₁.idx i₁.idx := by cases i₁ <;> first | exact h1 | exact absurd rfl ht1
  have e2 : o₂ = KSet.atom i₂.idx i₂.idx := by cases i₂ <;> first | exact h2 | exact absurd rfl ht2
  subst e1; subst e2
  refine ⟨KSet.allBut w, ⟨?_, w, by simp [KSet.allBut]⟩, ?_, ?_⟩
  · intro p v h
    unfold KSet.allBut at h
    by_cases hp : p = w
    · simp only [hp, ↓reduceIte] at h; cases h
    · simp only [hp, ↓reduceIte] at h; cases h; rfl
  · intro p v h
    obtain ⟨rfl, rfl⟩ := KSet.atom_some h
    have : i₁.idx ≠ w := fun e => hw1 e.symm
    simp [KSet.allBut, this]
  · intro p v h
    obtain ⟨rfl, rfl⟩ := KSet.atom_some h
    have : i₂.idx ≠ w := fun e => hw2 e.symm
    simp [KSet.allBut, this]

theorem spec4_not_ce : ¬ spec4.CommonExpansion := by
  intro hC
  obtain ⟨u, ⟨_, w, hw⟩, hall⟩ :=
    hC [(.a, KSet.atom 0 0), (.b, KSet.atom 1 1), (.c, KSet.atom 2 2)]
      (by intro r hr; simp at hr; rcases hr with rfl | rfl | rfl <;> rfl) .top
      (by intro r hr; simp at hr; rcases hr with rfl | rfl | rfl <;> exact Or.inr rfl)
  have h0 := hall _ (List.mem_cons_self ..) 0 0 (by simp [KSet.atom])
  have h1 := hall _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) 1 1 (by simp [KSet.atom])
  have h2 := hall _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    2 2 (by simp [KSet.atom])
  have : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases this w with rfl | rfl | rfl
  · rw [h0] at hw; cases hw
  · rw [h1] at hw; cases hw
  · rw [h2] at hw; cases hw

/-- Pairs not ranging over rows at `j` do not suffice. -/
theorem rowsAtJ_needed :
    (∀ i₁ o₁ i₂ o₂ j, i₁ ≠ j → i₂ ≠ j → spec4.S i₁ o₁ → spec4.S i₂ o₂ → i₁ ≼ j → i₂ ≼ j →
      ∃ u, spec4.S j u ∧ o₁ ≼ u ∧ o₂ ≼ u) ∧ ¬ spec4.CommonExpansion :=
  ⟨spec4_pairs_off_j, spec4_not_ce⟩

/-! ## 9. Corollary state-by-input does not carry over to relational specs -/

inductive Pt | pt
inductive Two | lo | hi

instance : PO Pt where
  le _ _ := True
  refl _ := trivial
  trans _ _ := trivial
  antisymm {a b} _ _ := by cases a; cases b; rfl

instance : PO Two where
  le x y := x = .lo ∨ y = .hi
  refl x := by cases x <;> simp
  trans := by
    intro x y z h1 h2
    cases x <;> cases y <;> cases z <;> simp_all
  antisymm := by
    intro x y h1 h2
    cases x <;> cases y <;> simp_all

/-- One input, two outputs `lo ≼ hi`, both permitted. -/
def specTwo : Spec Pt Two where
  S _ _ := True
  total _ := ⟨.lo, trivial⟩

/-- Section `sec:complete-calm-theorem`, last paragraph: a consistent
relational specification in which a run ends at a non-canonical state
(emitting `hi` retires the row `(pt, lo)`). -/
theorem state_by_input_fails_relationally :
    specTwo.Consistent ∧ ∃ τ : State specTwo, IsRun τ ∧ τ ≠ canon specTwo τ.cur := by
  refine ⟨?_, ?_⟩
  · rw [complete_calm_paper]
    intro rows _ _ _
    exact ⟨.hi, trivial, fun r _ => Or.inr rfl⟩
  · let τ := outputState (canon specTwo .pt) .hi ⟨trivial, trivial⟩
    refine ⟨τ, ⟨.pt, _, Exec.cons (step_outputState _ _ _) (Exec.nil _)⟩, fun h => ?_⟩
    have hR : τ.R .pt .lo := by
      rw [h]; exact ⟨trivial, trivial⟩
    rcases hR.2 with h | h <;> cases h

/-! ## 10. The election example (Section `sec:election-story`)

Three voters, ballots for `x` or `y`; the input is the ballots received so
far (`none` = dot), ordered by extension; the output is the candidate with
two ballots, or `⊥`.  `Res` carries the refinement order (`⊥ ≼` everything,
`x`, `y` incomparable); `ResE` the equality order. -/

inductive Cand | x | y
  deriving DecidableEq

structure Ballots where
  b1 : Option Cand
  b2 : Option Cand
  b3 : Option Cand
  deriving DecidableEq

abbrev oleq (a b : Option Cand) : Prop := a = none ∨ a = b

abbrev bLe (i j : Ballots) : Prop := oleq i.b1 j.b1 ∧ oleq i.b2 j.b2 ∧ oleq i.b3 j.b3

theorem oleq_trans {a b c : Option Cand} (h1 : oleq a b) (h2 : oleq b c) : oleq a c := by
  rcases h1 with rfl | rfl
  · exact Or.inl rfl
  · exact h2

theorem oleq_antisymm {a b : Option Cand} (h1 : oleq a b) (h2 : oleq b a) : a = b := by
  rcases h1 with rfl | rfl
  · rcases h2 with rfl | rfl <;> rfl
  · rfl

theorem oleq_some {c : Cand} {d : Option Cand} (h : oleq (some c) d) : d = some c := by
  rcases h with h | h
  · cases h
  · exact h.symm

instance : PO Ballots where
  le := bLe
  refl _ := ⟨Or.inr rfl, Or.inr rfl, Or.inr rfl⟩
  trans h1 h2 := ⟨oleq_trans h1.1 h2.1, oleq_trans h1.2.1 h2.2.1, oleq_trans h1.2.2 h2.2.2⟩
  antisymm {a b} h1 h2 := by
    cases a; cases b
    simp only [Ballots.mk.injEq]
    exact ⟨oleq_antisymm h1.1 h2.1, oleq_antisymm h1.2.1 h2.2.1, oleq_antisymm h1.2.2 h2.2.2⟩

instance (i j : Ballots) : Decidable (i ≼ j) := inferInstanceAs (Decidable (bLe i j))

inductive Res | bot | win (c : Cand)
  deriving DecidableEq

abbrev resLe (a b : Res) : Prop := a = .bot ∨ a = b

instance : PO Res where
  le := resLe
  refl _ := Or.inr rfl
  trans := by
    intro a b c h1 h2
    rcases h1 with rfl | rfl
    · exact Or.inl rfl
    · exact h2
  antisymm := by
    intro a b h1 h2
    rcases h1 with rfl | rfl
    · rcases h2 with h | h <;> simp_all
    · rfl

structure ResE where
  r : Res
  deriving DecidableEq

instance : PO ResE where
  le a b := a = b
  refl _ := rfl
  trans h1 h2 := h1.trans h2
  antisymm h _ := h

def cnt (c : Cand) (i : Ballots) : Nat :=
  (if i.b1 = some c then 1 else 0) + (if i.b2 = some c then 1 else 0) +
  (if i.b3 = some c then 1 else 0)

def winner (i : Ballots) : Res :=
  if 2 ≤ cnt .x i then .win .x else if 2 ≤ cnt .y i then .win .y else .bot

/-- The election, under the refinement order. -/
def elec : Spec Ballots Res where
  S i o := o = winner i
  total _ := ⟨_, rfl⟩

/-- The election, under the equality order. -/
def elecEq : Spec Ballots ResE where
  S i o := o = ⟨winner i⟩
  total _ := ⟨_, rfl⟩

theorem elec_functional : elec.Functional := fun _ _ _ h h' => h.trans h'.symm
theorem elecEq_functional : elecEq.Functional := fun _ _ _ h h' => h.trans h'.symm

theorem winner_mono_raw : ∀ i j : Ballots, bLe i j → resLe (winner i) (winner j) := by
  intro ⟨a1, a2, a3⟩ ⟨c1, c2, c3⟩
  rcases a1 with _ | _ | _ <;> rcases a2 with _ | _ | _ <;> rcases a3 with _ | _ | _ <;>
  rcases c1 with _ | _ | _ <;> rcases c2 with _ | _ | _ <;> rcases c3 with _ | _ | _ <;>
  decide

/-- The election is monotone, hence consistent (Functional CALM). -/
theorem elec_monotone : elec.MonotoneF := by
  intro i j o u hij hio hju
  subst hio; subst hju
  exact winner_mono_raw i j hij

theorem elec_consistent : elec.Consistent := (functional_calm elec_functional).2 elec_monotone

def bxd : Ballots := ⟨some .x, none, none⟩          -- x··
def bxy : Ballots := ⟨some .x, some .y, none⟩       -- xy·
def bxyx : Ballots := ⟨some .x, some .y, some .x⟩   -- xyx
def bxx : Ballots := ⟨some .x, some .x, none⟩       -- xx·

/-- `xy· ≼ xyx`, `f(xy·) = ⊥`, `f(xyx) = x`. -/
theorem bxy_le_bxyx : bxy ≼ bxyx := by decide
theorem winner_bxy : winner bxy = .bot := by decide
theorem winner_bxyx : winner bxyx = .win .x := by decide

/-- Under the equality order the election is not monotone, hence not
consistent. -/
theorem elecEq_not_monotone : ¬ elecEq.MonotoneF := by
  intro h
  have := h bxy bxyx ⟨winner bxy⟩ ⟨winner bxyx⟩ bxy_le_bxyx rfl rfl
  rw [winner_bxy, winner_bxyx] at this
  cases this

theorem elecEq_not_consistent : ¬ elecEq.Consistent := fun h =>
  elecEq_not_monotone ((functional_calm elecEq_functional).1 h)

/-- Panels (a)–(c): `⊥` is exposable at `σ_S(x··)` and `σ_S(xy·)`, and `x` at
`σ_S(xx·)` (monotone order). -/
theorem elec_panels_exposable :
    Exposable (canon elec bxd) .bot ∧ Exposable (canon elec bxy) .bot ∧
      Exposable (canon elec bxx) (.win .x) := by
  have hb := (functional_exposure_boundary elec_functional).1 elec_monotone
  refine ⟨hb _ ⟨_, [], ExecCF.nil _⟩ _ ⟨(by decide : Res.bot = winner bxd), PO.refl _⟩,
          hb _ ⟨_, [], ExecCF.nil _⟩ _ ⟨(by decide : Res.bot = winner bxy), PO.refl _⟩,
          hb _ ⟨_, [], ExecCF.nil _⟩ _ ⟨(by decide : Res.win .x = winner bxx), PO.refl _⟩⟩

/-- Panel (b) is undetermined (`⊥` at `xy·` and `x` at `xyx` remain). -/
theorem elec_panel_b_undetermined : ¬ Determined (canon elec bxy) := by
  rintro ⟨o, h⟩
  have h1 := h bxy (winner bxy) ⟨rfl, PO.refl _⟩
  have h2 := h bxyx (winner bxyx) ⟨rfl, bxy_le_bxyx⟩
  rw [winner_bxy] at h1; rw [winner_bxyx, ← h1] at h2
  cases h2

/-- Panel (c) is determined: every row at an expansion of `xx·` has output `x`. -/
theorem elec_panel_c_determined : Determined (canon elec bxx) := by
  refine ⟨.win .x, fun k u hk => ?_⟩
  obtain ⟨hS, hle⟩ := hk
  subst hS
  obtain ⟨c1, c2, c3⟩ := k
  obtain ⟨h1, h2, _⟩ := hle
  simp only [bxx] at h1 h2
  have e1 := oleq_some h1
  have e2 := oleq_some h2
  subst e1; subst e2
  rcases c3 with _ | _ | _ <;> decide

/-- Equality-order variant (Fig. `fig:nonmonotone-frame`): `output(⊥)` at
`σ_S(xy·)` seals `xyx` ... -/
theorem elecEq_bot_seals : Sealed (canon elecEq bxy) ⟨.bot⟩ bxyx ⟨winner bxyx⟩ :=
  nonmono_seals elecEq_functional bxy_le_bxyx
    (show (⟨Res.bot⟩ : ResE) = ⟨winner bxy⟩ by rw [winner_bxy]) rfl
    (by rw [winner_bxyx]; intro h; cases h)

/-- ... and leaves the single row `(xy·, ⊥)`
(`S[in ⪰ xy·, out ⪰ ⊥]`, the example after Lemma `lem:run-residual`). -/
theorem elecEq_bot_single_row (k : Ballots) (o : ResE) :
    outputTable (canon elecEq bxy) ⟨.bot⟩ k o ↔ (k = bxy ∧ o = ⟨.bot⟩) := by
  constructor
  · rintro ⟨⟨hS, hle⟩, hbo⟩
    subst hbo
    obtain ⟨c1, c2, c3⟩ := k
    obtain ⟨h1, h2, h3⟩ := hle
    have e1 := oleq_some h1
    have e2 := oleq_some h2
    subst e1; subst e2
    have hS' : (⟨Res.bot⟩ : ResE) = ⟨winner ⟨some .x, some .y, c3⟩⟩ := hS
    rcases c3 with _ | _ | _
    · exact ⟨rfl, rfl⟩
    · exact absurd hS' (by decide)
    · exact absurd hS' (by decide)
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨by show (⟨Res.bot⟩ : ResE) = ⟨winner bxy⟩; rw [winner_bxy], PO.refl _⟩, rfl⟩

/-- "A run that emits `⊥` at `xy·` and one that receives `xyx` cannot be
reconciled at `xyx`" (equality order). -/
theorem elecEq_not_confluent :
    ¬ ConfluentAt [outputState (canon elecEq bxy) ⟨.bot⟩ ((elecEq_bot_single_row bxy _).2 ⟨rfl, rfl⟩).1,
                   canon elecEq bxyx] bxyx := by
  intro h
  have hrun : ∀ σ ∈ [outputState (canon elecEq bxy) ⟨.bot⟩
      ((elecEq_bot_single_row bxy _).2 ⟨rfl, rfl⟩).1, canon elecEq bxyx], IsRun σ := by
    intro σ hσ
    rcases List.mem_cons.1 hσ with rfl | hσ
    · exact ⟨bxy, _, Exec.cons (step_outputState _ _ _) (Exec.nil _)⟩
    · rcases List.mem_cons.1 hσ with rfl | hσ
      · exact ⟨bxyx, [], Exec.nil _⟩
      · cases hσ
  have hcur : ∀ σ ∈ [outputState (canon elecEq bxy) ⟨.bot⟩
      ((elecEq_bot_single_row bxy _).2 ⟨rfl, rfl⟩).1, canon elecEq bxyx], σ.cur ≼ bxyx := by
    intro σ hσ
    rcases List.mem_cons.1 hσ with rfl | hσ
    · exact bxy_le_bxyx
    · rcases List.mem_cons.1 hσ with rfl | hσ
      · exact PO.refl _
      · cases hσ
  obtain ⟨u, _, hall⟩ := (survivor_test _ hrun bxyx hcur).1 h
  have := (elecEq_bot_single_row bxyx u).1 (hall _ (List.mem_cons_self ..))
  exact absurd this.1 (by decide)

/-! ## 11. The directed-fiber example (Section `sec:lifted-monotonicity`)

The fiber `{{a},{b},{a,b,c},{a,b,d},{a,b,c,d}}` under inclusion. -/

inductive F5 | a | b | abc | abd | abcd
  deriving DecidableEq

/-- Membership of `a, b, c, d` (as `0,1,2,3`). -/
def F5.mem : F5 → Fin 4 → Bool
  | .a, n => n == 0
  | .b, n => n == 1
  | .abc, n => n == 0 || n == 1 || n == 2
  | .abd, n => n == 0 || n == 1 || n == 3
  | .abcd, _ => true

/-- Inclusion, as a decidable proposition. -/
abbrev F5.sub (s t : F5) : Prop :=
  (s.mem 0 → t.mem 0) ∧ (s.mem 1 → t.mem 1) ∧ (s.mem 2 → t.mem 2) ∧ (s.mem 3 → t.mem 3)

instance : PO F5 where
  le := F5.sub
  refl s := by cases s <;> decide
  trans := by intro s t w; cases s <;> cases t <;> cases w <;> decide
  antisymm := by intro s t; cases s <;> cases t <;> decide

instance (s t : F5) : Decidable (s ≼ t) := inferInstanceAs (Decidable (F5.sub s t))

/-- The fiber is directed: `{a,b,c,d}` refines every member. -/
theorem f5_directed : JointLift (fun _ : F5 => True) (fun _ : F5 => True) := by
  intro X _ _
  exact ⟨.abcd, trivial, fun x _ => by cases x <;> decide⟩

/-- `{a}` and `{b}` have exactly the common refinements `{a,b,c}`, `{a,b,d}`,
`{a,b,c,d}` in the fiber; the two minimal ones are incomparable. -/
theorem f5_common_refinements (u : F5) : (F5.a ≼ u ∧ F5.b ≼ u) ↔ (u = .abc ∨ u = .abd ∨ u = .abcd) := by
  cases u <;> decide

theorem f5_minimal_incomparable :
    ¬ (F5.abc ≼ F5.abd) ∧ ¬ (F5.abd ≼ F5.abc) ∧
    (∀ u, F5.a ≼ u → F5.b ≼ u → u ≼ F5.abc → u = F5.abc) ∧
    (∀ u, F5.a ≼ u → F5.b ≼ u → u ≼ F5.abd → u = F5.abd) := by
  refine ⟨by decide, by decide, ?_, ?_⟩ <;> intro u <;> cases u <;> decide

/-- `{a,b,c}` and `{a,b,d}` are incomparable but compatible. -/
theorem f5_compatible : CompatibleIn (fun _ : F5 => True) [F5.abc, F5.abd] :=
  ⟨.abcd, trivial, fun x hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · decide
    · rcases List.mem_cons.1 hx with rfl | hx
      · decide
      · cases hx⟩

end CALM
end CC
