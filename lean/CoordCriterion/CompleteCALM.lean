/-
Section 3: Complete CALM.

* `liftedMono_iff_relMono_directed` : Lifted Monotonicity ↔ Relational
  Monotonicity ∧ Directed Outputs (paragraph after Def. lifted-monotonicity).
* `liftedMono_iff_commonExpansion` : Prop. common-expansion-form.
* `lifted_exposure_test` : Prop. exposability (lifted exposure test).
* `complete_calm` : Thm. complete-calm.
* `exposure_boundary` : Prop. exposure-boundary.
* Facts about the lifted output event (Def. lifted-output-event and the
  paragraph after it): classification, disjointness, independence of the two
  commitments, functional case.
-/
import CoordCriterion.Core
import CoordCriterion.Runs

namespace CC

variable {I O : Type} [PO I] [PO O]

/-! ### Lifted Monotonicity = Relational Monotonicity + Directed Outputs -/

/-- Accumulator lemma: from RelMono and Directed Outputs, any finite list in
`S i` together with a seed `u0 ∈ S j` has a common refinement in `S j`. -/
theorem relMono_directed_acc {sp : Spec I O} (hR : sp.RelMono) (hD : sp.DirectedOutputs)
    {i j : I} (hij : i ≼ j) :
    ∀ X : List O, (∀ x ∈ X, sp.S i x) → ∀ u0, sp.S j u0 →
      ∃ u, sp.S j u ∧ u0 ≼ u ∧ ∀ x ∈ X, x ≼ u := by
  intro X
  induction X with
  | nil => intro _ u0 hu0; exact ⟨u0, hu0, PO.refl _, by simp⟩
  | cons x X ih =>
    intro hX u0 hu0
    obtain ⟨u1, hu1, h01, hX1⟩ := ih (fun y hy => hX y (List.mem_cons_of_mem _ hy)) u0 hu0
    obtain ⟨v, hv, hxv⟩ := hR i j x hij (hX x (List.mem_cons_self ..))
    obtain ⟨w, hw, hall⟩ := hD j [u1, v] (by simp) (by simp [hu1, hv])
    have h1w : u1 ≼ w := hall u1 (by simp)
    have hvw : v ≼ w := hall v (by simp)
    refine ⟨w, hw, PO.trans h01 h1w, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact PO.trans hxv hvw
    · exact PO.trans (hX1 y hy) h1w

theorem liftedMono_iff_relMono_directed (sp : Spec I O) :
    sp.LiftedMono ↔ sp.RelMono ∧ sp.DirectedOutputs := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i j o hij ho
      obtain ⟨u, hu, hall⟩ := h i j hij [o] (by simp) (by simp [ho])
      exact ⟨u, hu, hall o (by simp)⟩
    · intro i
      exact h i i (PO.refl i)
  · rintro ⟨hR, hD⟩ i j hij X hne hX
    match X, hne with
    | x :: X', _ =>
      obtain ⟨u0, hu0, hxu0⟩ := hR i j x hij (hX x (List.mem_cons_self ..))
      obtain ⟨u, hu, h0u, hall⟩ := relMono_directed_acc hR hD hij (x :: X') hX u0 hu0
      exact ⟨u, hu, hall⟩

/-! ### Prop. common-expansion-form -/

theorem liftedMono_iff_commonExpansion (sp : Spec I O) :
    sp.LiftedMono ↔ sp.CommonExpansion := by
  constructor
  · intro hL
    obtain ⟨hR, hD⟩ := (liftedMono_iff_relMono_directed sp).1 hL
    intro rows hrows j hj
    -- accumulate one row at a time, starting from a totality witness
    have acc : ∀ rows : List (I × O), (∀ r ∈ rows, sp.S r.1 r.2) →
        (∀ r ∈ rows, r.1 ≼ j) → ∃ u, sp.S j u ∧ ∀ r ∈ rows, r.2 ≼ u := by
      intro rows
      induction rows with
      | nil => intro _ _; obtain ⟨u, hu⟩ := sp.total j; exact ⟨u, hu, by simp⟩
      | cons r rs ih =>
        intro hS hJ
        obtain ⟨u1, hu1, hall⟩ := ih (fun r' h => hS r' (List.mem_cons_of_mem _ h))
          (fun r' h => hJ r' (List.mem_cons_of_mem _ h))
        obtain ⟨v, hv, hrv⟩ := hR r.1 j r.2 (hJ r (List.mem_cons_self ..))
          (hS r (List.mem_cons_self ..))
        obtain ⟨w, hw, hw2⟩ := hD j [u1, v] (by simp) (by simp [hu1, hv])
        refine ⟨w, hw, ?_⟩
        intro r' hr'
        rcases List.mem_cons.1 hr' with rfl | hr'
        · exact PO.trans hrv (hw2 v (by simp))
        · exact PO.trans (hall r' hr') (hw2 u1 (by simp))
    exact acc rows hrows hj
  · intro hC i j hij X _ hX
    obtain ⟨u, hu, hall⟩ := hC (X.map fun x => (i, x))
      (by intro r hr; obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr; exact hX x hx) j
      (by intro r hr; obtain ⟨x, _, rfl⟩ := List.mem_map.1 hr; exact hij)
    exact ⟨u, hu, fun x hx => hall (i, x) (List.mem_map.2 ⟨x, hx, rfl⟩)⟩

/-! ### Lifted output event: classification of ruled-out rows -/

section Classification
variable {sp : Spec I O} (σ : State sp) (o : O)

/-- Every row in `Sealed`, `Retired`, `Rejected` is ruled out by `o`. -/
theorem sealed_ruledOut {k x} (h : Sealed σ o k x) : σ.R k x ∧ ¬ o ≼ x :=
  ⟨h.1, fun hox => h.2 ⟨x, h.1, hox⟩⟩

theorem sealed_retired_disjoint {k x} : ¬ (Sealed σ o k x ∧ Retired σ o k x) := by
  rintro ⟨hs, hr⟩
  obtain ⟨u, hu, hou, _⟩ := hr.2.2
  exact hs.2 ⟨u, hu, hou⟩

theorem sealed_rejected_disjoint {k x} : ¬ (Sealed σ o k x ∧ Rejected σ o k x) :=
  fun ⟨hs, hj⟩ => hj.2.2.1 hs

theorem retired_rejected_disjoint {k x} : ¬ (Retired σ o k x ∧ Rejected σ o k x) :=
  fun ⟨hr, hj⟩ => hj.2.2.2 hr

/-- The three classes partition exactly the ruled-out rows `R \ R[out ⪰ o]`. -/
theorem ruledOut_iff (k : I) (x : O) :
    (σ.R k x ∧ ¬ outputTable σ o k x) ↔
      (Sealed σ o k x ∨ Retired σ o k x ∨ Rejected σ o k x) := by
  constructor
  · rintro ⟨hR, hno⟩
    have hox : ¬ o ≼ x := fun h => hno ⟨hR, h⟩
    by_cases hs : Sealed σ o k x
    · exact Or.inl hs
    by_cases hr : Retired σ o k x
    · exact Or.inr (Or.inl hr)
    exact Or.inr (Or.inr ⟨hR, hox, hs, hr⟩)
  · intro h
    have : σ.R k x ∧ ¬ o ≼ x := by
      rcases h with hs | hr | hj
      · exact sealed_ruledOut σ o hs
      · exact ⟨hr.1, hr.2.1⟩
      · exact ⟨hj.1, hj.2.1⟩
    exact ⟨this.1, fun h' => this.2 h'.2⟩

/-- `Exposable` (every ruled-out row is retired) is the paper's
"applies no commitment": `Sealed_o` and `Rejected_o` are empty. -/
theorem exposable_iff_no_commitment :
    Exposable σ o ↔ (∀ k x, ¬ Sealed σ o k x) ∧ (∀ k x, ¬ Rejected σ o k x) := by
  constructor
  · intro h
    refine ⟨fun k x hs => ?_, fun k x hj => ?_⟩
    · obtain ⟨u, hu, hou, _⟩ := h k x hs.1 (sealed_ruledOut σ o hs).2
      exact hs.2 ⟨u, hu, hou⟩
    · exact hj.2.2.2 ⟨hj.1, hj.2.1, h k x hj.1 hj.2.1⟩
  · rintro ⟨hs, hj⟩ k x hR hox
    rcases (ruledOut_iff σ o k x).1 ⟨hR, fun h => hox h.2⟩ with h | h | h
    · exact absurd h (hs k x)
    · exact h.2.2
    · exact absurd h (hj k x)

/-- Sealing depends only on the input: a sealed input has all its rows sealed. -/
theorem sealed_input {k x x'} (h : Sealed σ o k x) (h' : σ.R k x') : Sealed σ o k x' :=
  ⟨h', h.2⟩

end Classification

/-! ### The two commitments as states, and their independence -/

section Commitments
variable {sp : Spec I O}

/-- The seal commitment `s_o(i,R) = (i, R \ Sealed_o)`, for `o ∈ R(i)`. -/
def sealState (σ : State sp) (o : O) (ho : σ.R σ.cur o) : State sp where
  cur := σ.cur
  R := fun k x => σ.R k x ∧ ¬ Sealed σ o k x
  sub := fun k x h => σ.sub k x h.1
  hasCur := ⟨o, ho, fun hs => hs.2 ⟨o, ho, PO.refl o⟩⟩
  above := fun k x h => σ.above k x h.1

/-- The choice commitment `c_o(i,R) = (i, R \ Rejected_o)`, for `o ∈ R(i)`. -/
def chooseState (σ : State sp) (o : O) (ho : σ.R σ.cur o) : State sp where
  cur := σ.cur
  R := fun k x => σ.R k x ∧ ¬ Rejected σ o k x
  sub := fun k x h => σ.sub k x h.1
  hasCur := ⟨o, ho, fun hj => hj.2.1 (PO.refl o)⟩
  above := fun k x h => σ.above k x h.1

/-- Helper: the kept rows `R[out ⪰ o]` are unchanged by either commitment. -/
theorem sealState_kept (σ : State sp) (o : O) (ho) (k : I) (u : O) :
    ((sealState σ o ho).R k u ∧ o ≼ u) ↔ (σ.R k u ∧ o ≼ u) := by
  simp only [sealState]
  constructor
  · rintro ⟨⟨h, _⟩, hou⟩; exact ⟨h, hou⟩
  · rintro ⟨h, hou⟩; exact ⟨⟨h, fun hs => hs.2 ⟨u, h, hou⟩⟩, hou⟩

theorem chooseState_kept (σ : State sp) (o : O) (ho) (k : I) (u : O) :
    ((chooseState σ o ho).R k u ∧ o ≼ u) ↔ (σ.R k u ∧ o ≼ u) := by
  simp only [chooseState]
  constructor
  · rintro ⟨⟨h, _⟩, hou⟩; exact ⟨h, hou⟩
  · rintro ⟨h, hou⟩; exact ⟨⟨h, fun hj => hj.2.1 hou⟩, hou⟩

/-- Removing the sealed rows leaves `Retired_o` unchanged. -/
theorem seal_retired (σ : State sp) (o : O) (ho) (k : I) (x : O) :
    Retired (sealState σ o ho) o k x ↔ Retired σ o k x := by
  have hk := sealState_kept σ o ho k
  constructor
  · rintro ⟨h, hox, u, hu, hou, hxu⟩
    exact ⟨h.1, hox, u, ((hk u).1 ⟨hu, hou⟩).1, hou, hxu⟩
  · rintro ⟨h, hox, u, hu, hou, hxu⟩
    exact ⟨⟨h, fun hs => hs.2 ⟨u, hu, hou⟩⟩, hox, u, ((hk u).2 ⟨hu, hou⟩).1, hou, hxu⟩

/-- Removing the sealed rows leaves `Rejected_o` unchanged. -/
theorem seal_rejected (σ : State sp) (o : O) (ho) (k : I) (x : O) :
    Rejected (sealState σ o ho) o k x ↔ Rejected σ o k x := by
  have hret := seal_retired σ o ho k x
  have hk := sealState_kept σ o ho k
  constructor
  · rintro ⟨h, hox, _, hnr⟩
    exact ⟨h.1, hox, h.2, fun hr => hnr (hret.2 hr)⟩
  · rintro ⟨h, hox, hns, hnr⟩
    refine ⟨⟨h, hns⟩, hox, ?_, fun hr => hnr (hret.1 hr)⟩
    -- `k` is not sealed in σ, so it keeps a row refining `o`, also after sealing
    intro hs'
    apply hns
    refine ⟨h, ?_⟩
    rintro ⟨u, hu, hou⟩
    exact hs'.2 ⟨u, ((hk u).2 ⟨hu, hou⟩).1, hou⟩

/-- After sealing, nothing is sealed. -/
theorem seal_sealed_empty (σ : State sp) (o : O) (ho) (k : I) (x : O) :
    ¬ Sealed (sealState σ o ho) o k x := by
  rintro ⟨⟨_, hns⟩, hno⟩
  apply hns
  refine ⟨‹_›, ?_⟩
  rintro ⟨u, hu, hou⟩
  exact hno ⟨u, ((sealState_kept σ o ho k u).2 ⟨hu, hou⟩).1, hou⟩

/-- Removing the rejected rows leaves `Sealed_o` unchanged. -/
theorem choose_sealed (σ : State sp) (o : O) (ho) (k : I) (x : O) :
    Sealed (chooseState σ o ho) o k x ↔ Sealed σ o k x := by
  have hk := chooseState_kept σ o ho k
  constructor
  · rintro ⟨h, hno⟩
    exact ⟨h.1, fun ⟨u, hu, hou⟩ => hno ⟨u, ((hk u).2 ⟨hu, hou⟩).1, hou⟩⟩
  · rintro ⟨h, hno⟩
    exact ⟨⟨h, fun hj => hj.2.2.1 ⟨h, hno⟩⟩,
      fun ⟨u, hu, hou⟩ => hno ⟨u, ((hk u).1 ⟨hu, hou⟩).1, hou⟩⟩

/-- Removing the rejected rows leaves `Retired_o` unchanged. -/
theorem choose_retired (σ : State sp) (o : O) (ho) (k : I) (x : O) :
    Retired (chooseState σ o ho) o k x ↔ Retired σ o k x := by
  have hk := chooseState_kept σ o ho k
  constructor
  · rintro ⟨h, hox, u, hu, hou, hxu⟩
    exact ⟨h.1, hox, u, ((hk u).1 ⟨hu, hou⟩).1, hou, hxu⟩
  · intro hr
    obtain ⟨h, hox, u, hu, hou, hxu⟩ := hr
    exact ⟨⟨h, fun hj => hj.2.2.2 ⟨h, hox, u, hu, hou, hxu⟩⟩, hox, u,
      ((hk u).2 ⟨hu, hou⟩).1, hou, hxu⟩

/-- After choosing, nothing is rejected. -/
theorem choose_rejected_empty (σ : State sp) (o : O) (ho) (k : I) (x : O) :
    ¬ Rejected (chooseState σ o ho) o k x := by
  rintro ⟨⟨h, hnj⟩, hox, hns, hnr⟩
  exact hnj ⟨h, hox, fun hs => hns ((choose_sealed σ o ho k x).2 hs),
    fun hr => hnr ((choose_retired σ o ho k x).2 hr)⟩

/-- The two commitments commute: both orders give `R \ (Sealed_o ∪ Rejected_o)`. -/
theorem seal_choose_comm (σ : State sp) (o : O) (ho : σ.R σ.cur o)
    (h1 : (sealState σ o ho).R (sealState σ o ho).cur o)
    (h2 : (chooseState σ o ho).R (chooseState σ o ho).cur o) :
    (chooseState (sealState σ o ho) o h1).R = (sealState (chooseState σ o ho) o h2).R := by
  funext k x
  apply propext
  -- unfold only the outer layer; use the invariance lemmas for the inner one
  show ((sealState σ o ho).R k x ∧ ¬ Rejected (sealState σ o ho) o k x) ↔
       ((chooseState σ o ho).R k x ∧ ¬ Sealed (chooseState σ o ho) o k x)
  rw [seal_rejected, choose_sealed]
  simp only [sealState, chooseState]
  constructor
  · rintro ⟨⟨a, b⟩, c⟩; exact ⟨⟨a, c⟩, b⟩
  · rintro ⟨⟨a, b⟩, c⟩; exact ⟨⟨a, c⟩, b⟩

/-- The choice commitment only narrows fibers: every input carrying a rejected
row keeps a row refining `o`. -/
theorem choice_narrows (σ : State sp) (o : O) {k x} (hj : Rejected σ o k x) :
    ∃ u, σ.R k u ∧ o ≼ u := by
  apply Classical.byContradiction
  intro hno
  exact hj.2.2.1 ⟨hj.1, hno⟩

/-- In a functional specification, `Retired_o` and `Rejected_o` are empty. -/
theorem functional_retired_rejected_empty (hF : sp.Functional) (σ : State sp) (o : O)
    (k : I) (x : O) : ¬ Retired σ o k x ∧ ¬ Rejected σ o k x := by
  refine ⟨?_, ?_⟩
  · rintro ⟨h, hox, u, hu, hou, _⟩
    have : x = u := hF k x u (σ.sub _ _ h) (σ.sub _ _ hu)
    subst this; exact hox hou
  · rintro ⟨h, hox, hns, _⟩
    apply hns
    refine ⟨h, ?_⟩
    rintro ⟨u, hu, hou⟩
    have : x = u := hF k x u (σ.sub _ _ h) (σ.sub _ _ hu)
    subst this; exact hox hou

end Commitments

/-! ### Prop. exposability: the lifted exposure test -/

/-- **Lifted exposure test.** `o ∈ R(i)` is exposable at `(i,R)` iff for every
legal `j ⪰ i` and `x ∈ R(j)` some `u ∈ R(j)` refines both `o` and `x`.
(Exposability is equivalently "no commitment", `exposable_iff_no_commitment`.) -/
theorem lifted_exposure_test {sp : Spec I O} (σ : State sp) (o : O) :
    Exposable σ o ↔
      ∀ j, σ.cur ≼ j → ∀ x, σ.R j x → ∃ u, σ.R j u ∧ o ≼ u ∧ x ≼ u := by
  constructor
  · intro h j _ x hx
    by_cases hox : o ≼ x
    · exact ⟨x, hx, hox, PO.refl x⟩
    · exact h j x hx hox
  · intro h k x hx _
    exact h k (σ.above _ _ hx) x hx

/-! ### Thm. Complete CALM -/

/-- From a run state, a row `(j,u)` with `j ⪰ cur` survives once `u` refines
some output at the current input. -/
theorem run_survive {sp : Spec I O} {σ : State sp} (hσ : IsRun σ) {j : I} {u v : O}
    (hcj : σ.cur ≼ j) (hju : sp.S j u) (hv : σ.R σ.cur v) (hvu : v ≼ u) : σ.R j u := by
  obtain ⟨E, hE⟩ := hσ.residual
  have hEv := ((hE _ _).1 hv).2.2
  exact (hE j u).2 ⟨hju, hcj, fun o ho => PO.trans (hEv o ho) hvu⟩

theorem commonExpansion_consistent {sp : Spec I O} (hC : sp.CommonExpansion) :
    sp.Consistent := by
  intro fam hrun j hj
  -- one row per run: (cur, some output still at cur), which refines all emitted
  let pick : State sp → I × O := fun σ => (σ.cur, σ.hasCur.choose)
  obtain ⟨u, hu, hall⟩ := hC (fam.map pick)
    (by
      intro r hr
      obtain ⟨σ, _, rfl⟩ := List.mem_map.1 hr
      exact σ.sub _ _ σ.hasCur.choose_spec) j
    (by
      intro r hr
      obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hr
      exact hj σ hσ)
  refine (survivor_test fam hrun j hj).2 ⟨u, hu, fun σ hσ => ?_⟩
  exact run_survive (hrun σ hσ) (hj σ hσ) hu σ.hasCur.choose_spec
    (hall (pick σ) (List.mem_map.2 ⟨σ, hσ, rfl⟩))

theorem meetState_isRun (sp : Spec I O) (i : I) (o : O) (h : sp.S i o) :
    IsRun (meetState sp i o h) :=
  ⟨i, reach_meet (residual_canon sp i) (show (canon sp i).R i o from ⟨h, PO.refl i⟩)⟩

theorem consistent_commonExpansion {sp : Spec I O} (hK : sp.Consistent) :
    sp.CommonExpansion := by
  intro rows
  induction rows with
  | nil =>
    intro _ j _
    obtain ⟨u, hu⟩ := sp.total j
    exact ⟨u, hu, by simp⟩
  | cons r rs ih =>
    intro hS j hJ
    obtain ⟨u1, hu1, hall⟩ := ih (fun r' h => hS r' (List.mem_cons_of_mem _ h)) j
      (fun r' h => hJ r' (List.mem_cons_of_mem _ h))
    have hr := hS r (List.mem_cons_self ..)
    -- two runs: canon r.1 then output r.2; canon j then output u1
    let σ1 := meetState sp r.1 r.2 hr
    let σ2 := meetState sp j u1 hu1
    have hfam : ∀ σ ∈ [σ1, σ2], IsRun σ := by
      intro σ hσ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
      rcases hσ with rfl | rfl
      · exact meetState_isRun sp _ _ hr
      · exact meetState_isRun sp _ _ hu1
    have hcur : ∀ σ ∈ [σ1, σ2], σ.cur ≼ j := by
      intro σ hσ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
      rcases hσ with rfl | rfl
      · exact hJ r (List.mem_cons_self ..)
      · exact PO.refl j
    obtain ⟨u, hu, hsurv⟩ := (survivor_test _ hfam j hcur).1 (hK _ hfam j hcur)
    have h1 : r.2 ≼ u := (hsurv σ1 (by simp)).2.2
    have h2 : u1 ≼ u := (hsurv σ2 (by simp)).2.2
    refine ⟨u, hu, fun r' hr' => ?_⟩
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact h1
    · exact PO.trans (hall r' hr') h2

/-- **Theorem (Complete CALM).** Consistent ↔ Lifted Monotonicity. -/
theorem complete_calm (sp : Spec I O) : sp.Consistent ↔ sp.LiftedMono := by
  rw [liftedMono_iff_commonExpansion]
  exact ⟨consistent_commonExpansion, commonExpansion_consistent⟩

theorem complete_calm_commonExpansion (sp : Spec I O) :
    sp.Consistent ↔ sp.CommonExpansion :=
  ⟨consistent_commonExpansion, commonExpansion_consistent⟩

/-! ### Prop. exposure-boundary -/


/-- Forward direction, in the stronger form: under the common-expansion
condition every output at every *run* state (not only commitment-free ones)
is exposable. -/
theorem commonExpansion_exposable {sp : Spec I O} (hC : sp.CommonExpansion)
    {τ : State sp} (hτ : IsRun τ) {o : O} (ho : τ.R τ.cur o) : Exposable τ o := by
  intro k x hx _
  have hck : τ.cur ≼ k := τ.above _ _ hx
  obtain ⟨u, hu, hall⟩ := hC [(τ.cur, o), (k, x)]
    (by simp [τ.sub _ _ ho, τ.sub _ _ hx]) k (by simp [hck, PO.refl k])
  have hou : o ≼ u := hall (τ.cur, o) (by simp)
  have hxu : x ≼ u := hall (k, x) (by simp)
  exact ⟨u, run_survive hτ hck hu ho hou, hou, hxu⟩

/-- **Proposition (Exposure boundary).** -/
theorem exposure_boundary (sp : Spec I O) :
    sp.CommonExpansion ↔
      ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o := by
  constructor
  · intro hC τ hτ o ho
    exact commonExpansion_exposable hC hτ.isRun ho
  · intro hE rows
    induction rows with
    | nil =>
      intro _ j _
      obtain ⟨u, hu⟩ := sp.total j
      exact ⟨u, hu, by simp⟩
    | cons r rs ih =>
      intro hS j hJ
      obtain ⟨u1, hu1, hall⟩ := ih (fun r' h => hS r' (List.mem_cons_of_mem _ h)) j
        (fun r' h => hJ r' (List.mem_cons_of_mem _ h))
      have hr := hS r (List.mem_cons_self ..)
      have hrj := hJ r (List.mem_cons_self ..)
      have hexp := hE (canon sp r.1) ⟨r.1, [], ExecCF.nil _⟩ r.2 ⟨hr, PO.refl _⟩
      obtain ⟨u, hu, hou, h1u⟩ :=
        (lifted_exposure_test _ _).1 hexp j hrj u1 ⟨hu1, hrj⟩
      refine ⟨u, hu.1, fun r' hr' => ?_⟩
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact hou
      · exact PO.trans (hall r' hr') h1u

end CC
