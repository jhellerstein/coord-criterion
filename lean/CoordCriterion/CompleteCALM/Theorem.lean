import CoordCriterion.Foundations.Core
import CoordCriterion.Foundations.Runs

/-!
# Complete CALM (Section 3, `sections/complete-calm.tex`)

* `liftedMono_iff_relMono_directed` — Lifted Monotonicity ↔ Relational
  Monotonicity ∧ directed fibers (paragraph after Def. lifted-monotonicity);
* `liftedMono_iff_commonExpansion` — Prop. common-extension-form (the single
  canonical statement; every other file uses it);
* `ce_of_pairs` — pairs of rows suffice for the common-extension condition
  (`app:pairs-suffice`);
* facts about the lifted output event: the Subsumed/Excluded classification
  (`ruledOut_iff`), disjointness, and the functional case;
* `lifted_exposure_test` — Prop. exposability (lifted exposure test);
* `complete_calm` — Thm. complete-calm;
* `exposure_boundary` — Prop. exposure-boundary.

The paper's own proof routes (via Lemma reconciliation) and the remaining
remarks are in `CALM/Lemmas.lean`.
-/

namespace CC

variable {I O : Type} [PO I] [PO O]

/-! ### Lifted Monotonicity = Relational Monotonicity + directed fibers -/

/-- Accumulator lemma: from RelMono and directed fibers, any finite list in
`S i` together with a seed `u0 ∈ S j` has a common output extension in `S j`. -/
theorem relMono_directed_acc {sp : Spec I O} (hR : sp.RelMono) (hD : sp.DirectedOutputs)
    {i j : I} (hij : i ≼ j) :
    ∀ X : List O, (∀ x ∈ X, sp.P i x) → ∀ u0, sp.P j u0 →
      ∃ u, sp.P j u ∧ u0 ≼ u ∧ ∀ x ∈ X, x ≼ u := by
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

/-! ### Prop. common-extension-form -/

theorem liftedMono_iff_commonExpansion (sp : Spec I O) :
    sp.LiftedMono ↔ sp.CommonExpansion := by
  constructor
  · intro hL
    obtain ⟨hR, hD⟩ := (liftedMono_iff_relMono_directed sp).1 hL
    intro rows hrows j hj
    -- accumulate one row at a time, starting from a totality witness
    have acc : ∀ rows : List (I × O), (∀ r ∈ rows, sp.P r.1 r.2) →
        (∀ r ∈ rows, r.1 ≼ j) → ∃ u, sp.P j u ∧ ∀ r ∈ rows, r.2 ≼ u := by
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

/-- Pairs of rows suffice for the common-extension condition
(paragraph `app:pairs-suffice`; the converse is
`CC.CALM.pairs_iff_commonExpansion`). -/
theorem ce_of_pairs {sp : Spec I O}
    (h : ∀ i₁ o₁ i₂ o₂ j, sp.P i₁ o₁ → sp.P i₂ o₂ → i₁ ≼ j → i₂ ≼ j →
      ∃ u, sp.P j u ∧ o₁ ≼ u ∧ o₂ ≼ u) :
    sp.CommonExpansion := by
  intro rows
  induction rows with
  | nil =>
    intro _ j _
    obtain ⟨u, hu⟩ := sp.total j
    exact ⟨u, hu, by simp⟩
  | cons r rs ih =>
    intro hrows j hj
    obtain ⟨u', hu', hall'⟩ := ih (fun r hr => hrows r (List.mem_cons_of_mem _ hr)) j
      (fun r hr => hj r (List.mem_cons_of_mem _ hr))
    obtain ⟨u, hu, h1, h2⟩ := h r.1 r.2 j u' j (hrows r (List.mem_cons_self ..)) hu'
      (hj r (List.mem_cons_self ..)) (PO.refl j)
    refine ⟨u, hu, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact h1
    · exact PO.trans (hall' x hx') h2

/-! ### Lifted output event: classification of ruled-out rows -/

section Classification
variable {sp : Spec I O} (σ : State sp) (o : O)

theorem subsumed_excluded_disjoint {k x} :
    ¬ (Subsumed σ o k x ∧ Excluded σ o k x) :=
  fun ⟨hr, he⟩ => he.2.2 hr

/-- `Subsumed_o` and `Excluded_o` partition exactly the ruled-out rows. -/
theorem ruledOut_iff (k : I) (x : O) :
    (σ.R k x ∧ ¬ outputTable σ o k x) ↔
      (Subsumed σ o k x ∨ Excluded σ o k x) := by
  constructor
  · rintro ⟨hR, hno⟩
    have hox : ¬ o ≼ x := fun h => hno ⟨hR, h⟩
    by_cases hr : Subsumed σ o k x
    · exact Or.inl hr
    · exact Or.inr ⟨hR, hox, hr⟩
  · rintro (hr | he)
    · exact ⟨hr.1, fun h => hr.2.1 h.2⟩
    · exact ⟨he.1, fun h => he.2.1 h.2⟩

/-- `Exposable` means that no row must be removed by commitment. -/
theorem exposable_iff_no_commitment :
    Exposable σ o ↔ ∀ k x, ¬ Excluded σ o k x := by
  constructor
  · intro h k x he
    exact he.2.2 ⟨he.1, he.2.1, h k x he.1 he.2.1⟩
  · intro he k x hR hox
    exact Classical.byContradiction fun hn =>
      he k x ⟨hR, hox, fun hs => hn hs.2.2⟩

end Classification

/-- In a functional specification, no ruled-out row is subsumed. -/
theorem functional_subsumed_empty {sp : Spec I O} (hF : sp.Functional) (σ : State sp) (o : O)
    (k : I) (x : O) : ¬ Subsumed σ o k x := by
  rintro ⟨h, hox, u, hu, hou, _⟩
  have : x = u := hF k x u (σ.sub _ _ h) (σ.sub _ _ hu)
  subst this
  exact hox hou

/-! ### Prop. exposability: the lifted exposure test -/

/-- **Lifted exposure test.** `o ∈ R(i)` is exposable at `(i,R)` iff for every
legal `j ⪰ i` and `x ∈ R(j)` some `u ∈ R(j)` extends both `o` and `x`.
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

/-- From a run state, a row `(j,u)` with `j ⪰ cur` survives once `u` extends
some output at the current input. -/
theorem run_survive {sp : Spec I O} {σ : State sp} (hσ : IsRun σ) {j : I} {u v : O}
    (hcj : σ.cur ≼ j) (hju : sp.P j u) (hv : σ.R σ.cur v) (hvu : v ≼ u) : σ.R j u := by
  obtain ⟨E, hE⟩ := hσ.residual
  have hEv := ((hE _ _).1 hv).2.2
  exact (hE j u).2 ⟨hju, hcj, fun o ho => PO.trans (hEv o ho) hvu⟩

theorem commonExpansion_consistent {sp : Spec I O} (hC : sp.CommonExpansion) :
    sp.Consistent := by
  intro fam hrun j hj
  -- one row per run: (cur, some output still at cur), which extends all emitted
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

theorem meetState_isRun (sp : Spec I O) (i : I) (o : O) (h : sp.P i o) :
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


/-- Forward direction, in the stronger form: under the common-extension
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
