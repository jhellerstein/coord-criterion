import CoordCriterion.Foundations.Runs

/-!
# Functional CALM (Section 2, `sections/functional-calm.tex`)

* `functional_calm` — Theorem functional-calm;
* `state_by_input` — Corollary state-by-input;
* `exposable_iff_functional` — remark after Def. exposable;
* `functional_exposure_boundary` — Proposition functional-exposure-boundary.

Further remarks of the section and the deferred proofs are in
`CALM/Lemmas.lean`; examples in `CALM/Examples.lean`.
-/

namespace CC

variable {I O : Type} [PO I] [PO O]

/-! ### Auxiliary run facts -/

/-- Along an execution the current input only grows, and every emitted output
lies in the fiber of some input below the final current input. -/
theorem exec_emitted {sp : Spec I O} {σ τ : State sp} {es : List (Event I O)}
    (hx : Exec σ es τ) :
    σ.cur ≼ τ.cur ∧ ∀ o ∈ outs es, ∃ c, sp.S c o ∧ c ≼ τ.cur := by
  induction hx with
  | nil σ => exact ⟨PO.refl _, fun o ho => by simp [outs] at ho⟩
  | @cons σ τ ρ e es hs _ ih =>
    obtain ⟨hτρ, hE⟩ := ih
    cases hs with
    | input _ j hleg hcur _ =>
      obtain ⟨u0, hu0⟩ := hleg
      have hσj : σ.cur ≼ j := σ.above _ _ hu0
      refine ⟨PO.trans hσj (hcur ▸ hτρ), fun o ho => ?_⟩
      simp only [outs] at ho
      exact hE o ho
    | output _ o' hleg hcur _ =>
      refine ⟨hcur ▸ hτρ, fun o ho => ?_⟩
      simp only [outs, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact ⟨σ.cur, σ.sub _ _ hleg, hcur ▸ hτρ⟩
      · exact hE o ho

/-- Monotone version of Corollary state-by-input: in a monotone (not
necessarily functional) spec every run state is canonical. -/
theorem run_canon_of_mono {sp : Spec I O} (hm : sp.MonotoneF)
    {τ : State sp} (hτ : IsRun τ) : τ = canon sp τ.cur := by
  obtain ⟨i, es, hx⟩ := hτ
  have hres := run_residual hx
  obtain ⟨_, hE⟩ := exec_emitted hx
  refine State.ext' (σ := τ) (τ := canon sp τ.cur) (by rfl) ?_
  funext k u
  apply propext
  rw [hres k u]
  simp only [canon]
  constructor
  · rintro ⟨hS, hk, _⟩; exact ⟨hS, hk⟩
  · rintro ⟨hS, hk⟩
    refine ⟨hS, hk, fun o ho => ?_⟩
    obtain ⟨c, hc, hcτ⟩ := hE o ho
    exact hm c k o u (PO.trans hcτ hk) hc hS

/-- The state `input i; output o` from `canon i` is a run state. -/
theorem isRun_meet (sp : Spec I O) (i : I) (o : O) (h : sp.S i o) :
    IsRun (meetState sp i o h) := by
  refine ⟨i, ?_⟩
  have hR : (canon sp i).R i o := ⟨h, PO.refl i⟩
  exact reach_meet (residual_canon sp i) hR

theorem isRun_canon (sp : Spec I O) (i : I) : IsRun (canon sp i) :=
  ⟨i, [], Exec.nil _⟩

/-! ### Theorem functional-calm -/

theorem consistent_of_mono {sp : Spec I O} (hm : sp.MonotoneF) : sp.Consistent := by
  intro fam hrun j hj
  obtain ⟨u, hu⟩ := sp.total j
  refine (survivor_test fam hrun j hj).2 ⟨u, hu, fun σ hσ => ?_⟩
  have h := run_canon_of_mono hm (hrun σ hσ)
  rw [h]
  exact ⟨hu, hj σ hσ⟩

theorem mono_of_consistent {sp : Spec I O} (hf : sp.Functional)
    (hc : sp.Consistent) : sp.MonotoneF := by
  intro i k o u hik hio hku
  let σ1 := meetState sp i o hio
  let σ2 := canon sp k
  have hrun : ∀ σ ∈ [σ1, σ2], IsRun σ := by
    intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl
    · exact isRun_meet sp i o hio
    · exact isRun_canon sp k
  have hj : ∀ σ ∈ [σ1, σ2], σ.cur ≼ k := by
    intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl
    · exact hik
    · exact PO.refl k
  obtain ⟨u', hu', hall⟩ := (survivor_test _ hrun k hj).1 (hc _ hrun k hj)
  have h1 : σ1.R k u' := hall σ1 (by simp)
  have : u' = u := hf k u' u hu' hku
  subst this
  exact h1.2.2

/-- **Theorem (Functional CALM).** -/
theorem functional_calm {sp : Spec I O} (hf : sp.Functional) :
    sp.Consistent ↔ sp.MonotoneF :=
  ⟨mono_of_consistent hf, consistent_of_mono⟩

/-! ### Corollary state-by-input -/

/-- **Corollary (State is fixed by input).** -/
theorem state_by_input {sp : Spec I O} (hf : sp.Functional) (hc : sp.Consistent)
    {τ : State sp} (hτ : IsRun τ) : τ = canon sp τ.cur :=
  run_canon_of_mono (mono_of_consistent hf hc) hτ

/-! ### Exposability in a functional spec -/

/-- Remark after Def. exposable: in a functional spec, `o` is exposable at
`σ` iff `output o` removes nothing. -/
theorem exposable_iff_functional {sp : Spec I O} (hf : sp.Functional)
    (σ : State sp) (o : O) :
    Exposable σ o ↔ outputTable σ o = σ.R := by
  constructor
  · intro he
    funext k x
    apply propext
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      apply Classical.byContradiction
      intro hn
      obtain ⟨u, hu, hou, _⟩ := he k x h hn
      have : u = x := hf k u x (σ.sub _ _ hu) (σ.sub _ _ h)
      subst this
      exact hn hou
  · intro heq k x h hn
    have h' : outputTable σ o k x := by rw [heq]; exact h
    exact absurd h'.2 hn

/-! ### Proposition functional-exposure-boundary -/


/-- **Proposition (Exposure boundary).**  "Output at state `τ`" is an `o`
with `τ.R τ.cur o`. -/
theorem functional_exposure_boundary {sp : Spec I O} (hf : sp.Functional) :
    sp.MonotoneF ↔
      ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o := by
  constructor
  · intro hm τ hτ o ho k x hkx hn
    exfalso
    apply hn
    have hcan := run_canon_of_mono hm hτ.isRun
    have hkx' : (canon sp τ.cur).R k x := hcan ▸ hkx
    exact hm τ.cur k o x hkx'.2 (τ.sub _ _ ho) hkx'.1
  · intro hexp i k o u hik hio hku
    have hcf : ReachableCF (canon sp i) := ⟨i, [], ExecCF.nil _⟩
    apply Classical.byContradiction
    intro hn
    obtain ⟨u', hu', hou', _⟩ :=
      hexp (canon sp i) hcf o ⟨hio, PO.refl i⟩ k u ⟨hku, hik⟩ hn
    have : u' = u := hf k u' u hu'.1 hku
    subst this
    exact hn hou'

end CC
