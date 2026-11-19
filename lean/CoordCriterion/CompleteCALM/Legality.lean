import CoordCriterion.CALM.Lemmas

/-!
# Complete CALM as "confluence is legality" + "legality is Lifted Monotonicity"

Scratch formalization of a proposed restructuring of Sections 2–3 (branch
`calm-restructure`; not yet cited by the paper).

* `Spec.RunsLegal` — every output at every run state is legal (exposable).
  Runs here are arbitrary sequences of input and output events; output events
  may emit any output of the current fiber, legal or not.
* `Spec.LegalReachLegal` — every output at every state reached by legal
  events only is legal (the hypothesis side of Prop. exposure-boundary).
* **Lemma 1** `consistent_iff_runsLegal`: runs are consistent (confluent) iff
  every output any run can emit is legal.  (⇒) is the conflict pair of
  `exposable_of_consistent`; (⇐) uses exposability at canonical states
  (`exposure_boundary`, ⇐) and the survivor test (`commonExpansion_consistent`).
* `runsLegal_iff_legalReachLegal`: the two legality conditions coincide, since
  if every output at every legally reached state is legal then every run is
  legally reached.
* **Lemma 2** `legalReachLegal_iff_liftedMono`: Prop. exposure-boundary with
  Prop. common-extension-form.
* `complete_calm_via_legality`: Lemma 1 + bridge + Lemma 2 = Complete CALM.
* `functional_calm_via_legality`: the same order in the functional case.
-/

namespace CC

variable {I O : Type} [PO I] [PO O]

/-- Every output that some run can emit is legal. -/
def Spec.RunsLegal (sp : Spec I O) : Prop :=
  ∀ τ : State sp, IsRun τ → ∀ o, τ.R τ.cur o → Exposable τ o

/-- Every output at every state reached by legal events is legal. -/
def Spec.LegalReachLegal (sp : Spec I O) : Prop :=
  ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o

/-- **Lemma 1 (confluence is legality).** -/
theorem consistent_iff_runsLegal (sp : Spec I O) : sp.Consistent ↔ sp.RunsLegal := by
  constructor
  · intro hc τ hτ o ho
    exact CALM.exposable_of_consistent hc hτ ho
  · intro hL
    exact commonExpansion_consistent
      ((exposure_boundary sp).2 fun τ hτ o ho => hL τ hτ.isRun o ho)

/-- A legal execution extends by one legal step. -/
theorem execCF_snoc {sp : Spec I O} {α σ τ : State sp} {l : List (Event I O)}
    {e : Event I O} (hl : ExecCF α l σ) (hs : Step σ e τ)
    (he : ∀ o, e = .output o → Exposable σ o) : ExecCF α (l ++ [e]) τ := by
  induction hl with
  | nil =>
    cases e with
    | input j => exact ExecCF.input hs (ExecCF.nil _)
    | output o => exact ExecCF.output hs (he o rfl) (ExecCF.nil _)
  | input h _ ih => exact ExecCF.input h (ih hs he)
  | output h hx _ ih => exact ExecCF.output h hx (ih hs he)

/-- If every output at every legally reached state is legal, every execution
from a legally reached state ends at a legally reached state. -/
theorem reachableCF_of_exec {sp : Spec I O} (hL : sp.LegalReachLegal)
    {σ τ : State sp} {es : List (Event I O)} (hσ : ReachableCF σ) (hx : Exec σ es τ) :
    ReachableCF τ := by
  induction hx with
  | nil => exact hσ
  | @cons σ τ ρ e es hs _ ih =>
    apply ih
    obtain ⟨i, es0, h0⟩ := hσ
    refine ⟨i, es0 ++ [e], execCF_snoc h0 hs ?_⟩
    rintro o rfl
    cases hs with
    | output _ _ ho _ _ => exact hL _ ⟨i, es0, h0⟩ o ho

/-- The two legality conditions coincide. -/
theorem runsLegal_iff_legalReachLegal (sp : Spec I O) :
    sp.RunsLegal ↔ sp.LegalReachLegal := by
  constructor
  · intro h τ hτ o ho
    exact h τ hτ.isRun o ho
  · intro hL τ hτ o ho
    obtain ⟨i, es, hx⟩ := hτ
    exact hL τ (reachableCF_of_exec hL ⟨i, [], ExecCF.nil _⟩ hx) o ho

/-- **Lemma 2 (legality is Lifted Monotonicity).** -/
theorem legalReachLegal_iff_liftedMono (sp : Spec I O) :
    sp.LegalReachLegal ↔ sp.LiftedMono := by
  rw [liftedMono_iff_commonExpansion]
  exact (exposure_boundary sp).symm

/-- **Complete CALM**, assembled from Lemma 1 and Lemma 2. -/
theorem complete_calm_via_legality (sp : Spec I O) :
    sp.Consistent ↔ sp.LiftedMono :=
  (consistent_iff_runsLegal sp).trans
    ((runsLegal_iff_legalReachLegal sp).trans (legalReachLegal_iff_liftedMono sp))

/-- **Functional CALM**, in the same order. -/
theorem functional_calm_via_legality {sp : Spec I O} (hf : sp.Functional) :
    sp.Consistent ↔ sp.MonotoneF :=
  (consistent_iff_runsLegal sp).trans
    ((runsLegal_iff_legalReachLegal sp).trans (functional_exposure_boundary hf).symm)

end CC
