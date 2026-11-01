import CoordCriterion.Distributed.Systems
import CoordCriterion.Figures
import CoordCriterion.Appendix.TransactionBases.NoReads

/-!
# Paper Appendix C: Output events and exclusion bases (statement layer)

Covers `appendices/exclusion-bases-general.tex` (`app:bases`): first the
formal lifted output events (`app:lifted-output-events`: the sets `Excluded^in_o`,
`Subsumed_o`, `Excluded^out_o`, Def. `def:lifted-output-event`, the remarks after
it, and Prop. `prop:exposability`), then (`app:exclusion-bases`)
the canonical basis and canonical event, the paragraph *The canonical input and output exclusions are
exclusions*, Lemma `lem:canonical-exclusion-normal-form` (three parts),
Def. `def:canonical-system`, Lemma `lem:compound-exclusion` and the remark
after it, Def. `def:run-under-basis`, observable equivalence,
Lemma `lem:canonical-equivalent`, Cor. `cor:reconciliation-any-basis`, the
failure of the converse, and *Application-specific exclusions*.

How to read this file.  Read it side by side with the appendix.  Entries are
in the appendix's order; each numbered result is named by its LaTeX label and
each unlabeled claim by `«app:bases/<slug>»`.  Docstrings quote the paper
(LaTeX lightly turned into Unicode) and explain any difference in reading.
Statements are written out; proofs are one-line references to
`CoordCriterion/Distributed/Exclusions.lean` (namespace `CC`) and
`CoordCriterion/Distributed/Systems.lean` (namespace `CC.Dist`), and, for the
lifted output events, to `CoordCriterion/CALM/` and `Figures.lean`.

Conventions: a state `(i,R)` is `σ : State sp` with `σ.cur = i`, `σ.R = R`;
`R[out ⪰ o]` is `outputTable σ o`; `Out_γ(o)` is `SEvent.output γ o`, and
legality under a basis `B` is `SysStep B` (see Def. system-output-event in
`Paper/S4_Distributed.lean`); `ε` is `[]`.
-/

namespace CC.Paper

open CC Classical

variable {I O : Type} [PO I] [PO O]

/-! ## Lifted output events (`app:lifted-output-events`)

Formal definitions behind the summary in §3.4 (`sec:lifted-output-events`). -/

section LiftedOutputEvents

open CC.CALM


/-- **Eq. `eq:input-exclusion-removals`**: `Excluded^in_o = {(k,x) ∈ R : k ∉ in(R[out ⪰ o])}`.
Lean: `InputExcluded σ o k x` is `σ.R k x ∧ ¬ ∃ u, σ.R k u ∧ o ≼ u`. -/
abbrev «eq:input-exclusion-removals» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) : Table I O :=
  InputExcluded σ o

/-- **Eq. `eq:output-subsumptions`**: `Subsumed_o = {(k,x) ∈ R ∖ R[out ⪰ o] :
x ≼ u for some u ∈ R[out ⪰ o](k)}`. -/
abbrev «eq:output-subsumptions» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) : Table I O :=
  Subsumed σ o

/-- **Eq. `eq:output-exclusion-removals`**: `Excluded^out_o = (R ∖ R[out ⪰ o]) ∖ (Excluded^in_o ∪
Subsumed_o)`. -/
abbrev «eq:output-exclusion-removals» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) : Table I O :=
  OutputExcluded σ o

/-- **Def. `def:lifted-output-event`** (Lifted output event, output
subsumption).  "`output(o)` keeps exactly the rows whose outputs refine `o`
and emits `o`, atomically, ending at `(i, R[out ⪰ o])`.  It removes the rows
in `Subsumed_o`, each refined past by a kept row at the same input, by
*output subsumption*, which is not an exclusion."

Lean: the event is `Step σ (.output o) τ` with `τ.R = outputTable σ o`,
the same transition as Def. `def:output-event`.  This declaration names the
event's resulting state, parameterized by `(σ, o)`. -/
abbrev «def:lifted-output-event» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) (ho : σ.R σ.cur o) : State sp :=
  outputState σ o ho

/-- **Def. `def:canonical-input-output-exclusion`** (Lifted input exclusion, lifted exclusion).  "When
`Excluded^in_o ≠ ∅`, the output event applies the *input exclusion* `x_o^in`; when
`Excluded^out_o ≠ ∅`, it applies the *output exclusion* `x_o^out`.  The input and output exclusions are
*exclusions*: `x_o^in(i,R) = (i, R ∖ Excluded^in_o)`,
`x_o^out(i,R) = (i, R ∖ Excluded^out_o)`."

Lean: as exclusions (in the sense of Def. `def:exclusion`), `inputExclusion o` and
`outputExclusion o` with their domains of definition (`Excluded^in_o ≠ ∅` and
`Excluded^out_o ≠ ∅` respectively).  This declaration names the pair as states
left behind. -/
abbrev «def:canonical-input-output-exclusion» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) (ho : σ.R σ.cur o) : State sp × State sp :=
  (inputExclusionState σ o ho, outputExclusionState σ o ho)

/-- **Eq. `eq:canonical-input-output-exclusion-relational`**:
"`x_o^in(i,R) = (i, R ∖ Excluded^in_o)`, `x_o^out(i,R) = (i, R ∖ Excluded^out_o)`."  Both
keep the current input; `inputExclusionState` removes exactly `Excluded^in_o`, `outputExclusionState`
exactly `Excluded^out_o`. -/
theorem «eq:canonical-input-output-exclusion-relational» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} (σ : State sp) (o : O) (ho : σ.R σ.cur o) :
    ((inputExclusionState σ o ho).cur = σ.cur ∧
        ∀ k x, (inputExclusionState σ o ho).R k x ↔ σ.R k x ∧ ¬ InputExcluded σ o k x) ∧
      ((outputExclusionState σ o ho).cur = σ.cur ∧
        ∀ k x, (outputExclusionState σ o ho).R k x ↔ σ.R k x ∧ ¬ OutputExcluded σ o k x) :=
  ⟨⟨rfl, fun _ _ => Iff.rfl⟩, ⟨rfl, fun _ _ => Iff.rfl⟩⟩

/-- After Def. `def:lifted-output-event`: "In Figure `fig:ambiguity-frames`(f),
emitting `[A,B]` places `[B,A]` in `Excluded^out_o` … In panel (g), the two
removed route sets are in `Subsumed_o`." -/
theorem «def:lifted-output-event/examples» :
    OutputExcluded (canon Figures.Txn.spec ()) .ab () .ba ∧
      Subsumed (canon Figures.Trace.spec ()) Figures.Trace.rS1 () Figures.Trace.rA ∧
      Subsumed (canon Figures.Trace.spec ()) Figures.Trace.rS1 () Figures.Trace.rA2 :=
  ⟨Figures.Txn.ba_outputExcluded.1, Figures.Trace.removed_subsumed.2.1,
   Figures.Trace.removed_subsumed.2.2.1⟩

/-- "The three sets are disjoint." -/
theorem «app:lifted-output-events/disjoint» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) (k : I) (x : O) :
    ¬ (InputExcluded σ o k x ∧ Subsumed σ o k x) ∧ ¬ (InputExcluded σ o k x ∧ OutputExcluded σ o k x) ∧
      ¬ (Subsumed σ o k x ∧ OutputExcluded σ o k x) :=
  ⟨inputExcluded_subsumed_disjoint σ o, inputExcluded_outputExcluded_disjoint σ o, subsumed_outputExcluded_disjoint σ o⟩

/-- "… removing the rows of either exclusion leaves the other sets
unchanged, so the event may apply `x_o^in` and `x_o^out` in either order." -/
theorem «app:lifted-output-events/commute» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) (ho : σ.R σ.cur o) :
    (∀ k x, Subsumed (inputExclusionState σ o ho) o k x ↔ Subsumed σ o k x) ∧
      (∀ k x, OutputExcluded (inputExclusionState σ o ho) o k x ↔ OutputExcluded σ o k x) ∧
      (∀ k x, InputExcluded (outputExclusionState σ o ho) o k x ↔ InputExcluded σ o k x) ∧
      (∀ k x, Subsumed (outputExclusionState σ o ho) o k x ↔ Subsumed σ o k x) ∧
      (∀ h₁ h₂, (outputExclusionState (inputExclusionState σ o ho) o h₁).R =
        (inputExclusionState (outputExclusionState σ o ho) o h₂).R) :=
  ⟨inputExclusion_subsumed σ o ho, inputExclusion_outputExcluded σ o ho, outputExclusion_inputExcluded σ o ho, outputExclusion_subsumed σ o ho,
   input_output_exclusion_states_commute σ o ho⟩

/-- "The output exclusion only narrows fibers: at each input it touches, some
row that refines `o` survives." -/
theorem «app:lifted-output-events/output-exclusion-narrows» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} (σ : State sp) (o : O) {k : I} {x : O} (h : OutputExcluded σ o k x) :
    ∃ u, σ.R k u ∧ o ≼ u :=
  output_exclusion_narrows σ o h

/-- "With one row per input, `Subsumed_o` and `Excluded^out_o` are empty; this is
the functional output event of Definition `def:output-event`." -/
theorem «app:lifted-output-events/functional» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) (σ : State sp) (o : O) (k : I) (x : O) :
    ¬ Subsumed σ o k x ∧ ¬ OutputExcluded σ o k x :=
  functional_subsumed_outputExcluded_empty hf σ o k x

/-- "Legality lifts with the event: `o` is a legal output when `output(o)`
applies no exclusion, that is, when `Excluded^in_o` and `Excluded^out_o` are empty." -/
theorem «app:lifted-output-events/exposable» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) :
    Exposable σ o ↔ (∀ k x, ¬ InputExcluded σ o k x) ∧ (∀ k x, ¬ OutputExcluded σ o k x) :=
  exposable_iff_no_exclusion σ o

/-- **Prop. `prop:exposability`** (Lifted exposure test).  "An output
`o ∈ R(i)` is a legal output at `(i,R)` if and only if, for every legal `j ⪰ i`
and `x ∈ R(j)`, some `u ∈ R(j)` refines both: `o ≼ u` and `x ≼ u`."  (The
Lean statement does not need the hypothesis `o ∈ R(i)`.) -/
theorem «prop:exposability» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) :
    Exposable σ o ↔ ∀ j, σ.cur ≼ j → ∀ x, σ.R j x → ∃ u, σ.R j u ∧ o ≼ u ∧ x ≼ u :=
  lifted_exposure_test σ o

/-- **Eq. `eq:safe-exposure`**: "some `u ∈ R(j)` refines both: `o ≼ u` and
`x ≼ u`" — the per-row test of Prop. `prop:exposability`, at legal input `j`
and remaining output `x`. -/
abbrev «eq:safe-exposure» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) (j : I) (x : O) : Prop :=
  ∃ u, σ.R j u ∧ o ≼ u ∧ x ≼ u

end LiftedOutputEvents

/-! ## Exclusion bases and compound exclusions (`app:exclusion-bases`) -/

/-! ## Canonical basis, canonical event -/

/-- **Def. `def:canonical-exclusion-basis`** (Canonical basis), the basis.
"`ℬ_S = {x_o^in : o ∈ O, dom(x_o^in) ≠ ∅} ∪ {x_o^out : o ∈ O, dom(x_o^out) ≠ ∅}`,
where `x_o^in` is defined at the states with `o ∈ R(i)` and `Excluded^in_o ≠ ∅`, and
`x_o^out` at those with `o ∈ R(i)` and `Excluded^out_o ≠ ∅`."
(Eq. canonical-exclusion-basis-relational.) -/
abbrev «def:canonical-exclusion-basis» (sp : Spec I O) : ExclusionBasis sp := canonExclusionBasis sp

/-- **Eq. `eq:canonical-exclusion-basis-relational`**:
"`ℬ_S = {x_o^in : o ∈ O, dom(x_o^in) ≠ ∅} ∪ {x_o^out : o ∈ O, dom(x_o^out) ≠ ∅}`."  A
exclusion is in `canonExclusionBasis sp` iff it is some `inputExclusion o` or `outputExclusion o`
defined at some state. -/
theorem «eq:canonical-exclusion-basis-relational» {sp : Spec I O} (c : Exclusion sp) :
    canonExclusionBasis sp c ↔
      ∃ o : O, (c = inputExclusion o ∧ ∃ σ τ : State sp, (inputExclusion o).app σ = some τ) ∨
        (c = outputExclusion o ∧ ∃ σ τ : State sp, (outputExclusion o).app σ = some τ) :=
  Iff.rfl

/-- Def. `def:canonical-exclusion-basis`: "At `(i,R)`, let `κ_o` apply `x_o^in`
when `Excluded^in_o ≠ ∅` and `x_o^out` when `Excluded^out_o ≠ ∅`, so `κ_o` is one of `ε`,
`x_o^in`, `x_o^out`, or `x_o^in x_o^out`." -/
theorem «def:canonical-exclusion-basis/kappa» {sp : Spec I O} (σ : State sp) (o : O) :
    kappa σ o =
      (if ∃ k x, InputExcluded σ o k x then [inputExclusion o] else []) ++
      (if ∃ k x, OutputExcluded σ o k x then [outputExclusion o] else []) :=
  rfl

/-- **Def. `def:canonical-event`** (Canonical event).  "At `(i,R)`, let `κ_o`
apply `x_o^in` when `Excluded^in_o ≠ ∅` and `x_o^out` when `Excluded^out_o ≠ ∅`, so `κ_o` is
one of `ε`, `x_o^in`, `x_o^out`, or `x_o^in x_o^out`.  The *canonical event* for `o` is
`Out_{κ_o}(o)`: the output event of Definition `def:lifted-output-event`, and
with one row per input that of Definition `def:output-event`."

Lean: `kappa σ o` is the list `[]`, `[inputExclusion o]`, `[outputExclusion o]`, or
`[inputExclusion o, outputExclusion o]`.  The event is `SEvent.output (kappa σ o) o`. -/
noncomputable abbrev «def:canonical-event» {sp : Spec I O} (σ : State sp) (o : O) : SEvent sp :=
  SEvent.output (kappa σ o) o

/-- Def. `def:canonical-exclusion-basis`: "The canonical event for `o` is
`Out_{κ_o}(o)`: the output event of Definition lifted-output-event, and with one
row per input that of Definition output-event."

Lean: (a) canonical steps are exactly the steps of §§2–3 (both directions);
(b) with one row per input, `κ_o` is at most the input exclusion, and the input exclusion leaves
`R[out ⪰ o]`, the table of Def. output-event. -/
theorem «def:canonical-exclusion-basis/canonical-event» {sp : Spec I O} :
    ((∀ (σ τ : State sp) (e : SEvent sp), CanonStep σ e τ →
      ∃ e' : Event I O, e.erase = some e' ∧ Step σ e' τ) ∧
     (∀ (σ τ : State sp) (e : Event I O), Step σ e τ →
        ∃ e' : SEvent sp, e'.erase = some e ∧ CanonStep σ e' τ)) ∧
    (sp.Functional →
      (∀ (σ : State sp) (o : O),
        kappa σ o = (if ∃ k x, InputExcluded σ o k x then [inputExclusion o] else [])) ∧
      (∀ (σ : State sp) (o : O) (ho : σ.R σ.cur o),
        (inputExcludeState σ o ho).R = outputTable σ o)) :=
  ⟨⟨fun _ _ _ => canonStep_step, fun _ _ _ => step_canonStep⟩,
    fun hf => ⟨Dist.functional_kappa hf, Dist.functional_inputExclusion_eq hf⟩⟩

/-! ## The canonical input and output exclusions are exclusions -/

/-- *The canonical input and output exclusions are exclusions.*  "With one row per input,
Equation exclusion-excludes holds vacuously, so the input exclusions of Definition
output-event are exclusions."

Lean: in a functional specification, Eq. exclusion-excludes holds for any
pair of states. -/
theorem «app:bases/functional-excludes-vacuous» {sp : Spec I O} (hf : sp.Functional)
    (σ τ : State sp) : ∀ k u w, σ.R k u → ¬ τ.R k u → τ.R k w → ¬ (u ≼ w) :=
  Dist.functional_excludes_vacuous hf σ τ

/-- *The canonical input and output exclusions are exclusions* (`x_o^in`).  "With several
outputs per input, the input exclusion `x_o^in` of Definition lifted-output-event removes
every row at the inputs of `Excluded^in_o`, so nothing remains there to refine a
removed row."

Lean: `inputExclusion o : Exclusion sp` is the exclusion (its `excludes` field is the
argument); it is defined exactly where the definition says and leaves
`R ∖ Excluded^in_o`. -/
theorem «app:bases/input-exclusion-is-exclusion» {sp : Spec I O} (o : O) (σ τ : State sp) :
    (inputExclusion o : Exclusion sp).app σ = some τ ↔
      ∃ h : σ.R σ.cur o, (∃ k x, InputExcluded σ o k x) ∧ inputExcludeState σ o h = τ :=
  inputExclusionApp_eq

/-- *The canonical input and output exclusions are exclusions* (`x_o^out`).  "For `x_o^out`,
suppose some `x ∈ Excluded^out_o` at input `k` were refined by a row `y` that `x_o^out`
leaves at `k` … so `x ∈ Subsumed_o`, a contradiction."

Lean: `outputExclusion o : Exclusion sp` is the exclusion (its `excludes` field is
this argument); it is defined exactly where the definition says and leaves
`R ∖ Excluded^out_o`. -/
theorem «app:bases/output-exclusion-is-exclusion» {sp : Spec I O} (o : O) (σ τ : State sp) :
    (outputExclusion o : Exclusion sp).app σ = some τ ↔
      σ.R σ.cur o ∧ (∃ k x, OutputExcluded σ o k x) ∧ outputExcludeState σ o = τ :=
  outputExclusionApp_eq

/-- *The canonical input and output exclusions are exclusions.*  "Since `x_o^in` and `x_o^out`
remove disjoint sets of rows and neither changes the other's …, each is defined
on the state the other leaves, and the canonical event may apply them in either
order."

Lean: if both classes are nonempty, `x_o^in; x_o^out` and `x_o^out; x_o^in` are both defined
and reach the same state, with table `R ∖ (Excluded^in_o ∪ Excluded^out_o)`. -/
theorem «app:bases/input-output-exclusions-commute» {sp : Spec I O} {σ : State sp} {o : O}
    (hS : ∃ k x, InputExcluded σ o k x) (hJ : ∃ k x, OutputExcluded σ o k x) (ho : σ.R σ.cur o) :
    ∃ τ₁ τ₂ ρ₁ ρ₂ : State sp,
      (inputExclusion o).app σ = some τ₁ ∧ (outputExclusion o).app τ₁ = some ρ₁ ∧
      (outputExclusion o).app σ = some τ₂ ∧ (inputExclusion o).app τ₂ = some ρ₂ ∧
      ρ₁ = ρ₂ ∧ ρ₁.cur = σ.cur ∧ ρ₁.R = Pruned σ o :=
  input_output_exclusion_commute hS hJ ho

/-! ## Lemma containment, canonical support, exclusion-free events -/

/-- **Lemma containment, canonical support, and exclusion-free events**
(`lem:canonical-exclusion-normal-form`).  Let `(i,R)` be a state and
`o ∈ R(i)`.

1. "Every legal output event `Out_γ(o)` takes `(i,R)` to some `(i,R')` with
   `R' ⊆ R[out ⪰ o]`, and removes the rows in `Excluded^in_o` and `Excluded^out_o` by
   exclusion."
2. "The canonical event `Out_{κ_o}(o)` is legal and takes `(i,R)` to
   `(i,R[out ⪰ o])`, so it retains every row that any legal `Out_γ(o)`
   retains."
3. "If `Out_ε(o)` is legal, it takes `(i,R)` to `(i,R[out ⪰ o])`; it is legal
   exactly when `o` is a legal output."

Lean, conjunct by conjunct.  (1) for any basis `B`: the event keeps the current
input, ends inside `R[out ⪰ o]`, and the state `σc` left by `γ` (before
subsumption) contains no row of `Excluded^in_o ∪ Excluded^out_o` — "by exclusion".
(2) `Out_{κ_o}(o)` is legal under `ℬ_S` and ends at `outState σ o ho`, whose
table is `R[out ⪰ o]`; every legal `Out_γ(o)` ends inside that table.
(3) `Out_ε(o)` is legal (under any basis) iff `o ∈ R(i)` is a legal output,
and then ends at `(i, R[out ⪰ o])`; being a legal output is "`Excluded^in_o` and
`Excluded^out_o` are empty". -/
theorem «lem:canonical-exclusion-normal-form» {sp : Spec I O} :
    (∀ {B : ExclusionBasis sp} {σ τ : State sp} {γ : List (Exclusion sp)} {o : O},
      SysStep B σ (.output γ o) τ →
      τ.cur = σ.cur ∧ σ.R σ.cur o ∧ (∀ k u, τ.R k u → σ.R k u ∧ o ≼ u) ∧
      ∃ σc, ApplySeq γ σ σc ∧ ∀ k x, (InputExcluded σ o k x ∨ OutputExcluded σ o k x) → ¬ σc.R k x) ∧
    (∀ (σ : State sp) (o : O) (ho : σ.R σ.cur o),
      SysStep (canonExclusionBasis sp) σ (.output (kappa σ o) o) (outState σ o ho) ∧
      (outState σ o ho).cur = σ.cur ∧ (outState σ o ho).R = outputTable σ o ∧
      ∀ {B : ExclusionBasis sp} {τ : State sp} {γ : List (Exclusion sp)},
        SysStep B σ (.output γ o) τ → ∀ k u, τ.R k u → outputTable σ o k u) ∧
    (∀ {B : ExclusionBasis sp} {σ τ : State sp} {o : O},
      (SysStep B σ (.output [] o) τ ↔
        σ.R σ.cur o ∧ Exposable σ o ∧ τ.cur = σ.cur ∧ τ.R = outputTable σ o) ∧
      (Exposable σ o ↔ (¬ ∃ k x, InputExcluded σ o k x) ∧ ¬ ∃ k x, OutputExcluded σ o k x)) :=
  ⟨fun h => containment h,
    fun σ o ho => ⟨canonical_support σ o ho, rfl, rfl, fun h => canonical_maximal h⟩,
    fun {_ σ _ o} => ⟨eps_step_iff, exposable_iff_empty σ o⟩⟩

/-! ## Canonical system -/

/-- **Def. canonical system** (`def:canonical-system`).  "A system is canonical
when its basis is `ℬ_S` and each output event it performs is the canonical
event `Out_{κ_o}(o)` at the participant's state where it occurs, and it
performs no exclusion event."

Lean: stated on histories, as the property that each participant's
input/output events, annotated with exclusion sequences, form a canonical run
(`CanonExec`) from `σ_P(i_p)`.  A canonical step is never an exclusion event
(`CanonStep`, third conjunct), so a canonical run has none
(`«def:canonical-system/no-exclusion-event»`).  There is no separate `CAP.System` instance
named "canonical system" in the library. -/
abbrev «def:canonical-system» {D : Type} {n : Nat} (sp : Spec I O)
    (H : Dist.History I O D n) : Prop :=
  Dist.CanonLegal sp H

/-- Def. `def:canonical-system`: "its histories are then exactly those of
Section histories."

Lean: (a) a history admits a canonical annotation iff it satisfies item 3 of
Def. distributed-history; (b) the annotation is unique (canonical runs are
determined by their erasure); (c) a canonical annotation is legal under
`ℬ_S`. -/
theorem «def:canonical-system/histories» {D : Type} {n : Nat} {sp : Spec I O} :
    (∀ H : Dist.History I O D n, Dist.CanonLegal sp H ↔
      ∀ p, ∃ τ : State sp, Exec (canon sp (H.init p)) (Dist.ioOf (H.ev p)) τ) ∧
    (∀ {σ ρ ρ' : State sp} {es es' : List (SEvent sp)}, CanonExec σ es ρ → CanonExec σ es' ρ' →
      es.filterMap SEvent.erase = es'.filterMap SEvent.erase → es = es' ∧ ρ = ρ') ∧
    (∀ H : Dist.History I O D n, Dist.CanonLegal sp H → Dist.SysLegal (canonExclusionBasis sp) H) :=
  ⟨Dist.canonLegal_iff, Dist.canonExec_unique, fun _ h => Dist.canonLegal_sysLegal h⟩

/-- Def. `def:canonical-system`: "… and it performs no exclusion event."
A canonical run (`CanonExec`) contains no exclusion event. -/
theorem «def:canonical-system/no-exclusion-event» {sp : Spec I O} {σ τ : State sp}
    {es : List (SEvent sp)} (h : CanonExec σ es τ) : ∀ γ, SEvent.exclude γ ∉ es :=
  canonExec_noCommit h

/-! ## Compound exclusions -/

/-- **Lemma compound exclusions are exclusions** (`lem:compound-exclusion`).
"The composite of a nonempty sequence of exclusions, defined wherever the
sequence is, is an exclusion."

Lean: the composite of `c :: cs` is a `Exclusion sp` (the type is the claim);
see `…/defined` for "defined wherever the sequence is". -/
noncomputable abbrev «lem:compound-exclusion» {sp : Spec I O} (c : Exclusion sp)
    (cs : List (Exclusion sp)) : Exclusion sp :=
  composite c cs

/-- Lemma `lem:compound-exclusion`: the composite is defined exactly where the
sequence is, with the same result; equivalently, applying `c :: cs` is applying
the one-element sequence `[composite c cs]`. -/
theorem «lem:compound-exclusion/defined» {sp : Spec I O} (c : Exclusion sp)
    (cs : List (Exclusion sp)) (σ ρ : State sp) :
    ((composite c cs).app σ = some ρ ↔ ApplySeq (c :: cs) σ ρ) ∧
    (ApplySeq (c :: cs) σ ρ ↔ ApplySeq [composite c cs] σ ρ) :=
  ⟨compApp_iff, applySeq_composite c cs σ ρ⟩

/-- "A compound output event therefore has the same effect as an event that
applies the composite exclusion alone, and Lemma
canonical-exclusion-normal-form covers it as stated.  In a functional
specification the composite removes every row at each input it touches, so it
input-excludes those inputs."

Lean: (a) `Out_{c::cs}(o)` under `B` is the event `Out_{[composite]}(o)` under
any basis `B'` containing the composite, and back; (b) in a functional
specification the composite input-excludes every input where it removes a row. -/
theorem «app:bases/compound-output-event» {sp : Spec I O} :
    (∀ {B B' : ExclusionBasis sp} {σ τ : State sp} {c : Exclusion sp} {cs : List (Exclusion sp)}
        {o : O}, B' (composite c cs) →
        SysStep B σ (.output (c :: cs) o) τ → SysStep B' σ (.output [composite c cs] o) τ) ∧
    (∀ {B B' : ExclusionBasis sp} {σ τ : State sp} {c : Exclusion sp} {cs : List (Exclusion sp)}
        {o : O}, (∀ c' ∈ c :: cs, B c') →
        SysStep B' σ (.output [composite c cs] o) τ → SysStep B σ (.output (c :: cs) o) τ) ∧
    (sp.Functional → ∀ (c : Exclusion sp) (cs : List (Exclusion sp)) {σ τ : State sp},
        (composite c cs).app σ = some τ →
        ∀ k, (∃ u, σ.R k u ∧ ¬ τ.R k u) → ∀ w, ¬ τ.R k w) :=
  ⟨Dist.sysStep_to_composite, Dist.sysStep_of_composite,
    fun hf c cs _ _ h k hk => Dist.composite_functional_inputExcludes hf c cs h k hk⟩

/-- A compound exclusion event has the same effect as an exclusion event that
applies the composite exclusion alone: "A compound output event
(Definition `def:system-output-event`), or a compound exclusion event,
therefore has the same effect as an event that applies the composite
exclusion alone".

Lean: `commit(c::cs)` under `B` is `commit([composite])` under any basis `B'`
containing the composite, and back. -/
theorem «app:bases/compound-exclusion-event» {sp : Spec I O} {B B' : ExclusionBasis sp}
    {σ τ : State sp} {c : Exclusion sp} {cs : List (Exclusion sp)}
    (hB : ∀ c' ∈ c :: cs, B c') (hB' : B' (composite c cs)) :
    SysStep B σ (.exclude (c :: cs)) τ ↔ SysStep B' σ (.exclude [composite c cs]) τ :=
  Dist.sysStep_exclude_composite_iff hB hB'

/-! ## Runs under a basis -/

/-- **Def. `def:run-under-basis`** (Run under a basis).  "A run under `ℬ` is
a finite transition sequence from a canonical state `σ_P(i)` of input events,
legal output events `Out_γ(o)` (Definition system-output-event), and
exclusion events (Definition exclusion-event) that use only exclusions
from `ℬ`."

Lean: `RunUnder B es τ`, an execution of `SysStep B` (input, output and
exclusion events `SEvent.exclude γ`) from `σ_P(i)`. -/
abbrev «def:run-under-basis» {sp : Spec I O} (B : ExclusionBasis sp) (es : List (SEvent sp))
    (τ : State sp) : Prop :=
  RunUnder B es τ

/-- **Def. `def:canonical-run`** (Canonical run).  "The *canonical runs* are
the runs under the canonical basis `ℬ_S` of Definition
`def:canonical-exclusion-basis` whose output events are all canonical; they
are the runs of Sections functional-calm–complete-calm."

Lean: an execution of canonical steps (`CanonStep`) from `σ_P(i)`. -/
abbrev «def:canonical-run» {sp : Spec I O} (i : I) (es : List (SEvent sp))
    (τ : State sp) : Prop :=
  CanonExec (canon sp i) es τ

/-- Legacy sub-label pointing at `«def:canonical-run»`. -/
abbrev «def:run-under-basis/canonical-run» {sp : Spec I O} (i : I) (es : List (SEvent sp))
    (τ : State sp) : Prop :=
  CanonExec (canon sp i) es τ

/-- Def. `def:run-under-basis`: canonical runs "are the runs of Sections
functional-calm–complete-calm", and they are runs under `ℬ_S`. -/
theorem «def:run-under-basis/canonical-runs-are-runs» {sp : Spec I O} :
    (∀ {σ τ : State sp} {es : List (SEvent sp)},
      CanonExec σ es τ → Exec σ (es.filterMap SEvent.erase) τ) ∧
    (∀ {σ τ : State sp} {es : List (Event I O)},
      Exec σ es τ → ∃ es' : List (SEvent sp), es'.filterMap SEvent.erase = es ∧ CanonExec σ es' τ) ∧
    (∀ {σ τ : State sp} {es : List (SEvent sp)},
      CanonExec σ es τ → SysExec (canonExclusionBasis sp) σ es τ) :=
  ⟨canonExec_exec, exec_canonExec, canonExec_sysExec⟩

/-- "Call two runs observably equivalent when they start at the same canonical
state and agree once exclusion sequences are erased and exclusion events
dropped: wherever one has `input(j)` the other does, and wherever one has
`Out_γ(o)` the other has `Out_{γ'}(o)` for some `γ'`."

Lean: the event lists agree after `filterMap SEvent.erase`, which erases `γ`
and drops exclusion events (`SEvent.erase (.exclude γ) = none`); the common start
state is fixed by the context. -/
abbrev «app:bases/observably-equivalent» {sp : Spec I O} (es es' : List (SEvent sp)) : Prop :=
  es.filterMap SEvent.erase = es'.filterMap SEvent.erase

/-- **Lemma canonical equivalents** (`lem:canonical-equivalent`).  "Every run
under any exclusion basis is observably equivalent to a canonical run.  After
each event, the canonical run's remainder table contains the original run's."

Lean: from a run under `B` from `σ_P(i)`, a canonical run from the same
`σ_P(i)` in `Lockstep` (after each event: erasures agree, current inputs
agree, and the canonical table contains the original's; an exclusion event of
the original is matched by no canonical event, and the canonical table still
contains the original's, since an exclusion only removes rows); its erasure is
a run of §§2–3 ending at `ρ'` with the same current input and a larger table.
(The paper's proof treats input and output events; the exclusion-event case
is the `Lockstep.exclude` step of `CC.canonical_equivalent_gen`.) -/
theorem «lem:canonical-equivalent» {sp : Spec I O} {B : ExclusionBasis sp} {i : I}
    {es : List (SEvent sp)} {ρ : State sp} (h : SysExec B (canon sp i) es ρ) :
    ∃ es' ρ', Lockstep B (canon sp i) es ρ (canon sp i) es' ρ' ∧
      es.filterMap SEvent.erase = es'.filterMap SEvent.erase ∧
      Exec (canon sp i) (es.filterMap SEvent.erase) ρ' ∧
      ρ'.cur = ρ.cur ∧ (∀ k u, ρ.R k u → ρ'.R k u) :=
  canonical_equivalent h

/-- **Cor. reconciliation under any basis** (`cor:reconciliation-any-basis`).
"Let runs under any exclusion bases end at `(i_r,R_r)`, and let `j` be a common
expansion of the `i_r`.  If some continuations, whose output and exclusion
events may apply any exclusions, bring them to a common state with current input `j`, then some
`u ∈ P(j)` refines every output emitted on every run."

Lean: the finite family is indexed by `Fin m`; run `r` is under basis `B r`
and its continuation under `B' r`.  The hypothesis that `j` is a common
expansion is not needed (it follows from reaching a state with input `j`). -/
theorem «cor:reconciliation-any-basis» {sp : Spec I O} {m : Nat} (B B' : Fin m → ExclusionBasis sp)
    (i : Fin m → I) (es : Fin m → List (SEvent sp)) (ρ : Fin m → State sp)
    (hrun : ∀ r, SysExec (B r) (canon sp (i r)) (es r) (ρ r))
    (τ : State sp) (j : I) (hτ : τ.cur = j)
    (hcont : ∀ r, ∃ es', SysExec (B' r) (ρ r) es' τ) :
    ∃ u, sp.P j u ∧ ∀ r, ∀ o ∈ outs ((es r).filterMap SEvent.erase), o ≼ u :=
  Dist.reconciliation_any_basis B B' i es ρ hrun τ j hτ hcont

/-- "The converse of Lemma canonical-equivalent fails: a canonical run need not
be observably equivalent to any run under a particular system's basis.  That
basis may lack the exclusion an output event requires, and so disable the
output altogether.  Restricting attention to one system's runs could therefore
hide non-monotonicity."

Lean: `Dist.spU` has one input and two incomparable outputs; under the empty
basis `Dist.noExclusionBasis` (a) the canonical run `output(true)` has no observably
equivalent run, and (b) `spU` is not consistent, yet every finite family of
runs under the empty basis is confluent, within that basis, at every input. -/
theorem «app:bases/converse-fails» :
    ((∃ τ, Exec (canon Dist.spU ()) [.output (true : Bool)] τ) ∧
      ¬ ∃ (es : List (SEvent Dist.spU)) (ρ : State Dist.spU),
          SysExec Dist.noExclusionBasis (canon Dist.spU ()) es ρ ∧
          es.filterMap SEvent.erase = [.output (true : Bool)]) ∧
    (¬ Dist.spU.Consistent ∧
      ∀ fam : List (State Dist.spU),
        (∀ σ ∈ fam, ∃ i es, SysExec Dist.noExclusionBasis (canon Dist.spU i) es σ) →
        ∀ j : Dist.U1, ∃ τ : State Dist.spU, τ.cur = j ∧
          ∀ σ ∈ fam, ∃ es, SysExec Dist.noExclusionBasis σ es τ) :=
  ⟨Dist.converse_fails, Dist.system_runs_hide_nonmonotonicity⟩

/-! ## Application-specific exclusions -/

/-- *Application-specific exclusions.*  "Locks and timestamps are exclusions
of this kind: two-phase locking issues an exclusion to an order among some transactions, and
timestamp assignment places one transaction relative to all others."

Lean: for any transaction specification whose fibers are antichains, the 2PL
basis `{order, commit, abort}`; the exclusions are `Txn.orderC`,
`Txn.commitC`, `Txn.abortC` (Appendix G, `app:cc-bases`). -/
abbrev «app:bases/basis-2PL» {T : Type} (sp : Spec (Txn.FinSet T) (Txn.Outcome T))
    (hA : Txn.Antichain sp) : ExclusionBasis sp :=
  Txn.basis2PL sp hA

/-- *Application-specific exclusions*: the MVTO basis
`{stamp, commit, abort}` (exclusions `Txn.stampC`, `Txn.commitC`,
`Txn.abortC`). -/
abbrev «app:bases/basis-MVTO» {T : Type} (sp : Spec (Txn.FinSet T) (Txn.Outcome T))
    (hA : Txn.Antichain sp) : ExclusionBasis sp :=
  Txn.basisMVTO sp hA

end CC.Paper
