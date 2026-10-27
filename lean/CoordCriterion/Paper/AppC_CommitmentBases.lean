import CoordCriterion.Distributed.Systems
import CoordCriterion.Figures
import CoordCriterion.Appendix.TransactionBases.NoReads

/-!
# Paper Appendix C: Output events and commitment bases (statement layer)

Covers `appendices/commitment-bases-general.tex` (`app:bases`): first the
formal lifted output events (`app:lifted-output-events`: the sets `Sealed_o`,
`Retired_o`, `Rejected_o`, Def. `def:lifted-output-event`, the remarks after
it, and Prop. `prop:exposability`), then (`app:commitment-bases`)
the canonical basis and canonical event, the paragraph *The canonical seals and choices are
commitments*, Lemma `lem:canonical-commitment-normal-form` (three parts),
Def. `def:canonical-system`, Lemma `lem:compound-commitment` and the remark
after it, Def. `def:run-under-basis`, observable equivalence,
Lemma `lem:canonical-equivalent`, Cor. `cor:reconciliation-any-basis`, the
failure of the converse, and *Application-specific commitments*.

How to read this file.  Read it side by side with the appendix.  Entries are
in the appendix's order; each numbered result is named by its LaTeX label and
each unlabeled claim by `«app:bases/<slug>»`.  Docstrings quote the paper
(LaTeX lightly turned into Unicode) and explain any difference in reading.
Statements are written out; proofs are one-line references to
`CoordCriterion/Distributed/Commitments.lean` (namespace `CC`) and
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


/-- **Eq. `eq:seal-inputs`**: `Sealed_o = {(k,x) ∈ R : k ∉ in(R[out ⪰ o])}`.
Lean: `Sealed σ o k x` is `σ.R k x ∧ ¬ ∃ u, σ.R k u ∧ o ≼ u`. -/
abbrev «eq:seal-inputs» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) : Table I O :=
  Sealed σ o

/-- **Eq. `eq:output-retirements`**: `Retired_o = {(k,x) ∈ R ∖ R[out ⪰ o] :
x ≼ u for some u ∈ R[out ⪰ o](k)}`. -/
abbrev «eq:output-retirements» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) : Table I O :=
  Retired σ o

/-- **Eq. `eq:choice-removals`**: `Rejected_o = (R ∖ R[out ⪰ o]) ∖ (Sealed_o ∪
Retired_o)`. -/
abbrev «eq:choice-removals» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) : Table I O :=
  Rejected σ o

/-- **Def. `def:lifted-output-event`** (Lifted output event, seal, output
retirement, choice).  "`output(o)` keeps exactly the rows whose outputs
refine `o` and emits `o`, atomically, ending at `(i, R[out ⪰ o])` … When
`Sealed_o ≠ ∅` it applies the *seal* `s_o`. … When `Rejected_o ≠ ∅` it
applies the *choice* `c_o`. … `s_o(i,R) = (i, R ∖ Sealed_o)`,
`c_o(i,R) = (i, R ∖ Rejected_o)`."

Lean: the event is `Step σ (.output o) τ` with `τ.R = outputTable σ o`,
the same transition as Def. `def:output-event`; the two commitments as states
are `sealState σ o _` and `chooseState σ o _` (as commitments in the sense of
Def. `def:commitment`, §4.3: `CC.sealC o`, `CC.choiceC o`).  This
declaration names the pair `(s_o, c_o)`. -/
abbrev «def:lifted-output-event» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) (ho : σ.R σ.cur o) : State sp × State sp :=
  (sealState σ o ho, chooseState σ o ho)

/-- **Eq. `eq:canonical-seal-commitment-relational`**:
"`s_o(i,R) = (i, R ∖ Sealed_o)`, `c_o(i,R) = (i, R ∖ Rejected_o)`."  Both
keep the current input; `sealState` removes exactly `Sealed_o`, `chooseState`
exactly `Rejected_o`. -/
theorem «eq:canonical-seal-commitment-relational» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} (σ : State sp) (o : O) (ho : σ.R σ.cur o) :
    ((sealState σ o ho).cur = σ.cur ∧
        ∀ k x, (sealState σ o ho).R k x ↔ σ.R k x ∧ ¬ Sealed σ o k x) ∧
      ((chooseState σ o ho).cur = σ.cur ∧
        ∀ k x, (chooseState σ o ho).R k x ↔ σ.R k x ∧ ¬ Rejected σ o k x) :=
  ⟨⟨rfl, fun _ _ => Iff.rfl⟩, ⟨rfl, fun _ _ => Iff.rfl⟩⟩

/-- After Def. `def:lifted-output-event`: "In Figure `fig:ambiguity-frames`(f),
emitting `[A,B]` places `[B,A]` in `Rejected_o` … In panel (g), the two
removed route sets are in `Retired_o`." -/
theorem «def:lifted-output-event/examples» :
    Rejected (canon Figures.Txn.spec ()) .ab () .ba ∧
      Retired (canon Figures.Trace.spec ()) Figures.Trace.rS1 () Figures.Trace.rA ∧
      Retired (canon Figures.Trace.spec ()) Figures.Trace.rS1 () Figures.Trace.rA2 :=
  ⟨Figures.Txn.ba_rejected.1, Figures.Trace.removed_retired.2.1,
   Figures.Trace.removed_retired.2.2.1⟩

/-- "The three sets are disjoint." -/
theorem «app:lifted-output-events/disjoint» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) (k : I) (x : O) :
    ¬ (Sealed σ o k x ∧ Retired σ o k x) ∧ ¬ (Sealed σ o k x ∧ Rejected σ o k x) ∧
      ¬ (Retired σ o k x ∧ Rejected σ o k x) :=
  ⟨sealed_retired_disjoint σ o, sealed_rejected_disjoint σ o, retired_rejected_disjoint σ o⟩

/-- "… removing the rows of either commitment leaves the other sets
unchanged, so the event may apply `s_o` and `c_o` in either order." -/
theorem «app:lifted-output-events/commute» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) (ho : σ.R σ.cur o) :
    (∀ k x, Retired (sealState σ o ho) o k x ↔ Retired σ o k x) ∧
      (∀ k x, Rejected (sealState σ o ho) o k x ↔ Rejected σ o k x) ∧
      (∀ k x, Sealed (chooseState σ o ho) o k x ↔ Sealed σ o k x) ∧
      (∀ k x, Retired (chooseState σ o ho) o k x ↔ Retired σ o k x) ∧
      (∀ h₁ h₂, (chooseState (sealState σ o ho) o h₁).R =
        (sealState (chooseState σ o ho) o h₂).R) :=
  ⟨seal_retired σ o ho, seal_rejected σ o ho, choose_sealed σ o ho, choose_retired σ o ho,
   seal_choose_comm σ o ho⟩

/-- "The choice commitment only narrows fibers: at each input it touches, some
row that refines `o` survives." -/
theorem «app:lifted-output-events/choice-narrows» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} (σ : State sp) (o : O) {k : I} {x : O} (h : Rejected σ o k x) :
    ∃ u, σ.R k u ∧ o ≼ u :=
  choice_narrows σ o h

/-- "With one row per input, `Retired_o` and `Rejected_o` are empty; this is
the functional output event of Definition `def:output-event`." -/
theorem «app:lifted-output-events/functional» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) (σ : State sp) (o : O) (k : I) (x : O) :
    ¬ Retired σ o k x ∧ ¬ Rejected σ o k x :=
  functional_retired_rejected_empty hf σ o k x

/-- "Exposability lifts with the event: `o` is exposable when `output(o)`
applies no commitment, that is, when `Sealed_o` and `Rejected_o` are empty." -/
theorem «app:lifted-output-events/exposable» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) :
    Exposable σ o ↔ (∀ k x, ¬ Sealed σ o k x) ∧ (∀ k x, ¬ Rejected σ o k x) :=
  exposable_iff_no_commitment σ o

/-- **Prop. `prop:exposability`** (Lifted exposure test).  "An output
`o ∈ R(i)` is exposable at `(i,R)` if and only if, for every legal `j ⪰ i`
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

/-! ## Commitment bases and compound commitments (`app:commitment-bases`) -/

/-! ## Canonical basis, canonical event -/

/-- **Def. canonical basis, canonical event** (`def:canonical-commitment-basis`),
the basis.  "`ℬ_S = {s_o : o ∈ O, dom(s_o) ≠ ∅} ∪ {c_o : o ∈ O, dom(c_o) ≠ ∅}`,
where `s_o` is defined at the states with `o ∈ R(i)` and `Sealed_o ≠ ∅`, and
`c_o` at those with `o ∈ R(i)` and `Rejected_o ≠ ∅`."
(Eq. canonical-commitment-basis-relational.) -/
abbrev «def:canonical-commitment-basis» (sp : Spec I O) : Basis sp := canonBasis sp

/-- **Eq. `eq:canonical-commitment-basis-relational`**:
"`ℬ_S = {s_o : o ∈ O, dom(s_o) ≠ ∅} ∪ {c_o : o ∈ O, dom(c_o) ≠ ∅}`."  A
commitment is in `canonBasis sp` iff it is some `sealC o` or `choiceC o`
defined at some state. -/
theorem «eq:canonical-commitment-basis-relational» {sp : Spec I O} (c : Commitment sp) :
    canonBasis sp c ↔
      ∃ o : O, (c = sealC o ∧ ∃ σ τ : State sp, (sealC o).app σ = some τ) ∨
        (c = choiceC o ∧ ∃ σ τ : State sp, (choiceC o).app σ = some τ) :=
  Iff.rfl

/-- Def. `def:canonical-commitment-basis`: "At `(i,R)`, let `κ_o` apply `s_o`
when `Sealed_o ≠ ∅` and `c_o` when `Rejected_o ≠ ∅`, so `κ_o` is one of `ε`,
`s_o`, `c_o`, or `s_o c_o`." -/
theorem «def:canonical-commitment-basis/kappa» {sp : Spec I O} (σ : State sp) (o : O) :
    kappa σ o =
      (if ∃ k x, Sealed σ o k x then [sealC o] else []) ++
      (if ∃ k x, Rejected σ o k x then [choiceC o] else []) :=
  rfl

/-- Def. `def:canonical-commitment-basis`: "The canonical event for `o` is
`Out_{κ_o}(o)`: the output event of Definition lifted-output-event, and with one
row per input that of Definition output-event."

Lean: (a) canonical steps are exactly the steps of §§2–3 (both directions);
(b) with one row per input, `κ_o` is at most the seal, and the seal leaves
`R[out ⪰ o]`, the table of Def. output-event. -/
theorem «def:canonical-commitment-basis/canonical-event» {sp : Spec I O} :
    ((∀ (σ τ : State sp) (e : SEvent sp), CanonStep σ e τ →
      ∃ e' : Event I O, e.erase = some e' ∧ Step σ e' τ) ∧
     (∀ (σ τ : State sp) (e : Event I O), Step σ e τ →
        ∃ e' : SEvent sp, e'.erase = some e ∧ CanonStep σ e' τ)) ∧
    (sp.Functional →
      (∀ (σ : State sp) (o : O),
        kappa σ o = (if ∃ k x, Sealed σ o k x then [sealC o] else [])) ∧
      (∀ (σ : State sp) (o : O) (ho : σ.R σ.cur o),
        (cmSealState σ o ho).R = outputTable σ o)) :=
  ⟨⟨fun _ _ _ => canonStep_step, fun _ _ _ => step_canonStep⟩,
    fun hf => ⟨Dist.functional_kappa hf, Dist.functional_seal_eq hf⟩⟩

/-! ## The canonical seals and choices are commitments -/

/-- *The canonical seals and choices are commitments.*  "With one row per input,
Equation commitment-excludes holds vacuously, so the seals of Definition
output-event are commitments."

Lean: in a functional specification, Eq. commitment-excludes holds for any
pair of states. -/
theorem «app:bases/functional-excludes-vacuous» {sp : Spec I O} (hf : sp.Functional)
    (σ τ : State sp) : ∀ k u w, σ.R k u → ¬ τ.R k u → τ.R k w → ¬ (u ≼ w) :=
  Dist.functional_excludes_vacuous hf σ τ

/-- *The canonical seals and choices are commitments* (`s_o`).  "With several
outputs per input, the seal `s_o` of Definition lifted-output-event removes
every row at the inputs of `Sealed_o`, so nothing remains there to refine a
removed row."

Lean: `sealC o : Commitment sp` is the commitment (its `excludes` field is the
argument); it is defined exactly where the definition says and leaves
`R ∖ Sealed_o`. -/
theorem «app:bases/seal-is-commitment» {sp : Spec I O} (o : O) (σ τ : State sp) :
    (sealC o : Commitment sp).app σ = some τ ↔
      ∃ h : σ.R σ.cur o, (∃ k x, Sealed σ o k x) ∧ cmSealState σ o h = τ :=
  sealApp_eq

/-- *The canonical seals and choices are commitments* (`c_o`).  "For `c_o`,
suppose some `x ∈ Rejected_o` at input `k` were refined by a row `y` that `c_o`
leaves at `k` … so `x ∈ Retired_o`, a contradiction."

Lean: `choiceC o : Commitment sp` is the commitment (its `excludes` field is
this argument); it is defined exactly where the definition says and leaves
`R ∖ Rejected_o`. -/
theorem «app:bases/choice-is-commitment» {sp : Spec I O} (o : O) (σ τ : State sp) :
    (choiceC o : Commitment sp).app σ = some τ ↔
      σ.R σ.cur o ∧ (∃ k x, Rejected σ o k x) ∧ cmChooseState σ o = τ :=
  chooseApp_eq

/-- *The canonical seals and choices are commitments.*  "Since `s_o` and `c_o`
remove disjoint sets of rows and neither changes the other's …, each is defined
on the state the other leaves, and the canonical event may apply them in either
order."

Lean: if both classes are nonempty, `s_o; c_o` and `c_o; s_o` are both defined
and reach the same state, with table `R ∖ (Sealed_o ∪ Rejected_o)`. -/
theorem «app:bases/seal-choice-commute» {sp : Spec I O} {σ : State sp} {o : O}
    (hS : ∃ k x, Sealed σ o k x) (hJ : ∃ k x, Rejected σ o k x) (ho : σ.R σ.cur o) :
    ∃ τ₁ τ₂ ρ₁ ρ₂ : State sp,
      (sealC o).app σ = some τ₁ ∧ (choiceC o).app τ₁ = some ρ₁ ∧
      (choiceC o).app σ = some τ₂ ∧ (sealC o).app τ₂ = some ρ₂ ∧
      ρ₁ = ρ₂ ∧ ρ₁.cur = σ.cur ∧ ρ₁.R = Pruned σ o :=
  seal_choice_commute hS hJ ho

/-! ## Lemma containment, canonical support, commitment-free events -/

/-- **Lemma containment, canonical support, and commitment-free events**
(`lem:canonical-commitment-normal-form`).  Let `(i,R)` be a state and
`o ∈ R(i)`.

1. "Every legal output event `Out_γ(o)` takes `(i,R)` to some `(i,R')` with
   `R' ⊆ R[out ⪰ o]`, and removes the rows in `Sealed_o` and `Rejected_o` by
   commitment."
2. "The canonical event `Out_{κ_o}(o)` is legal and takes `(i,R)` to
   `(i,R[out ⪰ o])`, so it retains every row that any legal `Out_γ(o)`
   retains."
3. "If `Out_ε(o)` is legal, it takes `(i,R)` to `(i,R[out ⪰ o])`; it is legal
   exactly when `o` is exposable."

Lean, conjunct by conjunct.  (1) for any basis `B`: the event keeps the current
input, ends inside `R[out ⪰ o]`, and the state `σc` left by `γ` (before
retirement) contains no row of `Sealed_o ∪ Rejected_o` — "by commitment".
(2) `Out_{κ_o}(o)` is legal under `ℬ_S` and ends at `outState σ o ho`, whose
table is `R[out ⪰ o]`; every legal `Out_γ(o)` ends inside that table.
(3) `Out_ε(o)` is legal (under any basis) iff `o ∈ R(i)` is exposable, and then
ends at `(i, R[out ⪰ o])`; exposability is "`Sealed_o` and `Rejected_o` are
empty". -/
theorem «lem:canonical-commitment-normal-form» {sp : Spec I O} :
    (∀ {B : Basis sp} {σ τ : State sp} {γ : List (Commitment sp)} {o : O},
      SysStep B σ (.output γ o) τ →
      τ.cur = σ.cur ∧ σ.R σ.cur o ∧ (∀ k u, τ.R k u → σ.R k u ∧ o ≼ u) ∧
      ∃ σc, ApplySeq γ σ σc ∧ ∀ k x, (Sealed σ o k x ∨ Rejected σ o k x) → ¬ σc.R k x) ∧
    (∀ (σ : State sp) (o : O) (ho : σ.R σ.cur o),
      SysStep (canonBasis sp) σ (.output (kappa σ o) o) (outState σ o ho) ∧
      (outState σ o ho).cur = σ.cur ∧ (outState σ o ho).R = outputTable σ o ∧
      ∀ {B : Basis sp} {τ : State sp} {γ : List (Commitment sp)},
        SysStep B σ (.output γ o) τ → ∀ k u, τ.R k u → outputTable σ o k u) ∧
    (∀ {B : Basis sp} {σ τ : State sp} {o : O},
      (SysStep B σ (.output [] o) τ ↔
        σ.R σ.cur o ∧ Exposable σ o ∧ τ.cur = σ.cur ∧ τ.R = outputTable σ o) ∧
      (Exposable σ o ↔ (¬ ∃ k x, Sealed σ o k x) ∧ ¬ ∃ k x, Rejected σ o k x)) :=
  ⟨fun h => containment h,
    fun σ o ho => ⟨canonical_support σ o ho, rfl, rfl, fun h => canonical_maximal h⟩,
    fun {_ σ _ o} => ⟨eps_step_iff, exposable_iff_empty σ o⟩⟩

/-! ## Canonical system -/

/-- **Def. canonical system** (`def:canonical-system`).  "A system is canonical
when its basis is `ℬ_S` and each output event it performs is the canonical
event `Out_{κ_o}(o)` at the participant's state where it occurs, and it
performs no commitment event."

Lean: stated on histories, as the property that each participant's
input/output events, annotated with commitment sequences, form a canonical run
(`CanonExec`) from `σ_S(i_p)`.  A canonical step is never a commitment event
(`CanonStep`, third conjunct), so a canonical run has none
(`«def:canonical-system/no-commitment-event»`).  There is no separate `CAP.System` instance
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
    (∀ H : Dist.History I O D n, Dist.CanonLegal sp H → Dist.SysLegal (canonBasis sp) H) :=
  ⟨Dist.canonLegal_iff, Dist.canonExec_unique, fun _ h => Dist.canonLegal_sysLegal h⟩

/-- Def. `def:canonical-system`: "… and it performs no commitment event."
A canonical run (`CanonExec`) contains no commit event. -/
theorem «def:canonical-system/no-commitment-event» {sp : Spec I O} {σ τ : State sp}
    {es : List (SEvent sp)} (h : CanonExec σ es τ) : ∀ γ, SEvent.commit γ ∉ es :=
  canonExec_noCommit h

/-! ## Compound commitments -/

/-- **Lemma compound commitments are commitments** (`lem:compound-commitment`).
"The composite of a nonempty sequence of commitments, defined wherever the
sequence is, is a commitment."

Lean: the composite of `c :: cs` is a `Commitment sp` (the type is the claim);
see `…/defined` for "defined wherever the sequence is". -/
noncomputable abbrev «lem:compound-commitment» {sp : Spec I O} (c : Commitment sp)
    (cs : List (Commitment sp)) : Commitment sp :=
  composite c cs

/-- Lemma `lem:compound-commitment`: the composite is defined exactly where the
sequence is, with the same result; equivalently, applying `c :: cs` is applying
the one-element sequence `[composite c cs]`. -/
theorem «lem:compound-commitment/defined» {sp : Spec I O} (c : Commitment sp)
    (cs : List (Commitment sp)) (σ ρ : State sp) :
    ((composite c cs).app σ = some ρ ↔ ApplySeq (c :: cs) σ ρ) ∧
    (ApplySeq (c :: cs) σ ρ ↔ ApplySeq [composite c cs] σ ρ) :=
  ⟨compApp_iff, applySeq_composite c cs σ ρ⟩

/-- "A compound output event therefore has the same effect as an event that
applies the composite commitment alone, and Lemma
canonical-commitment-normal-form covers it as stated.  In a functional
specification the composite removes every row at each input it touches, so it
seals."

Lean: (a) `Out_{c::cs}(o)` under `B` is the event `Out_{[composite]}(o)` under
any basis `B'` containing the composite, and back; (b) in a functional
specification the composite seals every input where it removes a row. -/
theorem «app:bases/compound-output-event» {sp : Spec I O} :
    (∀ {B B' : Basis sp} {σ τ : State sp} {c : Commitment sp} {cs : List (Commitment sp)}
        {o : O}, B' (composite c cs) →
        SysStep B σ (.output (c :: cs) o) τ → SysStep B' σ (.output [composite c cs] o) τ) ∧
    (∀ {B B' : Basis sp} {σ τ : State sp} {c : Commitment sp} {cs : List (Commitment sp)}
        {o : O}, (∀ c' ∈ c :: cs, B c') →
        SysStep B' σ (.output [composite c cs] o) τ → SysStep B σ (.output (c :: cs) o) τ) ∧
    (sp.Functional → ∀ (c : Commitment sp) (cs : List (Commitment sp)) {σ τ : State sp},
        (composite c cs).app σ = some τ →
        ∀ k, (∃ u, σ.R k u ∧ ¬ τ.R k u) → ∀ w, ¬ τ.R k w) :=
  ⟨Dist.sysStep_to_composite, Dist.sysStep_of_composite,
    fun hf c cs _ _ h k hk => Dist.composite_functional_seals hf c cs h k hk⟩

/-! ## Runs under a basis -/

/-- **Def. run under a basis, canonical run** (`def:run-under-basis`).  "A run under `ℬ` is a
finite transition sequence from a canonical state `σ_S(i)` of input events,
legal output events `Out_γ(o)` (Definition system-output-event), and
commitment events (Definition commitment-event) that use only commitments from
`ℬ`."  Lean: `RunUnder B es τ`, an execution of `SysStep B` (input, output and
commit events `SEvent.commit γ`) from `σ_S(i)`. -/
abbrev «def:run-under-basis» {sp : Spec I O} (B : Basis sp) (es : List (SEvent sp))
    (τ : State sp) : Prop :=
  RunUnder B es τ

/-- Def. `def:run-under-basis`: "The canonical runs are the runs under the
canonical basis `ℬ_S` … whose output events are all canonical."

Lean: an execution of canonical steps (`CanonStep`) from `σ_S(i)`. -/
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
      CanonExec σ es τ → SysExec (canonBasis sp) σ es τ) :=
  ⟨canonExec_exec, exec_canonExec, canonExec_sysExec⟩

/-- "Call two runs observably equivalent when they start at the same canonical
state and agree once commitment sequences are erased and commitment events
dropped: wherever one has `input(j)` the other does, and wherever one has
`Out_γ(o)` the other has `Out_{γ'}(o)` for some `γ'`."

Lean: the event lists agree after `filterMap SEvent.erase`, which erases `γ`
and drops commit events (`SEvent.erase (.commit γ) = none`); the common start
state is fixed by the context. -/
abbrev «app:bases/observably-equivalent» {sp : Spec I O} (es es' : List (SEvent sp)) : Prop :=
  es.filterMap SEvent.erase = es'.filterMap SEvent.erase

/-- **Lemma canonical equivalents** (`lem:canonical-equivalent`).  "Every run
under any commitment basis is observably equivalent to a canonical run.  After
each event, the canonical run's remainder table contains the original run's."

Lean: from a run under `B` from `σ_S(i)`, a canonical run from the same
`σ_S(i)` in `Lockstep` (after each event: erasures agree, current inputs
agree, and the canonical table contains the original's; a commitment event of
the original is matched by no canonical event, and the canonical table still
contains the original's, since a commitment only removes rows); its erasure is
a run of §§2–3 ending at `ρ'` with the same current input and a larger table.
(The paper's proof treats input and output events; the commitment-event case
is the `Lockstep.commit` step of `CC.canonical_equivalent_gen`.) -/
theorem «lem:canonical-equivalent» {sp : Spec I O} {B : Basis sp} {i : I}
    {es : List (SEvent sp)} {ρ : State sp} (h : SysExec B (canon sp i) es ρ) :
    ∃ es' ρ', Lockstep B (canon sp i) es ρ (canon sp i) es' ρ' ∧
      es.filterMap SEvent.erase = es'.filterMap SEvent.erase ∧
      Exec (canon sp i) (es.filterMap SEvent.erase) ρ' ∧
      ρ'.cur = ρ.cur ∧ (∀ k u, ρ.R k u → ρ'.R k u) :=
  canonical_equivalent h

/-- **Cor. reconciliation under any basis** (`cor:reconciliation-any-basis`).
"Let runs under any commitment bases end at `(i_r,R_r)`, and let `j` be a common
expansion of the `i_r`.  If some continuations, whose output events may apply
any commitments, bring them to a common state with current input `j`, then some
`u ∈ S(j)` refines every output emitted on every run."

Lean: the finite family is indexed by `Fin m`; run `r` is under basis `B r`
and its continuation under `B' r`.  The hypothesis that `j` is a common
expansion is not needed (it follows from reaching a state with input `j`). -/
theorem «cor:reconciliation-any-basis» {sp : Spec I O} {m : Nat} (B B' : Fin m → Basis sp)
    (i : Fin m → I) (es : Fin m → List (SEvent sp)) (ρ : Fin m → State sp)
    (hrun : ∀ r, SysExec (B r) (canon sp (i r)) (es r) (ρ r))
    (τ : State sp) (j : I) (hτ : τ.cur = j)
    (hcont : ∀ r, ∃ es', SysExec (B' r) (ρ r) es' τ) :
    ∃ u, sp.S j u ∧ ∀ r, ∀ o ∈ outs ((es r).filterMap SEvent.erase), o ≼ u :=
  Dist.reconciliation_any_basis B B' i es ρ hrun τ j hτ hcont

/-- "The converse of Lemma canonical-equivalent fails: a canonical run need not
be observably equivalent to any run under a particular system's basis.  That
basis may lack the commitment an output event requires, and so disable the
output altogether.  Restricting attention to one system's runs could therefore
hide non-monotonicity."

Lean: `Dist.spU` has one input and two incomparable outputs; under the empty
basis `Dist.noBasis` (a) the canonical run `output(true)` has no observably
equivalent run, and (b) `spU` is not consistent, yet every finite family of
runs under the empty basis is confluent, within that basis, at every input. -/
theorem «app:bases/converse-fails» :
    ((∃ τ, Exec (canon Dist.spU ()) [.output (true : Bool)] τ) ∧
      ¬ ∃ (es : List (SEvent Dist.spU)) (ρ : State Dist.spU),
          SysExec Dist.noBasis (canon Dist.spU ()) es ρ ∧
          es.filterMap SEvent.erase = [.output (true : Bool)]) ∧
    (¬ Dist.spU.Consistent ∧
      ∀ fam : List (State Dist.spU),
        (∀ σ ∈ fam, ∃ i es, SysExec Dist.noBasis (canon Dist.spU i) es σ) →
        ∀ j : Dist.U1, ∃ τ : State Dist.spU, τ.cur = j ∧
          ∀ σ ∈ fam, ∃ es, SysExec Dist.noBasis σ es τ) :=
  ⟨Dist.converse_fails, Dist.system_runs_hide_nonmonotonicity⟩

/-! ## Application-specific commitments -/

/-- *Application-specific commitments.*  "Locks and timestamps are commitments
of this kind: two-phase locking issues a commitment to an order among some transactions, and
timestamp assignment places one transaction relative to all others."

Lean: for any transaction specification whose fibers are antichains, the 2PL
basis `{order, commit, abort}`; the commitments are `Txn.orderC`,
`Txn.commitC`, `Txn.abortC` (Appendix G, `app:cc-bases`). -/
abbrev «app:bases/basis-2PL» {T : Type} (sp : Spec (Txn.FinSet T) (Txn.Outcome T))
    (hA : Txn.Antichain sp) : Basis sp :=
  Txn.basis2PL sp hA

/-- *Application-specific commitments*: the MVTO basis
`{stamp, commit, abort}` (commitments `Txn.stampC`, `Txn.commitC`,
`Txn.abortC`). -/
abbrev «app:bases/basis-MVTO» {T : Type} (sp : Spec (Txn.FinSet T) (Txn.Outcome T))
    (hA : Txn.Antichain sp) : Basis sp :=
  Txn.basisMVTO sp hA

end CC.Paper
