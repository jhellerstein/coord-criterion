import CoordCriterion.Distributed.Systems
import CoordCriterion.Figures
import CoordCriterion.Appendix.TransactionBases.NoReads

/-!
# Paper Appendix C: Output events and exclusion bases (statement layer)

This file mirrors `appendices/exclusion-bases-general.tex`.  A ruled-out row is
`Subsumed` when a surviving row at the same input refines it, and `Excluded`
otherwise.  The canonical event applies at most one `canonicalExclusion`.
-/

namespace CC.Paper

open CC Classical

variable {I O : Type} [PO I] [PO O]

section LiftedOutputEvents

open CC.CALM

/-- **Eq. `eq:output-subsumptions`**: ruled-out rows refined by a kept row at the
same input. -/
abbrev «eq:output-subsumptions» {sp : Spec I O} (σ : State sp) (o : O) : Table I O :=
  Subsumed σ o

/-- **Eq. `eq:exclusion-removals`**: ruled-out rows not in `Subsumed_o`. -/
abbrev «eq:exclusion-removals» {sp : Spec I O} (σ : State sp) (o : O) : Table I O :=
  Excluded σ o

/-- **Def. `def:lifted-output-event`**.  The output event keeps exactly the rows
whose outputs refine `o`; removed rows with a surviving refinement are removed
by output subsumption. -/
abbrev «def:lifted-output-event» {sp : Spec I O}
    (σ : State sp) (o : O) (ho : σ.R σ.cur o) : State sp :=
  outputState σ o ho

/-- **Def. `def:canonical-exclusion`**.  When `Excluded_o` is nonempty, `x_o`
removes it. -/
noncomputable abbrev «def:canonical-exclusion» {sp : Spec I O} (o : O) : Exclusion sp :=
  canonicalExclusion o

/-- **Eq. `eq:canonical-exclusion-relational`**: `x_o(i,R)=(i,R∖Excluded_o)`. -/
theorem «eq:canonical-exclusion-relational» {sp : Spec I O}
    (σ : State sp) (o : O) (ho : σ.R σ.cur o) :
    (excludeState σ o ho).cur = σ.cur ∧
      ∀ k x, (excludeState σ o ho).R k x ↔ σ.R k x ∧ ¬ Excluded σ o k x :=
  ⟨rfl, fun _ _ => Iff.rfl⟩

/-- The ambiguity example excludes `[B,A]`; the routing example only subsumes
its removed route sets. -/
theorem «def:lifted-output-event/examples» :
    Excluded (canon Figures.Txn.spec ()) .ab () .ba ∧
      Subsumed (canon Figures.Trace.spec ()) Figures.Trace.rS1 () Figures.Trace.rA ∧
      Subsumed (canon Figures.Trace.spec ()) Figures.Trace.rS1 () Figures.Trace.rA2 :=
  ⟨Figures.Txn.ba_excluded.1, Figures.Trace.removed_subsumed.2.1,
   Figures.Trace.removed_subsumed.2.2.1⟩

/-- `Subsumed_o` and `Excluded_o` are disjoint. -/
theorem «app:lifted-output-events/disjoint» {sp : Spec I O}
    (σ : State sp) (o : O) (k : I) (x : O) :
    ¬ (Subsumed σ o k x ∧ Excluded σ o k x) :=
  subsumed_excluded_disjoint σ o

/-- With one row per input, no ruled-out row is subsumed. -/
theorem «app:lifted-output-events/functional» {sp : Spec I O}
    (hf : sp.Functional) (σ : State sp) (o : O) (k : I) (x : O) :
    ¬ Subsumed σ o k x :=
  functional_subsumed_empty hf σ o k x

/-- A legal output applies no exclusion exactly when `Excluded_o` is empty. -/
theorem «app:lifted-output-events/exposable» {sp : Spec I O}
    (σ : State sp) (o : O) :
    Exposable σ o ↔ ∀ k x, ¬ Excluded σ o k x :=
  exposable_iff_no_exclusion σ o

/-- **Prop. `prop:exposability`** (Legal-output test). -/
theorem «prop:exposability» {sp : Spec I O} (σ : State sp) (o : O) :
    Exposable σ o ↔ ∀ j, σ.cur ≼ j → ∀ x, σ.R j x →
      ∃ u, σ.R j u ∧ o ≼ u ∧ x ≼ u :=
  lifted_exposure_test σ o

/-- **Eq. `eq:safe-exposure`**, the per-row common-refinement test. -/
abbrev «eq:safe-exposure» {sp : Spec I O}
    (σ : State sp) (o : O) (j : I) (x : O) : Prop :=
  ∃ u, σ.R j u ∧ o ≼ u ∧ x ≼ u

end LiftedOutputEvents

/-- **Def. `def:canonical-exclusion-basis`**. -/
abbrev «def:canonical-exclusion-basis» (sp : Spec I O) : ExclusionBasis sp :=
  canonExclusionBasis sp

/-- **Eq. `eq:canonical-exclusion-basis-relational`**. -/
theorem «eq:canonical-exclusion-basis-relational» {sp : Spec I O} (c : Exclusion sp) :
    canonExclusionBasis sp c ↔ ∃ o : O, c = canonicalExclusion o ∧
      ∃ σ τ : State sp, (canonicalExclusion o).app σ = some τ :=
  Iff.rfl

/-- **Def. `def:canonical-event`**.  `κ_o` is empty or `[x_o]`. -/
noncomputable abbrev «def:canonical-event» {sp : Spec I O}
    (σ : State sp) (o : O) : SEvent sp :=
  SEvent.output (kappa σ o) o

/-- The canonical exclusion is defined precisely when the output is in the
current fiber and `Excluded_o` is nonempty. -/
theorem «app:bases/canonical-exclusion-is-exclusion» {sp : Spec I O}
    (o : O) (σ τ : State sp) :
    (canonicalExclusion o : Exclusion sp).app σ = some τ ↔
      ∃ h : σ.R σ.cur o, (∃ k x, Excluded σ o k x) ∧ excludeState σ o h = τ :=
  excludeApp_eq

/-- **Lemma `lem:canonical-exclusion-normal-form`**: containment, canonical
support, and the exclusion-free case. -/
theorem «lem:canonical-exclusion-normal-form» {sp : Spec I O} :
    (∀ {B : ExclusionBasis sp} {σ τ : State sp} {γ : List (Exclusion sp)} {o : O},
      SysStep B σ (.output γ o) τ →
      τ.cur = σ.cur ∧ σ.R σ.cur o ∧
        (∀ k u, τ.R k u → σ.R k u ∧ o ≼ u) ∧
        ∃ σc, ApplySeq γ σ σc ∧ ∀ k x, Excluded σ o k x → ¬ σc.R k x) ∧
    (∀ (σ : State sp) (o : O) (ho : σ.R σ.cur o),
      SysStep (canonExclusionBasis sp) σ (.output (kappa σ o) o) (outState σ o ho) ∧
      ∀ {B : ExclusionBasis sp} {τ : State sp} {γ : List (Exclusion sp)},
        SysStep B σ (.output γ o) τ → ∀ k u, τ.R k u → outputTable σ o k u) ∧
    (∀ {B : ExclusionBasis sp} {σ τ : State sp} {o : O},
      SysStep B σ (.output [] o) τ ↔
        σ.R σ.cur o ∧ Exposable σ o ∧ τ.cur = σ.cur ∧ τ.R = outputTable σ o) :=
  ⟨fun h => containment h,
   fun σ o ho => ⟨canonical_support σ o ho, fun h => canonical_maximal h⟩,
   eps_step_iff⟩

/-! ## Canonical system -/

/-- **Def. canonical system** (`def:canonical-system`).  "A system is canonical
when its basis is `ℬ_P` and each output event it performs is the canonical
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
`ℬ_P`. -/
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
excludes those inputs."

Lean: (a) `Out_{c::cs}(o)` under `B` is the event `Out_{[composite]}(o)` under
any basis `B'` containing the composite, and back; (b) in a functional
specification the composite excludes every input where it removes a row. -/
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
    fun hf c cs _ _ h k hk => Dist.composite_functional_empties hf c cs h k hk⟩

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
the runs under the canonical basis `ℬ_P` of Definition
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
functional-calm–complete-calm", and they are runs under `ℬ_P`. -/
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
