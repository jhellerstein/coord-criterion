import CoordCriterion.CALM.Lemmas
import CoordCriterion.Distributed.Systems
import CoordCriterion.Distributed.SystemConfluence
import CoordCriterion.CAP.ResponseForm
import CoordCriterion.CAP.AvailabilityAtEnd
import CoordCriterion.CAP.Coordination
import CoordCriterion.Appendix.Deployment
import CoordCriterion.CAP.LocalCommitment

/-!
# Paper Appendix A: notation and terms (`appendices/notation.tex`)

One declaration per row of the appendix's tables, in table order, each
resolving to the Lean definition of the term, for the tables of Sections
`sec:functional-calm`, `sec:complete-calm`, and `sec:distributed-execution`.
A few rows share a declaration where the term has no separate Lean meaning
(determination, participant run, final cut, local history).  The Composition
and Related-work tables point to definitions whose Lean entries are in
`Paper/S5_Composition.lean`, `Paper/S6_Instances.lean`, and
`Paper/AppD_Composition.lean`, under the same labels.  Names are
`«app:notation/<term>»`; the docstring gives the table's gloss and its
pointer (Def./Sec./Eq.) into the paper.

Some terms have no named Lean definition because the library states them
inline (e.g. the fiber `P(i)` is just `sp.P i`).  For those, the abbreviation
below *is* the reading the library's statements use, and its docstring says
so.

Conventions: `≼` is both orders; a table is `Table I O := I → O → Prop`;
a set of outputs is a predicate `O → Prop`; finite families are `List`s;
participants are `Fin n`.  §4 has two encodings of systems: `CC.Dist`
(`Distributed/`) for histories and distributed consistency, `CC`
(`Distributed/Commitments.lean`) for commitments and system output events,
and the self-contained `CC.CAP` model (`CAP/Model.lean`) for Complete CAP;
`CC.Dist.sysStep_iff_CAP` shows the two commitment/output-event encodings
agree.
-/

namespace CC.Paper

open CC CC.CALM

section
variable {I O : Type} [PO I] [PO O]

/-! ## Functional CALM (Section `sec:functional-calm`) -/

/-- *functional I/O specification* — `Spec = (I,≼,O,≼,P)` with `P` total on
`I` and one output per input; the induced function `f` (Def.
`def:functional-specification`).  Lean: `Spec I O`
with `Spec.Functional`. -/
abbrev «app:notation/functional-specification» (I O : Type) [PO I] [PO O] :=
  { sp : Spec I O // sp.Functional }

/-- *possibility relation `P`* — the spec's table of permitted rows `(i,o)`
(Def. `def:functional-specification`).  Lean: `sp.P`. -/
abbrev «app:notation/possibility-relation» (sp : Spec I O) : Table I O := sp.P

/-- *`i ≼ j`; `j` extends `i`* — `j` contains at least the input information in
`i`; `j` is an input extension of `i` (Sec. `sec:functional-specifications`).  Lean: `PO.le` on `I`, written `≼`. -/
abbrev «app:notation/expands» (i j : I) : Prop := i ≼ j

/-- *`o ≼ u`; `u` extends `o`* — `u` subsumes every externally visible claim in
`o`; `u` is an output extension of `o` (Sec. `sec:functional-specifications`).  Lean: `PO.le` on `O`, written `≼`. -/
abbrev «app:notation/refines» (o u : O) : Prop := o ≼ u

/-- *common input extension* — an input that extends each given input
(Sec. `sec:functional-specifications`).  No library name: statements write
`∀ i ∈ is, i ≼ j` (or `∀ σ ∈ fam, σ.cur ≼ j`). -/
abbrev «app:notation/common-expansion» (is : List I) (j : I) : Prop := ∀ i ∈ is, i ≼ j

/-- *common output extension* — an output that extends each given output
(Sec. `sec:functional-specifications`).  No library name: statements write
`∀ o ∈ os, o ≼ u`; "a common output extension in `F`" is `CompatibleIn F os`. -/
abbrev «app:notation/common-refinement» (os : List O) (u : O) : Prop := ∀ o ∈ os, o ≼ u

/-- *`(k,u)` extended by `(k,w)`* — `w` extends `u`, for two rows at the same
input (Sec. `sec:functional-specifications`).  No library name: statements
write `u ≼ w` for rows `R k u`, `R k w`. -/
abbrev «app:notation/extended-by» (u w : O) : Prop := u ≼ w

/-- *monotone (functional)* — `i ≼ j ⇒ f(i) ≼ f(j)`
(Def. `def:functional-monotonicity`).  Lean: `Spec.MonotoneF`, stated on
rows. -/
abbrev «app:notation/monotone-functional» (sp : Spec I O) : Prop := sp.MonotoneF

/-- *selection `R[…]`* — the rows of `R` that satisfy a predicate on `in` and
`out`; commas separate conjuncts (Sec. `sec:functional-specifications`).  Lean: a selection is a conjunction in a
table predicate; the two used by events are `inputTable σ j = R[in ⪰ j]` and
`outputTable σ o = R[out ⪰ o]`.  This names `R[in ⪰ j]`. -/
abbrev «app:notation/selection-in» {sp : Spec I O} (σ : State sp) (j : I) : Table I O :=
  inputTable σ j

/-- *selection* `R[out ⪰ o]` (see `«app:notation/selection-in»`). -/
abbrev «app:notation/selection-out» {sp : Spec I O} (σ : State sp) (o : O) : Table I O :=
  outputTable σ o

/-- *projection `π_in(R)`* — the set of inputs that appear in `R` (Sec. `sec:functional-specifications`).
No library name: statements write `∃ u, R k u`. -/
abbrev «app:notation/in» (R : Table I O) (k : I) : Prop := ∃ u, R k u

/-- *projection `π_out(R)`* — the set of outputs that appear in `R` (Sec. `sec:functional-specifications`).
No library name: statements write `∃ k, R k o`. -/
abbrev «app:notation/out» (R : Table I O) (o : O) : Prop := ∃ k, R k o

/-- *row at `k`* — a row `(k,u)` (Sec. `sec:functional-specifications`):
`R k u`.  *fiber `R(k)`* — `π_out(R[in = k])`, the outputs paired with `k`
(Def. `def:fiber`): Lean `R k`, a predicate on outputs (for the
specification, `sp.P k`). -/
abbrev «app:notation/fiber» (R : Table I O) (k : I) : O → Prop := R k

/-- *upper fiber at `k`* — `π_out(R[in ⪰ k])` (Def. `def:fiber`).
No library name: statements write `∃ k', k ≼ k' ∧ R k' o`; for a state
`(i,R)` the upper fiber at `i` is `∃ k, σ.R k o` (`R` holds only rows at
input extensions of `i`). -/
abbrev «app:notation/upper-fiber» (R : Table I O) (k : I) (o : O) : Prop :=
  ∃ k', k ≼ k' ∧ R k' o

/-- *specification state `(i,R)`* — current input `i` and remainder table
`R ⊆ P`, with a row at `i` and only rows at input extensions of `i` (Def.
`def:residual-state`).  Lean: `State sp`. -/
abbrev «app:notation/state» (sp : Spec I O) := State sp

/-- *legal input* — an input `k` at which `R` has a row (Def. `def:legal-input`).
No library name: `∃ u, σ.R k u` (the hypothesis of `Step.input`). -/
abbrev «app:notation/legal» {sp : Spec I O} (σ : State sp) (k : I) : Prop := ∃ u, σ.R k u

/-- *canonical state `σ_P(i)`* — `(i, P[in ⪰ i])` (Eq. `eq:canonical-state`).
Lean: `canon sp i`. -/
abbrev «app:notation/canonical-state» (sp : Spec I O) (i : I) : State sp := canon sp i

/-- *input event `input(j)`* — keeps `R[in ⪰ j]` and makes `j` the current
input (Eq. `eq:input-event`).
Lean: `Step σ (.input j) τ` (constructor `Step.input`). -/
abbrev «app:notation/input-event» (j : I) : Event I O := .input j

/-- *input loss* — the rows an input event removes (Sec. `sec:functional-events`):
rows of `R` whose input does not extend `j`.  No library name. -/
abbrev «app:notation/input-loss» {sp : Spec I O} (σ : State sp) (j : I) : Table I O :=
  fun k u => σ.R k u ∧ ¬ j ≼ k

/-- *output event `output(o)`* — keeps `R[out ⪰ o]` and emits `o`
(Def. `def:output-event`).  Lean: `Step σ (.output o) τ`. -/
abbrev «app:notation/output-event» (o : O) : Event I O := .output o

/-- *canonical commitment `x_o`* — the removal an output event makes when `o` is
not legal (Def. `def:canonical-commitment-functional`).  This entry states when
it applies: `o` is not legal.  In a functional specification that is
"`R' ≠ R`", equivalently "`Excluded_o ≠ ∅`"
(`CALM.functional_exclude_iff_excluded`).  The commitment itself is
`«app:notation/canonical-commitment»`; the general notion of commitment is
Def. `def:commitment` (`«app:notation/commitment»`). -/
abbrev «app:notation/output-event-excludes» {sp : Spec I O} (σ : State sp) (o : O) : Prop :=
  ¬ Exposable σ o

/-- *legal output* — an output `o` at `(i,R)` that every output in the upper
fiber extends (Def. `def:exposable`); in general, `Excluded_o` is empty
(Sec. `sec:lifted-output-events`).  Lean: `Exposable σ o`. -/
abbrev «app:notation/exposable» {sp : Spec I O} (σ : State sp) (o : O) : Prop := Exposable σ o

/-- *determined state* — a state whose upper fiber has one element;
*determination* — reaching a determined state (Sec. `sec:functional-events`).  Lean:
`CALM.Determined σ`. -/
abbrev «app:notation/determined» {sp : Spec I O} (σ : State sp) : Prop := Determined σ

/-- *specification event* (*event*) — an input or output event; from Section
`sec:systems` on, also a commitment event (Def. `def:specification-event`).
Lean: `Event I O` (input and output events); with commitment events,
`SEvent sp`. -/
abbrev «app:notation/specification-event» (I O : Type) := Event I O

/-- *canonical run* (*run*) — a finite sequence of specification events from a
canonical state (Def. `def:run`).
Lean: `Exec (canon sp i) es τ`; `IsRun τ` for "`τ` ends a run". -/
abbrev «app:notation/run» {sp : Spec I O} (τ : State sp) : Prop := IsRun τ

/-- *commitment-free run* — a run none of whose output events applies a
commitment (Sec. `sec:executions`).  Lean: `ExecCF σ es τ`. -/
abbrev «app:notation/commitment-free» {sp : Spec I O} (σ : State sp) (es : List (Event I O))
    (τ : State sp) : Prop :=
  ExecCF σ es τ

/-- *reachable without commitment* — reached by some commitment-free run
(Sec. `sec:executions`).  Lean: `ReachableCF τ`. -/
abbrev «app:notation/reachable-cf» {sp : Spec I O} (τ : State sp) : Prop := ReachableCF τ

/-- *consistent (runs)* — every finite family of runs is confluent at every
common input extension of their current inputs (Def. `def:consistency`).  Lean:
`Spec.Consistent`. -/
abbrev «app:notation/consistent» (sp : Spec I O) : Prop := sp.Consistent

/-- *confluent at `j`* — each run of a finite family can be continued to one
common state with current input `j` (Def. `def:confluence`).  Lean: `ConfluentAt fam j`,
for the list `fam` of run end states. -/
abbrev «app:notation/confluent-at» {sp : Spec I O} (fam : List (State sp)) (j : I) : Prop :=
  ConfluentAt fam j

/-! ## Complete CALM (Section `sec:complete-calm`) -/

/-- *I/O specification* — `Spec = (I,≼,O,≼,P)` with `P ⊆ I × O` total on `I`
(Def. `def:relational-specification`).  Lean: `Spec I O`. -/
abbrev «app:notation/relational-specification» (I O : Type) [PO I] [PO O] := Spec I O

/-- *nondeterministic* — some fiber has more than one output
(Def. `def:nondeterministic`).  No library name; equivalently
`¬ sp.Functional` (`«def:relational-specification/nondeterministic»`). -/
abbrev «app:notation/nondeterministic» (sp : Spec I O) : Prop :=
  ∃ i o o', sp.P i o ∧ sp.P i o' ∧ o ≠ o'

/-- *Relational Monotonicity* — every output keeps an output extension as input
grows (Def. `def:relational-monotonicity`).  Lean: `Spec.RelMono`. -/
abbrev «app:notation/relational-monotonicity» (sp : Spec I O) : Prop := sp.RelMono

/-- *compatible in `F`* — outputs that some `u ∈ F` extends all at once
(Sec. `sec:lifted-monotonicity`).  Lean: `CompatibleIn F X`. -/
abbrev «app:notation/compatible-in» (F : O → Prop) (X : List O) : Prop := CompatibleIn F X

/-- *directed fiber* — every nonempty finite subset is compatible in the fiber
(Def. `def:fiber-directedness`).  Lean: `JointLift F F`. -/
abbrev «app:notation/directed» (F : O → Prop) : Prop := JointLift F F

/-- *directed fibers* — every fiber of the spec is directed
(Def. `def:fiber-directedness`).
Lean: `Spec.DirectedOutputs`. -/
abbrev «app:notation/directed-outputs» (sp : Spec I O) : Prop := sp.DirectedOutputs

/-- *joint refinement lift `A ⊑ B`* — every nonempty finite `X ⊆ A` is compatible in `B`
(Eq. `eq:joint-output-order`).  Lean: `JointLift A B`. -/
abbrev «app:notation/joint-lift» (A B : O → Prop) : Prop := JointLift A B

/-- *Lifted Monotonicity* (*monotone*) — `i ≼ j ⇒ P(i) ⊑ P(j)`
(Def. `def:lifted-monotonicity`).  Lean: `Spec.LiftedMono`. -/
abbrev «app:notation/lifted-monotonicity» (sp : Spec I O) : Prop := sp.LiftedMono

/-- *common-extension condition* — rows with a common input extension `j` have a
common output extension in `P(j)` (Def. `def:common-expansion-condition`).  Lean:
`Spec.CommonExpansion`. -/
abbrev «app:notation/common-expansion-condition» (sp : Spec I O) : Prop := sp.CommonExpansion

/-- *ruled out by `o`* — a row whose output does not extend `o`
(App. `app:lifted-output-events`).  No library name: `σ.R k x ∧ ¬ o ≼ x`
(equivalently in `R ∖ outputTable σ o`, `CC.ruledOut_iff`). -/
abbrev «app:notation/ruled-out» {sp : Spec I O} (σ : State sp) (o : O) : Table I O :=
  fun k x => σ.R k x ∧ ¬ o ≼ x

/-- *`Subsumed_o`* — removed rows `(k,x)` for which some output at `k` extends
both `x` and `o` (Eq. `eq:output-subsumptions`).  Lean: `Subsumed σ o`. -/
abbrev «app:notation/Subsumed» {sp : Spec I O} (σ : State sp) (o : O) : Table I O := Subsumed σ o

/-- *`Excluded_o`* — all other removed rows (Eq. `eq:commitment-removals`).
Lean: `Excluded σ o`. -/
abbrev «app:notation/Excluded» {sp : Spec I O} (σ : State sp) (o : O) : Table I O :=
  Excluded σ o

/-- *canonical commitment `x_o`* (general) — removes the rows of `Excluded_o`
(Def. `def:canonical-commitment`).  Lean: `canonicalCommitment o`. -/
noncomputable abbrev «app:notation/canonical-commitment» {sp : Spec I O} : O → Commitment sp :=
  canonicalCommitment

/-- *output subsumption* — removing the rows of `Subsumed_o`, which is not a
commitment
(Def. `def:lifted-output-event`).  Lean: the rows `Subsumed σ o`, removed by
`outputTable σ o` (no separate state). -/
abbrev «app:notation/output-subsumption» {sp : Spec I O} (σ : State sp) (o : O) : Table I O :=
  Subsumed σ o

/-- *legal output* (general) — an output `o` with `Excluded_o` empty
(Sec. `sec:lifted-output-events`).  Lean: `∀ k x, ¬ Excluded σ o k x`, which
is `Exposable σ o` (`«app:notation/exposable»`). -/
abbrev «app:notation/legal-output-general» {sp : Spec I O} (σ : State sp) (o : O) : Prop :=
  ∀ k x, ¬ Excluded σ o k x

/-! ## Distributed execution (Section `sec:distributed-execution`) -/

/-- *participant* — holds a specification state and exchanges messages
(Sec. `sec:histories`).
Lean: participants are `Fin n`; each has initial input `H.init p` and its
state is that of its participant run. -/
abbrev «app:notation/participant» (n : Nat) := Fin n

/-- *message `m = (j,d)`* — a cumulative input `j`, or `∅`, and other data `d`
(Sec. `sec:histories`).  Lean: `Option I × D` (`none` is `∅`), the
payload of `Dist.LEv.send`/`recv`. -/
abbrev «app:notation/message» (I D : Type) := Option I × D

/-- *distributed history* — history events with a total local order at each
participant and a matching send for each receive (Def.
`def:distributed-history`).  Lean: `Dist.History I O D n`
(local event lists) with well-formedness `Dist.History.WF`. -/
abbrev «app:notation/distributed-history» (I O D : Type) (n : Nat) := Dist.History I O D n

/-- *history event* — a specification, send, or receive event at one
participant (Def. `def:distributed-history`).  Lean: a position
`(p, k)` with `H.InH (p, k)`; local events are `Dist.LEv I O D`. -/
abbrev «app:notation/history-event» {D : Type} {n : Nat} (H : Dist.History I O D n)
    (a : Dist.Pos n) : Prop :=
  H.InH a

/-- *happens-before* — transitive closure of the local orders and of send
before receive (Def. `def:happens-before`).  Lean: `Dist.History.HB`. -/
abbrev «app:notation/happens-before» {D : Type} {n : Nat} (H : Dist.History I O D n) :
    Dist.Pos n → Dist.Pos n → Prop :=
  H.HB

/-- *consistent cut* — a set of history events closed under happens-before
(Def. `def:consistent-cut`).  Lean: `Dist.History.IsCut`. -/
abbrev «app:notation/consistent-cut» {D : Type} {n : Nat} (H : Dist.History I O D n)
    (C : Dist.Pos n → Prop) : Prop :=
  H.IsCut C

/-- *participant run* — `p`'s specification events at a cut `C`, in local order,
ending at `σ_p(C)` (Def. `def:participant-run`); *endpoint* —
`(σ_p(C))_{p ∈ 𝒩}` (Def. `def:endpoint`).  Lean:
`Dist.History.Endpoint sp H C σs` says `σs p` is the final state of `p`'s
participant run `ioOf ((H.ev p).take c)` at `C`. -/
abbrev «app:notation/endpoint» {D : Type} {n : Nat} (sp : Spec I O) (H : Dist.History I O D n)
    (C : Dist.Pos n → Prop) (σs : Fin n → State sp) : Prop :=
  H.Endpoint sp C σs

/-- *continuation* — a history that extends the events of a cut with later
events (Sec. `sec:distributed-consistency`); its *final cut* is all of it, as a
consistent cut.  Lean: `Dist.History.Extends H H' C`. -/
abbrev «app:notation/continuation» {D : Type} {n : Nat} (H H' : Dist.History I O D n)
    (C : Dist.Pos n → Prop) : Prop :=
  H.Extends H' C

/-- *cut confluent at `j`* — some continuation brings every participant to
one state `(j,R)` (Sec. `sec:distributed-consistency`).  Lean:
`Dist.History.CutConfluentAt`. -/
abbrev «app:notation/cut-confluent-at» {D : Type} {n : Nat} (sp : Spec I O)
    (H : Dist.History I O D n) (C : Dist.Pos n → Prop) (j : I) : Prop :=
  H.CutConfluentAt sp C j

/-- *consistent (distributed histories)* — every consistent cut of every history is
confluent at every common input extension (Def. `def:distributed-consistency`).
Lean: `Dist.DistConsistent sp D`, for message data `D`. -/
abbrev «app:notation/distributed-consistency» (sp : Spec I O) (D : Type) : Prop :=
  Dist.DistConsistent sp D

/-- *commitment* — a partial function on states that removes a nonempty set of
rows, none extended by a remaining row at the same input (Def.
`def:commitment`).  Lean:
`CC.Commitment sp` (and the equivalent `CC.CAP.Commitment sp`). -/
abbrev «app:notation/commitment» (sp : Spec I O) := Commitment sp

/-- *local history* — `p`'s history events in order (Def. `def:local-history`);
*strategy `θ_p`* — maps a local history to the output, commitment, and send
events `p` may perform next (Def. `def:strategy`).  Lean (`CC.CAP`): a local history is a list
`pre : List (CAP.LEv sp D n)`; the strategy is the field `System.rule`,
applied to `p`'s number, its own initial input and its erased local history;
`strat n init p pre e` (`p` may perform `e` after `pre`) is the induced
relation, i.e. nondeterministic. -/
abbrev «app:notation/strategy» {sp : Spec I O} {D : Type} (Sys : CAP.System sp D) :
    (n : Nat) → (Fin n → I) → Fin n → List (CAP.LEv sp D n) → CAP.LEv sp D n → Prop :=
  Sys.strat

/-- *system* — a commitment basis and a strategy per participant
(Def. `def:system`).  Lean: `CAP.System sp D` (fields `basis`, `rule`). -/
abbrev «app:notation/system» (sp : Spec I O) (D : Type) := CAP.System sp D

/-- *commitment basis* (Def. `def:commitment-basis`: "A commitment basis is a
set `ℬ` of commitments").  Lean: `CommitmentBasis sp := Commitment sp → Prop`
(in `CC.CAP`: the field `System.basis`). -/
abbrev «app:notation/basis» (sp : Spec I O) := CommitmentBasis sp

/-- *history of a system* — a history whose output, commitment, and send events
its strategies choose (Def. `def:produced-history`).  Lean:
`CAP.Produced`. -/
abbrev «app:notation/produced» {sp : Spec I O} {D : Type} (Sys : CAP.System sp D) (n : Nat)
    (init : Fin n → I) (H : CAP.History sp D n) : Prop :=
  CAP.Produced Sys n init H

/-- *commitment event `apply(γ)`* — applies a nonempty sequence `γ` of
commitments and emits nothing (Def. `def:commitment-event`); when run by a
system, `γ ⊆ B` (Def. `def:system`).  Lean: the event `SEvent.commitment γ`,
with transition `SysStep B σ (.commitment γ) τ`. -/
abbrev «app:notation/commitment-event» {sp : Spec I O} (B : CommitmentBasis sp) (σ : State sp)
    (γ : List (Commitment sp)) (τ : State sp) : Prop :=
  SysStep B σ (.commitment γ) τ

/-- *run under `ℬ`* — input, output, and commitment events from a canonical
state, applying only commitments in `ℬ` (Def. `def:run-under-basis`); an
output event whose output is not already legal applies its `x_o ∈ ℬ`.  Lean:
`RunUnder B es τ`. -/
abbrev «app:notation/run-under-basis» {sp : Spec I O} (B : CommitmentBasis sp) (es : List (SEvent sp))
    (τ : State sp) : Prop :=
  RunUnder B es τ

/-- *canonical run* — a run (Def. `def:run`), seen as a run under the canonical basis.
Lean: `CanonExec σ es τ` (runs under the canonical basis with no
commitment events); `CC.canonExec_exec` / `CC.exec_canonExec` identify these with
`Exec`. -/
abbrev «app:notation/canonical-run» {sp : Spec I O} (σ : State sp) (es : List (SEvent sp))
    (τ : State sp) : Prop :=
  CanonExec σ es τ

/-- *observably equivalent* — same inputs and outputs, and the canonical run
keeps every row the run keeps (Lem. `lem:canonical-equivalent`).  Lean: two event lists are observably
equivalent when their images under `filterMap SEvent.erase` (which drops
commitment events) agree; the lemma is `CC.canonical_equivalent`. -/
abbrev «app:notation/observably-equivalent» {sp : Spec I O} (es es' : List (SEvent sp)) : Prop :=
  es.filterMap SEvent.erase = es'.filterMap SEvent.erase

/-- *`Δ(ρ)`* — rows of the final table of `ρ`'s canonical run that a
commitment event of `ρ` removed (Sec. `sec:commitment-conflict`).  Lean: `Dist.Removed B σ es k u`, restricted
to the canonical final table `ρh`; `Dist.table_decomp` is "`ρ` keeps the rest". -/
def «app:notation/delta» {sp : Spec I O} (B : CommitmentBasis sp) (σ : State sp)
    (es : List (SEvent sp)) (ρh : State sp) : I → O → Prop :=
  fun k u => ρh.R k u ∧ Dist.Removed B σ es k u

/-- Supporting notation for a canonical run that contradicts a commitment in
Proposition `prop:canonical-commitment-witness`: it accepts an input whose fiber
the commitment emptied, or emits an output whose row it removed. -/
abbrev appCommitmentContradictedBy {sp : Spec I O} (emits : I → O → Prop) (accepts : I → Prop)
    (σ σc : State sp) : Prop :=
  CAP.Contradicts emits accepts σ σc

/-- *partitioned history* — participants divided into two or more sides, with
no message across sides (Def. `def:partitioned-history`).  Lean:
`CAP.Partitioned H comp` (at least two sides, no cross-side receive). -/
abbrev «app:notation/partitioned-history» {sp : Spec I O} {D : Type} {n : Nat}
    (H : CAP.History sp D n) (comp : Fin n → Nat) : Prop :=
  CAP.Partitioned H comp

/-- *side* — one of the two or more classes into which a partitioned history
divides the participants (Def. `def:partitioned-history`).  Lean: the label
class of `p` under the labelling `comp : Fin n → Nat`. -/
abbrev «app:notation/side» {n : Nat} (comp : Fin n → Nat) (p : Fin n) : Fin n → Prop :=
  fun q => comp q = comp p

  /-- *explicit possibility relation `E`* — `E ⊆ P`, the rows whose outputs
  participants actually emit (Def. `def:explicit-relation`).  Lean: a table
  `E : Table I O` with `∀ i o, E i o → sp.P i o`. -/
abbrev «app:notation/explicit-relation» {sp : Spec I O} (E : Table I O) : Prop :=
  ∀ i o, E i o → sp.P i o

/-- *same-side continuation for `p`* — extends a partitioned history with
events on `p`'s side alone, with no new input and no message from another side
(Def. `def:local-continuation`).  Lean: a continuation `ext` of `H` with
`Produced`, `Partitioned … comp`, `ext q = []` off `p`'s side, and no input
event. -/
abbrev «app:notation/same-side-continuation» {sp : Spec I O} {D : Type} {n : Nat}
    (Sys : CAP.System sp D) (init : Fin n → I) (H : CAP.History sp D n)
    (comp : Fin n → Nat) (p : Fin n) (ext : Fin n → List (CAP.LEv sp D n)) : Prop :=
  CAP.WF init (fun q => H q ++ ext q) ∧ CAP.Produced Sys n init (fun q => H q ++ ext q) ∧
    CAP.Partitioned (fun q => H q ++ ext q) comp ∧
    (∀ q, comp q ≠ comp p → ext q = []) ∧ (∀ q j, CAP.LEv.inp j ∉ ext q)

/-- *Availability for `E`* — each participant can emit every output in
`R(i) ∩ E(i)` in a same-side continuation (Def. `def:partition-notions`).  Lean: `CAP.AvailabilityFor E`; Availability
is `E = P` (`CAP.AvailabilityAtEnd`). -/
abbrev «app:notation/availability» {sp : Spec I O} {D : Type} (E : Table I O)
    (Sys : CAP.System sp D) : Prop :=
  CAP.AvailabilityFor E Sys

/-- *canonical system for `E`* — participants follow canonical runs and emit
only outputs of `E` (Section `sec:complete-cap`).  Lean: `CAP.respSystem E`. -/
noncomputable abbrev «app:notation/canonical-system» (sp : Spec I O) (D : Type)
    (E : Table I O) : CAP.System sp D :=
  CAP.respSystem E

/-- *Lifted Monotonicity for `E`* — every finite set of rows of `E` with a
common input extension `j` has a common output extension in `P(j)` (Def. `def:lm-for-A`).
Lean: `CAP.ConsistentOn`. -/
abbrev «app:notation/lm-for-A» (sp : Spec I O) (E : Table I O) : Prop :=
  CAP.ConsistentOn sp E

/-- *escapes CAP for `E`* — the canonical system for `E` has Availability for
`E` and Partition Consistency (Def. `def:escapes-cap`).  Lean:
`CAP.AvailabilityFor E (CAP.respSystem E) ∧
CAP.PartitionConsistencyAtEnd (CAP.respSystem E)`. -/
abbrev «app:notation/escapes-cap» (sp : Spec I O) (D : Type) (E : Table I O) : Prop :=
  CAP.AvailabilityFor E (CAP.respSystem (sp := sp) (D := D) E) ∧
    CAP.PartitionConsistencyAtEnd (CAP.respSystem (sp := sp) (D := D) E)

/-- *emitted rows* — the pairs `(i,o)` such that a run emits `o` at current
input `i` (Def. `def:emitted-rows`, in Def. `def:deployment`).  Lean, for a
system: `CAP.SysEmits Sys`. -/
abbrev «app:notation/emitted-rows» {sp : Spec I O} {D : Type} (Sys : CAP.System sp D) :
    Table I O :=
  CAP.SysEmits Sys

/-- *deployment* — one explicit relation `E_p` per participant
(Def. `def:deployment`).  Lean: `CC.Deploy.Deployment sp n`. -/
abbrev «app:notation/deployment» (sp : Spec I O) (n : Nat) : Type := CC.Deploy.Deployment sp n

/-- *Partition Consistency* — the final cut of every partitioned history is
confluent at every common input extension (Def. `def:partition-consistency`).  Lean: `CAP.PartitionConsistencyAtEnd`
(equivalently `CAP.PartitionConsistency`, stated at cuts). -/
abbrev «app:notation/partition-consistency» {sp : Spec I O} {D : Type}
    (Sys : CAP.System sp D) : Prop :=
  CAP.PartitionConsistencyAtEnd Sys

/-- *response obligation* — per participant, the outputs that count as
answers, upward closed within fibers (Def. `def:response-obligation`).  Lean:
`CAP.Obligation sp` (uniform case); `CAP.ResponseAvailability` takes a
per-participant family `Q n p`. -/
abbrev «app:notation/response-obligation» (sp : Spec I O) := CAP.Obligation sp

/-- *response interface* — a total, self-continuing explicit relation
`T ⊆ Q` (Def. `def:response-interface`).  Lean: `CAP.ResponseInterface Q T`. -/
abbrev «app:notation/response-interface» {sp : Spec I O} (Q : CAP.Obligation sp)
    (T : Table I O) : Prop :=
  CAP.ResponseInterface Q T

end

end CC.Paper
