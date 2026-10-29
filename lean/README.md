# Lean formalization of the paper

This directory checks the paper's definitions, results, and proved claims in
Lean 4 (core library only, no Mathlib; toolchain in `lean-toolchain`).

## How to read it alongside the paper

Start in `CoordCriterion/Paper/`.  It has one file per section and appendix,
and each file follows its section in paper order, with headers matching the
paper's subsections:

* every numbered definition, theorem, lemma, proposition, corollary, figure,
  and equation is a declaration named by its LaTeX label, for example
  `CC.Paper.«thm:complete-calm»` or `CC.Paper.«def:commitment»`; search the
  `.tex` label and you find the Lean;
* claims that the text proves inline are named `«<enclosing label>/<slug>»`,
  for example `CC.Paper.«sec:hat-instance/rc-timestamps»`;
* each declaration states the result in full and quotes the paper in its
  docstring; when the Lean reading differs from the paper's wording (finite
  sets as lists, tables as predicates), the docstring says how;
* each proof is a one-line reference to the library under
  `CoordCriterion/`, so following it leads to the actual argument.

The index below lists every `Paper/` declaration.  The library files carry
module docstrings that name the paper section they support, what they
contain, and their modeling choices.

What is argued only in prose, not in Lean: the step from Gilbert and Lynch's
fair-execution definitions to the finite forms used in
`«prop:gl-async»` (Appendix F); the protocol steps of 2PL and MVTO (which
arrival makes a lock wait, issues a timestamp, or triggers the write rule;
Appendix G, where Lean checks the commitments those steps apply and the MVTO
run driven by arrivals); the
protocol steps of two-phase commit in §4.4 (prepare messages, logging,
blocking; Lean checks only that the vote-counting decision is monotone,
needs no coordination, and aborts exactly when the votes do not all say yes);
the remark closing §4.4's shared-nothing paragraph that all three cases
exchange messages and that a client cut off from an owner cannot get its
answer; the
operational results that §6.1 cites (the transducer theorems of Ameloot et
al., Zinn et al., and Baccaert and Ketsman, which input order a placement
model justifies, and their notion of coordination; for Baccaert and Ketsman
also their notion of computing a behavior, that a node without the list of
all nodes may be the whole network and must emit, that their construction
waits until a group confirms its members and that groups sharing a node are
nested, that the group's choice requires coordination but not distributed
coordination, and that the list and an order on nodes compute every behavior;
Lean checks only the mapping of their conditions into our frame); in
Appendix E (`app:rtc`), the reading of the real-time causal views as Mahajan et
al.'s checks, the correspondence of the hypotheses to theirs, and the remark
that a strengthening may read real time from the input; in §6.3, that HAT's session guarantees under sticky availability are deployments; in §6.5, that
distributing a compiled state machine is direct (each client's events go to
some participant and §4 applies with the induced specification), and in its
"Testing and proof" paragraph that simulators and model checkers run the
machine on bounded inputs and that the input/output pairs they collect form a
finite specification that can be checked for violations, that this is routine engineering practice and has
found serious bugs in production systems, that testing cannot show Lifted
Monotonicity holds, the example rules of a declared specification ("the set
of ballots received", "the largest timestamp seen"), and the relation of the
two obligations to the verification literature (invariants, forward
simulations, refinement mappings, mechanized proofs, realizability typically
proved by induction on the input); and the design discussion of §6–§7.  The `Paper/` docstrings point these out where
they occur.

## Building and checking

From this directory:

* `lake build` builds everything, including the `Paper/` layer;
* `lake env lean scripts/CheckAxioms.lean` reports any theorem in namespace
  `CC` that uses `sorry` or an axiom other than `propext`, `Quot.sound`,
  `Classical.choice`;
* `python3 scripts/gen_index.py` regenerates the index below and
  `scripts/CheckReadme.lean`, and `lake env lean scripts/CheckReadme.lean`
  checks that every indexed name exists.

## Library layout

The directories follow the paper.  Within a directory, the theorem file comes
first and supporting claims and examples follow.

| File (`CoordCriterion/…`) | Namespace | Paper | Contents |
|---|---|---|---|
| `Paper/*.lean` | `CC.Paper` | all | The paper's results by label, in paper order (see the index below) |
| `Foundations/Core.lean` | `CC` | §2–§3, App. A | Orders, specifications, states, events, monotonicity notions, consistency |
| `Foundations/Runs.lean` | `CC` | §2–§3 | Lemma run-residual, survivor test, determinism of events |
| `Foundations/IOAutomata.lean` | `CC.IOA` | §6 | Lynch–Tuttle I/O automata: signatures, input-enabled automata, executions, compatible composition, projection and its converse |
| `FunctionalCALM/Theorem.lean` | `CC` | §2 | Thm. Functional CALM, Cor. state-by-input, functional exposure boundary |
| `CompleteCALM/Theorem.lean` | `CC` | §3 | LM characterizations, common-expansion form, pairs suffice, lifted output event, Thm. Complete CALM, exposure boundary |
| `CompleteCALM/Cofinal.lean` | `CC` | §6.5 | Cofinality (used by Prop. declared-specification): a declared spec whose rows are rows of `T` and dominate every row of `T` (same inputs, or along an order embedding) is Lifted Monotone / consistent iff `T` is |
| `CALM/Lemmas.lean` | `CC.CALM` | §2–§3, App. B | Event facts, functional remarks, Lemma reconciliation, paper proof routes, pairs suffice |
| `CALM/Examples.lean` | `CC.CALM` | §2–§3, App. B | `k`-set agreement (pairs), rows at `j`, relational state-by-input, election, directed fiber |
| `CALM/TransientConflict.lean` | `CC.CALM.Transient` | §4.4 | A conflict confined to the current input: no meeting at `i`, confluent at `j`, not consistent |
| `Figures.lean` | `CC.Figures` | §2–§3, §7 | Figure tables: election frames, ambiguity frames; decisive ballot vs. closing the polls |
| `Distributed/Histories.lean` | `CC.Dist` | §4.1–4.2 | Histories, cuts, Prop. distributed consistency, Cor. convergence, exchanging outputs |
| `Distributed/Commitments.lean` | `CC` | §4.3–4.4, App. C | Commitments, canonical seal/choice, system output events `Out_γ(o)` and commit events `Commit(γ)` (a nonempty sequence of basis commitments applied without emitting; erased to nothing), normal form, seal-or-choose, coordination (an output event with `γ ≠ ε` or a commit event), canonical-equivalent (the canonical run skips commit events), conflicting outputs |
| `Distributed/Systems.lean` | `CC.Dist` | §4.1–4.4, App. C | Figure participant-runs, consistency without unique send ids, canonical systems, reconciliation under any basis, encodings of output and commit events agree |
| `CAP/Model.lean` | `CC.CAP` | §4.1–4.5 | System model for Complete CAP: commitments, histories (local events: inputs, output events `out γ o`, commit events `cmt γ`, sends, receives), cuts, systems, Availability, Partition Consistency |
| `CAP/CompleteCAP.lean` | `CC.CAP` | §4.5 | Thm. Complete CAP; deterministic strategies do not suffice |
| `CAP/TwoPhaseCommit.lean` | `CC.CAP` | §4.4 | Two-phase commit: vote counting over a fixed membership is monotone, consistent, and coordination-free |
| `CAP/ResponseForm.lean` | `CC.CAP` | App. F | Response Availability, Response Partition Consistency, Thm. Complete CAP (response form) |
| `CAP/Register.lean` | `CC.GL` | App. F | Linearizable register, realized histories, Cor. Gilbert–Lynch |
| `CAP/ResponseAvailability.lean` | `CC.CAP` | §4.5, App. F | Strong (2)⇒(1), RPC vs. confluence, input acceptance, Lemma locality, without replication, choosing vs. requiring every output, Lemma forced-answer, GL via forced answer |
| `CAP/AsyncGilbertLynch.lean` | `CC.AsyncGL` | App. F | Gilbert–Lynch Theorem 1 (asynchronous model) by reduction to the corollary |
| `CAP/ChosenAvailability.lean` | `CC.CAP`, `CC.AsyncGL` | App. F | End-of-history forms of Response Availability / RPC / Answering; RPC is the converse's common-refinement condition; a response interface as a chosen explicit relation; Lemma forced-answer and Cor. Gilbert–Lynch at the end of histories |
| `Instances/InvariantConfluence.lean` | `CC.IConf` | §6, App. B | Bailis et al. model; Prop. invariant confluence ⇔ LM |
| `Instances/BailisDefinition.lean` | `CC.IConf` | §6 | Bailis et al. Def. 5/6 ⇔ `IConfluent` |
| `Instances/Examples.lean` | `CC.Inst` | §5–§6, App. B, App. D | CRDTs, uniqueness example, composition examples |
| `Instances/HATRC.lean` | `CC.HATRC` | §6.3 | HAT's Read Committed algorithm (App. B pseudocode, partial replication, anti-entropy): a G1c witness with timestamps fixed at `BEGIN`; with Lamport timestamps chosen at commit every run is PL-2 |
| `Instances/HATUnion.lean` | `CC.HATUnion` | — (not cited) | Bailis's dissertation frame (histories merged by union): two read-committed histories whose union has G1c; with the Lamport condition unions never do |
| `Instances/HATSpec.lean` | `CC.HATSpec` | §6.3 | Def. hat-spec, Thm. hat-levels: event-history inputs with happens-before (optionally with the timestamp condition), read-answer outputs, HAT levels (RU, RC, SI, RR, SER; item-only); HAT's read rule as explicit relation; RU/RC available under the timestamp condition; any level proscribing Lost Update unavailable; without the condition the read rule leaves `S_RC` |
| `Instances/QueryRefinements.lean` | `CC.QRef` | §6.1 | Domain-distinct/disjoint monotonicity as Functional CALM under restricted expansion orders; one-fact versions are weaker; behaviors over located facts, node monotonicity vs. Lifted Monotonicity |
| `Instances/StateMachine.lean` | `CC.SM` | §6 | State machines and the prefix-ordered table of event sequences (used by Prop. induced-specification (2)); arrival-order independence; the election as an induced specification |
| `Instances/IOMachine.lean` | `CC.IOM` | §6 | A general machine automaton (receives, outputs and internal steps that may change state; state machines as the special case `ofSM`), clients, and a bag or FIFO channel as composed I/O automata; happens-before; the specification of (received events with happens-before, observation) pairs; fibers are reached by machine executions on arrival orders, every one over a bag without observations; FIFO single client is the table of payload sequences under prefix (the prefix encoding for state machines); confluence across executions ⇔ Lifted Monotonicity, also for emitted outputs when outputs report observations; later sends after an output (Def./Prop. induced-specification) |
| `Instances/IOMachineCofinal.lean` | `CC.IOM` | §6.5 | Prop. declared-specification (machine bridge): a declared spec over the occurring inputs (or along an order embedding of them) whose rows are produced by executions and dominate every execution's final observation is Lifted Monotone iff the induced spec is, iff observations are confluent; re-derives single-client FIFO stationary consistency ⇔ `TransMono` and Lifted Monotonicity of the transient dip (a machine whose internal step lowers the observation); finite witnesses of a violation of Lifted Monotonicity, certified by the machine's own runs or a finite list containing the fiber; the `fork` machine, showing neither obligation alone suffices |
| `Appendix/Composition.lean` | `CC.Comp` | §5, App. D | Composition lemmas, independently parameterized composition, curried plan |
| `Appendix/Guarded.lean` | `CC.Guard` | §5, App. D | `Joint.Img`, `Joint.CEOn`, `Joint.restrictTo`; guarded runs, store under the empty basis, covering, invisible coordination, Proper Coordination (`𝒮₂` restricted to the outputs of `𝒮₁` needs no commitment; pipeline runs as composite runs, confluence, where the upstream must commit), systems with strategies, commitment-erased replacement, pipelines, early/late locks, counterexamples, per-key store, replicated store |
| `Appendix/JointMono.lean` | `CC.Joint` | §5.1, App. D | Jointly monotone composites: filtering (capped counter), re-ordering the middle (boolean toggle, constant store; also the double complement, no longer cited in the paper), preorder/injective characterization and the no-partial-order counterexample |
| `Appendix/Deployment.lean` | `CC.Deploy` | App. E | Deployments, separability, monotone across partitions, partition compatibility, Deployment Availability |
| `Appendix/DeploymentExamples.lean` | `CC.Deploy` | App. E | Chains of emitted outputs, leader example, sole-authority sufficient condition, single-authority deployments |
| `Appendix/DeploymentSystems.lean` | `CC.Deploy` | App. E | Remark: the proposition applies to system runs |
| `Appendix/DeploymentFor.lean` | `CC.Deploy` | App. E | Deployment Availability at the end of histories; uniform deployment is Availability for `E`; Lifted Monotonicity for `E` implies monotone across partitions; single authority: choices not distributed coordination |
| `Appendix/TransactionBases/NoReads.lean` | `CC.Txn` | §4.3, App. C | Complete `(L,X)` outcomes, finite sets, filter commitments on antichain fibers (used by Fig. cc-commitments in §4.3 and App. C) |
| `Appendix/TransactionBases/Spec.lean` | `CC.Txn.Partial` | App. G | The specification: inputs are transactions with operation sequences (prefix order, frozen after the commit request); outputs `(L,X,ρ)` with reads by position; complete outputs, read rule, abort-free variant |
| `Appendix/TransactionBases/Partial.lean` | `CC.Txn.Partial` | App. G | Closure commitments; 2PL/MVTO bases; bases differ at three transactions that requested commit; deadlock (and under abort-free: the two commit requests are never both accepted); MVTO: what a reported read commits to, when the writer's abort is entailed |
| `Appendix/TransactionBases/MVTO.lean` | `CC.Txn.Partial` | App. G | MVTO's eager abort as a run driven by operation arrivals: stamps, the read report, the write arrival, `Out_[abort(A)]` as a choice, and the abort exposable after `TxCommit(B)`; the version condition is needed |
| `Appendix/TransactionBases/CommitEvent.lean` | `CC.Txn.Partial.CommitEx` | §4.3 | 2PL commitment event `Commit([order(A,B)])` when `B` waits for `A`'s lock, at three transactions that requested commit, then `[A,C,B]`; lockstep with the canonical run, same final state |
| `Appendix/Frontiers.lean` | `CC.Front` | §3 (Hoare remark); otherwise not in paper | Hoare preorder vs. the joint lift; remembered-output hull, Table lookup-lift, Hoare quotient, persistent forwarding |
| `Appendix/ProductFrontier.lean` | `CC.Deploy` | App. E (real-time causal) | Thm. independent products (`thm:product-frontier`), configuration example |
| `Appendix/Graphs.lean` | `CC.Graph` | not in paper | Products, tee vs. running twice, merge, partition; stage expressions with per-node offered-domain test; Proper Coordination for products; parameterized composition as a product |
| `Appendix/Registers.lean` | `CC.Deploy` | App. E (registers) | Causal and linearizable registers, two-write history, causal-register frontier |
| `Appendix/RealTimeCausal.lean` | `CC.Deploy` | App. E (real-time causal) | Histories with real-time precedence, real-time causal views, their product interface, forcing, maximality for real-time blind strengthenings |
| `Appendix/Applications.lean` | `CC.Apps` | App. H | Committed authority, `k`-set agreement, tight renaming, snapshots |

`ProductFrontier`, `Registers`, and `RealTimeCausal` are in `CC.Deploy` because they are stated
in terms of the deployment notions of `Appendix/Deployment.lean`.

## Paper index

<!-- BEGIN PAPER INDEX -->

617 entries.

### §2 Functional CALM

File `Paper/S2_FunctionalCALM.lean`; paper source `sections/functional-calm.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«sec:election-story/input-order»` | theorem | "The *input order* records accumulated ballots: |
| `«sec:election-story/output-order»` | theorem | "The *output order* says which announcements are safe to build on: |
| `«sec:election-story/monotone»` | theorem | "The functional table is *monotone* … Here, for example, the input sequence `x·· ⪯ xy· ⪯ xyx` monotonically produces the output sequence `⊥ ⪯ ⊥ ⪯ x`." The el… |
| `«fig:election-frames/printed-rows»` | theorem | Fig. |
| `«fig:election-frames/a»` | theorem | Fig. |
| `«fig:election-frames/b»` | theorem | Fig. |
| `«fig:election-frames/b-rows»` | theorem | Fig. |
| `«fig:election-frames/c»` | theorem | Fig. |
| `«fig:election-frames/d»` | theorem | Fig. |
| `«fig:election-frames/d-gray»` | theorem | Fig. |
| `«fig:election-frames/bot-alone»` | theorem | Fig. |
| `«fig:nonmonotone-frame»` | theorem | Fig. |
| `«fig:nonmonotone-frame/matches-d»` | theorem | Fig. |
| `«sec:election-story/exposable-panels»` | theorem | §2.1 "Output and consistency": |
| `«sec:election-story/equality-order-seal»` | theorem | §2.1: |
| `«sec:election-story/obstruction»` | theorem | §2.1: |
| `«sec:election-story/not-reconciled»` | theorem | §2.1: |
| `«sec:election-story/consistency»` | theorem | §2.1: |
| `«def:functional-specification»` | abbrev | **Def. |
| `«def:functional-specification/induced-function»` | theorem | "The unique output paired with `i` induces the function `f : |
| `«sec:functional-specifications/subsequence-example»` | theorem | "Neither need be unique or least: |
| `«def:functional-monotonicity»` | abbrev | **Def. |
| `«eq:functional-monotonicity»` | abbrev | **Eq. |
| `«def:functional-monotonicity/via-f»` | theorem | Def. |
| `«def:residual-state»` | abbrev | **Def. |
| `«eq:canonical-state»` | abbrev | **Eq. |
| `«eq:canonical-state/largest»` | theorem | "The *canonical state at `i`* is the state at `i` with no rows removed: |
| `«eq:canonical-state/input-moves-canonical»` | theorem | "An input event from a canonical state leads to another canonical state." |
| `«eq:input-event»` | abbrev | **Eq. |
| `«eq:input-event/legal-expands»` | theorem | The paper's input event asks for `j` legal *and* `i ≼ j`; the second follows from the first, since the remainder table contains only rows at expansions of `i`. |
| `«sec:functional-events/input-cumulative»` | theorem | "`input(j)` then `input(k)` has the effect of `input(k)` alone; `input(i)` at `(i,R)` has no effect." |
| `«def:output-event»` | abbrev | **Def. |
| `«eq:output-action»` | theorem | **Eq. |
| `«def:output-event/commit-iff-seal»` | theorem | Def. |
| `«sec:functional-events/output-ends-at-state»` | theorem | "The current row `(i,o)` remains, since `o` refines itself, so the event always ends at a state." |
| `«sec:functional-events/extra-commitments»` | theorem | "Systems may issue more commitments than an output requires, as the registrar does in Figure `fig:election-frames`(d), but extra commitments only restrict be… |
| `«def:exposable»` | abbrev | **Def. |
| `«def:exposable/no-commitment»` | theorem | Def. |
| `«sec:functional-events/functional-exposable»` | theorem | "In a functional specification this means `R[out ⪰ o] = R`: |
| `«sec:functional-events/determined»` | abbrev | §2.3 "Determination": |
| `«sec:functional-events/determined-one-element»` | theorem | "Determined": |
| `«sec:functional-events/determination-examples»` | theorem | "A functional specification can therefore have undetermined states, as in panel (b) … An input event may [reach a determined state] by retiring rows … and a… |
| `«sec:functional-events/stays-determined»` | theorem | "An event from a determined state always leads to another determined state: |
| `«def:run»` | abbrev | **Def. |
| `«def:run/reachable-without-commitment»` | abbrev | "A run is *commitment-free* when none of its output events applies a commitment. |
| `«lem:run-residual»` | theorem | **Lemma `lem:run-residual`** (Rows remaining after a run). |
| `«eq:run-residual»` | abbrev | **Eq. |
| `«lem:run-residual/example»` | theorem | Example after Lemma `lem:run-residual`: |
| `«def:consistency»` | abbrev | **Def. |
| `«prop:confluence»` | theorem | **Prop. |
| `«eq:reconciliation»` | abbrev | **Eq. |
| `«thm:functional-calm»` | theorem | **Theorem `thm:functional-calm`** (Functional CALM). |
| `«thm:functional-calm/example»` | theorem | Example after Theorem `thm:functional-calm`: |
| `«cor:state-by-input»` | theorem | **Corollary `cor:state-by-input`** (State is fixed by input). |
| `«cor:state-by-input/input-suffices»` | theorem | After Cor. |
| `«prop:functional-exposure-boundary»` | theorem | **Prop. |
| `«prop:functional-exposure-boundary/nonmonotone-seals»` | theorem | After Prop. |
| `«eq:query-monotonicity»` | theorem | **Eq. |

### §3 Complete CALM

File `Paper/S3_CompleteCALM.lean`; paper source `sections/complete-calm.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«fig:ambiguity-frames/f»` | theorem | Fig. |
| `«fig:ambiguity-frames/g»` | theorem | Fig. |
| `«sec:ambiguity-story/choice»` | theorem | §3.1 "Output choice and directedness": |
| `«sec:ambiguity-story/three-ways»` | theorem | §3.1: |
| `«sec:ambiguity-story/transactions-fail»` | theorem | §3.1: |
| `«sec:ambiguity-story/traceroute-passes»` | theorem | §3.1: |
| `«def:relational-specification»` | abbrev | **Def. |
| `«eq:relational-specification»` | abbrev | **Eq. |
| `«eq:fiber»` | abbrev | **Eq. |
| `«def:relational-specification/ambiguous»` | theorem | Def. |
| `«def:relational-monotonicity»` | abbrev | **Def. |
| `«eq:relational-monotonicity»` | theorem | **Eq. |
| `«def:relational-monotonicity/functional»` | theorem | After Def. |
| `«sec:lifted-monotonicity/compatible»` | abbrev | "For a set `F ⊆ O` of outputs, outputs `o₁,…,o_k` are *compatible in `F`* if some `u ∈ F` refines all of them." Lean: |
| `«def:fiber-directedness»` | abbrev | **Def. |
| `«def:fiber-directedness/singleton»` | theorem | After Def. |
| `«sec:lifted-monotonicity/directed-example»` | theorem | "The fiber `{{a},{b},{a,b,c},{a,b,d},{a,b,c,d}}` under inclusion is directed, since `{a,b,c,d}` refines every member, yet `{a}` and `{b}` have two incomparab… |
| `«sec:lifted-monotonicity/figure-fibers»` | theorem | "Thus the traceroute fiber is directed: |
| `«eq:joint-output-order»` | abbrev | **Eq. |
| `«def:lifted-monotonicity»` | abbrev | **Def. |
| `«eq:lifted-monotonicity»` | theorem | **Eq. |
| `«def:lifted-monotonicity/functional»` | theorem | After Def. |
| `«def:lifted-monotonicity/relmono-directed»` | theorem | After Def. |
| `«def:lifted-monotonicity/hoare»` | theorem | After Def. |
| `«def:lifted-monotonicity/not-reflexive»` | theorem | After Def. |
| `«def:common-expansion-condition»` | abbrev | **Def. |
| `«def:common-expansion-condition/empty»` | theorem | After Def. |
| `«prop:common-expansion-form»` | theorem | **Prop. |
| `«sec:lifted-output-events/functional»` | theorem | §3.4: |
| `«sec:complete-calm-theorem/lift-unchanged»` | theorem | "Specification states, input events, runs, commitment-free runs, and consistency are defined as before, and the results of Section `sec:executions` … lift un… |
| `«thm:complete-calm»` | theorem | **Theorem `thm:complete-calm`** (Complete CALM). |
| `«prop:exposure-boundary»` | theorem | **Prop. |
| `«prop:exposure-boundary/common-expansion»` | theorem | Prop. |
| `«prop:exposure-boundary/functional»` | theorem | After Prop. |

### §4.1–4.4 Distributed execution

File `Paper/S4_Distributed.lean`; paper source `sections/distributed-histories.tex, sections/distributed.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«def:distributed-history»` | abbrev | **Def. |
| `«def:distributed-history/well-formed»` | abbrev | Def. |
| `«def:distributed-history/happens-before»` | abbrev | Def. |
| `«def:distributed-history/consistent-cut»` | abbrev | Def. |
| `«sec:histories/cut-determines-runs»` | theorem | "A consistent cut contains a prefix of each participant's history events, so by item 3 it determines one run per participant." Lean: |
| `«def:participant-run»` | abbrev | **Def. |
| `«def:participant-run/is-run»` | theorem | Def. |
| `«fig:participant-runs»` | theorem | **Fig. |
| `«fig:participant-runs/general»` | theorem | The general form of Fig. |
| `«sec:distributed-consistency/continuation»` | abbrev | "A continuation of a history at a consistent cut `C` is a history `H'` that extends the history events of `C` with further history events after them." Lean: |
| `«sec:distributed-consistency/cut-confluent»` | abbrev | "A consistent cut `C` is confluent at `j` … when some continuation at `C` has a final cut with endpoint `((j,R))_{p∈P}` for some `R`." |
| `«sec:distributed-consistency/cut-confluent-iff-runs»` | theorem | "History events at different participants are independent, so this holds exactly when the participant runs at `C` are confluent at `j`." |
| `«def:distributed-consistency»` | abbrev | **Def. |
| `«prop:distributed-consistency»` | theorem | **Prop. |
| `«prop:distributed-consistency/literal-matching»` | theorem | Prop. |
| `«sec:distributed-consistency/lifted-monotonicity»` | theorem | "By Complete CALM, which reduces to Functional CALM with one output per input, a specification has distributed consistency exactly when it satisfies Lifted M… |
| `«cor:convergence»` | theorem | **Cor. |
| `«cor:convergence/relational-fails»` | theorem | After Cor. |
| `«cor:convergence/relational-fails-minimal»` | theorem | The same failure on a minimal example: |
| `«sec:distributed-consistency/message-data»` | theorem | *Message data.* "Data can influence which events occur next at the receiver, but it never directly changes the receiver's specification state, and nothing in… |
| `«sec:distributed-consistency/sharing-outputs»` | theorem | *Message data*: |
| `«sec:systems/registrar»` | theorem | "The registrar … emits `⊥` and closes the polls in the same event (Figure election-frames(d)); the output event for `⊥` does not require the poll-closing sea… |
| `«def:commitment»` | abbrev | **Def. |
| `«eq:commitment-excludes»` | theorem | **Eq. |
| `«sec:systems/seals-and-choices-are-commitments»` | theorem | "The seals and choices of Definitions output-event and lifted-output-event satisfy this definition: |
| `«prop:seal-or-choose»` | theorem | **Prop. |
| `«prop:seal-or-choose/functional»` | theorem | "In a functional specification each fiber has one row, so every commitment seals." |
| `«def:strategy»` | abbrev | **Def. |
| `«def:system»` | abbrev | **Def. |
| `«def:system/produced»` | theorem | Def. |
| `«def:system/restrict»` | theorem | Def. |
| `«def:system-output-event»` | abbrev | **Def. |
| `«def:commitment-event»` | abbrev | **Def. |
| `«sec:systems/commitment-event-unobserved»` | theorem | After Def. |
| `«eq:lifted-validity»` | theorem | **Eq. |
| `«sec:systems/legal-event-containment»` | theorem | "A legal `Out_γ(o)` issues at least the commitments of the `output(o)` of Sections functional-calm–complete-calm: |
| `«sec:systems/output-is-canonical-event»` | theorem | "… and `output(o)` is the case in which they remove exactly those." Lean: |
| `«sec:systems/system-histories»` | theorem | "The environment observes `o`, not `γ`." Together with Def. |
| `«sec:systems/bases-differ»` | theorem | *A transactional example of bespoke commitments.* "The lock manager … is one system; multiversion timestamp ordering (MVTO) is another, and they have differe… |
| `«fig:cc-commitments»` | theorem | Fig. |
| `«sec:systems/two-systems-two-choices»` | theorem | *A transactional example of bespoke commitments.* "Both are choices: |
| `«sec:systems/neither-is-the-choice»` | theorem | "… and neither is the choice `c_o` of Definition lifted-output-event." At the canonical state of an input whose transactions `A`, `B`, `C` have each requeste… |
| `«sec:systems/run-under-basis»` | abbrev | "We call the runs of Sections functional-calm–complete-calm canonical runs, and a run under a basis `ℬ` is one whose output and commitment events apply only… |
| `«sec:systems/canonical-equivalent»` | theorem | *Canonical runs suffice.* "Locks, timestamps, quorums, and consensus differ in how and when they decide. |
| `«sec:systems/canonical-example»` | theorem | *Canonical runs suffice*, example. |
| `«sec:coordination/closing-after-voting»` | theorem | §4.4: |
| `«def:contradicts»` | abbrev | **Def. |
| `«def:coordination»` | abbrev | **Def. |
| `«def:coordination/distributed»` | abbrev | Def. |
| `«def:coordination/specification»` | abbrev | Def. |
| `«def:coordination-free»` | abbrev | **Def. |
| `«def:coordination-free/local-iff»` | theorem | Def. |
| `«def:coordination-free/distributed»` | abbrev | Def. |
| `«def:coordination-free/distributed-of-free»` | theorem | Def. |
| `«sec:coordination/specification-contradicted»` | theorem | "Whether a commitment requires coordination depends on the set of runs: |
| `«def:coordination-free/specification»` | abbrev | Def. |
| `«sec:coordination/closing-before-voting-seals»` | theorem | "Closing the polls before every voter has voted seals the remaining ballots." Lean: |
| `«sec:coordination/choices-by-strategies»` | theorem | "Outputs, by contrast, come only from the system's strategies, so a choice requires coordination only when the system can perform a run that emits an output… |
| `«def:coordination-free/commitment-free-runs»` | theorem | Def. |
| `«thm:commitments-require-coordination»` | theorem | **Prop. |
| `«thm:commitments-require-coordination/any-bases»` | theorem | Prop. |
| `«thm:commitments-require-coordination/reach»` | theorem | Prop. |
| `«thm:commitments-require-coordination/any-event»` | theorem | Prop. |
| `«thm:commitments-require-coordination/confined-to-current-input»` | theorem | "The conflict is confined to the current input. |
| `«sec:coordination/shared-nothing-single-key»` | theorem | Paragraph "Locks in a shared-nothing database": |
| `«sec:coordination/shared-nothing-cross-key»` | theorem | Paragraph "Locks in a shared-nothing database", *Distributed coordination*: |
| `«sec:coordination/two-phase-commit»` | theorem | Paragraph "Locks in a shared-nothing database", *No coordination*: |
| `«sec:coordination/two-phase-commit-detects»` | theorem | Paragraph "Locks in a shared-nothing database", *No coordination*: |
| `«sec:coordination/shared-nothing-only-second»` | theorem | Paragraph "Locks in a shared-nothing database": |
| `«sec:coordination/conflict-is-choice»` | theorem | "The first event's commitment is a choice against `x`." Lean: |
| `«sec:coordination/conflict-is-choice-commit»` | theorem | "The first event's commitment is a choice against `x`", when the first event is a commitment event `commit(γ)`, as the proposition allows ("an output or comm… |
| `«sec:coordination/deterministic-reconciliation»` | theorem | "Under Lifted Monotonicity, participants at a common input `j` can each emit a `u ∈ S(j)` that refines everything emitted, without commitment; choosing `u` b… |

### §4.5 Complete CAP

File `Paper/S4_5_CompleteCAP.lean`; paper source `sections/distributed.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«sec:complete-cap/intro»` | theorem | Section `sec:complete-cap`, opening: |
| `«def:partitioned-history»` | abbrev | **Def. |
| `«def:partitioned-history/unfolded»` | theorem | Def. |
| `«sec:complete-cap/system»` | abbrev | Paragraph after Def. |
| `«sec:complete-cap/system-produced»` | theorem | "We fix a system …": |
| `«sec:complete-cap/environment»` | theorem | "… and an adversarial environment that may supply any legal input event to any participant." Lean: |
| `«def:partition-notions»` | abbrev | **Def. |
| `«def:partition-notions/for»` | abbrev | Def. |
| `«def:partition-notions/for-S»` | theorem | Def. |
| `«def:partition-notions/unfolded»` | theorem | Def. |
| `«def:partition-notions/at-cuts»` | theorem | Def. |
| `«def:partition-consistency»` | abbrev | **Def. |
| `«def:partition-consistency/unfolded»` | theorem | Def. |
| `«def:partition-consistency/at-cuts»` | theorem | Def. |
| `«def:lm-for-A»` | abbrev | **Def. |
| `«sec:complete-cap/lm-for-S»` | theorem | "With `E = S`, Lifted Monotonicity for `E` is the common-expansion condition." |
| `«thm:complete-cap»` | theorem | **Theorem `thm:complete-cap` (Complete CAP).** "For an ordered specification `S` and an explicit relation `E ⊆ S`, the following are equivalent: |
| `«cor:complete-cap-S»` | theorem | **Corollary `cor:complete-cap-S`.** "Some system has Availability and Partition Consistency if and only if `S` satisfies Lifted Monotonicity." |
| `«cor:complete-cap-S/commitment-free»` | theorem | Corollary `cor:complete-cap-S`: |
| `«sec:complete-cap/necessity-any-system»` | theorem | "A system might hope to keep more outputs available by issuing commitments, coordinating within each side of a partition. |
| `«sec:complete-cap/proof-system-coordination-free»` | theorem | "Nor does the system in the proof need coordination. |
| `«sec:complete-cap/A-eq-S-no-commitment»` | theorem | "For `E = S` it needs no commitment at all." Lean: |
| `«sec:complete-cap/local-choice-necessary»` | theorem | "For a smaller `E` such local choices can be necessary: |
| `«sec:complete-cap/lm-for-A-fails»` | theorem | "When Lifted Monotonicity for `E` fails, some output of `E` waits for another component, sacrificing Availability, or is emitted anyway, sacrificing Partitio… |
| `«sec:complete-cap/deterministic-strategies»` | theorem | Precise reading (not a claim of the paper): |
| `«sec:complete-cap/gl-register»` | theorem | "Consider a register specification whose inputs are sets of operations with their real-time precedence, and whose outputs answer every operation of the input… |
| `«sec:complete-cap/gl-no-system»` | theorem | "By Complete CAP, then, no system keeps both outputs available and consistent across a partition, which is Gilbert and Lynch's theorem." Lean: |
| `«sec:complete-cap/gl-two-row-forced»` | theorem | "The proof needs less than the full hypotheses here, which is why it yields Gilbert and Lynch's theorem exactly. |
| `«sec:complete-cap/gilbert-lynch»` | theorem | "Their theorem is a case of Complete CAP" … "No such refinement exists.": |
| `«sec:complete-cap/gl-realized»` | theorem | "Appendix `app:cap-response` takes precedence from real time" — Corollary `cor:gilbert-lynch`, client form (both hypotheses required only of two-participant… |
| `«sec:complete-cap/response-form»` | theorem | "extends Complete CAP to systems that choose their responses when responses are not forced" — Theorem `thm:complete-cap-response` (see `Paper/AppF_ResponseAv… |
| `«sec:complete-cap/gl-async»` | theorem | "and derives the theorem in Gilbert and Lynch's asynchronous model" (Proposition `prop:gl-async`). |

### §5 Composition and Proper Coordination

File `Paper/S5_Composition.lean`; paper source `sections/composition.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«eq:spec-composition»` | theorem | Eq. |
| `«sec:composition/seq-total»` | theorem | "Since `S₁` is total on `I` and `S₂` is total on `M` (it has a row at every `m ∈ M`), every `i ∈ I` has a nonempty fiber in `S₂ ∘ S₁`." Lean: |
| `«sec:composition/middle-totality-needed»` | theorem | Totality of `S₂` on *all* of `M` is needed (not stated in the paper; it explains the hypothesis above). |
| `«lem:composition»` | theorem | **Lemma `lem:composition`** (Composition): |
| `«sec:composition/associativity»` | theorem | "By associativity the lemma extends to finite pipelines." |
| `«sec:composition/function-tables»` | theorem | "For a function `f`, its table `{(i,f(i))}` satisfies Lifted Monotonicity exactly when `f` is monotone (Section `sec:lifted-monotonicity`)." Lean: |
| `«sec:composite-calm/complete-calm»` | theorem | "The composite is itself an ordered specification. |
| `«sec:composite-calm/middle-order»` | theorem | "The orders on `I` and `O` are part of the composite's contract with its environment. |
| `«sec:composite-calm/all-monotone»` | theorem | "First, every stage is monotone. |
| `«sec:composite-calm/crdt-query»` | theorem | "The CRDT observations of Section `sec:crdt-instance` have this shape: |
| `«sec:composite-calm/filtering»` | theorem | "Second, the upstream can filter out the inputs on which the downstream is not monotone. |
| `«sec:composite-calm/cancellation»` | theorem | "Third, considering a different order on `M` can make two non-monotone stages both monotone. |
| `«prop:joint-monotone»` | theorem | **Proposition `prop:joint-monotone`** (Jointly monotone composites): |
| `«sec:composite-calm/reach»` | theorem | "The three cases do not cover every monotone composite (Appendix `app:composition`). |
| `«sec:proper-coordination/kvs-on-logs»` | theorem | "The replicated store of the opening extends the filtering case of Proposition `prop:joint-monotone`(2). |
| `«def:proper-coordination»` | theorem | **Definition `def:proper-coordination`** (Proper Coordination): |
| `«thm:proper-coordination»` | theorem | **Theorem `thm:proper-coordination`** (Proper Coordination): |
| `«sec:proper-coordination/locks-overhead»` | theorem | "The theorem holds whatever basis `𝒮₁` uses, and a proper pipeline is itself a guard for a further stage (Corollary `cor:pipelines`). |

### §6 Instances

File `Paper/S6_Instances.lean`; paper source `sections/instances.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«sec:query-instance/weaker-monotonicity»` | theorem | Sec. |
| `«sec:query-instance/one-fact-version»` | theorem | Sec. |
| `«sec:query-instance/node-monotonicity»` | theorem | Sec. |
| `«sec:query-instance/all-nodes»` | theorem | Sec. |
| `«sec:query-instance/pairing»` | theorem | Sec. |
| `«sec:query-instance/deterministic-behaviors»` | theorem | Sec. |
| `«sec:crdt-instance/state-function»` | theorem | Sec. |
| `«sec:crdt-instance/state-monotone»` | theorem | Sec. |
| `«sec:crdt-instance/query-calm»` | theorem | Sec. |
| `«sec:crdt-instance/query-monotone-on-reachable»` | theorem | Sec. |
| `«sec:crdt-instance/two-phase»` | theorem | Sec. |
| `«sec:crdt-instance/semilattice»` | theorem | Sec. |
| `«sec:crdt-instance/some-refinement»` | theorem | Sec. |
| `«def:hat-spec»` | abbrev | **Definition `def:hat-spec`** (HAT specification): |
| `«def:hat-spec/inputs-closed»` | theorem | Def. |
| `«def:hat-spec/read-rule»` | theorem | Def. |
| `«thm:hat-levels»` | theorem | **Theorem `thm:hat-levels`** (HAT levels): |
| `«thm:hat-levels/answers-stable»` | theorem | Proof sketch of Thm. |
| `«thm:hat-levels/lost-update-pair»` | theorem | Proof sketch of Thm. |
| `«sec:hat-instance/rc-timestamps»` | theorem | "The timestamp condition is needed. |
| `«sec:iconfluence-instance/model»` | abbrev | Sec. |
| `«sec:iconfluence-instance/reachable»` | abbrev | "A state is reachable when it can be derived from `s₀` by applying transactions and merging states, with every state along the way satisfying `𝓘`." Lean: |
| `«sec:iconfluence-instance/iconfluent-def»` | theorem | "`T` is invariant confluent exactly when `𝓘(s₁ ∪ s₂)` for all reachable `s₁` and `s₂`." Lean: |
| `«sec:iconfluence-instance/bailis-definition»` | theorem | "Every reachable state descends from `s₀`, so `T` is invariant confluent exactly when `𝓘(s₁ ∪ s₂)` for all reachable `s₁` and `s₂`." This is the step from Ba… |
| `«sec:iconfluence-instance/spec»` | theorem | "From an instance `(s₀, T, 𝓘)` of their model we construct a specification `S_𝓘` in ours as follows. |
| `«prop:iconfluence-lm»` | theorem | **Proposition `prop:iconfluence-lm`** (Invariant confluence and Lifted Monotonicity): |
| `«sec:iconfluence-instance/iconfluence-is-consistency»` | theorem | Invariant confluence is consistency of `S_𝓘`: |
| `«sec:iconfluence-instance/uniqueness»` | theorem | The uniqueness example: |
| `«sec:iconfluence-instance/concurrency-decides»` | theorem | "Concurrency, not the transactions alone, decides the outcome: |
| `«sec:operational-models/later-sends»` | theorem | "An output of the machine is an input of the client that receives it, so a client's later sends happen after everything the machine had received when it emit… |
| `«def:induced-specification»` | theorem | **Def. |
| `«prop:induced-specification»` | theorem | **Prop. |
| `«sec:operational-models/testing-witness»` | theorem | "If Lifted Monotonicity fails, finitely many executions show it: |
| `«sec:operational-models/both-halves»` | theorem | "The second is proof. |
| `«prop:declared-specification»` | theorem | **Prop. |

### Appendix A: Notation

File `Paper/AppA_Notation.lean`; paper source `appendices/notation.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«app:notation/functional-specification»` | abbrev | *specification* — `Spec = (I,≼,O,≼,S)`, total on `I`, one output per input; induced `f` (Def. |
| `«app:notation/expands»` | abbrev | *expands; expansion* — `i ≼ j`: |
| `«app:notation/refines»` | abbrev | *refines; refinement* — `o ≼ u`: |
| `«app:notation/common-expansion»` | abbrev | *common expansion* — an input that expands each (Sec. |
| `«app:notation/common-refinement»` | abbrev | *common refinement* — an output that refines each (Sec. |
| `«app:notation/monotone-functional»` | abbrev | *monotone (functional)* — `i ≼ j ⇒ f(i) ≼ f(j)` (Def. |
| `«app:notation/selection-in»` | abbrev | *selection* — `R[predicate on in, out]` (Sec. |
| `«app:notation/selection-out»` | abbrev | *selection* `R[out ⪰ o]` (see `«app:notation/selection-in»`). |
| `«app:notation/in»` | abbrev | *`in(R)`* — the inputs in `R` (Sec. |
| `«app:notation/out»` | abbrev | *`out(R)`* — the outputs in `R` (Sec. |
| `«app:notation/fiber»` | abbrev | *row at `k`* — a row `(k,u)` (Sec. |
| `«app:notation/upper-fiber»` | abbrev | *upper fiber* — `out(R[in ⪰ k])` (Sec. |
| `«app:notation/state»` | abbrev | *state `(i,R)`* — current input and remainder table, every row at an expansion of `i` (Def. |
| `«app:notation/legal»` | abbrev | *legal input* — an input with a row in `R` (Def. |
| `«app:notation/canonical-state»` | abbrev | *canonical state* — `σ_S(i) = (i, S[in ⪰ i])` (Eq. |
| `«app:notation/input-event»` | abbrev | *input event* — `input(j)` keeps `R[in ⪰ j]` (Eq. |
| `«app:notation/input-retirement»` | abbrev | *input retirement* — the rows `input(j)` removes (Eq. |
| `«app:notation/output-event»` | abbrev | *output event* — `output(o)` keeps `R[out ⪰ o]` and emits `o` (Def. |
| `«app:notation/seal»` | abbrev | *seal* — the output event, when it removes rows (Def. |
| `«app:notation/output-event-commits»` | abbrev | *commitment* (§2 sense) — an output event that removes rows (Def. |
| `«app:notation/exposable»` | abbrev | *exposable* — `output(o)` applies no commitment (Def. |
| `«app:notation/determined»` | abbrev | *determined* — the upper fiber has one element; *determination* — reaching such a state (Sec. |
| `«app:notation/run»` | abbrev | *run* — finite event sequence from a canonical state (Def. |
| `«app:notation/commitment-free»` | abbrev | *commitment-free* — no output event commits (Def. |
| `«app:notation/consistent»` | abbrev | *consistent* — every finite family of runs can reach one common state at each common expansion `j` (Def. |
| `«app:notation/confluent-at»` | abbrev | *confluent at `j`* (Def. |
| `«app:notation/relational-specification»` | abbrev | *relational specification* — `S ⊆ I × O` total on `I` (Def. |
| `«app:notation/ambiguous»` | abbrev | *ambiguous* — some fiber has several outputs (Def. |
| `«app:notation/stranded-output»` | abbrev | *stranded output* — an output at `i` with no refinement at some expansion (Sec. |
| `«app:notation/incompatible-pair»` | abbrev | *incompatible pair* — two outputs at `i` with no common refinement there (Sec. |
| `«app:notation/relational-monotonicity»` | abbrev | *Relational Monotonicity* — every output keeps a refinement as input grows (Def. |
| `«app:notation/compatible-in»` | abbrev | *compatible in `F`* — some `u ∈ F` refines all (Def. |
| `«app:notation/directed»` | abbrev | *directed* — every (nonempty) finite subset compatible (Def. |
| `«app:notation/directed-outputs»` | abbrev | *Directed Outputs* — every fiber directed (Def. |
| `«app:notation/joint-lift»` | abbrev | *joint lift `A ⊑ B`* — every nonempty finite `X ⊆ A` is compatible in `B` (Eq. |
| `«app:notation/lifted-monotonicity»` | abbrev | *Lifted Monotonicity* — `i ≼ j ⇒ S(i) ⊑ S(j)` (Def. |
| `«app:notation/common-expansion-condition»` | abbrev | *common-expansion condition* — rows with a common expansion `j` have a common refinement in `S(j)` (Def. |
| `«app:notation/ruled-out»` | abbrev | *ruled out by `o`* — a row whose output does not refine `o` (Sec. |
| `«app:notation/Sealed»` | abbrev | *`Sealed_o`* — ruled-out rows at inputs with no row refining `o` (Eq. |
| `«app:notation/Retired»` | abbrev | *`Retired_o`* — ruled-out rows refined by a kept row at the same input (Eq. |
| `«app:notation/Rejected»` | abbrev | *`Rejected_o`* — the rest (Eq. |
| `«app:notation/lifted-seal»` | abbrev | *seal* (lifted) — remove `Sealed_o` (Def. |
| `«app:notation/output-retirement»` | abbrev | *output retirement* — remove `Retired_o`, not a commitment (Def. |
| `«app:notation/choice»` | abbrev | *choice* — remove `Rejected_o` (Def. |
| `«app:notation/participant»` | abbrev | *participant* — holds a specification state (Sec. |
| `«app:notation/message»` | abbrev | *message* — `m = (j,d)`, a cumulative input `j` (or `∅`) and other data `d` (Sec. |
| `«app:notation/distributed-history»` | abbrev | *distributed history* — locally ordered input, output, send and receive events (Def. |
| `«app:notation/history-event»` | abbrev | *history event* — (Def. |
| `«app:notation/happens-before»` | abbrev | *happens-before* — closure of local orders and send-before-receive (Def. |
| `«app:notation/consistent-cut»` | abbrev | *consistent cut* — a set of history events closed under happens-before (Def. |
| `«app:notation/endpoint»` | abbrev | *participant run; endpoint* — `p`'s input, output, and commitment events at `C`; `(σ_p(C))_{p ∈ P}` (Def. |
| `«app:notation/continuation»` | abbrev | *continuation* — a history extending `C` (Sec. |
| `«app:notation/cut-confluent-at»` | abbrev | *cut confluent at `j`* — some continuation brings every participant to one state `(j,R)` (Sec. |
| `«app:notation/distributed-consistency»` | abbrev | *distributed consistency* — every consistent cut of every history is confluent at every common expansion (Def. |
| `«app:notation/commitment»` | abbrev | *commitment* — partial function on states removing rows, none refined by a remaining row at the same input (Def. |
| `«app:notation/strategy»` | abbrev | *local history; strategy* — `p`'s history events in order; `θ_p(λ)`, the output, commitment, send, and receive events `p` may perform next (Def. |
| `«app:notation/system»` | abbrev | *system* — a commitment basis `𝓑` and a strategy per participant (Def. |
| `«app:notation/basis»` | abbrev | *basis* (Def. |
| `«app:notation/produced»` | abbrev | *produced* — every non-input event permitted by its strategy and using only commitments from `𝓑` (Def. |
| `«app:notation/system-output-event»` | abbrev | *system output event `Out_γ(o)`* — applies commitments `γ` from the basis, retires, emits `o` (Def. |
| `«app:notation/commitment-event»` | abbrev | *commitment event `commit(γ)`* — applies a nonempty sequence `γ` from the basis, emits nothing (Def. |
| `«app:notation/run-under-basis»` | abbrev | *run under a basis* — events whose commitments come from the basis (Def. |
| `«app:notation/canonical-run»` | abbrev | *canonical run* — a run of Sections 2–3 (Def. |
| `«app:notation/observably-equivalent»` | abbrev | *observably equivalent* — same input and output events, commitments and commitment events erased; every run has a canonical one (Lem. |
| `«app:notation/contradicts»` | abbrev | *contradicts* — accepts an input the commitment seals, or emits an output it chooses against (Def. |
| `«app:notation/coordination»` | abbrev | *requires coordination* — a commitment some run contradicts (Def. |
| `«app:notation/distributed-coordination»` | abbrev | *requires distributed coordination* — a commitment some run at another participant contradicts (Def. |
| `«app:notation/coordination-free»` | abbrev | *coordination-free* — applies no commitment that requires coordination (Def. |
| `«app:notation/partitioned-history»` | abbrev | *partitioned history* — no message crosses components (Def. |
| `«app:notation/explicit-relation»` | abbrev | *explicit relation `E`; explicit, implicit output* — `E ⊆ S`, the rows whose outputs must stay available; outputs of `E`, and the other permitted outputs (Def. |
| `«app:notation/availability»` | abbrev | *Availability for `E`* — each output of `R(i) ∩ E(i)` emittable locally (Def. |
| `«app:notation/lm-for-A»` | abbrev | *Lifted Monotonicity for `E`* — every finite set of rows of `E` with a common expansion `j` has a common refinement in `S(j)` (Def. |
| `«app:notation/deployment»` | abbrev | *deployment* — one explicit relation `E_p` per participant (Def. |
| `«app:notation/partition-consistency»` | abbrev | *Partition Consistency* — final cuts of partitioned histories confluent (Def. |
| `«app:notation/response-obligation»` | abbrev | *response obligation* — per participant, the outputs that count as answers; upward closed within fibers (Def. |
| `«app:notation/response-interface»` | abbrev | *response interface* — a total, self-continuing explicit relation `T ⊆ Q` (Def. |

### Appendix B: Deferred proofs

File `Paper/AppB_Proofs.lean`; paper source `appendices/proof-machinery.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«proof:lem:run-residual»` | theorem | Proof of Lemma `lem:run-residual`: |
| `«proof:prop:confluence»` | theorem | Proof of Prop. |
| `«proof:thm:functional-calm»` | theorem | Proof of Thm. |
| `«proof:cor:state-by-input»` | theorem | Proof of Cor. |
| `«proof:prop:functional-exposure-boundary»` | theorem | Proof of Prop. |
| `«proof:prop:common-expansion-form»` | theorem | Proof of Prop. |
| `«lem:reconciliation»` | theorem | **Lemma `lem:reconciliation`** (Reconciliation). |
| `«lem:reconciliation/consistency-over-runs»` | theorem | Lemma `lem:reconciliation` quantifies over runs with their events; Def. |
| `«proof:thm:complete-calm/if»` | theorem | Proof of Thm. |
| `«proof:thm:complete-calm/only-if»` | theorem | Proof of Thm. |
| `«proof:thm:complete-calm»` | theorem | Proof of Thm. |
| `«proof:prop:exposure-boundary/only-if»` | theorem | Proof of Prop. |
| `«proof:prop:exposure-boundary»` | theorem | Proof of Prop. |
| `«app:pairs-suffice»` | theorem | `app:pairs-suffice`: |
| `«app:pairs-suffice/rows-at-j»` | theorem | `app:pairs-suffice`: |
| `«app:pairs-suffice/k-at-a-time»` | theorem | `app:pairs-suffice`: |
| `«app:pairs-suffice/k-set-not-monotone»` | theorem | Consequence for `app:pairs-suffice`: |

### Appendix B: Deferred proofs for §4

File `Paper/AppB_ProofsDistributed.lean`; paper source `appendices/proof-machinery.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«proof:prop:distributed-consistency»` | theorem | Proof of Prop. |
| `«app:exchanging-outputs»` | theorem | *Exchanging outputs* (table level). |
| `«app:exchanging-outputs/cut»` | theorem | *Exchanging outputs* (history level). |
| `«app:exchanging-outputs/honored-table-not-state»` | theorem | *Exchanging outputs.* "This restriction is a table, not a specification state: |
| `«proof:thm:commitments-require-coordination»` | theorem | Proof of Prop. |
| `«thm:complete-cap/proof-sufficiency»` | theorem | Proof of Theorem `thm:complete-cap`, (2)⇒(1): |
| `«thm:complete-cap/proof-necessity»` | theorem | Proof of Theorem `thm:complete-cap`, (1)⇒(2): |
| `«cor:complete-cap-S/proof-cf-continuations»` | theorem | Proof of Corollary `cor:complete-cap-S`: |

### Appendix B: Invariant confluence

File `Paper/AppB_InvariantConfluence.lean`; paper source `appendices/proof-machinery.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«app:iconfluence/history»` | abbrev | "A transaction history `h` … is a finite partial order of transaction events, each labeled by a transaction in `T`; `e' < e` means that `e'` was visible to t… |
| `«app:iconfluence/expansion-order»` | theorem | "History `h'` expands `h` when `h` is a downward-closed sub-order of `h'`, so an event keeps exactly the predecessors it had." Lean: |
| `«app:iconfluence/eval»` | theorem | "The state of a history is computed event by event: |
| `«app:iconfluence/sub-keeps-pre-post»` | theorem | "A downward-closed sub-history keeps each event's predecessors, and so its `pre` and `post`." |
| `«app:iconfluence/eval-union»` | theorem | "Hence the state of a union of downward-closed sub-histories is the union of their states." Lean: |
| `«app:iconfluence/pre-post-as-eval»` | theorem | "Because `h` is a partial order and transactions are inflationary (`t(s) ⊇ s`), `pre(e)` is the state of the sub-history strictly below `e` and `post(e)` is… |
| `«app:iconfluence/valid-def»` | theorem | "A history is locally valid when every `pre(e)` and `post(e)` satisfies `𝓘` … It is valid when every downward-closed sub-history `c` has `𝓘(eval(c))`." |
| `«app:iconfluence/valid-locally-valid»` | theorem | (Used in the proof) A valid history is locally valid, since `pre(e)` and `post(e)` are states of downward-closed sub-histories. |
| `«app:iconfluence/inputs-closed»` | theorem | "The specification `S_𝓘` has the locally valid histories as inputs; a downward-closed sub-order of a locally valid history is locally valid, so the inputs ar… |
| `«app:iconfluence/spec»` | theorem | "An output is a state, and `u` covers `s` when `s ⊆ u`. |
| `«app:iconfluence/total»` | theorem | "Taking `g` empty gives `s₀`, so the specification is total." |
| `«app:iconfluence/proof-common-expansion-form»` | theorem | "We use the common-expansion form of Lifted Monotonicity (Prop. |
| `«app:iconfluence/proof-valid-reachable»` | theorem | First step: |
| `«app:iconfluence/proof-union-valid»` | theorem | (⇒), key step: |
| `«app:iconfluence/proof-merge-reachable»` | theorem | (⇒), inline: |
| `«app:iconfluence/proof-forward»` | theorem | (⇒): |
| `«app:iconfluence/proof-disjoint-union»` | theorem | (⇐): |
| `«app:iconfluence/proof-parts»` | theorem | (⇐): |
| `«app:iconfluence/proof-halves»` | theorem | (⇐): |
| `«app:iconfluence/proof-pair»` | theorem | (⇐): |
| `«app:iconfluence/proof-reachable-valid»` | theorem | (⇐): |
| `«app:iconfluence/proof-backward»` | theorem | (⇐): |
| `«app:iconfluence/proof-directed-suffices»` | theorem | (⇐): |

### Appendix C: Commitment bases

File `Paper/AppC_CommitmentBases.lean`; paper source `appendices/commitment-bases-general.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«eq:seal-inputs»` | abbrev | **Eq. |
| `«eq:output-retirements»` | abbrev | **Eq. |
| `«eq:choice-removals»` | abbrev | **Eq. |
| `«def:lifted-output-event»` | abbrev | **Def. |
| `«eq:canonical-seal-commitment-relational»` | theorem | **Eq. |
| `«def:lifted-output-event/examples»` | theorem | After Def. |
| `«app:lifted-output-events/disjoint»` | theorem | "The three sets are disjoint." |
| `«app:lifted-output-events/commute»` | theorem | "… removing the rows of either commitment leaves the other sets unchanged, so the event may apply `s_o` and `c_o` in either order." |
| `«app:lifted-output-events/choice-narrows»` | theorem | "The choice commitment only narrows fibers: |
| `«app:lifted-output-events/functional»` | theorem | "With one row per input, `Retired_o` and `Rejected_o` are empty; this is the functional output event of Definition `def:output-event`." |
| `«app:lifted-output-events/exposable»` | theorem | "Exposability lifts with the event: |
| `«prop:exposability»` | theorem | **Prop. |
| `«eq:safe-exposure»` | abbrev | **Eq. |
| `«def:canonical-commitment-basis»` | abbrev | **Def. |
| `«eq:canonical-commitment-basis-relational»` | theorem | **Eq. |
| `«def:canonical-commitment-basis/kappa»` | theorem | Def. |
| `«def:canonical-commitment-basis/canonical-event»` | theorem | Def. |
| `«app:bases/functional-excludes-vacuous»` | theorem | *The canonical seals and choices are commitments.* "With one row per input, Equation commitment-excludes holds vacuously, so the seals of Definition output-e… |
| `«app:bases/seal-is-commitment»` | theorem | *The canonical seals and choices are commitments* (`s_o`). |
| `«app:bases/choice-is-commitment»` | theorem | *The canonical seals and choices are commitments* (`c_o`). |
| `«app:bases/seal-choice-commute»` | theorem | *The canonical seals and choices are commitments.* "Since `s_o` and `c_o` remove disjoint sets of rows and neither changes the other's …, each is defined on… |
| `«lem:canonical-commitment-normal-form»` | theorem | **Lemma containment, canonical support, and commitment-free events** (`lem:canonical-commitment-normal-form`). |
| `«def:canonical-system»` | abbrev | **Def. |
| `«def:canonical-system/histories»` | theorem | Def. |
| `«def:canonical-system/no-commitment-event»` | theorem | Def. |
| `«lem:compound-commitment»` | abbrev | **Lemma compound commitments are commitments** (`lem:compound-commitment`). |
| `«lem:compound-commitment/defined»` | theorem | Lemma `lem:compound-commitment`: |
| `«app:bases/compound-output-event»` | theorem | "A compound output event therefore has the same effect as an event that applies the composite commitment alone, and Lemma canonical-commitment-normal-form co… |
| `«app:bases/compound-commitment-event»` | theorem | A compound commitment event has the same effect as a commitment event that applies the composite commitment alone: |
| `«def:run-under-basis»` | abbrev | **Def. |
| `«def:run-under-basis/canonical-run»` | abbrev | Def. |
| `«def:run-under-basis/canonical-runs-are-runs»` | theorem | Def. |
| `«app:bases/observably-equivalent»` | abbrev | "Call two runs observably equivalent when they start at the same canonical state and agree once commitment sequences are erased and commitment events dropped: |
| `«lem:canonical-equivalent»` | theorem | **Lemma canonical equivalents** (`lem:canonical-equivalent`). |
| `«cor:reconciliation-any-basis»` | theorem | **Cor. |
| `«app:bases/converse-fails»` | theorem | "The converse of Lemma canonical-equivalent fails: |
| `«app:bases/basis-2PL»` | abbrev | *Application-specific commitments.* "Locks and timestamps are commitments of this kind: |
| `«app:bases/basis-MVTO»` | abbrev | *Application-specific commitments*: |

### Appendix D: Proofs and details for composition

File `Paper/AppD_Composition.lean`; paper source `appendices/composition.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«cor:functional-composition»` | theorem | **Corollary `cor:functional-composition`** (Functional composition): |
| `«eq:parameterized-composition»` | theorem | Eq. |
| `«lem:parameterized-composition»` | theorem | **Lemma `lem:parameterized-composition`** (Independently parameterized composition): |
| `«eq:curried-fibers»` | theorem | Eq. |
| `«eq:curried-query-plan»` | theorem | Eq. |
| `«prop:curried-query-plan»` | theorem | **Proposition `prop:curried-query-plan`** (Curried equijoin plan): |
| `«eq:curried-composition»` | theorem | Eq. |
| `«app:composition/all-monotone»` | theorem | "If every stage satisfies Lifted Monotonicity and `𝒮₁` runs under the empty basis, the pipeline emits only what `S₂ ∘ S₁` emits under the empty basis. |
| `«app:composition/joint-monotone»` | theorem | Proof of Proposition `prop:joint-monotone`: |
| `«app:composition/reach»` | theorem | "The reach of case (3). |
| `«app:composition/capped-counter»` | theorem | "For the capped counter of Section `sec:composite-calm`, let `𝒮₁` be the table of the function `c(n) = min(n,9)` on `(ℕ, ≤)` and `𝒮₂` the table of the test `… |
| `«app:composition/boolean-toggle»` | theorem | "For the boolean toggle, let `I`, `M`, and `O` be the booleans with `false` below `true`, and let both stages be negation. |
| `«app:composition/components-commit»` | theorem | "Let `𝒮₁` have one input `*` and table `{(*,x),(*,y)}` with `x,y` incomparable, and let `𝒮₂` be the table of a function `f` that maps both to one value. |
| `«app:composition/image-canon»` | theorem | "For tables `R` of `𝒮₁` and `T` of `𝒮₂` we write `R ⋈ T = {(k,x) : |
| `«app:composition/pipeline-run»` | theorem | "A run of the pipeline is a run of `𝒮₁` under `ℬ`, together with a run of `𝒮₂\|_{𝒮₁}` from `σ(m₁)`, where `m₁` is the first output of `𝒮₁`. |
| `«app:composition/store-facts»` | theorem | "In a proper pipeline, two facts about a state `τ` that `𝒮₂\|_{𝒮₁}` reaches without commitment carry the proofs. |
| `«app:composition/guarded-lockstep»` | theorem | Proof of Theorem `thm:proper-coordination`(2): |
| `«app:composition/canonical-states-suffice»` | theorem | Proof of Theorem `thm:proper-coordination`(3): |
| `«app:composition/properness-needed»` | theorem | "Properness is needed in (3). |
| `«app:composition/replacement»` | theorem | "The commitment-erased replacement of a system has the empty basis and the same strategy, with each `Out_δ(x)` replaced by `Out_ε(x)` and its commitment even… |
| `«cor:empty-store»` | theorem | **Corollary `cor:empty-store`** (Empty store): |
| `«app:composition/empty-store»` | theorem | Proof of Corollary `cor:empty-store`: |
| `«cor:pipelines»` | theorem | **Corollary `cor:pipelines`** (Pipelines): |
| `«app:composition/pipelines»` | theorem | Proof of Corollary `cor:pipelines`: |
| `«app:composition/mutex-store»` | theorem | "Let `𝒮₁` be the log specification of Example `ex:committed-log-composition`, under its canonical basis with a strategy that allows every event, and `𝒮₂` the… |
| `«prop:invisible-coordination»` | theorem | **Proposition `prop:invisible-coordination`** (Invisible coordination): |
| `«app:composition/coverage»` | theorem | The covering argument: |
| `«app:composition/per-key»` | theorem | "Consider a store that answers each key from that key's commands, in log order. |
| `«app:composition/no-pushforward»` | theorem | "The commitments of `𝒮₁` do not themselves push forward. |
| `«app:composition/monotone-needed»` | theorem | "Monotonicity of `f` is needed. |
| `«app:composition/store-choice»` | theorem | "A downstream that must itself choose cannot delegate the choice either. |
| `«ex:committed-log-composition»` | theorem | **Example `ex:committed-log-composition`** (Replicated store), for any deterministic state machine `δ` and two distinct commands: |
| `«ex:bare-reads»` | theorem | **Example `ex:bare-reads`** (Bare reads), position-tagged responses, for any deterministic state machine `δ`, read function `rd`, and two distinct commands: |
| `«ex:bare-reads/latest-value»` | theorem | Inside Example `ex:bare-reads`: |

### Appendix E: Deployment

File `Paper/AppE_Deployment.lean`; paper source `appendices/deployment.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«def:deployment»` | abbrev | **Definition `def:deployment`** (Deployment, emitted rows, participant run family, silent participant, separable run family). |
| `«def:deployment/emitted-rows»` | theorem | Def. |
| `«def:deployment/partition»` | theorem | Def. |
| `«def:deployment/family»` | theorem | Def. |
| `«def:deployment/separable»` | theorem | Def. |
| `«def:monotone-across-partitions»` | theorem | **Definition `def:monotone-across-partitions`** (Monotone across partitions). |
| `«app:deployment/lm-for-implies-mono-across»` | theorem | "If `S` satisfies Lifted Monotonicity for a relation that contains every `E_p`, it is monotone across partitions: |
| `«app:deployment/uniform-mono-across»` | theorem | "So Lifted Monotonicity for `E` suffices for the uniform deployment `E_p = E` …" |
| `«app:deployment/lm-implies-mono-across»` | theorem | "… and Lifted Monotonicity suffices for every deployment." |
| `«app:deployment/run-outputs-chain»` | theorem | "Rows authorized only to `p` can be emitted only by `p`'s run, whose emitted outputs form a chain (each output event keeps only rows refining it)." The chain… |
| `«app:deployment/sole-rows-single-row»` | theorem | "… so a family whose emitted rows are all authorized only to `p` is separable only when it emits a single row." Lean: |
| `«app:deployment/leader-example/setup»` | theorem | "Let `P = {p,q}`, let every fiber be `{a,b}` ordered by equality, and let `E_p = S` and `E_q = ∅`, so that `p` alone names a leader." Lean: |
| `«app:deployment/leader-example/one-output»` | theorem | "A run of `p` emits at most one distinct output …" |
| `«app:deployment/leader-example/separable-shape»` | theorem | "… and `q` never emits, so every separable family consists of one row `(i,a)` or `(i,b)` beside a silent `q`." |
| `«app:deployment/leader-example»` | theorem | "So `S` is monotone across partitions, yet `(i,a)` and `(i,b)` have no common expansion and Lifted Monotonicity fails." (Any input `i` witnesses the failure.) |
| `«app:deployment/sufficient-condition»` | theorem | "The same happens whenever each authorized row has an expansion at every expansion of its input and every set of authorized rows lacking a common expansion a… |
| `«app:deployment/further-examples»` | theorem | "The causal register of Appendix `app:registers` is a further example, with no single authority, of monotonicity across partitions without Lifted Monotonicit… |
| `«app:deployment/further-examples/condition-fails»` | theorem | "… they need not satisfy this condition, since a set of rows lacking a common expansion may also contain rows of other participants." Witness: |
| `«app:deployment/full-deployment»` | theorem | "If `\|P\| ≥ 2` and `E_p = S` for every `p`, every pair of rows can be split across a partition and every single row paired with a silent participant at the co… |
| `«app:deployment/full-deployment/pairs-suffice»` | theorem | The pairs-suffice step used above (Appendix `app:pairs-suffice`). |
| `«def:deployment-availability»` | theorem | **Definition `def:deployment-availability`** (Deployment Availability). |
| `«app:deployment/uniform-availability»` | theorem | "This is Availability for `E_p`, one relation per participant. |
| `«app:deployment/full-deployment-availability»` | theorem | "… and for `E_p = S` it is Availability." `AvailabilityAt Sys n` is `CAP.Availability` restricted to histories over `Fin n` (`CAP.Availability Sys ↔ ∀ n, Ava… |
| `«app:deployment/single-authority/def»` | theorem | "A deployment is *single-authority* when `E_q = ∅` for every participant `q` but one, as in the leader example above." |
| `«app:deployment/single-authority/shape»` | theorem | "Every separable family is then one row emitted by the single authority beside a silent participant …" |
| `«app:deployment/single-authority»` | theorem | "… and monotonicity across partitions says only that each such row has an expansion at every expansion of its input." (With `\|P\| ≥ 2`, so that some partition… |
| `«app:deployment/single-authority/not-distributed»` | theorem | "In a system whose other participants emit nothing, no other participant emits an output that the authority chooses against, so its choices do not require di… |
| `«app:deployment/single-authority/coordination»` | theorem | "They still require coordination when another run of the authority may choose differently, as for the lock manager of Section `sec:coordination`." Lean: |
| `«thm:complete-cap-deployment»` | theorem | **Proposition `thm:complete-cap-deployment`** (Partition compatibility under a deployment). |
| `«thm:complete-cap-deployment/proof»` | theorem | Proof of Prop. |
| `«app:deployment/system-runs/canonical»` | theorem | "The proposition concerns canonical runs and does not use Deployment Availability. |
| `«app:deployment/system-runs»` | theorem | "So if `S` is monotone across partitions, the outputs emitted by a separable family of runs of a partitioned history, as Deployment Availability permits, hav… |
| `«app:deployment/unauthorized-refinement»` | theorem | "It does not follow that the deployment authorizes any participant to emit `u`; confluence through legal output events of the deployment would additionally r… |
| `«app:deployment/full-deployment-step»` | theorem | "With `\|P\| ≥ 2` and `E_p = S` for every `p`, item (2) is Lifted Monotonicity, and the proposition is the step behind Corollary `cor:complete-cap-S` stating t… |
| `«app:registers/history»` | abbrev | "An input is a finite operation history `h`: |
| `«app:registers/history-order»` | theorem | "We set `h ⊑ h'` when the operations of `h` form a causally closed subset of `h'` and `→` restricted to them is the order of `h`." |
| `«app:registers/no-new-past»` | theorem | "Thus an expansion never adds an operation to the causal past of an existing one." |
| `«app:registers/source-map»` | theorem | "An output is a *source map* `ρ`: |
| `«app:registers/serialization»` | theorem | "A *serialization* for replica `p` is a total order of `p`'s operations and all writes of `h` that extends `→`; it explains a read of `p` with source `w` whe… |
| `«app:registers/fibers»` | theorem | "Under causal consistency, `ρ ∈ S(h)` when each replica has a serialization explaining every read of that replica in the domain of `ρ`. |
| `«app:registers/two-write-history»` | theorem | "Participant `p` completes `w_p(x,dog)` while `q` concurrently completes `w_q(x,cat)`; … each serves a local read, `r_p` at `p` and `r_q` at `q`. |
| `«app:registers/linearizable-not-monotone-across»` | theorem | "Under linearizability, if `p` reads cat the order has `w_p(x,dog)` before `w_q(x,cat)`; if `q` reads dog it has the opposite. |
| `«app:registers/causal-two-write»` | theorem | "Under causal consistency the two replicas may serialize the concurrent writes differently, and one source map sends `r_p` to `w_q(x,cat)` and `r_q` to `w_p(… |
| `«app:registers/causal-monotone-across»` | theorem | "Under the deployment in which each replica answers only its own reads (`E_p` holds the rows whose source map is defined only on reads of `p`), the causal re… |
| `«app:registers/serialization-extends»` | theorem | Proof step: |
| `«app:registers/linear-extension»` | theorem | Supporting fact: |
| `«app:registers/same-read-incompatible»` | theorem | "Two answers to the same read remain incompatible, but only the reading replica may emit either." The causal register is not monotone: |
| `«thm:product-frontier»` | theorem | **Theorem `thm:product-frontier`** (Independent products). |
| `«app:rtc/input»` | theorem | "Consider the histories of Appendix `app:registers` with a second strict partial order `≺`: |
| `«app:rtc/views»` | theorem | "A *real-time causal view* of replica `p` assigns to every read `r` of `p` a source `s(r)` such that (1) `s(r)` is a write visible to `r`, or `v₀` if none is… |
| `«app:rtc/monotone-across»` | theorem | "Views exist … They continue … Views share a domain, so they form an antichain. |
| `«app:rtc/blind»` | theorem | "A strengthening is *real-time blind* when a tuple it selects at an input stays selected at the same history with fewer real-time edges, provided its views a… |
| `«prop:rtc-maximal»` | theorem | **Proposition `prop:rtc-maximal`** (Real-time causal maximality). |
| `«prop:rtc-maximal/forced»` | theorem | Proof of `prop:rtc-maximal`: |
| `«prop:rtc-maximal/locally-conservative»` | theorem | Proof of `prop:rtc-maximal`: |

### Appendix F: Response availability and Gilbert–Lynch

File `Paper/AppF_ResponseAvailability.lean`; paper source `appendices/cap-response.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«app:cap-response/emitted-rows»` | abbrev | "The *emitted rows* of a run are the pairs `(i,o)` such that it emits `o` at current input `i`." Lean: |
| `«def:response-obligation»` | abbrev | **Def. |
| `«def:response-obligation/fields»` | theorem | Def. |
| `«app:cap-response/trivially-available»` | theorem | "Response availability is only as strong as `Q_p`: |
| `«def:response-availability»` | abbrev | **Def. |
| `«def:response-availability/unfolded»` | theorem | Def. |
| `«def:response-availability/at-cuts»` | theorem | Def. |
| `«def:response-availability(1)»` | theorem | Def. |
| `«def:response-availability/input-acceptance-no-seal»` | theorem | "Input acceptance says that `p` never seals an expansion of its current input." Lean, at any cut, in particular the end of the history: |
| `«def:response-availability/excludes-forced-seal»` | theorem | "It excludes specifications whose answers require such a seal": |
| `«def:response-availability/election-equality-order»` | theorem | "… such as the election under the equality order (Figure `fig:nonmonotone-frame`)": |
| `«def:response-partition-consistency»` | theorem | **Def. |
| `«def:response-partition-consistency/converse-part»` | theorem | "This is the part of Partition Consistency that the converse of Theorem `thm:complete-cap` uses, so that theorem also holds with Response Partition Consisten… |
| `«def:response-partition-consistency/of-confluent»` | theorem | "Confluence at `j` implies a common refinement at `j` (Corollary `cor:reconciliation-any-basis`)." Lean, at any cut, in particular the final one. |
| `«def:response-partition-consistency/canonical»` | theorem | "for a canonical system (Definition `def:canonical-system`) the two coincide by Lemma `lem:reconciliation`, applied to the participant runs." Lean, at any cu… |
| `«def:response-partition-consistency/converse-fails»` | theorem | "With other commitments the converse can fail: |
| `«app:cap-response/replicated»` | theorem | "A system is *replicated* when its obligation is uniform and every participant runs the same strategy, which depends only on the participant's initial input… |
| `«lem:locality»` | theorem | **Lemma `lem:locality` (Locality).** "For each of some participants `p`, let `ℓ_p` be a local history that `p`'s strategy can produce from initial input `i_p… |
| `«def:response-interface»` | theorem | **Def. |
| `«def:response-interface/lm-for-T»` | theorem | "Lifted Monotonicity for `T` is that of Definition `def:lm-for-A`, and the reconciling output may lie outside `T`." Lean: |
| `«def:response-interface/T-eq-S»` | theorem | "With `T = S` it is the common-expansion condition of Proposition `prop:common-expansion-form`." |
| `«def:response-interface/confluence»` | theorem | "and by Lemma `lem:reconciliation` it is confluence of the canonical runs whose emitted rows lie in `T`." Lean: |
| `«app:cap-response/serve-interface»` | theorem | "A response interface is an explicit relation that a system can always serve. |
| `«thm:complete-cap-response»` | theorem | **Theorem `thm:complete-cap-response` (Complete CAP with chosen responses).** "For an ordered relational specification `S` and a uniform obligation `Q`, the… |
| `«thm:complete-cap-response/proof-sufficiency»` | theorem | Proof of Theorem `thm:complete-cap-response`, (2⇒1): |
| `«app:cap-response/without-replication»` | theorem | **Remark "Without replication"**: |
| `«app:cap-response/without-replication/local-init-needed»` | theorem | The `LocalInit` hypothesis ("each strategy depends on the initial inputs only through its own participant's") is needed: |
| `«app:cap-response/lm-implies-response-form»` | theorem | "Theorem `thm:complete-cap` with `E = S` requires every permitted output to stay available; Theorem `thm:complete-cap-response` lets the system choose which… |
| `«app:cap-response/converse-fails»` | theorem | "The converse fails. |
| `«app:cap-response/functional-coincide»` | theorem | "For a functional specification the two coincide: |
| `«app:cap-response/lm-subspec»` | theorem | "A total `T ⊆ Q` that satisfies Lifted Monotonicity as a specification is a response interface for which `S` satisfies Lifted Monotonicity". |
| `«app:cap-response/subspec-weaker»` | theorem | "… but the condition is weaker." The five-input example: |
| `«app:cap-response/subspec-seals»` | theorem | "Reconciling outputs need not lie in `T`: |
| `«lem:forced-answer»` | theorem | **Lemma `lem:forced-answer` (Forced answer).** "Let `i ⪯ j`, and suppose no output in `Q_q(i)` has a refinement in `S(j)`. |
| `«app:cap-response/register-fiber»` | theorem | "The fiber `S(h)` contains the maps explained by some linearization of `h`, a total order of its operations extending precedence in which each answered read… |
| `«app:cap-response/register-obligation-def»` | theorem | "The obligation `Q_p(h)` consists of the maps in `S(h)` that answer every read and acknowledge every write invoked at `p`." |
| `«app:cap-response/register-obligation»` | theorem | "Every finite history has a linearization, so `Q_p` is total, and it is upward closed within fibers." Lean: |
| `«app:cap-response/interleaving»` | theorem | "an *interleaving* `λ` of a distributed history is a linear order of its events consistent with happens-before". |
| `«app:cap-response/realized-history»` | theorem | "For a prefix `C` of `λ` (a consistent cut), the *realized history* `h_C` contains the operations invoked in `C`, with an edge from `a` to `b` when `a`'s res… |
| `«app:cap-response/realized-mono»` | theorem | "If `C' ⊆ C` is also a prefix, `h_C` expands `h_{C'}`." |
| `«app:cap-response/realized-not-expansion»` | theorem | "The realized history need not be a common expansion of the participants' current inputs: |
| `«app:cap-response/client-history»` | theorem | "A *client history* has two participants with empty initial inputs, and each of its input events adds one operation, invoked at its participant after all of… |
| `«cor:gilbert-lynch»` | theorem | **Corollary `cor:gilbert-lynch` (Gilbert–Lynch).** "No system for the linearizable register has Answering for `(Q_p)` together with the following, both requi… |
| `«cor:gilbert-lynch/hypotheses»` | theorem | The two hypotheses of Corollary `cor:gilbert-lynch`, unfolded; Answering at the end of client histories is equivalent to its cut form `AnsweringC` (cuts of c… |
| `«cor:gilbert-lynch/via-forced-answer»` | theorem | Proof of Corollary `cor:gilbert-lynch`, along the paper's route through Lemma `lem:forced-answer` (here with the hypotheses required of all histories, not on… |
| `«cor:gilbert-lynch/also-excludes»` | theorem | "A system with Response Availability, and with a common refinement at `h_C` for every prefix `C` of every partitioned history, satisfies these hypotheses, so… |
| `«cor:gilbert-lynch/not-relMono»` | theorem | (Section `sec:complete-cap`, repeated here for reference.) "a single emitted output has no refinement in the fiber at some expansion of its input, a failure… |
| `«prop:gl-async/available»` | theorem | Prop. |
| `«prop:gl-async/atomic»` | theorem | Prop. |
| `«prop:gl-async»` | theorem | **Proposition `prop:gl-async` (Gilbert–Lynch, asynchronous model).** "In the asynchronous network model with at least two nodes, no algorithm for a read/writ… |
| `«prop:gl-async/proof»` | theorem | Proof sketch of Prop. |
| `«prop:gl-async/atomic-view»` | theorem | Proof sketch of Prop. |
| `«prop:gl-async/non-vacuity»` | theorem | Non-vacuity (not a claim of the paper): |

### Appendix G: 2PL and MVTO

File `Paper/AppG_TransactionBases.lean`; paper source `appendices/commitment-bases.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«app:cc-bases/input»` | abbrev | "An input is a finite set of transactions, each given by the sequence of operations that its client has issued so far: |
| `«app:cc-bases/input-order»` | theorem | "One input precedes another when every transaction of the first is in the second and its sequence in the first is a prefix of its sequence in the second; onc… |
| `«app:cc-bases/output»` | abbrev | "An output has three parts: |
| `«app:cc-bases/output-order»` | theorem | "One output refines another when it extends all three parts …" `(L,X,ρ) ⪯ (L',X',ρ') ⟺ X ⊆ X', dom L ⊆ dom L', L'\|_{dom L} = L, ρ ⊆ ρ'`. |
| `«app:cc-bases/complete-output»` | theorem | "An output is *complete* at an input when it commits or aborts every transaction of the input, and not both, and commits only transactions whose commit reque… |
| `«app:cc-bases/read-rule»` | theorem | "… each read of a key `x` by a committed transaction `T` returns `T`'s own write of `x` if `T` writes `x` earlier in its sequence, and otherwise the write of… |
| `«app:cc-bases/complete»` | theorem | "A complete output is permitted when each reported read result is for a read in the input and returns the initial version or the write of its key by a transa… |
| `«app:cc-bases/permitted»` | theorem | "Any output is permitted when some permitted complete output refines it, that is, when it can still be completed." |
| `«app:cc-bases/spec»` | abbrev | The specification. |
| `«app:cc-bases/figure-rows»` | theorem | "The figures … show only complete outputs without aborts or read results, as serial orders, at inputs in which every transaction has requested commit": |
| `«app:cc-bases/total»` | theorem | "Every input has a permitted row: |
| `«app:cc-bases/ab-ba-not-monotone»` | theorem | "Let `{A,B}` be an input in which `A` and `B` have each requested commit. |
| `«app:cc-bases/abort-free-spec»` | theorem | "The *abort-free* specification permits a row when it can be completed with `X = ∅`, where a complete output now commits exactly the transactions whose commi… |
| `«app:cc-bases/abort-free-not-monotone»` | theorem | "… the same two rows show that it is not monotone either." |
| `«app:cc-bases/applied»` | theorem | "Applied at a state `(i,R)`, it keeps the rows of `R` that can still be completed, within `R`, by a complete row satisfying the condition, and removes the rest. |
| `«app:cc-bases/conditions»` | theorem | The four conditions. |
| `«app:cc-bases/order»` | abbrev | `order(A,B)`, for distinct `A,B ∈ i`. |
| `«app:cc-bases/commit»` | abbrev | `TxCommit(A)`, for `A` whose commit request is in `i`. |
| `«app:cc-bases/abort»` | abbrev | `abort(A)`, for `A ∈ i`. |
| `«app:cc-bases/stamp»` | abbrev | `stamp(A)`, for `A ∈ i ∖ Z`, `Z ⊆ i`. |
| `«app:cc-bases/read»` | abbrev | `read(A,k,v)`, for `A ∈ i` whose `k`-th operation in `i` is a read. |
| `«app:cc-bases/each-is-commitment»` | theorem | "Each is a commitment (Definition `def:commitment`). |
| `«app:cc-bases/complete-kept-iff»` | theorem | "… for them a complete row is kept exactly when it satisfies the condition, since two permitted complete outputs at one input, one refining the other, have t… |
| `«app:cc-bases/bases»` | theorem | "The bases are `B_2PL = {order, TxCommit, abort, read}` and `B_MVTO = {stamp, TxCommit, abort, read}`, over all transactions, positions, and versions." |
| `«app:cc-bases/bases-differ»` | theorem | "… and differ in how they order. |
| `«app:cc-bases/run-states»` | theorem | "In every state that a run under either basis reaches, each row has a complete refinement in the table at its input, and any output between two rows of the t… |
| `«app:cc-bases/read-emit»` | theorem | "So a read is reported by applying `read(A,k,v)` and then emitting the result, which is then exposable." Precisely: |
| `«app:cc-bases/fig-h»` | theorem | "If `A` holds that lock in a conflicting mode, `B` waits, and the scheduler applies `order(A,B)` in a commitment event, reporting nothing. |
| `«app:cc-bases/order-at-ABC»` | theorem | "At the canonical state of `{A,B,C}` it removes `[B,A,C]` and keeps `[A,B,C]` and `[C,A,B]`, so it is a choice, and it is not the choice `c_o` of any output… |
| `«app:cc-bases/deadlock»` | theorem | "A deadlock between `A` and `B` arises when `B` waits for a lock that `A` holds and an operation of `A` then waits for a lock that `B` holds: |
| `«app:cc-bases/deadlock-resolution»` | theorem | "Once the scheduler applies `TxCommit(A)`, every remaining complete row aborts `B`, and `TxCommit(B)` is never again defined." |
| `«app:cc-bases/abort-free-waits-forever»` | theorem | "Under the abort-free specification, once both orderings have been applied, no remaining row is at an input in which both `A` and `B` have requested commit. |
| `«app:cc-bases/fig-i»` | theorem | "On complete rows without aborts, `stamp(B)` with `Z = ∅` keeps exactly those with `B` first (Figure `fig:cc-commitments`(i))." |
| `«app:cc-bases/stamp-at-ABC»` | theorem | "… at the canonical state of `{A,B,C}` it is a choice, and it is not the choice `c_o` of any output": |
| `«app:cc-bases/mvto-row»` | theorem | *What a read is a commitment to*, the row argument: |
| `«app:cc-bases/read-commits»` | theorem | "Hence, after the two stamps, no row that reports the read and is at an input in which `A` writes `x` commits both `A` and `B`. |
| `«app:cc-bases/writer-before-A»` | theorem | "The condition on the version is needed. |
| `«app:cc-bases/abort-entailed»` | theorem | *When the abort is entailed.* "Suppose `A`'s write of `x` has arrived. |
| `«app:cc-bases/abort-is-a-choice»` | theorem | "While `B` is undecided, it does not. |
| `«app:cc-bases/comparison»` | theorem | "Under MVTO, a later transaction's read of an older version is a commitment that, if the writer writes that key, the writer and the reader do not both commit. |

### Appendix H: Additional applications

File `Paper/AppH_Applications.lean`; paper source `appendices/additional-applications.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«app:additional-applications/authority-output»` | abbrev | "An output is a triple `(E,V,D)`: |
| `«eq:authority-refinement»` | theorem | Eq. |
| `«app:additional-applications/safety-exposable»` | theorem | "Protocol safety guarantees that every output permitted at the current or any later input [refines] the certified evidence already emitted, so authority chan… |
| `«app:additional-applications/slot-conflict»` | theorem | "Competing proposals for an undecided slot have incompatible extensions of `D`, so certifying one is a commitment." Two current outputs deciding different va… |
| `«app:additional-applications/epoch-conflict»` | theorem | "If the succession rule were not fixed, competing next epochs would require one [a commitment] as well." Two current outputs extending the chain `e` by diffe… |
| `«app:additional-applications/kset-input»` | abbrev | "An input is a finite set of proposals `(p,v)`, at most one per participant, ordered by inclusion." |
| `«app:additional-applications/pmap-order»` | theorem | "Outputs are partial decision maps `m : |
| `«app:additional-applications/kset-permitted»` | theorem | "At input `I`, `m` is permitted when it decides only participants that propose in `I`, every value in its range is proposed in `I` (validity), and its range… |
| `«app:additional-applications/kset-proposal-row»` | theorem | "At `p_r`'s proposal input, `{p_r ↦ v_r}` is permitted" (`k ≥ 1`). |
| `«app:additional-applications/kset-union»` | theorem | "… and the union of the proposal inputs is a common [expansion]" (an input because the `p_r` are distinct). |
| `«app:additional-applications/kset-any-k»` | theorem | "Any `k` of these `k+1` rows have a common [refinement] there": |
| `«app:additional-applications/kset-all-fail»` | theorem | "… all `k+1` do not, since it would have `k+1` values." |
| `«app:additional-applications/kset-not-monotone»` | theorem | "So the common-[expansion] condition fails and the specification is not monotone (Proposition `prop:common-expansion-form`); a partition separating the `p_r`… |
| `«app:additional-applications/consensus»` | theorem | "Consensus is `k = 1`": |
| `«eq:tight-renaming»` | theorem | Eq. |
| `«app:additional-applications/renaming-singletons»` | theorem | "At `{p}` the only output is `p ↦ 1`, and at `{q}` it is `q ↦ 1`." |
| `«app:additional-applications/renaming-each-extends»` | theorem | "Each has a [refinement] at `{p,q}`, so Relational Monotonicity does not fail here, but no injective map extends both." |
| `«app:additional-applications/renaming-not-monotone»` | theorem | "Directed Outputs also fails at `{p,q}`: |
| `«app:additional-applications/history-order»` | theorem | "Inputs are finite causal histories, that is, finite sets of events with a causal partial order; `h ⊑ h'` when `h` is a downward-closed subset of `h'` carryi… |
| `«app:additional-applications/prefix-spec»` | theorem | "The *prefix* specification permits at `h` any downward-closed subset of `h`, with outputs ordered by inclusion." |
| `«app:additional-applications/prefix-monotone»` | theorem | "Old prefixes stay legal as history grows, and finite unions of prefixes are prefixes, so it satisfies Lifted Monotonicity." |
| `«app:additional-applications/prefix-empty»` | theorem | "… it guarantees neither freshness nor completeness": |
| `«app:additional-applications/complete-history»` | theorem | "A specification that requires the complete history, with output `h` at `h` and outputs ordered by equality, is functional and not monotone: |
| `«app:additional-applications/complete-history-seal»` | theorem | "By Proposition `prop:functional-exposure-boundary`, some output can then be exposed only after a commitment that seals larger inputs." At some state reachab… |

<!-- END PAPER INDEX -->
