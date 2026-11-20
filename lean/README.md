# Lean formalization of the paper

This directory checks the paper's definitions, results, and proved claims in
Lean 4 (core library only, no Mathlib; toolchain in `lean-toolchain`).

## How to read it alongside the paper

Start in `CoordCriterion/Paper/`.  It has one file per section and appendix,
and each file follows its section in paper order, with headers matching the
paper's subsections:

* every numbered definition, theorem, lemma, proposition, corollary, figure,
  and equation is a declaration named by its LaTeX label, for example
  `CC.Paper.«thm:complete-calm»` or `CC.Paper.«def:exclusion»`; search the
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

What is argued only in prose, not in Lean: the reading of consistency in §2 as a safety property of a spec's runs that guarantees a common state exists but not that a system reaches it, and the remark in §1 and §5 that a system omitting a required commitment can produce inconsistent runs or that a mutable replicated store's replicas can diverge without coordination; in Appendix F, Lynch's result that atomicity is a safety property (Lean takes atomicity of an infinite execution to be atomicity of each finite prefix, `«prop:gl-async/fair-executions»`); the description of the 2PL and MVTO protocols themselves (which arrival makes a lock wait, issues a timestamp, or triggers the write rule; Appendix G, where Lean checks the commitments those steps apply, when `order(A,B)` removes nothing, and the MVTO run driven by arrivals); the messaging of two-phase commit in §4.3 (prepare messages, logging, blocking; Lean checks that a prepare reports the owner's commitments, that the decision is monotone, applies no commitment, and commits exactly when every owner's commitments allow commit); that consensus is the mechanism that provides the log's commitment in §5.1 (Lean checks that some output of the log needs a commitment, `«sec:proper-coordination/locks-overhead»`); the
operational results that §6.1 cites (the transducer theorems of Ameloot et
al., Zinn et al., and Baccaert and Ketsman as statements about transducer
runs (which input order policy-aware, domain-guided and original placement
justify, and the resulting CALM variants at the level of a node's view, are
proved in Lean, `«sec:query-instance/policy-aware-order»`,
`«sec:query-instance/domain-guided-order»`,
`«sec:query-instance/placement-calm»`), and their notion of coordination; for Baccaert and Ketsman
also that they were the first to extend CALM beyond deterministic queries,
that leader election is their running example, how Ameloot et al. and they
model placement, that an identifier and an order on identifiers is what their
coordination-free transducers know, that their programs must treat data values only as interchangeable symbols (their characterization theorem itself is proved in Lean, both directions, `«sec:query-instance/characterization»`); and their aims, notion of coordination, correctness criterion, fixed inputs, and quorum construction in which a group's smallest node decides; that the necessary half of their characterization is the partition argument behind Complete CAP, run over placed histories (`«sec:query-instance/node-monotonicity»`), and that their quorum decisions are commitments (`«sec:query-instance/sufficient-half»`)); in §6.1, the opening sentences that several CALM results for deterministic queries share one form, which Functional CALM states at the level of a spec (the instances are proved, `«sec:query-instance/placement-calm»`); in §6.1, the closing sentence summarizing which choice of our model each refinement corresponds to; in §6.1, Li and Lee's CALM theorem for replicated objects and its reading as a counterpart of Functional CALM for set inputs under inclusion, with the existence of a coordination-free implementation in place of consistency; in §4 (`sec:systems`), that Ameloot et al. show a list of
all participants enlarges what a system can compute; in
Appendix B (`app:hat-taxonomy`), what the HAT papers' text says (their list of recency guarantees, the extended paper's descriptions of its algorithms, the wording, names and examples of Defs. 14, 24, 26, 28, 30, 32 and 34, and the legend of its dependency graphs, which swaps the labels of read- and anti-dependencies relative to its figures; the definitions as we read them, and the consequences of the literal readings of Defs. 26 and 34, are in Lean, `Paper/AppB_HATTaxonomy.lean`, `«sec:hat-instance/myr-as-written»`); in §6.3 (`sec:hat-instance`), the description of Kaki et al.'s program logic, its compositional proof rules and its inference procedure; in Appendix E (`app:rtc`), that Mahajan et al.'s implementations satisfy the abstract execution-level forms used in Lean (their run model with environment graphs and messages is not formalized; their check, always availability, one-way convergence and blindness to real time are, in `Appendix/MahajanRTC.lean`, and their Theorem 3.1 is derived from ours, `«app:rtc/mahajan»`); in §4.4, the signpost that the voters in the election of Section `sec:election-story` show commitments and availability coexisting when each commitment is made by a single participant, the opening that the election discussion centered on the spec for vote collection, and the remark that the voters are unaffected by a partition since each ballot is a commitment its voter makes alone (the example's facts are `«def:explicit-relation/election-voters»`, `«def:explicit-relation/election-registrar»` and `«sec:complete-cap/local-row-removal-necessary»`); in §6.5, the reading of an automaton as a server (arrival, handing a request to the computation, when a reply fires) and that a server built from several communicating automata is a distributed system; in its "Testing and proof" paragraph, that simulators and model checkers run the
automaton on bounded inputs and that the pairs of receive and reply sequences they collect form a
finite specification that can be checked for violations, that this is routine engineering practice and has
found serious bugs in production systems, that confirming a violation of an automaton's confluence means exploring the continuations of the executions involved, and the relation of the
two obligations to the verification literature (invariants, forward
simulations, refinement mappings, mechanized proofs, domination as the counterpart of refinement, realizability typically
proved by induction on the input); in Appendix D (`app:components`),
that a system's messages and partitions stay inside its component, that the
implementation form determines which internal system model and coordination
classification justify a component's admitted runs, the Hydro interface
analogy, and the list of topics left out (cyclic dataflows, scheduling,
placement, co-location, failure domains, one history across components); that reaching a common state takes an algorithm, message delivery, and a termination argument (§2.4); and the design discussion of §6–§7.  The `Paper/` docstrings point these out where
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
| `CompleteCALM/Legality.lean` | `CC` | §2–§3 | Lemma confluence-legality (runs consistent iff every output a run can emit is legal), the bridge to legality at states reachable without commitment, and Functional and Complete CALM assembled in the paper's order |
| `CompleteCALM/Cofinal.lean` | `CC` | §6.5 | Cofinality (used by Prop. declared-specification): a declared spec whose rows are rows of `T` and dominate every row of `T` (same inputs, or along an order embedding) is Lifted Monotone / consistent iff `T` is |
| `CALM/Lemmas.lean` | `CC.CALM` | §2–§3, App. B | Event facts, functional remarks, Lemma reconciliation, paper proof routes, pairs suffice |
| `CALM/Examples.lean` | `CC.CALM` | §2–§3, App. B | `k`-set agreement (pairs), rows at `j`, relational state-by-input, election, directed fiber |
| `CALM/TransientConflict.lean` | `CC.CALM.Transient` | §2 (after Def. consistency) | A conflict confined to the current input: no meeting at `i`, confluent at `j`, not consistent |
| `Figures.lean` | `CC.Figures` | §2–§3, §7 | Figure tables: election frames, ambiguity frames; decisive ballot vs. closing the polls |
| `Distributed/Histories.lean` | `CC.Dist` | §4.1–4.2 | Histories, cuts, Prop. distributed consistency, Cor. convergence, exchanging outputs |
| `Distributed/Exclusions.lean` | `CC` | §4.3–4.4, App. C | Exclusions, the canonical exclusion for an output, system output events `output(o)` (the lifted output event, whose canonical exclusion must be in the basis when `o` is not legal) and exclusion events `Exclude(γ)` (a nonempty sequence of basis exclusions applied without emitting; erased to nothing), output containment, coordination (a run that is not a run under the empty basis), canonical-equivalent (the canonical run skips exclusion events), conflicting outputs |
| `Distributed/Systems.lean` | `CC.Dist` | §4.1–4.4, App. C | Figure participant-runs, consistency without unique send ids, canonical systems, reconciliation under any basis, encodings of output and exclusion events agree |
| `Distributed/SystemConfluence.lean` | `CC.Dist` | §4.3, App. B | Prop. system-confluence: a system's table is its canonical run's table minus the rows its commitment events removed; confluence under any bases is the Survivor test on those tables, for runs and for consistent cuts; the system's own continuations; Prop. commitment-conflict as the two-run case; the registrar and server examples |
| `CAP/Model.lean` | `CC.CAP` | §4.1–4.5 | System model for Complete CAP: exclusions, histories (local events: inputs, output events `out o`, exclusion events `cmt γ`, sends, receives), cuts, systems, Availability, Partition Consistency |
| `CAP/CompleteCAP.lean` | `CC.CAP` | §4.4 | Thm. Complete CAP; deterministic strategies do not suffice |
| `CAP/FullKnowledge.lean` | `CC.CAP` | §4 | Strategies that see the participant set and all initial inputs (`KSystem`); every system is one; the necessity half of Complete CAP for an explicit relation holds for them |
| `CAP/TwoPhaseCommit.lean` | `CC.CAP` | §4.3–4.4 | Two-phase commit: vote counting over a fixed membership is monotone, consistent, and coordination-free; prepares report the owners' commitments; the voters' spec and its explicit relation (the election's voters); a majority decision, kept as library, is monotone |
| `CAP/TimeoutAbort.lean` | `CC.CAP.Timeout` | §4.3 | Two-phase commit aborting on timeout: on the vote-decision specification, closing the polls excludes every future input that adds a missing vote; run by the coordinator alone this is local coordination, replicated it is distributed; on a specification where abort remains allowed until a decision, aborting excludes the commit outputs at later inputs while keeping those inputs legal, so it is local coordination when only the coordinator decides and distributed when the decision is replicated |
| `CAP/ResponseForm.lean` | `CC.CAP` | App. F | Response Availability, Response Partition Consistency, Thm. Complete CAP (response form) |
| `CAP/Register.lean` | `CC.GL` | App. F | Linearizable register, realized histories, Cor. Gilbert–Lynch |
| `CAP/ResponseAvailability.lean` | `CC.CAP` | §4.4, App. F | Strong (2)⇒(1), RPC vs. confluence, input acceptance, Lemma locality, without replication, choosing vs. requiring every output, Lemma forced-answer, GL via forced answer |
| `CAP/AsyncGilbertLynch.lean` | `CC.AsyncGL` | App. F | Gilbert–Lynch Theorem 1 (asynchronous model) by reduction to the corollary |
| `CAP/AsyncGLFair.lean` | `CC.AsyncGL` | App. F | Fair infinite executions; every finite execution extends fairly with no new request and every message lost; Gilbert and Lynch's fair-execution availability and atomicity imply the finite forms |
| `CAP/ChosenAvailability.lean` | `CC.CAP`, `CC.AsyncGL` | App. F | End-of-history forms of Response Availability / RPC / Answering; RPC is the converse's common-refinement condition; a response interface as a chosen explicit relation; Lemma forced-answer and Cor. Gilbert–Lynch at the end of histories |
| `Instances/InvariantConfluence.lean` | `CC.IConf` | §6, App. B | Bailis et al. model; Prop. invariant confluence ⇔ LM |
| `Instances/BailisDefinition.lean` | `CC.IConf` | §6 | Bailis et al. Def. 5/6 ⇔ `IConfluent` |
| `Instances/Examples.lean` | `CC.Inst` | §5–§6, App. B, App. D | CRDTs, uniqueness example, composition examples |
| `Instances/HATRC.lean` | `CC.HATRC` | §6.3 | HAT's Read Committed algorithm (App. B pseudocode, partial replication, anti-entropy): a G1c witness with timestamps fixed at `BEGIN`; with Lamport timestamps chosen at commit every run is PL-2 |
| `Instances/HATUnion.lean` | `CC.HATUnion` | — (not cited) | Bailis's dissertation frame (histories merged by union): two read-committed histories whose union has G1c; with the Lamport condition unions never do |
| `Instances/HATSpec.lean` | `CC.HATSpec` | §6.3 | Def. hat-spec, Thm. hat-levels: event-history inputs with happens-before (optionally with the timestamp condition), read-answer outputs, HAT levels (RU, RC, SI, RR, SER; item-only); HAT's read rule as explicit relation; RU/RC available under the timestamp condition; any level proscribing Lost Update unavailable; without the condition the read rule leaves `S_RC` |
| `Instances/HATWriteSkew.lean` | `CC.HATSpec.WS` | §6.3 | Write Skew (Adya G2-item, Bailis et al. §5.2.1 and extended Def. 39) is unavailable: Bailis's `T₁ : r y w x`, `T₂ : r x w y` at two partitioned replicas; any level proscribing it (RR, SER) has no consistent explicit relation answering every read |
| `Instances/HATTaxonomy.lean` | `CC.HATTax` | §6.3 | Bailis et al.'s taxonomy, model: HAT histories with item replica sets, predicate reads, sessions; the extended paper's phenomena (IMP, PMP, OTV, N-MR, N-MW, MRWD, MYR, as written and repaired), recency; the visibility store; specs `tax g`; high and sticky availability as Availability for an explicit relation answering every (sticky) read |
| `Instances/HATTaxonomyRules.lean` | `CC.HATTax` | §6.3 | Pending-stable and dependency-stable reveal (Bailis §5.1.2–5.1.3, App. B) with per-transaction snapshots; RC, MAV, I-CI, P-CI, MR, MW, WFR highly available and RYW, PRAM, causal sticky available, via Complete CAP for an explicit relation; the sticky deployment is monotone across partitions and has a system with Deployment Availability and Partition Consistency |
| `Instances/HATTaxonomyWitness.lean` | `CC.HATTax` | §6.3 | RYW, PRAM, causal not highly available (Bailis's partitioned-replica history); recency neither highly nor sticky available; finding: MYR as the extended paper's Def. 34 writes it is not sticky available |
| `Instances/HATAppB.lean` | `CC.HATTax` | §6.3 | App. B's MAV algorithm (good/pending, GET with required timestamps, per-transaction required map) as explicit relation, for every acknowledgment schedule: MAV highly available under the timestamp condition; findings F7 (App. B fixes timestamps at BEGIN: G1c, not RC) and F5 (App. B's answers exhibit OTV as Def. 26 literally writes it); F1 in deployment form (literal MYR has no sticky deployment with Deployment Availability and Partition Consistency) |
| `Instances/QueryRefinements.lean` | `CC.QRef` | §6.1 | Domain-distinct/disjoint monotonicity as Functional CALM under restricted expansion orders; one-fact versions are weaker; behaviors over located facts, node monotonicity vs. Lifted Monotonicity, matching over located items |
| `Instances/Placement.lean` | `CC.Place` | §6.1 | Policy-aware, domain-guided and original placement at the level of a node's view: the inputs a node cannot rule out are the domain-distinct, domain-disjoint, or inclusion extensions; coordination-free computation under each iff the matching monotonicity, via Functional CALM |
| `Instances/BaccaertKetsman.lean` | `CC.BK`, `CC.CAP` | §6.1 | Baccaert and Ketsman's setting as an anonymous cluster: anonymized strategies, histories side by side, causal histories, placement (participants are nodes, inputs only held, node-closed facts), consistency on placed histories, realized rows; their Prop. 11 (necessity: realized rows are node monotone) |
| `Instances/BKTransducers.lean` | `CC.BK` | §6.1 | Baccaert and Ketsman's operational model (node programs under Id+Ord, networks, broadcast log, fair runs, quiescent output, computes/characterizes) and its translation into an anonymous cluster: computing implies consistency on placed histories (`placedConsistent_of_computes`), characterized rows are covered by placed histories (`covers_of_characterizes`), and their Prop. 11 on finite networks through our necessity theorem (`nodeMono_of_characterizes`) |
| `Instances/BKSufficiency.lean` | `CC.BK` | §6.1 | Sufficiency (their Prop. 10): a node program under Id+Ord (`qProg`: gossip records, quorums confirmed by every member, the least node decides once, decisions extend all known ones) computes and characterizes every node monotone behavior whose outputs lie at network nodes (`computes_qProg`, `characterizes_qProg`); with Prop. 11, their Thm. 5 (`bk_characterized_iff`) and its computability form with their Lemma 4 (`bk_computable_iff`) |
| `Instances/StateMachine.lean` | `CC.SM` | — | State machines and the prefix-ordered table of event sequences; arrival-order independence; the election as an induced specification (from an earlier version of §6.5; not cited by the paper) |
| `Instances/IOTrace.lean` | `CC.IOT` | §6.5 | The projection of an I/O automaton (receive and reply sequences under prefix): executions are runs; Relational Monotonicity; consistency iff reply sequences at each receive sequence are pairwise prefix-comparable; reachable rows and the narrowing commitment; the system of an automaton (soundness, completeness, catching up); confluent automata, system confluence and removed rows; a confluent automaton has a consistent projected spec; testing witness; declared specs |
| `Instances/IOTraceExamples.lean` | `CC.IOT` | §6.5 | The early-closing registrar (consistent projected spec, not confluent; a run of the projected spec no execution has); a hidden internal choice that is a commitment event; racing and recording counters; neither declared-spec obligation suffices alone; a declared rule for the recording counter |
| `Instances/TestingLimits.lean` | `CC.Testing` | §6.5 | Testing cannot show Lifted Monotonicity: for every finite set of explored inputs, two specs agree on those fibers, one Lifted Monotone and one not |
| `Appendix/Composition.lean` | `CC.Comp` | §5, App. D | Composition lemmas, independently parameterized composition, curried plan |
| `Appendix/Guarded.lean` | `CC.Guard` | §5, App. D | `Joint.Img`, `Joint.CEOn`, `Joint.restrictTo`; guarded runs, store under the empty basis, covering, invisible coordination, Proper Coordination (`𝒮₂` restricted to the outputs of `𝒮₁` needs no exclusion; pipeline runs as composite runs, confluence, where the upstream must apply an exclusion), systems with strategies, exclusion-erased replacement, pipelines, early/late locks, counterexamples, per-key store, replicated store |
| `Appendix/JointMono.lean` | `CC.Joint` | §5.1, App. D | Jointly monotone composites: filtering (capped counter), re-ordering the middle (boolean toggle, constant store; also the double complement, no longer cited in the paper), preorder/injective characterization and the no-partial-order counterexample |
| `Appendix/Components.lean` | `CC.Components` | §5, App. D | Components and typed pipelines: component implementations (basis, admitted output-annotated runs, soundness certificates, implementation-form metadata), feed witnesses, external observations, boundary safety; contract properness (= `Guard.Proper`) vs. implementation properness, with the early-lock and capped-counter counterexamples; bridges to Proper Coordination (upstream retyped at its offered outputs, empty-basis `𝒮₂\|_{𝒮₁}` admits a following run, `Guard.proper_follows`/`proper_run` for admitted runs) |
| `Appendix/ComponentSystems.lean` | `CC.Components` | §4.3–4.4, App. D | A system as one component implementation (participant runs of produced histories); process and cluster forms; the 2PC timeout exclusion, which rules out future inputs containing a late vote, as a process (coordinator alone) and as a cluster (replicated) |
| `Appendix/Deployment.lean` | `CC.Deploy` | App. E | Deployments, separability, monotone across partitions, partition compatibility, Deployment Availability |
| `Appendix/DeploymentExamples.lean` | `CC.Deploy` | App. E | Chains of emitted outputs, leader example, sole-authority sufficient condition, single-authority deployments |
| `Appendix/DeploymentSystems.lean` | `CC.Deploy` | App. E | Remark: the proposition applies to system runs |
| `Appendix/DeploymentFor.lean` | `CC.Deploy` | App. E | Deployment Availability at the end of histories; uniform deployment is Availability for `E`; Lifted Monotonicity for `E` implies monotone across partitions; single authority: exclusions that remove competing outputs while keeping their inputs legal need not require distributed coordination |
| `Appendix/DeploymentCAP.lean` | `CC.Deploy` | App. E | Existence half of Prop. complete-cap-deployment: with two or more participants, monotone across partitions makes every authorized family compatible, and the deployment's canonical system has Deployment Availability and Partition Consistency; necessity for authorized rows (`authorized_reconciled`) |
| `Appendix/TransactionBases/NoReads.lean` | `CC.Txn` | §4.3, App. C | Complete `(L,X)` outcomes, finite sets, filter exclusions on antichain fibers (used by Fig. cc-exclusions in §4.3 and App. C) |
| `Appendix/TransactionBases/Spec.lean` | `CC.Txn.Partial` | App. G | The specification: inputs are transactions with operation sequences (prefix order, frozen after the commit request); outputs `(L,X,ρ)` with reads by position; complete outputs, read rule, abort-free variant |
| `Appendix/TransactionBases/Partial.lean` | `CC.Txn.Partial` | App. G | Closure exclusions; 2PL/MVTO bases; bases differ at three transactions that requested commit; deadlock (and under abort-free: the two commit requests are never both accepted); MVTO: what a reported read commits to, when the writer's abort is entailed |
| `Appendix/TransactionBases/MVTO.lean` | `CC.Txn.Partial` | App. G | MVTO's eager abort as a run driven by operation arrivals: stamps, the read report, the write arrival, the exclusion event `apply(abort(A))` removes the commit-`A` completions while keeping the same inputs legal, and the abort becomes exposable after `TxCommit(B)`; the version condition is needed |
| `Appendix/TransactionBases/CommitEvent.lean` | `CC.Txn.Partial.CommitEx` | §4.3 | 2PL exclusion event `Exclude([order(A,B)])` when `B` waits for `A`'s lock, at three transactions that requested commit, then `[A,C,B]`; lockstep with the canonical run, same final state |
| `Appendix/Frontiers.lean` | `CC.Front` | §3 (Hoare remark); otherwise not in paper | Hoare preorder vs. the joint refinement lift; remembered-output hull, Table lookup-lift, Hoare quotient, persistent forwarding |
| `Appendix/ProductFrontier.lean` | `CC.Deploy` | App. E (real-time causal) | Thm. independent products (`thm:product-frontier`), configuration example |
| `Appendix/Graphs.lean` | `CC.Graph` | not in paper | Products, tee vs. running twice, merge, partition; stage expressions with per-node offered-domain test; Proper Coordination for products; parameterized composition as a product |
| `Appendix/Registers.lean` | `CC.Deploy` | App. E (registers) | Causal and linearizable registers, two-write history, causal-register frontier |
| `Appendix/RealTimeCausal.lean` | `CC.Deploy` | App. E (real-time causal) | Histories with real-time precedence, real-time causal views, their product interface, forcing, maximality for real-time blind strengthenings |
| `Appendix/MahajanRTC.lean` | `CC.Deploy` | App. E (real-time causal) | Mahajan et al.'s RTC check for one replica's reads is the real-time causal views (single-source writeLists; one element of a set-valued writeList is not enough); always availability as totality plus Deployment Availability; one-way convergence from delivery in the input; implementations that do not observe real time induce real-time blind strengthenings; their Theorem 3.1 derived from Prop. rtc-maximal and Thm. independent products (2), realized in any system with Deployment Availability |
| `Appendix/RealTimeTies.lean` | `CC.Deploy.Tie` | App. E | A strict strengthening of the real-time causal product interface that reads real time to break ties is monotone across partitions under its owner deployment, so real-time blindness is needed |
| `Appendix/Applications.lean` | `CC.Apps` | App. H | Committed authority, `k`-set agreement, tight renaming, snapshots |

`ProductFrontier`, `Registers`, `RealTimeCausal`, and `MahajanRTC` are in `CC.Deploy` because they are stated
in terms of the deployment notions of `Appendix/Deployment.lean`.

## Paper index

<!-- BEGIN PAPER INDEX -->

701 entries.

### §2 Functional CALM

File `Paper/S2_FunctionalCALM.lean`; paper source `sections/functional-calm.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«sec:election-story/input-order»` | theorem | "The *input order* records accumulated ballots: |
| `«sec:election-story/output-order»` | theorem | "The *output order* says which announcements are safe to build on: |
| `«sec:election-story/monotone»` | theorem | "The functional table is *monotone* … Here, for example, the input sequence `a·· ⪯ ab· ⪯ aba` monotonically produces the output sequence `⊥ ⪯ ⊥ ⪯ a`." The el… |
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
| `«sec:election-story/equality-order-commitment»` | theorem | §2.1: |
| `«sec:election-story/obstruction»` | theorem | §2.1: |
| `«sec:election-story/not-reconciled»` | theorem | §2.1: |
| `«sec:election-story/consistency»` | theorem | §2.1: |
| `«def:functional-specification»` | abbrev | **Def. |
| `«def:functional-specification/induced-function»` | theorem | "The unique output paired with `i` induces the function `f : |
| `«def:functional-monotonicity»` | abbrev | **Def. |
| `«eq:functional-monotonicity»` | abbrev | **Eq. |
| `«def:functional-monotonicity/via-f»` | theorem | Def. |
| `«def:residual-state»` | abbrev | **Def. |
| `«def:legal-input»` | abbrev | **Def. |
| `«eq:canonical-state»` | abbrev | **Eq. |
| `«eq:canonical-state/largest»` | theorem | "The *canonical state at `i`* is the state at `i` with no rows removed: |
| `«eq:canonical-state/input-moves-canonical»` | theorem | "An input event from a canonical state leads to another canonical state." |
| `«def:fiber»` | abbrev | **Def. |
| `«def:fiber/upper»` | abbrev | Def. |
| `«def:fiber/state»` | theorem | Def. |
| `«eq:input-event»` | abbrev | **Eq. |
| `«eq:input-event/legal-expands»` | theorem | The paper's input event asks for `j` legal *and* `i ≼ j`; the second follows from the first, since the remainder table contains only rows at input extensions… |
| `«sec:functional-events/input-cumulative»` | theorem | "`input(j)` then `input(k)` has the effect of `input(k)` alone; `input(i)` at `(i,R)` has no effect." |
| `«def:output-event»` | abbrev | **Def. |
| `«def:canonical-commitment-functional»` | abbrev | **Def. |
| `«eq:output-action»` | theorem | **Eq. |
| `«def:output-event/commitment-iff-excluded»` | theorem | Def. |
| `«sec:functional-events/output-ends-at-state»` | theorem | "The current row `(i,o)` remains, since `o` extends itself, so the event always ends at a specification state with current input `i`." |
| `«sec:functional-events/extra-commitments»` | theorem | "Systems may issue more commitments than an output requires, as the registrar does in Figure `fig:election-frames`(d), but such extra commitments are a syste… |
| `«def:exposable»` | abbrev | **Def. |
| `«def:exposable/no-commitment»` | theorem | Def. |
| `«def:commitment»` | abbrev | "Emitting an output can require removing rows that no remaining output covers. |
| `«eq:commitment-unsubsumed»` | theorem | **Eq. |
| `«def:commitment/functional»` | theorem | After Def. |
| `«sec:functional-events/determined»` | abbrev | §2.3 "Determination": |
| `«sec:functional-events/determined-one-element»` | theorem | "Determined": |
| `«sec:functional-events/determination-examples»` | theorem | "A spec with multiple distinct outputs can have undetermined states, as in panel (b) … An input event can achieve determination through input loss, as in pan… |
| `«sec:functional-events/stays-determined»` | theorem | "An event from a determined state always leads to another determined state with the same output: |
| `«def:specification-event»` | abbrev | **Def. |
| `«def:transition-system»` | abbrev | **Def. |
| `«def:run»` | abbrev | **Def. |
| `«def:run/reachable-without-commitment»` | abbrev | "A run is *commitment-free* when none of its output events applies a commitment. |
| `«lem:run-residual»` | theorem | **Lemma `lem:run-residual`** (Rows remaining after a run). |
| `«eq:run-residual»` | abbrev | **Eq. |
| `«lem:run-residual/example»` | theorem | Example after Lemma `lem:run-residual`: |
| `«def:confluence»` | abbrev | **Def. |
| `«def:consistency»` | abbrev | **Def. |
| `«prop:confluence»` | theorem | **Prop. |
| `«eq:reconciliation»` | abbrev | **Eq. |
| `«sec:executions/safety-of-runs»` | theorem | Before Lemma `lem:confluence-legality`: |
| `«lem:confluence-legality»` | theorem | **Lemma `lem:confluence-legality`** (Confluence and legality). |
| `«thm:functional-calm»` | theorem | **Theorem `thm:functional-calm`** (Functional CALM). |
| `«thm:functional-calm/example»` | theorem | Example after Theorem `thm:functional-calm`: |
| `«cor:state-by-input»` | theorem | **Corollary `cor:state-by-input`** (State is fixed by input). |
| `«cor:state-by-input/input-suffices»` | theorem | After Cor. |
| `«prop:functional-exposure-boundary»` | theorem | **Prop. |
| `«prop:functional-exposure-boundary/nonmonotone-excludes»` | theorem | After Prop. |
| `«eq:query-monotonicity»` | theorem | **Eq. |

### §3 Complete CALM

File `Paper/S3_CompleteCALM.lean`; paper source `sections/complete-calm.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«fig:ambiguity-frames/f»` | theorem | Fig. |
| `«fig:ambiguity-frames/g»` | theorem | Fig. |
| `«fig:ambiguity-frames/h»` | theorem | Fig. |
| `«fig:ambiguity-frames/caption»` | theorem | Fig. |
| `«sec:ambiguity-story/commitment»` | theorem | §3.1 "Commitment and directedness": |
| `«sec:ambiguity-story/three-ways»` | theorem | §3.1: |
| `«sec:ambiguity-story/transactions-fail»` | theorem | §3.1: |
| `«def:relational-specification»` | abbrev | **Def. |
| `«eq:relational-specification»` | abbrev | **Eq. |
| `«eq:fiber»` | abbrev | **Eq. |
| `«def:relational-specification/nondeterministic»` | theorem | Def. |
| `«def:nondeterministic»` | abbrev | **Def. |
| `«def:relational-monotonicity»` | abbrev | **Def. |
| `«eq:relational-monotonicity»` | theorem | **Eq. |
| `«sec:lifted-monotonicity/traceroute-relational»` | theorem | After Def. |
| `«def:relational-monotonicity/functional»` | theorem | After Def. |
| `«sec:lifted-monotonicity/compatible»` | abbrev | "For a set `F ⊆ O` of outputs, outputs `o₁,…,o_k` are *compatible in `F`* if some `u ∈ F` extends all of them." Lean: |
| `«def:fiber-directedness»` | abbrev | **Def. |
| `«def:directed-outputs»` | abbrev | Def. |
| `«def:fiber-directedness/singleton»` | theorem | After Def. |
| `«sec:lifted-monotonicity/directed-example»` | theorem | "Directedness is more permissive than a join-semilattice. |
| `«sec:lifted-monotonicity/figure-fibers»` | theorem | "A singleton fiber is trivially directed. |
| `«eq:joint-output-order»` | abbrev | **Eq. |
| `«def:lifted-monotonicity»` | abbrev | **Def. |
| `«eq:lifted-monotonicity»` | theorem | **Eq. |
| `«def:lifted-monotonicity/functional»` | theorem | After Def. |
| `«def:lifted-monotonicity/relmono-directed»` | theorem | After Def. |
| `«def:lifted-monotonicity/at-j-eq-i»` | theorem | After Def. |
| `«def:lifted-monotonicity/hoare»` | theorem | After Def. |
| `«def:lifted-monotonicity/not-reflexive»` | theorem | After Def. |
| `«sec:lifted-monotonicity/traceroute-common-extension»` | theorem | Before Def. |
| `«def:common-expansion-condition»` | abbrev | **Def. |
| `«def:common-expansion-condition/empty»` | theorem | After Def. |
| `«prop:common-expansion-form»` | theorem | **Prop. |
| `«sec:lifted-output-events/functional»` | theorem | §3.2: |
| `«sec:complete-calm-theorem/lift-unchanged»` | theorem | "Specification states, input events, runs, commitment-free runs, and consistency are defined as before. |
| `«thm:complete-calm»` | theorem | **Theorem `thm:complete-calm`** (Complete CALM). |
| `«prop:exposure-boundary»` | theorem | **Prop. |
| `«prop:exposure-boundary/common-expansion»` | theorem | Prop. |
| `«prop:exposure-boundary/functional»` | theorem | After Prop. |

### §4.1–4.3 Distributed execution

File `Paper/S4_Distributed.lean`; paper source `sections/distributed-histories.tex, sections/distributed.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«def:distributed-history»` | abbrev | **Def. |
| `«def:distributed-history/well-formed»` | abbrev | Def. |
| `«def:happens-before»` | abbrev | **Def. |
| `«def:consistent-cut»` | abbrev | **Def. |
| `«sec:histories/cut-determines-runs»` | theorem | "A consistent cut contains a prefix of each participant's history events, so by item 3 it determines one run per participant." Lean: |
| `«def:participant-run»` | abbrev | **Def. |
| `«def:endpoint»` | abbrev | **Def. |
| `«def:participant-run/is-run»` | theorem | Def. |
| `«fig:participant-runs»` | theorem | **Fig. |
| `«fig:participant-runs/general»` | theorem | The general form of Fig. |
| `«sec:distributed-consistency/continuation»` | abbrev | "A continuation of a history at a consistent cut `C` is a history `H'` that extends the history events of `C` with further history events after them." Lean: |
| `«sec:distributed-consistency/cut-confluent»` | abbrev | "Let `j` be a common input extension of the participants' current inputs at a consistent cut `C`. |
| `«sec:distributed-consistency/cut-confluent-iff-runs»` | theorem | "History events at different participants are independent, so this holds exactly when the participant runs at `C` are confluent at `j`." |
| `«def:distributed-consistency»` | abbrev | **Def. |
| `«prop:distributed-consistency»` | theorem | **Prop. |
| `«prop:distributed-consistency/literal-matching»` | theorem | Prop. |
| `«sec:distributed-consistency/lifted-monotonicity»` | theorem | "By Complete CALM, which reduces to Functional CALM with one output per input, the distributed histories of a spec are consistent exactly when the spec satis… |
| `«cor:distributed-calm»` | theorem | **Corollary `cor:distributed-calm`** (Complete CALM at consistent cuts). |
| `«sec:distributed-consistency/constructive-continuation»` | theorem | "For specs with Lifted Monotonicity, the Survivor test (Proposition `prop:confluence`) gives a row `(j,u)` that every participant's state still contains, whe… |
| `«cor:convergence»` | theorem | **Cor. |
| `«cor:convergence/relational-fails»` | theorem | After Cor. |
| `«cor:convergence/relational-fails-minimal»` | theorem | The same failure on a minimal example: |
| `«sec:distributed-consistency/message-data»` | theorem | *Message data.* "Data can influence which history events occur next at the receiver, but can never directly change the receiver's specification state, and no… |
| `«sec:distributed-consistency/sharing-outputs»` | theorem | *Message data*: |
| `«sec:systems/registrar»` | theorem | "The registrar of Section election-story is a similar example. |
| `«def:local-history»` | abbrev | **Def. |
| `«def:strategy»` | abbrev | **Def. |
| `«def:system»` | abbrev | **Def. |
| `«def:produced-history»` | abbrev | **Def. |
| `«def:system/produced»` | theorem | Def. |
| `«def:system/restrict»` | theorem | Def. |
| `«sec:systems/one-specification»` | theorem | After Def. |
| `«sec:systems/all-relation»` | theorem | After Def. |
| `«def:commitment-event»` | abbrev | **Def. |
| `«sec:systems/commitment-event-unobserved»` | theorem | After Def. |
| `«sec:systems/commitment-then-output»` | theorem | After Def. |
| `«sec:systems/output-is-canonical-event»` | theorem | Every output event of a system is the output event of §§2–3: |
| `«sec:systems/system-histories»` | theorem | Def. |
| `«sec:systems/bases-differ»` | theorem | Opener of §4.2: |
| `«fig:cc-commitments»` | theorem | Fig. |
| `«sec:systems/two-systems-two-commitments»` | theorem | "Both are commitments that leave some rows at the input." Lean, for any commitment (in particular `Txn.Partial.order`, `Txn.Partial.stamp`): |
| `«sec:systems/neither-is-canonical-commitment»` | theorem | "… and neither is the canonical commitment `x_o` of an output." At the canonical state of an input whose transactions `A`, `B`, `C` have each requested commi… |
| `«sec:systems/run-under-basis»` | abbrev | After Def. |
| `«sec:systems/canonical-equivalent»` | theorem | *Observable equivalence.* "Let `ρ` be a run of a system for a spec `𝒮`, under any commitment basis. |
| `«sec:systems/canonical-example»` | theorem | *Canonical runs suffice*, example. |
| `«sec:systems/at-most-the-rows»` | theorem | §`sec:systems`, end of *Observable equivalence*: |
| `«sec:commitment-conflict/delta»` | def | §`sec:commitment-conflict`, before Prop. |
| `«prop:system-confluence»` | theorem | **Proposition `prop:system-confluence`** (System confluence). |
| `«prop:system-confluence/survivor»` | theorem | Prop. |
| `«prop:system-confluence/cut»` | theorem | §`sec:commitment-conflict`, after Prop. |
| `«sec:commitment-conflict/registrar»` | theorem | §`sec:commitment-conflict`: |
| `«sec:commitment-conflict/own»` | theorem | §`sec:commitment-conflict`, the system's own continuations: |
| `«sec:commitment-conflict/silent-registrar»` | theorem | §`sec:commitment-conflict`: |
| `«prop:commitment-conflict/from-system-confluence»` | theorem | §`sec:commitment-conflict`, before Prop. |
| `«prop:commitment-conflict»` | theorem | **Proposition `prop:commitment-conflict`** (Commitment conflict). |
| `«prop:commitment-conflict/second-run»` | theorem | Supporting form of Prop. |
| `«prop:commitment-conflict/canonical-run»` | theorem | Supporting form: |
| `«prop:commitment-conflict/general»` | theorem | General form of Prop. |
| `«prop:commitment-conflict/reach-general»` | theorem | Prop. |
| `«prop:commitment-conflict/any-bases»` | theorem | Supporting output-only form of Prop. |
| `«prop:commitment-conflict/reach»` | theorem | Prop. |
| `«prop:commitment-conflict/any-event»` | theorem | Prop. |
| `«sec:commitment-conflict/deployments»` | theorem | §`sec:commitment-conflict`, after Prop. |
| `«sec:commitment-conflict/shared-nothing»` | theorem | Paragraph "Locks in a shared-nothing database": |
| `«sec:commitment-conflict/two-phase-commit»` | theorem | Paragraph "Locks in a shared-nothing database": |
| `«sec:commitment-conflict/two-phase-commit-detects»` | theorem | Paragraph "Locks in a shared-nothing database": |
| `«sec:commitment-conflict/two-phase-commit-prepare»` | theorem | Paragraph "Locks in a shared-nothing database": |
| `«sec:commitment-conflict/2pc-timeout-abort»` | theorem | Paragraph "Locks in a shared-nothing database": |
| `«sec:commitment-conflict/2pc-timeout-abort-local»` | theorem | A timeout before the final vote applies the nonempty poll-closing commitment. |

### §4.4 Complete CAP

File `Paper/S4_5_CompleteCAP.lean`; paper source `sections/distributed.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«sec:complete-cap/intro»` | theorem | Section `sec:complete-cap`, opening: |
| `«def:partitioned-history»` | abbrev | **Def. |
| `«def:partitioned-history/unfolded»` | theorem | Def. |
| `«def:explicit-relation»` | abbrev | **Def. |
| `«def:explicit-relation/election-voters»` | theorem | Example after Theorem `thm:complete-cap`, introduced by "Commitments and availability can still coexist when each commitment is made by a single participant,… |
| `«def:explicit-relation/election-registrar»` | theorem | Last sentence of the election-voters example: |
| `«def:emitted-rows»` | abbrev | **Def. |
| `«def:emitted-rows/availability»` | theorem | After Def. |
| `«sec:complete-cap/system»` | abbrev | Paragraph after Def. |
| `«sec:complete-cap/system-produced»` | theorem | "We consider a system …": |
| `«sec:complete-cap/environment»` | theorem | "… and an environment that may send any legal input to any participant." Lean: |
| `«def:local-continuation»` | abbrev | **Def. |
| `«def:partition-notions»` | abbrev | **Def. |
| `«def:partition-notions/for»` | abbrev | Def. |
| `«def:partition-notions/for-S»` | theorem | Def. |
| `«def:partition-notions/unfolded»` | theorem | Def. |
| `«def:partition-notions/at-cuts»` | theorem | Def. |
| `«def:partition-consistency»` | abbrev | **Def. |
| `«def:partition-consistency/unfolded»` | theorem | Def. |
| `«def:partition-consistency/at-cuts»` | theorem | Def. |
| `«sec:complete-cap/canonical-system»` | abbrev | "The *canonical system for `E`* is the system whose participants follow canonical runs and emit only outputs of `E`." Lean: |
| `«sec:complete-cap/canonical-system-canonical»` | theorem | The canonical system for `E` "follow[s] canonical runs": |
| `«def:lm-for-A»` | abbrev | **Def. |
| `«def:escapes-cap»` | abbrev | **Def. |
| `«sec:complete-cap/canonical-never-waits»` | theorem | "The canonical system's participants never wait: |
| `«sec:complete-cap/lm-for-S»` | theorem | Supporting step for `«thm:complete-cap/E-eq-P»`: |
| `«thm:complete-cap»` | theorem | **Theorem `thm:complete-cap` (Complete CAP).** "A spec escapes CAP for `E` if and only if it satisfies Lifted Monotonicity for `E`." Lean: |
| `«thm:complete-cap/E-eq-P»` | theorem | "For `E=P`, a spec escapes CAP exactly when Lifted Monotonicity holds" (first half). |
| `«cor:complete-cap-any-system»` | theorem | **Corollary `cor:complete-cap-any-system`.** "If some system for a spec has Availability for `E` and Partition Consistency, then so does the spec's canonical… |
| `«sec:complete-cap/necessity-any-system»` | theorem | Full paper: |
| `«sec:complete-cap/proof-system-commitment-free»` | theorem | "For `E=P`, … the canonical system then needs no commitment" (second half; for the canonical system itself see `«sec:complete-cap/canonical-system-commitment… |
| `«sec:complete-cap/canonical-system-commitment-free»` | theorem | "For `E=P`, a spec escapes CAP exactly when Lifted Monotonicity holds; the canonical system then needs no commitment." Lean: |
| `«sec:complete-cap/A-eq-S-no-commitment»` | theorem | Supporting operational lemma for the full-availability case. |
| `«sec:complete-cap/local-row-removal-necessary»` | theorem | Supporting example for the voters' remark in the election-voters example after Theorem `thm:complete-cap` (not quoted): |
| `«sec:complete-cap/lm-for-A-fails»` | theorem | "When Lifted Monotonicity for `E` fails, some output of `E` waits for another side, sacrificing Availability, or is emitted anyway, sacrificing Partition Con… |
| `«sec:complete-cap/deterministic-strategies»` | theorem | Precise reading (not a claim of the paper): |
| `«sec:complete-cap/gl-register»` | theorem | "Linearizability respects real-time order: |
| `«sec:complete-cap/gl-no-system»` | theorem | "By Corollary `cor:complete-cap-any-system`, no system can keep both outputs available and stay consistent across a partition, which is Gilbert and Lynch's t… |
| `«sec:complete-cap/gl-two-row-forced»` | theorem | "In this example, the proof of Corollary `cor:complete-cap-any-system` uses only weaker forms of its hypotheses, and these weaker forms are Gilbert and Lynch… |
| `«sec:complete-cap/gilbert-lynch»` | theorem | "Gilbert and Lynch's theorem is a case of Complete CAP in which Lifted Monotonicity for `E` fails. |
| `«sec:complete-cap/gl-realized»` | theorem | "In this section the real-time order of the write and the read is part of the input. |
| `«sec:complete-cap/response-form»` | theorem | "extends Complete CAP to systems that choose their responses when responses are not forced" — Theorem `thm:complete-cap-response` (see `Paper/AppF_ResponseAv… |
| `«sec:complete-cap/gl-async»` | theorem | "and derives the theorem in Gilbert and Lynch's asynchronous model" (Proposition `prop:gl-async`). |

### §5 Composition and Proper Coordination

File `Paper/S5_Composition.lean`; paper source `sections/composition.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«eq:spec-composition»` | theorem | Eq. |
| `«sec:composition/seq-total»` | theorem | "Every `i ∈ I` has a nonempty fiber in `P₂ ∘ P₁`, since `P₁` is total on `I` and `P₂` is total on `M` (it has a row at every `m ∈ M`)." Lean: |
| `«sec:composition/middle-totality-needed»` | theorem | Totality of `P₂` on *all* of `M` is needed (not stated in the paper; it explains the hypothesis above). |
| `«lem:composition»` | theorem | **Lemma `lem:composition`** (Composition): |
| `«sec:composition/associativity»` | theorem | "By associativity the lemma extends to finite pipelines." |
| `«sec:composition/function-tables»` | theorem | "For a function `f`, its table `{(i,f(i))}` satisfies Lifted Monotonicity exactly when `f` is monotone (Section `sec:lifted-monotonicity`)." Lean: |
| `«sec:proper-coordination/kvs-on-logs»` | theorem | "We return to the replicated store of the opening. |
| `«def:proper-coordination»` | theorem | **Definition `def:proper-coordination`** (Proper Coordination): |
| `«thm:proper-coordination»` | theorem | **Theorem `thm:proper-coordination`** (Proper Coordination): |
| `«sec:proper-coordination/locks-overhead»` | theorem | "This answers the opening puzzle. |
| `«sec:proper-coordination/nesting»` | theorem | "Longer pipelines nest: |
| `«sec:proper-coordination/components»` | theorem | "We call a system for one spec, seen only through its boundary, a component. |
| `«sec:composite-calm/all-monotone»` | theorem | "Composite CALM asks a stronger question: |
| `«sec:composite-calm/complete-calm»` | theorem | "The composite is itself an I/O specification. |
| `«sec:composite-calm/middle-order»` | theorem | "The orders on `I` and `O` are part of the composite's contract with its environment. |
| `«sec:composite-calm/crdt-query»` | theorem | "The CRDT observations of Section `sec:crdt-instance` have this shape. |
| `«sec:composite-calm/filtering»` | theorem | "Second, the upstream can filter out the inputs on which the downstream is not monotone. |
| `«sec:composite-calm/output-orders»` | theorem | "Under the usual boolean order, as in LVars, `false` is only a lower bound, and the test is monotone." And, from the second case: |
| `«sec:composite-calm/cancellation»` | theorem | "Third, a different order on `M` can make two non-monotone stages monotone. |
| `«prop:joint-monotone»` | theorem | **Proposition `prop:joint-monotone`** (Jointly monotone composites): |
| `«sec:composite-calm/reach»` | theorem | "The three cases do not cover every monotone composite (Appendix `app:composition`). |
| `«def:intersection»` | theorem | **Definition `def:intersection`** (Intersection): |
| `«sec:intersection/not-closed»` | theorem | "Intersection does not preserve Lifted Monotonicity. |
| `«prop:intersection-bound»` | theorem | **Proposition `prop:intersection-bound`** (Intersection under a monotone bound): |

### §6 Instances

File `Paper/S6_Instances.lean`; paper source `sections/instances.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«sec:query-instance/weaker-monotonicity»` | theorem | Sec. |
| `«sec:query-instance/policy-aware-order»` | theorem | Sec. |
| `«sec:query-instance/domain-guided-order»` | theorem | Sec. |
| `«sec:query-instance/placement-calm»` | theorem | Sec. |
| `«sec:query-instance/mapping»` | theorem | Sec. |
| `«sec:query-instance/characterization»` | theorem | Sec. |
| `«sec:query-instance/aims»` | theorem | Sec. |
| `«sec:query-instance/node-monotonicity»` | theorem | Sec. |
| `«sec:query-instance/asks-for-more»` | theorem | Sec. |
| `«sec:query-instance/matching»` | theorem | Sec. |
| `«sec:query-instance/deterministic-behaviors»` | theorem | Sec. |
| `«sec:query-instance/sufficient-half»` | theorem | Sec. |
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
| `«def:store-spec»` | theorem | **Definition `def:store-spec`** (Store specification): |
| `«thm:hat-levels»` | theorem | **Theorem `thm:hat-levels`** (HAT levels): |
| `«thm:hat-levels/answers-stable»` | theorem | Proof sketch of Thm. |
| `«thm:hat-levels/lost-update-pair»` | theorem | Proof sketch of Thm. |
| `«sec:hat-instance/rc-timestamps»` | theorem | "The timestamp condition in the theorem is required, correcting an error in the extended HAT paper. |
| `«sec:hat-instance/mav-timestamps»` | theorem | Sec. |
| `«sec:hat-instance/session-guarantees»` | theorem | Sec. |
| `«sec:hat-instance/myr-as-written»` | theorem | Sec. |
| `«sec:iconfluence-instance/model»` | abbrev | Sec. |
| `«sec:iconfluence-instance/reachable»` | abbrev | "A state is reachable when it can be derived from `s₀` by applying transactions and merging states, with every state along the way satisfying `𝓘`." Lean: |
| `«sec:iconfluence-instance/iconfluent-def»` | theorem | "`T` is invariant confluent exactly when `𝓘(s₁ ∪ s₂)` for all reachable `s₁` and `s₂`." Lean: |
| `«sec:iconfluence-instance/bailis-definition»` | theorem | "Every reachable state descends from `s₀`, so `T` is invariant confluent exactly when `𝓘(s₁ ∪ s₂)` for all reachable `s₁` and `s₂`." This is the step from Ba… |
| `«sec:iconfluence-instance/spec»` | theorem | "From an instance `(s₀, T, 𝓘)` of their model we construct a spec `𝒮_𝓘` in ours as follows. |
| `«prop:iconfluence-lm»` | theorem | **Proposition `prop:iconfluence-lm`** (Invariant confluence as Lifted Monotonicity): |
| `«sec:iconfluence-instance/uniqueness»` | theorem | The uniqueness example: |
| `«sec:iconfluence-instance/concurrency-decides»` | theorem | "Concurrency, not the transactions alone, decides the outcome: |
| `«def:projection»` | theorem | **Def. |
| `«sec:operational-models/step-by-step»` | theorem | "Followed step by step, an execution is a run of `P_M`. |
| `«prop:projection»` | theorem | **Prop. |
| `«sec:operational-models/distributing»` | theorem | "Since `P_M` is an I/O specification, the results of Section `sec:distributed-execution` apply to it as to any other spec." Lean: |
| `«sec:operational-models/registrar»` | theorem | "The converse of item (1) fails. |
| `«sec:operational-models/reachable-rows»` | theorem | "The automaton as a system": |
| `«def:automaton-system»` | abbrev | **Def. |
| `«prop:automaton-system»` | theorem | **Prop. |
| `«sec:operational-models/hidden-choice»` | theorem | "The commitment events record choices that traces do not show. |
| `«def:confluent-automaton»` | abbrev | **Def. |
| `«prop:automaton-confluence»` | theorem | **Prop. |
| `«sec:operational-models/registrar-commitment»` | theorem | "For the registrar, replying early loses every reachable row with reply sequence `xz`, so its system removes them in a commitment event. |
| `«sec:operational-models/counters»` | theorem | "A failure can also come from the projected spec itself. |
| `«sec:operational-models/testing-witness»` | theorem | "If the projected spec does not satisfy Lifted Monotonicity, two executions show it: |
| `«sec:operational-models/testing-cannot-show»` | theorem | "Testing cannot show that Lifted Monotonicity holds, since that is a claim about every input." Lean (`Testing.testing_cannot_show`): |
| `«sec:operational-models/both-halves»` | theorem | "The second approach is proof. |
| `«sec:operational-models/recording-rule»` | theorem | "Domination is the counterpart, for receive and reply sequences, of the refinement obligation above. |
| `«prop:declared-specification»` | theorem | **Prop. |

### Appendix A: Notation

File `Paper/AppA_Notation.lean`; paper source `appendices/notation.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«app:notation/functional-specification»` | abbrev | *spec* — `Spec = (I,≼,O,≼,P)`, total on `I`, one output per input; induced `f` (Def. |
| `«app:notation/expands»` | abbrev | *extends; input extension* — `i ≼ j`: |
| `«app:notation/refines»` | abbrev | *extends; output extension* — `o ≼ u`: |
| `«app:notation/common-expansion»` | abbrev | *common input extension* — an input that extends each (Sec. |
| `«app:notation/common-refinement»` | abbrev | *common output extension* — an output that extends each (Sec. |
| `«app:notation/monotone-functional»` | abbrev | *monotone (functional)* — `i ≼ j ⇒ f(i) ≼ f(j)` (Def. |
| `«app:notation/selection-in»` | abbrev | *selection* — `R[predicate on in, out]` (Sec. |
| `«app:notation/selection-out»` | abbrev | *selection* `R[out ⪰ o]` (see `«app:notation/selection-in»`). |
| `«app:notation/in»` | abbrev | *`π_in(R)`* — the inputs in `R` (Sec. |
| `«app:notation/out»` | abbrev | *`π_out(R)`* — the outputs in `R` (Sec. |
| `«app:notation/fiber»` | abbrev | *row at `k`* — a row `(k,u)` (Sec. |
| `«app:notation/upper-fiber»` | abbrev | *upper fiber* — `π_out(R[in ⪰ k])` (Def. |
| `«app:notation/state»` | abbrev | *state `(i,R)`* — current input and remainder table, every row at an input extension of `i` (Def. |
| `«app:notation/legal»` | abbrev | *legal input* — an input with a row in `R` (Def. |
| `«app:notation/canonical-state»` | abbrev | *canonical state* — `σ_P(i) = (i, P[in ⪰ i])` (Eq. |
| `«app:notation/input-event»` | abbrev | *input event* — `input(j)` keeps `R[in ⪰ j]` (Eq. |
| `«app:notation/input-loss»` | abbrev | *input loss* — the rows `input(j)` removes (Eq. |
| `«app:notation/output-event»` | abbrev | *output event* — `output(o)` keeps `R[out ⪰ o]` and emits `o` (Def. |
| `«app:notation/output-event-excludes»` | abbrev | *commitment* (§2 sense) — an output event that removes rows (Def. |
| `«app:notation/exposable»` | abbrev | *legal output* — `output(o)` applies no commitment (Def. |
| `«app:notation/determined»` | abbrev | *determined* — the upper fiber has one element; *determination* — reaching such a state (Sec. |
| `«app:notation/run»` | abbrev | *canonical run* (*run*) — finite sequence of specification events from a canonical state (Def. |
| `«app:notation/commitment-free»` | abbrev | *commitment-free* — no output event commits (Def. |
| `«app:notation/consistent»` | abbrev | *consistent runs* — every finite family of runs can reach one common state at each common input extension `j` (Def. |
| `«app:notation/confluent-at»` | abbrev | *confluent at `j`* (Def. |
| `«app:notation/relational-specification»` | abbrev | *I/O specification* — `P ⊆ I × O` total on `I` (Def. |
| `«app:notation/nondeterministic»` | abbrev | *nondeterministic* — some fiber has several outputs (Def. |
| `«app:notation/relational-monotonicity»` | abbrev | *Relational Monotonicity* — every output keeps an output extension as input grows (Def. |
| `«app:notation/compatible-in»` | abbrev | *compatible in `F`* — some `u ∈ F` extends all (Def. |
| `«app:notation/directed»` | abbrev | *directed* — every (nonempty) finite subset compatible (Def. |
| `«app:notation/directed-outputs»` | abbrev | *directed fibers* — every fiber directed (Def. |
| `«app:notation/joint-lift»` | abbrev | *joint refinement lift `A ⊑ B`* — every nonempty finite `X ⊆ A` is compatible in `B` (Eq. |
| `«app:notation/lifted-monotonicity»` | abbrev | *Lifted Monotonicity* — `i ≼ j ⇒ P(i) ⊑ P(j)` (Def. |
| `«app:notation/common-expansion-condition»` | abbrev | *common-extension condition* — rows with a common input extension `j` have a common output extension in `P(j)` (Def. |
| `«app:notation/ruled-out»` | abbrev | *ruled out by `o`* — a row whose output does not extend `o` (Sec. |
| `«app:notation/Subsumed»` | abbrev | *`Subsumed_o`* — removed rows `(k,x)` for which some output at `k` extends both `x` and `o` (Eq. |
| `«app:notation/Excluded»` | abbrev | *`Excluded_o`* — every ruled-out row not in `Subsumed_o`. |
| `«app:notation/canonical-commitment»` | abbrev | *canonical commitment* — remove `Excluded_o`. |
| `«app:notation/output-subsumption»` | abbrev | *output subsumption* — remove `Subsumed_o`, not a commitment (Def. |
| `«app:notation/participant»` | abbrev | *participant* — holds a specification state (Sec. |
| `«app:notation/message»` | abbrev | *message* — `m = (j,d)`, a cumulative input `j` (or `∅`) and other data `d` (Sec. |
| `«app:notation/distributed-history»` | abbrev | *distributed history* — locally ordered input, output, send and receive events (Def. |
| `«app:notation/history-event»` | abbrev | *history event* — (Def. |
| `«app:notation/happens-before»` | abbrev | *happens-before* — closure of local orders and send-before-receive (Def. |
| `«app:notation/consistent-cut»` | abbrev | *consistent cut* — a set of history events closed under happens-before (Def. |
| `«app:notation/endpoint»` | abbrev | *participant run; endpoint* — `p`'s input, output, and commitment events at `C`; `(σ_p(C))_{p ∈ 𝒩}` (Def. |
| `«app:notation/continuation»` | abbrev | *continuation* — a history extending `C` (Sec. |
| `«app:notation/cut-confluent-at»` | abbrev | *cut confluent at `j`* — some continuation brings every participant to one state `(j,R)` (Sec. |
| `«app:notation/distributed-consistency»` | abbrev | *consistent distributed histories* — every consistent cut of every history is confluent at every common input extension (Def. |
| `«app:notation/commitment»` | abbrev | *commitment* — partial function on states removing rows, none extended by a remaining row at the same input (Def. |
| `«app:notation/strategy»` | abbrev | *local history; strategy* — `p`'s history events in order; `θ_p(λ)`, the output, commitment, and send events `p` may perform next (Def. |
| `«app:notation/system»` | abbrev | *system* — a commitment basis `𝓑` and a strategy per participant (Def. |
| `«app:notation/basis»` | abbrev | *commitment basis* (Def. |
| `«app:notation/produced»` | abbrev | *history of a system* — every event other than an input or receive permitted by its strategy and using only commitments from `𝓑` (Defs. |
| `«app:notation/commitment-event»` | abbrev | *commitment event `apply(γ)`* — applies a nonempty sequence `γ` of commitments, emits nothing (Def. |
| `«app:notation/run-under-basis»` | abbrev | *commitment basis; run under a basis* — a set `ℬ` of commitments; input, output, and commitment events whose commitments, including each non-legal output's `… |
| `«app:notation/canonical-run»` | abbrev | *canonical run* — a run (Def. |
| `«app:notation/observably-equivalent»` | abbrev | *observably equivalent* — same input and output events, commitment events erased; every run has a canonical one (Lem. |
| `«app:notation/delta»` | def | *`Δ(ρ)`* — rows of the final table of `ρ`'s canonical run that a commitment event of `ρ` removed; `ρ` keeps the rest (Prop. |
| `«app:notation/partitioned-history»` | abbrev | *partitioned history* — participants divided into two or more sides, no message crosses sides (Def. |
| `«app:notation/side»` | abbrev | *side* — one of the two or more classes into which a partitioned history divides the participants (Def. |
| `«app:notation/explicit-relation»` | abbrev | *explicit possibility relation `E`* — `E ⊆ P`, the rows whose outputs participants actually emit (Def. |
| `«app:notation/same-side-continuation»` | abbrev | *same-side continuation for `p`* — extends a partitioned history with events on `p`'s side alone, with no new input and no message from another side (Def. |
| `«app:notation/availability»` | abbrev | *Availability for `E`* — each output of `R(i) ∩ E(i)` emittable in a same-side continuation (Def. |
| `«app:notation/canonical-system»` | abbrev | *canonical system for `E`* — participants follow canonical runs and emit only outputs of `E` (Section `sec:complete-cap`). |
| `«app:notation/lm-for-A»` | abbrev | *Lifted Monotonicity for `E`* — every finite set of rows of `E` with a common input extension `j` has a common output extension in `P(j)` (Def. |
| `«app:notation/escapes-cap»` | abbrev | *escapes CAP for `E`* — the canonical system for `E` has Availability for `E` and Partition Consistency (Def. |
| `«app:notation/deployment»` | abbrev | *deployment* — one explicit relation `E_p` per participant (Def. |
| `«app:notation/partition-consistency»` | abbrev | *Partition Consistency* — final cuts of partitioned histories confluent (Def. |
| `«app:notation/response-obligation»` | abbrev | *response obligation* — per participant, the outputs that count as answers; upward closed within fibers (Def. |
| `«app:notation/response-interface»` | abbrev | *response interface* — a total, self-continuing explicit relation `T ⊆ Q` (Def. |

### Appendix B: Deferred Proofs

File `Paper/AppB_Proofs.lean`; paper source `appendices/proof-machinery.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«proof:lem:run-residual»` | theorem | Proof of Lemma `lem:run-residual`: |
| `«proof:prop:confluence»` | theorem | Proof of Prop. |
| `«proof:lem:confluence-legality»` | theorem | Proof of Lemma `lem:confluence-legality`. |
| `«proof:cor:state-by-input»` | theorem | Proof of Cor. |
| `«proof:prop:functional-exposure-boundary»` | theorem | Proof of Prop. |
| `«proof:thm:functional-calm»` | theorem | Proof of Thm. |
| `«proof:prop:common-expansion-form»` | theorem | Proof of Prop. |
| `«lem:reconciliation»` | theorem | **Lemma `lem:reconciliation`** (Reconciliation). |
| `«lem:reconciliation/consistency-over-runs»` | theorem | Lemma `lem:reconciliation` quantifies over runs with their events; Def. |
| `«proof:prop:exposure-boundary/only-if»` | theorem | Proof of Prop. |
| `«proof:prop:exposure-boundary»` | theorem | Proof of Prop. |
| `«proof:thm:complete-calm»` | theorem | Proof of Thm. |
| `«app:pairs-suffice»` | theorem | `app:pairs-suffice`: |
| `«app:pairs-suffice/rows-at-j»` | theorem | `app:pairs-suffice`: |
| `«app:pairs-suffice/k-at-a-time»` | theorem | `app:pairs-suffice`: |
| `«app:pairs-suffice/k-set-not-monotone»` | theorem | Consequence for `app:pairs-suffice`: |

### Appendix B: Deferred Proofs for §4

File `Paper/AppB_ProofsDistributed.lean`; paper source `appendices/proof-machinery.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«proof:prop:distributed-consistency»` | theorem | Proof of Prop. |
| `«app:exchanging-outputs»` | theorem | *Exchanging outputs* (table level). |
| `«app:exchanging-outputs/cut»` | theorem | *Exchanging outputs* (history level). |
| `«app:exchanging-outputs/honored-table-not-state»` | theorem | *Exchanging outputs.* "This restriction is a table, not a specification state: |
| `«proof:prop:system-confluence»` | theorem | Proof of Prop. |
| `«proof:prop:commitment-conflict»` | theorem | Proof of Prop. |
| `«thm:complete-cap/proof-sufficiency»` | theorem | Proof of Theorem `thm:complete-cap`: |
| `«thm:complete-cap/proof-necessity»` | theorem | Proof of Theorem `thm:complete-cap`, converse: |
| `«cor:complete-cap-any-system/proof»` | theorem | Proof of Corollary `cor:complete-cap-any-system`: |

### Appendix B: Invariant confluence

File `Paper/AppB_InvariantConfluence.lean`; paper source `appendices/proof-machinery.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«app:iconfluence/history»` | abbrev | "A transaction history `h` … is a finite partial order of transaction events, each labeled by a transaction in `T`. |
| `«app:iconfluence/expansion-order»` | theorem | "History `h'` extends `h` when `h` is a closed sub-history of `h'`. |
| `«app:iconfluence/eval»` | theorem | "The state of a history is computed event by event. |
| `«app:iconfluence/sub-keeps-pre-post»` | theorem | "A closed sub-history keeps each event's predecessors, so it also keeps each event's `pre` and `post`." |
| `«app:iconfluence/eval-union»` | theorem | "Hence the state of a union of closed sub-histories is the union of their states." Lean: |
| `«app:iconfluence/pre-post-as-eval»` | theorem | "Because `h` is a partial order and transactions are inflationary (`t(s) ⊇ s`), `pre(e)` is the state of the sub-history strictly below `e`, and `post(e)` is… |
| `«app:iconfluence/valid-def»` | theorem | "A history is locally valid when every `pre(e)` and `post(e)` satisfies `𝓘` … A history is valid when the state of each of its closed sub-histories satisfies… |
| `«app:iconfluence/valid-locally-valid»` | theorem | (Used in the proof) A valid history is locally valid, since `pre(e)` and `post(e)` are states of closed sub-histories. |
| `«app:iconfluence/inputs-closed»` | theorem | "The spec `𝒮_𝓘` has the locally valid histories as inputs; a closed sub-history of a locally valid history is locally valid, so the inputs are closed under t… |
| `«app:iconfluence/spec»` | theorem | "An output is a state, and `u` covers `s` when `s ⊆ u`. |
| `«app:iconfluence/total»` | theorem | "Taking `g` empty gives `s₀`, so the spec is total." |
| `«app:iconfluence/proof-common-expansion-form»` | theorem | "We use the common-extension form of Lifted Monotonicity (Prop. |
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

### Appendix B: The HAT taxonomy

File `Paper/AppB_HATTaxonomy.lean`; paper source `appendices/proof-machinery.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«app:hat-taxonomy/inputs»` | abbrev | Opening paragraph: |
| `«app:hat-taxonomy/guarantees»` | theorem | Paragraph "Guarantees": |
| `«def:hat-availability»` | theorem | **Definition `def:hat-availability`** (Guarantee spec, high availability, sticky read, sticky availability). |
| `«app:hat-taxonomy/complete-cap»` | theorem | "Sticky availability follows Bailis et al.: |
| `«app:hat-taxonomy/reveal-rules»` | theorem | Paragraph "Reveal rules": |
| `«thm:hat-taxonomy»` | theorem | **Theorem `thm:hat-taxonomy`** (HAT taxonomy). |
| `«thm:hat-taxonomy/proof-ha»` | theorem | Proof of Theorem `thm:hat-taxonomy`, item (1): |
| `«thm:hat-taxonomy/proof-sticky»` | theorem | Proof of Theorem `thm:hat-taxonomy`, item (2): |
| `«thm:hat-taxonomy/proof-unavailable»` | theorem | Proof of Theorem `thm:hat-taxonomy`, item (3): |
| `«app:hat-taxonomy/mav-algorithm»` | theorem | Paragraph "The algorithm for monotonic atomic view": |
| `«prop:hat-mav-algorithm»` | theorem | **Proposition `prop:hat-mav-algorithm`** (The algorithm provides monotonic atomic view). |
| `«app:hat-taxonomy/form-choices»` | theorem | Paragraph "Differences in form": |
| `«app:hat-taxonomy/pmp-for-some»` | theorem | Predicate cut isolation, read "for some": |
| `«app:hat-taxonomy/otv-literal»` | theorem | Monotonic atomic view, read literally: |
| `«app:hat-taxonomy/nmr-intermediate»` | theorem | Monotonic reads across intermediate versions: |
| `«app:hat-taxonomy/nmw-example»` | theorem | Monotonic writes and its example: |
| `«app:hat-taxonomy/mrwd-reading»` | theorem | Writes follow reads, as we read it: |

### Appendix C: Commitment bases

File `Paper/AppC_CommitmentBases.lean`; paper source `appendices/commitment-bases-general.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«eq:output-subsumptions»` | abbrev | **Eq. |
| `«eq:commitment-removals»` | abbrev | **Eq. |
| `«def:lifted-output-event»` | abbrev | **Def. |
| `«def:canonical-commitment»` | abbrev | **Def. |
| `«eq:canonical-commitment-relational»` | theorem | **Eq. |
| `«def:lifted-output-event/examples»` | theorem | "In Figure `fig:ambiguity-frames`(f), emitting `[A,B]` places the row for `[B,A]` in `Excluded_o` … In panel (g), the removed route sets, at both inputs, are… |
| `«app:lifted-output-events/disjoint»` | theorem | `Subsumed_o` and `Excluded_o` are disjoint. |
| `«app:lifted-output-events/functional»` | theorem | With one row per input, no ruled-out row is subsumed. |
| `«app:lifted-output-events/exposable»` | theorem | A legal output applies no commitment exactly when `Excluded_o` is empty. |
| `«prop:exposability»` | theorem | **Prop. |
| `«eq:safe-exposure»` | abbrev | **Eq. |
| `«def:canonical-commitment-basis»` | abbrev | **Def. |
| `«eq:canonical-commitment-basis-relational»` | theorem | **Eq. |
| `«app:bases/canonical-event-effect»` | theorem | Supporting fact for Def. |
| `«app:bases/canonical-commitment-is-commitment»` | theorem | The canonical commitment is defined precisely when the output is in the current fiber and `Excluded_o` is nonempty. |
| `«lem:canonical-equivalent/output-case»` | theorem | Supporting fact for the output case of the proof of Lemma `lem:canonical-equivalent`: |
| `«app:bases/output-event-effect»` | theorem | Supporting facts for Def. |
| `«app:bases/canonical-system»` | abbrev | Supporting notion for the appendix on `app:bases` and Appendix `app:cap-response`: |
| `«app:bases/canonical-system/histories»` | theorem | Supporting fact: |
| `«app:bases/canonical-system/no-commitment-event»` | theorem | Supporting fact: |
| `«app:bases/composite-commitment»` | abbrev | Supporting form of Def. |
| `«app:bases/composite-commitment-defined»` | theorem | Supporting form of Def. |
| `«def:run-under-basis»` | abbrev | **Def. |
| `«def:run-under-basis/canonical-run»` | abbrev | "Canonical runs (Definition run) are exactly the runs under the canonical basis `ℬ_P` of Definition `def:canonical-commitment-basis` with no commitment event… |
| `«def:run-under-basis/canonical-runs-are-runs»` | theorem | "Canonical runs (Definition run) are exactly the runs under the canonical basis `ℬ_P` … with no commitment events": |
| `«app:bases/observably-equivalent»` | abbrev | "Call two runs observably equivalent when they start at the same canonical state and agree once commitment events are dropped: |
| `«lem:canonical-equivalent»` | theorem | **Lemma Observable Equivalence** (`lem:canonical-equivalent`). |
| `«cor:reconciliation-any-basis»` | theorem | **Cor. |
| `«app:bases/converse-fails»` | theorem | "The converse of Lemma canonical-equivalent fails: |
| `«app:bases/basis-2PL»` | abbrev | *Application-specific commitments.* "Locks and timestamps are examples: |
| `«app:bases/basis-MVTO»` | abbrev | *Application-specific commitments*: |

### Appendix D: Proofs and Details for Composition

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
| `«app:composition/all-monotone»` | theorem | "Suppose every stage satisfies Lifted Monotonicity and `𝒮₁` runs under the empty basis. |
| `«app:composition/joint-monotone»` | theorem | Proof of Proposition `prop:joint-monotone`: |
| `«app:composition/reach»` | theorem | "The reach of case (3). |
| `«app:composition/capped-counter»` | theorem | "For the capped counter of Section `sec:composite-calm`, let `𝒮₁` be the table of the function `c(n) = min(n,9)` on `(ℕ, ≤)` and `𝒮₂` the table of the test `… |
| `«app:composition/boolean-toggle»` | theorem | "For the boolean toggle, let `I`, `M`, and `O` be the booleans with `false` below `true`, and let both stages be negation. |
| `«app:composition/components-commit»` | theorem | "Let `𝒮₁` have one input `*` and possibility relation `{(*,x),(*,y)}` with `x,y` incomparable, and let `𝒮₂` be the functional spec induced by a function `f`… |
| `«app:composition/image-canon»` | theorem | "For tables `R` of `𝒮₁` and `T` of `𝒮₂` we write `R ⋈ T = {(k,x) : |
| `«app:composition/pipeline-run»` | theorem | "A run of the pipeline is a run of `𝒮₁` under `ℬ`, together with a run of `𝒮₂\|_{𝒮₁}` from `σ(m₁)`, where `m₁` is the first output of `𝒮₁`. |
| `«app:composition/store-facts»` | theorem | "The proofs below rest on three facts about a proper pipeline. |
| `«app:composition/guarded-lockstep»` | theorem | Proof of Theorem `thm:proper-coordination`(2): |
| `«app:composition/canonical-states-suffice»` | theorem | Proof of Theorem `thm:proper-coordination`(3): |
| `«app:composition/properness-needed»` | theorem | "Properness is needed in (3). |
| `«app:composition/replacement»` | theorem | "The commitment-erased replacement of a system has the empty basis and the same strategy, with its commitment events dropped." Lean: |
| `«cor:empty-store»` | theorem | **Corollary `cor:empty-store`** (Empty store): |
| `«app:composition/empty-store»` | theorem | Proof of Corollary `cor:empty-store`: |
| `«cor:pipelines»` | theorem | **Corollary `cor:pipelines`** (Pipelines): |
| `«app:composition/pipelines»` | theorem | Proof of Corollary `cor:pipelines`: |
| `«app:composition/mutex-store»` | theorem | "Let `𝒮₁` be the log spec of Example `ex:committed-log-composition`, under its canonical basis with a strategy that allows every event. |
| `«prop:invisible-coordination»` | theorem | **Proposition `prop:invisible-coordination`** (Invisible coordination): |
| `«app:composition/coverage»` | theorem | The covering argument: |
| `«app:composition/per-key»` | theorem | "Consider a store that answers each key from that key's commands, in log order. |
| `«app:composition/no-pushforward»` | theorem | "The image under `f` of a commitment of `𝒮₁` need not be a commitment of the composite. |
| `«app:composition/monotone-needed»` | theorem | "Monotonicity of `f` is needed. |
| `«app:composition/store-commitment»` | theorem | "Nor can a downstream stage that needs a commitment of its own delegate it upstream. |
| `«ex:committed-log-composition»` | theorem | **Example `ex:committed-log-composition`** (Replicated store), for any deterministic state machine `δ` and two distinct commands: |
| `«ex:bare-reads»` | theorem | **Example `ex:bare-reads`** (Bare reads), position-tagged responses, for any deterministic state machine `δ`, read function `rd`, and two distinct commands: |
| `«ex:bare-reads/latest-value»` | theorem | Inside Example `ex:bare-reads`: |
| `«app:intersection/bound»` | theorem | Proof of Proposition `prop:intersection-bound`: |
| `«app:intersection/example»` | theorem | "In the example of Section `sec:intersection`, both specs satisfy Lifted Monotonicity: |
| `«def:component»` | abbrev | **Definition `def:component`** (Component, admitted run). |
| `«def:implementation-form»` | abbrev | **Definition `def:implementation-form`** (Implementation form). |
| `«app:components/system-is-component»` | theorem | "A system for `𝒮` (Definition `def:system`) induces a component once we choose its boundary observations. |
| `«app:components/two-phase-commit»` | theorem | "The two-phase commit decision discussed after Proposition `prop:commitment-conflict` can take either form. |
| `«def:typed-pipeline»` | theorem | **Definition `def:typed-pipeline`** (Feed, typed pipeline, external observation). |
| `«def:proper-pipeline»` | theorem | **Definition `def:proper-pipeline`** (Contract-proper, implementation-proper). |
| `«app:components/feed-is-input»` | theorem | "The value `m` is the downstream run's initial input, so receiving it is not a commitment of `C₂`." Lean: |
| `«prop:typed-pipelines»` | theorem | **Proposition `prop:typed-pipelines`** (Typed pipelines): |
| `«app:components/follows»` | theorem | "Item (5) covers one boundary output. |

### Appendix E: Deployment

File `Paper/AppE_Deployment.lean`; paper source `appendices/deployment.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«def:deployment»` | abbrev | **Definition `def:deployment`** (Deployment, emitted rows, partition). |
| `«def:deployment/emitted-rows»` | theorem | Def. |
| `«def:deployment/partition»` | theorem | Def. |
| `«def:participant-run-family»` | abbrev | **Definition `def:participant-run-family`** (Participant run family, silent participant, separable run family). |
| `«def:deployment/family»` | theorem | Def. |
| `«def:deployment/separable»` | theorem | Def. |
| `«def:monotone-across-partitions»` | theorem | **Definition `def:monotone-across-partitions`** (Monotone across partitions). |
| `«app:deployment/lm-for-implies-mono-across»` | theorem | "If `P` satisfies Lifted Monotonicity for a relation that contains every `E_p`, it is monotone across partitions, since the emitted rows of a family are rows… |
| `«app:deployment/uniform-mono-across»` | theorem | "So Lifted Monotonicity for `E` suffices for the uniform deployment `E_p = E` …" |
| `«app:deployment/lm-implies-mono-across»` | theorem | "… and Lifted Monotonicity suffices for every deployment." |
| `«app:deployment/run-outputs-chain»` | theorem | "Rows authorized only to `p` can be emitted only by `p`'s run. |
| `«app:deployment/sole-rows-single-row»` | theorem | "So a family whose emitted rows are all authorized only to `p` is separable only when it emits a single row." Lean: |
| `«app:deployment/leader-example/setup»` | theorem | "Let `𝒩 = {p,q}`, let every fiber be `{a,b}` ordered by equality, and let `E_p = P` and `E_q = ∅`, so that `p` alone names a leader." Lean: |
| `«app:deployment/leader-example/one-output»` | theorem | "A run of `p` emits at most one distinct output …" |
| `«app:deployment/leader-example/separable-shape»` | theorem | "… and `q` never emits. |
| `«app:deployment/leader-example»` | theorem | "So `P` is monotone across partitions, yet `(i,a)` and `(i,b)` have no common output extension, and Lifted Monotonicity fails." (Any input `i` witnesses the… |
| `«app:deployment/sufficient-condition»` | theorem | "The same happens whenever two conditions hold. |
| `«app:deployment/further-examples»` | theorem | "The causal register of Appendix `app:registers` is a further example of monotonicity across partitions without Lifted Monotonicity, with no single authority… |
| `«app:deployment/further-examples/condition-fails»` | theorem | "It need not satisfy these conditions, since a set of rows lacking a common output extension may also contain rows of other participants." Witness: |
| `«app:deployment/full-deployment»` | theorem | "Suppose `\|𝒩\| ≥ 2` and `E_p = P` for every `p`. |
| `«app:deployment/full-deployment/pairs-suffice»` | theorem | The pairs-suffice step used above (Appendix `app:pairs-suffice`). |
| `«def:deployment-availability»` | theorem | **Definition `def:deployment-availability`** (Deployment Availability). |
| `«app:deployment/uniform-availability»` | theorem | "This is Availability for `E_p`, one relation per participant. |
| `«app:deployment/full-deployment-availability»` | theorem | Supporting lemma (the sentence it backed, "… and for `E_p = P` it is Availability", was removed): |
| `«app:deployment/single-authority/def»` | theorem | "A deployment is *single-authority* when `E_q = ∅` for every participant `q` but one, as in the leader example above." |
| `«app:deployment/single-authority/shape»` | theorem | "Every separable family is then one row emitted by the single authority beside a silent participant …" |
| `«app:deployment/single-authority»` | theorem | "Monotonicity across partitions then says only that each such row has an output extension at every input extension of its input." (With `\|𝒩\| ≥ 2`, so that so… |
| `«app:deployment/single-authority/not-distributed»` | theorem | "The deployment keeps the conflicting choice from being made at another participant …" Lean: |
| `«app:deployment/single-authority/coordination»` | theorem | "… It does not change the semantic conflict: |
| `«thm:complete-cap-deployment»` | theorem | **Proposition `thm:complete-cap-deployment`** (Partition compatibility under a deployment). |
| `«thm:complete-cap-deployment/proof»` | theorem | Proof of Prop. |
| `«app:deployment/system-runs/canonical»` | theorem | "The proposition concerns canonical runs and does not use Deployment Availability. |
| `«app:deployment/system-runs»` | theorem | "So if `P` is monotone across partitions, the outputs that a separable family of system runs emits in a partitioned history, as Deployment Availability permi… |
| `«lem:deployment-compatible»` | theorem | **Lemma `lem:deployment-compatible`** (Compatibility of participant run families). |
| `«app:deployment/canonical-system»` | abbrev | "The *canonical system* of a deployment is the system whose participants follow canonical runs, each participant `p` emitting any output of `E_p` at its curr… |
| `«prop:deployment-complete-cap»` | theorem | **Proposition `prop:deployment-complete-cap`** (Complete CAP for a deployment). |
| `«prop:deployment-complete-cap/proof-sufficiency»` | theorem | Proof of Prop. |
| `«prop:deployment-complete-cap/proof-necessity»` | theorem | Proof of Prop. |
| `«app:deployment/unauthorized-refinement»` | theorem | "It does not follow that the deployment authorizes any participant to emit `u`. |
| `«app:deployment/full-deployment-step»` | theorem | "With `\|𝒩\| ≥ 2` and `E_p = P` for every `p`, item (2) is Lifted Monotonicity. |
| `«app:registers/history»` | abbrev | "An input is a finite operation history `h`: |
| `«app:registers/history-order»` | theorem | "We set `h ⊑ h'` when the operations of `h` form a causally closed subset of `h'` and `→` restricted to them is the order of `h`." |
| `«app:registers/no-new-past»` | theorem | "Thus an input extension never adds an operation to the causal past of an existing one." |
| `«app:registers/source-map»` | theorem | "An output is a *source map* `ρ`: |
| `«app:registers/serialization»` | theorem | "A *serialization* for replica `p` is a total order of `p`'s operations and all writes of `h` that extends `→`. |
| `«app:registers/fibers»` | theorem | "Under causal consistency, `ρ ∈ P(h)` when each replica has a serialization explaining every read of that replica in the domain of `ρ`. |
| `«app:registers/two-write-history»` | theorem | "Participant `p` completes `w_p(x,dog)` while `q` concurrently completes `w_q(x,cat)`; … each serves a local read, `r_p` at `p` and `r_q` at `q`. |
| `«app:registers/linearizable-not-monotone-across»` | theorem | "Under linearizability, a source map that sends `r_p` to `w_q(x,cat)` needs a linearization with `w_p(x,dog)` before `w_q(x,cat)`. |
| `«app:registers/causal-two-write»` | theorem | "Under causal consistency the two replicas may serialize the concurrent writes differently, so one source map sends `r_p` to `w_q(x,cat)` and `r_q` to `w_p(x… |
| `«app:registers/causal-monotone-across»` | theorem | "More generally, consider the deployment in which each replica answers only its own reads (`E_p` holds the rows whose source map is defined only on reads of… |
| `«app:registers/serialization-extends»` | theorem | Proof step: |
| `«app:registers/linear-extension»` | theorem | Supporting fact: |
| `«app:registers/same-read-incompatible»` | theorem | "Two answers to the same read remain incompatible, but only the reading replica may emit either." The causal register is not monotone: |
| `«app:rtc/mahajan»` | theorem | "[A] system can provide real-time causal consistency, but no stronger consistency, while staying always available … and one-way convergent … We recover both… |
| `«app:rtc/mahajan-impl»` | theorem | The "no stronger consistency" part for an implementation that does not observe real time: |
| `«thm:product-frontier»` | theorem | **Theorem `thm:product-frontier`** (Independent products). |
| `«app:rtc/input»` | theorem | "Consider the histories of Appendix `app:registers` with a second strict partial order `≺`: |
| `«app:rtc/views»` | theorem | "A *real-time causal view* of replica `p` assigns to every read `r` of `p` a source `s(r)` such that (1) `s(r)` is a write visible to `r`, or `v₀` if none is… |
| `«app:rtc/mahajan-checks»` | theorem | "Intuitively, these items are Mahajan et al.'s checks for the order that `p`'s reads expose. |
| `«app:rtc/one-source»` | theorem | "Their reads return all concurrent latest writes, while ours return one. |
| `«app:rtc/monotone-across»` | theorem | "Views exist. |
| `«app:rtc/blind»` | theorem | "A strengthening is *real-time blind* when a tuple it selects at an input stays selected at the same history with fewer real-time edges, provided its views a… |
| `«prop:rtc-maximal»` | theorem | **Proposition `prop:rtc-maximal`** (Real-time causal maximality). |
| `«prop:rtc-maximal/forced»` | theorem | Proof of `prop:rtc-maximal`: |
| `«prop:rtc-maximal/locally-conservative»` | theorem | Proof of `prop:rtc-maximal`: |
| `«app:rtc/always-available»` | theorem | "Each hypothesis has a counterpart in Mahajan et al.'s theorem. |
| `«app:rtc/one-way-convergence»` | theorem | "One-way convergence needs no separate hypothesis: |
| `«app:rtc/no-real-time»` | theorem | "Real-time blindness is their assumption that an implementation does not observe real time, which their proof uses to swap the real-time order of concurrent… |
| `«app:rtc/reads-real-time»` | theorem | Last paragraph of `app:rtc`: |

### Appendix F: Response availability and Gilbert–Lynch

File `Paper/AppF_ResponseAvailability.lean`; paper source `appendices/cap-response.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«app:cap-response/emitted-rows»` | abbrev | "Emitted rows are as in Definition `def:emitted-rows`" (the pairs `(i,o)` such that it emits `o` at current input `i`). |
| `«def:response-obligation»` | abbrev | **Def. |
| `«def:response-obligation/fields»` | theorem | Def. |
| `«def:uniform-obligation»` | abbrev | **Def. |
| `«app:cap-response/trivially-available»` | theorem | "Response Availability is only as strong as `Q_p`: |
| `«def:response-availability»` | abbrev | **Def. |
| `«def:response-availability/unfolded»` | theorem | Def. |
| `«def:response-availability/at-cuts»` | theorem | Def. |
| `«def:response-availability(1)»` | theorem | Def. |
| `«def:response-availability/input-acceptance-preserves-expansion»` | theorem | "Input acceptance says that `p` never rules out an input extension of its current input." Lean, at any cut, in particular the end of the history: |
| `«def:response-availability/excludes-unavailable-expansion»` | theorem | "It excludes specs whose answers require ruling out such an input": |
| `«def:response-availability/election-equality-order»` | theorem | "… such as the election under the equality order (Figure `fig:nonmonotone-frame`)": |
| `«def:response-partition-consistency»` | theorem | **Def. |
| `«def:response-partition-consistency/converse-part»` | theorem | "Response Partition Consistency is the part of Partition Consistency that the converse of Theorem `thm:complete-cap` and Corollary `cor:complete-cap-any-syst… |
| `«def:response-partition-consistency/of-confluent»` | theorem | "Confluence at `j` implies a common output extension at `j` (Corollary `cor:reconciliation-any-basis`)." Lean, at any cut, in particular the final one. |
| `«def:response-partition-consistency/canonical»` | theorem | "The two coincide for a system with basis `ℬ_P` and no commitment events. |
| `«def:response-partition-consistency/converse-fails»` | theorem | "With other commitments the converse can fail. |
| `«app:cap-response/replicated»` | theorem | "A system is *replicated* (SPMD) when its obligation is uniform and every participant runs the same strategy, which depends only on the participant's initial… |
| `«lem:locality»` | theorem | **Lemma `lem:locality` (Locality).** "For each participant `p` in some set of participants, let `ℓ_p` be a local history that `p`'s strategy can produce from… |
| `«def:response-interface»` | theorem | **Def. |
| `«def:response-interface/lm-for-T»` | theorem | "Lifted Monotonicity for `T` is that of Definition `def:lm-for-A`, and the reconciling output may lie outside `T`." Lean: |
| `«def:response-interface/T-eq-S»` | theorem | "With `T = P` it is the common-extension condition of Proposition `prop:common-expansion-form`." |
| `«def:response-interface/confluence»` | theorem | "and by Lemma `lem:reconciliation` it is confluence of the canonical runs whose emitted rows lie in `T`." Lean: |
| `«app:cap-response/serve-interface»` | theorem | "A response interface is an explicit relation that a system can always serve. |
| `«thm:complete-cap-response»` | theorem | **Theorem `thm:complete-cap-response` (Complete CAP with chosen responses).** "For an I/O specification `P` and a uniform obligation `Q`, the following are e… |
| `«thm:complete-cap-response/proof-sufficiency»` | theorem | Proof of Theorem `thm:complete-cap-response`, (2⇒1): |
| `«app:cap-response/without-replication»` | theorem | **Remark "Without replication"**: |
| `«app:cap-response/lm-implies-response-form»` | theorem | "Theorem `thm:complete-cap` with `E = P` requires every permitted output to stay available. |
| `«app:cap-response/converse-fails»` | theorem | "The converse fails. |
| `«app:cap-response/functional-coincide»` | theorem | "For a functional spec the two coincide: |
| `«app:cap-response/lm-subspec»` | theorem | "If a total `T ⊆ Q` satisfies Lifted Monotonicity as a spec in its own right, then `T` is a response interface for which `P` satisfies Lifted Monotonicity." |
| `«app:cap-response/subspec-weaker»` | theorem | "The converse fails. |
| `«app:cap-response/subspec-empties-fibers»` | theorem | "Reconciling outputs need not lie in `T`: |
| `«lem:forced-answer»` | theorem | **Lemma `lem:forced-answer` (Forced answer).** "Let `i ⪯ j`, and suppose no output in `Q_q(i)` has an output extension in `P(j)`. |
| `«app:cap-response/register-fiber»` | theorem | "A linearization of `h` is a total order of its operations extending precedence in which each answered read returns the last preceding write, or the initial… |
| `«app:cap-response/register-obligation-def»` | theorem | "The obligation `Q_p(h)` consists of the maps in `P(h)` that answer every read and acknowledge every write invoked at `p`." |
| `«app:cap-response/register-obligation»` | theorem | "Every finite history has a linearization, so `Q_p` is total, and it is upward closed within fibers." Lean: |
| `«app:cap-response/interleaving»` | theorem | "Real time is the order of history events in an execution. |
| `«app:cap-response/realized-history»` | theorem | "For a prefix `C` of `λ` (a consistent cut), the *realized history* `h_C` contains the operations invoked in `C`, with an edge from `a` to `b` when `a`'s res… |
| `«app:cap-response/realized-mono»` | theorem | "If `C' ⊆ C` is also a prefix, `h_C` extends `h_{C'}`." |
| `«app:cap-response/realized-not-expansion»` | theorem | "The realized history need not be a common input extension of the participants' current inputs: |
| `«app:cap-response/client-history»` | theorem | "A *client history* has two participants with empty initial inputs, and each of its input events adds one operation, invoked at its participant after all of… |
| `«cor:gilbert-lynch»` | theorem | **Corollary `cor:gilbert-lynch` (Gilbert–Lynch).** "No system for the linearizable register has Answering for `(Q_p)` together with the following, both requi… |
| `«cor:gilbert-lynch/hypotheses»` | theorem | The two hypotheses of Corollary `cor:gilbert-lynch`, unfolded; Answering at the end of client histories is equivalent to its cut form `AnsweringC` (cuts of c… |
| `«cor:gilbert-lynch/via-forced-answer»` | theorem | Proof of Corollary `cor:gilbert-lynch`, along the paper's route through Lemma `lem:forced-answer` (here with the hypotheses required of all histories, not on… |
| `«cor:gilbert-lynch/also-excludes»` | theorem | "A system with Response Availability, and with a common output extension at `h_C` for every prefix `C` of every partitioned history, satisfies these hypothes… |
| `«cor:gilbert-lynch/not-relMono»` | theorem | (Section `sec:complete-cap`, repeated here for reference.) "a single emitted output has no output extension in the fiber at some input extension of its input… |
| `«prop:gl-async/available»` | theorem | Prop. |
| `«prop:gl-async/atomic»` | theorem | Prop. |
| `«prop:gl-async»` | theorem | **Proposition `prop:gl-async` (Gilbert–Lynch, asynchronous model).** "In the asynchronous network model with at least two nodes, no algorithm for a read/writ… |
| `«prop:gl-async/proof»` | theorem | Proof sketch of Prop. |
| `«prop:gl-async/atomic-view»` | theorem | Proof sketch of Prop. |
| `«prop:gl-async/non-vacuity»` | theorem | Non-vacuity (not a claim of the paper): |
| `«prop:gl-async/fair-executions»` | theorem | The fair-execution forms imply the finite forms, and Gilbert and Lynch's Theorem 1 holds as they state it. |

### Appendix G: 2PL and MVTO

File `Paper/AppG_TransactionBases.lean`; paper source `appendices/commitment-bases.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«app:cc-bases/input»` | abbrev | "An input is a finite set of transactions, each given by the sequence of operations that its client has issued so far: |
| `«app:cc-bases/input-order»` | theorem | "One input precedes another when every transaction of the first is in the second and its sequence in the first is a prefix of its sequence in the second; onc… |
| `«app:cc-bases/output»` | abbrev | "An output has three parts: |
| `«app:cc-bases/output-order»` | theorem | "One output extends another when it extends all three parts …" `(L,X,ρ) ⪯ (L',X',ρ') ⟺ X ⊆ X', dom L ⊆ dom L', L'\|_{dom L} = L, ρ ⊆ ρ'`. |
| `«app:cc-bases/complete-output»` | theorem | "An output is *complete* at an input when it commits or aborts every transaction of the input, and not both, and commits only transactions whose commit reque… |
| `«app:cc-bases/read-rule»` | theorem | "… each read of a key `x` by a committed transaction `T` returns `T`'s own write of `x` if `T` writes `x` earlier in its sequence, and otherwise the write of… |
| `«app:cc-bases/complete»` | theorem | "A complete output is permitted when it meets two conditions. |
| `«app:cc-bases/permitted»` | theorem | "Any output is permitted when some permitted complete output extends it, that is, when it can still be completed." |
| `«app:cc-bases/spec»` | abbrev | The specification. |
| `«app:cc-bases/figure-rows»` | theorem | "The figures … show only complete outputs without aborts or read results, as serial orders, at inputs in which every transaction has requested commit": |
| `«app:cc-bases/total»` | theorem | "Every input has a permitted row: |
| `«app:cc-bases/ab-ba-not-monotone»` | theorem | "Let `{A,B}` be an input in which `A` and `B` have each requested commit. |
| `«app:cc-bases/abort-free-spec»` | theorem | "The *abort-free* specification permits a row when it can be completed with `X = ∅`. |
| `«app:cc-bases/abort-free-not-monotone»` | theorem | "The same two rows show that it is not monotone either." |
| `«app:cc-bases/applied»` | theorem | "Applied at a state `(i,R)`, it keeps the rows of `R` that can still be completed, within `R`, by a complete row satisfying the condition, and removes the rest. |
| `«app:cc-bases/conditions»` | theorem | The four conditions. |
| `«app:cc-bases/order»` | abbrev | `order(A,B)`, for distinct `A,B ∈ i`. |
| `«app:cc-bases/commit»` | abbrev | `TxCommit(A)`, for `A` whose commit request is in `i`. |
| `«app:cc-bases/abort»` | abbrev | `abort(A)`, for `A ∈ i`. |
| `«app:cc-bases/stamp»` | abbrev | `stamp(A)`, for `A ∈ i ∖ Z`, `Z ⊆ i`. |
| `«app:cc-bases/read»` | abbrev | `read(A,k,v)`, for `A ∈ i` whose `k`-th operation in `i` is a read. |
| `«app:cc-bases/each-is-commitment»` | theorem | "Each is a commitment (Definition `def:commitment`). |
| `«app:cc-bases/complete-kept-iff»` | theorem | "… For them a complete row is kept exactly when it satisfies the condition, since two permitted complete outputs at one input, one extending the other, have… |
| `«app:cc-bases/bases»` | theorem | "The bases are `B_2PL = {order, TxCommit, abort, read}` and `B_MVTO = {stamp, TxCommit, abort, read}`, over all transactions, positions, and versions." |
| `«app:cc-bases/bases-differ»` | theorem | "… and differ in how they order. |
| `«app:cc-bases/run-states»` | theorem | "Every state that a run under either basis reaches has two properties: |
| `«app:cc-bases/read-emit»` | theorem | "Because of these properties, a scheduler reports a read by first applying `read(A,k,v)` in a commitment event; emitting the result is then a legal output."… |
| `«app:cc-bases/fig-h»` | theorem | "If `A` holds that lock in a conflicting mode, `B` waits. |
| `«app:cc-bases/order-nothing»` | theorem | "Sometimes every remaining complete row that commits both already places `A` before `B`. |
| `«app:cc-bases/order-at-ABC»` | theorem | "At the canonical state of `{A,B,C}` it removes `[B,A,C]` and keeps `[A,B,C]` and `[C,A,B]`. |
| `«app:cc-bases/deadlock»` | theorem | "A deadlock between `A` and `B` arises when `B` waits for a lock that `A` holds and an operation of `A` then waits for a lock that `B` holds. |
| `«app:cc-bases/deadlock-resolution»` | theorem | "Once the scheduler applies `TxCommit(A)`, every remaining complete row aborts `B`, and `TxCommit(B)` is never again defined." |
| `«app:cc-bases/abort-free-waits-forever»` | theorem | "Under the abort-free spec, once both orderings have been applied, no remaining row is at an input in which both `A` and `B` have requested commit. |
| `«app:cc-bases/fig-i»` | theorem | "On complete rows without aborts, `stamp(B)` with `Z = ∅` keeps exactly those with `B` first (Figure `fig:cc-commitments`(i))." |
| `«app:cc-bases/stamp-at-ABC»` | theorem | "At the canonical state of `{A,B,C}` it is a commitment, and it is not the commitment `x_o` of any output": |
| `«app:cc-bases/mvto-row»` | theorem | *What a read is a commitment to*, the row argument: |
| `«app:cc-bases/read-commits»` | theorem | "Hence, after the two stamps, no row that reports the read and is at an input in which `A` writes `x` commits both `A` and `B`. |
| `«app:cc-bases/writer-before-A»` | theorem | "The condition on the version, that `B` read a version older than `A`, is needed. |
| `«app:cc-bases/abort-entailed»` | theorem | *When the abort is entailed.* "Suppose `A`'s write of `x` has arrived. |
| `«app:cc-bases/abort-is-commitment»` | theorem | "While `B` is undecided, the spec does not entail it. |
| `«app:cc-bases/comparison»` | theorem | "Under MVTO, suppose `B` reads a version of a key older than `A`, which is stamped before `B`. |

### Appendix H: Additional applications

File `Paper/AppH_Applications.lean`; paper source `appendices/additional-applications.tex`.

| Lean name (`CC.Paper.…`) | Kind | Paper statement (first sentence of the docstring) |
|---|---|---|
| `«app:additional-applications/authority-output»` | abbrev | "An output is a triple `(E,V,D)`: |
| `«eq:authority-refinement»` | theorem | Eq. |
| `«app:additional-applications/safety-exposable»` | theorem | "Protocol safety guarantees that every output permitted at the current or any later input extends the certified evidence already emitted. |
| `«app:additional-applications/slot-conflict»` | theorem | "Competing proposals for an undecided slot have incompatible extensions of `D`, so certifying one is a commitment." Two current outputs deciding different va… |
| `«app:additional-applications/epoch-conflict»` | theorem | "If the succession rule were not fixed, choosing among competing next epochs would require a commitment as well." Two current outputs extending the chain `e`… |
| `«app:additional-applications/kset-input»` | abbrev | "An input is a finite set of proposals `(p,v)`, at most one per participant, ordered by inclusion." |
| `«app:additional-applications/pmap-order»` | theorem | "Outputs are partial decision maps `m : |
| `«app:additional-applications/kset-permitted»` | theorem | "At input `I`, `m` is permitted when three conditions hold: |
| `«app:additional-applications/kset-proposal-row»` | theorem | "At `p_r`'s proposal input, `{p_r ↦ v_r}` is permitted" (`k ≥ 1`). |
| `«app:additional-applications/kset-union»` | theorem | "… and the union of the proposal inputs is a common input extension" (an input because the `p_r` are distinct). |
| `«app:additional-applications/kset-any-k»` | theorem | "Any `k` of these `k+1` rows have a common output extension there": |
| `«app:additional-applications/kset-all-fail»` | theorem | "All `k+1` do not, since such an output would have `k+1` values." |
| `«app:additional-applications/kset-not-monotone»` | theorem | "So the common-extension condition fails, and the spec is not monotone (Proposition `prop:common-expansion-form`). |
| `«app:additional-applications/consensus»` | theorem | "Consensus is `k = 1`": |
| `«eq:tight-renaming»` | theorem | Eq. |
| `«app:additional-applications/renaming-singletons»` | theorem | "At `{p}` the only output is `p ↦ 1`, and at `{q}` it is `q ↦ 1`." |
| `«app:additional-applications/renaming-each-extends»` | theorem | "Each has an output extension at `{p,q}`, so Relational Monotonicity does not fail here, but no injective map extends both." |
| `«app:additional-applications/renaming-not-monotone»` | theorem | "Directed fibers also fail at `{p,q}`: |
| `«app:additional-applications/history-order»` | theorem | "Inputs are finite causal histories, that is, finite sets of environment events with a causal partial order; `h ⊑ h'` when `h` is a downward-closed subset of… |
| `«app:additional-applications/prefix-spec»` | theorem | "The *prefix* spec permits at `h` any downward-closed subset of `h`, with outputs ordered by inclusion." |
| `«app:additional-applications/prefix-monotone»` | theorem | "Old prefixes stay legal as history grows, and finite unions of prefixes are prefixes, so it satisfies Lifted Monotonicity." |
| `«app:additional-applications/prefix-empty»` | theorem | "… it guarantees neither freshness nor completeness": |
| `«app:additional-applications/complete-history»` | theorem | "A spec that requires the complete history, with output `h` at `h` and outputs ordered by equality, is functional and not monotone: |
| `«app:additional-applications/complete-history-commitment»` | theorem | "By Proposition `prop:functional-exposure-boundary`, some output can then be emitted only after a commitment that rules out larger inputs." At some state rea… |

<!-- END PAPER INDEX -->
