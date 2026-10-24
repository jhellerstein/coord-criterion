# Lean formalization

Lean 4 (core only, no Mathlib), toolchain in `lean-toolchain`.

* Build: `lake build` from this directory.
* Axiom check: `lake env lean scripts/CheckAxioms.lean` (after `lake build`).
  It reports every constant in namespace `CC` that uses `sorryAx` or an axiom
  other than `propext`, `Quot.sound`, `Classical.choice`; currently all 1508
  theorems pass and there is no `sorry`.

Every file begins with a module docstring naming the paper section it
supports, what it contains, and its modeling choices.

## Layout

The directories follow the paper.  Within a directory, the theorem file comes
first and supporting claims and examples follow.

| File (`CoordCriterion/…`) | Namespace | Paper | Contents |
|---|---|---|---|
| `Foundations/Core.lean` | `CC` | §2–§3, App. A | Orders, specifications, states, events, monotonicity notions, consistency |
| `Foundations/Runs.lean` | `CC` | §2–§3 | Lemma run-residual, survivor test, determinism of events |
| `FunctionalCALM/Theorem.lean` | `CC` | §2 | Thm. Functional CALM, Cor. state-by-input, functional exposure boundary |
| `CompleteCALM/Theorem.lean` | `CC` | §3 | LM characterizations, common-expansion form, pairs suffice, lifted output event, Thm. Complete CALM, exposure boundary |
| `CALM/Lemmas.lean` | `CC.CALM` | §2–§3, App. B | Event facts, functional remarks, Lemma reconciliation, paper proof routes, pairs suffice |
| `CALM/Examples.lean` | `CC.CALM` | §2–§3, App. B | `k`-set agreement (pairs), rows at `j`, relational state-by-input, election, directed fiber |
| `Figures.lean` | `CC.Figures` | §2–§3, §6 | Figure tables: election frames, ambiguity frames; decisive ballot vs. closing the polls |
| `Distributed/Histories.lean` | `CC.Dist` | §4.1–4.2 | Histories, cuts, Prop. distributed consistency, Cor. convergence, exchanging outputs |
| `Distributed/Commitments.lean` | `CC` | §4.3–4.4, App. C | Commitments, canonical seal/choice, system output events, normal form, seal-or-choose, canonical-equivalent, conflicting outputs |
| `Distributed/Systems.lean` | `CC.Dist` | §4.1–4.4, App. C | Figure participant-runs, consistency without unique send ids, canonical systems, reconciliation under any basis, encodings agree |
| `CAP/Model.lean` | `CC.CAP` | §4.1–4.5 | System model for Complete CAP: commitments, histories, cuts, systems, Availability, Partition Consistency |
| `CAP/CompleteCAP.lean` | `CC.CAP` | §4.5 | Thm. Complete CAP; deterministic strategies do not suffice |
| `CAP/ResponseForm.lean` | `CC.CAP` | App. F | Response Availability, Response Partition Consistency, Thm. Complete CAP (response form) |
| `CAP/Register.lean` | `CC.GL` | App. F | Linearizable register, realized histories, Cor. Gilbert–Lynch |
| `CAP/ResponseAvailability.lean` | `CC.CAP` | §4.5, App. F | Strong (2)⇒(1), RPC vs. confluence, input acceptance, Lemma locality, without replication, interface form, Lemma forced-answer, GL via forced answer |
| `CAP/AsyncGilbertLynch.lean` | `CC.AsyncGL` | App. F | Gilbert–Lynch Theorem 1 (asynchronous model) by reduction to the corollary |
| `Instances/InvariantConfluence.lean` | `CC.IConf` | §5, App. B | Bailis et al. model; Prop. invariant confluence ⇔ LM |
| `Instances/BailisDefinition.lean` | `CC.IConf` | §5 | Bailis et al. Def. 5/6 ⇔ `IConfluent` |
| `Instances/Examples.lean` | `CC.Inst` | §5, App. B, App. D | CRDTs, HAT, uniqueness example, composition examples |
| `Appendix/Composition.lean` | `CC.Comp` | App. D | Composition lemmas, Proper Coordination |
| `Appendix/Deployment.lean` | `CC.Deploy` | App. E | Deployments, separability, monotone across partitions, partition compatibility, Deployment Availability |
| `Appendix/DeploymentExamples.lean` | `CC.Deploy` | App. E | Chains of emitted outputs, leader example, sole-authority sufficient condition, single-authority deployments |
| `Appendix/DeploymentSystems.lean` | `CC.Deploy` | App. E | Remark: the proposition applies to system runs |
| `Appendix/TransactionBases/NoReads.lean` | `CC.Txn` | App. G | `(L,X)` spec, filter commitments on antichain fibers, 2PL/MVTO bases |
| `Appendix/TransactionBases/ReadSpec.lean` | `CC.Txn.Reads` | App. G | The `(L,X,ρ)` spec of the appendix; MVTO abort claim; concrete instance |
| `Appendix/TransactionBases/PaperSpec.lean` | `CC.Txn.Full` | App. G | Appendix claims re-proved for the `(L,X,ρ)` spec |
| `Appendix/Frontiers.lean` | `CC.Front` | App. H | Remembered-output hull, Table lookup-lift, Hoare quotient, persistent forwarding |
| `Appendix/ProductFrontier.lean` | `CC.Deploy` | App. H | Thm. independent-product frontier, configuration example |
| `Appendix/Registers.lean` | `CC.Deploy` | App. E (registers), App. H | Causal and linearizable registers, two-write history, causal-register frontier |
| `Appendix/Applications.lean` | `CC.Apps` | App. I | Committed authority, `k`-set agreement, tight renaming, snapshots |

`ProductFrontier` and `Registers` are in `CC.Deploy` because they are stated
in terms of the deployment notions of `Appendix/Deployment.lean`.

## Paper results

Each row names the Lean declarations and the file (relative to
`CoordCriterion/`, without `.lean`).  Every name below is checked to exist by
`lake env lean scripts/CheckReadme.lean` (one `#check` per name; regenerate it
when the table changes).

### Foundations

| Paper result | Lean | File |
|---|---|---|
| Lemma run-residual | `CC.run_residual` | Foundations/Runs |
| Prop. survivor test | `CC.survivor_test` | Foundations/Runs |

### §2 Functional CALM

| Paper result | Lean | File |
|---|---|---|
| Event facts: `input j; input k` = `input k`, `input i` no-op, determinism, determined stays determined, canonical state largest | `CC.CALM.input_input`, `CC.CALM.input_self`, `CC.step_det`, `CC.CALM.step_determined`, `CC.CALM.state_le_canon`, `CC.CALM.input_canon` | CALM/Lemmas; `step_det`: Foundations/Runs |
| Thm. Functional CALM | `CC.functional_calm` | FunctionalCALM/Theorem |
| Cor. state-by-input | `CC.state_by_input` | FunctionalCALM/Theorem |
| Prop. functional exposure boundary | `CC.functional_exposure_boundary` | FunctionalCALM/Theorem |
| Functional remarks: exposability test, commit ⇔ seal, failure of monotonicity seals `k`, RelMono/LM/CE = monotonicity for functions, `input(j)` alone reaches `σ_S(j)` | `CC.CALM.exposable_iff_refines_all`, `CC.CALM.functional_commit_iff_sealed`, `CC.CALM.nonmono_seals`, `CC.CALM.liftedMono_iff_monoF`, `CC.CALM.commonExpansion_iff_monoF`, `CC.CALM.functional_meet_by_input` | CALM/Lemmas |
| Prop. survivor test, explicit `input(j); output(u)` form | `CC.CALM.survivor_exec` | CALM/Lemmas |

### §3 Complete CALM

| Paper result | Lean | File |
|---|---|---|
| LM ⇔ Relational Monotonicity ∧ Directed Outputs | `CC.liftedMono_iff_relMono_directed` | CompleteCALM/Theorem |
| Prop. common-expansion form | `CC.liftedMono_iff_commonExpansion` | CompleteCALM/Theorem |
| Prop. lifted exposure test | `CC.lifted_exposure_test` | CompleteCALM/Theorem |
| Thm. Complete CALM | `CC.complete_calm` | CompleteCALM/Theorem |
| Prop. exposure boundary | `CC.exposure_boundary` | CompleteCALM/Theorem |
| Sealed/Retired/Rejected partition and commutation | `CC.ruledOut_iff`, `CC.seal_choose_comm`, … | CompleteCALM/Theorem |
| Cor. state-by-input fails for relational specs | `CC.CALM.state_by_input_fails_relationally` | CALM/Examples |
| Election example (monotone / equality order, panels) | `CC.CALM.elec_consistent`, `CC.CALM.elecEq_not_consistent`, `CC.CALM.elec_panels_exposable`, `CC.CALM.elecEq_bot_single_row`, `CC.CALM.elecEq_not_confluent` | CALM/Examples |
| Directed-fiber example `{{a},{b},{a,b,c},{a,b,d},{a,b,c,d}}` | `CC.CALM.f5_directed`, `CC.CALM.f5_minimal_incomparable`, `CC.CALM.f5_compatible` | CALM/Examples |

### Appendix B: deferred proofs for §2–§3

| Paper result | Lean | File |
|---|---|---|
| Lemma reconciliation; consistency over run families | `CC.CALM.reconciliation`, `CC.CALM.consistent_iff_runs` | CALM/Lemmas |
| Thm. Complete CALM, paper's proof route (via Lemma reconciliation) | `CC.CALM.complete_calm_paper`, `CC.CALM.complete_calm_paper_lm` | CALM/Lemmas |
| Prop. exposure boundary, paper's proof route (forward via consistency; holds at every run state) | `CC.CALM.exposure_boundary_paper`, `CC.CALM.exposable_of_consistent` | CALM/Lemmas |
| Pairs suffice (`app:pairs-suffice`); rows at `j` needed; minimal-input rows fail even `k` at a time (`k`-set agreement) | `CC.CALM.pairs_iff_commonExpansion`, `CC.CALM.rowsAtJ_needed`, `CC.CALM.KSet.atomic_k_at_a_time`, `CC.CALM.KSet.not_commonExpansion` | CALM/Lemmas, CALM/Examples |
| `k`-set agreement example: any `k` proposal rows compatible, not all `k+1`; not monotone | `CC.CALM.KSet.any_k_compatible`, `CC.CALM.KSet.not_all_compatible`, `CC.CALM.KSet.not_liftedMono` | CALM/Examples |

### Figures of §2–§3 and the discussion

| Paper result | Lean | File |
|---|---|---|
| Fig. election-frames (d) "(b), then polls closed": the registrar's seal `closePolls` is a commitment and a seal; `Out_{[closePolls]}(⊥)` ends at the single row `(xy·,⊥)`, determined with result `⊥`; struck rows exactly `(xyx,x)`, `(xyy,y)`; `⊥` alone needs no commitment; table equals Fig. nonmonotone-frame; canonical equivalent run | `CC.Figures.closePolls`, `CC.Figures.closePolls_seals`, `CC.Figures.Elec.registrar_step`, `CC.Figures.Elec.panelD_rows`, `CC.Figures.Elec.panelD_determined`, `CC.Figures.Elec.panelD_struck`, `CC.Figures.Elec.panelD_gray`, `CC.Figures.Elec.bot_alone_at_b`, `CC.Figures.Elec.panelD_matches_e`, `CC.Figures.Elec.registrar_canonical` | Figures |
| Fig. election-frames (a)–(c): printed outputs (exactly the rows ⪰ `x··`), upper fibers, panel (b) rows | `CC.Figures.Elec.printed_rows`, `CC.Figures.Elec.printed_complete`, `CC.Figures.Elec.upper_ab`, `CC.Figures.Elec.upper_c`, `CC.Figures.Elec.panel_b`, `CC.Figures.Elec.shown_inputs` | Figures |
| Sec. discussion: decisive ballot (input retirement) vs. closing the polls (commitment); in the election they never leave the same result | `CC.Figures.Elec.decisive_vs_close`, `CC.Figures.Elec.determined_has_winner` | Figures |
| Fig. ambiguity-frames (f): `[B,A]` rejected (not sealed/retired), not exposable, `c_[A,B]` applies with the input legal, incompatible / not monotone / not consistent, runs emitting `[A,B]` and `[B,A]` not confluent | `CC.Figures.Txn.after_ab`, `CC.Figures.Txn.ba_rejected`, `CC.Figures.Txn.ab_not_exposable`, `CC.Figures.Txn.choice_applies`, `CC.Figures.Txn.not_monotone`, `CC.Figures.Txn.runs_not_confluent` | Figures |
| Fig. ambiguity-frames (g): remaining rows, removed rows retired, exposable; fiber union-closed and directed, monotone, consistent; union survives in both runs; state depends on outputs | `CC.Figures.Trace.after_s1`, `CC.Figures.Trace.removed_retired`, `CC.Figures.Trace.union_mem`, `CC.Figures.Trace.directed`, `CC.Figures.Trace.union_survives`, `CC.Figures.Trace.state_depends_on_outputs` | Figures |

### §4.1–4.2 Histories and distributed consistency

| Paper result | Lean | File |
|---|---|---|
| Prop. consistency ⇔ distributed consistency | `CC.Dist.consistent_iff_distConsistent` | Distributed/Histories |
| Cor. convergence | `CC.Dist.convergence` | Distributed/Histories |
| Exchanging outputs (table level) | `CC.Dist.honor_survivor`, `CC.Dist.honor_cut_confluent` | Distributed/Histories |
| Fig. participant-runs: distinct histories, equal endpoints | `CC.Dist.fig_participant_runs` | Distributed/Systems |
| Prop. distributed-consistency without unique send identifiers | `CC.Dist.consistent_iff_distConsistent0` | Distributed/Systems |
| Distributed consistency ⇔ Lifted Monotonicity | `CC.Dist.distConsistent_iff_liftedMono` | Distributed/Systems |

### §4.3–4.4 Systems and coordination; Appendix C commitment bases

| Paper result | Lean | File |
|---|---|---|
| Def. commitment; canonical seals/choices are commitments | `CC.Commitment`, `CC.sealC`, `CC.choiceC` | Distributed/Commitments |
| Lemma containment (normal form) | `CC.containment`, `CC.canonical_support`, `CC.eps_step_iff` | Distributed/Commitments |
| Prop. seal-or-choose | `CC.seal_or_choose` | Distributed/Commitments |
| Lemma canonical-equivalent | `CC.canonical_equivalent` | Distributed/Commitments |
| Prop. conflicting outputs | `CC.conflicting_outputs` | Distributed/Commitments |
| One row per input: excludes vacuous, κ_o ⊆ s_o, s_o = functional seal, legality | `CC.Dist.functional_excludes_vacuous`, `CC.Dist.functional_kappa`, `CC.Dist.functional_seal_eq`, `CC.Dist.functional_legal_ge` | Distributed/Systems |
| Def. canonical system: canonical histories = histories of Sec. histories | `CC.Dist.canonLegal_iff`, `CC.Dist.canonExec_unique` | Distributed/Systems |
| Prop. conflicting outputs (separate bases); conflict is a choice | `CC.Dist.conflicting_outputs2`, `CC.Dist.conflict_is_choice` | Distributed/Systems |
| Compound output event = composite event; functional composite seals | `CC.Dist.sysStep_to_composite`, `CC.Dist.sysStep_of_composite`, `CC.Dist.composite_functional_seals` | Distributed/Systems |
| Cor. reconciliation under any basis | `CC.Dist.reconciliation_any_basis` | Distributed/Systems |
| Converse of Lemma canonical-equivalent fails; system runs hide non-monotonicity | `CC.Dist.converse_fails`, `CC.Dist.system_runs_hide_nonmonotonicity` | Distributed/Systems |
| Deterministic reconciliation is commitment-free under LM | `CC.Dist.reconcile_cf` | Distributed/Systems |
| `Distributed/Commitments` and `CAP/Model` encodings of commitments/output events agree | `CC.Dist.toCAP`, `CC.Dist.ofCAP`, `CC.Dist.sysStep_iff_CAP` | Distributed/Systems |
| "Neither is the choice c_o" (antichain fibers) | `CC.Dist.choice_antichain`, `CC.Dist.not_choice_of_two` | Distributed/Systems |

### §4.5 Complete CAP

| Paper result | Lean | File |
|---|---|---|
| Thm. Complete CAP | `CC.CAP.complete_cap` | CAP/CompleteCAP |
| Thm. Complete CAP, (2)⇒(1) with commitment-free, receive-free confluence continuations | `CC.CAP.cf_partitionConsistencyCF`, `CC.CAP.complete_cap_strong` | CAP/ResponseAvailability |

### §5 Instances (incl. Appendix B invariant confluence)

| Paper result | Lean | File |
|---|---|---|
| Sec. query-instance: functional fibers are directed | `CC.CALM.functional_directed` | CALM/Lemmas |
| Sec. crdt-instance: Eq. crdt-state-function monotone, `s(U₁)⊔s(U₂)=s(U₁∪U₂)`, least | `CC.Inst.st_mono`, `CC.Inst.st_union`, `CC.Inst.st_union_least` | Instances/Examples |
| Eq. crdt-query-monotonicity (Functional CALM for `q∘s`); sufficient, reachable-only, not required | `CC.Inst.crdt_query_calm`, `CC.Inst.crdt_query_of_mono`, `CC.Inst.crdt_query_mono_iff_reachable`, `CC.Inst.crdt_query_mono_not_required` | Instances/Examples |
| Two-phase set (Eq. crdt-2p-query) | `CC.Inst.twoPhase_unsafe` | Instances/Examples |
| Threshold queries (Eq. crdt-thresholds) | `CC.Inst.Q100_mono`, `CC.Inst.Q100_consistent_exposable`, `CC.Inst.lvar_threshold_mono` | Instances/Examples |
| LWW: monotone convergence depends on the output order | `CC.Inst.lww_depends_on_order` | Instances/Examples |
| Sec. hat-instance: accumulating facts (read committed) | `CC.Inst.factSpec_liftedMono`, `CC.Inst.rc_liftedMono_consistent`, `CC.Inst.accumulating_example` | Instances/Examples |
| Sec. hat-instance: serialization cycle; first-committer-wins | `CC.Inst.serializability_cycle`, `CC.Inst.serializable_spec_not_consistent`, `CC.Inst.snapshot_fcw` | Instances/Examples |
| App. iconfluence: inputs closed under the order | `CC.Inst.pre_sub`, `CC.Inst.locValid_sub` | Instances/Examples |
| Sec. iconfluence-instance: uniqueness (`sam`) example | `CC.Inst.uniqueness_example`, `CC.Inst.uniqueness_concurrency` | Instances/Examples |
| Prop. invariant confluence ⇔ Lifted Monotonicity | `CC.IConf.ic_iff_liftedMono` | Instances/InvariantConfluence |
| Sec. iconfluence-instance: Bailis et al. Def. 5/6 (I-T-reachability, common ancestor) ⇔ `IConfluent` | `CC.IConf.ReachFrom`, `CC.IConf.bailis_iff`, `CC.IConf.Anc`, `CC.IConf.s0_anc`, `CC.IConf.bailisAnc_iff`, `CC.IConf.reachPlus_iff` | Instances/BailisDefinition |

### Appendix D: composition

| Paper result | Lean | File |
|---|---|---|
| Lemma composition (+ associativity) | `CC.Comp.seq_liftedMono`, `CC.Comp.tcomp_assoc` | Appendix/Composition |
| Cor. functional composition | `CC.Comp.functional_composition` | Appendix/Composition |
| Prop. curried equijoin plan | `CC.Comp.curried_query_plan` | Appendix/Composition |
| Lemma independently parameterized composition (+ graph instance) | `CC.Comp.par_liftedMono`, `CC.Comp.parameterized_functional_composition` | Appendix/Composition |
| Def./Cor. Proper Coordination (sequential, parameterized) | `CC.Comp.proper_coordination_seq`, `CC.Comp.proper_coordination_par`, `CC.Comp.proper_second_clause` | Appendix/Composition |
| Cor. committing upstream to a monotone function | `CC.Comp.monotone_commitment_seq`, `CC.Comp.monotone_commitment_par` | Appendix/Composition |
| Remarks: neither S₁ nor unresolved composition need be monotone; strict generality | `CC.Comp.monotone_commitment_neither_monotone`, `CC.Comp.proper_strictly_more_general` | Appendix/Composition |
| Counterexample: Lemma composition needs S₂ total on all of M | `CC.Comp.restricted_middle_counterexample` | Appendix/Composition |
| App. composition: converse example after Cor. monotone-commitment | `CC.Inst.converse_example` | Instances/Examples |
| Eq. curried-composition: curried form, plan on graph tables | `CC.Inst.curried_sharp`, `CC.Inst.curried_plan_graph` | Instances/Examples |
| Example committed-log-composition (incl. restriction to coherent pairs) | `CC.Inst.committed_log_example`, `CC.Inst.onDom_liftedMono` | Instances/Examples |

### Appendix E: deployment (incl. registers)

| Paper result | Lean | File |
|---|---|---|
| Defs. deployment, separable family, monotone across partitions, deployment availability | `CC.Deploy.Separable`, `CC.Deploy.MonoAcrossPartitions`, `CC.Deploy.DeploymentAvailability` | Appendix/Deployment |
| Prop. partition compatibility under a deployment | `CC.Deploy.partition_compatibility`, `CC.Deploy.partition_compatibility_confluent` | Appendix/Deployment |
| Monotonicity ⇒ monotone across partitions | `CC.Deploy.monoAcrossPartitions_of_liftedMono` | Appendix/Deployment |
| Full deployment: monotone across partitions ⇔ monotone (pairs suffice); Deployment Availability = Availability | `CC.Deploy.full_deployment_iff`, `CC.ce_of_pairs`, `CC.Deploy.deploymentAvailability_full` | Appendix/Deployment; `ce_of_pairs`: CompleteCALM/Theorem |
| Run outputs form a chain; rows authorized only to `p` are separable only as one row | `CC.Deploy.rows_chain`, `CC.Deploy.rows_max`, `CC.Deploy.sole_rows_separable`, `CC.Deploy.sole_rows_two_not_separable` | Appendix/DeploymentExamples |
| Leader example (equality order, `A_p=S`, `A_q=∅`, any input poset) | `CC.Deploy.lead_monoAcross`, `CC.Deploy.lead_not_liftedMono`, `CC.Deploy.lead_separable_shape`, `CC.Deploy.lead_run_one_output` | Appendix/DeploymentExamples |
| Sufficient condition for monotone across partitions (sole-authority conflicts) | `CC.Deploy.monoAcross_of_sole_conflicts`, `CC.Deploy.cfg_product_conflict` (product interface does not satisfy it) | Appendix/DeploymentExamples, Appendix/ProductFrontier |
| Single-authority deployments | `CC.Deploy.single_authority_shape`, `CC.Deploy.single_authority_iff` | Appendix/DeploymentExamples |
| App. deployment remark: system runs (`CC.CAP` local runs, any commitments) of a separable authorized family / partitioned-history cut have a common refinement in `S(j)` under monotonicity across partitions (via `canonical_equivalent`, `sysStep_iff_CAP`); `u` need not be authorized | `CC.Deploy.lrun_sysExec`, `CC.Deploy.SRun.canonical`, `CC.Deploy.system_monoAcross`, `CC.Deploy.history_monoAcross`, `CC.Deploy.unauthorized_refinement` | Appendix/DeploymentSystems |
| Linear extensions of finite strict partial orders | `CC.Deploy.linExt`, `CC.Deploy.concat_sto`, `CC.Deploy.sto_max` | Appendix/Registers |
| Causal register monotone across partitions (replica deployment, every history) | `CC.Deploy.causal_monoAcross`, `CC.Deploy.causal_confluent`, `CC.Deploy.ser_extend` | Appendix/Registers |
| Two-write history (linearizable not monotone across `{{p},{q}}`; causal map; causal not monotone) | `CC.Deploy.lin_not_monoAcross`, `CC.Deploy.causal_two_write`, `CC.Deploy.causal_not_liftedMono` | Appendix/Registers |
| Real-time precedence breaks local conservativity | `CC.Deploy.linRT_not_locCons` | Appendix/Registers |

### Appendix F: response availability and Gilbert–Lynch

| Paper result | Lean | File |
|---|---|---|
| Thm. Complete CAP, response form | `CC.CAP.complete_cap_response` | CAP/ResponseForm |
| Remark: confluence ⇒ RPC; coincide for canonical systems; converse fails with other commitments | `CC.CAP.rpc_of_confluent`, `CC.CAP.canonical_rpc_iff_confluent`, `CC.CAP.rpc_not_confluent` | CAP/ResponseAvailability |
| Input acceptance ⇔ no seal of an expansion; excludes forced seals (election, equality order) | `CC.CAP.input_acceptance_iff`, `CC.CAP.ra_excludes_forced_seal`, `CC.CAP.election_eq_no_ra` | CAP/ResponseAvailability |
| An output answering at every input makes every spec available | `CC.CAP.trivially_available` | CAP/ResponseAvailability |
| Lemma locality | `CC.CAP.locality_glue`, `CC.CAP.locality_transfer` | CAP/ResponseAvailability |
| Remark: consistency on `T` (= CE for `T = S`; = confluence of canonical runs with rows in `T`) | `CC.CAP.consistentOn_S`, `CC.CAP.consistentOn_iff_confluent` | CAP/ResponseAvailability |
| Remark without replication: counterexample as stated; corrected form (fixed participant set, `LocalInit`) | `CC.CAP.without_replication_counterexample`, `CC.CAP.without_replication_interface`, `CC.CAP.without_replication` | CAP/ResponseAvailability |
| LM ⇒ response form with `T = Q`; converse fails; functional coincidence | `CC.CAP.lm_response_interface`, `CC.CAP.lm_response_form`, `CC.CAP.converse_counterexample`, `CC.CAP.converse_counterexample_systems`, `CC.CAP.functional_response_iff`, `CC.CAP.functional_forms_coincide` | CAP/ResponseAvailability |
| LM sub-spec ⇒ interface; five-input counterexample (and `d₁`/`d₂` seal `k₂`/`k₁`) | `CC.CAP.subspec_lm_interface`, `CC.CAP.subspec_counterexample`, `CC.CAP.emit_d1_seals_k2`, `CC.CAP.emit_d2_seals_k1` | CAP/ResponseAvailability |
| Lemma forced-answer (only `q`'s events, no input event; from Answering) | `CC.CAP.forced_answer` | CAP/ResponseAvailability |
| Cor. Gilbert–Lynch along the paper's proof, from Answering only | `CC.CAP.gilbert_lynch_answering`, `CC.CAP.gilbert_lynch_via_forced_answer` | CAP/ResponseAvailability |
| Register fails Relational Monotonicity; `Q_p` is an obligation | `CC.CAP.reg_not_relMono`, `CC.CAP.regQ_obligation` | CAP/ResponseAvailability |
| Register spec: `Q_p` total and upward closed | `CC.GL.regQ_total`, `CC.GL.regQ_upward` | CAP/Register |
| Realized history monotone in the prefix | `CC.GL.realized_mono` | CAP/Register |
| Cor. Gilbert–Lynch | `CC.GL.gilbert_lynch`, `CC.GL.gilbert_lynch_full` | CAP/Register |
| Counterexample: `h_C` need not expand the current inputs | `CC.GL.realized_not_expansion` | CAP/Register |
| GL model: async algorithms, executions, atomicity (Lynch), availability under message loss; non-vacuity | `CC.AsyncGL.Alg`, `CC.AsyncGL.IsGExec`, `CC.AsyncGL.Atomic`, `CC.AsyncGL.Available`, `CC.AsyncGL.silent_atomic`, `CC.AsyncGL.eager_available` | CAP/AsyncGilbertLynch |
| Cor. Gilbert–Lynch, client form (hypotheses only on two-participant client histories; implies the paper's form) | `CC.AsyncGL.gilbert_lynch_client`, `CC.AsyncGL.answeringC_of_RA`, `CC.AsyncGL.realizedRPCC_of` | CAP/AsyncGilbertLynch |
| Correspondence (1): algorithms are strategies; a lone node's atomic responses lie in the fiber at its view | `CC.AsyncGL.sysOf`, `CC.AsyncGL.atomic_view`, `CC.AsyncGL.lin_to_regS`, `CC.AsyncGL.emit_legal` | CAP/AsyncGilbertLynch |
| Correspondence (2), (3): availability gives Answering; atomicity gives RPC at the realized history | `CC.AsyncGL.sys_answering`, `CC.AsyncGL.sys_rpc` | CAP/AsyncGilbertLynch |
| Gilbert–Lynch Theorem 1 (async), by reduction to the corollary | `CC.AsyncGL.gilbert_lynch_async` | CAP/AsyncGilbertLynch |

### Appendix G: 2PL/MVTO commitment bases

| Paper result | Lean | File |
|---|---|---|
| App. cc-bases, `(L,X)` spec: spec, abort-free spec, not monotone (`([A,B],∅)`, `([B,A],∅)`) | `CC.Txn.txnSpec`, `CC.Txn.abortFreeSpec`, `CC.Txn.ab_ba_no_common_refinement`, `CC.Txn.txnSpec_not_liftedMono`, `CC.Txn.abortFreeSpec_not_liftedMono` | Appendix/TransactionBases/NoReads |
| App. cc-bases, `(L,X)` spec: fibers are antichains; order/commit/abort/stamp are commitments, defined iff some row at `i` satisfies and some row fails; bases | `CC.Txn.partitions_antichain`, `CC.Txn.filterC`, `CC.Txn.filterC_app_iff`, `CC.Txn.orderC`, `CC.Txn.stampC`, `CC.Txn.basis2PL`, `CC.Txn.basisMVTO` | Appendix/TransactionBases/NoReads |
| App. cc-bases, `(L,X)` spec: deadlock rows; abort-free `order(B,A)` undefined forever; Fig. cc-commitments (h)/(i); MVTO forces no abort; exposability here | `CC.Txn.deadlock_state`, `CC.Txn.deadlock_forces_abort`, `CC.Txn.abortFree_order_blocks_forever`, `CC.Txn.orderP_abortFree`, `CC.Txn.stampP_first_abortFree`, `CC.Txn.stamp_order_row`, `CC.Txn.exposable_iff_refines` | Appendix/TransactionBases/NoReads |
| App. cc-bases, read-result spec: spec `(L,X,ρ)` total; fibers not antichains; order/commit/abort/stamp still commitments | `CC.Txn.Reads.readSpec`, `CC.Txn.Reads.not_antichain`, `CC.Txn.Reads.comparable_same_LX`, `CC.Txn.Reads.filterCS`, `CC.Txn.Reads.stable_lift`, `CC.Txn.Reads.stampR`, `CC.Txn.Reads.basisMVTO_R` | Appendix/TransactionBases/ReadSpec |
| App. cc-bases, read-result spec: after `stamp(A)`, `stamp(B)`, emitting `ρ(B,x)=v` forces `A ∈ X` (needs `v` initial or written by a transaction stamped before `A`); base spec does not; legal instance | `CC.Txn.Reads.forced_abort_row`, `CC.Txn.Reads.forced_abort`, `CC.Txn.Reads.Ex.base_keeps_commit`, `CC.Txn.Reads.Ex.reads_rows`, `CC.Txn.Reads.Ex.read_event_legal`, `CC.Txn.Reads.Ex.writer_after_A` | Appendix/TransactionBases/ReadSpec |
| App. cc-bases, spec `(L,X,ρ)`: abort-free variant; `([A,B],∅,∅)`, `([B,A],∅,∅)` no common refinement, not monotone; comparable rows share `(L,X)`; 2PL bases | `CC.Txn.Full.abortFreeFull`, `CC.Txn.Full.full_no_common_refinement`, `CC.Txn.Full.full_not_liftedMono`, `CC.Txn.Full.abortFreeFull_not_liftedMono`, `CC.Txn.Full.full_comparable_same_LX`, `CC.Txn.Full.abortFreeFull_stable_lift`, `CC.Txn.Full.basis2PL_R`, `CC.Txn.Full.basis2PL_AF` | Appendix/TransactionBases/PaperSpec |
| App. cc-bases, spec `(L,X,ρ)`: deadlock rows at every input, later outputs abort `A` or `B`; abort-free `order(B,A)` never defined; Fig. (h)/(i) on rows without aborts; MVTO abort required by the spec | `CC.Txn.Full.deadlock_state_R`, `CC.Txn.Full.deadlock_forces_abort_R`, `CC.Txn.Full.abortFree_order_blocks_forever_R`, `CC.Txn.Full.orderP_noabort`, `CC.Txn.Full.stampP_first_noabort`, `CC.Txn.Full.mvto_forced_abort` | Appendix/TransactionBases/PaperSpec |

### Appendix H: frontiers

| Paper result | Lean | File |
|---|---|---|
| Thm. remembered-output frontier (monotone hull, pruning) | `CC.Front.monotone_hull`, `CC.Front.pruned_unique`, `CC.Front.hullSpec_consistent` | Appendix/Frontiers |
| Table lookup-lift as printed (`X(i₁)={o_b}`, `M=X̂`, forwarding above `X̂`) | `CC.Front.lookup_hull_i1`, `CC.Front.lookup_pruned`, `CC.Front.lookup_not_relMono`, `CC.Front.lookup_hull_le_fwd` | Appendix/Frontiers |
| Hoare quotient order; Eq. forwarding-hull via Eq. hull-coverage | `CC.Front.hclass_of_le_iff`, `CC.Front.hclass_of_eq_iff`, `CC.Front.hclass_eq_of`, `CC.Front.forwarding_hull_via_coverage` | Appendix/Frontiers |
| Prop. persistent-forwarding monotonicity; Eq. forwarding-hull | `CC.Front.persistent_forwarding`, `CC.Front.fwdSpec_consistent`, `CC.Front.forwarding_hull` | Appendix/Frontiers |
| Thm. independent-product frontier (per-participant posets `W_p`) | `CC.Deploy.product_monoAcross`, `CC.Deploy.product_confluent`, `CC.Deploy.strengthening_not_monoAcross` | Appendix/ProductFrontier |
| "deployment is essential" (corrected: no common upper bound in `V_p(i)`); counterexample to literal wording | `CC.Deploy.product_not_liftedMono`, `CC.Deploy.product_full_not_monoAcross`, `CC.Deploy.tri_incomparable`, `CC.Deploy.tri_liftedMono` | Appendix/ProductFrontier |
| Configuration example (any input poset; single-authority variant) | `CC.Deploy.cfg_agree_not_monoAcross`, `CC.Deploy.cfg_agree_single_authority` | Appendix/ProductFrontier |
| Causal-register frontier application (antichain, views continue, part (1); linearizability locally conservative and strict, part (2)) | `CC.Deploy.cviews_antichain`, `CC.Deploy.cviews_cont`, `CC.Deploy.causal_product_monoAcross`, `CC.Deploy.lin_locCons`, `CC.Deploy.lin_strict`, `CC.Deploy.lin_product_not_monoAcross` | Appendix/Registers |

### Appendix I: additional applications

| Paper result | Lean | File |
|---|---|---|
| App. additional-applications: authority (order; safety ⇒ exposable; competing slot decisions / next epochs need a commitment) | `CC.Apps.instPOAuth`, `CC.Apps.safety_exposable`, `CC.Apps.slot_conflict`, `CC.Apps.epoch_conflict` | Appendix/Applications |
| App. additional-applications: k-set agreement (general k) | `CC.Apps.kset_single_row`, `CC.Apps.kset_union_upper`, `CC.Apps.kset_any_k`, `CC.Apps.kset_all_fail`, `CC.Apps.kset_not_commonExpansion`, `CC.Apps.kset_not_liftedMono`, `CC.Apps.kset_no_cap` | Appendix/Applications |
| App. additional-applications: tight renaming | `CC.Apps.ren_singleton_iff`, `CC.Apps.ren_each_extends`, `CC.Apps.ren_no_injective_extends_both`, `CC.Apps.ren_not_directed`, `CC.Apps.ren_no_cap` | Appendix/Applications |
| App. additional-applications: snapshots (prefix spec monotone; complete-history spec functional, not monotone, needs a seal) | `CC.Apps.prefix_mono`, `CC.Apps.prefix_union`, `CC.Apps.prefixSpec_liftedMono`, `CC.Apps.prefix_empty`, `CC.Apps.completeSpec_functional`, `CC.Apps.completeSpec_not_monotone`, `CC.Apps.completeSpec_seal_needed` | Appendix/Applications |
