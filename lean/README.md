# Lean formalization

Lean 4 (core only, no Mathlib), toolchain in `lean-toolchain`.
Build: `lake build` from this directory.  Every theorem below depends only on
the standard axioms (`propext`, `Quot.sound`, and in some cases
`Classical.choice`); there is no `sorry`.  A metaprogram check over all
2125 theorem constants in namespace `CC` confirms this.

The `Audit/` files check each proved claim against the current paper text and
add proofs where the earlier files differ from it.  Where a result appears both
in an earlier file and in an `Audit/` file, the `Audit/` row is the one that
matches the current text; the table marks the earlier rows that no longer do.

| Paper result | Lean | File |
|---|---|---|
| Lemma run-residual | `CC.run_residual` | Runs |
| Prop. survivor test | `CC.survivor_test` | Runs |
| Thm. Functional CALM | `CC.functional_calm` | FunctionalCALM |
| Cor. state-by-input | `CC.state_by_input` | FunctionalCALM |
| Prop. functional exposure boundary | `CC.functional_exposure_boundary` | FunctionalCALM |
| LM ⇔ Relational Monotonicity ∧ Directed Outputs | `CC.liftedMono_iff_relMono_directed` | CompleteCALM |
| Prop. common-expansion form | `CC.liftedMono_iff_commonExpansion` | CompleteCALM |
| Prop. lifted exposure test | `CC.lifted_exposure_test` | CompleteCALM |
| Thm. Complete CALM | `CC.complete_calm` | CompleteCALM |
| Prop. exposure boundary | `CC.exposure_boundary` | CompleteCALM |
| Sealed/Retired/Rejected partition and commutation | `CC.ruledOut_iff`, `CC.seal_choose_comm`, … | CompleteCALM |
| Prop. consistency ⇔ distributed consistency | `CC.Dist.consistent_iff_distConsistent` | Distributed |
| Cor. convergence | `CC.Dist.convergence` | Distributed |
| Exchanging outputs (table level) | `CC.Dist.honor_survivor`, `CC.Dist.honor_cut_confluent` | Distributed |
| Def. commitment; canonical seals/choices are commitments | `CC.Commitment`, `CC.sealC`, `CC.choiceC` | Commitments |
| Lemma containment (normal form) | `CC.containment`, `CC.canonical_support`, `CC.eps_step_iff` | Commitments |
| Prop. seal-or-choose | `CC.seal_or_choose` | Commitments |
| Lemma canonical-equivalent | `CC.canonical_equivalent` | Commitments |
| Prop. conflicting outputs | `CC.conflicting_outputs` | Commitments |
| Fig. participant-runs: distinct histories, equal endpoints | `CC.AuditB.fig_participant_runs` | Audit/Distributed |
| Prop. distributed-consistency without unique send identifiers | `CC.AuditB.consistent_iff_distConsistent0` | Audit/Distributed |
| Distributed consistency ⇔ Lifted Monotonicity | `CC.AuditB.distConsistent_iff_liftedMono` | Audit/Distributed |
| One row per input: excludes vacuous, κ_o ⊆ s_o, s_o = functional seal, legality | `CC.AuditB.functional_excludes_vacuous`, `CC.AuditB.functional_kappa`, `CC.AuditB.functional_seal_eq`, `CC.AuditB.functional_legal_ge` | Audit/Distributed |
| Def. canonical system: canonical histories = histories of Sec. histories | `CC.AuditB.canonLegal_iff`, `CC.AuditB.canonExec_unique` | Audit/Distributed |
| Prop. conflicting outputs (separate bases); conflict is a choice | `CC.AuditB.conflicting_outputs2`, `CC.AuditB.conflict_is_choice` | Audit/Distributed |
| Compound output event = composite event; functional composite seals | `CC.AuditB.sysStep_to_composite`, `CC.AuditB.sysStep_of_composite`, `CC.AuditB.composite_functional_seals` | Audit/Distributed |
| Cor. reconciliation under any basis | `CC.AuditB.reconciliation_any_basis` | Audit/Distributed |
| Converse of Lemma canonical-equivalent fails; system runs hide non-monotonicity | `CC.AuditB.converse_fails`, `CC.AuditB.system_runs_hide_nonmonotonicity` | Audit/Distributed |
| Deterministic reconciliation is commitment-free under LM | `CC.AuditB.reconcile_cf` | Audit/Distributed |
| `Commitments` and `CompleteCAP` encodings of commitments/output events agree | `CC.AuditB.toCAP`, `CC.AuditB.ofCAP`, `CC.AuditB.sysStep_iff_CAP` | Audit/Distributed |
| "Neither is the choice c_o" (antichain fibers) | `CC.AuditB.choice_antichain`, `CC.AuditB.not_choice_of_two` | Audit/Distributed |
| Thm. Complete CAP | `CC.CAP.complete_cap` | CompleteCAP |
| Thm. Complete CAP, response form | `CC.CAP.complete_cap_response` | CompleteCAP |
| Prop. invariant confluence ⇔ Lifted Monotonicity | `CC.IConf.ic_iff_liftedMono` | IConfluence |
| Lemma composition (+ associativity) | `CC.Comp.seq_liftedMono`, `CC.Comp.tcomp_assoc` | Composition |
| Cor. functional composition | `CC.Comp.functional_composition` | Composition |
| Prop. curried equijoin plan | `CC.Comp.curried_query_plan` | Composition |
| Lemma independently parameterized composition (+ graph instance) | `CC.Comp.par_liftedMono`, `CC.Comp.parameterized_functional_composition` | Composition |
| Def./Cor. Proper Coordination (sequential, parameterized) | `CC.Comp.proper_coordination_seq`, `CC.Comp.proper_coordination_par`, `CC.Comp.proper_second_clause` | Composition |
| Cor. committing upstream to a monotone function | `CC.Comp.monotone_commitment_seq`, `CC.Comp.monotone_commitment_par` | Composition |
| Remarks: neither S₁ nor unresolved composition need be monotone; strict generality | `CC.Comp.monotone_commitment_neither_monotone`, `CC.Comp.proper_strictly_more_general` | Composition |
| Counterexample: Lemma composition needs S₂ total on all of M | `CC.Comp.restricted_middle_counterexample` | Composition |
| Thm. remembered-output frontier (monotone hull, pruning) | `CC.Front.monotone_hull`, `CC.Front.pruned_unique`, `CC.Front.hullSpec_consistent` | Frontiers |
| Table lookup-lift (earlier version, X(i₁)={o_b,o_ab}; superseded by Audit D) | `CC.Front.lookup_hull_i1`, `CC.Front.lookup_pruned_i1` | Frontiers |
| Prop. persistent-forwarding monotonicity; Eq. forwarding-hull | `CC.Front.persistent_forwarding`, `CC.Front.fwdSpec_consistent`, `CC.Front.forwarding_hull` | Frontiers |
| Def. monotone across partitions; Prop. partition compatibility (family level) | `CC.Front.MonoAcrossPartitions`, `CC.Front.partition_compat_iff` | Frontiers |
| Thm. independent-product frontier (single value type, stricter separability; superseded by Audit D) | `CC.Front.product_monoAcross`, `CC.Front.product_partition_compat`, `CC.Front.strengthening_not_monoAcross` | Frontiers |
| Example product-config (and sole-owner variant where the other participant may emit the empty tuple) | `CC.Front.config_agreement_not_ok`, `CC.Front.agreement_ok_sole_owner` | Frontiers |
| Defs. deployment, separable family, monotone across partitions, deployment availability | `CC.Deploy.Separable`, `CC.Deploy.MonoAcrossPartitions`, `CC.Deploy.DeploymentAvailability` | Deployment |
| Prop. partition compatibility under a deployment | `CC.Deploy.partition_compatibility`, `CC.Deploy.partition_compatibility_confluent` | Deployment |
| Monotonicity ⇒ monotone across partitions; converse fails (earlier leader order ⊥<s1,s2; current text's example is Audit D `lead_*`) | `CC.Deploy.monoAcrossPartitions_of_liftedMono`, `CC.Deploy.single_authority_monoAcross`, `CC.Deploy.leader_not_liftedMono`, `CC.Deploy.split_authority_not_monoAcross` | Deployment |
| Full deployment: pairs suffice, monotone across partitions ⇔ monotone; Deployment Availability = Availability | `CC.Deploy.ce_of_pairs`, `CC.Deploy.full_deployment_iff`, `CC.Deploy.deploymentAvailability_full` | Deployment |
| Lemma forced-answer (earlier form; current statement is `CC.AuditC.forced_answer_strong`) | `CC.CAP.forced_answer` | CompleteCAP |
| Register spec: `Q_p` total and upward closed | `CC.GL.regQ_total`, `CC.GL.regQ_upward` | GilbertLynch |
| Realized history monotone in the prefix | `CC.GL.realized_mono` | GilbertLynch |
| Cor. Gilbert–Lynch | `CC.GL.gilbert_lynch`, `CC.GL.gilbert_lynch_full` | GilbertLynch |
| Counterexample: `h_C` need not expand the current inputs | `CC.GL.realized_not_expansion` | GilbertLynch |
| Lemma reconciliation; consistency over run families | `CC.AuditA.reconciliation`, `CC.AuditA.consistent_iff_runs` | Audit/CALM |
| Thm. Complete CALM, paper's proof route (via Lemma reconciliation) | `CC.AuditA.complete_calm_paper`, `CC.AuditA.complete_calm_paper_lm` | Audit/CALM |
| Prop. exposure boundary, paper's proof route (forward via consistency; holds at every run state) | `CC.AuditA.exposure_boundary_paper`, `CC.AuditA.exposable_of_consistent` | Audit/CALM |
| Prop. survivor test, explicit `input(j); output(u)` form | `CC.AuditA.survivor_exec` | Audit/CALM |
| Pairs suffice (`app:pairs-suffice`); rows at `j` needed; minimal-input rows fail even `k` at a time (`k`-set agreement) | `CC.AuditA.pairs_iff_commonExpansion`, `CC.AuditA.rowsAtJ_needed`, `CC.AuditA.KSet.atomic_k_at_a_time`, `CC.AuditA.KSet.not_commonExpansion` | Audit/CALM |
| `k`-set agreement example: any `k` proposal rows compatible, not all `k+1`; not monotone | `CC.AuditA.KSet.any_k_compatible`, `CC.AuditA.KSet.not_all_compatible`, `CC.AuditA.KSet.not_liftedMono` | Audit/CALM |
| Functional remarks: exposability test, commit ⇔ seal, failure of monotonicity seals `k`, RelMono/LM/CE = monotonicity for functions, `input(j)` alone reaches `σ_S(j)` | `CC.AuditA.exposable_iff_refines_all`, `CC.AuditA.functional_commit_iff_sealed`, `CC.AuditA.nonmono_seals`, `CC.AuditA.liftedMono_iff_monoF`, `CC.AuditA.commonExpansion_iff_monoF`, `CC.AuditA.functional_meet_by_input` | Audit/CALM |
| Event facts: `input j; input k` = `input k`, `input i` no-op, determinism, determined stays determined, canonical state largest | `CC.AuditA.input_input`, `CC.AuditA.input_self`, `CC.AuditA.step_det`, `CC.AuditA.step_determined`, `CC.AuditA.state_le_canon`, `CC.AuditA.input_canon` | Audit/CALM |
| Cor. state-by-input fails for relational specs | `CC.AuditA.state_by_input_fails_relationally` | Audit/CALM |
| Election example (monotone / equality order, panels) | `CC.AuditA.elec_consistent`, `CC.AuditA.elecEq_not_consistent`, `CC.AuditA.elec_panels_exposable`, `CC.AuditA.elecEq_bot_single_row`, `CC.AuditA.elecEq_not_confluent` | Audit/CALM |
| Directed-fiber example `{{a},{b},{a,b,c},{a,b,d},{a,b,c,d}}` | `CC.AuditA.f5_directed`, `CC.AuditA.f5_minimal_incomparable`, `CC.AuditA.f5_compatible` | Audit/CALM |
| Sec. query-instance: functional fibers are directed | `CC.AuditE.functional_directed` | Audit/Instances |
| Sec. crdt-instance: Eq. crdt-state-function monotone, `s(U₁)⊔s(U₂)=s(U₁∪U₂)`, least | `CC.AuditE.st_mono`, `CC.AuditE.st_union`, `CC.AuditE.st_union_least` | Audit/Instances |
| Eq. crdt-query-monotonicity (Functional CALM for `q∘s`); sufficient, reachable-only, not required | `CC.AuditE.crdt_query_calm`, `CC.AuditE.crdt_query_of_mono`, `CC.AuditE.crdt_query_mono_iff_reachable`, `CC.AuditE.crdt_query_mono_not_required` | Audit/Instances |
| Two-phase set (Eq. crdt-2p-query) | `CC.AuditE.twoPhase_unsafe` | Audit/Instances |
| Threshold queries (Eq. crdt-thresholds) | `CC.AuditE.Q100_mono`, `CC.AuditE.Q100_consistent_exposable`, `CC.AuditE.lvar_threshold_mono` | Audit/Instances |
| LWW: monotone convergence depends on the output order | `CC.AuditE.lww_depends_on_order` | Audit/Instances |
| Sec. hat-instance: accumulating facts (read committed) | `CC.AuditE.factSpec_liftedMono`, `CC.AuditE.rc_liftedMono_consistent`, `CC.AuditE.accumulating_example` | Audit/Instances |
| Sec. hat-instance: serialization cycle; first-committer-wins | `CC.AuditE.serializability_cycle`, `CC.AuditE.serializable_spec_not_consistent`, `CC.AuditE.snapshot_fcw` | Audit/Instances |
| App. iconfluence: inputs closed under the order | `CC.AuditE.pre_sub`, `CC.AuditE.locValid_sub` | Audit/Instances |
| Sec. iconfluence-instance: uniqueness (`sam`) example | `CC.AuditE.uniqueness_example`, `CC.AuditE.uniqueness_concurrency` | Audit/Instances |
| App. composition: converse example after Cor. monotone-commitment | `CC.AuditE.converse_example` | Audit/Instances |
| Eq. curried-composition: curried form, plan on graph tables | `CC.AuditE.curried_sharp`, `CC.AuditE.curried_plan_graph` | Audit/Instances |
| Example committed-log-composition (incl. restriction to coherent pairs) | `CC.AuditE.committed_log_example`, `CC.AuditE.onDom_liftedMono` | Audit/Instances |
| Thm. Complete CAP, (2)⇒(1) with commitment-free, receive-free confluence continuations | `CC.AuditC.cf_partitionConsistencyCF`, `CC.AuditC.complete_cap_strong` | Audit/CAP |
| Remark: confluence ⇒ RPC; coincide for canonical systems; converse fails with other commitments | `CC.AuditC.rpc_of_confluent`, `CC.AuditC.canonical_rpc_iff_confluent`, `CC.AuditC.rpc_not_confluent` | Audit/CAP |
| Input acceptance ⇔ no seal of an expansion; excludes forced seals (election, equality order) | `CC.AuditC.input_acceptance_iff`, `CC.AuditC.ra_excludes_forced_seal`, `CC.AuditC.election_eq_no_ra` | Audit/CAP |
| An output answering at every input makes every spec available | `CC.AuditC.trivially_available` | Audit/CAP |
| Lemma locality | `CC.AuditC.locality_glue`, `CC.AuditC.locality_transfer` | Audit/CAP |
| Remark: consistency on `T` (= CE for `T = S`; = confluence of canonical runs with rows in `T`) | `CC.AuditC.consistentOn_S`, `CC.AuditC.consistentOn_iff_confluent` | Audit/CAP |
| Remark without replication: counterexample as stated; corrected form (fixed participant set, `LocalInit`) | `CC.AuditC.without_replication_counterexample`, `CC.AuditC.without_replication_interface`, `CC.AuditC.without_replication` | Audit/CAP |
| LM ⇒ response form with `T = Q`; converse fails; functional coincidence | `CC.AuditC.lm_response_interface`, `CC.AuditC.lm_response_form`, `CC.AuditC.converse_counterexample`, `CC.AuditC.converse_counterexample_systems`, `CC.AuditC.functional_response_iff`, `CC.AuditC.functional_forms_coincide` | Audit/CAP |
| LM sub-spec ⇒ interface; five-input counterexample (and `d₁`/`d₂` seal `k₂`/`k₁`) | `CC.AuditC.subspec_lm_interface`, `CC.AuditC.subspec_counterexample`, `CC.AuditC.emit_d1_seals_k2`, `CC.AuditC.emit_d2_seals_k1` | Audit/CAP |
| Lemma forced-answer (current form: only `q`'s events, no input event; Answering only) | `CC.AuditC.forced_answer_strong` | Audit/CAP |
| Cor. Gilbert–Lynch along the paper's proof, from Answering only | `CC.AuditC.gilbert_lynch_answering`, `CC.AuditC.gilbert_lynch_via_forced_answer` | Audit/CAP |
| Register fails Relational Monotonicity; `Q_p` is an obligation | `CC.AuditC.reg_not_relMono`, `CC.AuditC.regQ_obligation` | Audit/CAP |
| Audit D: run outputs form a chain; rows authorized only to `p` are separable only as one row | `CC.AuditD.rows_chain`, `CC.AuditD.rows_max`, `CC.AuditD.sole_rows_separable`, `CC.AuditD.sole_rows_two_not_separable` | Audit/Deployment |
| Audit D: leader example as stated (equality order, `A_p=S`, `A_q=∅`, any input poset) | `CC.AuditD.lead_monoAcross`, `CC.AuditD.lead_not_liftedMono`, `CC.AuditD.lead_separable_shape`, `CC.AuditD.lead_run_one_output` | Audit/Deployment |
| Audit D: sufficient condition for monotone across partitions (sole-authority conflicts) | `CC.AuditD.monoAcross_of_sole_conflicts`, `CC.AuditD.cfg_product_conflict` (product interface does not satisfy it) | Audit/Deployment |
| Audit D: single-authority deployments | `CC.AuditD.single_authority_shape`, `CC.AuditD.single_authority_iff` | Audit/Deployment |
| Audit D: Thm. independent-product frontier, per-participant posets `W_p`, `CC.Deploy` definitions | `CC.AuditD.product_monoAcross`, `CC.AuditD.product_confluent`, `CC.AuditD.strengthening_not_monoAcross` | Audit/Deployment |
| Audit D: "deployment is essential" (corrected: no common upper bound in `V_p(i)`); counterexample to literal wording | `CC.AuditD.product_not_liftedMono`, `CC.AuditD.product_full_not_monoAcross`, `CC.AuditD.tri_incomparable`, `CC.AuditD.tri_liftedMono` | Audit/Deployment |
| Audit D: configuration example (any input poset; single-authority variant) | `CC.AuditD.cfg_agree_not_monoAcross`, `CC.AuditD.cfg_agree_single_authority` | Audit/Deployment |
| Audit D: linear extensions of finite strict partial orders | `CC.AuditD.linExt`, `CC.AuditD.concat_sto`, `CC.AuditD.sto_max` | Audit/Deployment |
| Audit D: causal register monotone across partitions (replica deployment, every history) | `CC.AuditD.causal_monoAcross`, `CC.AuditD.causal_confluent`, `CC.AuditD.ser_extend` | Audit/Deployment |
| Audit D: two-write history (linearizable not monotone across `{{p},{q}}`; causal map; causal not monotone) | `CC.AuditD.lin_not_monoAcross`, `CC.AuditD.causal_two_write`, `CC.AuditD.causal_not_liftedMono` | Audit/Deployment |
| Audit D: causal-register frontier application (antichain, views continue, part (1); linearizability locally conservative and strict, part (2)) | `CC.AuditD.cviews_antichain`, `CC.AuditD.cviews_cont`, `CC.AuditD.causal_product_monoAcross`, `CC.AuditD.lin_locCons`, `CC.AuditD.lin_strict`, `CC.AuditD.lin_product_not_monoAcross` | Audit/Deployment |
| Audit D: real-time precedence breaks local conservativity | `CC.AuditD.linRT_not_locCons` | Audit/Deployment |
| Audit D: Table lookup-lift as printed (`X(i₁)={o_b}`, `M=X̂`, forwarding above `X̂`) | `CC.AuditD.lookup2_hull_i1`, `CC.AuditD.lookup2_pruned`, `CC.AuditD.lookup2_not_relMono`, `CC.AuditD.lookup2_hull_le_fwd` | Audit/Deployment |
| Audit D: Hoare quotient order; Eq. forwarding-hull via Eq. hull-coverage | `CC.AuditD.hclass_of_le_iff`, `CC.AuditD.hclass_of_eq_iff`, `CC.AuditD.hclass_eq_of`, `CC.AuditD.forwarding_hull_via_coverage` | Audit/Deployment |

Modeling choices are documented at the top of each file.
| App. cc-bases: spec, abort-free spec, not monotone (`([A,B],∅)`, `([B,A],∅)`) | `CC.AuditF.txnSpec`, `CC.AuditF.abortFreeSpec`, `CC.AuditF.ab_ba_no_common_refinement`, `CC.AuditF.txnSpec_not_liftedMono`, `CC.AuditF.abortFreeSpec_not_liftedMono` | Audit/Bases |
| App. cc-bases: fibers are antichains; order/commit/abort/stamp are commitments, defined iff some row at `i` satisfies and some row fails; bases | `CC.AuditF.partitions_antichain`, `CC.AuditF.filterC`, `CC.AuditF.filterC_app_iff`, `CC.AuditF.orderC`, `CC.AuditF.stampC`, `CC.AuditF.basis2PL`, `CC.AuditF.basisMVTO` | Audit/Bases |
| App. cc-bases: deadlock rows; abort-free `order(B,A)` undefined forever; Fig. cc-commitments (h)/(i); MVTO forces no abort; exposability here | `CC.AuditF.deadlock_state`, `CC.AuditF.deadlock_forces_abort`, `CC.AuditF.abortFree_order_blocks_forever`, `CC.AuditF.orderP_abortFree`, `CC.AuditF.stampP_first_abortFree`, `CC.AuditF.stamp_order_row`, `CC.AuditF.exposable_iff_refines` | Audit/Bases |
| App. cc-bases, proposed MVTO read facts: spec `(L,X,ρ)` total; fibers not antichains; order/commit/abort/stamp still commitments | `CC.AuditF.Reads.readSpec`, `CC.AuditF.Reads.not_antichain`, `CC.AuditF.Reads.comparable_same_LX`, `CC.AuditF.Reads.filterCS`, `CC.AuditF.Reads.stable_lift`, `CC.AuditF.Reads.stampR`, `CC.AuditF.Reads.basisMVTO_R` | Audit/MVTOReads |
| App. cc-bases, proposed MVTO read facts: after `stamp(A)`, `stamp(B)`, emitting `ρ(B,x)=v` forces `A ∈ X` (needs `v` initial or written by a transaction stamped before `A`); base spec does not; legal instance | `CC.AuditF.Reads.forced_abort_row`, `CC.AuditF.Reads.forced_abort`, `CC.AuditF.Reads.Ex.base_keeps_commit`, `CC.AuditF.Reads.Ex.reads_rows`, `CC.AuditF.Reads.Ex.read_event_legal`, `CC.AuditF.Reads.Ex.writer_after_A` | Audit/MVTOReads |
| App. cc-bases (rewritten, spec with reads `(L,X,ρ)`): abort-free variant; `([A,B],∅,∅)`, `([B,A],∅,∅)` no common refinement, not monotone; comparable rows share `(L,X)`; 2PL bases | `CC.AuditF.Full.abortFreeFull`, `CC.AuditF.Full.full_no_common_refinement`, `CC.AuditF.Full.full_not_liftedMono`, `CC.AuditF.Full.abortFreeFull_not_liftedMono`, `CC.AuditF.Full.full_comparable_same_LX`, `CC.AuditF.Full.abortFreeFull_stable_lift`, `CC.AuditF.Full.basis2PL_R`, `CC.AuditF.Full.basis2PL_AF` | Audit/MVTOFull |
| App. cc-bases (rewritten): deadlock rows at every input, later outputs abort `A` or `B`; abort-free `order(B,A)` never defined; Fig. (h)/(i) on rows without aborts; MVTO abort required by the spec | `CC.AuditF.Full.deadlock_state_R`, `CC.AuditF.Full.deadlock_forces_abort_R`, `CC.AuditF.Full.abortFree_order_blocks_forever_R`, `CC.AuditF.Full.orderP_noabort`, `CC.AuditF.Full.stampP_first_noabort`, `CC.AuditF.Full.mvto_forced_abort` | Audit/MVTOFull |
| App. additional-applications: authority (order; safety ⇒ exposable; competing slot decisions / next epochs need a commitment) | `CC.AuditF.instPOAuth`, `CC.AuditF.safety_exposable`, `CC.AuditF.slot_conflict`, `CC.AuditF.epoch_conflict` | Audit/Applications |
| App. additional-applications: k-set agreement (general k) | `CC.AuditF.kset_single_row`, `CC.AuditF.kset_union_upper`, `CC.AuditF.kset_any_k`, `CC.AuditF.kset_all_fail`, `CC.AuditF.kset_not_commonExpansion`, `CC.AuditF.kset_not_liftedMono`, `CC.AuditF.kset_no_cap` | Audit/Applications |
| App. additional-applications: tight renaming | `CC.AuditF.ren_singleton_iff`, `CC.AuditF.ren_each_extends`, `CC.AuditF.ren_no_injective_extends_both`, `CC.AuditF.ren_not_directed`, `CC.AuditF.ren_no_cap` | Audit/Applications |
| App. additional-applications: snapshots (prefix spec monotone; complete-history spec functional, not monotone, needs a seal) | `CC.AuditF.prefix_mono`, `CC.AuditF.prefix_union`, `CC.AuditF.prefixSpec_liftedMono`, `CC.AuditF.prefix_empty`, `CC.AuditF.completeSpec_functional`, `CC.AuditF.completeSpec_not_monotone`, `CC.AuditF.completeSpec_seal_needed` | Audit/Applications |
| Fig. election-frames (d) "(b), then polls closed": the registrar's seal `closePolls` is a commitment and a seal; `Out_{[closePolls]}(⊥)` ends at the single row `(xy·,⊥)`, determined with result `⊥`; struck rows exactly `(xyx,x)`, `(xyy,y)`; `⊥` alone needs no commitment; table equals Fig. nonmonotone-frame; canonical equivalent run | `CC.AuditR.closePolls`, `CC.AuditR.closePolls_seals`, `CC.AuditR.Elec.registrar_step`, `CC.AuditR.Elec.panelD_rows`, `CC.AuditR.Elec.panelD_determined`, `CC.AuditR.Elec.panelD_struck`, `CC.AuditR.Elec.panelD_gray`, `CC.AuditR.Elec.bot_alone_at_b`, `CC.AuditR.Elec.panelD_matches_e`, `CC.AuditR.Elec.registrar_canonical` | Audit/Remaining |
| Fig. election-frames (a)–(c): printed outputs (exactly the rows ⪰ `x··`), upper fibers, panel (b) rows | `CC.AuditR.Elec.printed_rows`, `CC.AuditR.Elec.printed_complete`, `CC.AuditR.Elec.upper_ab`, `CC.AuditR.Elec.upper_c`, `CC.AuditR.Elec.panel_b`, `CC.AuditR.Elec.shown_inputs` | Audit/Remaining |
| Sec. discussion: decisive ballot (input retirement) vs. closing the polls (commitment); in the election they never leave the same result | `CC.AuditR.Elec.decisive_vs_close`, `CC.AuditR.Elec.determined_has_winner` | Audit/Remaining |
| Fig. ambiguity-frames (f): `[B,A]` rejected (not sealed/retired), not exposable, `c_[A,B]` applies with the input legal, incompatible / not monotone / not consistent, runs emitting `[A,B]` and `[B,A]` not confluent | `CC.AuditR.Txn.after_ab`, `CC.AuditR.Txn.ba_rejected`, `CC.AuditR.Txn.ab_not_exposable`, `CC.AuditR.Txn.choice_applies`, `CC.AuditR.Txn.not_monotone`, `CC.AuditR.Txn.runs_not_confluent` | Audit/Remaining |
| Fig. ambiguity-frames (g): remaining rows, removed rows retired, exposable; fiber union-closed and directed, monotone, consistent; union survives in both runs; state depends on outputs | `CC.AuditR.Trace.after_s1`, `CC.AuditR.Trace.removed_retired`, `CC.AuditR.Trace.union_mem`, `CC.AuditR.Trace.directed`, `CC.AuditR.Trace.union_survives`, `CC.AuditR.Trace.state_depends_on_outputs` | Audit/Remaining |
| App. deployment remark: system runs (`CC.CAP` local runs, any commitments) of a separable authorized family / partitioned-history cut have a common refinement in `S(j)` under monotonicity across partitions (via `canonical_equivalent`, `sysStep_iff_CAP`); `u` need not be authorized | `CC.AuditR.DeployR.lrun_sysExec`, `CC.AuditR.DeployR.SRun.canonical`, `CC.AuditR.DeployR.system_monoAcross`, `CC.AuditR.DeployR.history_monoAcross`, `CC.AuditR.DeployR.unauthorized_refinement` | Audit/Remaining |
| Sec. iconfluence-instance: Bailis et al. Def. 5/6 (I-T-reachability, common ancestor) ⇔ `IConfluent` | `CC.AuditR.IConfR.ReachFrom`, `CC.AuditR.IConfR.bailis_iff`, `CC.AuditR.IConfR.Anc`, `CC.AuditR.IConfR.s0_anc`, `CC.AuditR.IConfR.bailisAnc_iff`, `CC.AuditR.IConfR.reachPlus_iff` | Audit/Remaining |
