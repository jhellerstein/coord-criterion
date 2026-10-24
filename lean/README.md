# Lean formalization

Lean 4 (core only, no Mathlib), toolchain in `lean-toolchain`.
Build: `lake build` from this directory.  Every theorem below depends only on
the standard axioms (`propext`, `Quot.sound`, and in some cases
`Classical.choice`); there is no `sorry`.

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
| Table lookup-lift | `CC.Front.lookup_hull_i1`, `CC.Front.lookup_pruned_i1` | Frontiers |
| Prop. persistent-forwarding monotonicity; Eq. forwarding-hull | `CC.Front.persistent_forwarding`, `CC.Front.fwdSpec_consistent`, `CC.Front.forwarding_hull` | Frontiers |
| Def. monotone across partitions; Prop. partition compatibility (family level) | `CC.Front.MonoAcrossPartitions`, `CC.Front.partition_compat_iff` | Frontiers |
| Thm. independent-product frontier | `CC.Front.product_monoAcross`, `CC.Front.product_partition_compat`, `CC.Front.strengthening_not_monoAcross` | Frontiers |
| Example product-config (and injective-ownership counterexample) | `CC.Front.config_agreement_not_ok`, `CC.Front.agreement_ok_sole_owner` | Frontiers |
| Defs. deployment, separable family, monotone across partitions, deployment availability | `CC.Deploy.Separable`, `CC.Deploy.MonoAcrossPartitions`, `CC.Deploy.DeploymentAvailability` | Deployment |
| Prop. partition compatibility under a deployment | `CC.Deploy.partition_compatibility`, `CC.Deploy.partition_compatibility_confluent` | Deployment |
| Monotonicity ⇒ monotone across partitions; converse fails (leader election) | `CC.Deploy.monoAcrossPartitions_of_liftedMono`, `CC.Deploy.single_authority_monoAcross`, `CC.Deploy.leader_not_liftedMono`, `CC.Deploy.split_authority_not_monoAcross` | Deployment |
| Full deployment: pairs suffice, monotone across partitions ⇔ monotone; Deployment Availability = Availability | `CC.Deploy.ce_of_pairs`, `CC.Deploy.full_deployment_iff`, `CC.Deploy.deploymentAvailability_full` | Deployment |
| Lemma forced-answer | `CC.CAP.forced_answer` | CompleteCAP |
| Register spec: `Q_p` total and upward closed | `CC.GL.regQ_total`, `CC.GL.regQ_upward` | GilbertLynch |
| Realized history monotone in the prefix | `CC.GL.realized_mono` | GilbertLynch |
| Cor. Gilbert–Lynch | `CC.GL.gilbert_lynch`, `CC.GL.gilbert_lynch_full` | GilbertLynch |
| Counterexample: `h_C` need not expand the current inputs | `CC.GL.realized_not_expansion` | GilbertLynch |

Modeling choices are documented at the top of each file.
