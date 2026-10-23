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
| Thm. Complete CAP | `CC.CAP.complete_cap` | CompleteCAP |
| Thm. Complete CAP, response form | `CC.CAP.complete_cap_response` | CompleteCAP |
| Prop. invariant confluence ⇔ Lifted Monotonicity | `CC.IConf.ic_iff_liftedMono` | IConfluence |

Modeling choices are documented at the top of each file.
