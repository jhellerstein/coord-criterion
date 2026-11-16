import CoordCriterion.Appendix.Deployment
import CoordCriterion.Appendix.DeploymentExamples
import CoordCriterion.Appendix.DeploymentSystems
import CoordCriterion.Appendix.Registers
import CoordCriterion.Appendix.RealTimeCausal
import CoordCriterion.Appendix.RealTimeTies
import CoordCriterion.Appendix.MahajanRTC
import CoordCriterion.Appendix.DeploymentFor
import CoordCriterion.Appendix.DeploymentCAP

/-!
# Paper, Appendix E: Deployments: One Explicit Relation per Participant

Source: `appendices/deployment.tex` (Appendix `app:deployment`, including
subsections `app:registers` and `app:rtc`).

How to read this file: open it beside the appendix.  Every numbered result
and every claim the text proves or justifies appears below in paper order,
under a header naming the paper's (sub)section.  Numbered results carry their
LaTeX label (`«def:deployment»`, `«thm:complete-cap-deployment»`, …);
unlabeled inline claims are named `«<enclosing label>/<slug>»`.  Each
docstring quotes the paper (LaTeX lightly normalized to Unicode) and, where
the Lean statement reads differently, says how the two correspond.  Proofs are
one-line references to the library (`CoordCriterion/Appendix/Deployment*.lean`,
`ProductFrontier.lean`, `Registers.lean`).

Conventions used throughout (see `Appendix/Deployment.lean`, modeling
row-removing commitments):
* the participant set `𝒩` is `Fin n`; a deployment is `A : Fin n → Table I O`
  with `A p ⊆ P` (the paper's `E_p` is `A p`);
* a partition `Π` is a labelling `comp : Fin n → Nat` with at least two
  distinct labels (`IsPartition`); sides are the label classes;
* a participant run family is `F : Fin n → Option (PRun sp)`: participant `p`
  belongs to the family iff `F p = some m`, and `m` is a canonical run from
  `σ_P(m.init)`; `Emits F p r` says `p`'s run emits row `r = (i, o)`;
* "`j` is a common input extension of the participants' current inputs" is `UB F j`;
* "`u` extends `o`" is `o ≼ u`.
-/

namespace CC
namespace Paper

open CC.Deploy

set_option linter.unusedSectionVars false

section Deployment
variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {n : Nat}

/-! ## Appendix E: Deployments: One Explicit Relation per Participant -/

/-- **Definition `def:deployment`** (Deployment, emitted rows, partition).
"A *deployment* over a finite participant set `𝒩` assigns to each `p ∈ 𝒩` an
explicit relation `E_p ⊆ P`, the rows `p` may emit: `p` performs an output event `output(o)`
at current input `i` only if `(i,o) ∈ E_p`."

Lean: `Deployment sp n` has a field `A : Fin n → Table I O` (the paper's
`E_p` is `A p`) and a proof `sub : A p ⊆ P`.  The restriction on output events is imposed where families
are used (`Authorized`). -/
abbrev «def:deployment» (sp : Spec I O) (n : Nat) : Type := CC.Deploy.Deployment sp n

/-- Def. `def:deployment`: "Emitted rows are as in Definition
`def:emitted-rows`" ("the pairs `(i,o)` such that the run emits `o` at current
input `i`").  For a canonical run of one
participant these are `m.rows`; along an event list they are computed by
`emitted`, which tracks the current input through input events. -/
theorem «def:deployment/emitted-rows» (m : PRun sp) (c j : I) (o : O)
    (es : List (Event I O)) :
    m.rows = emitted m.init m.es ∧
    emitted c ([] : List (Event I O)) = [] ∧
    emitted c (.input j :: es) = emitted j es ∧
    emitted c (.output o :: es) = (c, o) :: emitted c es :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Def. `def:deployment`: "A *partition* `Π` of `𝒩` divides `𝒩` into two or more nonempty sides."  A labelling `comp : Fin n → Nat` with two
participants on different sides. -/
theorem «def:deployment/partition» (comp : Fin n → Nat) :
    IsPartition comp ↔ ∃ p q, comp p ≠ comp q :=
  Iff.rfl

/-- **Definition `def:participant-run-family`** (Participant run family,
silent participant, separable run family).  "A *participant run family*
assigns to each of finitely many participants `p ∈ 𝒩` an initial input and a
canonical run whose emitted rows lie in `E_p`.  A participant whose run emits
no output is *silent*.  The family is *separable under `Π`* when either
participants on at least two sides emit, or exactly one distinct row is
emitted and some silent participant lies on another side."

Lean: a family is `Fin n → Option (PRun sp)`; `Authorized Dp F` enforces
"emitted rows lie in `E_p`"; `Silent F q` and `Separable F comp` carry the
rest. -/
abbrev «def:participant-run-family» (sp : Spec I O) (n : Nat) : Type := Family sp n

/-- Def. `def:participant-run-family`: `Authorized` captures the authorization
condition; `Silent` captures silence. -/
theorem «def:deployment/family» (Dp : Deployment sp n) (F : Family sp n) :
    (Authorized Dp F ↔ ∀ p r, Emits F p r → Dp.A p r.1 r.2) ∧
    (∀ q, Silent F q ↔ ∃ m, F q = some m ∧ m.rows = []) :=
  ⟨Iff.rfl, fun _ => Iff.rfl⟩

/-- Def. `def:participant-run-family`: "The family is *separable under `Π`*
when either participants on at least two sides emit, or exactly one distinct
row is emitted and some silent participant lies on another side." -/
theorem «def:deployment/separable» (F : Family sp n) (comp : Fin n → Nat) :
    Separable F comp ↔
      ((∃ p q r r', Emits F p r ∧ Emits F q r' ∧ comp p ≠ comp q) ∨
       (∃ r₀ p q, Emits F p r₀ ∧ (∀ p' r, Emits F p' r → r = r₀) ∧
          Silent F q ∧ comp q ≠ comp p)) :=
  Iff.rfl

/-- **Definition `def:monotone-across-partitions`** (Monotone across
partitions).  "Relative to a deployment, `P` is *monotone across `Π`* when,
for every participant run family separable under `Π` and every common
input extension `j` of its participants' current inputs, some `u ∈ P(j)` extends
every emitted output.  It is *monotone across partitions* when it is monotone across every partition of `𝒩`." -/
theorem «def:monotone-across-partitions» (Dp : Deployment sp n) :
    (∀ comp, MonoAcross Dp comp ↔
      ∀ F : Family sp n, Authorized Dp F → Separable F comp →
        ∀ j, UB F j → ∃ u, sp.P j u ∧ ∀ p r, Emits F p r → r.2 ≼ u) ∧
    (MonoAcrossPartitions Dp ↔ ∀ comp, IsPartition comp → MonoAcross Dp comp) :=
  ⟨fun _ => Iff.rfl, Iff.rfl⟩

/-- "If `P` satisfies Lifted Monotonicity for a relation that contains every `E_p`, it is monotone across partitions, since the emitted rows of a family are rows of that relation at inputs below `j`." -/
theorem «app:deployment/lm-for-implies-mono-across» (Dp : Deployment sp n)
    (B : Table I O) (hB : ∀ p i o, Dp.A p i o → B i o) (hc : CAP.ConsistentOn sp B) :
    MonoAcrossPartitions Dp :=
  monoAcrossPartitions_of_consistentOn Dp B hB hc

/-- "So Lifted Monotonicity for `E` suffices for the uniform deployment `E_p = E` …" -/
theorem «app:deployment/uniform-mono-across» (E : Table I O) (hES : ∀ i o, E i o → sp.P i o)
    (hc : CAP.ConsistentOn sp E) :
    MonoAcrossPartitions (Deployment.uniform (n := n) E hES) :=
  monoAcrossPartitions_uniform E hES hc

/-- "… and Lifted Monotonicity suffices for every deployment." -/
theorem «app:deployment/lm-implies-mono-across» (hlm : sp.LiftedMono)
    (Dp : Deployment sp n) : MonoAcrossPartitions Dp :=
  monoAcrossPartitions_of_liftedMono hlm Dp

/-- "Rows authorized only to `p` can be emitted only by `p`'s run, and the
outputs that run emits form a chain, since each output event keeps only rows
whose outputs extend it."  The chain is in emission order; its last row extends every emitted
output. -/
theorem «app:deployment/run-outputs-chain» (m : PRun sp) :
    List.Pairwise (fun a b : I × O => a.2 ≼ b.2) m.rows ∧
    (m.rows ≠ [] → ∃ r ∈ m.rows, ∀ r' ∈ m.rows, r'.2 ≼ r.2) :=
  ⟨rows_chain m, rows_max m⟩

/-- "So a family whose emitted rows are all authorized only to `p` is separable only when it emits a single row."  Lean: every emitter is `p` and
every emitted row is the same `r₀`; consequently two distinct rows make the
family non-separable. -/
theorem «app:deployment/sole-rows-single-row» (Dp : Deployment sp n) (F : Family sp n)
    (hA : Authorized Dp F) (p : Fin n)
    (honly : ∀ q r, Emits F q r → ∀ q', Dp.A q' r.1 r.2 → q' = p) (comp : Fin n → Nat) :
    (Separable F comp → ∃ r₀, ∀ q r, Emits F q r → q = p ∧ r = r₀) ∧
    (∀ q q' r r', Emits F q r → Emits F q' r' → r ≠ r' → ¬ Separable F comp) :=
  ⟨sole_rows_separable Dp F hA p honly comp,
   fun _ _ _ _ h1 h2 hne => sole_rows_two_not_separable Dp F hA p honly h1 h2 hne comp⟩

end Deployment

/-! ### The leader example -/

/-- "Let `𝒩 = {p,q}`, let every fiber be `{a,b}` ordered by equality, and let
`E_p = P` and `E_q = ∅`, so that `p` alone names a leader."

Lean: `leadSpec I` over any input poset `I`, outputs `Disc Bool` (equality
order; `a = ⟨false⟩`, `b = ⟨true⟩`); `leadD I` with `p = 0`, `q = 1`. -/
theorem «app:deployment/leader-example/setup» (I : Type) [PO I] :
    (∀ i o, (leadSpec I).P i o) ∧ (∀ i o, (leadD I).A 0 i o) ∧
    (∀ i o, ¬ (leadD I).A 1 i o) ∧ SingleAuthority (leadD I) 0 :=
  ⟨fun _ _ => trivial, fun _ _ => rfl, fun _ _ h => absurd h (by decide : ¬ ((1 : Fin 2) = 0)), leadD_single⟩

/-- "A run of `p` emits at most one distinct output …" -/
theorem «app:deployment/leader-example/one-output» {I : Type} [PO I]
    (m : PRun (leadSpec I)) : ∀ r ∈ m.rows, ∀ r' ∈ m.rows, r.2 = r'.2 :=
  lead_run_one_output m

/-- "… and `q` never emits.  Every separable family therefore consists of one
row `(i,a)` or `(i,b)` beside a silent `q`." -/
theorem «app:deployment/leader-example/separable-shape» {I : Type} [PO I]
    (F : Family (leadSpec I) 2) (hA : Authorized (leadD I) F) (comp : Fin 2 → Nat)
    (hs : Separable F comp) :
    ∃ r₀, (∀ q r, Emits F q r → q = 0 ∧ r = r₀) ∧ Emits F 0 r₀ ∧ Silent F 1 :=
  lead_separable_shape F hA comp hs

/-- "So `P` is monotone across partitions, yet `(i,a)` and `(i,b)` have no
common output extension, and Lifted Monotonicity fails."  (Any input `i` witnesses the
failure.) -/
theorem «app:deployment/leader-example» (I : Type) [PO I] (i : I) :
    MonoAcrossPartitions (leadD I) ∧ ¬ (leadSpec I).LiftedMono :=
  ⟨lead_monoAcross, lead_not_liftedMono i⟩

section Deployment2
variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {n : Nat}

/-- "The same happens whenever two conditions hold: each authorized row has an
output extension at every input extension of its input, and every set of
authorized rows that lacks a common output extension at some common input
extension is authorized only to a single participant."  Finite sets of rows are lists. -/
theorem «app:deployment/sufficient-condition» (Dp : Deployment sp n)
    (h1 : ∀ p i o, Dp.A p i o → ∀ j, i ≼ j → ∃ u, sp.P j u ∧ o ≼ u)
    (h2 : ∀ E : List (I × O), (∀ r ∈ E, ∃ p, Dp.A p r.1 r.2) → ∀ j, (∀ r ∈ E, r.1 ≼ j) →
      (¬ ∃ u, sp.P j u ∧ ∀ r ∈ E, r.2 ≼ u) →
      ∃ p, ∀ r ∈ E, ∀ q, Dp.A q r.1 r.2 → q = p) :
    MonoAcrossPartitions Dp :=
  monoAcross_of_sole_conflicts Dp h1 h2

end Deployment2

/-- "The causal register of Appendix `app:registers` is a further example of
monotonicity across partitions without Lifted Monotonicity, with no single
authority."

Lean: the two-write history signature `G2` with the replica deployment. -/
theorem «app:deployment/further-examples» :
    MonoAcrossPartitions (replicaD G2) ∧ ¬ (causalSpec G2).LiftedMono :=
  ⟨causal_monoAcross G2, causal_not_liftedMono⟩

/-- "It need not satisfy these conditions, since a set of rows lacking a
common output extension may also contain rows of other participants."  Witness: in
the configuration product interface, the rows `e_0(0)`, `e_0(1)`, `e_1(0)` are
authorized, lack a common output extension, and are not authorized to a single
participant. -/
theorem «app:deployment/further-examples/condition-fails» {I : Type} [PO I] (i : I) :
    let sp := prodSpec (W := fun _ => Front.Disc Bool) (cfgV I) cfgV_ne
    let E : List (I × PTd (fun _ : Fin 2 => Front.Disc Bool)) :=
      [(i, single1 0 ⟨false⟩), (i, single1 0 ⟨true⟩), (i, single1 1 ⟨false⟩)]
    (∀ r ∈ E, ∃ p, (ownerD sp).A p r.1 r.2) ∧
      (¬ ∃ u, sp.P i u ∧ ∀ r ∈ E, r.2 ≼ u) ∧
      ¬ ∃ p, ∀ r ∈ E, ∀ q, (ownerD sp).A q r.1 r.2 → q = p :=
  cfg_product_conflict i

section Deployment3
variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {n : Nat}

/-- "If `|𝒩| ≥ 2` and `E_p = P` for every `p`, every pair of rows can be split
across a partition, and every single row can be paired with a silent
participant at the common input extension.  Pairs of rows suffice for the
common-extension condition (Appendix `app:pairs-suffice`), so monotonicity
across partitions is then Lifted Monotonicity." -/
theorem «app:deployment/full-deployment» (hn : 2 ≤ n) (Dp : Deployment sp n)
    (hA : ∀ p, Dp.A p = sp.P) : MonoAcrossPartitions Dp ↔ sp.LiftedMono :=
  full_deployment_iff hn Dp hA

/-- The pairs-suffice step used above (Appendix `app:pairs-suffice`). -/
theorem «app:deployment/full-deployment/pairs-suffice»
    (h : ∀ i₁ o₁ i₂ o₂ j, sp.P i₁ o₁ → sp.P i₂ o₂ → i₁ ≼ j → i₂ ≼ j →
      ∃ u, sp.P j u ∧ o₁ ≼ u ∧ o₂ ≼ u) :
    sp.CommonExpansion :=
  ce_of_pairs h

/-- **Definition `def:deployment-availability`** (Deployment Availability).
"Relative to a deployment, a system has *Deployment Availability* when, in
every partitioned history over `𝒩` it produces, each participant `p` can emit
every output in `R(i) ∩ E_p(i)`, where `(i,R)` is `p`'s final state."

Lean: `DeploymentAvailabilityEnd`, unfolded below; it is equivalent to the cut
form `DeploymentAvailability` used by the library. -/
theorem «def:deployment-availability» {D : Type} (Sys : CAP.System sp D)
    (Dp : Deployment sp n) :
    (DeploymentAvailabilityEnd Sys Dp ↔
      ∀ (init : Fin n → I) (H : CAP.History sp D n) (comp : Fin n → Nat),
        CAP.WF init H → CAP.Produced Sys n init H → CAP.Partitioned H comp →
        ∀ (p : Fin n) (σ : State sp), CAP.LRun (canon sp (init p)) (H p) σ →
        ∀ o, σ.R σ.cur o → Dp.A p σ.cur o →
        ∃ ext : Fin n → List (CAP.LEv sp D n),
          CAP.WF init (fun q => H q ++ ext q) ∧ CAP.Produced Sys n init (fun q => H q ++ ext q) ∧
          CAP.Partitioned (fun q => H q ++ ext q) comp ∧
          (∀ q, comp q ≠ comp p → ext q = []) ∧
          (∀ q j, CAP.LEv.inp j ∉ ext q) ∧
          CAP.LEv.out o ∈ ext p) ∧
    (DeploymentAvailability Sys Dp ↔ DeploymentAvailabilityEnd Sys Dp) :=
  ⟨Iff.rfl, deploymentAvailability_iff_end Sys Dp⟩

/-- "This is Availability for `E_p`, one relation per participant.  For the
uniform deployment `E_p = E` it is Availability for `E` on histories over
`𝒩` …"  `AvailabilityForAt E Sys n` is `CAP.AvailabilityFor E` restricted to
histories over `Fin n`. -/
theorem «app:deployment/uniform-availability» {D : Type} (Sys : CAP.System sp D)
    (E : Table I O) (hES : ∀ i o, E i o → sp.P i o) :
    (DeploymentAvailabilityEnd Sys (Deployment.uniform (n := n) E hES) ↔
      AvailabilityForAt E Sys n) ∧
    (CAP.AvailabilityFor E Sys ↔ ∀ m, AvailabilityForAt E Sys m) :=
  ⟨deploymentAvailability_uniform Sys E hES, availabilityFor_iff_at E Sys⟩

/-- "… and for `E_p = P` it is Availability."  `AvailabilityAt Sys n` is
`CAP.Availability` restricted to histories over `Fin n`
(`CAP.Availability Sys ↔ ∀ n, AvailabilityAt Sys n`). -/
theorem «app:deployment/full-deployment-availability» {D : Type} (Sys : CAP.System sp D)
    (Dp : Deployment sp n) (hA : ∀ p, Dp.A p = sp.P) :
    (DeploymentAvailabilityEnd Sys Dp ↔ AvailabilityAt Sys n) ∧
    (CAP.Availability Sys ↔ ∀ m, AvailabilityAt Sys m) :=
  ⟨(deploymentAvailability_iff_end Sys Dp).symm.trans (deploymentAvailability_full Sys Dp hA),
    availability_iff Sys⟩

/-! ### Single-authority deployments -/

/-- "A deployment is *single-authority* when `E_q = ∅` for every participant
`q` but one, as in the leader example above." -/
theorem «app:deployment/single-authority/def» (Dp : Deployment sp n) (p₀ : Fin n) :
    SingleAuthority Dp p₀ ↔ ∀ q, q ≠ p₀ → ∀ i o, ¬ Dp.A q i o :=
  Iff.rfl

/-- "Every separable family is then one row emitted by the single authority
beside a silent participant …" -/
theorem «app:deployment/single-authority/shape» (Dp : Deployment sp n) (p₀ : Fin n)
    (hSA : SingleAuthority Dp p₀) (F : Family sp n) (hA : Authorized Dp F)
    (comp : Fin n → Nat) (hs : Separable F comp) :
    ∃ r₀, (∀ q r, Emits F q r → q = p₀ ∧ r = r₀) ∧ Emits F p₀ r₀ ∧
      ∃ q, Silent F q ∧ comp q ≠ comp p₀ :=
  single_authority_shape Dp p₀ hSA F hA comp hs

/-- "… so monotonicity across partitions says only that each such row has an
output extension at every input extension of its input."  (With `|𝒩| ≥ 2`, so that some
partition exists.) -/
theorem «app:deployment/single-authority» (hn : 2 ≤ n) (Dp : Deployment sp n) (p₀ : Fin n)
    (hSA : SingleAuthority Dp p₀) :
    MonoAcrossPartitions Dp ↔ ∀ i o, Dp.A p₀ i o → ∀ j, i ≼ j → ∃ u, sp.P j u ∧ o ≼ u :=
  single_authority_iff hn Dp p₀ hSA

/-- "The deployment keeps the conflicting choice from being made at another
participant …"  Lean: if only participant `0` may perform output events,
no row that an output event removes by its canonical commitment is emitted, at
the same input, by another participant of the same history. -/
theorem «app:deployment/single-authority/not-distributed» {D : Type} (Sys : CAP.System sp D)
    (hsole : ∀ n init (p : Fin n) pre o, Sys.strat n init p pre (CAP.LEv.out o) → p.val = 0) :
    RowRemovalsNotDistributed Sys :=
  sole_emitter_rowRemovals Sys hsole

/-- "… but it does not change the semantic conflict: a canonical run still
conflicts with the authority's commitment.  For example, another canonical run
of the spec conflicts with a lock manager's choice even when only the manager
is authorized to emit the result."  Lean: the owner system's row-removing event is
a commitment, and the library's operational predicates record that the conflict
is local rather than cross-participant. -/
theorem «app:deployment/single-authority/coordination» (D : Type) :
    ¬ Exposable (canon CAP.ordSpec ()) .ab ∧ ¬ (CAP.ownerSys D).CoordinationFree ∧
      (CAP.ownerSys D).CoordinationFreeH :=
  ⟨CAP.ordSpec_ab_not_exposable, CAP.ownerSys_not_coordinationFree D,
    CAP.ownerSys_coordinationFreeH D⟩

/-! ### Proposition `thm:complete-cap-deployment` -/

/-- **Proposition `thm:complete-cap-deployment`** (Partition compatibility
under a deployment).  "Fix a deployment.  The following are equivalent.
(1) For every partition `Π`, every participant run family separable under
`Π` is confluent at every common input extension `j` of its participants' current
inputs.  (2) `P` is monotone across partitions."

Lean: item (1) is `PartitionConfluent Dp`, written out on the left;
`famStates F` lists the final states of the family's runs, and `ConfluentAt`
is confluence of runs ending there at `j`. -/
theorem «thm:complete-cap-deployment» (Dp : Deployment sp n) :
    (∀ comp : Fin n → Nat, IsPartition comp →
      ∀ F : Family sp n, Authorized Dp F → Separable F comp →
        ∀ j, UB F j → ConfluentAt (famStates F) j) ↔
    MonoAcrossPartitions Dp :=
  partition_compatibility_confluent Dp

/-- Proof of Prop. `thm:complete-cap-deployment`: "By Lemma
`lem:reconciliation`, the family is confluent at `j` if and only if some
`u ∈ P(j)` extends every output in `X`.  The two conditions thus agree family
by family."  Lean: the per-family step in survivor form (some row at `j`
survives in every remainder table iff the emitted outputs have a common
input extension in `P(j)`), and the proposition in survivor form. -/
theorem «thm:complete-cap-deployment/proof» (Dp : Deployment sp n) :
    (∀ (F : Family sp n) (j : I), UB F j →
      ((∃ u, sp.P j u ∧ ∀ p m, F p = some m → m.fin.R j u) ↔
        (∃ u, sp.P j u ∧ ∀ p r, Emits F p r → r.2 ≼ u))) ∧
    (PartitionSurvivor Dp ↔ MonoAcrossPartitions Dp) :=
  ⟨fun F _ hj => survivor_iff_compatible F hj, partition_compatibility Dp⟩

/-- "The proposition concerns canonical runs and does not use Deployment
Availability.  It also applies to the runs of a system: by Lemma
`lem:canonical-equivalent`, each such run is observably equivalent to a
canonical run with the same emitted rows, which therefore lie in `E_p`."

Lean: a system participant run (`SRun`: a `CAP` local run from a canonical
state, with sends, receives and output events carrying arbitrary commitments)
has a canonical run with the same emitted rows and current input. -/
theorem «app:deployment/system-runs/canonical» {D : Type} {m : Nat} (r : SRun sp D m) :
    ∃ q : PRun sp, q.rows = r.rows ∧ q.fin.cur = r.fin.cur :=
  r.canonical

/-- "So if `P` is monotone across partitions, the outputs that a separable
family of system runs emits in a partitioned history, as Deployment
Availability permits, have a common output extension `u ∈ P(j)` at every common
input extension `j`."

Lean: first for any separable authorized family of system runs (under `Π`),
then for the participants' runs to a cut of a history partitioned by `comp`. -/
theorem «app:deployment/system-runs» {D : Type} {m : Nat} (Dp : Deployment sp n) :
    (∀ {comp : Fin n → Nat}, MonoAcross Dp comp →
      ∀ F : SFamily sp D m n, SAuthorized Dp F → SSeparable F comp →
        ∀ j, SUB F j → ∃ u, sp.P j u ∧ ∀ p r, SEmits F p r → r.2 ≼ u) ∧
    (MonoAcrossPartitions Dp →
      ∀ (init : Fin n → I) (H : CAP.History sp D n) (comp : Fin n → Nat),
        CAP.Partitioned H comp → ∀ (c : Fin n → Nat) (σ : Fin n → State sp)
        (hσ : ∀ p, CAP.LRun (canon sp (init p)) ((H p).take (c p)) (σ p)),
        SSeparable (fun p => some ⟨init p, (H p).take (c p), σ p, hσ p⟩) comp →
        (∀ p r, r ∈ emittedL (init p) ((H p).take (c p)) → Dp.A p r.1 r.2) →
        ∀ j, (∀ p, (σ p).cur ≼ j) →
        ∃ u, sp.P j u ∧ ∀ p r, r ∈ emittedL (init p) ((H p).take (c p)) → r.2 ≼ u) :=
  ⟨fun hmono F ha hs j hj => system_monoAcross Dp hmono F ha hs j hj,
   fun hmono init H comp hP c σ hσ hsep hauth j hj =>
     history_monoAcross Dp hmono init H comp hP c σ hσ hsep hauth j hj⟩

end Deployment3

/-! ### Complete CAP for a deployment -/

section DeploymentCAP
variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {n : Nat}

/-- **Lemma `lem:deployment-compatible`** (Compatibility of participant run
families).  "Fix a deployment with `|𝒩| ≥ 2`.  Then `P` is monotone across
partitions if and only if, for every participant run family and every common
input extension `j` of its participants' current inputs, some `u ∈ P(j)`
extends every emitted output."  (Introduced by: "Proposition
`thm:complete-cap-deployment` concerns runs.  For systems, a deployment has its
own form of Complete CAP.  It rests on one more fact about families: with two
or more participants, monotonicity across partitions already covers every
family, separable or not.")

Proof sketch: "If participants `p` and `q` both emit, a partition with `p` on
one side and `q` on the other makes the family separable, and the separable
case applies.  Otherwise one participant `p` emits.  Its outputs form a chain,
so the last of them extends the rest.  Its last row, beside any other
participant placed on another side and kept silent, is a separable family at
the same `j`, and the common output extension for that row extends every output
of `p`."  Lean: `Deploy.monoAcrossPartitions_iff_compatible` (the hard
direction is `Deploy.compatible_of_monoAcrossPartitions`). -/
theorem «lem:deployment-compatible» (hn : 2 ≤ n) (Dp : Deployment sp n) :
    MonoAcrossPartitions Dp ↔
      ∀ F : Family sp n, Authorized Dp F → ∀ j, UB F j →
        ∃ u, sp.P j u ∧ ∀ p r, Emits F p r → r.2 ≼ u :=
  monoAcrossPartitions_iff_compatible hn Dp

/-- "The *canonical system* of a deployment is the system whose participants
follow canonical runs, each participant `p` emitting any output of `E_p` at its
current input that extends its earlier outputs."  Lean: `Deploy.depSystem`,
in which participant `p` runs the canonical response strategy for `E_p`
(`CAP.respSystem (Dp.A p)`); it is canonical (`Deploy.depSystem_canonical`). -/
noncomputable abbrev «app:deployment/canonical-system» (D : Type) (Dp : Deployment sp n) :
    CAP.System sp D :=
  depSystem Dp

/-- **Proposition `prop:deployment-complete-cap`** (Complete CAP for a
deployment).  "Fix a deployment with `|𝒩| ≥ 2`.  Some system has Deployment
Availability and Partition Consistency on histories over `𝒩` if and only if
`P` is monotone across partitions.  When it is, the deployment's canonical
system is such a system."  Lean: Partition Consistency on histories over `𝒩`
is `Deploy.PartitionConsistencyAt Sys n`; `Deploy.deployment_complete_cap_iff`
and `Deploy.deployment_complete_cap`. -/
theorem «prop:deployment-complete-cap» (D : Type) (hn : 2 ≤ n) (Dp : Deployment sp n) :
    ((∃ Sys : CAP.System sp D, DeploymentAvailability Sys Dp ∧ PartitionConsistencyAt Sys n) ↔
      MonoAcrossPartitions Dp) ∧
    (MonoAcrossPartitions Dp →
      DeploymentAvailability (depSystem (D := D) Dp) Dp ∧
        PartitionConsistencyAt (depSystem (D := D) Dp) n) :=
  ⟨deployment_complete_cap_iff hn Dp, deployment_complete_cap hn Dp⟩

/-- Proof of Prop. `prop:deployment-complete-cap`, sufficiency: "The canonical
system has Deployment Availability, since each participant can emit any
authorized output that its state allows.  Its participants' runs in a
partitioned history form a participant run family, so by Lemma
`lem:deployment-compatible` their emitted outputs have a common output
extension in `P(j)`.  By Lemma `lem:reconciliation` the runs are then confluent
at `j`, which is Partition Consistency."  Lean:
`Deploy.depSystem_availability` (for every deployment) and
`Deploy.depSystem_pc`. -/
theorem «prop:deployment-complete-cap/proof-sufficiency» (D : Type) (hn : 2 ≤ n)
    (Dp : Deployment sp n) :
    DeploymentAvailability (depSystem (D := D) Dp) Dp ∧
      (MonoAcrossPartitions Dp → PartitionConsistencyAt (depSystem (D := D) Dp) n) :=
  ⟨depSystem_availability Dp, depSystem_pc hn Dp⟩

/-- Proof of Prop. `prop:deployment-complete-cap`, necessity: "Each
participant's emitted outputs form a chain, so it suffices to reach each
participant's last emitted row.  We start each participant alone on its own
side, at the input of that row.  Deployment Availability lets it emit the row's
output, and Partition Consistency gives the emitted outputs a common output
extension in `P(j)`."  Lean: `Deploy.authorized_reconciled` (each participant
`p` starts at `init p` and emits an authorized `o p`, or nothing), then
`Deploy.compatible_of_system` for families. -/
theorem «prop:deployment-complete-cap/proof-necessity» {D : Type} (hn : 2 ≤ n)
    {Dp : Deployment sp n} (Sys : CAP.System sp D)
    (hDA : DeploymentAvailability Sys Dp) (hPC : PartitionConsistencyAt Sys n) :
    (∀ (init : Fin n → I) (o : Fin n → Option O), (∀ p v, o p = some v → Dp.A p (init p) v) →
      ∀ j : I, (∀ p, init p ≼ j) → ∃ u, sp.P j u ∧ ∀ p v, o p = some v → v ≼ u) ∧
    (∀ F : Family sp n, Authorized Dp F → ∀ j, UB F j →
      ∃ u, sp.P j u ∧ ∀ p r, Emits F p r → r.2 ≼ u) :=
  ⟨fun init o ho j hj => authorized_reconciled hn Sys hDA hPC init o ho j hj,
   fun F hA j hj => compatible_of_system hn Sys hDA hPC F hA j hj⟩

end DeploymentCAP

/-- "It does not follow that the deployment authorizes any participant to emit
`u`.  Confluence through authorized output events would also require that
authority, a condition we do not impose."

Lean witness: one input, fiber `{a, b, top}` with `a, b < top` (`CAP.triSpec`),
`E_0 = {a}`, `E_1 = {b}`: the specification is monotone across partitions, the
family "`0` emits `a`, `1` emits `b`" is authorized and separable, its only
common output extension is `top`, and no participant may emit `top`. -/
theorem «app:deployment/unauthorized-refinement» :
    MonoAcrossPartitions triD ∧
    ∃ (F : Family CAP.triSpec 2) (comp : Fin 2 → Nat), IsPartition comp ∧
      Authorized triD F ∧ Separable F comp ∧ UB F () ∧
      (∀ u, (∀ p r, Emits F p r → r.2 ≼ u) → u = .top) ∧ ∀ p, ¬ triD.A p () .top :=
  unauthorized_refinement

/-- "With `|𝒩| ≥ 2` and `E_p = P` for every `p`, item (2) is Lifted
Monotonicity.  The proposition is then the step behind Theorem
`thm:complete-cap` with `E = P`: separable families are confluent at every
common input extension exactly when Lifted Monotonicity holds." -/
theorem «app:deployment/full-deployment-step» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    {n : Nat} (hn : 2 ≤ n) (Dp : Deployment sp n) (hA : ∀ p, Dp.A p = sp.P) :
    PartitionConfluent Dp ↔ sp.LiftedMono :=
  (partition_compatibility_confluent Dp).trans (full_deployment_iff hn Dp hA)

/-! ## Appendix E.1: Registers (`app:registers`) -/

/-! ### The causal register -/

section Registers
variable {α : Type} {n : Nat}

/-- "An input is a finite operation history `h`: a set of reads and writes of
one register `x` at replicas, with a strict partial order `→` of causal
precedence."  Lean: `Hist α` (operations of type `α`, finite membership,
strict partial order `hb`); replicas and kinds are given by an `OpSig α n`
(`rep`, `isW`). -/
abbrev «app:registers/history» (α : Type) : Type := Hist α

/-- "We set `h ⊑ h'` when the operations of `h` form a causally closed subset
of `h'` and `→` restricted to them is the order of `h`." -/
theorem «app:registers/history-order» (h h' : Hist α) :
    h ≼ h' ↔ ((∀ a, h.mem a → h'.mem a) ∧ (∀ a b, h'.hb a b → h.mem b → h.mem a) ∧
      (∀ a b, h.mem a → h.mem b → (h'.hb a b ↔ h.hb a b))) :=
  Iff.rfl

/-- "Thus an input extension never adds an operation to the causal past of an
existing one." -/
theorem «app:registers/no-new-past» {h h' : Hist α} (hle : h ≼ h') {a b : α}
    (hab : h'.hb a b) (hb : h.mem b) : h.mem a :=
  no_new_past hle hab hb

/-- "An output is a *source map* `ρ`: a partial map assigning to some reads of
`h` a write of `h` or the initial value `v₀`, ordered by extension."  Lean:
`SMap α` with `f r = none` (undefined), `some none` (`v₀`), `some (some w)`;
"reads/writes of `h`" is `WellDom`. -/
theorem «app:registers/source-map» (G : OpSig α n) (h : Hist α) (ρ ρ' : SMap α) :
    (ρ ≼ ρ' ↔ ∀ r s, ρ.f r = some s → ρ'.f r = some s) ∧
    (WellDom G h ρ ↔ ∀ r s, ρ.f r = some s →
      h.mem r ∧ G.isW r = false ∧ ∀ w, s = some w → h.mem w ∧ G.isW w = true) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- "A *serialization* for replica `p` is a total order of `p`'s operations and
all writes of `h` that extends `→`; it explains a read of `p` with source `w`
when `w` is the last write before the read, or `v₀` if there is none." -/
theorem «app:registers/serialization» (G : OpSig α n) (h : Hist α) (p : Fin n)
    (lt : α → α → Prop) (r w : α) :
    (Ser G h p lt ↔ STO (Dom G h p) lt ∧ Ext h.hb (Dom G h p) lt) ∧
    (Explains G h lt r none ↔ ∀ w, h.mem w → G.isW w = true → ¬ lt w r) ∧
    (Explains G h lt r (some w) ↔ h.mem w ∧ G.isW w = true ∧ lt w r ∧
        ∀ w', h.mem w' → G.isW w' = true → lt w' r → w' = w ∨ lt w' w) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- "Under causal consistency, `ρ ∈ P(h)` when each replica has a
serialization explaining every read of that replica in the domain of `ρ`.
Under linearizability, a single total order of all operations of `h`
extending `→` must explain every read in the domain." -/
theorem «app:registers/fibers» (G : OpSig α n) (h : Hist α) (ρ : SMap α) :
    ((causalSpec G).P h ρ ↔ WellDom G h ρ ∧ ∀ p, ∃ lt, Ser G h p lt ∧
      ∀ r s, ρ.f r = some s → G.rep r = p → Explains G h lt r s) ∧
    ((linSpec G).P h ρ ↔ WellDom G h ρ ∧ ∃ lt, STO h.mem lt ∧ Ext h.hb h.mem lt ∧
      ∀ r s, ρ.f r = some s → Explains G h lt r s) :=
  ⟨Iff.rfl, Iff.rfl⟩

end Registers

/-! ### The two-write history -/

/-- "Participant `p` completes `w_p(x,dog)` while `q` concurrently completes
`w_q(x,cat)`; … each serves a local read, `r_p` at `p` and `r_q` at `q`.  Both
writes causally precede both reads, and the writes are concurrent."

Lean: operations `0 = w_p`, `1 = w_q`, `2 = r_p`, `3 = r_q` (signature `G2`,
replicas `p = 0`, `q = 1`), history `h2`. -/
theorem «app:registers/two-write-history» :
    h2.hb 0 2 ∧ h2.hb 0 3 ∧ h2.hb 1 2 ∧ h2.hb 1 3 ∧ ¬ h2.hb 0 1 ∧ ¬ h2.hb 1 0 :=
  h2_shape

/-- "Under linearizability, a source map that sends `r_p` to `w_q(x,cat)` needs
a linearization with `w_p(x,dog)` before `w_q(x,cat)`, and one that sends `r_q`
to `w_p(x,dog)` needs the opposite order.  No source map extends
both, so the register is not monotone across the partition `{{p},{q}}` under
any deployment authorizing these two reads."

Lean: `ρ1 = (r_p ↦ w_q)`, `ρ2 = (r_q ↦ w_p)` are linearizable; no single
linearization explains both; the partition `{{p},{q}}` is `comp = Fin.val`. -/
theorem «app:registers/linearizable-not-monotone-across» :
    (linSpec G2).P h2 ρ1 ∧ (linSpec G2).P h2 ρ2 ∧
    (∀ T, STO h2.mem T → Ext h2.hb h2.mem T →
      Explains G2 h2 T 2 (some 1) → Explains G2 h2 T 3 (some 0) → False) ∧
    ∀ Dp : Deployment (linSpec G2) 2, Dp.A 0 h2 ρ1 → Dp.A 1 h2 ρ2 →
      ¬ MonoAcross Dp (fun p => p.val) :=
  ⟨lin_ρ1', lin_ρ2', fun _ hT hE h1 h2 => no_lin_both hT hE h1 h2,
   fun Dp h0 h1 => lin_not_monoAcross Dp h0 h1⟩

/-- "Under causal consistency the two replicas may serialize the concurrent
writes differently, so one source map sends `r_p` to `w_q(x,cat)` and `r_q`
to `w_p(x,dog)`." -/
theorem «app:registers/causal-two-write» : (causalSpec G2).P h2 ρ12 :=
  causal_two_write

section Registers2
variable {α : Type} {n : Nat}

/-- "More generally, consider the deployment in which each replica answers
only its own reads (`E_p` holds the rows whose source map is defined only on
reads of `p`).  Under it the causal register is monotone across partitions, for
every history. … Separability
is not used."

Lean: `replicaD G`; the statement holds for every signature `G` (hence every
history), and the common output extension exists for every authorized family,
separable or not.  By Prop. `thm:complete-cap-deployment` the separable
families are confluent. -/
theorem «app:registers/causal-monotone-across» (G : OpSig α n) :
    (∀ p h ρ, (replicaD G).A p h ρ ↔ CausalFib G h ρ ∧ ∀ r s, ρ.f r = some s → G.rep r = p) ∧
    (∀ F : Family (causalSpec G) n, Authorized (replicaD G) F → ∀ j, UB F j →
      ∃ u, CausalFib G j u ∧ ∀ p r, Emits F p r → r.2 ≼ u) ∧
    MonoAcrossPartitions (replicaD G) ∧ PartitionConfluent (replicaD G) :=
  ⟨fun _ _ _ => Iff.rfl, fun F hA j hj => causal_common G F hA j hj,
   causal_monoAcross G, causal_confluent G⟩

/-- Proof step: "We take a serialization `L_p` of `i_p` explaining `ρ_p`, and
extend it to `j` by appending the new operations of `p` and the new writes in
any order extending `→`.  Since no new operation causally precedes an old one,
the result extends `→` and explains the same reads."  (The appended order is
built from a linear extension of a finite strict partial order, `linExt`.) -/
theorem «app:registers/serialization-extends» (G : OpSig α n) {h j : Hist α} (hle : h ≼ j)
    {p : Fin n} {lt : α → α → Prop} (hs : Ser G h p lt) :
    ∃ lt', Ser G j p lt' ∧ ∀ r s, Dom G h p r → Explains G h lt r s → Explains G j lt' r s :=
  ser_extend G hle hs

/-- Supporting fact: every strict partial order has a linear extension on
every finite set (finite sets are those enumerated by a list). -/
theorem «app:registers/linear-extension» (r : α → α → Prop) (hirr : ∀ a, ¬ r a a)
    (htr : ∀ a b c, r a b → r b c → r a c) (l : List α) (M : α → Prop)
    (hM : ∀ a, M a → a ∈ l) : ∃ lt, STO M lt ∧ Ext r M lt :=
  linExt r hirr htr l M hM

end Registers2

/-- "Two answers to the same read remain incompatible, but only the reading
replica may emit either."  The causal register is not monotone: `r_p ↦ w_p` and
`r_p ↦ w_q` are both causal outputs at the two-write history and have no
common output extension; both are authorized only to `p` under `replicaD`. -/
theorem «app:registers/same-read-incompatible» :
    (causalSpec G2).P h2 ρa ∧ (causalSpec G2).P h2 ρ1 ∧ ¬ (causalSpec G2).LiftedMono :=
  ⟨causal_ρa, causal_ρ1, causal_not_liftedMono⟩

/-! ## Appendix E.2: Real-time causal consistency (`app:rtc`) -/

section RTC
variable {α : Type} {n : Nat}

/-- "[A] system can provide real-time causal consistency, but no stronger
consistency, while staying always available … and one-way convergent …  We
recover both parts with real-time precedence recorded in the input."  (First
paragraph of `app:rtc`, on the theorem of Mahajan et al.)

Lean: their Theorem 3.1 ("no consistency semantics stronger than real time
causal consistency can be implemented using a one-way convergent and always
available distributed storage implementation"), derived from ours.  Let `T`
be strict (stronger than RTC) and real-time blind (does not observe real
time), and let `Sys` be any system for `T`'s specification with Deployment
Availability under the owner deployment (always available; one-way
convergence is in the input).  Then `Sys` produces a partitioned,
message-free history where every replica emits a real-time causal view at one
input `i` and `T` rejects the combined execution `y`, so `Sys` lacks Partition
Consistency.  The same holds for an implementation that does not observe real
time.  The proof is carried by Prop. `prop:rtc-maximal` (its step
`rtc_locCons`) and Theorem `thm:product-frontier`(2) in witness form
(`strengthening_witness`); Deployment Availability runs that theorem's
separable family in the system (`da_realize`). -/
theorem «app:rtc/mahajan» (G : OpSig α n) (hn : 2 ≤ n)
    (T : NormStr (W := fun _ => SMap α) (RView G))
    (sp : Spec (RHist G) (PTd (fun _ : Fin n => SMap α)))
    (hsp : ∀ i x, sp.P i x ↔ T.table i x) (hbl : RBlind T) (hst : T.Strict)
    {D : Type} (Sys : CAP.System sp D) (hDA : DeploymentAvailability Sys (ownerD sp)) :
    (∃ (i : RHist G) (y : Fin n → SMap α) (H : CAP.History sp D n),
      (∀ p, RView G p i (y p)) ∧ ¬ T.sel i y ∧
      CAP.WF (fun _ => i) H ∧ CAP.Produced Sys n (fun _ => i) H ∧
      CAP.Partitioned H (fun p => p.val) ∧
      (∀ p q k j d, CAP.LEv.recv q k j d ∉ H p) ∧ (∀ p j, CAP.LEv.inp j ∉ H p) ∧
      (∀ p, CAP.LEv.out (restrictTo y p) ∈ H p) ∧
      ¬ ∃ u, sp.P i u ∧ ∀ p, restrictTo y p ≼ u) ∧
    ¬ CAP.PartitionConsistency Sys :=
  ⟨mahajan_rtc hn T sp hsp hbl hst Sys hDA,
   mahajan_rtc_not_partitionConsistency hn T sp hsp hbl hst Sys hDA⟩

/-- The "no stronger consistency" part for an implementation that does not observe real time:
if its strengthening is strict and its specification is total, no system for
it with Deployment Availability has Partition Consistency. -/
theorem «app:rtc/mahajan-impl» (G : OpSig α n) (hn : 2 ≤ n) (Im : MImpl G)
    (hrt : Im.NoRealTime) (sp : Spec (RHist G) (PTd (fun _ : Fin n => SMap α)))
    (hsp : ∀ i x, sp.P i x ↔ Im.str.table i x) (hst : Im.str.Strict)
    {D : Type} (Sys : CAP.System sp D) (hDA : DeploymentAvailability Sys (ownerD sp)) :
    ¬ CAP.PartitionConsistency Sys :=
  mahajan_rtc_impl hn Im hrt sp hsp hst Sys hDA

/-- **Theorem `thm:product-frontier`** (Independent products).  "(1) If views
continue (for `i ⊑ j` and `v ∈ V_p(i)` some `w ∈ V_p(j)` has `v ≤_p w`), the
product interface is monotone across partitions under the owner deployment.
(2) No strict, locally conservative strengthening is monotone across
partitions under its owner deployment."

Lean: participants `Fin n` with `2 ≤ n` for part (2); views `V p i` nonempty
(`hne`), an antichain at each input (`Antichain`); a strengthening is
`NormStr V` and `sp` any specification whose table is its table. -/
theorem «thm:product-frontier» {I : Type} [PO I] {W : Fin n → Type} [∀ p, PO (W p)]
    (V : (p : Fin n) → I → W p → Prop) (hne : ∀ p i, ∃ v, V p i v) :
    (Continue V → MonoAcrossPartitions (ownerD (prodSpec V hne))) ∧
    (2 ≤ n → Antichain V → ∀ (T : NormStr V) (sp : Spec I (PTd W)),
      (∀ i x, sp.P i x ↔ T.table i x) → T.LocCons → T.Strict →
      ¬ MonoAcrossPartitions (ownerD sp)) :=
  ⟨fun hc => product_monoAcross V hne hc,
   fun hn hAC T sp hsp hLC hst => strengthening_not_monoAcross hn V hAC T sp hsp hLC hst⟩

/-- "Consider the histories of Appendix `app:registers` with a second strict
partial order `≺`: `a ≺ b` when `a` ended before `b` began.  We assume that
`a → b` implies `a ≺ b`, so replicas propagate only completed writes, and that
`→` totally orders the operations of each replica.  One input extends another
when it does so as a history and `≺` agrees on the old operations."

Lean: `RHist G` (fields `rt`, `hb_rt`, `po`) and its order. -/
theorem «app:rtc/input» (G : OpSig α n) (i j : RHist G) :
    (i ≼ j ↔ i.h ≼ j.h ∧ ∀ a b, i.h.mem a → i.h.mem b → (j.rt a b ↔ i.rt a b)) ∧
    (∀ a b, i.h.hb a b → i.rt a b) ∧
    (∀ a b, i.h.mem a → i.h.mem b → G.rep a = G.rep b → a ≠ b → i.h.hb a b ∨ i.h.hb b a) :=
  ⟨Iff.rfl, i.hb_rt, i.po⟩

/-- "A *real-time causal view* of replica `p` assigns to every read `r` of `p`
a source `s(r)` such that (1) `s(r)` is a write visible to `r`, or `v₀` if none
is; (2) `s(r) ⊀ w` for every write `w` visible to `r`; (3) if `r' → r` is a
read of `p` to which `s(r)` is visible, then `s(r') = s(r)`."

Lean: `RView G p i v`; (1) and (2) are `RSrc`, (3) is `RMono`. -/
theorem «app:rtc/views» (G : OpSig α n) (p : Fin n) (i : RHist G) (v : SMap α) :
    RView G p i v ↔ (∀ r, (∃ s, v.f r = some s) ↔ PRead G i.h p r) ∧
      (∀ r s, v.f r = some s → RSrc G i r s) ∧ RMono G i p v :=
  Iff.rfl

/-- "Intuitively, these are Mahajan et al.'s checks for the order that `p`'s
reads expose, in which each visible write precedes the read and each
overwritten write precedes the source.  Item (1) says a replica returns only
writes it has received, (2) is their real-time check 'time doesn't travel
backward', and (3) keeps one replica's overwrites consistent."

Lean (`Appendix/MahajanRTC.lean`): `HBCheck i p v HB` is Mahajan et al.'s RTC
check (TR-11-22, §2.1) for `p`'s reads: `HB` is a strict partial order with
CC1 (one replica's operations ordered by program order), "each visible write
precedes the read" (`vis`, their Lemma 3.2), CC2 with writeList `{s(r)}`
(`∅` for `v₀`), CC3 ("time doesn't travel backward": `a ≺ b → ¬ HB b a`), and
"only received writes are returned" (`rcv`, their Lemma 3.3).  The views are
exactly the source maps of `p`'s reads passing the check.  The order is
`→` plus "each overwritten write precedes the source" (`Kv` at `hbRt i`).
In the converse, item (1) comes from `rcv` and CC2, item (2) from CC3, and
item (3) from one order serving all of `p`'s reads (CC1 and CC2). -/
theorem «app:rtc/mahajan-checks» (G : OpSig α n) (p : Fin n) (i : RHist G) (v : SMap α) :
    (RView G p i v ↔ RTCCheck G p i v) ∧
    (RView G p i v → HBCheck i p v (Kv G (hbRt i) v)) :=
  ⟨rview_iff_check G p i v, rview_check⟩

/-- "Their reads return all concurrent latest writes; ours return one, so a
view matches their check when that write is the only latest one."

Lean: the match is with a singleton writeList (`«app:rtc/mahajan-checks»`),
not with one element of theirs.  At the
two-write history where `a` ended before `b` began, `→` passes CC1, delivery
and CC3 with writeList `{a, b}` for the read `r`, yet returning `a` is not a
real-time causal view. -/
theorem «app:rtc/one-source» :
    (∀ a, ¬ Tie.hb0 a a) ∧ (∀ a b c, Tie.hb0 a b → Tie.hb0 b c → Tie.hb0 a c) ∧
    (∀ a b, Tie.i1.h.hb a b ↔ Tie.hb0 a b) ∧
    (∀ a b, Tie.i1.rt a b → ¬ Tie.hb0 b a) ∧
    WL Tie.G Tie.hb0 2 0 ∧ WL Tie.G Tie.hb0 2 1 ∧ Tie.i1.rt 0 1 ∧
    ¬ RView Tie.G 0 Tie.i1 Tie.va :=
  wl_member_not_rview

/-- "Views exist … Views also continue. … All views of `p` at an input are
defined on the same reads, so no view extends a different one, and they form
an antichain.  By Theorem `thm:product-frontier`(1), the real-time causal product
interface, in which each replica answers its own reads, is monotone across
partitions under the owner deployment." -/
theorem «app:rtc/monotone-across» (G : OpSig α n) :
    (∀ p i, ∃ v, RView G p i v) ∧ Continue (W := fun _ => SMap α) (RView G) ∧
    Antichain (W := fun _ => SMap α) (RView G) ∧
    MonoAcrossPartitions (ownerD (prodSpec (W := fun _ => SMap α) (RView G) rview_ne)) :=
  ⟨rview_ne, rview_cont, rview_antichain, rtc_product_monoAcross⟩

/-- "A strengthening is *real-time blind* when a tuple it selects at an input
stays selected at the same history with fewer real-time edges, provided its
views are still real-time causal there." -/
theorem «app:rtc/blind» (G : OpSig α n) (T : NormStr (W := fun _ => SMap α) (RView G)) :
    RBlind T ↔ ∀ (i i' : RHist G), i'.h = i.h → (∀ a b, i.rt a b → i'.rt a b) →
      ∀ y, T.sel i' y → (∀ q, RView G q i (y q)) → T.sel i y :=
  Iff.rfl

/-- **Proposition `prop:rtc-maximal`** (Real-time causal maximality).  "No
strict, real-time blind strengthening of the real-time causal product interface
is monotone across partitions under its owner deployment."  (With `2 ≤ n`.) -/
theorem «prop:rtc-maximal» (G : OpSig α n) (hn : 2 ≤ n)
    (T : NormStr (W := fun _ => SMap α) (RView G))
    (sp : Spec (RHist G) (PTd (fun _ : Fin n => SMap α)))
    (hsp : ∀ i x, sp.P i x ↔ T.table i x) (hbl : RBlind T) (hst : T.Strict) :
    ¬ MonoAcrossPartitions (ownerD sp) :=
  rtc_strengthening_not_monoAcross hn T sp hsp hbl hst

/-- Proof of `prop:rtc-maximal`: "Items (2) and (3) and program order make
`≺_v` a strict partial order, and it contains `→`.  At `(h,≺_v)`, `v` is `p`'s
only view … Real-time edges only exclude views."  Here `forceRt i _` is
`(h,≺_v)`. -/
theorem «prop:rtc-maximal/forced» (G : OpSig α n) {p : Fin n} {i : RHist G} {v : SMap α}
    (hv : RView G p i v) :
    (forceRt i (rview_good G hv)).h = i.h ∧
    (∀ a b, i.rt a b → (forceRt i (rview_good G hv)).rt a b) ∧
    (∀ v', RView G p (forceRt i (rview_good G hv)) v' → v' = v) ∧
    (∀ q y, RView G q (forceRt i (rview_good G hv)) y → RView G q i y) :=
  ⟨rfl, fun _ _ h => Or.inl h, fun _ h => rview_unique hv h,
   fun _ _ h => rview_back (rview_good G hv) h⟩

/-- Proof of `prop:rtc-maximal`: "it suffices to show local conservativity". -/
theorem «prop:rtc-maximal/locally-conservative» (G : OpSig α n)
    (T : NormStr (W := fun _ => SMap α) (RView G))
    (sp : Spec (RHist G) (PTd (fun _ : Fin n => SMap α)))
    (hsp : ∀ i x, sp.P i x ↔ T.table i x) (hbl : RBlind T) : T.LocCons :=
  rtc_locCons T sp hsp hbl

end RTC

section RTCHyp
variable {α : Type} {n : Nat}

/-- "Each hypothesis has a counterpart in Mahajan et al.'s theorem.  Their
always availability corresponds to two conditions here: `T` selects a tuple at
every input, so every replica can answer every read, and the system has
Deployment Availability."

Lean: their always availability (TR-11-22, App. A.2: every read and write
completes in every environment, whatever messages are lost).  `T` selects a
tuple `y` at every input because its specification is total; `y p` answers
every read of `p`.  With Deployment Availability under the owner deployment,
in every partition `comp` and at every input `i`, replica `p` emits `y`
restricted to `p` in a run that adds events only at `p`'s block and no input. -/
theorem «app:rtc/always-available» (G : OpSig α n)
    (T : NormStr (W := fun _ => SMap α) (RView G))
    (sp : Spec (RHist G) (PTd (fun _ : Fin n => SMap α)))
    (hsp : ∀ i x, sp.P i x ↔ T.table i x) {D : Type} (Sys : CAP.System sp D)
    (hDA : DeploymentAvailability Sys (ownerD sp)) (comp : Fin n → Nat)
    (hcomp : ∃ p q, comp p ≠ comp q) (i : RHist G) (p : Fin n) :
    ∃ (y : Fin n → SMap α) (ext : CAP.History sp D n), T.sel i y ∧
      (∀ r, PRead G i.h p r ↔ ∃ s, (y p).f r = some s) ∧
      CAP.WF (fun _ => i) ext ∧ CAP.Produced Sys n (fun _ => i) ext ∧
      CAP.Partitioned ext comp ∧ (∀ q, comp q ≠ comp p → ext q = []) ∧
      (∀ q j, CAP.LEv.inp j ∉ ext q) ∧ CAP.LEv.out (restrictTo y p) ∈ ext p :=
  always_available T sp hsp Sys hDA comp hcomp i p

/-- "One-way convergence needs no separate hypothesis: the input records which
writes each replica has received, the environment supplies that input, and
views must respect `→`."

Lean: their one-way convergence (TR-11-22, Def. 2.2: once `s` has sent its
updates to `d`, `d` reflects them).  Here delivery is part of the input: for
any input `i`, replica `d` and causally closed set `S` of operations
containing `d`'s own (for delivery from `s`: `s`'s operations, their causal
past and `d`'s), some input extension adds a read `r` of `d` that has received
`S`.  Every view of `d` there has a check order, and in every check order
each write of `S` is `r`'s source or precedes it. -/
theorem «app:rtc/one-way-convergence» {G : OpSig α n} (i : RHist G) (d : Fin n)
    (S : α → Prop) (hSm : ∀ a, S a → i.h.mem a) (hSc : ∀ a b, i.h.hb a b → S b → S a)
    (hSd : ∀ a, i.h.mem a → G.rep a = d → S a)
    (r : α) (hr : ¬ i.h.mem r) (hrW : G.isW r = false) (hrd : G.rep r = d) :
    ∃ j : RHist G, i ≼ j ∧ PRead G j.h d r ∧ (∀ a, S a → j.h.hb a r) ∧
      ∀ v, RView G d j v → (∃ HB, HBCheck j d v HB) ∧
        ∀ HB, HBCheck j d v HB → ∀ w, S w → G.isW w = true →
          ∃ m, v.f r = some (some m) ∧ (w = m ∨ HB w m) :=
  one_way_convergence i d S hSm hSc hSd r hr hrW hrd

/-- "Real-time blindness is their assumption that an implementation does not
observe real time, which their proof uses to swap the real-time order of
concurrent writes."

Lean: an implementation, at the level of its executions, returns set-valued
writeLists `Im.wl i r` (`MImpl`), and it does not observe real time when they
depend only on the history (`NoRealTime`).  Its strengthening `Im.str`
selects the tuples of real-time causal views whose sources come from those
writeLists, and it is real-time blind.  Their proof makes one concurrent write
end before the other begins (execution `e''`).  Ours (Prop.
`prop:rtc-maximal`) adds real-time edges `x ≺ w` from a write `x` a read saw
to its source `w` where `w ≺ x` did not hold, keeping the history. -/
theorem «app:rtc/no-real-time» (G : OpSig α n) (Im : MImpl G) (hrt : Im.NoRealTime) :
    RBlind Im.str ∧
    ∀ {i : RHist G} {p : Fin n} {v : SMap α} (hv : RView G p i v) {r x w : α},
      Ed G i v r x w →
      (forceRt i (rview_good G hv)).h = i.h ∧
      (∀ a b, i.rt a b → (forceRt i (rview_good G hv)).rt a b) ∧
      (forceRt i (rview_good G hv)).rt x w ∧ ¬ i.rt w x :=
  ⟨Im.rblind hrt, fun hv _ _ _ e => forceRt_swap hv e⟩

end RTCHyp

/-- Last paragraph of `app:rtc`: "The proof of Proposition `prop:rtc-maximal`
needs it too, since a strengthening may read real time from the input, for
instance to break ties between writes that overlap in real time."

Lean (`Appendix/RealTimeTies.lean`): two replicas, writes `a` (replica `0`)
and `b` (replica `1`), and a read `r` at replica `0`.  The strengthening
`Tie.tieStr` keeps every real-time causal view except that `r` returns `a`
whenever `a` is a source for it, which depends on real time: when `a` and `b`
are both visible to `r` and overlap in real time, it breaks the tie toward `a`.
Its spec is the product interface of the kept views.  It is strict, and it is
monotone across partitions under its owner deployment, so the conclusion of
Prop. `prop:rtc-maximal` fails without blindness; by the proposition it is not
real-time blind.  (The other sentences of the paragraph are
`«app:rtc/always-available»`, `«app:rtc/one-way-convergence»` and
`«app:rtc/no-real-time»`.) -/
theorem «app:rtc/reads-real-time» :
    (∀ i x, Tie.tieSpec.P i x ↔ Tie.tieStr.table i x) ∧ Tie.tieStr.Strict ∧
      MonoAcrossPartitions (ownerD Tie.tieSpec) ∧ ¬ RBlind (G := Tie.G) Tie.tieStr :=
  Tie.tie_counterexample

end Paper
end CC
