import CoordCriterion.Appendix.Deployment
import CoordCriterion.Appendix.DeploymentExamples
import CoordCriterion.Appendix.DeploymentSystems
import CoordCriterion.Appendix.Registers
import CoordCriterion.Appendix.RealTimeCausal
import CoordCriterion.Appendix.DeploymentFor

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
choices):
* the participant set `P` is `Fin n`; a deployment is `A : Fin n → Table I O`
  with `A p ⊆ S` (the paper's `E_p` is `A p`);
* a partition `Π` is a labelling `comp : Fin n → Nat` with at least two
  distinct labels (`IsPartition`); blocks are the label classes;
* a participant run family is `F : Fin n → Option (PRun sp)`: participant `p`
  belongs to the family iff `F p = some m`, and `m` is a canonical run from
  `σ_S(m.init)`; `Emits F p r` says `p`'s run emits row `r = (i, o)`;
* "`j` is a common expansion of the participants' current inputs" is `UB F j`;
* "`u` refines `o`" is `o ≼ u`.
-/

namespace CC
namespace Paper

open CC.Deploy

set_option linter.unusedSectionVars false

section Deployment
variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {n : Nat}

/-! ## Appendix E: Deployments: One Explicit Relation per Participant -/

/-- **Definition `def:deployment`** (Deployment, emitted rows, partition).
"A *deployment* over a finite participant set `P` assigns to each `p ∈ P` an
explicit relation `E_p ⊆ S`, the rows `p` may emit: `p` performs an output event `Out_γ(o)`
at current input `i` only if `(i,o) ∈ E_p`."

Lean: `Deployment sp n` has a field `A : Fin n → Table I O` (the paper's
`E_p` is `A p`) and a proof `sub : A p ⊆ S`.  The restriction on output events is imposed where families
are used (`Authorized`). -/
abbrev «def:deployment» (sp : Spec I O) (n : Nat) : Type := CC.Deploy.Deployment sp n

/-- Def. `def:deployment`: "The *emitted rows* of a run are the pairs `(i,o)`
such that the run emits `o` at current input `i`."  For a canonical run of one
participant these are `m.rows`; along an event list they are computed by
`emitted`, which tracks the current input through input events. -/
theorem «def:deployment/emitted-rows» (m : PRun sp) (c j : I) (o : O)
    (es : List (Event I O)) :
    m.rows = emitted m.init m.es ∧
    emitted c ([] : List (Event I O)) = [] ∧
    emitted c (.input j :: es) = emitted j es ∧
    emitted c (.output o :: es) = (c, o) :: emitted c es :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Def. `def:deployment`: "A *partition* `Π` of `P` divides `P` into two or
more nonempty blocks."  A labelling `comp : Fin n → Nat` with two
participants in different blocks. -/
theorem «def:deployment/partition» (comp : Fin n → Nat) :
    IsPartition comp ↔ ∃ p q, comp p ≠ comp q :=
  Iff.rfl

/-- **Definition `def:participant-run-family`** (Participant run family,
silent participant, separable run family).  "A *participant run family*
assigns to each of finitely many participants `p ∈ P` an initial input and a
canonical run whose emitted rows lie in `E_p`.  A participant whose run emits
no output is *silent*.  The family is *separable under `Π`* when either
participants in at least two blocks emit, or exactly one distinct row is
emitted and some silent participant lies in another block."

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
when either participants in at least two blocks emit, or exactly one distinct
row is emitted and some silent participant lies in another block." -/
theorem «def:deployment/separable» (F : Family sp n) (comp : Fin n → Nat) :
    Separable F comp ↔
      ((∃ p q r r', Emits F p r ∧ Emits F q r' ∧ comp p ≠ comp q) ∨
       (∃ r₀ p q, Emits F p r₀ ∧ (∀ p' r, Emits F p' r → r = r₀) ∧
          Silent F q ∧ comp q ≠ comp p)) :=
  Iff.rfl

/-- **Definition `def:monotone-across-partitions`** (Monotone across
partitions).  "Relative to a deployment, `S` is *monotone across `Π`* when,
for every participant run family separable under `Π` and every common
expansion `j` of its participants' current inputs, some `u ∈ S(j)` refines
every emitted output.  It is *monotone across partitions* when it is monotone
across every partition of `P`." -/
theorem «def:monotone-across-partitions» (Dp : Deployment sp n) :
    (∀ comp, MonoAcross Dp comp ↔
      ∀ F : Family sp n, Authorized Dp F → Separable F comp →
        ∀ j, UB F j → ∃ u, sp.S j u ∧ ∀ p r, Emits F p r → r.2 ≼ u) ∧
    (MonoAcrossPartitions Dp ↔ ∀ comp, IsPartition comp → MonoAcross Dp comp) :=
  ⟨fun _ => Iff.rfl, Iff.rfl⟩

/-- "If `S` satisfies Lifted Monotonicity for a relation that contains every `E_p`, it is
monotone across partitions: the emitted rows of a family are rows of that
relation at inputs below `j`." -/
theorem «app:deployment/lm-for-implies-mono-across» (Dp : Deployment sp n)
    (B : Table I O) (hB : ∀ p i o, Dp.A p i o → B i o) (hc : CAP.ConsistentOn sp B) :
    MonoAcrossPartitions Dp :=
  monoAcrossPartitions_of_consistentOn Dp B hB hc

/-- "So Lifted Monotonicity for `E` suffices for the uniform deployment `E_p = E` …" -/
theorem «app:deployment/uniform-mono-across» (E : Table I O) (hES : ∀ i o, E i o → sp.S i o)
    (hc : CAP.ConsistentOn sp E) :
    MonoAcrossPartitions (Deployment.uniform (n := n) E hES) :=
  monoAcrossPartitions_uniform E hES hc

/-- "… and Lifted Monotonicity suffices for every deployment." -/
theorem «app:deployment/lm-implies-mono-across» (hlm : sp.LiftedMono)
    (Dp : Deployment sp n) : MonoAcrossPartitions Dp :=
  monoAcrossPartitions_of_liftedMono hlm Dp

/-- "Rows authorized only to `p` can be emitted only by `p`'s run, whose
emitted outputs form a chain (each output event keeps only rows refining
it)."  The chain is in emission order; its last row refines every emitted
output. -/
theorem «app:deployment/run-outputs-chain» (m : PRun sp) :
    List.Pairwise (fun a b : I × O => a.2 ≼ b.2) m.rows ∧
    (m.rows ≠ [] → ∃ r ∈ m.rows, ∀ r' ∈ m.rows, r'.2 ≼ r.2) :=
  ⟨rows_chain m, rows_max m⟩

/-- "… so a family whose emitted rows are all authorized only to `p` is
separable only when it emits a single row."  Lean: every emitter is `p` and
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

/-- "Let `P = {p,q}`, let every fiber be `{a,b}` ordered by equality, and let
`E_p = S` and `E_q = ∅`, so that `p` alone names a leader."

Lean: `leadSpec I` over any input poset `I`, outputs `Disc Bool` (equality
order; `a = ⟨false⟩`, `b = ⟨true⟩`); `leadD I` with `p = 0`, `q = 1`. -/
theorem «app:deployment/leader-example/setup» (I : Type) [PO I] :
    (∀ i o, (leadSpec I).S i o) ∧ (∀ i o, (leadD I).A 0 i o) ∧
    (∀ i o, ¬ (leadD I).A 1 i o) ∧ SingleAuthority (leadD I) 0 :=
  ⟨fun _ _ => trivial, fun _ _ => rfl, fun _ _ h => absurd h (by decide : ¬ ((1 : Fin 2) = 0)), leadD_single⟩

/-- "A run of `p` emits at most one distinct output …" -/
theorem «app:deployment/leader-example/one-output» {I : Type} [PO I]
    (m : PRun (leadSpec I)) : ∀ r ∈ m.rows, ∀ r' ∈ m.rows, r.2 = r'.2 :=
  lead_run_one_output m

/-- "… and `q` never emits, so every separable family consists of one row
`(i,a)` or `(i,b)` beside a silent `q`." -/
theorem «app:deployment/leader-example/separable-shape» {I : Type} [PO I]
    (F : Family (leadSpec I) 2) (hA : Authorized (leadD I) F) (comp : Fin 2 → Nat)
    (hs : Separable F comp) :
    ∃ r₀, (∀ q r, Emits F q r → q = 0 ∧ r = r₀) ∧ Emits F 0 r₀ ∧ Silent F 1 :=
  lead_separable_shape F hA comp hs

/-- "So `S` is monotone across partitions, yet `(i,a)` and `(i,b)` have no
common expansion and Lifted Monotonicity fails."  (Any input `i` witnesses the
failure.) -/
theorem «app:deployment/leader-example» (I : Type) [PO I] (i : I) :
    MonoAcrossPartitions (leadD I) ∧ ¬ (leadSpec I).LiftedMono :=
  ⟨lead_monoAcross, lead_not_liftedMono i⟩

section Deployment2
variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {n : Nat}

/-- "The same happens whenever each authorized row has an expansion at every
expansion of its input and every set of authorized rows lacking a common
expansion at some common expansion is authorized only to a single
participant."  Finite sets of rows are lists. -/
theorem «app:deployment/sufficient-condition» (Dp : Deployment sp n)
    (h1 : ∀ p i o, Dp.A p i o → ∀ j, i ≼ j → ∃ u, sp.S j u ∧ o ≼ u)
    (h2 : ∀ E : List (I × O), (∀ r ∈ E, ∃ p, Dp.A p r.1 r.2) → ∀ j, (∀ r ∈ E, r.1 ≼ j) →
      (¬ ∃ u, sp.S j u ∧ ∀ r ∈ E, r.2 ≼ u) →
      ∃ p, ∀ r ∈ E, ∀ q, Dp.A q r.1 r.2 → q = p) :
    MonoAcrossPartitions Dp :=
  monoAcross_of_sole_conflicts Dp h1 h2

end Deployment2

/-- "The causal register of Appendix `app:registers` is a further example,
with no single authority, of monotonicity across partitions without Lifted
Monotonicity."

Lean: the two-write history signature `G2` with the replica deployment. -/
theorem «app:deployment/further-examples» :
    MonoAcrossPartitions (replicaD G2) ∧ ¬ (causalSpec G2).LiftedMono :=
  ⟨causal_monoAcross G2, causal_not_liftedMono⟩

/-- "… they need not satisfy this condition, since a set of rows lacking a
common expansion may also contain rows of other participants."  Witness: in
the configuration product interface, the rows `e_0(0)`, `e_0(1)`, `e_1(0)` are
authorized, lack a common expansion, and are not authorized to a single
participant. -/
theorem «app:deployment/further-examples/condition-fails» {I : Type} [PO I] (i : I) :
    let sp := prodSpec (W := fun _ => Front.Disc Bool) (cfgV I) cfgV_ne
    let E : List (I × PTd (fun _ : Fin 2 => Front.Disc Bool)) :=
      [(i, single1 0 ⟨false⟩), (i, single1 0 ⟨true⟩), (i, single1 1 ⟨false⟩)]
    (∀ r ∈ E, ∃ p, (ownerD sp).A p r.1 r.2) ∧
      (¬ ∃ u, sp.S i u ∧ ∀ r ∈ E, r.2 ≼ u) ∧
      ¬ ∃ p, ∀ r ∈ E, ∀ q, (ownerD sp).A q r.1 r.2 → q = p :=
  cfg_product_conflict i

section Deployment3
variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {n : Nat}

/-- "If `|P| ≥ 2` and `E_p = S` for every `p`, every pair of rows can be split
across a partition and every single row paired with a silent participant at
the common expansion; since pairs of rows suffice for the common-expansion
condition (Appendix `app:pairs-suffice`), monotonicity across partitions is
then Lifted Monotonicity." -/
theorem «app:deployment/full-deployment» (hn : 2 ≤ n) (Dp : Deployment sp n)
    (hA : ∀ p, Dp.A p = sp.S) : MonoAcrossPartitions Dp ↔ sp.LiftedMono :=
  full_deployment_iff hn Dp hA

/-- The pairs-suffice step used above (Appendix `app:pairs-suffice`). -/
theorem «app:deployment/full-deployment/pairs-suffice»
    (h : ∀ i₁ o₁ i₂ o₂ j, sp.S i₁ o₁ → sp.S i₂ o₂ → i₁ ≼ j → i₂ ≼ j →
      ∃ u, sp.S j u ∧ o₁ ≼ u ∧ o₂ ≼ u) :
    sp.CommonExpansion :=
  ce_of_pairs h

/-- **Definition `def:deployment-availability`** (Deployment Availability).
"Relative to a deployment, a system has *Deployment Availability* when, in
every partitioned history over `P` it produces, each participant `p`, ending
in state `(i,R)`, can emit each output in `R(i) ∩ E_p(i)` in some
continuation local to `p`."

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
          ∃ γ, CAP.LEv.out γ o ∈ ext p) ∧
    (DeploymentAvailability Sys Dp ↔ DeploymentAvailabilityEnd Sys Dp) :=
  ⟨Iff.rfl, deploymentAvailability_iff_end Sys Dp⟩

/-- "This is Availability for `E_p`, one relation per participant.  For the
uniform deployment `E_p = E` it is Availability for `E` on histories over
`P` …"  `AvailabilityForAt E Sys n` is `CAP.AvailabilityFor E` restricted to
histories over `Fin n`. -/
theorem «app:deployment/uniform-availability» {D : Type} (Sys : CAP.System sp D)
    (E : Table I O) (hES : ∀ i o, E i o → sp.S i o) :
    (DeploymentAvailabilityEnd Sys (Deployment.uniform (n := n) E hES) ↔
      AvailabilityForAt E Sys n) ∧
    (CAP.AvailabilityFor E Sys ↔ ∀ m, AvailabilityForAt E Sys m) :=
  ⟨deploymentAvailability_uniform Sys E hES, availabilityFor_iff_at E Sys⟩

/-- "… and for `E_p = S` it is Availability."  `AvailabilityAt Sys n` is
`CAP.Availability` restricted to histories over `Fin n`
(`CAP.Availability Sys ↔ ∀ n, AvailabilityAt Sys n`). -/
theorem «app:deployment/full-deployment-availability» {D : Type} (Sys : CAP.System sp D)
    (Dp : Deployment sp n) (hA : ∀ p, Dp.A p = sp.S) :
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

/-- "… and monotonicity across partitions says only that each such row has an
expansion at every expansion of its input."  (With `|P| ≥ 2`, so that some
partition exists.) -/
theorem «app:deployment/single-authority» (hn : 2 ≤ n) (Dp : Deployment sp n) (p₀ : Fin n)
    (hSA : SingleAuthority Dp p₀) :
    MonoAcrossPartitions Dp ↔ ∀ i o, Dp.A p₀ i o → ∀ j, i ≼ j → ∃ u, sp.S j u ∧ o ≼ u :=
  single_authority_iff hn Dp p₀ hSA

/-- "In a system whose other participants emit nothing, no other participant
emits an output that the authority chooses against, so its choices do not
require distributed coordination."  Lean: if only participant `0` may perform output
events, no row removed by an output event is emitted, at the same input, by
another participant of the same history. -/
theorem «app:deployment/single-authority/not-distributed» {D : Type} (Sys : CAP.System sp D)
    (hsole : ∀ n init (p : Fin n) pre γ o, Sys.strat n init p pre (CAP.LEv.out γ o) → p.val = 0) :
    ChoicesNotDistributed Sys :=
  sole_emitter_choices Sys hsole

/-- "They still require coordination when another run of the authority may choose
differently, as for the lock manager of Section `sec:coordination`."  Lean:
the owner system of §4.4 (only participant `0` may emit an order): its choice
is a commitment, contradicted by another of its runs, but not at another
participant. -/
theorem «app:deployment/single-authority/coordination» (D : Type) :
    ¬ Exposable (canon CAP.ordSpec ()) .ab ∧ ¬ (CAP.ownerSys D).CoordinationFree ∧
      (CAP.ownerSys D).CoordinationFreeH :=
  ⟨CAP.ordSpec_ab_not_exposable, CAP.ownerSys_not_coordinationFree D,
    CAP.ownerSys_coordinationFreeH D⟩

/-! ### Proposition `thm:complete-cap-deployment` -/

/-- **Proposition `thm:complete-cap-deployment`** (Partition compatibility
under a deployment).  "Fix a deployment.  The following are equivalent.
(1) For every partition `Π`, every participant run family separable under
`Π` is confluent at every common expansion `j` of its participants' current
inputs.  (2) `S` is monotone across partitions."

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
`u ∈ S(j)` refines every output in `X`.  The two conditions thus agree family
by family."  Lean: the per-family step in survivor form (some row at `j`
survives in every remainder table iff the emitted outputs have a common
expansion in `S(j)`), and the proposition in survivor form. -/
theorem «thm:complete-cap-deployment/proof» (Dp : Deployment sp n) :
    (∀ (F : Family sp n) (j : I), UB F j →
      ((∃ u, sp.S j u ∧ ∀ p m, F p = some m → m.fin.R j u) ↔
        (∃ u, sp.S j u ∧ ∀ p r, Emits F p r → r.2 ≼ u))) ∧
    (PartitionSurvivor Dp ↔ MonoAcrossPartitions Dp) :=
  ⟨fun F _ hj => survivor_iff_compatible F hj, partition_compatibility Dp⟩

/-- "The proposition concerns canonical runs and does not use Deployment
Availability.  It applies to the runs of a system as well: by Lemma
`lem:canonical-equivalent`, each such run is observably equivalent to a
canonical run with the same emitted rows, which therefore lie in `E_p`."

Lean: a system participant run (`SRun`: a `CAP` local run from a canonical
state, with sends, receives and output events carrying arbitrary commitments)
has a canonical run with the same emitted rows and current input. -/
theorem «app:deployment/system-runs/canonical» {D : Type} {m : Nat} (r : SRun sp D m) :
    ∃ q : PRun sp, q.rows = r.rows ∧ q.fin.cur = r.fin.cur :=
  r.canonical

/-- "So if `S` is monotone across partitions, the outputs emitted by a
separable family of runs of a partitioned history, as Deployment Availability
permits, have a common expansion `u ∈ S(j)` at every common expansion `j`."

Lean: first for any separable authorized family of system runs (under `Π`),
then for the participants' runs to a cut of a history partitioned by `comp`. -/
theorem «app:deployment/system-runs» {D : Type} {m : Nat} (Dp : Deployment sp n) :
    (∀ {comp : Fin n → Nat}, MonoAcross Dp comp →
      ∀ F : SFamily sp D m n, SAuthorized Dp F → SSeparable F comp →
        ∀ j, SUB F j → ∃ u, sp.S j u ∧ ∀ p r, SEmits F p r → r.2 ≼ u) ∧
    (MonoAcrossPartitions Dp →
      ∀ (init : Fin n → I) (H : CAP.History sp D n) (comp : Fin n → Nat),
        CAP.Partitioned H comp → ∀ (c : Fin n → Nat) (σ : Fin n → State sp)
        (hσ : ∀ p, CAP.LRun (canon sp (init p)) ((H p).take (c p)) (σ p)),
        SSeparable (fun p => some ⟨init p, (H p).take (c p), σ p, hσ p⟩) comp →
        (∀ p r, r ∈ emittedL (init p) ((H p).take (c p)) → Dp.A p r.1 r.2) →
        ∀ j, (∀ p, (σ p).cur ≼ j) →
        ∃ u, sp.S j u ∧ ∀ p r, r ∈ emittedL (init p) ((H p).take (c p)) → r.2 ≼ u) :=
  ⟨fun hmono F ha hs j hj => system_monoAcross Dp hmono F ha hs j hj,
   fun hmono init H comp hP c σ hσ hsep hauth j hj =>
     history_monoAcross Dp hmono init H comp hP c σ hσ hsep hauth j hj⟩

end Deployment3

/-- "It does not follow that the deployment authorizes any participant to emit
`u`; confluence through legal output events of the deployment would
additionally require that authority, a condition we do not impose."

Lean witness: one input, fiber `{a, b, top}` with `a, b < top` (`CAP.triSpec`),
`E_0 = {a}`, `E_1 = {b}`: the specification is monotone across partitions, the
family "`0` emits `a`, `1` emits `b`" is authorized and separable, its only
common refinement is `top`, and no participant may emit `top`. -/
theorem «app:deployment/unauthorized-refinement» :
    MonoAcrossPartitions triD ∧
    ∃ (F : Family CAP.triSpec 2) (comp : Fin 2 → Nat), IsPartition comp ∧
      Authorized triD F ∧ Separable F comp ∧ UB F () ∧
      (∀ u, (∀ p r, Emits F p r → r.2 ≼ u) → u = .top) ∧ ∀ p, ¬ triD.A p () .top :=
  unauthorized_refinement

/-- "With `|P| ≥ 2` and `E_p = S` for every `p`, item (2) is Lifted
Monotonicity, and the proposition is the step behind Corollary
`cor:complete-cap-S` stating that separable families are confluent at every
common expansion exactly when Lifted Monotonicity holds." -/
theorem «app:deployment/full-deployment-step» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    {n : Nat} (hn : 2 ≤ n) (Dp : Deployment sp n) (hA : ∀ p, Dp.A p = sp.S) :
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

/-- "Thus an expansion never adds an operation to the causal past of an
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

/-- "Under causal consistency, `ρ ∈ S(h)` when each replica has a
serialization explaining every read of that replica in the domain of `ρ`.
Under linearizability, a single total order of all operations of `h`
extending `→` must explain every read in the domain." -/
theorem «app:registers/fibers» (G : OpSig α n) (h : Hist α) (ρ : SMap α) :
    ((causalSpec G).S h ρ ↔ WellDom G h ρ ∧ ∀ p, ∃ lt, Ser G h p lt ∧
      ∀ r s, ρ.f r = some s → G.rep r = p → Explains G h lt r s) ∧
    ((linSpec G).S h ρ ↔ WellDom G h ρ ∧ ∃ lt, STO h.mem lt ∧ Ext h.hb h.mem lt ∧
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

/-- "Under linearizability, if `p` reads cat the order has `w_p(x,dog)` before
`w_q(x,cat)`; if `q` reads dog it has the opposite.  No source map refines
both, so the register is not monotone across the partition `{{p},{q}}` under
any deployment authorizing these two reads."

Lean: `ρ1 = (r_p ↦ w_q)`, `ρ2 = (r_q ↦ w_p)` are linearizable; no single
linearization explains both; the partition `{{p},{q}}` is `comp = Fin.val`. -/
theorem «app:registers/linearizable-not-monotone-across» :
    (linSpec G2).S h2 ρ1 ∧ (linSpec G2).S h2 ρ2 ∧
    (∀ T, STO h2.mem T → Ext h2.hb h2.mem T →
      Explains G2 h2 T 2 (some 1) → Explains G2 h2 T 3 (some 0) → False) ∧
    ∀ Dp : Deployment (linSpec G2) 2, Dp.A 0 h2 ρ1 → Dp.A 1 h2 ρ2 →
      ¬ MonoAcross Dp (fun p => p.val) :=
  ⟨lin_ρ1', lin_ρ2', fun _ hT hE h1 h2 => no_lin_both hT hE h1 h2,
   fun Dp h0 h1 => lin_not_monoAcross Dp h0 h1⟩

/-- "Under causal consistency the two replicas may serialize the concurrent
writes differently, and one source map sends `r_p` to `w_q(x,cat)` and `r_q`
to `w_p(x,dog)`." -/
theorem «app:registers/causal-two-write» : (causalSpec G2).S h2 ρ12 :=
  causal_two_write

section Registers2
variable {α : Type} {n : Nat}

/-- "Under the deployment in which each replica answers only its own reads
(`E_p` holds the rows whose source map is defined only on reads of `p`), the
causal register is monotone across partitions, for every history. … Separability
is not used."

Lean: `replicaD G`; the statement holds for every signature `G` (hence every
history), and the common refinement exists for every authorized family,
separable or not.  By Prop. `thm:complete-cap-deployment` the separable
families are confluent. -/
theorem «app:registers/causal-monotone-across» (G : OpSig α n) :
    (∀ p h ρ, (replicaD G).A p h ρ ↔ CausalFib G h ρ ∧ ∀ r s, ρ.f r = some s → G.rep r = p) ∧
    (∀ F : Family (causalSpec G) n, Authorized (replicaD G) F → ∀ j, UB F j →
      ∃ u, CausalFib G j u ∧ ∀ p r, Emits F p r → r.2 ≼ u) ∧
    MonoAcrossPartitions (replicaD G) ∧ PartitionConfluent (replicaD G) :=
  ⟨fun _ _ _ => Iff.rfl, fun F hA j hj => causal_common G F hA j hj,
   causal_monoAcross G, causal_confluent G⟩

/-- Proof step: "Take a serialization `L_p` of `i_p` explaining `ρ_p`, and
extend it to `j` by appending the new operations of `p` and the new writes in
any order extending `→`; since no new operation causally precedes an old one,
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
common expansion; both are authorized only to `p` under `replicaD`. -/
theorem «app:registers/same-read-incompatible» :
    (causalSpec G2).S h2 ρa ∧ (causalSpec G2).S h2 ρ1 ∧ ¬ (causalSpec G2).LiftedMono :=
  ⟨causal_ρa, causal_ρ1, causal_not_liftedMono⟩

/-! ## Appendix E.2: Real-time causal consistency (`app:rtc`) -/

section RTC
variable {α : Type} {n : Nat}

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
      (∀ i x, sp.S i x ↔ T.table i x) → T.LocCons → T.Strict →
      ¬ MonoAcrossPartitions (ownerD sp)) :=
  ⟨fun hc => product_monoAcross V hne hc,
   fun hn hAC T sp hsp hLC hst => strengthening_not_monoAcross hn V hAC T sp hsp hLC hst⟩

/-- "Consider the histories of Appendix `app:registers` with a second strict
partial order `≺`: `a ≺ b` when `a` ended before `b` began.  We assume that
`a → b` implies `a ≺ b`, so replicas propagate only completed writes, and that
`→` totally orders the operations of each replica.  One input expands another
when it does as a history and `≺` agrees on the old operations."

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

/-- "Views exist … They continue … Views share a domain, so they form an
antichain.  By Theorem `thm:product-frontier`(1), the real-time causal product
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
    (hsp : ∀ i x, sp.S i x ↔ T.table i x) (hbl : RBlind T) (hst : T.Strict) :
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
    (hsp : ∀ i x, sp.S i x ↔ T.table i x) (hbl : RBlind T) : T.LocCons :=
  rtc_locCons T sp hsp hbl

end RTC

end Paper
end CC
