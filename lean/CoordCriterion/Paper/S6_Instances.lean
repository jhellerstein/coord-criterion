import CoordCriterion.Instances.Examples
import CoordCriterion.Instances.BailisDefinition
import CoordCriterion.Instances.QueryRefinements
import CoordCriterion.Instances.Placement
import CoordCriterion.Instances.BKTransducers
import CoordCriterion.Instances.BKSufficiency
import CoordCriterion.CALM.Lemmas
import CoordCriterion.Instances.IOTraceExamples
import CoordCriterion.Instances.TestingLimits
import CoordCriterion.Distributed.Histories
import CoordCriterion.CAP.CompleteCAP
import CoordCriterion.Instances.HATSpec
import CoordCriterion.Instances.HATInter
import CoordCriterion.Instances.HATWriteSkew
import CoordCriterion.Instances.HATTaxonomyWitness
import CoordCriterion.Instances.HATAppB

/-!
# Paper §6, "Instances Across the Literature" (`sections/instances.tex`)

Statement layer for Section `sec:instances`.  Read it side by side with
`sections/instances.tex`: the `/-! ## … -/` headers follow the paper's
subsections, entries appear in paper order, and each entry quotes the claim
it formalizes.

* Numbered results and displayed equations are named by their LaTeX label
  (`«prop:iconfluence-lm»`, …).
* Unlabeled claims are named `«<enclosing label>/<slug>»`, e.g.
  `«sec:iconfluence-instance/spec»`.
* Every proof is a pointer to the library (`Instances/Examples.lean`,
  `Instances/QueryRefinements.lean`, `Instances/Placement.lean`,
  `Instances/InvariantConfluence.lean`,
  `Instances/BailisDefinition.lean`, `Instances/IOTrace.lean`,
  `Instances/IOTraceExamples.lean`).

Conventions shared by the entries (details in `Instances/Examples.lean`):
finite payload sets are `Inst.FSet P` (inclusion); a join-semilattice is
`Inst.JSL D`; the CRDT state `s(U) = s₀ ⊔ ⨆U` is `Inst.st s₀ U`; a function
`f` is read as the specification `Comp.graph f`; `Comp.Monotone f` is
`∀ x y, x ≼ y → f x ≼ f y`; the Boolean order `false ≼ true` is `Prop` under
implication; fact sets and database states are `IConf.St X := X → Prop`,
ordered by inclusion.  Finite families of rows are lists.

The invariant-confluence model and its proof are spelled out in
`Paper/AppB_InvariantConfluence.lean`.
-/

namespace CC
namespace Paper

open CC.Comp (Monotone graph)

/-! The opening paragraph ("Complete CALM provides a unified lens for many
results across literatures.  For the key related ideas, we provide mappings
here to our specification model.  Each setting declares an input, an output,
and their orders before applying either CALM theorem.") frames the section;
it states no claim of its own.

## Query monotonicity (`sec:query-instance`)

The first paragraph recalls the relational-transducer CALM Theorem ("The CALM
Theorem of Ameloot et al. is stated in a particular operational model,
relational languages on transducer networks: a query can be evaluated without coordination
exactly when it is monotone … Functional CALM restates the result as a property
of a spec, so that it can be compared with specs outside Datalog; it does not
replace the operational details of that theorem.").  The abstraction is
`«eq:query-monotonicity»` (§2); the transducer theorem itself is cited, not
formalized.  The entries below check the mapping of its output extensions into our
frame (`Instances/QueryRefinements.lean`).  Which order a placement model
justifies, and the resulting weaker CALM variants, are checked at the level of
a node's view (`Instances/Placement.lean`); the transducer runs of those
papers are cited, not formalized. -/

/-- Sec. `sec:query-instance`: "Ameloot et al. characterized these queries by
weaker forms of monotonicity.  A query is domain-distinct-monotone when
`Q(I) ⊆ Q(I ∪ J)` whenever each new fact in `J` contains a value not in `I`,
and domain-disjoint-monotone when this holds whenever each new fact uses only
such values. … Under these orders, functional
monotonicity is exactly domain-distinct- and domain-disjoint-monotonicity, so
Functional CALM gives their characterizations."  (Ameloot et al., PODS 2014
version of the cited TODS paper, Definition 1.)  Lean: facts carry values
`vals : F → V → Prop`; `ExtInp (distinctAdm vals)` and
`ExtInp (disjointAdm vals)` order instances by domain-distinct and
domain-disjoint input extension (nullary facts are never domain disjoint, as in
Ameloot et al.).  For each order, the weaker monotonicity is monotonicity of
`J ↦ Q(J)`, and by Functional CALM the graph is consistent exactly when it
holds.  With every fact admissible the order is inclusion and the condition
is ordinary query monotonicity. -/
theorem «sec:query-instance/weaker-monotonicity» {F V A : Type} (vals : F → V → Prop)
    (Q : CALM.PSet F → CALM.PSet A) :
    ((QRef.DistinctMono vals Q ↔ Monotone (fun I : QRef.ExtInp (QRef.distinctAdm vals) => Q I.set)) ∧
      ((graph (fun I : QRef.ExtInp (QRef.distinctAdm vals) => Q I.set)).Consistent ↔
        QRef.DistinctMono vals Q)) ∧
    ((QRef.DisjointMono vals Q ↔ Monotone (fun I : QRef.ExtInp (QRef.disjointAdm vals) => Q I.set)) ∧
      ((graph (fun I : QRef.ExtInp (QRef.disjointAdm vals) => Q I.set)).Consistent ↔
        QRef.DisjointMono vals Q)) ∧
    (QRef.RMono (QRef.allAdm F) Q ↔ ∀ J J' : CALM.PSet F, J ≼ J' → Q J ≼ Q J') :=
  ⟨QRef.distinctMono_iff vals Q, QRef.disjointMono_iff vals Q, QRef.allAdm_rmono_iff Q⟩

/-- Sec. `sec:query-instance`: "We model each data placement by an input order.
For the placement that Ameloot et al. call “policy-aware”, `I ∪ J` extends `I`
only when `J` is domain-distinct from `I`".  This sentence declares the
modeling choice; the entry checks that the order matches their placement model.
Lean (Zinn et al.'s first model, Ameloot et al.'s policy-aware distribution
policies, PODS 2014 §4.1.1): a policy `P` assigns each fact to a non-empty set of nodes, and a node
can ask the policy about the facts it can construct from its known values.
Node `x` has received the complete local inputs of the nodes in `C`
(`Place.known P H C`); its view is those local inputs and the policy answers
of `C` on constructible facts.  It cannot rule out `H'` when some policy gives
the same view (`Place.Model.Unruled`).  It "knows which facts over its known
values are absent" when each such fact is assigned to a node of `C`
(`Place.Complete`), a property of the view (second conjunct).  At such a
view, while some node `y` has not been heard from, the unruled inputs are
exactly the extensions of what `x` holds in the domain-distinct order
`QRef.ExtInp (QRef.distinctAdm vals)` (first conjunct). -/
theorem «sec:query-instance/policy-aware-order» {F V N : Type} (vals : F → V → Prop)
    {P : Place.Policy F N} {H : CALM.PSet F} {C : N → Prop} {y : N} (hP : Place.Total P)
    (hy : ¬ C y) (hc : Place.Complete vals P H C) :
    (∀ H', (Place.policyAware vals N).Unruled P H C H' ↔
      (⟨Place.known P H C⟩ : QRef.ExtInp (QRef.distinctAdm vals)) ≼ ⟨H'⟩) ∧
    (∀ P' H', Place.SameView vals P H P' H' C → Place.Complete vals P' H' C) :=
  ⟨Place.policyAware_unruled vals hP hy hc, fun _ _ hs => Place.complete_of_sameView hs hc⟩

/-- Sec. `sec:query-instance`: "for “domain-guided” placement, only when `J` is
domain-disjoint from `I`."  Lean (Ameloot et al.'s domain-guided policies,
PODS 2014 §4.1.1, Zinn et al.'s second model): admissible policies place
each non-nullary fact at `⋃_{v ∈ f} α(v)` for some `α` assigning each value a
non-empty node set (`Place.DomainGuided`); views and completeness as for
policy-aware placement.  At a complete view, with some node not yet heard
from, the unruled inputs are exactly the extensions in the domain-disjoint
order.  Hypothesis `Place.HasDiag`: every value `v` has a fact whose only value
is `v`, such as `R(v,…,v)` for any relation of arity at least one.  Under the
original placement (`N0`: any placement, no knowledge of it) they are exactly
the supersets (third conjunct, `QRef.allAdm`). -/
theorem «sec:query-instance/domain-guided-order» {F V N : Type} (vals : F → V → Prop)
    (hd : Place.HasDiag vals) {P : Place.Policy F N} {H : CALM.PSet F} {C : N → Prop} {y : N}
    (hy : ¬ C y) :
    (Place.DomainGuided vals P → Place.Complete vals P H C → ∀ H',
      ((Place.domainGuided vals N).Unruled P H C H' ↔
        (⟨Place.known P H C⟩ : QRef.ExtInp (QRef.disjointAdm vals)) ≼ ⟨H'⟩)) ∧
    (Place.Total P → ∀ H', ((Place.oblivious F N).Unruled P H C H' ↔
        (⟨Place.known P H C⟩ : QRef.ExtInp (QRef.allAdm F)) ≼ ⟨H'⟩)) :=
  ⟨fun hP hc => Place.domainGuided_unruled vals hd hP hy hc,
    fun hP => Place.oblivious_unruled hP hy⟩

/-- Sec. `sec:query-instance`: "Under these orders, functional monotonicity is
exactly domain-distinct- and domain-disjoint-monotonicity, so Functional CALM
gives their characterizations."  Lean: their weaker CALM variants derived from Functional
CALM through the orders above.  `Place.CFComputes M x Q out` reads
coordination-free computation at the level of views: node `x`'s output is a
function of its view, never outside `Q(H)`, all of `Q(H)` once `x` has heard
from every node, and all of `Q(H)` before any message when all input is placed
at `x` (the one-node network of Zinn's Lemma 3.7).  For any model that
justifies an order, such a computation exists iff the graph of `Q` over that
order is consistent (`Place.cf_iff_consistent`, carried by
`QRef.rmono_iff_consistent`, i.e. `functional_calm`).  Instantiated:
policy-aware iff domain-distinct-monotone, domain-guided iff
domain-disjoint-monotone, original placement iff monotone.  Transducer runs
are not modeled. -/
theorem «sec:query-instance/placement-calm» {F V N A : Type} (vals : F → V → Prop)
    (hd : Place.HasDiag vals) {x y : N} (hxy : x ≠ y) (Q : CALM.PSet F → CALM.PSet A) :
    ((∃ out, Place.CFComputes (Place.policyAware vals N) x Q out) ↔ QRef.DistinctMono vals Q) ∧
    ((∃ out, Place.CFComputes (Place.domainGuided vals N) x Q out) ↔ QRef.DisjointMono vals Q) ∧
    ((∃ out, Place.CFComputes (Place.oblivious F N) x Q out) ↔
      ∀ J J' : CALM.PSet F, J ≼ J' → Q J ≼ Q J') :=
  ⟨Place.policyAware_cf_iff vals hxy Q, Place.domainGuided_cf_iff vals hd hxy Q,
    Place.oblivious_cf_iff hxy Q⟩

/-- Sec. `sec:query-instance`: "Their model maps directly to ours.  A
behavior is an I/O specification whose outputs are ordered by inclusion.  Each
fact names the participant that holds it.  One input extends another by adding
the facts of participants not yet heard from, never by adding facts of a
participant already heard from.  A network of transducers is a system in which
every participant runs the same strategy, sees only its own facts and the
contents of the messages it receives, and broadcasts its messages. … Under
their placement, a participant's input events contain only the facts that name
it, at the start; other facts reach it only in messages, and a participant
passes on only facts it holds.  A
transducer that computes a behavior translates into our framework as a system
whose runs stay confluent.  Every output that some fair run of the transducer can produce is
emitted by some run of that system."

Lean: inputs are `QRef.ExtInp (QRef.netAdm loc)` (located facts; an input
extends another by facts at new locations, `BK.LInp`), outputs located facts
under inclusion.  Their transducer networks are `BK.Prog` (abstracted over
their relational mappings; genericity and domain preservation are not
modeled, so the class of programs is larger), translated by `BK.sysOf` into an
anonymous cluster (`CAP.System.Anonymous`: one strategy, seeing its own
initial input and the contents of its receives; sends are broadcasts, each
received at most once per participant, `BK.WFB`).  Placement is `BK.Placed`
(own facts at the start, later inputs only of held facts, `BK.Holds`).  First
conjunct (T1): if the program computes `B`, the cluster is consistent on
placed histories (`BK.PlacedConsistent`) for the downward closure `BK.downB B`.
Second conjunct (T2): if it characterizes `B` (every output of a fair run),
every row of `B` at a nonempty finite network is covered by a placed history
of the cluster.  The sentence on what their coordination-free transducers
know (an identifier and an order on identifiers) is cited. -/
theorem «sec:query-instance/mapping» {F Msg St Out : Type} {loc : F → Nat}
    (Pg : BK.Prog F Msg St Out) (B : Spec (BK.LInp loc) (CALM.PSet (Nat × Out))) :
    (BK.sysOf (sp := BK.downB B) Pg).Anonymous ∧
    (BK.Computes Pg B → BK.PlacedConsistent (BK.sysOf (sp := BK.downB B) Pg)) ∧
    (BK.Characterizes Pg B → ∀ (H : CALM.PSet F) (K : CALM.PSet (Nat × Out)),
      BK.FinNet loc H → (∃ f, H.mem f) → B.P ⟨H⟩ K →
        BK.Covers (BK.sysOf (sp := BK.downB B) Pg) H K) :=
  ⟨BK.sysOf_anonymous Pg, BK.placedConsistent_of_computes,
    fun hCh _ _ hf hn hK => BK.covers_of_characterizes hCh hf hn hK⟩

/-- Sec. `sec:query-instance`: "Baccaert and Ketsman show that a behavior can
be computed without the list of all nodes exactly when it contains a node
monotone behavior, and this characterization holds in our formalism. … Our
version does not need their requirement that programs treat data values only as
interchangeable symbols."

Lean: "computable without the list of all nodes" is `BK.Computes` by a node
program under Id+Ord (`BK.Prog`, their Def. 6 reading of coordination-free);
node programs are arbitrary state machines, not required to be generic or
domain-preserving.  First conjunct (their Lemma 4 with Thm. 5,
`BK.bk_computable_iff`): computable iff some sub-behavior is node monotone
with its outputs at network nodes (their Def. 1 condition, `BK.LocatedFin`).
Second conjunct (their Thm. 5, `BK.bk_characterized_iff`): characterized by
some program iff node monotone and located.  Sufficiency is the quorum
program `BK.qProg` (their Prop. 10). -/
theorem «sec:query-instance/characterization» {F Out : Type} {loc : F → Nat}
    (B : Spec (BK.LInp loc) (CALM.PSet (Nat × Out))) :
    ((∃ (Msg St : Type) (Pg : BK.Prog F Msg St Out), BK.Computes Pg B) ↔
      ∃ B' : Spec (BK.LInp loc) (CALM.PSet (Nat × Out)), (∀ i K, B'.P i K → B.P i K) ∧
        BK.NodeMonoFin loc B' ∧ BK.LocatedFin loc B') ∧
    ((∃ (Msg St : Type) (Pg : BK.Prog F Msg St Out), BK.Characterizes Pg B) ↔
      BK.NodeMonoFin loc B ∧ BK.LocatedFin loc B) :=
  ⟨BK.bk_computable_iff B, BK.bk_characterized_iff B⟩

/-- Sec. `sec:query-instance`: "Their aims differ from ours.  They ask which
behaviors become computable when nodes share some piece of system knowledge,
such as identifiers, an order on them, or the list of all nodes.  For them, a
behavior needs coordination when it cannot be computed without the list of all
nodes.  Correctness is judged by the final output of a run, and the input is
fixed when the run starts.  We ask instead when a spec requires a commitment,
judge consistency at every point of a run, and let input arrive over time.  A
behavior can therefore be coordination-free in their sense while still needing
a commitment in ours.  For them, coordination means needing the list of all
nodes, so a commitment that one participant makes locally, as when a group's
smallest node decides for the group, does not count.  Our criterion identifies
such local commitments as well.  Each refinement of CALM
in this subsection thus corresponds to a choice our model makes explicit: the
input order, for the placements of Ameloot et al.; sets ordered by inclusion as
inputs, for Li and Lee; and the facts that an input event at each participant
may contain, together with nondeterministic outputs, for Baccaert and
Ketsman."

Lean: the coordination-free-but-commitment sentence's example is the matching
problem below: it is node
monotone (`QRef.matching_nodeMono`; coordination-free in their sense by their
characterization theorem, cited) and fails Lifted Monotonicity, so by Complete
CALM some reachable output needs a commitment.  "Our criterion identifies such
local commitments as well": the spanning-tree instance `QRef.tree` is node
monotone yet no total sub-behavior is consistent on it
(`«sec:query-instance/sufficient-half»`), so a system for it needs a
commitment, which their quorum construction makes at a group's smallest node
(`BK.qProg`, `BK.dec_lam`); reading that decision as a local commitment is
prose.  The descriptions of their aims, notion of coordination ("needing the
list of all nodes"), correctness and inputs are cited prose.  The closing
sentence summarizes the subsection's mappings: the input orders are
`«sec:query-instance/placement-calm»`, the set inputs of Li and Lee are cited
prose, and the placement of input facts is `BK.Placed`
(`«sec:query-instance/mapping»`). -/
theorem «sec:query-instance/aims» :
    QRef.NodeMono (id : Nat → Nat) (QRef.matching (id : Nat → Nat)) ∧
      ¬ (QRef.matching (id : Nat → Nat)).LiftedMono :=
  ⟨QRef.matching_nodeMono id,
    fun h => QRef.matching_not_consistentOn.2.2.2.2.2.2.2
      ((liftedMono_iff_commonExpansion _).1 h)⟩

/-- Sec. `sec:query-instance`: "Two sides of a partition cannot tell that they
are disconnected, so each must emit to be available, and when the partition
heals, their outputs must have a common output extension at any input that
extends what both sides have received. … Baccaert and Ketsman's node
monotonicity is the same condition, restricted to sides that have heard from
disjoint sets of participants." and "Its necessary half is the partition
argument above, applied to histories that respect their placement."

Lean, first conjunct: node monotonicity (`QRef.NodeMono`, their Def. 7) is
the common-extension condition for two rows at disjoint networks and any
common input extension (`QRef.DisjointPairExpansion`).  Second conjunct (the
argument, in our model): an anonymous cluster consistent on placed histories
realizes rows (`BK.realized`, the rows it emits) that have a common output
extension at the union of disjoint networks; the two witness histories are
placed side by side, since no strategy can tell.  Third conjunct: through the
translation, a behavior characterizing a transducer is node monotone on finite
networks (their Prop. 11).  The second and third conjuncts are the necessary
half; that this is "the partition argument above" (the argument behind
Theorem `thm:complete-cap`'s necessity, run over placed histories) is a
prose reading.  Their characterization theorem (Thm. 5 with Lemma 4) is proved
in both directions in `«sec:query-instance/characterization»`. -/
theorem «sec:query-instance/node-monotonicity» :
    (∀ {F N G : Type} (loc : F → N) (B : Spec (QRef.ExtInp (QRef.netAdm loc)) (CALM.PSet G)),
      QRef.NodeMono loc B ↔ QRef.DisjointPairExpansion loc B) ∧
    (∀ {F O D : Type} [PO O] {loc : F → Nat} {sp : Spec (BK.LInp loc) O} (Sys : CAP.System sp D),
      Sys.Anonymous → BK.PlacedConsistent Sys → BK.NodeMonoFor sp (BK.realized Sys)) ∧
    (∀ {F Msg St Out : Type} {loc : F → Nat} (Pg : BK.Prog F Msg St Out)
      (B : Spec (BK.LInp loc) (CALM.PSet (Nat × Out))),
      BK.Characterizes Pg B → BK.NodeMonoFin loc B) :=
  ⟨fun loc B => QRef.nodeMono_iff_disjointPair loc B,
    fun _ hA hc => BK.nodeMono_of_placedConsistent hA hc,
    fun _ _ hCh => BK.nodeMono_of_characterizes hCh⟩

/-- Sec. `sec:query-instance`: "Complete CAP requires this condition across
every partition." and "Since other facts reach a participant only in messages
and no message crosses a partition, the inputs of the two sides never share a
fact.  In our model, an input event at any participant may contain any fact, so
input events on both sides may contain the same fact, and for nondeterministic
behaviors node monotonicity is strictly weaker than Lifted Monotonicity."
Lean (strictness: `«sec:query-instance/matching»`): the common-extension condition (equivalently Lifted
Monotonicity, the condition of Theorem `thm:complete-cap` with `E = P`), which
also covers sides with overlapping inputs, implies node monotonicity, which
asks it only for inputs at disjoint networks.  That their placement gives
disjoint sides is `BK.Placed` (`«sec:query-instance/mapping»`). -/
theorem «sec:query-instance/asks-for-more» {F N G : Type} (loc : F → N)
    (B : Spec (QRef.ExtInp (QRef.netAdm loc)) (CALM.PSet G)) :
    B.CommonExpansion → QRef.NodeMono loc B :=
  fun h => QRef.nodeMono_of_consistent loc ((complete_calm_commonExpansion B).2 h)

/-- Sec. `sec:query-instance`: "Unconstrained matching shows the gap.  Each
item is a fact that names one participant, and any set of disjoint pairs of
items is a permitted output.  Under their placement, the inputs of the two
sides contain disjoint sets of items, so their pairings always combine.  In our
model, input events on both sides of a partition can contain the same item `i`.
One side can pair `i` with `j` and the other with `k`, and no matching contains
both pairs."

Lean: `QRef.matching loc` (items located by `loc`, outputs symmetric
matchings of the input's items under inclusion, every matching permitted).
First conjunct: it is node monotone for every placement.  Second conjunct, with
each item at its own location (`loc = id`, `i = 0`, `j = 1`, `k = 2`): both
inputs contain item `0`; the rows `({0,1}, {0–1})` and `({0,2}, {0–2})` are
rows of the spec; `{0,1,2}` extends both inputs; no matching there contains
both pairs; so the spec fails Lifted Monotonicity for `E = P`. -/
theorem «sec:query-instance/matching» :
    (∀ {F N : Type} (loc : F → N), QRef.NodeMono loc (QRef.matching loc)) ∧
    ((QRef.net fun x => x = 0 ∨ x = 1).set.mem 0 ∧ (QRef.net fun x => x = 0 ∨ x = 2).set.mem 0 ∧
      (QRef.matching (id : Nat → Nat)).P (QRef.net fun x => x = 0 ∨ x = 1) (QRef.pairOf 0 1) ∧
      (QRef.matching (id : Nat → Nat)).P (QRef.net fun x => x = 0 ∨ x = 2) (QRef.pairOf 0 2) ∧
      (QRef.net fun x => x = 0 ∨ x = 1) ≼ (QRef.net fun x => x = 0 ∨ x = 1 ∨ x = 2) ∧
      (QRef.net fun x => x = 0 ∨ x = 2) ≼ (QRef.net fun x => x = 0 ∨ x = 1 ∨ x = 2) ∧
      (∀ u, (QRef.matching (id : Nat → Nat)).P (QRef.net fun x => x = 0 ∨ x = 1 ∨ x = 2) u →
        ¬ (QRef.pairOf 0 1 ≼ u ∧ QRef.pairOf 0 2 ≼ u)) ∧
      ¬ CAP.ConsistentOn (QRef.matching (id : Nat → Nat)) (QRef.matching (id : Nat → Nat)).P) :=
  ⟨fun loc => QRef.matching_nodeMono loc, QRef.matching_not_consistentOn⟩

/-- Sec. `sec:query-instance`: "For deterministic behaviors the two conditions
coincide: a function's output on each side's input must lie below its one
output on the union, and node monotonicity already requires this, since the
union extends each side's input by participants that side has not heard from."
Lean: for the graph of `b`, node monotonicity is monotonicity
under network input extension, which by Functional CALM is consistency. -/
theorem «sec:query-instance/deterministic-behaviors» {F N G : Type} (loc : F → N)
    (b : QRef.ExtInp (QRef.netAdm loc) → CALM.PSet G) :
    (QRef.NodeMono loc (graph b) ↔ Monotone b) ∧ ((graph b).Consistent ↔ Monotone b) :=
  QRef.nodeMono_graph_iff loc b

/-- Sec. `sec:query-instance`: "The sufficient half does not follow from
Complete CAP: participants on the same side can hear from overlapping sets of
participants, and their construction, in which a group's smallest node decides
for the group, makes commitments that keep such outputs compatible."

Lean: a spanning-tree behavior (`QRef.tree`, a concrete instance of their
`Top_span`, Example 8) is node monotone, yet no total explicit relation inside
it satisfies the common-extension condition: the pairwise-overlapping networks
`{0,1}`, `{1,2}`, `{0,2}` would need a tree on `{0,1,2}` with all three edges.
So by Theorem `thm:complete-cap` no system for it has Availability for such a
relation and Partition Consistency, although it is node monotone.  Their
construction is `BK.qProg`; that its quorum decisions keep decided records
nested or disjoint is `BK.dec_lam`.  Reading those decisions as commitments is
prose. -/
theorem «sec:query-instance/sufficient-half» :
    QRef.NodeMono id QRef.tree ∧
      ∀ A : Table (QRef.ExtInp (QRef.netAdm (id : Nat → Nat))) (CALM.PSet (Nat × Nat)),
        (∀ H, ∃ K, A H K) → (∀ H K, A H K → QRef.tree.P H K) → ¬ CAP.ConsistentOn QRef.tree A :=
  ⟨QRef.tree_nodeMono, fun A hA hsub => QRef.tree_no_consistentOn A hA hsub⟩

/-! ## CRDTs: monotone queries over convergent state (`sec:crdt-instance`)

The opening paragraph ("A CRDT uses join semilattices to guarantee that
replicas that have received the same updates converge to equivalent states,
whatever the order of delivery and merge [Shapiro et al.].  That guarantee,
Strong Eventual Consistency, is the convergence of Corollary `cor:convergence`.
The corollary assumes only that the spec is monotone, not that its input or
output order is a join semilattice."  Next paragraph: "Strong Eventual
Consistency says nothing about what a client observes when it queries a replica
that has not yet received every update.
Such a query risks Lamport's "anomalous behavior" (§`sec:functional-events`).
Laddad et al. proposed monotonicity as the right test for safe observation
from CRDT state.") cites rather than proves; its two-phase-set example is
checked in `«sec:crdt-instance/two-phase»` below. -/

/-- Sec. `sec:crdt-instance`: "the replica's state is `s(U) = s₀ ⊔ ⨆U`."
Lean: `Inst.st s₀ U` is the least upper bound of `{s₀} ∪ U` (independent of
an enumeration of the finite set `U`). -/
theorem «sec:crdt-instance/state-function» {D : Type} [PO D] [Inst.JSL D] (s0 : D) (U : Inst.FSet D) :
    Inst.IsLUB s0 U.1 (Inst.st s0 U) :=
  Inst.st_lub s0 U

/-- Sec. `sec:crdt-instance`: "Then `U ⊆ V` implies `s(U) ⊑ s(V)`, and
`s(U₁) ⊔ s(U₂) = s(U₁ ∪ U₂)` is the least state extending both." -/
theorem «sec:crdt-instance/state-monotone» {D : Type} [PO D] [Inst.JSL D] (s0 : D) :
    Monotone (Inst.st s0 : Inst.FSet D → D) ∧
      (∀ U₁ U₂ : Inst.FSet D, Inst.JSL.join (Inst.st s0 U₁) (Inst.st s0 U₂) = Inst.st s0 (U₁.union U₂)) ∧
      ∀ U₁ U₂ : Inst.FSet D,
        (Inst.st s0 U₁ ≼ Inst.st s0 (U₁.union U₂) ∧ Inst.st s0 U₂ ≼ Inst.st s0 (U₁.union U₂)) ∧
          ∀ c, Inst.st s0 U₁ ≼ c → Inst.st s0 U₂ ≼ c → Inst.st s0 (U₁.union U₂) ≼ c :=
  ⟨Inst.st_mono s0, Inst.st_union s0, Inst.st_union_least s0⟩

/-- Sec. `sec:crdt-instance`: "By Functional CALM, the runs of `q ∘ s` are
consistent exactly when `U ⊆ V` implies `q(s(U)) ≼_Y q(s(V))`." -/
theorem «sec:crdt-instance/query-calm» {D Y : Type} [PO D] [Inst.JSL D] [PO Y] (s0 : D) (q : D → Y) :
    (graph (fun U : Inst.FSet D => q (Inst.st s0 U))).Consistent ↔
      ∀ U V : Inst.FSet D, U ≼ V → q (Inst.st s0 U) ≼ q (Inst.st s0 V) :=
  Inst.crdt_query_calm s0 q

/-- Sec. `sec:crdt-instance`: "Monotonicity of `q` on all of `D` suffices, but
`q` need only be monotone between reachable states."  Lean:
(1) sufficient; (2) `q ∘ s` is monotone iff `q` is monotone between reachable
states `s(U) ⊑ s(V)`; (3) not required: on the two-point lattice with
`s₀ = tt`, negation is not monotone but `neg ∘ s` is. -/
theorem «sec:crdt-instance/query-monotone-on-reachable» :
    (∀ {D Y : Type} [PO D] [Inst.JSL D] [PO Y] (s0 : D) {q : D → Y},
        Monotone q → Monotone (fun U : Inst.FSet D => q (Inst.st s0 U))) ∧
      (∀ {D Y : Type} [PO D] [Inst.JSL D] [PO Y] (s0 : D) (q : D → Y),
        Monotone (fun U : Inst.FSet D => q (Inst.st s0 U)) ↔
          ∀ U V : Inst.FSet D, Inst.st s0 U ≼ Inst.st s0 V → q (Inst.st s0 U) ≼ q (Inst.st s0 V)) ∧
      (¬ Monotone Inst.B2.neg ∧ Monotone (fun U : Inst.FSet Inst.B2 => Inst.B2.neg (Inst.st Inst.B2.tt U))) :=
  ⟨fun s0 _ hq => Inst.crdt_query_of_mono s0 hq, fun s0 q => Inst.crdt_query_mono_iff_reachable s0 q,
    Inst.crdt_query_mono_not_required⟩

/-- Sec. `sec:crdt-instance`: a two-phase set's "state `(Add, Del)` merges by
componentwise union.  The query `Add \ Del` can report a Ferrari in a shopping
cart before a delayed removal arrives … The query `Add \ Del` over a two-phase set fails the test: a
removal payload grows `U` and shrinks the answer."  Lean: payloads are pairs
`(Add, Del)` joined componentwise, `s₀ = (∅, ∅)`; with
`s(U₀) = ({potato, Ferrari}, ∅)` and `s(U₁) = ({potato, Ferrari}, {Ferrari})`,
`U₀ ⊆ U₁` but `q_2P(s(U₀)) = {potato, Ferrari} ⋠ {potato} = q_2P(s(U₁))`, so
`q_2P ∘ s` is not consistent, while the state specification `s` is. -/
theorem «sec:crdt-instance/two-phase» :
    Inst.st (Inst.emp, Inst.emp) Inst.U0 = (Inst.both, Inst.emp) ∧
      Inst.st (Inst.emp, Inst.emp) Inst.U1 = (Inst.both, Inst.sgl .ferrari) ∧
      Inst.q2P (Inst.st (Inst.emp, Inst.emp) Inst.U0) = Inst.both ∧
      Inst.q2P (Inst.st (Inst.emp, Inst.emp) Inst.U1) = Inst.sgl .potato ∧ Inst.U0 ≼ Inst.U1 ∧
      ¬ (Inst.q2P (Inst.st (Inst.emp, Inst.emp) Inst.U0) ≼ Inst.q2P (Inst.st (Inst.emp, Inst.emp) Inst.U1)) ∧
      ¬ (graph (fun U : Inst.FSet (Inst.PS × Inst.PS) => Inst.q2P (Inst.st (Inst.emp, Inst.emp) U))).Consistent ∧
      (graph (Inst.st (Inst.emp, Inst.emp) : Inst.FSet (Inst.PS × Inst.PS) → Inst.PS × Inst.PS)).Consistent :=
  ⟨Inst.st_U0, Inst.st_U1, Inst.twoPhase_unsafe⟩

/-- Sec. `sec:crdt-instance`: "CRDT states form a join-semilattice …"  Lean: a
merge that is commutative, associative, and idempotent orders states by
`x ≼ y ⟺ merge x y = y`; this relation is a partial order and `merge a b` is
the least upper bound of `a` and `b`. -/
theorem «sec:crdt-instance/semilattice» {D : Type} (m : Inst.CAI D) :
    let le := fun x y => m.merge x y = y
    (∀ x, le x x) ∧ (∀ x y z, le x y → le y z → le x z) ∧ (∀ x y, le x y → le y x → x = y) ∧
      ∀ a b, le a (m.merge a b) ∧ le b (m.merge a b) ∧ ∀ c, le a c → le b c → le (m.merge a b) c :=
  Inst.cai_semilattice m

/-- Sec. `sec:crdt-instance`: "CRDT states form a join-semilattice, but `q`
needs less: Complete CALM requires only some common output extension of query
outputs (Section `sec:lifted-monotonicity`), not a least one."  Lean: on the state
lattice `B2 × B2`, a monotone observation `qY` into a five-element order makes
`q ∘ s` consistent, yet its outputs `a = q(s({(tt,ff)}))` and
`b = q(s({(ff,tt)}))` have common output extensions (`c`, and also `d`) but no
least one. -/
theorem «sec:crdt-instance/some-refinement» :
    (graph (fun U : Inst.FSet (Inst.B2 × Inst.B2) => Inst.qY (Inst.st (Inst.B2.ff, Inst.B2.ff) U))).Consistent ∧
      Inst.qY (Inst.st (Inst.B2.ff, Inst.B2.ff) (Inst.FSet.ofList [(Inst.B2.tt, Inst.B2.ff)])) = Inst.Y5.a ∧
      Inst.qY (Inst.st (Inst.B2.ff, Inst.B2.ff) (Inst.FSet.ofList [(Inst.B2.ff, Inst.B2.tt)])) = Inst.Y5.b ∧
      (Inst.Y5.a ≼ Inst.Y5.c ∧ Inst.Y5.b ≼ Inst.Y5.c) ∧
      ¬ ∃ y : Inst.Y5, Inst.Y5.a ≼ y ∧ Inst.Y5.b ≼ y ∧ ∀ z, Inst.Y5.a ≼ z → Inst.Y5.b ≼ z → y ≼ z :=
  Inst.crdt_observation_no_join

/-! ## Highly available transactions (`sec:hat-instance`)

The opening paragraph ("Bailis et al. define isolation levels by Adya's
phenomena, adding sessions and per-item dependencies … We take their
assumptions as given.  Items are partially replicated, and a client sends
each operation to some replica of its item.  A transaction's writes carry a
unique client timestamp, and versions are ordered by timestamp, last writer
wins.  The system never aborts a transaction on its own.  A replica answers a
read with the highest-timestamped committed write of the item that it has
received; we call this the store's *read rule*.") fixes the model of `Instances/HATSpec.lean`; the read rule is
`HATSpec.hatOut`.  The next paragraph ("The HAT results illustrate the
intersection reasoning of Section `sec:intersection`.  An isolation level and a
store are separate specs on the same histories: the level constrains which
read answers may appear together, and the store answers each read by its read
rule.  The store held to a level is their intersection, and we ask which
intersections satisfy Lifted Monotonicity.") is realized by `HATSpec.store`,
`HATSpec.spec`, and `Inter.inter` (`«def:store-spec»`, `«thm:hat-levels»`).  After the timestamp paragraph
(`«sec:hat-instance/rc-timestamps»`), the paragraph on the algorithm for
monotonic atomic view is `«sec:hat-instance/mav-timestamps»`; the paragraph
recovering Bailis et al.'s classification (Table 3) is
`«sec:hat-instance/session-guarantees»`, in the model of
`Instances/HATTaxonomy.lean` (details in `Paper/AppB_HATTaxonomy.lean`, where
the differences in form are `«app:hat-taxonomy/form-choices»`); and the
paragraph on the extended paper's definition of read your writes (Def. 34) is
`«sec:hat-instance/myr-as-written»`. -/

/-- **Definition `def:hat-spec`** (HAT specification): "An input is a history
ordered by happens-before.  It contains reads, each tagged with its replica;
commits, each
with its client timestamp and write set; and arrivals of committed writes
at replicas.  The history preserves each client's program order and each
replica's arrival order, and a transaction's reads precede its commit, which
precedes the arrivals of its writes at replicas.  One input extends another when it adds events, none of which
happens before an event already present.  An output is a set of read answers, ordered by
inclusion.  A history is *complete* when it answers every read and orders
versions by timestamp.  For an isolation level `L`, the table `P_L` of `𝒮_L`
contains an output at an input when the input extends to a complete history
that includes the output and exhibits none of the phenomena that `L`
proscribes.  The explicit relation `E` contains, at each input, the output
that the read rule gives."  (CIDR version:
"An input is a history: a set of events, partially ordered by happens-before,
of three kinds.  A read is tagged with its replica; a commit carries its
timestamp and write set; a delivery brings a committed write to a replica.  One
input extends another when it adds events, none of which happens before an
event already present.  An output is a set of read answers, ordered by
inclusion.  An isolation level `L` is defined by the phenomena it proscribes.
A history is complete when …" as above.)  A complete history is `HATSpec.CH`;
`P_L` contains `F` when `F ≼ H.facts` for some complete `H` avoiding the
phenomena (`HATSpec.specP`).
Lean: inputs `HATSpec.Inp true` (events `rd`, `cm`, and `dl` for arrivals; legality `WF` plus
the timestamp condition of Thm. `thm:hat-levels`, so that the theorem's
hypothesis is part of the input domain; of program order only "reads precede
their commit" is required); `𝒮_L = HATSpec.spec L`; `E = HATSpec.hatA`, the
rows `(j, hatOut j)`.  A history (`HATSpec.CH`) returns, for each read, the
initial version or one installed by another committed transaction; levels
are item-only (`HATSpec.Level`: RU, RC, SI, RR, SER). -/
abbrev «def:hat-spec» (L : HATSpec.Level) : Spec (HATSpec.Inp true) (IConf.St HATSpec.Fact) :=
  HATSpec.spec L

/-- Def. `def:hat-spec`: "One input extends another when it adds events, none of
which happens before an event already present."
Lean: inputs are closed under the order: a downward-closed sub-history of a
legal input is legal, and satisfies the timestamp condition if the input
does. -/
theorem «def:hat-spec/inputs-closed» {a b : IConf.Hist HATSpec.Ev} (hab : a ≼ b) :
    (HATSpec.WF b → HATSpec.WF a) ∧ (HATSpec.Lamport b → HATSpec.Lamport a) :=
  ⟨HATSpec.wf_down hab, HATSpec.lamport_down hab⟩

/-- Def. `def:hat-spec`: "The explicit relation `E` holds, at each input, the
answers that the read rule above gives", i.e. "A replica answers a read with the highest-timestamped
committed write of the item that it has received."  Lean: `hatOut j` answers
read event `e` with the highest timestamp among the writes of its item
delivered to its replica before `e` (or the initial version); every read gets
exactly one answer. -/
theorem «def:hat-spec/read-rule» :
    ∀ (j : HATSpec.Inp true) e, HATSpec.IsRd j e → (∃ v, HATSpec.hatOut j (.read e v)) ∧
      ∀ v v', HATSpec.hatOut j (.read e v) → HATSpec.hatOut j (.read e v') → v = v' :=
  HATSpec.hat_rule.1

/-- **Definition `def:store-spec`** (Store specification): "The store
specification `𝒮_st` has the inputs and outputs of Definition `def:hat-spec`.
At each input, it permits any subset of the answers that the read rule
gives."  And after it: "The store spec says only that answers follow the read
rule, and nothing about isolation.  On its own it satisfies Lifted
Monotonicity: a read's answer under the read rule depends only on the writes
its replica received before the read, so later input never changes it.  The
store's rows that answer every read are exactly the rows of `E`."  Next
paragraph: "Holding the store to an isolation level `L` means taking the intersection `𝒮_st ∩ 𝒮_L`
(Definition `def:intersection`), which is total, since both specs permit
answering no reads.  By Proposition `prop:intersection-bound`, the
intersection keeps Lifted Monotonicity when `𝒮_L` permits the read rule's
answers."  Lean: `HATSpec.store`; its fiber at `j`
is the subsets of `hatOut j`, so the rows of `E = HATSpec.hatA` are its full
rows; the store satisfies Lifted Monotonicity (`HATSpec.store_liftedMono`, via
`HATSpec.hatOut_mono`, which is `«thm:hat-levels/answers-stable»`); the
intersection is total (`HATSpec.store_inter_total`); the bound step is
`«prop:intersection-bound»`. -/
theorem «def:store-spec» :
    (∀ (j : HATSpec.Inp true) F, (HATSpec.store (lam := true)).P j F ↔ F ≼ HATSpec.hatOut j) ∧
      (∀ j o, HATSpec.hatA j o → (HATSpec.store (lam := true)).P j o) ∧
      (∀ (L : HATSpec.Level) (j : HATSpec.Inp true),
        ∃ o, (HATSpec.store (lam := true)).P j o ∧ (HATSpec.spec L).P j o) ∧
      (HATSpec.store (lam := true)).LiftedMono :=
  ⟨fun _ _ => Iff.rfl, fun _ _ h => h ▸ PO.refl _,
    fun L => HATSpec.store_inter_total (HATSpec.Proscribed L) fun j => HATSpec.serial_clean j L,
    HATSpec.store_liftedMono⟩

/-- **Theorem `thm:hat-levels`** (HAT levels): "Suppose each transaction's
timestamp exceeds that of every version it reads.  For read uncommitted and
read committed, `E ⊆ P_L` and `𝒮_st ∩ 𝒮_L` satisfies Lifted Monotonicity, so
`𝒮_L` satisfies Lifted Monotonicity for `E`, so some system for `𝒮_L` has
Availability for `E` and Partition Consistency.  For any level that proscribes
Lost Update, including snapshot isolation, repeatable read, and
serializability, `𝒮_st ∩ 𝒮_L` does not satisfy Lifted Monotonicity, and `𝒮_L`
does not satisfy Lifted Monotonicity for any explicit relation `E` that
answers every read; hence no system for `𝒮_L` has Availability for such an
`E` and Partition Consistency."  Lean:
(1) for `L ∈ {RU, RC}`, `E ⊆ P_L`, Lifted Monotonicity of the intersection
(`HATSpec.store_inter_rc`), Lifted Monotonicity for `E`
(`CAP.ConsistentOn`), and some system with Availability for `E` and
Partition Consistency (`CAP.complete_cap_for`); (2) for any proscribed set
`P` containing Lost Update (avoided by the serial history, so `𝒮_P` is a
specification), the intersection `𝒮_st ∩ 𝒮_P` fails Lifted Monotonicity
(`HATSpec.store_inter_lostUpdate`), and every `E ⊆ P_P` that answers every read fails Lifted
Monotonicity for `E`, and no system has Availability for `E` and Partition
Consistency; (3) in particular for SI, RR, and serializability.  The
hypothesis is the timestamp condition on inputs: under `E`, the version a
read returns is the highest delivered before it, so "exceeds every version
it reads" and "exceeds every version delivered before its reads" agree.
Part (2) holds with or without it. -/
theorem «thm:hat-levels» (D : Type) :
    (∀ L, L = .RU ∨ L = .RC →
      (∀ i o, HATSpec.hatA i o → (HATSpec.spec (lam := true) L).P i o) ∧
        (∃ htot, (Inter.inter (HATSpec.store (lam := true)) (HATSpec.spec L) htot).LiftedMono) ∧
        CAP.ConsistentOn (HATSpec.spec (lam := true) L) HATSpec.hatA ∧
        ∃ Sys : CAP.System (HATSpec.spec (lam := true) L) D,
          CAP.AvailabilityFor HATSpec.hatA Sys ∧ CAP.PartitionConsistencyAtEnd Sys) ∧
    (∀ (P : (j : HATSpec.Inp true) → HATSpec.CH j → Prop) (hP : ∀ j, ¬ P j (HATSpec.serial j)),
      (∀ j (H : HATSpec.CH j), HATSpec.LostUpdate H → P j H) →
      (∀ htot, ¬ (Inter.inter (HATSpec.store (lam := true)) (HATSpec.specP P hP) htot).LiftedMono) ∧
      ∀ (E : Table (HATSpec.Inp true) (IConf.St HATSpec.Fact)),
        (∀ i o, E i o → (HATSpec.specP P hP).P i o) → (∀ i, ∃ o, E i o) →
        (∀ i o e, E i o → HATSpec.IsRd i e → ∃ v, o (.read e v)) →
        ¬ CAP.ConsistentOn (HATSpec.specP P hP) E ∧
          ¬ ∃ Sys : CAP.System (HATSpec.specP P hP) D,
            CAP.AvailabilityFor E Sys ∧ CAP.PartitionConsistencyAtEnd Sys) ∧
    (∀ L, L = .SI ∨ L = .RR ∨ L = .SER → ∀ (j : HATSpec.Inp true) (H : HATSpec.CH j),
      HATSpec.LostUpdate H → HATSpec.Proscribed L j H) :=
  ⟨fun L hL => let h := HATSpec.rc_available L hL D; ⟨h.1, HATSpec.store_inter_rc L hL, h.2⟩,
    fun P hP hLU => ⟨fun htot => (HATSpec.store_inter_lostUpdate P hP hLU htot).2,
      fun E hES htot hans => HATSpec.lostUpdate_unavailableP P hP hLU D E hES htot hans⟩,
    fun L hL _ H h => HATSpec.proscribes_lostUpdate L hL H h⟩

/-- Proof sketch of Thm. `thm:hat-levels`: "The theorem has two parts.  First,
for read uncommitted and read committed, the timestamp condition rules out the
dependency cycles of G0 and G1c, so `𝒮_L` permits the read rule's answers.
Proposition `prop:intersection-bound`, with the read rule as the bound, then
gives Lifted Monotonicity of `𝒮_st ∩ 𝒮_L`, whose rows include those of `E`."  (The bound
step is `HATSpec.store_inter_rc`; monotonicity of the rule, stated with the
store specification, is the first conjunct here.)  Lean:
the candidates of a read are the same at every input extension containing it
(`HATSpec.cand_iff`), so `hatOut` is monotone; under the timestamp condition
every read- and write-dependency of HAT's history increases timestamps, so
`hatOut j ∈ P_RC(j)`. -/
theorem «thm:hat-levels/answers-stable» :
    (∀ i j : HATSpec.Inp true, i ≼ j → HATSpec.hatOut i ≼ HATSpec.hatOut j) ∧
      ∀ j : HATSpec.Inp true, (HATSpec.spec .RC).P j (HATSpec.hatOut j) :=
  ⟨HATSpec.hat_rule.2, HATSpec.hatOut_rc⟩

/-- Proof sketch of Thm. `thm:hat-levels`: "Second, for a level that
proscribes Lost Update, the intersection loses Lifted Monotonicity, because the
read rule's own answers can exhibit Lost Update.  Let two transactions at
different replicas each read `x₀` and write `x`.  Under the
read rule, each replica can answer only `x₀`, since neither has received the
other's write.  Together the two answers contain a cycle on `x` with an
anti-dependency, which is Lost Update.  So the store's answer at one replica
has no extension in `𝒮_st ∩ 𝒮_L` once both transactions are in the
input.  The store needs no commitment on its own, so this need comes from the
intersection with `𝒮_L`.  In both parts, the conclusions about systems
follow from Complete CAP (Theorem `thm:complete-cap`) and Corollary
`cor:complete-cap-any-system`."  (The store's own Lifted Monotonicity is
`HATSpec.store_liftedMono`; the last step is `HATSpec.store_inter_lostUpdate`: the row of `T₂`'s
answer `x₀` at `i₂` has no extension at the union; `HATSpec.i2_ans`.)  Lean: `T₁` (timestamp `(1,1)`) and
`T₂` (`(1,2)`) read and write `x` at replicas 0 and 1, with no arrival event; at
each one-transaction input the only version a read may return is `x₀`; in
every complete history of the union in which `T₂` read `x₀`, the
anti-dependency `T₂ → T₁` and the write-dependency `T₁ → T₂` on `x` form a
Lost Update (and a G2) cycle. -/
theorem «thm:hat-levels/lost-update-pair» :
    (∀ v, HATSpec.Ver (HATSpec.i1 (lam := true)) 1 1 0 v → v = HATRC.tsInit) ∧
      (∀ v, HATSpec.Ver (HATSpec.i2 (lam := true)) 2 1 0 v → v = HATRC.tsInit) ∧
      HATSpec.i1 (lam := true) ≼ HATSpec.iJ ∧ HATSpec.i2 (lam := true) ≼ HATSpec.iJ ∧
      ∀ H : HATSpec.CH (HATSpec.iJ (lam := true)), H.ans 2 = HATRC.tsInit →
        HATSpec.LostUpdate H ∧ HATSpec.G2 H :=
  ⟨fun _ h => HATSpec.i1_ver h, fun _ h => HATSpec.i2_ver h, HATSpec.le_hJ _ HATSpec.hk1,
    HATSpec.le_hJ _ HATSpec.hk2, fun H h => HATSpec.lu_cycle H h⟩

/-- "The timestamp condition in the theorem is required, correcting an error in
the extended HAT paper.  That paper's pseudocode
fixes each transaction's timestamp when it begins.  A transaction can then read
a version with a higher timestamp than its own and overwrite it, so its write
is ordered before the version it read: a G1c cycle, which read committed
proscribes.  The algorithm as written therefore does not guarantee read
committed.  Our framework exposed the problem directly as we were writing this
up, since the read rule's output at such an input is not in `P_RC`.
Taking each timestamp at commit, above every version read, repairs the
algorithm."  (CIDR adds: "Details are in the full paper.")  Lean: (1) in the specification
without the timestamp condition (`Inp false`), an input where `T₁` reads
`T₂`'s version `(1,2)` and then commits `x` with timestamp `(1,1)` has HAT's
answer outside `P_RC`; (2) the pseudocode itself, run with timestamps fixed at
`BEGIN` (`HATRC`), produces that G1c history; (3) with Lamport timestamps
taken at commit, every run is PL-2 (no G1a, G0, G1c; distinct timestamps). -/
theorem «sec:hat-instance/rc-timestamps» :
    (¬ HATSpec.Lamport HATSpec.wHist ∧ ¬ (HATSpec.spec .RC).P HATSpec.wInp (HATSpec.hatOut HATSpec.wInp)) ∧
      (HATRC.ww HATRC.wfinal (1, 1) (1, 2) ∧ HATRC.wr HATRC.wfinal (1, 2) (1, 1) ∧
        HATRC.G1c HATRC.wfinal ∧ ¬ HATRC.G1a HATRC.wfinal) ∧
      ∀ l, ((HATRC.run .lamport l).commits.map (·.ts)).Nodup ∧
        ¬ HATRC.G1a (HATRC.run .lamport l) ∧ ¬ HATRC.G0 (HATRC.run .lamport l) ∧
        ¬ HATRC.G1c (HATRC.run .lamport l) :=
  ⟨⟨HATSpec.timestamp_condition_needed.1, HATSpec.timestamp_condition_needed.2.2⟩,
    HATRC.g1c_witness.2.2.2, fun l => let h := HATRC.lamport_pl2 l; ⟨h.1, h.2.2⟩⟩

/-- Sec. `sec:hat-instance`: "The extended paper's algorithm for monotonic
atomic view has the same error.  Its clients run the read committed algorithm
and also fix each timestamp when the transaction begins.  When a transaction
reads a version with a higher timestamp than its own and then overwrites that
item, the algorithm's answers contain the same G1c cycle.  So the algorithm
does not guarantee read committed, and therefore not monotonic atomic view
either.  With timestamps taken at commit, above every version read, it provides
monotonic atomic view (Appendix `app:hat-taxonomy`)."

Lean (`Instances/HATAppB.lean`, the algorithm of the extended paper's App. B
as `HATTax.outB`): (1) on input `w7`, without the timestamp condition, the
algorithm's answers are outside `P_RC`, hence outside `P_MAV`, whose
phenomena include G1c (`HATTax.appB_not_rc`); (2) under the timestamp
condition, for every acknowledgment schedule, monotonic atomic view is highly
available with the algorithm as explicit relation (`HATTax.mav_appB`; Prop.
`prop:hat-mav-algorithm`). -/
theorem «sec:hat-instance/mav-timestamps» (D : Type) :
    ¬ (HATTax.tax (reps := HATTax.r0) (lam := false) .RC).P HATTax.w7
        (HATTax.outB HATTax.stableK HATTax.w7) ∧
      ∀ (reps : Nat → List Nat) (K : HATTax.AckK reps),
        HATTax.HighlyAvailable (reps := reps) (lam := true) (HATTax.tax .MAV) D :=
  ⟨HATTax.appB_not_rc, fun _ K => HATTax.mav_appB K D⟩

/-- Sec. `sec:hat-instance`: "Bailis et al. also classify session guarantees
and recency alongside further isolation levels, calling them all
*guarantees*.  Each guarantee `G` becomes a spec `𝒮_G`: a store that returns
only versions the reading replica has received, held to `G`.  Their high
availability becomes Availability for an explicit relation inside `𝒮_G` that
answers every read, together with Partition Consistency, so by Theorem
`thm:complete-cap` it holds exactly when `𝒮_G` satisfies Lifted Monotonicity
for such a relation.  Their sticky availability, in which each client is
served by a replica that already holds its earlier writes, becomes Deployment
Availability for a deployment that assigns clients to replicas (Proposition
`prop:deployment-complete-cap`).  Their algorithms supply the explicit
relations.  Our mapping recovers their classification of every guarantee, each
as an instance of Complete CAP or its deployment form (Theorem
`thm:hat-taxonomy`, Appendix `app:hat-taxonomy`)."

Lean: Bailis et al.'s classification (VLDB 2014, Table 3; guarantees as the
phenomena of the extended paper's App. A), in the model of
`Instances/HATTaxonomy.lean` (each guarantee is the visibility store held to
it, `HATTax.tax`; high and sticky availability are `HATTax.HighlyAvailable`
and `HATTax.StickyAvailable`, and `HATTax.highlyAvailable_iff` is the step
through `CAP.complete_cap_for`):

* *highly available* (RC and MAV under the timestamp condition, I-CI, P-CI,
  MR, MW, WFR): the reveal rule is an explicit relation inside the spec that
  answers every read and is monotone (`HATTax.ha_of_rule`); for MAV also the
  App. B algorithm itself (`«sec:hat-instance/mav-timestamps»`);
* *sticky available* (RYW, PRAM, causal; also the highly available session
  guarantees): the sticky rule (`HATTax.sticky_of_rule`); as a deployment
  (`HATTax.stickyD`) it is monotone across partitions, so by Prop.
  `prop:deployment-complete-cap` some system has Deployment Availability and
  Partition Consistency for it (`HATTax.stickyD_available`);
* *not highly available*: RYW, PRAM and causal (`HATTax.ryw_not_ha`); recency,
  which is not sticky available either (`HATTax.recency_not_ha`,
  `HATTax.recency_not_sticky`); and any level proscribing Write Skew
  (`HATSpec.WS.writeSkew_unavailable`; Lost Update is `«thm:hat-levels»`).
  The negative results for RYW and recency assume only that item `0` has
  replica `0`.

The reveal rule in Lean reveals a write once its transaction and every
transaction committed before it are pending stable, for all highly available
guarantees at once (`HATTax.Rev`, `HATTax.DepStable`); for MAV the App. B
algorithm, which waits only for pending stability, gives the same
classification. -/
theorem «sec:hat-instance/session-guarantees» (reps : Nat → List Nat) (lam : Bool) (D : Type) :
    (∀ g, HATTax.HAGuar lam g → HATTax.HighlyAvailable (reps := reps) (lam := lam) (HATTax.tax g) D) ∧
    (∀ g (hg : HATTax.StickyGuar g),
      HATTax.StickyAvailable (reps := reps) (lam := lam) (HATTax.tax g) D ∧
      ∀ (n : Nat) (srv : Nat → Fin n), 2 ≤ n →
        Deploy.MonoAcrossPartitions (HATTax.stickyD (reps := reps) (lam := lam) hg srv) ∧
        ∃ Sys : CAP.System (HATTax.tax (reps := reps) (lam := lam) g) D,
          Deploy.DeploymentAvailability Sys (HATTax.stickyD hg srv) ∧
          Deploy.PartitionConsistencyAt Sys n) ∧
    (0 ∈ reps 0 →
      (∀ g, (g = .RYW ∨ g = .PRAM ∨ g = .Causal) →
        ¬ HATTax.HighlyAvailable (reps := reps) (lam := lam) (HATTax.tax g) D) ∧
      ¬ HATTax.HighlyAvailable (reps := reps) (lam := lam) (HATTax.tax .Rec) D ∧
      ¬ HATTax.StickyAvailable (reps := reps) (lam := lam) (HATTax.tax .Rec) D) ∧
    (∀ (L : HATSpec.Level), (L = .RR ∨ L = .SER) →
      ∀ A : Table (HATSpec.Inp lam) (IConf.St HATSpec.Fact), (∀ i o, A i o → (HATSpec.spec L).P i o) →
        (∀ i, ∃ o, A i o) → (∀ i o e, A i o → HATSpec.IsRd i e → ∃ v, o (.read e v)) →
        ¬ ∃ Sys : CAP.System (HATSpec.spec L) D,
          CAP.AvailabilityFor A Sys ∧ CAP.PartitionConsistencyAtEnd Sys) :=
  ⟨fun _ hg => HATTax.ha_of_rule hg D,
   fun _ hg => ⟨HATTax.sticky_of_rule hg D, fun _ srv hn =>
     ⟨HATTax.stickyD_monoAcross hg srv, HATTax.stickyD_available hg hn srv D⟩⟩,
   fun h0 => ⟨fun _ hg => HATTax.ryw_not_ha h0 hg D, HATTax.recency_not_ha h0 D,
     HATTax.recency_not_sticky h0 D⟩,
   fun L hL A hAS ht ha => (HATSpec.WS.writeSkew_unavailable L hL D A hAS ht ha).2⟩

/-- Sec. `sec:hat-instance`: "Stating the classification precisely also exposed
a mismatch in the extended paper.  Its formal definition of the anomaly that
read your writes rules out lets the forbidden cycle pass through other
clients' transactions on other items [Def. 34].  Under that definition, read
your writes is not sticky available.  Consider two clients at partitioned replicas.
Client 1 writes `x`, and then a second transaction of client 1 reads `x` and
`y` at its own replica, which has its write of `x` but no write of `y`.
Client 2 reads `x` at the other replica, which has no write of `x`, and writes
`y`.  Every read is sticky, and each replica can return only the initial
version of the item it lacks.  Together these answers form the forbidden
cycle, so no system can keep both clients available and stay consistent, even
with each client assigned to its own replica.  The definition's own example
uses a single item, and in that form read your writes is sticky available, as
Bailis et al. state."

Lean: Def. 34 as written ("a directed cycle consisting of a transitive
session-dependency between transactions `T_j` and `T_i`, at least one
anti-dependency edge, and the remainder anti-dependency or write-dependency
edges") is `HATTax.MYRlit`.  So defined, read your writes is not sticky
available (`HATTax.myrLit_not_sticky`), and no deployment that puts clients 1
and 2 on different participants, each answering its client's sticky reads,
has a system with Deployment Availability and Partition Consistency
(`HATTax.myrLit_not_sticky_deploy`).  The cycle is
`T₁ →s T₂ →rw_y T₃ →rw_x T₁`.  The single-item form (`HATTax.MYR`) is sticky
available (`«sec:hat-instance/session-guarantees»`). -/
theorem «sec:hat-instance/myr-as-written» (reps : Nat → List Nat) (lam : Bool) (D : Type)
    (h00 : 0 ∈ reps 0) (h01 : 0 ∈ reps 1) (h10 : 1 ∈ reps 0) :
    ¬ HATTax.StickyAvailable (reps := reps) (lam := lam) (HATTax.tax .RYWlit) D ∧
      (∀ {n : Nat}, 2 ≤ n → ∀ (Dp : Deploy.Deployment (HATTax.tax (reps := reps) (lam := lam) .RYWlit) n)
        (srv : Nat → Fin n), srv 1 ≠ srv 2 → HATTax.StickyComplete Dp srv →
        ∀ Sys : CAP.System (HATTax.tax (reps := reps) (lam := lam) .RYWlit) D,
          ¬ (Deploy.DeploymentAvailability Sys Dp ∧ Deploy.PartitionConsistencyAt Sys n)) ∧
      HATTax.StickyAvailable (reps := reps) (lam := lam) (HATTax.tax .RYW) D :=
  ⟨HATTax.myrLit_not_sticky h00 h01 h10 D,
   fun hn Dp srv hsrv hst Sys => HATTax.myrLit_not_sticky_deploy h00 h01 h10 hn Dp srv hsrv hst Sys,
   HATTax.sticky_of_rule (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl rfl)))))) D⟩

/-! ## Invariant confluence (`sec:iconfluence-instance`) -/

/-- Sec. `sec:iconfluence-instance`, the model of Bailis et al.: states are
sets of versions merged by union, transactions are inflationary
(`t(s) ⊇ s`), `s₀` satisfies `𝓘`.  Lean: `IConf.Model V Tx` (fields `app`,
`infl`, `s0`, `Inv`, `init`). -/
abbrev «sec:iconfluence-instance/model» (V Tx : Type) : Type := IConf.Model V Tx

/-- "A state is reachable when it can be derived from `s₀` by
applying transactions and merging states, with every state along the way
satisfying `𝓘`."  Lean: the inductive predicate `IConf.Reach M`. -/
abbrev «sec:iconfluence-instance/reachable» {V Tx : Type} (M : IConf.Model V Tx) :
    IConf.St V → Prop := IConf.Reach M

/-- "`T` is invariant confluent exactly when `𝓘(s₁ ∪ s₂)` for all reachable
`s₁` and `s₂`."  Lean: `IConf.Model.IConfluent`. -/
theorem «sec:iconfluence-instance/iconfluent-def» {V Tx : Type} (M : IConf.Model V Tx) :
    M.IConfluent ↔ ∀ s₁ s₂, IConf.Reach M s₁ → IConf.Reach M s₂ → M.Inv (s₁.union s₂) :=
  Iff.rfl

/-- "Every reachable state descends from `s₀`, so `T` is invariant confluent
exactly when `𝓘(s₁ ∪ s₂)` for all reachable `s₁` and `s₂`."  This is the
step from Bailis et al.'s Def. 6 (merges of I-T-reachable states with a
common ancestor) to the reading above.  Lean: `s₀` is an ancestor of every
reachable state; the states reachable from `s₀` by at least one invocation
are the reachable states; and both readings of Def. 6 (explicit reachable
ancestor `BailisIC`; literal common ancestor `BailisAnc`) are equivalent to
`IConfluent`. -/
theorem «sec:iconfluence-instance/bailis-definition» {V Tx : Type} (M : IConf.Model V Tx) :
    (∀ {s}, IConf.Reach M s → IConf.Anc M M.s0 s) ∧
      (∀ s, (∃ a, IConf.Anc M a s) ↔ IConf.Reach M s) ∧
      (IConf.BailisIC M ↔ M.IConfluent) ∧ (IConf.BailisAnc M ↔ M.IConfluent) :=
  ⟨IConf.s0_anc, IConf.reachPlus_iff, IConf.bailis_iff, IConf.bailisAnc_iff⟩

/-- "From an instance `(s₀, T, 𝓘)` of their model we construct a
spec `𝒮_𝓘` in ours as follows.  Inputs are transaction histories:
partial orders of events, each labeled by a transaction in `T`, where one
event precedes another when the second ran on a state that included the
first's writes.  One history extends another when it adds events, none of
which precedes an event already present.  Legal inputs include only the
locally valid histories, in which each transaction preserves `𝓘` on the
state it ran on.  Outputs are database states, ordered by set-containment of
versioned data.  The state of a history is `s₀` together with every version
its transactions write.  Call a sub-history closed when it contains every
event that precedes one of its own, and valid when the state of each of its
closed sub-histories satisfies `𝓘`.  At input `h`, each valid closed
sub-history of `h` contributes its state as a permitted output.  An output
may therefore leave out some of the input's transactions, but what it
includes must be closed and valid."  Lean (a closed sub-history of `h` is a
`g ≼ h`):
`IConf.SI M` on inputs `IConf.Inp M` (locally valid histories, input extension
order) with outputs `IConf.St V` under inclusion; full model in
`Paper/AppB_InvariantConfluence`. -/
theorem «sec:iconfluence-instance/spec» {V Tx : Type} (M : IConf.Model V Tx) (h : IConf.Inp M)
    (s : IConf.St V) :
    (IConf.SI M).P h s ↔ ∃ g, g ≼ h.1 ∧ IConf.Valid M g ∧ IConf.eval M g = s :=
  Iff.rfl

/-- **Proposition `prop:iconfluence-lm`** (Invariant confluence as Lifted
Monotonicity): "`T` is invariant confluent if and only if `𝒮_𝓘` satisfies
Lifted Monotonicity, that is, if and only if the runs of `𝒮_𝓘` are
consistent."

Lean: the first claim is `IConf.ic_iff_liftedMono`; the second ("that is")
follows by Complete CALM (`complete_calm`), which equates Lifted Monotonicity
of a spec with consistency of its runs (`Spec.Consistent`). -/
theorem «prop:iconfluence-lm» {V Tx : Type} (M : IConf.Model V Tx) :
    (M.IConfluent ↔ (IConf.SI M).LiftedMono) ∧
      (M.IConfluent ↔ (IConf.SI M).Consistent) :=
  ⟨IConf.ic_iff_liftedMono M, (IConf.ic_iff_liftedMono M).trans (complete_calm _).symm⟩

/-- The uniqueness example: "The uniqueness constraint in Bailis et al.'s
payroll example is not invariant confluent, and in `𝒮_𝓘` the failure is a
fiber that is not directed.  Let `c₁` and `c₂` be creations at two replicas
that each assign ID 7, each running on a state in which ID 7 is unused, and let
`h` be the history in which neither ran on a state that included the other's
writes. … `h` is locally valid, and it extends both one-creation histories.
At `h` the closed sub-histories are `∅`, `{c₁}`, `{c₂}`, and `h` itself.  The
first three are valid, but `h` is not, since its state has two employees with
ID 7.  So the outputs permitted at `h` are `s₀` and the states of `{c₁}` and
`{c₂}`.  None of them contains the employees created by both `c₁` and `c₂`, so
none extends both one-creation states.  The fiber at `h` is therefore not
directed, and `𝒮_𝓘` fails Lifted Monotonicity at `h`."  The entry checks that
no output permitted at `h` extends both one-creation states, the step the
enumeration of sub-histories justifies.  Lean (library names from an earlier
username version of the example): versions are the employees holding ID 7;
`alloc a` creates employee `a` with ID 7 if ID 7 is unused in the state it runs on;
the invariant `uModel.Inv` is "at most one employee has ID 7"; `jU` has the
unordered events `alloc 1`, `alloc 2`; `oneU n t` is the one-event history.
Consequently `𝒮_𝓘` fails Lifted Monotonicity and the transactions are not
invariant confluent. -/
theorem «sec:iconfluence-instance/uniqueness» :
    IConf.LocValid Inst.uModel Inst.jU ∧ Inst.oneU 0 1 ≼ Inst.jU ∧ Inst.oneU 1 2 ≼ Inst.jU ∧
      IConf.eval Inst.uModel Inst.jU 1 ∧ IConf.eval Inst.uModel Inst.jU 2 ∧
      ¬ Inst.uModel.Inv (IConf.eval Inst.uModel Inst.jU) ∧
      (∀ u, (IConf.SI Inst.uModel).P ⟨Inst.jU, Inst.locValid_jU⟩ u →
        ¬ (IConf.eval Inst.uModel (Inst.oneU 0 1) ≼ u ∧ IConf.eval Inst.uModel (Inst.oneU 1 2) ≼ u)) ∧
      ¬ (IConf.SI Inst.uModel).LiftedMono ∧ ¬ Inst.uModel.IConfluent :=
  Inst.uniqueness_example

/-- The uniqueness example: "Each creation preserves `𝓘` on the state it ran
on" (from `s₀`), while the merge of the two states violates it.  Lean: `alloc 1` and `alloc 2`, each run from
`s₀`, give states satisfying the invariant, but the merge of the two states is
invalid. -/
theorem «sec:iconfluence-instance/concurrency-decides» :
    Inst.uModel.Inv (Inst.uModel.app 1 Inst.uModel.s0) ∧
      Inst.uModel.Inv (Inst.uModel.app 2 Inst.uModel.s0) ∧
      ¬ Inst.uModel.Inv ((Inst.uModel.app 1 Inst.uModel.s0).union (Inst.uModel.app 2 Inst.uModel.s0)) :=
  ⟨fun a b ha hb => by
      rcases ha with ha | ⟨rfl, _⟩
      · exact ha.elim
      rcases hb with hb | ⟨rfl, _⟩
      · exact hb.elim
      rfl,
    Inst.uniqueness_concurrency.2.1, Inst.uniqueness_concurrency.2.2⟩

/-! ## General operational specification models (`sec:operational-models`)

The opening paragraph ("Many systems are specified as state machines.  This
subsection shows how to project a state machine written as an I/O automaton
onto a spec, and how to analyze the automaton with our results. … We close
with two ways to check these properties in practice: testing on bounded
inputs, and proof.") outlines the subsection.  Its claims are the entries
below: "Each row of the projected spec is a pair the automaton can be observed
in: the requests it has received and the replies it has sent, as they occur
together in some trace" is Def. `def:projection`; "Every execution of the
automaton is a run of this spec" is Prop. `prop:projection` (1); "a run of the
spec may combine rows that no single execution reaches in that order" and
"After such a commitment, it can no longer reach some rows that other
executions do reach" are `«sec:operational-models/registrar»`; "Complete CALM
tells whether the projected spec's runs are consistent" is Prop. `prop:projection`
(2); and "it is confluent exactly when its commitments never remove every row
its canonical runs could still agree on" is Prop. `prop:automaton-confluence`
(2).

"The automaton model": "We use the standard I/O-automaton model.  An
automaton has input, output, and internal actions, a set of states with a
nonempty set of start states, and a transition relation in which every input
action is enabled in every state.  A finite execution takes a sequence of
steps from a start state.  We read the automaton as a server. … The
*receive sequence* of an execution lists its input actions in order, and its
*reply sequence* lists its output actions in order.  We order both kinds of
sequence by prefix."

Lean: Lynch–Tuttle I/O automata are `CC.IOA.Automaton`
(`Foundations/IOAutomata.lean`: signature, start states with
`start_nonempty`, transitions with `input_enabled`); a finite execution is
`IOA.Execution M β s` (schedule `β`, final state `s`).  The receive and reply
sequences are `IOT.recvs M β` and `IOT.replies M β`, as elements of
`IOT.InS M` and `IOT.OutS M` (`IOT.inW`, `IOT.outW`), ordered by prefix
(`IOT.Wd.instPO`).  The reading as a server (arrival, handing to the
computation, when a reply fires) and the closing remarks ("This subsection
treats a single automaton.  A server built from several communicating
automata is a distributed system in the sense of Section
`sec:distributed-execution`.") describe the model and are argued in prose
only (see the README). -/

/-- **Def. `def:projection`** (Projection of an automaton).  "The
*projection* of an automaton `M` is the I/O specification `P_M` whose inputs
are receive sequences and whose outputs are reply sequences, and whose rows
are the pairs `(w,t)` for which some finite execution of `M` has receive
sequence `w` and reply sequence `t`.  We call `P_M` the *projected spec* of
`M`."

Lean: `IOT.spec M`; this theorem gives the rows and the prefix order. -/
theorem «def:projection» {A : Type} (M : IOA.Automaton A) :
    (∀ w t, (IOT.spec M).P w t ↔
      ∃ β s, IOA.Execution M β s ∧ IOT.inW M β = w ∧ IOT.outW M β = t) ∧
    (∀ w w' : IOT.InS M, w ≼ w' ↔ w.val <+: w'.val) ∧
    (∀ t t' : IOT.OutS M, t ≼ t' ↔ t.val <+: t'.val) :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-- "Followed step by step, an execution is a run of `P_M`.  An arrival is an
input event carrying the receive sequence so far, a reply is an output event
carrying the reply sequence so far, and an internal step is no event.  What
grows along the execution is the reply sequence, whatever the replies say: a
counter's reports may go up, down, and up again, and its reply sequence still
only grows."

Lean: `IOT.evs M β` is defined this way (`IOT.evsFrom`); the run itself is
Prop. `prop:projection` (1).  The reply and receive sequences grow along an
execution whatever the actions are (`IOT.outW_le_append`,
`IOT.inW_le_append`), and the events determine the trace
(`IOT.evs_inj`). -/
theorem «sec:operational-models/step-by-step» {A : Type} (M : IOA.Automaton A) :
    (∀ (pre : List A) (a : A) (r : List A),
      (M.sig.inp a → IOT.evsFrom M pre (a :: r) =
        .input (IOT.inW M (pre ++ [a])) :: IOT.evsFrom M (pre ++ [a]) r) ∧
      (M.sig.out a → IOT.evsFrom M pre (a :: r) =
        .output (IOT.outW M (pre ++ [a])) :: IOT.evsFrom M (pre ++ [a]) r) ∧
      (M.sig.int a → IOT.evsFrom M pre (a :: r) = IOT.evsFrom M (pre ++ [a]) r)) ∧
    (∀ β γ : List A, IOT.outW M β ≼ IOT.outW M (β ++ γ) ∧ IOT.inW M β ≼ IOT.inW M (β ++ γ)) ∧
    (∀ β β' : List A, IOT.evs M β = IOT.evs M β' → IOT.trace M β = IOT.trace M β') :=
  ⟨IOT.evsFrom_cons M, fun β γ => ⟨IOT.outW_le_append β γ, IOT.inW_le_append β γ⟩,
    fun _ _ h => IOT.evs_inj h⟩

/-- **Prop. `prop:projection`** (Projection).  "Let `M` be an automaton.
(1) `P_M` is an I/O specification, and every finite execution of `M` is a run
of `P_M` from the canonical state at the empty receive sequence, with one
input event per arrival and one output event per reply.  (2) `P_M` satisfies
Relational Monotonicity.  Its runs are consistent exactly when, at each
receive sequence, every reply sequence in its fiber is a prefix of every
longer one."

Lean: (1) every receive sequence has a row (`IOT.spec` is a `Spec`), and
`IOT.exec_run`: the events `IOT.evs M β` run from `canon (spec M) (inW M [])`
to the state at `inW M β` whose table is the canonical table `IOT.Canon M β`;
(2) `IOT.relMono` and `IOT.consistent_iff`.  The proof follows the sketch:
legality of each event comes from the execution's own row
(`IOT.inv_step`); Relational Monotonicity receives the added requests by
input-enabledness; and pairwise comparable reply sequences have the longest
as common extension (`IOT.max_of_comparable`), with Complete CALM in the form
`liftedMono_iff_relMono_directed`.  Lean states the condition as pairwise
prefix-comparability (`t ≼ t' ∨ t' ≼ t`), which is the paper's "every reply
sequence … is a prefix of every longer one". -/
theorem «prop:projection» {A : Type} (M : IOA.Automaton A) :
    ((∀ w, ∃ t, (IOT.spec M).P w t) ∧
      ∀ β s, IOA.Execution M β s → ∃ σ,
        Exec (canon (IOT.spec M) (IOT.inW M [])) (IOT.evs M β) σ ∧ σ.cur = IOT.inW M β ∧
          ∀ k u, σ.R k u ↔ IOT.Canon M β k u) ∧
    (IOT.spec M).RelMono ∧
    ((IOT.spec M).Consistent ↔
      ∀ w t t', (IOT.spec M).P w t → (IOT.spec M).P w t' → t ≼ t' ∨ t' ≼ t) :=
  ⟨⟨(IOT.spec M).total, fun _ _ h => IOT.exec_run h⟩, IOT.relMono, IOT.consistent_iff⟩

/-- "Since `P_M` is an I/O specification, the results of Section
`sec:distributed-execution` apply to it as to any other spec."

Lean: the results of Section `sec:distributed-execution` are stated for every
spec.  For instance, the projected spec has distributed consistency, for any
message type `D`, exactly when it satisfies Lifted Monotonicity
(Prop. `prop:distributed-consistency` with Complete CALM), and some system for
it has Availability and Partition Consistency exactly when it satisfies
Lifted Monotonicity (Theorem `thm:complete-cap`). -/
theorem «sec:operational-models/distributing» {A : Type} (M : IOA.Automaton A) (D : Type) :
    (Dist.DistConsistent (IOT.spec M) D ↔ (IOT.spec M).LiftedMono) ∧
    ((∃ Sys : CAP.System (IOT.spec M) D, CAP.Availability Sys ∧ CAP.PartitionConsistency Sys) ↔
      (IOT.spec M).LiftedMono) :=
  ⟨(Dist.consistent_iff_distConsistent _ D).symm.trans (complete_calm _), CAP.complete_cap _ D⟩

/-- "The converse of item (1) fails.  Consider a registrar that receives
ballots `p`.  After the first ballot it may reply `x` at once and ignore later
ballots, which closes the polls.  Or it may wait for a second ballot, reply
`x`, and later reply `z`.  Its projected spec has a run that receives `p`,
replies `x`, receives a second `p`, and replies `z`: each row the run passes
through occurs in some execution.  No execution has that trace, because a
registrar that replied early never replies `z`.  Every reply sequence of the
registrar is empty, `x`, or `xz`, so the runs of its projected spec are
consistent."

Lean: the registrar is `IOT.Poll.M` (`s1 → cl` replies early; `cl` ignores
later ballots).  `IOT.Poll.spec_run`: the events of `p, x, p, z` form a run of
the projected spec; `IOT.Poll.no_execution`: no execution has those events
(they determine the trace, and the registrar has no internal actions);
`IOT.Poll.replies_cases` and `IOT.Poll.consistent`. -/
theorem «sec:operational-models/registrar» :
    (∃ σ, Exec (canon (IOT.spec IOT.Poll.M) (IOT.inW IOT.Poll.M []))
      (IOT.evs IOT.Poll.M [.p, .x, .p, .z]) σ) ∧
    (∀ β s, IOA.Execution IOT.Poll.M β s →
      IOT.evs IOT.Poll.M β ≠ IOT.evs IOT.Poll.M [.p, .x, .p, .z]) ∧
    (∀ β s, IOA.Execution IOT.Poll.M β s →
      IOT.replies IOT.Poll.M β = [] ∨ IOT.replies IOT.Poll.M β = [.x] ∨
        IOT.replies IOT.Poll.M β = [.x, .z]) ∧
    (IOT.spec IOT.Poll.M).Consistent :=
  ⟨IOT.Poll.spec_run, fun _ _ h => IOT.Poll.no_execution h, fun _ _ h => IOT.Poll.replies_cases h,
    IOT.Poll.consistent⟩

/-- "The automaton as a system": "To recover what the projection drops, we
map the automaton into our system model with a single participant.  The rows
of `P_M` that a finite execution can still reach, by continuing from its final
state, are its *reachable rows*.  Removing every other row from a table that
contains them is a commitment whenever it removes a row.  Suppose the
execution can reach `(k,w)`, and `u` is a prefix of `w` that extends the
execution's reply sequence.  The execution can stop replying once it has
replied `u` and then receive the rest of `k`, so it also reaches `(k,u)`.  No
removed row is therefore extended by a kept row at the same input."

Lean: the reachable rows are `IOT.Live M β s`; `IOT.live_closed` is the
argument; `IOT.narrow M X` keeps the rows in `X`, and it applies (is a
commitment at the state) when it removes a row, keeps a row at the current
input, and removes no row below a kept row (`IOT.NarrowOK`).  At a produced
history matched by the execution (Def. `def:automaton-system`), every row of
the table extends the execution's reply sequence, and `IOT.narrowOK_of_matches`
gives the commitment. -/
theorem «sec:operational-models/reachable-rows» {A : Type} (M : IOA.Automaton A) :
    (∀ (β : List A) (s : M.St) (k : IOT.InS M) (u w : IOT.OutS M),
      IOT.Live M β s k w → IOT.outW M β ≼ u → u ≼ w → IOT.Live M β s k u) ∧
    (∀ l σ β s, SysExec (IOT.basis M) (canon (IOT.spec M) (IOT.inW M [])) l σ →
      IOT.Matches l σ β s → (∃ k u, σ.R k u ∧ ¬ IOT.Live M β s k u) →
        (IOT.narrow M (IOT.Live M β s)).app σ ≠ none) := by
  refine ⟨fun _ _ _ _ _ hw hlo huw => IOT.live_closed hw hlo huw, fun l σ β s hp hm hs => ?_⟩
  rw [IOT.narrow_app_of (IOT.narrowOK_of_matches hp hm hs)]
  simp

/-- **Def. `def:automaton-system`** (System of an automaton).  "An execution
of `M` *matches* a local history `λ` when the input and output events of `λ`
carry the execution's arrivals and replies in order, and the table after `λ`
keeps all of the execution's reachable rows.  An input event may carry
several consecutive arrivals, or none.  The *system of* `M` has one
participant and runs over `P_M`.  Its basis contains the canonical
commitments and, for each finite execution, the commitment that keeps only
that execution's reachable rows.  After a local history `λ`, its strategy
allows the events that some execution matching `λ` allows next: the output
event that adds a reply the execution's final state can send, and the
commitment event that keeps only the execution's reachable rows."

Lean: `IOT.sys M : Guard.Sys (IOT.spec M)` (a one-participant system: basis
and strategy; `Guard.Produces` are its histories), with basis `IOT.basis M`;
matching is `IOT.Matches` (with `IOT.Corr` for "carry the arrivals and
replies in order"). -/
noncomputable abbrev «def:automaton-system» {A : Type} (M : IOA.Automaton A) :
    Guard.Sys (IOT.spec M) :=
  IOT.sys M

/-- **Prop. `prop:automaton-system`** (System of an automaton).  "Let `M` be
an automaton.  (1) Every history of the system of `M` is matched by some
execution of `M`.  (2) Every execution of `M` is matched by a history of the
system whose input and output events are its run of `P_M` (Proposition
`prop:projection`) and whose table is exactly its reachable rows.  (3) After
any history, one commitment event brings the table down to exactly the
reachable rows of a matching execution, unless the table is already there."

Lean: (1) `IOT.sound`; (2) `IOT.complete`, whose history's input and output
events (`filterMap SEvent.erase`) are `IOT.evs M β`; (3) `IOT.catchup`.  The
proof follows the sketch, by induction on the history and on the execution
(after each step the history adds the step's event and, if the step lost
reachable rows, the commitment event of (3)).  The remark after it ("Item (3)
reflects the one difference between the two models. … an input may arrive in
between, and the commitment then applies after that input.") explains (3):
input events are always allowed, and `IOT.catchup` applies at every
history. -/
theorem «prop:automaton-system» {A : Type} (M : IOA.Automaton A) :
    (∀ l σ, Guard.Produces (IOT.sys M) (IOT.inW M []) l σ → ∃ β s, IOT.Matches l σ β s) ∧
    (∀ β s, IOA.Execution M β s → ∃ l σ, Guard.Produces (IOT.sys M) (IOT.inW M []) l σ ∧
      IOT.Matches l σ β s ∧ (∀ k u, σ.R k u ↔ IOT.Live M β s k u) ∧
      l.filterMap SEvent.erase = IOT.evs M β) ∧
    (∀ l σ β s, Guard.Produces (IOT.sys M) (IOT.inW M []) l σ → IOT.Matches l σ β s →
      (∀ k u, σ.R k u ↔ IOT.Live M β s k u) ∨
        ∃ σ', Guard.Produces (IOT.sys M) (IOT.inW M [])
          (l ++ [.commitment [IOT.narrow M (IOT.Live M β s)]]) σ' ∧
          ∀ k u, σ'.R k u ↔ IOT.Live M β s k u) :=
  ⟨IOT.sound, IOT.complete, fun _ _ _ _ hp hm => (IOT.catchup hp hm).imp id
    fun ⟨σ', h1, _, h3⟩ => ⟨σ', h1, h3⟩⟩

/-- "The commitment events record choices that traces do not show.  Consider
an automaton that, after the first request, takes an internal step to one of
two states.  Both reply `x`, but only the second can then reply `z`.  A second
automaton has only the second state.  The two automata have the same traces,
and therefore the same projected spec.  In the first, the internal step to the
first state loses reachable rows, so its system removes the rows with reply
sequence `xz` in a commitment event.  The system of the second automaton never
does."

Lean: the automata `IOT.Hid.H` and `IOT.Hid.V` (states `sA`, `sB`; later
requests are ignored).  They have the same execution schedules, hence the same
traces (`IOT.Hid.same_executions`), and the same pairs of receive and reply
sequences (`IOT.Hid.same_rows`).  `IOT.Hid.hid_narrows`: `H`'s system has a
history that has emitted `[x]` and whose table has no row with `[x, z]` at its
current input; `IOT.Hid.vis_keeps`: every history of `V`'s system that has
emitted `[x]` keeps that row. -/
theorem «sec:operational-models/hidden-choice» :
    (∀ β, (∃ s, IOA.Execution IOT.Hid.H β s) ↔ (∃ s, IOA.Execution IOT.Hid.V β s)) ∧
    (∀ w t, (∃ β s, IOA.Execution IOT.Hid.H β s ∧ IOT.recvs IOT.Hid.H β = w ∧
        IOT.replies IOT.Hid.H β = t) ↔
      (∃ β s, IOA.Execution IOT.Hid.V β s ∧ IOT.recvs IOT.Hid.V β = w ∧
        IOT.replies IOT.Hid.V β = t)) ∧
    (∃ l σ, Guard.Produces (IOT.sys IOT.Hid.H) (IOT.inW IOT.Hid.H []) l σ ∧
      l.foldl IOT.outStep (IOT.outW IOT.Hid.H []) = IOT.Hid.xH ∧ ¬ σ.R σ.cur IOT.Hid.xzH) ∧
    (∀ l σ, Guard.Produces (IOT.sys IOT.Hid.V) (IOT.inW IOT.Hid.V []) l σ →
      l.foldl IOT.outStep (IOT.outW IOT.Hid.V []) = IOT.Hid.xV → σ.R σ.cur IOT.Hid.xzV) :=
  ⟨IOT.Hid.same_executions, IOT.Hid.same_rows, IOT.Hid.hid_narrows,
    fun _ _ hp ho => IOT.Hid.vis_keeps hp ho⟩

/-- **Def. `def:confluent-automaton`** (Confluent automaton).  "An automaton
is *confluent* when, for any finitely many finite executions and any receive
sequence `j` that extends the receive sequence of each, there is a reply
sequence `u` such that each of the executions can continue to an execution
with receive sequence `j` and reply sequence `u`."

Lean: `IOT.Confluent M` (finitely many executions as a list; "can continue
to" is `IOT.Live`). -/
abbrev «def:confluent-automaton» {A : Type} (M : IOA.Automaton A) : Prop := IOT.Confluent M

/-- **Prop. `prop:automaton-confluence`** (Confluent automata).  "Let `M` be
an automaton.  (1) Every finite family of histories of the system of `M` is
confluent at every common input extension of their current inputs, by
continuations that may apply any commitments, exactly when `M` is confluent.
(2) For an execution of `M`, the canonical run of its run of `P_M` keeps the
rows at extensions of its receive sequence whose reply sequences extend its
own.  The history of item (2) of Proposition `prop:automaton-system` keeps
those rows less the rows its commitment events removed.  `M` is confluent
exactly when, for any finitely many executions and any common input
extension `j` of their receive sequences, some row at `j` lies in the
canonical table of each and in none of the sets of removed rows.  (3) If `M`
is confluent, the runs of `P_M` are consistent.  The converse fails."

Lean: (1) `IOT.sys_consistent_iff` (`Guard.SysConsistent` of the system's
history endpoints `IOT.SysRun`), proved with the Survivor test for runs
under bases of Prop. `prop:system-confluence` (`Dist.sysConfluentAt_iff`);
(2) `IOT.tables`: the matching history and the canonical run of its input and
output events, with tables `IOT.Live` and `IOT.Canon`, and `IOT.Removed`
(canonical rows no longer reachable) is the canonical part of the set `Δ` of
Prop. `prop:system-confluence` (`Dist.Removed`, by `Dist.table_decomp`);
`IOT.confluent_iff_removed`; (3) `IOT.consistent_of_confluent` (through the
common-extension form), and the registrar `IOT.Poll.M`
(`IOT.Poll.consistent`, `IOT.Poll.not_confluent`). -/
theorem «prop:automaton-confluence» {A : Type} (M : IOA.Automaton A) :
    (Guard.SysConsistent (IOT.SysRun (M := M)) ↔ IOT.Confluent M) ∧
    (∀ β s, IOA.Execution M β s → ∃ l σ ρh,
      Guard.Produces (IOT.sys M) (IOT.inW M []) l σ ∧ IOT.Matches l σ β s ∧
      l.filterMap SEvent.erase = IOT.evs M β ∧
      Exec (canon (IOT.spec M) (IOT.inW M [])) (l.filterMap SEvent.erase) ρh ∧
      (∀ k u, σ.R k u ↔ IOT.Live M β s k u) ∧ (∀ k u, ρh.R k u ↔ IOT.Canon M β k u) ∧
      ∀ k u, IOT.Removed M β s k u ↔
        ρh.R k u ∧ Dist.Removed (IOT.basis M) (canon (IOT.spec M) (IOT.inW M [])) l k u) ∧
    (IOT.Confluent M ↔
      ∀ fam : List (List A × M.St), (∀ e ∈ fam, IOA.Execution M e.1 e.2) →
        ∀ j : IOT.InS M, (∀ e ∈ fam, IOT.inW M e.1 ≼ j) →
          ∃ u, ∀ e ∈ fam, IOT.Canon M e.1 j u ∧ ¬ IOT.Removed M e.1 e.2 j u) ∧
    (IOT.Confluent M → (IOT.spec M).Consistent) ∧
    ((IOT.spec IOT.Poll.M).Consistent ∧ ¬ IOT.Confluent IOT.Poll.M) :=
  ⟨IOT.sys_consistent_iff, fun _ _ h => IOT.tables h, IOT.confluent_iff_removed,
    IOT.consistent_of_confluent, IOT.Poll.consistent, IOT.Poll.not_confluent⟩

/-- "For the registrar, replying early loses every reachable row with reply
sequence `xz`, so its system removes them in a commitment event.  An execution
that replied early and one that waited and replied `xz` then have no common
reachable row at two ballots, and the registrar is not confluent, although the
runs of its projected spec are consistent.  Closing the polls is a commitment the projected
spec does not require: a canonical run can emit `x` after one ballot and still
emit `xz` after the second."

Lean: from the early execution `p, x` (state `cl`), every reachable row has
reply sequence `[x]` (`IOT.Poll.live_quiet`), so the row at two ballots with
`[x, z]`, which is in its canonical table, is removed (`IOT.Poll.early_removes`);
`IOT.Poll.not_confluent`, `IOT.Poll.consistent`; the canonical run is
`IOT.Poll.spec_run`. -/
theorem «sec:operational-models/registrar-commitment» :
    IOT.Removed IOT.Poll.M [.p, .x] .cl ⟨[.p, .p], by simp [IOT.Poll.M, IOT.Poll.sig]⟩
      ⟨[.x, .z], by simp [IOT.Poll.M, IOT.Poll.sig]⟩ ∧
    ¬ IOT.Confluent IOT.Poll.M ∧ (IOT.spec IOT.Poll.M).Consistent ∧
    (∃ σ, Exec (canon (IOT.spec IOT.Poll.M) (IOT.inW IOT.Poll.M []))
      (IOT.evs IOT.Poll.M [.p, .x, .p, .z]) σ) :=
  ⟨IOT.Poll.early_removes, IOT.Poll.not_confluent, IOT.Poll.consistent, IOT.Poll.spec_run⟩

/-- "A failure can also come from the projected spec itself.  Consider a
counter whose report carries the count at the moment the report fires.  After
two arrivals, one execution has reported `1`, before the second arrival, and
another has reported `2`.  Neither reply sequence is a prefix of the other, so
the projected spec does not satisfy Lifted Monotonicity.  A counter that
records the count when each request arrives, and later reports from that
record, sends the reports `1,2,…,m` in order.  Its projected spec satisfies
Lifted Monotonicity, and the counter itself is confluent."

Lean: `IOT.Ctr.Race` (state: the count; a report `rep n` at count `n`) and
`IOT.Ctr.Queue` (state `(n, m)`: arrivals and reports; it reports `m + 1`
when `m < n`).  `IOT.Ctr.race_inconsistent`; `IOT.Ctr.queue_exec` (the reply
sequence of every execution is `reps m`, the reports `1, …, m`);
`IOT.Ctr.queue_consistent`; `IOT.Ctr.queue_confluent`; Lifted Monotonicity
from consistency by Complete CALM. -/
theorem «sec:operational-models/counters» :
    ¬ (IOT.spec IOT.Ctr.Race).LiftedMono ∧
    (∀ β s, IOA.Execution IOT.Ctr.Queue β s → IOT.replies IOT.Ctr.Queue β = IOT.Ctr.reps s.2) ∧
    (IOT.spec IOT.Ctr.Queue).LiftedMono ∧ IOT.Confluent IOT.Ctr.Queue :=
  ⟨fun h => IOT.Ctr.race_inconsistent ((complete_calm _).2 h),
    fun _ _ h => (IOT.Ctr.queue_exec h).2.1, (complete_calm _).1 IOT.Ctr.queue_consistent,
    IOT.Ctr.queue_confluent⟩

/-! "Testing and proof": "The projected spec and the system of an automaton
are defined by every finite execution of the automaton.  There are infinitely
many such executions, so both are semantic objects: we can reason about them,
but not list them.  Two standard approaches make that reasoning practical."
This frames the paragraph.  "The first is testing.  A simulator or model
checker runs the automaton on bounded inputs; the pairs of receive and reply
sequences it collects form a finite spec in our model, which can be checked for
violations of Lifted Monotonicity.  This is routine engineering practice and
has found serious bugs in production systems.  Testing suits refutation."
These sentences describe tools and practice and are argued in prose only (see
the README); the refutation claim is the next entry. -/

/-- "If the projected spec does not satisfy Lifted Monotonicity, two
executions show it: they have
the same receive sequence, and neither reply sequence is a prefix of the
other.  A violation of the automaton's own confluence is shown by finitely
many executions and a receive sequence at which they have no common
reachable row, and confirming that they have none means exploring all of their
continuations to that receive sequence."

Lean: `IOT.not_consistent_iff`, with Complete CALM turning Lifted Monotonicity
into consistency of the runs; the violation of confluence is the negation of
Def. `def:confluent-automaton`, unfolded here.  That confirming it means
exploring the continuations is argued in prose only (see the README). -/
theorem «sec:operational-models/testing-witness» {A : Type} (M : IOA.Automaton A) :
    (¬ (IOT.spec M).LiftedMono ↔
      ∃ β s β' s', IOA.Execution M β s ∧ IOA.Execution M β' s' ∧ IOT.inW M β = IOT.inW M β' ∧
        ¬ (IOT.outW M β ≼ IOT.outW M β' ∨ IOT.outW M β' ≼ IOT.outW M β)) ∧
    (¬ IOT.Confluent M ↔
      ∃ fam : List (List A × M.St), (∀ e ∈ fam, IOA.Execution M e.1 e.2) ∧
        ∃ j : IOT.InS M, (∀ e ∈ fam, IOT.inW M e.1 ≼ j) ∧
          ∀ u, ∃ e ∈ fam, ¬ IOT.Live M e.1 e.2 j u) := by
  refine ⟨(not_congr (complete_calm _)).symm.trans IOT.not_consistent_iff,
    ⟨fun h => ?_, fun ⟨fam, hx, j, hj, hu⟩ hc => ?_⟩⟩
  · apply Classical.byContradiction
    intro hn
    apply h
    intro fam hx j hj
    apply Classical.byContradiction
    intro hu
    apply hn
    refine ⟨fam, hx, j, hj, fun u => Classical.byContradiction fun he => hu ⟨u, fun e hm =>
      Classical.byContradiction fun hl => he ⟨e, hm, hl⟩⟩⟩
  · obtain ⟨u, hu'⟩ := hc fam hx j hj
    obtain ⟨e, he, hne⟩ := hu u
    exact hne (hu' e he)

/-- "Testing cannot show that Lifted Monotonicity holds, since that is a claim
about every input."

Lean (`Testing.testing_cannot_show`): for every finite set `X` of explored
inputs (a chain of stages), the spec `Testing.base`, which satisfies Lifted
Monotonicity, and the spec `Testing.spoil X` have the same fiber at every input
of `X`, but `Testing.spoil X` fails Lifted Monotonicity at an input outside
`X`.  So the fibers at finitely many inputs never determine whether Lifted
Monotonicity holds. -/
theorem «sec:operational-models/testing-cannot-show» (X : List Testing.Stage) :
    (∀ s ∈ X, ∀ o, Testing.base.P s o ↔ (Testing.spoil X).P s o) ∧
      Testing.base.LiftedMono ∧ ¬ (Testing.spoil X).LiftedMono :=
  Testing.testing_cannot_show X

/-- "The second approach is proof.  Verification work routinely proves that
an automaton refines a spec: every trace of the automaton is allowed by the
spec. … Our use adds one obligation.  A *declared* spec `D` gives, for each
receive sequence, a set of reply sequences by a rule; it does not enumerate
executions.  To check Lifted Monotonicity on `D` instead of on the projected spec, two
things must be shown, and both are needed: if `D` omits a reply sequence the
automaton can produce, it may hide an incompatibility, and if `D` adds one the
automaton cannot produce, it may create an incompatibility the automaton does
not have."  The description of verification work (invariants, forward
simulations, refinement mappings, mechanized proofs) is argued in prose only
(see the README).

Lean: `IOT.Ctr.realizability_alone`: allowing no replies (`IOT.Ctr.noReplies`)
is realizable for the racing counter and consistent, while the racing
counter's projected spec is inconsistent, so omitting reply sequences hides the
incompatibility.  `IOT.Ctr.domination_alone`: allowing every reply sequence
(`IOT.Ctr.allReplies`) dominates the recording counter and is inconsistent,
while the recording counter's projected spec is consistent, so adding reply
sequences creates an incompatibility. -/
theorem «sec:operational-models/both-halves» :
    ((∀ w t, (IOT.Ctr.noReplies IOT.Ctr.Race).P w t → (IOT.spec IOT.Ctr.Race).P w t) ∧
      (IOT.Ctr.noReplies IOT.Ctr.Race).Consistent ∧ ¬ (IOT.spec IOT.Ctr.Race).Consistent) ∧
    ((∀ w t, (IOT.spec IOT.Ctr.Queue).P w t →
        ∃ u, (IOT.Ctr.allReplies IOT.Ctr.Queue).P w u ∧ t ≼ u) ∧
      ¬ (IOT.Ctr.allReplies IOT.Ctr.Queue).Consistent ∧ (IOT.spec IOT.Ctr.Queue).Consistent) :=
  ⟨IOT.Ctr.realizability_alone, IOT.Ctr.domination_alone⟩

/-- "Domination is the counterpart, for receive and reply sequences, of the
refinement obligation above.  Realizability is its converse, that `D` allows
nothing the automaton cannot produce; it too is proved once for all inputs,
typically by induction on the input.  `D` need not match the automaton
exactly: it may leave out reply sequences that others extend.  For the
recording counter, the rule "after `n` arrivals, the reports `1,…,n`"
satisfies both obligations."

Lean: `IOT.Ctr.queue_declared`: the rule `IOT.Ctr.allReported` (it leaves out
every shorter reply sequence) satisfies Realizability and Domination
(`CofinalAlong id`) and is consistent.  How realizability is typically
proved, and the relation to the refinement obligation, are argued in prose
only (see the README). -/
theorem «sec:operational-models/recording-rule» :
    CofinalAlong id IOT.Ctr.allReported (IOT.spec IOT.Ctr.Queue) ∧
      IOT.Ctr.allReported.Consistent :=
  IOT.Ctr.queue_declared

/-- **Prop. `prop:declared-specification`** (Declared specifications).  "Let
`D` be an I/O specification whose outputs are reply sequences and whose inputs
correspond, by an order isomorphism, to receive sequences.  If `D` satisfies
realizability and domination, then `D` satisfies Lifted Monotonicity exactly
when the projected spec does."  With the obligations: "*Realizability.*  Every reply
sequence that `D` allows at a receive sequence is the reply sequence of some
execution with that receive sequence.  *Domination.*  Every execution's reply
sequence is a prefix of one that `D` allows at its receive sequence."

Lean: `D : Spec J (OutS M)` and `φ : InS M → J`; `CofinalAlong φ D (spec M)`
bundles that `φ` is an order embedding (`emb`), Realizability (`real`: every
row `(j, t)` of `D` is `(φ w, t)` for a row `(w, t)` of the projected spec,
i.e. of an execution), and Domination (`dom`).  The paper's order isomorphism
is an order embedding that is onto; ontoness is not assumed, since
Realizability and totality of `D` imply it.  `IOT.declared`, through
`liftedMono_iff_of_cofinalAlong`, whose proof follows the sketch through the
common-extension form.  The closing paragraph ("Together, the two obligations
let `D` stand in for the projected spec: Lifted Monotonicity is checked on `D`
exactly as everywhere else in this paper.  Whether the automaton itself is confluent
is a question about its executions (Proposition
`prop:automaton-confluence`).") relates the statement to the rest of the
subsection. -/
theorem «prop:declared-specification» {A J : Type} [PO J] (M : IOA.Automaton A)
    (φ : IOT.InS M → J) (D : Spec J (IOT.OutS M)) (H : CofinalAlong φ D (IOT.spec M)) :
    D.LiftedMono ↔ (IOT.spec M).LiftedMono :=
  (complete_calm D).symm.trans ((IOT.declared φ D H).trans (complete_calm _))

end Paper
end CC
