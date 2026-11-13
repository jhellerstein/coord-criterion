import CoordCriterion.Instances.Examples
import CoordCriterion.Instances.BailisDefinition
import CoordCriterion.Instances.QueryRefinements
import CoordCriterion.Instances.BKTransducers
import CoordCriterion.CALM.Lemmas
import CoordCriterion.Instances.StateMachine
import CoordCriterion.Instances.IOMachine
import CoordCriterion.Instances.IOMachineCofinal
import CoordCriterion.Instances.HATSpec
import CoordCriterion.Instances.HATInter

/-!
# Paper §6, "Instances Across the Literature" (`sections/instances.tex`)

Statement layer for Section `sec:instances`.  Read it side by side with
`sections/instances.tex`: the `/-! ## … -/` headers follow the paper's
subsections, entries appear in paper order, and each entry quotes the claim
it formalizes.

* Numbered results and displayed equations are named by their LaTeX label
  (`«prop:iconfluence-lm»`, …).
* Unlabeled claims are named `«<enclosing label>/<slug>»`, e.g.
  `«sec:iconfluence-instance/iconfluence-is-consistency»`.
* Every proof is a pointer to the library (`Instances/Examples.lean`,
  `Instances/QueryRefinements.lean`, `Instances/InvariantConfluence.lean`,
  `Instances/BailisDefinition.lean`, `Instances/StateMachine.lean`,
  `Instances/IOMachine.lean`, `Instances/IOMachineCofinal.lean`).

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
relational languages on transducer networks: a program can be evaluated without coordination
exactly when it is monotone … Functional CALM does not replace the details of
that theorem.  It restates the result as a property of a spec, which can be
compared with specs outside Datalog.").  The abstraction is
`«eq:query-monotonicity»` (§2); the transducer theorem itself is cited, not
formalized.  The entries below check the mapping of its output extensions into our
frame (`Instances/QueryRefinements.lean`); the operational statements of
those papers (placement policies, transducers, which orders their placement
models justify) are cited, not formalized. -/

/-- Sec. `sec:query-instance`: "A query is domain-distinct-monotone when
`Q(I) ⊆ Q(I ∪ J)` for every `J` whose facts each contain a value that does
not occur in `I`.  It is domain-disjoint-monotone when this holds for every
`J` whose facts use only such values.  Each is Functional CALM under a
different input order. … When the order lets `I ∪ J` extend `I` only for such
`J`, each condition is functional monotonicity."  Lean: facts carry values
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

/-- Sec. `sec:query-instance`: "Ameloot et al. characterized the new classes
by weaker forms of monotonicity, correcting an earlier one-fact version."
Lean: the one-fact domain-distinct test is strictly weaker.  The query "the
edge relation has no 2-cycle" passes it, but adding the domain-disjoint
instance `{e(0,1), e(1,0)}` to `∅` falsifies the query, so it is neither
domain-disjoint- nor domain-distinct-monotone. -/
theorem «sec:query-instance/one-fact-version» :
    QRef.OneFactDistinctMono QRef.edgeVals QRef.noCycle2 ∧
      ¬ QRef.DisjointMono QRef.edgeVals QRef.noCycle2 ∧
      ¬ QRef.DistinctMono QRef.edgeVals QRef.noCycle2 :=
  ⟨QRef.noCycle2_oneFact, QRef.noCycle2_not_disjointMono, QRef.noCycle2_not_distinctMono⟩

/-- Sec. `sec:query-instance`: "Their model maps directly to ours.  A
behavior is an I/O specification whose outputs are ordered by inclusion.  Each
fact names the participant that holds it.  One input extends another by adding
the facts of participants not yet heard from, never by adding facts of a
participant already heard from.  A network of transducers is a system in which
every participant runs the same strategy, sees only its own facts and the
contents of the messages it receives, and broadcasts its messages. … Under
their placement, the environment gives each participant only its own facts, at
the start, so the facts in a participant's input that name other participants
arrived in messages, and a participant passes on only facts it holds.  A
transducer that computes a behavior translates into a system whose runs stay
confluent.  Every output that some fair run of the transducer can produce is
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

/-- Sec. `sec:query-instance`: "Two sides of a partition cannot know that
they are disconnected, so neither can tell whether it is the whole network,
and each must emit.  When the partition heals, the outputs of both sides must
have a common output extension at any input that extends what both sides have
received.  This is what Baccaert and Ketsman call node monotonicity: the
common-extension condition for outputs of participants that have heard from
disjoint sets of participants.  They show that a behavior is coordination-free
exactly when it contains a node monotone behavior."

Lean, first conjunct: node monotonicity (`QRef.NodeMono`, their Def. 7) is
the common-extension condition for two rows at disjoint networks and any
common input extension (`QRef.DisjointPairExpansion`).  Second conjunct (the
argument, in our model): an anonymous cluster consistent on placed histories
realizes rows (`BK.realized`, the rows it emits) that have a common output
extension at the union of disjoint networks; the two witness histories are
placed side by side, since no strategy can tell.  Third conjunct: through the
translation, a behavior characterizing a transducer is node monotone on finite
networks (their Prop. 11).  Their characterization theorem (Thm. 5 with
Lemma 4) is cited; its sufficiency half (Prop. 10) is not formalized. -/
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

/-- Sec. `sec:query-instance`: "Complete CAP asks for more, because the
environment is not constrained from back-channel sharing of facts across
sides.  It requires the common-extension condition even when participants on
different sides receive overlapping input."  Lean: the common-extension
condition (equivalently Lifted Monotonicity, the condition of Theorem
`thm:complete-cap` with `E = P`) implies node monotonicity, which asks it only
for inputs at disjoint networks. -/
theorem «sec:query-instance/asks-for-more» {F N G : Type} (loc : F → N)
    (B : Spec (QRef.ExtInp (QRef.netAdm loc)) (CALM.PSet G)) :
    B.CommonExpansion → QRef.NodeMono loc B :=
  fun h => QRef.nodeMono_of_consistent loc ((complete_calm_commonExpansion B).2 h)

/-- Sec. `sec:query-instance`: "Consider an unconstrained matching problem
over data items partitioned across participants: any set of disjoint pairs of
items is a permitted output.  Under a network partition with Baccaert and
Ketsman's placement, each side can pair its items arbitrarily.  Two sides can
always combine their pairings, because no item can be found on both sides.
This changes in our model, where the environment can provide an item to
participants on both sides of the partition.  An item `i` may then be paired
with `j` on one side and with `k` on the other, and no matching contains both
pairs."

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
coincide."  Lean: for the graph of `b`, node monotonicity is monotonicity
under network input extension, which by Functional CALM is consistency. -/
theorem «sec:query-instance/deterministic-behaviors» {F N G : Type} (loc : F → N)
    (b : QRef.ExtInp (QRef.netAdm loc) → CALM.PSet G) :
    (QRef.NodeMono loc (graph b) ↔ Monotone b) ∧ ((graph b).Consistent ↔ Monotone b) :=
  QRef.nodeMono_graph_iff loc b

/-! ## CRDTs: monotone queries over convergent state (`sec:crdt-instance`)

The opening paragraph ("A CRDT guarantees that replicas receiving the same
updates converge to equivalent states … But the Strong Eventual Consistency
property it offers provides no guarantee on what the environment may observe,
and is subject to Lamport's "anomalous behavior" (§`sec:functional-events`).
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

/-- Sec. `sec:crdt-instance`: "By Functional CALM, `q ∘ s` is consistent
exactly when `U ⊆ V` implies `q(s(U)) ≼_Y q(s(V))`." -/
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
received.") fixes the model of `Instances/HATSpec.lean`; the read rule is
`HATSpec.hatOut`.  The next paragraph ("The HAT results illustrate the
intersection reasoning of Section `sec:intersection`.  An isolation level and a
store are separate specs on the same histories: the level constrains which
read answers may appear together, and the store answers each read by its read
rule.  The store held to a level is their intersection, and we ask which
intersections satisfy Lifted Monotonicity.") is realized by `HATSpec.store`,
`HATSpec.spec`, and `Inter.inter` (`«def:store-spec»`, `«thm:hat-levels»`).  The closing sentence on session guarantees ("Session
guarantees, which Bailis et al. achieve under sticky availability, are
deployments in our terms (Proposition `thm:complete-cap-deployment`); we do
not treat them here.") is argued only in prose. -/

/-- **Definition `def:hat-spec`** (HAT specification): "An input is a history
ordered by happens-before: reads, each tagged with its replica; commits, each
with its client timestamp and write set; and deliveries of committed writes
to replicas.  The history preserves each client's program order and each
replica's arrival order, and a transaction's reads precede its commit, which
precedes its deliveries.  Inputs are ordered by
downward-closed extension.  An output is a set of read answers, ordered by
inclusion.  A history is *complete* when it answers every read and orders
versions by timestamp.  For an isolation level `L`, the table `P_L` of `𝒮_L`
contains an output at an input when the input extends to a complete history
that includes the output and exhibits none of the phenomena that `L`
proscribes.  The explicit relation `E` contains, at each input, the output
that the read rule above gives."  (CIDR version:
"An input is a history: a set of events, partially ordered by happens-before,
of three kinds.  A read is tagged with its replica; a commit carries its
timestamp and write set; a delivery brings a committed write to a replica.  One
input extends another when it adds events, none of which happens before an
event already present.  An output is a set of read answers, ordered by
inclusion.  An isolation level `L` is defined by the phenomena it proscribes.
A history is complete when …" as above.)  A complete history is `HATSpec.CH`;
`P_L` contains `F` when `F ≼ H.facts` for some complete `H` avoiding the
phenomena (`HATSpec.specP`).
Lean: inputs `HATSpec.Inp true` (events `rd`, `cm`, `dl`; legality `WF` plus
the timestamp condition of Thm. `thm:hat-levels`, so that the theorem's
hypothesis is part of the input domain; of program order only "reads precede
their commit" is required); `𝒮_L = HATSpec.spec L`; `E = HATSpec.hatA`, the
rows `(j, hatOut j)`.  A history (`HATSpec.CH`) returns, for each read, the
initial version or one installed by another committed transaction; levels
are item-only (`HATSpec.Level`: RU, RC, SI, RR, SER). -/
abbrev «def:hat-spec» (L : HATSpec.Level) : Spec (HATSpec.Inp true) (IConf.St HATSpec.Fact) :=
  HATSpec.spec L

/-- Def. `def:hat-spec`: "Inputs are ordered by downward-closed extension."
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
gives."  And after it: "The store promises its read rule and nothing about
isolation.  It satisfies Lifted Monotonicity on its own: a read's answer under
the read rule depends only on the history preceding it, so later input never
changes it, and the rule is a monotone function of the input.  Its full answers
are the rows of `E`, and the intersection `𝒮_st ∩ 𝒮_L` (Definition
`def:intersection`) is the store held to isolation level `L`.  It is total,
since both permit the empty set of answers.  By Proposition
`prop:intersection-bound`, the intersection keeps Lifted Monotonicity when
`𝒮_L` permits the read rule's answers."  Lean: `HATSpec.store`; its fiber at `j`
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

/-- Proof sketch of Thm. `thm:hat-levels`: "For read uncommitted and read
committed, the timestamp condition rules out the dependency cycles of G0 and
G1c, so `𝒮_L` permits the read rule's answers.  Proposition
`prop:intersection-bound`, with the read rule as the bound, gives Lifted
Monotonicity of `𝒮_st ∩ 𝒮_L`, whose rows include those of `E`."  (The bound
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

/-- Proof sketch of Thm. `thm:hat-levels`: "For the converse, let two
transactions at different replicas each read `x₀` and write `x`.  Each
replica's answer is forced, and their union contains a cycle on `x` with an
anti-dependency, which is Lost Update.  So the store's forced answer at one
replica has no extension in `𝒮_st ∩ 𝒮_L` once both transactions are in the
input.  The store needs no commitment on its own, so this need comes from the
intersection with `𝒮_L`."  (The store's own Lifted Monotonicity is
`HATSpec.store_liftedMono`; the last step is `HATSpec.store_inter_lostUpdate`: the row of `T₂`'s
answer `x₀` at `i₂` has no extension at the union; `HATSpec.i2_ans`.)  Lean: `T₁` (timestamp `(1,1)`) and
`T₂` (`(1,2)`) read and write `x` at replicas 0 and 1, with no delivery; at
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

/-- "The timestamp condition is required, correcting an error in the pseudocode of
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

/-- **Proposition `prop:iconfluence-lm`** (Invariant confluence and Lifted
Monotonicity): "`T` is invariant confluent if and only if `𝒮_𝓘` satisfies
Lifted Monotonicity." -/
theorem «prop:iconfluence-lm» {V Tx : Type} (M : IConf.Model V Tx) :
    M.IConfluent ↔ (IConf.SI M).LiftedMono :=
  IConf.ic_iff_liftedMono M

/-- Invariant confluence is consistency of `𝒮_𝓘`: Prop. `prop:iconfluence-lm`
read through "applying either CALM theorem" (§6 opening: "Each setting
declares an input, an output, and their orders before applying either CALM
theorem.").  The sentence that stated this directly was removed from §6.4;
Lean: by Complete CALM, Lifted Monotonicity of `𝒮_𝓘` is its consistency. -/
theorem «sec:iconfluence-instance/iconfluence-is-consistency» {V Tx : Type} (M : IConf.Model V Tx) :
    M.IConfluent ↔ (IConf.SI M).Consistent :=
  (IConf.ic_iff_liftedMono M).trans (complete_calm _).symm

/-- The uniqueness example: "The uniqueness constraint of Bailis et al.'s
payroll example shows the failure directly.  Two replicas each create an
employee and assign ID 7, each running on a state in which ID 7 is unused.
The history in which neither creation ran on a state that included the
other's writes is locally valid and extends both
one-creation histories, but its state has two employees with ID 7, so no
state it permits extends both."  Lean (library names from an earlier
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

/-- "Concurrency, not the transactions alone, decides the outcome: a
transaction that is harmless after another can, when it runs on a state
without the other's writes, produce a state whose merge with the other's is invalid."  Lean:
`alloc 2` after `alloc 1` is valid, `alloc 2` alone is valid, but the merge of
`alloc 1` and `alloc 2` run concurrently from `s₀` is invalid. -/
theorem «sec:iconfluence-instance/concurrency-decides» :
    Inst.uModel.Inv (Inst.uModel.app 2 (Inst.uModel.app 1 Inst.uModel.s0)) ∧
      Inst.uModel.Inv (Inst.uModel.app 2 Inst.uModel.s0) ∧
      ¬ Inst.uModel.Inv ((Inst.uModel.app 1 Inst.uModel.s0).union (Inst.uModel.app 2 Inst.uModel.s0)) :=
  Inst.uniqueness_concurrency

/-! ## General operational specification models (`sec:operational-models`)

The opening paragraph ("An I/O spec declaratively relates
cumulative inputs to permitted outputs.  An I/O automaton instead defines
operational states, input, output, and internal actions, and a transition
relation.  Projecting its externally visible behavior can yield an I/O
spec. … Thus our specification model does not replace an operational
formalism; it is a semantic projection designed to make the intrinsic
coordination question comparable across such formalisms.") positions the model;
it states no claim of its own.

"Compiling a state machine": "Automata are a traditional way to model
operational behavior abstractly.  Our model keeps only the inputs and outputs
of that behavior and drops the operational details.  The mapping is
straightforward: for each input, record the outputs of the runs that consume it.
Work that models systems as state machines therefore maps naturally into our
model, where Complete CALM assesses its consistency directly.  We now make the
mapping precise, and then explain how it is used in practice."  The mapping is
Def. `def:induced-specification`, and "Complete CALM assesses its consistency
directly" is `IOM.confluent_iff_liftedMono` (consistency iff Lifted
Monotonicity for every induced specification; part (4) of
Prop. `prop:induced-specification`).  How it is used in practice is the
paragraph "Testing and proof" (entries after
Prop. `prop:induced-specification`).

We take the standard I/O-automaton model of a state machine, its clients,
and the channel that carries their state-machine events.  The machine `M` has states `Q`,
an initial state `q₀`, receive transitions for
state-machine events that accept
every payload in every state, output transitions that emit an output to a
client and may change state, internal transitions, and an observation
`obs : Q → O`.  There are finitely many clients.  Each may send a
state-machine event with any payload at any time, and receives the machine's
outputs.  A channel carries each state-machine event at most once to the
machine's input queue, possibly reordering events on the way, and the machine
consumes the queue in order.  In an execution of the composed
automaton, *happens-before* is Lamport's order: the transitive closure of the
local order at the machine and at each client and of the edge from sending a state-machine event to receiving it."

Lean: Lynch–Tuttle I/O automata and their composition are `CC.IOA`
(`Foundations/IOAutomata.lean`).  The machine is a general machine automaton
`G : IOM.Machine C P Q O` (payloads `P`; fields `q0`; receive transitions
`recv` with `recv_enabled`; output transitions `out q c o q'`, emitting `o` to
client `c` and moving to `q'`; internal transitions `tau`; `obs`), as the
I/O automaton `IOM.machA G` (inputs `recv e`, outputs `out c o`, internal
action `tau`).  A state machine `M : SM.Machine Q P O` is the special case
`IOM.ofSM M`.  `IOM.sys k G` composes `IOM.machA G`, the clients `IOM.cliA c`
(outputs `send e` with any payload at any time, inputs `out c o`), and the
channel `IOM.chanA k`, which neither loses nor duplicates.  The machine's
input queue is folded into the channel: the machine's `recv e` is the
channel's delivery of `e`, i.e. the machine consuming `e` from its queue.  A
channel that may reorder is the bag, `k = .bag` (any state-machine event in transit is
consumed next); the case in which state-machine events arrive in the order sent (part (2)
of Prop. `prop:induced-specification`) is the FIFO queue, `k = .fifo`.
Events `IOM.Ev C P` carry a client, a sequence number, and a payload.
`IOM.HB β` is happens-before on positions of the schedule `β`.  The client
type `C` is arbitrary; finiteness is not needed.  A sent state-machine event may stay in
transit in a finite execution. -/

/-- "An output of the machine is an input of the client that receives it, so
a client's later sends happen after everything the machine had received when
it emitted that output."  From the remark after
Proposition `prop:induced-specification`: "A client that sends after
observing an output is ordered after everything that output reflected, and the
input records that dependence."

Lean (general machine `G`): in an execution `β`, if the machine received `e`
(position `r`) before emitting `out c o` (position `m`), and client `c` sends
`e'` at a later position `j`, then the send of `e` happens before the send of
`e'`, every delivery of `e'` in `β` comes after position `r`, and if `e'` is
received the input of `β` orders `e` before `e'`.  The delivery claim is read
within the execution in which the client observed the output.  The rest of
the remark ("what the client saw is recorded by the run's output events,
which keep only rows that refine it") applies Def. `def:output-event` to the
induced specification. -/
theorem «sec:operational-models/later-sends» {C P Q O : Type} [DecidableEq C]
    (k : IOM.ChanKind) (G : IOM.Machine C P Q O) {β : List (IOM.Act C P O)}
    {s : (IOM.sys (C := C) k G).St} (hx : IOA.Execution (IOM.sys k G) β s)
    {m r j : Nat} {c : C} {o : O} {e e' : IOM.Ev C P}
    (hm : β[m]? = some (.out c o)) (hrv : β[r]? = some (.recv e)) (hrm : r < m)
    (hj : IOM.SendAt β j e') (hmj : m < j) (hc : e'.client = c) :
    (∃ i, IOM.SendAt β i e ∧ IOM.HB β i j) ∧ (∀ t, β[t]? = some (.recv e') → r < t) ∧
      (.recv e' ∈ β → (IOM.input β).lt e e') :=
  IOM.send_after_out ⟨s, hx, rfl⟩ hm hrv hrm hj hmj hc

/-- **Def. `def:induced-specification`** (Induced specification).  "The
specification *induced* by `M` and its environment pairs each input
(Definition `def:execution-input`) that occurs with the machine's observation
at the end of every execution with that input."

Lean: the table `IOM.spec k G` on `IOM.OccInp C P k G`; for a general
machine `G`, this theorem gives the unfolded conditions for input
membership, order, and fiber membership together.

The remarks that follow ("This is not a
distributed execution in the sense of Section `sec:distributed-execution`.
… Happens-before here only records which state-machine events each
client sent after which outputs, so the input remembers what the
environment's choices depended on.") explain the model and state no claim of
their own.  The sentence "Distributing the machine is then direct: … among
participants Section `sec:distributed-execution` applies, using the induced
spec." is argued in prose only (see the
README). -/
theorem «def:induced-specification» {C P Q O : Type} [PO O] (k : IOM.ChanKind)
    (G : IOM.Machine C P Q O) :
    (∀ (β : List (IOM.Act C P O)) e, (IOM.input β).mem e ↔ .recv e ∈ β) ∧
    (∀ (β : List (IOM.Act C P O)) a b, (IOM.input β).lt a b ↔
      (.recv a ∈ β ∧ .recv b ∈ β) ∧ ∃ i j, IOM.SendAt β i a ∧ IOM.SendAt β j b ∧ IOM.HB β i j) ∧
    (∀ h h' : IOM.Inp C P, h ≼ h' ↔
      (∀ e, h.mem e → h'.mem e) ∧ ∀ a b, h.mem a → h.mem b → (h.lt a b ↔ h'.lt a b)) ∧
    (∀ (h : IOM.OccInp C P k G) o, (IOM.spec k G).P h o ↔
      ∃ β s, IOA.Execution (IOM.sys k G) β s ∧ IOM.input β = h.val ∧ G.obs (s .mach) = o) :=
  ⟨fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-- **Def. `def:execution-input`** (Input of an execution).  "The *input* of
a finite execution is the set of state-machine events the machine has
received, ordered by happens-before between their sends; `h ⊑ h'` when
`h ⊆ h'` and the two orders agree on `h`."

Lean: `IOM.input β` (membership: `recv e ∈ β`; order: happens-before between
the positions sending the two events), the order `IOM.Inp.instPO`. -/
abbrev «def:execution-input» {C P O : Type} (β : List (IOM.Act C P O)) : IOM.Inp C P :=
  IOM.input β

/-- **Prop. `prop:induced-specification`** (Induced specifications).
"(1) The induced specification is an I/O specification, and the input of
an execution only extends as the execution continues.  (2) When there is one
client and its state-machine events arrive in the order it sent them, every input is a
chain, inputs correspond to state-machine event sequences ordered by prefix, and the fiber
at a sequence collects the observations of the machine's runs that receive it
in order, interleaved with output and internal steps.  If output and internal
steps leave the state unchanged and receiving is deterministic, the
specification is functional and consistent exactly when `obs(q) ⪯ obs(q')`
for every receive transition `q → q'` from a reachable state.  (3) Every
observation in the fiber at `h` is reached by a run of the machine that
receives each state-machine event of `h` once, interleaved with output and internal steps.
If the channel may reorder and clients observe no outputs, every such run is
reached, whatever the order of its receives.  (4) The machine's observations
are confluent across its executions exactly when the induced specification
satisfies Lifted Monotonicity.  Here confluence means that for executions with
inputs `h₁,…,hₖ` and any input `h` that occurs and extends each `hᵣ`, some
execution with input `h` ends in an observation that extends each of
theirs."

Lean, part by part, for a general machine `G`; a run of the machine is an
execution `γ` of the machine automaton `IOM.machA G` (its receives
`IOM.recvs γ`, interleaved with `out` and `tau` steps):
(1) every input that occurs has a row (`IOM.spec` is a `Spec`), and
`IOM.input_mono`;
(2) one client is `C = Unit`, and arrival in the order sent is the channel
`.fifo`; `IOM.fifo_single_run`: every input is a chain, `IOM.word` (payloads
in sequence order) is an order isomorphism onto `SM.Seq P` under the prefix
order, and it carries each fiber to the fiber of `IOM.runSpec G` (the
observations at the end of runs of the machine whose receives carry the
sequence in order).  The special case: `IOM.Stationary G` (output and
internal steps leave the state unchanged) and `SM.Deterministic (IOM.recvSM G)`
(receiving is deterministic); `IOM.fifo_single_stationary` gives
functionality and consistency iff `SM.TransMono (IOM.recvSM G)` (observations
grow along every receive transition from a state reachable by receives,
which for a stationary machine are all its reachable states).  It goes
through `IOM.runSpec_stationary` (the prefix table `SM.induced`) and
`SM.induced_prefix` (monotonicity along transitions and Functional CALM).
State machines are stationary (`IOM.stationary_ofSM`, and `IOM.fifo_single`
for `IOM.ofSM M`);
(3) `IOM.fiber_sub_run` (any channel; with a FIFO channel the receive order is
moreover a linear extension of the input order) and `IOM.bag_fiber_of_run`:
for the input of an execution over a bag with no `out` actions
(`IOM.OutFree`, clients observe no outputs), the observation at the end of
every run of the machine that receives each of its state-machine events once, in any
order, is in the fiber (`IOM.bag_arrival_run` gives the execution);
(4) `IOM.ObsConfluent k G` is the confluence condition on observations at the
end of executions, and `IOM.confluent_iff_liftedMono`.  The proof follows the
paper's sketch; (4) unfolds the fiber in the common-extension condition
(`IOM.obsConfluent_iff_commonExpansion`) and applies
`liftedMono_iff_commonExpansion`.  The library also proves the version for
emitted outputs (`IOM.emitConfluent_iff_liftedMono_of`). -/
theorem «prop:induced-specification» {C P Q O : Type} [PO O] [DecidableEq C]
    (k : IOM.ChanKind) (G : IOM.Machine C P Q O) (G₁ : IOM.Machine Unit P Q O) :
    -- (1)
    ((∀ h : IOM.OccInp C P k G, ∃ o, (IOM.spec k G).P h o) ∧
      ∀ (β γ : List (IOM.Act C P O)) (s : (IOM.sys (C := C) k G).St),
        IOA.Execution (IOM.sys k G) (β ++ γ) s → IOM.input β ≼ IOM.input (β ++ γ)) ∧
    -- (2)
    ((∀ h : IOM.OccInp Unit P .fifo G₁, ∀ a b, h.val.mem a → h.val.mem b → a ≠ b →
        h.val.lt a b ∨ h.val.lt b a) ∧
      (∀ h h' : IOM.OccInp Unit P .fifo G₁, h ≼ h' ↔ IOM.word h ≼ IOM.word h') ∧
      (∀ w : SM.Seq P, ∃ h : IOM.OccInp Unit P .fifo G₁, IOM.word h = w) ∧
      (∀ h o, (IOM.spec .fifo G₁).P h o ↔ (IOM.runSpec G₁).P (IOM.word h) o) ∧
      (IOM.Stationary G₁ → SM.Deterministic (IOM.recvSM G₁) →
        (IOM.spec (C := Unit) .fifo G₁).Functional ∧
          ((IOM.spec (C := Unit) .fifo G₁).Consistent ↔ SM.TransMono (IOM.recvSM G₁)))) ∧
    -- (3)
    ((∀ (h : IOM.OccInp C P k G) o, (IOM.spec k G).P h o →
        ∃ γ : List (IOM.Act C P O), ∃ q, IOA.Execution (IOM.machA G) γ q ∧ G.obs q = o ∧
          (IOM.recvs γ).Nodup ∧ (∀ e, e ∈ IOM.recvs γ ↔ h.val.mem e) ∧
          (k = .fifo → (IOM.recvs γ).Pairwise fun a b => ¬ h.val.lt b a)) ∧
      ∀ (β : List (IOM.Act C P O)) (s : (IOM.sys (C := C) .bag G).St),
        IOA.Execution (IOM.sys .bag G) β s → IOM.OutFree β →
        ∀ h : IOM.OccInp C P .bag G, h.val = IOM.input β →
        ∀ (γ : List (IOM.Act C P O)) q, IOA.Execution (IOM.machA G) γ q →
        (IOM.recvs γ).Nodup → (∀ e, e ∈ IOM.recvs γ ↔ h.val.mem e) →
        (IOM.spec .bag G).P h (G.obs q)) ∧
    -- (4)
    (IOM.ObsConfluent (C := C) k G ↔ (IOM.spec (C := C) k G).LiftedMono) :=
  have h2 := IOM.fifo_single_run G₁
  ⟨⟨(IOM.spec k G).total, fun _ _ s hx => IOM.input_mono ⟨s, hx, rfl⟩⟩,
    ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, IOM.fifo_single_stationary⟩,
    ⟨IOM.fiber_sub_run, fun _ _ hx hout h hh _ _ hγ hw hmem =>
      IOM.bag_fiber_of_run hx hout h hh hγ hw hmem⟩,
    (IOM.confluent_iff_liftedMono k G).1⟩

/-! "Testing and proof": "The induced spec is defined by every
finite execution of the machine and its environment.  There are infinitely
many such executions, so the induced spec is a semantic object: we
can reason about it, but not list it.  Two standard approaches make that
reasoning practical."  This frames the paragraph.  "The first is testing.  A
simulator or model checker runs the machine and its environment on bounded
inputs; the input/output pairs it collects form a finite spec in our
model, which can be checked for violations of Lifted Monotonicity.  This is
routine engineering practice and has found serious bugs in production
systems.  Testing suits refutation."
These sentences describe tools and practice and are argued in prose only (see
the README); the refutation claim is the next entry. -/

/-- "If Lifted Monotonicity fails, finitely many executions show it:
executions with inputs `h₁,…,hₖ`, and a common input extension `h` at which no
execution's observation extends all of theirs."

Lean (general machine `G`, either channel): `IOM.not_liftedMono_iff_witness`.
Lifted Monotonicity of the induced specification fails iff there are a
finite list of executions `βᵣ` and an execution `β` whose input extends each
`input βᵣ`, such that every execution `β'` with `input β' = input β` ends in
an observation that fails to extend some `βᵣ`'s.  The common input extension `h`
is the input of `β`; it is an input that occurs, as every input of the
induced specification is.  The library also gives finite certificates for
the last clause (`IOM.not_liftedMono_of_fiber_list`,
`IOM.not_liftedMono_of_machine_cert`); the first of these is the paper's next
sentence, "A violation found in the finite spec is such a witness
when the exploration covers every execution with input `h`, so that its fiber
there is complete": a finite list containing every observation at `h`, each
failing to refine some `βᵣ`'s, refutes Lifted Monotonicity.  The next sentence ("Testing cannot
show that Lifted Monotonicity holds, since that is a claim about every
input.") is argued in prose only (see the README). -/
theorem «sec:operational-models/testing-witness» {C P Q O : Type} [PO O]
    (k : IOM.ChanKind) (G : IOM.Machine C P Q O) :
    ¬ (IOM.spec (C := C) k G).LiftedMono ↔
      ∃ fam : List (List (IOM.Act C P O) × (IOM.sys (C := C) k G).St),
        (∀ r ∈ fam, IOA.Execution (IOM.sys k G) r.1 r.2) ∧
        ∃ β s, IOA.Execution (IOM.sys k G) β s ∧ (∀ r ∈ fam, IOM.input r.1 ≼ IOM.input β) ∧
          ∀ β' s', IOA.Execution (IOM.sys k G) β' s' → IOM.input β' = IOM.input β →
            ∃ r ∈ fam, ¬ G.obs (r.2 .mach) ≼ G.obs (s' .mach) :=
  IOM.not_liftedMono_iff_witness k G

/-- "The second is proof.  Instead of computing the induced spec,
a designer writes one down.  A *declared* spec `D` gives, for
each input, a set of outputs by a rule … it does not enumerate executions.
The proof then shows that `D` describes the machine well enough that Lifted
Monotonicity can be checked on `D` instead.  Two things must be shown, and
both are needed, because neither half alone preserves Lifted Monotonicity:
if `D` omits an output the machine can produce, it may hide an
incompatibility, and if `D` adds an output the machine cannot produce, it may
supply a common output extension that no execution reaches."  The examples of rules
("the set of ballots received", "the largest timestamp seen") are
illustrations, argued in prose only (see the README).

Lean: the machine `IOM.fork` (receives keep the state; an internal step moves
to `b`, observed as `l`, or to `c`, observed as `r`, from any state; `l` and
`r` are incomparable, below `top`) is not Lifted Monotone.  `IOM.forkOmit`
(only `l` at every input) omits the output `r` the machine produces: it
satisfies Realizability and is Lifted Monotone.  `IOM.forkAdd` (only `top`)
adds an output no execution reaches: it satisfies Domination and is Lifted
Monotone.  So neither obligation alone carries Lifted Monotonicity from `D`
to the machine (`IOM.fork_halves`). -/
theorem «sec:operational-models/both-halves» {C P : Type} [DecidableEq C]
    (k : IOM.ChanKind) :
    letI := IOM.lvlPO
    (∀ h o, (IOM.forkOmit C P k).P h o →
      ∃ β s, IOA.Execution (IOM.sys k (IOM.fork C P)) β s ∧ IOM.input β = h.val ∧
        (IOM.fork C P).obs (s .mach) = o) ∧
    (IOM.forkOmit C P k).LiftedMono ∧
    (∀ β s, ∀ hx : IOA.Execution (IOM.sys k (IOM.fork C P)) β s,
      ∃ o, (IOM.forkAdd C P k).P (IOM.occOfExec k (IOM.fork C P) hx) o ∧
        (IOM.fork C P).obs (s .mach) ≼ o) ∧
    (IOM.forkAdd C P k).LiftedMono ∧
    ¬ (IOM.spec (C := C) k (IOM.fork C P)).LiftedMono :=
  IOM.fork_halves k

/-- **Prop. `prop:declared-specification`** (Declared specifications).  "Let
`D` be an I/O specification whose inputs correspond, by an order
isomorphism, to the inputs that occur.  If `D` satisfies realizability and
domination, then `D` satisfies Lifted Monotonicity exactly when the induced
specification does, and so exactly when the machine's observations are
confluent across its executions."  With the obligations: "*Realizability.*
Every output that `D` allows at an input is the observation of some execution
with that input.  *Domination.*  Every execution's final observation is
extended by some output that `D` allows at its input."  The remark "`D` need
not match the machine exactly: it may leave out observations that others
refine, such as transient intermediate states" is illustrated by
`IOM.dip_liftedMono_via_cofinal` (a declared specification that omits two
transient observations).

Lean (general machine `G`, either channel): `D : Spec J O` over an ordered
input type `J`, and `φ : OccInp C P k G → J`.  `IOM.MachineCofinal k G φ D`
bundles: `φ` is an order embedding (`emb`); Realizability over executions
(`real`: every row `(j, o)` of `D` is `(φ (input β), obs)` for an execution
`β`); Domination (`dom`: every execution's final observation is extended by
a row of `D` at the image of its input).  The paper's order isomorphism is
an order embedding that is onto; ontoness is not assumed, since Realizability
and totality of `D` imply it.  The conclusion is
`IOM.liftedMono_iff_of_machineCofinal`: `D.LiftedMono ↔ (spec k G).LiftedMono`,
`D.LiftedMono ↔ ObsConfluent k G`, and also `D` consistent iff the induced
specification is.  The proof follows the sketch: both directions go through
the common-extension form (`commonExpansion_of_dominated`,
`commonExpansion_of_realized` in `CompleteCALM/Cofinal.lean`).

The closing paragraph ("Both obligations are standard in the verification
literature. … nothing about coordination is proved about the machine
itself.") relates the obligations to invariants, forward simulations,
refinement mappings, and mechanized proofs, and says how realizability is
typically proved; these are argued in prose only (see the README).  "The
proposition asks for nothing beyond these two facts" is the shape of the
statement above. -/
theorem «prop:declared-specification» {C P Q O J : Type} [PO O] [PO J]
    (k : IOM.ChanKind) (G : IOM.Machine C P Q O) (φ : IOM.OccInp C P k G → J)
    (D : Spec J O) (H : IOM.MachineCofinal k G φ D) :
    (D.LiftedMono ↔ (IOM.spec (C := C) k G).LiftedMono) ∧
      (D.LiftedMono ↔ IOM.ObsConfluent (C := C) k G) ∧
      (D.Consistent ↔ (IOM.spec (C := C) k G).Consistent) :=
  IOM.liftedMono_iff_of_machineCofinal H

end Paper
end CC
