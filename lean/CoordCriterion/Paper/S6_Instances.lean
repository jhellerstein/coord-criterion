import CoordCriterion.Instances.Examples
import CoordCriterion.Instances.BailisDefinition
import CoordCriterion.Instances.QueryRefinements
import CoordCriterion.CALM.Lemmas
import CoordCriterion.Instances.StateMachine
import CoordCriterion.Instances.IOMachine

/-!
# Paper §6, "Instances Across the Literature" (`sections/instances.tex`)

Statement layer for Section `sec:instances`.  Read it side by side with
`sections/instances.tex`: the `/-! ## … -/` headers follow the paper's
subsections, entries appear in paper order, and each entry quotes the claim
it formalizes.

* Numbered results and displayed equations are named by their LaTeX label
  (`«prop:iconfluence-lm»`, …).
* Unlabeled claims are named `«<enclosing label>/<slug>»`, e.g.
  `«sec:hat-instance/serializability-cycle»`.
* Every proof is a pointer to the library (`Instances/Examples.lean`,
  `Instances/QueryRefinements.lean`, `Instances/InvariantConfluence.lean`,
  `Instances/BailisDefinition.lean`, `Instances/StateMachine.lean`,
  `Instances/IOMachine.lean`).

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
results across literatures.  Each setting below declares an input, an output,
and their orders before applying either theorem.") frames the section; it
states no claim of its own.

## Query monotonicity (`sec:query-instance`)

The first paragraph recalls the relational-transducer CALM Theorem ("the CALM
Theorem of Ameloot et al. proves an operational result for relational
languages on transducer networks: coordination-free evaluation is possible
iff a program is monotone … Functional CALM does not replace the details of
that theorem.  It abstracts the result to a property that can be compared
with specifications outside Datalog.").  The abstraction is
`«eq:query-monotonicity»` (§2); the transducer theorem itself is cited, not
formalized.  The entries below check the mapping of its refinements into our
frame (`Instances/QueryRefinements.lean`); the operational statements of
those papers (placement policies, transducers, which orders their placement
models justify) are cited, not formalized. -/

/-- Sec. `sec:query-instance`: "A query is domain-distinct-monotone when
`Q(I) ⊆ Q(I ∪ J)` for every `J` whose facts each contain a value that does
not occur in `I`.  It is domain-disjoint-monotone when this holds for every
`J` whose facts use only such values.  Each is Functional CALM under a
different input order. … When the order lets `I ∪ J` expand `I` only for such
`J`, each condition is functional monotonicity."  Lean: facts carry values
`vals : F → V → Prop`; `ExtInp (distinctAdm vals)` and
`ExtInp (disjointAdm vals)` order instances by domain-distinct and
domain-disjoint expansion (nullary facts are never domain disjoint, as in
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

/-- Sec. `sec:query-instance`: "Under inclusion of outputs, with inputs
expanding only by facts at new nodes, a behavior is a relational
specification.  A transducer computes a behavior if every fair run ends at a
permitted output, and so implements a sub-behavior `A`. … Their
characterization, node monotonicity of `A`, is the common-expansion condition
on `A` for two rows at disjoint networks.  Complete CAP extends it to
overlapping networks"  Lean: inputs are `ExtInp (netAdm loc)` (located facts,
network expansion, so the network `Netw loc H` is read off the input) and a
behavior is any `Spec` on them.  Node monotonicity is equivalent to the
common-expansion condition for two rows at disjoint networks and any common
expansion `j` (`QRef.DisjointPairExpansion`); the full common-expansion
condition implies it.  The transducer model, its notion of computing a
behavior (Inf. Syst. 2026, Def. 4, Lemma 4), and its characterization theorem
(Def. 6, Thm. 5) are cited, not formalized. -/
theorem «sec:query-instance/node-monotonicity» {F N G : Type} (loc : F → N)
    (B : Spec (QRef.ExtInp (QRef.netAdm loc)) (CALM.PSet G)) :
    (QRef.NodeMono loc B ↔ QRef.DisjointPairExpansion loc B) ∧
      (B.CommonExpansion → QRef.NodeMono loc B) :=
  ⟨QRef.nodeMono_iff_disjointPair loc B,
    fun h => QRef.nodeMono_of_consistent loc ((complete_calm_commonExpansion B).2 h)⟩

/-- Sec. `sec:query-instance`: "A list of all nodes lets nodes wait for
everyone and choose consistently."  Lean: the list puts the membership in the
input (`QRef.AllInp`: membership `mem` and the nodes heard from, `view ⊆
mem`; an input expands another only at the same membership).  A complete
view is maximal, and a choice of one output at each maximal input is a table
on which any behavior containing it is consistent (`CAP.ConsistentOn`, the
condition of Theorem `thm:complete-cap`).  For instance, the star centred at
the least member is a spanning tree of the membership, the spanning-tree
behavior is consistent on it, and as a specification it is consistent.  That
the list and an order on nodes compute every behavior is Baccaert and
Ketsman's Thm. 2–3, cited, not formalized. -/
theorem «sec:query-instance/all-nodes» :
    (∀ {i j : QRef.AllInp}, i.Complete → i ≼ j → i = j) ∧
    (∀ {I O : Type} [PO I] [PO O] (B : Spec I O) (A : Table I O),
      (∀ i o, A i o → B.S i o) → (∀ i o j, A i o → i ≼ j → i = j) →
      (∀ i o o', A i o → A i o' → o = o') → CAP.ConsistentOn B A) ∧
    ((∀ i, QRef.treeAll.S i (QRef.star i.mem)) ∧
      CAP.ConsistentOn QRef.treeAll (fun i K => K = QRef.star i.mem) ∧
      (graph (fun i : QRef.AllInp => QRef.star i.mem)).Consistent) :=
  ⟨QRef.allInp_complete_maximal, fun B A => QRef.consistentOn_of_maximal B A, QRef.treeAll_star⟩

/-- Sec. `sec:query-instance`: "Pairing off nodes, leaving at most one
unpaired, is node monotone, yet every `A` pairs `b` with `a` at `{a,b}` and
with `c` at `{b,c}`."  Lean, with node names as input (`loc = id`, inputs
`QRef.net P`): `QRef.pairing` permits symmetric pairings in which, on a
finite network, at most one node is unpaired.  It is node monotone, every
output at a two-node network pairs its nodes, and no total sub-behavior `A`
has `pairing` consistent on it (rows at `{0,1}` and `{1,2}`, common expansion
`{0,1,2}`).  The surrounding prose (isolated nodes must emit; their
construction waits for a group to confirm itself; groups sharing a node are
nested; the group's choice is coordination but not distributed coordination)
reads Baccaert and Ketsman's Prop. 9–11 and is not formalized. -/
theorem «sec:query-instance/pairing» :
    QRef.NodeMono id QRef.pairing ∧
      (∀ a b K, a ≠ b → QRef.pairing.S (QRef.net fun x => x = a ∨ x = b) K → K.mem (a, b)) ∧
      (∀ A : Table (QRef.ExtInp (QRef.netAdm (id : Nat → Nat))) (CALM.PSet (Nat × Nat)),
        (∀ H, ∃ K, A H K) → (∀ H K, A H K → QRef.pairing.S H K) →
          ¬ CAP.ConsistentOn QRef.pairing A) :=
  ⟨QRef.pairing_nodeMono, QRef.pairing_pair, QRef.pairing_no_consistentOn⟩

/-- Sec. `sec:query-instance`: "For deterministic behaviors the two conditions
coincide."  Lean: for the graph of `b`, node monotonicity is monotonicity
under network expansion, which by Functional CALM is consistency. -/
theorem «sec:query-instance/deterministic-behaviors» {F N G : Type} (loc : F → N)
    (b : QRef.ExtInp (QRef.netAdm loc) → CALM.PSet G) :
    (QRef.NodeMono loc (graph b) ↔ Monotone b) ∧ ((graph b).Consistent ↔ Monotone b) :=
  QRef.nodeMono_graph_iff loc b

/-! ## CRDTs: monotone queries over convergent state (`sec:crdt-instance`)

The opening paragraph ("A CRDT guarantees that replicas receiving the same
updates converge to equivalent states … But the Strong Eventual Consistency
property it offers provides no guarantee on what the environment may observe,
and is subject to Lamport's "anomalous behavior" (§`sec:coordination`).
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
`s(U₁) ⊔ s(U₂) = s(U₁ ∪ U₂)` is the least state refining both." -/
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
cart before a delayed removal arrives … The two-phase query fails the test: a
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

/-- Sec. `sec:crdt-instance`: "CRDT states form a join-semilattice."  Lean: a
merge that is commutative, associative, and idempotent orders states by
`x ≼ y ⟺ merge x y = y`; this relation is a partial order and `merge a b` is
the least upper bound of `a` and `b`. -/
theorem «sec:crdt-instance/semilattice» {D : Type} (m : Inst.CAI D) :
    let le := fun x y => m.merge x y = y
    (∀ x, le x x) ∧ (∀ x y z, le x y → le y z → le x z) ∧ (∀ x y, le x y → le y x → x = y) ∧
      ∀ a b, le a (m.merge a b) ∧ le b (m.merge a b) ∧ ∀ c, le a c → le b c → le (m.merge a b) c :=
  Inst.cai_semilattice m

/-- Sec. `sec:crdt-instance`: "Observations `q` need less: Complete CALM
requires only some common refinement of query outputs
(Section `sec:lifted-monotonicity`), not a least one."  Lean: on the state
lattice `B2 × B2`, a monotone observation `qY` into a five-element order makes
`q ∘ s` consistent, yet its outputs `a = q(s({(tt,ff)}))` and
`b = q(s({(ff,tt)}))` have common refinements (`c`, and also `d`) but no
least one. -/
theorem «sec:crdt-instance/some-refinement» :
    (graph (fun U : Inst.FSet (Inst.B2 × Inst.B2) => Inst.qY (Inst.st (Inst.B2.ff, Inst.B2.ff) U))).Consistent ∧
      Inst.qY (Inst.st (Inst.B2.ff, Inst.B2.ff) (Inst.FSet.ofList [(Inst.B2.tt, Inst.B2.ff)])) = Inst.Y5.a ∧
      Inst.qY (Inst.st (Inst.B2.ff, Inst.B2.ff) (Inst.FSet.ofList [(Inst.B2.ff, Inst.B2.tt)])) = Inst.Y5.b ∧
      (Inst.Y5.a ≼ Inst.Y5.c ∧ Inst.Y5.b ≼ Inst.Y5.c) ∧
      ¬ ∃ y : Inst.Y5, Inst.Y5.a ≼ y ∧ Inst.Y5.b ≼ y ∧ ∀ z, Inst.Y5.a ≼ z → Inst.Y5.b ≼ z → y ≼ z :=
  Inst.crdt_observation_no_join

/-! ## Highly available transactions (`sec:hat-instance`)

The opening paragraph (inputs are request sets, outputs are fact sets, both
under inclusion; the isolation level or session guarantee determines which
fact sets are permitted) is the model of `Inst.factSpec allowed P`: at input
`i` expose any fact set `F ⊆ allowed i` satisfying the isolation predicate
`P`.  The second paragraph ("The ingredients of highly available transactions
(HAT) then come apart"), on the response obligation and on sticky
availability as a deployment, points to App. `app:cap-response` and Prop.
`thm:complete-cap-deployment`; it states no claim proved here. -/

/-- Paragraph "Read committed": "Under read committed, a transaction reads
only committed versions.  Suppose two separated replicas run transactions on
disjoint keys.  One exposes `read(T₁,x,0)` and `commit(T₁)`, and the other
exposes `read(T₂,y,0)` and `commit(T₂)`.  Each read saw a committed version, so
the union of the four facts contains no dirty read and is itself permitted.
It is a common refinement of what the two replicas exposed."  Lean: each side
and their union are read committed, and the read-committed specification
satisfies Lifted Monotonicity and is consistent for any monotone
`allowed`. -/
theorem «sec:hat-instance/read-committed» {I : Type} [PO I] (allowed : I → IConf.St Inst.Fact)
    (hmono : Monotone allowed) :
    (Inst.RC Inst.acc1 ∧ Inst.RC Inst.acc2 ∧ Inst.RC (Inst.acc1.union Inst.acc2)) ∧
      (Inst.factSpec allowed Inst.RC Inst.rc_empty).LiftedMono ∧
      (Inst.factSpec allowed Inst.RC Inst.rc_empty).Consistent :=
  ⟨Inst.accumulating_example, Inst.rc_liftedMono_consistent allowed hmono⟩

/-- Paragraph "Serializability": `T₁` reads `x = 0`, writes `y = 1`, commits;
`T₂` reads `y = 0`, writes `x = 1`, commits.  "Each replica's facts are
permitted on their own.  `T₁`'s read places `T₁` before `T₂` in any serial
explanation, and `T₂`'s read places `T₂` before `T₁`.  So no serial order
explains both sets of facts, and no permitted output contains them both."
Lean: each side is serializable; no fact set
containing both sides (and supported by the requests) is serializable; hence
the serializable specification violates Lifted Monotonicity and is not
consistent. -/
theorem «sec:hat-instance/serializability-cycle» :
    (Inst.Ser Inst.ser1 ∧ Inst.Ser Inst.ser2 ∧
        ∀ G : IConf.St Inst.Fact, Inst.ser1 ≼ G → Inst.ser2 ≼ G → G ≼ Inst.serAllowed → ¬ Inst.Ser G) ∧
      ¬ (Inst.factSpec (fun i : IConf.St Inst.Fact => i) Inst.Ser Inst.ser_empty).LiftedMono ∧
      ¬ (Inst.factSpec (fun i : IConf.St Inst.Fact => i) Inst.Ser Inst.ser_empty).Consistent :=
  ⟨Inst.serializability_cycle, Inst.serializable_spec_not_consistent⟩

/-- Paragraph "Snapshot isolation": for concurrent writers `T₁, T₂` of `x`,
"Each replica's commit fact is permitted on its own.  The first-committer-wins
rule of snapshot isolation lets only one of two concurrent writers of `x`
commit, so no permitted output contains both commit facts."
Lean: each local commit is permitted, no fact set containing both is, and
the specification is not consistent. -/
theorem «sec:hat-instance/snapshot-isolation» :
    Inst.FCW Inst.fcw1 ∧ Inst.FCW Inst.fcw2 ∧
      (∀ G : IConf.St Inst.Fact, Inst.fcw1 ≼ G → Inst.fcw2 ≼ G → ¬ Inst.FCW G) ∧
      ¬ (Inst.factSpec (fun i : IConf.St Inst.Fact => i) Inst.FCW (fun h => h.1)).Consistent :=
  Inst.snapshot_fcw

/-- The boundary paragraph: "When the permitted fact sets are closed under
union, as for read committed here, whatever separated replicas expose has a
common refinement, so the guarantee stays available.  Serializability and
first-committer-wins instead exclude some combinations of facts that
separated replicas can each expose."  Lean:
(1) for any isolation predicate `P` closed under union, the fact-set
specification satisfies Lifted Monotonicity; (2) two rows below a common
input `j` with no permitted common upper bound at `j` refute Lifted
Monotonicity and consistency.  (Availability then follows from
Thm. `thm:complete-cap`; that emitting either side requires a choice is
Prop. `thm:commitments-require-coordination`, both in the general theory.) -/
theorem «sec:hat-instance/boundary» {I Φ : Type} [PO I] (allowed : I → IConf.St Φ)
    (P : IConf.St Φ → Prop) (hP0 : P Inst.noFacts) :
    (Monotone allowed → (∀ F G, P F → P G → P (F.union G)) →
        (Inst.factSpec allowed P hP0).LiftedMono) ∧
      ∀ {i₁ i₂ j : I} {F₁ F₂ : IConf.St Φ}, i₁ ≼ j → i₂ ≼ j →
        (Inst.factSpec allowed P hP0).S i₁ F₁ → (Inst.factSpec allowed P hP0).S i₂ F₂ →
        (∀ G, F₁ ≼ G → F₂ ≼ G → G ≼ allowed j → ¬ P G) →
        ¬ (Inst.factSpec allowed P hP0).LiftedMono ∧ ¬ (Inst.factSpec allowed P hP0).Consistent :=
  ⟨fun hm hU => Inst.factSpec_liftedMono allowed hm P hP0 hU,
    fun h₁ h₂ r₁ r₂ hno => Inst.factSpec_not_liftedMono allowed P hP0 h₁ h₂ r₁ r₂ hno⟩

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
specification `S_𝓘` in ours as follows.  Inputs are transaction histories:
partial orders of events, each labeled by a transaction in `T`, where one
event precedes another when the replica running the second saw the first.  A
history expands each of its downward-closed sub-orders.  We keep the locally
valid histories, in which every transaction step preserves `𝓘` on its
replica's state.  Outputs are database states, ordered by inclusion.  The
specification table permits, at input `h`, the state of any downward-closed sub-history of
`h` that is valid: every merge of what it contains satisfies `𝓘`."  Lean:
`IConf.SI M` on inputs `IConf.Inp M` (locally valid histories, expansion
order) with outputs `IConf.St V` under inclusion; full model in
`Paper/AppB_InvariantConfluence`. -/
theorem «sec:iconfluence-instance/spec» {V Tx : Type} (M : IConf.Model V Tx) (h : IConf.Inp M)
    (s : IConf.St V) :
    (IConf.SI M).S h s ↔ ∃ g, g ≼ h.1 ∧ IConf.Valid M g ∧ IConf.eval M g = s :=
  Iff.rfl

/-- **Proposition `prop:iconfluence-lm`** (Invariant confluence and Lifted
Monotonicity): "`T` is invariant confluent if and only if `S_𝓘` satisfies
Lifted Monotonicity." -/
theorem «prop:iconfluence-lm» {V Tx : Type} (M : IConf.Model V Tx) :
    M.IConfluent ↔ (IConf.SI M).LiftedMono :=
  IConf.ic_iff_liftedMono M

/-- "Invariant confluence is therefore not a separate boundary: for the
specification that exposes database states, it is Lifted Monotonicity, and
by Complete CALM it is consistency." -/
theorem «sec:iconfluence-instance/iconfluence-is-consistency» {V Tx : Type} (M : IConf.Model V Tx) :
    M.IConfluent ↔ (IConf.SI M).Consistent :=
  (IConf.ic_iff_liftedMono M).trans (complete_calm _).symm

/-- The uniqueness example: "The uniqueness constraint of Bailis et al.'s
payroll example shows the failure directly.  Two replicas each create an
employee and assign ID 7, which each sees is unused.  The history in which
neither creation saw the other is locally valid and expands both
one-creation histories, but its state has two employees with ID 7, so no
state it permits refines both."  Lean (library names from an earlier
username version of the example): versions are the employees holding ID 7;
`alloc a` creates employee `a` with ID 7 if the replica sees the ID unused;
the invariant `uModel.Inv` is "at most one employee has ID 7"; `jU` has the
unordered events `alloc 1`, `alloc 2`; `oneU n t` is the one-event history.
Consequently `S_𝓘` fails Lifted Monotonicity and the transactions are not
invariant confluent. -/
theorem «sec:iconfluence-instance/uniqueness» :
    IConf.LocValid Inst.uModel Inst.jU ∧ Inst.oneU 0 1 ≼ Inst.jU ∧ Inst.oneU 1 2 ≼ Inst.jU ∧
      IConf.eval Inst.uModel Inst.jU 1 ∧ IConf.eval Inst.uModel Inst.jU 2 ∧
      ¬ Inst.uModel.Inv (IConf.eval Inst.uModel Inst.jU) ∧
      (∀ u, (IConf.SI Inst.uModel).S ⟨Inst.jU, Inst.locValid_jU⟩ u →
        ¬ (IConf.eval Inst.uModel (Inst.oneU 0 1) ≼ u ∧ IConf.eval Inst.uModel (Inst.oneU 1 2) ≼ u)) ∧
      ¬ (IConf.SI Inst.uModel).LiftedMono ∧ ¬ Inst.uModel.IConfluent :=
  Inst.uniqueness_example

/-- "Concurrency, not the transactions alone, decides the outcome: a
transaction that is harmless after another can, when it runs without seeing
it, produce a state whose merge with the other's is invalid."  Lean:
`alloc 2` after `alloc 1` is valid, `alloc 2` alone is valid, but the merge of
`alloc 1` and `alloc 2` run concurrently from `s₀` is invalid. -/
theorem «sec:iconfluence-instance/concurrency-decides» :
    Inst.uModel.Inv (Inst.uModel.app 2 (Inst.uModel.app 1 Inst.uModel.s0)) ∧
      Inst.uModel.Inv (Inst.uModel.app 2 Inst.uModel.s0) ∧
      ¬ Inst.uModel.Inv ((Inst.uModel.app 1 Inst.uModel.s0).union (Inst.uModel.app 2 Inst.uModel.s0)) :=
  Inst.uniqueness_concurrency

/-! ## General operational specification models (`sec:operational-models`)

The opening paragraph ("Labeled transition systems and I/O automata provide
general operational models of components … Thus our specification model does
not replace an operational formalism; it is a semantic projection designed to
make the intrinsic coordination question comparable across such
formalisms.") positions the model; it states no claim of its own.

"Compiling a state machine": "We take the standard I/O-automaton
model of a state machine, its clients, and the channel that carries their
events.  The machine `M` has states `Q`, an initial state `q₀`, a transition
relation on event payloads that accepts every payload in every state, and an
observation `obs : Q → O`, which it may output at any time without changing
state.  Each of finitely many clients may send an event with any payload at
any time and receives the machine's outputs; the channel delivers each sent
event at most once, in any order or in the order sent.  In an execution of
the composed automaton, *happens-before* is Lamport's order: the transitive
closure of the local order at the machine and at each client and of the edge
from sending an event to receiving it."

Lean: Lynch–Tuttle I/O automata and their composition are `CC.IOA`
(`Foundations/IOAutomata.lean`).  The machine is `SM.Machine Q P O` (payloads
`P`; fields `q0`, `step`, `enabled`, `obs`), and `IOM.sys k M` composes the
machine automaton `IOM.machA M` (inputs `recv e`, outputs `out c o` reporting
`obs q` without changing state), the clients `IOM.cliA c` (outputs `send e`
with any payload at any time, inputs `out c o`), and the channel
`IOM.chanA k` (a bag, `k = .bag`, or a FIFO queue, `k = .fifo`; it neither
loses nor duplicates).  Events `IOM.Ev C P` carry a client, a sequence
number, and a payload.  `IOM.HB β` is happens-before on positions of the
schedule `β`.  The client type `C` is arbitrary; finiteness is not needed.
A sent event may stay in transit in a finite execution. -/

/-- "An output of the machine is an input of the client that receives it, so
a client's later sends happen after everything the machine had received when
it emitted that output."  From the remark after
Proposition `prop:induced-specification`: "A client that sends after
observing an output is ordered after everything that output reflected, and the
input records that dependence."

Lean: in an execution `β`, if the machine received `e` (position `r`) before
emitting `out c o` (position `m`), and client `c` sends `e'` at a later
position `j`, then the send of `e` happens before the send of `e'`, every
delivery of `e'` in `β` comes after position `r`, and if `e'` is received the
input of `β` orders `e` before `e'`.  The delivery claim is read within the
execution in which the client observed the output.  The rest of the remark
("what the client saw is recorded by the run's output events, which keep only
rows that refine it") applies Def. `def:output-event` to the induced
specification. -/
theorem «sec:operational-models/later-sends» {C P Q O : Type} [DecidableEq C]
    (k : IOM.ChanKind) (M : SM.Machine Q P O) {β : List (IOM.Act C P O)}
    {s : (IOM.sys (C := C) k M).St} (hx : IOA.Execution (IOM.sys k M) β s)
    {m r j : Nat} {c : C} {o : O} {e e' : IOM.Ev C P}
    (hm : β[m]? = some (.out c o)) (hrv : β[r]? = some (.recv e)) (hrm : r < m)
    (hj : IOM.SendAt β j e') (hmj : m < j) (hc : e'.client = c) :
    (∃ i, IOM.SendAt β i e ∧ IOM.HB β i j) ∧ (∀ t, β[t]? = some (.recv e') → r < t) ∧
      (.recv e' ∈ β → (IOM.input β).lt e e') :=
  IOM.send_after_out ⟨s, hx, rfl⟩ hm hrv hrm hj hmj hc

/-- **Def. `def:induced-specification`** (Induced specification).  "The
*input* of a finite execution is the set of events the machine has received,
ordered by happens-before between their sends; `h ⊑ h'` when `h ⊆ h'` and the
two orders agree on `h`.  The specification *induced* by `M` and its
environment pairs each input that occurs with the machine's observation at
the end of every execution with that input."

Lean: `IOM.input β` (membership: `recv e ∈ β`; order: happens-before between
the positions sending the two events), the order `IOM.Inp.instPO`, the
inputs that occur `IOM.OccInp C P k M`, and the table `IOM.spec k M`; the
statement unfolds each.

The remarks that follow ("This is not a
distributed execution in the sense of Section `sec:distributed-execution`.
… Happens-before here only keeps the books: it records which events each
client sent after which outputs, so the input remembers what the
environment's choices depended on.") explain the model and state no claim of
their own.  The sentence "Distributing the machine is then direct: … among
participants Section `sec:distributed-execution` applies, with the induced
specification as the specification." is argued in prose only (see the
README). -/
theorem «def:induced-specification» {C P Q O : Type} [PO O] (k : IOM.ChanKind)
    (M : SM.Machine Q P O) :
    (∀ (β : List (IOM.Act C P O)) e, (IOM.input β).mem e ↔ .recv e ∈ β) ∧
    (∀ (β : List (IOM.Act C P O)) a b, (IOM.input β).lt a b ↔
      (.recv a ∈ β ∧ .recv b ∈ β) ∧ ∃ i j, IOM.SendAt β i a ∧ IOM.SendAt β j b ∧ IOM.HB β i j) ∧
    (∀ h h' : IOM.Inp C P, h ≼ h' ↔
      (∀ e, h.mem e → h'.mem e) ∧ ∀ a b, h.mem a → h.mem b → (h.lt a b ↔ h'.lt a b)) ∧
    (∀ (h : IOM.OccInp C P k M) o, (IOM.spec k M).S h o ↔
      ∃ β s, IOA.Execution (IOM.sys k M) β s ∧ IOM.input β = h.val ∧ M.obs (s .mach) = o) :=
  ⟨fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-- **Prop. `prop:induced-specification`** (Induced specifications).
"(1) The induced specification is an ordered specification, and the input of
an execution only expands as the execution continues.  (2) With one client
and an order-preserving channel, every input is a chain and the induced
specification is the table of event sequences ordered by prefix; for a
deterministic machine it is consistent exactly when `obs(q) ⪯ obs(q')` for
every transition `q → q'` from a reachable state.  (3) Every observation in
the fiber at `h` is reached by `M` on some arrival order of the events of
`h`.  With a reordering channel and clients that observe no outputs, every
arrival order is reached.  (4) The machine's observations are confluent
across its executions—for executions with inputs `h₁,…,hₖ` and any input `h`
that occurs and expands each `hᵣ`, some execution with input `h` ends in an
observation that refines each of theirs—exactly when the induced
specification satisfies Lifted Monotonicity."

Lean, part by part:
(1) every input that occurs has a row (`IOM.spec` is a `Spec`), and
`IOM.input_mono`;
(2) one client is `C = Unit` and the channel `.fifo`; `IOM.fifo_single`:
every input is a chain, `IOM.word` (payloads in sequence order) is an order
isomorphism onto `SM.Seq P` under the prefix order carrying each fiber to the
fiber of the prefix table `SM.induced M (SM.prefixAbs P)`, and for
deterministic `M` consistency is `SM.TransMono M`;
(3) `IOM.fiber_sub` (any channel; with a FIFO channel the arrival order is
moreover a linear extension of the input order) and
`IOM.bag_fiber_of_outFree`: for the input of an execution over a bag with no
`out` actions (`IOM.OutFree`), the observation after every run of `M` on
every arrival order of its events is in the fiber;
(4) `IOM.ObsConfluent k M` is the confluence condition on observations at the
end of executions, and `IOM.confluent_iff_liftedMono`.  The proof follows the
paper's sketch; (4) unfolds the fiber in the common-expansion condition
(`IOM.obsConfluent_iff_commonExpansion`) and applies
`liftedMono_iff_commonExpansion`.  The library also proves the version for
emitted outputs (`IOM.emitConfluent_iff_liftedMono`). -/
theorem «prop:induced-specification» {C P Q O : Type} [PO O] [DecidableEq C]
    (k : IOM.ChanKind) (M : SM.Machine Q P O) :
    -- (1)
    ((∀ h : IOM.OccInp C P k M, ∃ o, (IOM.spec k M).S h o) ∧
      ∀ (β γ : List (IOM.Act C P O)) (s : (IOM.sys (C := C) k M).St),
        IOA.Execution (IOM.sys k M) (β ++ γ) s → IOM.input β ≼ IOM.input (β ++ γ)) ∧
    -- (2)
    ((∀ h : IOM.OccInp Unit P .fifo M, ∀ a b, h.val.mem a → h.val.mem b → a ≠ b →
        h.val.lt a b ∨ h.val.lt b a) ∧
      (∀ h h' : IOM.OccInp Unit P .fifo M, h ≼ h' ↔ IOM.word h ≼ IOM.word h') ∧
      (∀ w : SM.Seq P, ∃ h : IOM.OccInp Unit P .fifo M, IOM.word h = w) ∧
      (∀ h o, (IOM.spec .fifo M).S h o ↔ (SM.induced M (SM.prefixAbs P)).S (IOM.word h) o) ∧
      (SM.Deterministic M → ((IOM.spec (C := Unit) .fifo M).Consistent ↔ SM.TransMono M))) ∧
    -- (3)
    ((∀ (h : IOM.OccInp C P k M) o, (IOM.spec k M).S h o →
        ∃ w : List (IOM.Ev C P), w.Nodup ∧ (∀ e, e ∈ w ↔ h.val.mem e) ∧
          (∃ q, SM.Runs M M.q0 (w.map IOM.Ev.payload) q ∧ M.obs q = o) ∧
          (k = .fifo → w.Pairwise fun a b => ¬ h.val.lt b a)) ∧
      ∀ (β : List (IOM.Act C P O)) (s : (IOM.sys (C := C) .bag M).St),
        IOA.Execution (IOM.sys .bag M) β s → IOM.OutFree β →
        ∀ h : IOM.OccInp C P .bag M, h.val = IOM.input β →
        ∀ w : List (IOM.Ev C P), w.Nodup → (∀ e, e ∈ w ↔ h.val.mem e) →
        ∀ q, SM.Runs M M.q0 (w.map IOM.Ev.payload) q → (IOM.spec .bag M).S h (M.obs q)) ∧
    -- (4)
    (IOM.ObsConfluent (C := C) k M ↔ (IOM.spec (C := C) k M).LiftedMono) :=
  have h2 := IOM.fifo_single M
  ⟨⟨(IOM.spec k M).total, fun _ _ s hx => IOM.input_mono ⟨s, hx, rfl⟩⟩,
    ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2.2⟩,
    ⟨IOM.fiber_sub, fun _ _ hx hout h hh _ hw hmem _ hq =>
      IOM.bag_fiber_of_outFree hx hout h hh hw hmem hq⟩,
    (IOM.confluent_iff_liftedMono k M).1⟩

end Paper
end CC
