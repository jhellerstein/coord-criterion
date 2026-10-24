import CoordCriterion.Instances.Examples
import CoordCriterion.Instances.BailisDefinition
import CoordCriterion.CALM.Lemmas

/-!
# Paper §5, "Instances Across the Literature" (`sections/instances.tex`)

Statement layer for Section `sec:instances`.  Read it side by side with
`sections/instances.tex`: the `/-! ## … -/` headers follow the paper's
subsections, entries appear in paper order, and each entry quotes the claim
it formalizes.

* Numbered results and displayed equations are named by their LaTeX label
  (`«prop:iconfluence-lm»`, …).
* Unlabeled claims are named `«<enclosing label>/<slug>»`, e.g.
  `«sec:hat-instance/serializability-cycle»`.
* Every proof is a pointer to the library (`Instances/Examples.lean`,
  `Instances/InvariantConfluence.lean`, `Instances/BailisDefinition.lean`).

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

/-! ## Query monotonicity (`sec:query-instance`) -/

/-- Sec. `sec:query-instance`: "Their query specification is functional:
each input `J` has one result `Q(J)`, so each output fiber is a singleton and
directed automatically." -/
theorem «sec:query-instance/functional-directed» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) : sp.DirectedOutputs :=
  CALM.functional_directed hf

/-! ## CRDTs: monotone queries over convergent state (`sec:crdt-instance`)

The opening paragraph credits the observation that convergent state can yield
unsafe observations to Keep CALM and CRDT On; its two-phase-set example is
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

/-- Sec. `sec:crdt-instance`: "a Boolean test `[t ⊑ d]` under
`false ≼ true`, which stays true as the state grows.  A replica can thus
report that a grow-only set of failed logins has reached 100 entries without
knowing that it has seen them all."  Lean: LVars threshold queries `[t ⊑ d]`
are monotone; for `q₁₀₀(d) = [|d| ≥ 100]` on a grow-only set, `q₁₀₀ ∘ s` is
monotone and consistent, and every output at every state reachable without
commitment is exposable. -/
theorem «sec:crdt-instance/thresholds» {A : Type} (s0 : IConf.St A) :
    Monotone (fun U : Inst.FSet (IConf.St A) => Inst.qThr 100 (Inst.st s0 U)) ∧
      (graph (fun U : Inst.FSet (IConf.St A) => Inst.qThr 100 (Inst.st s0 U))).Consistent ∧
      (∀ τ : State (graph (fun U : Inst.FSet (IConf.St A) => Inst.qThr 100 (Inst.st s0 U))),
        ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o) ∧
      ∀ {D : Type} [PO D] (t : D), Monotone (fun d : D => (t ≼ d : Prop)) :=
  ⟨Inst.Q100_mono s0, (Inst.Q100_consistent_exposable s0).1, (Inst.Q100_consistent_exposable s0).2,
    fun t => Inst.lvar_threshold_mono t⟩

/-- Sec. `sec:crdt-instance`: "A last-writer-wins replica converges, yet it
can expose one value and later discard it, so whether convergence is monotone
depends on the declared output order."  Lean: LWW states `(timestamp, value)`
in lexicographic order; the state function is monotone, but exposing the value
under the discrete order is neither monotone nor consistent. -/
theorem «sec:crdt-instance/lww» :
    Monotone (Inst.st (⟨0, 0⟩ : Inst.LWW)) ∧
      ¬ Monotone (fun U : Inst.FSet Inst.LWW => (⟨(Inst.st ⟨0, 0⟩ U).v⟩ : Inst.Disc Nat)) ∧
      ¬ (graph (fun U : Inst.FSet Inst.LWW => (⟨(Inst.st ⟨0, 0⟩ U).v⟩ : Inst.Disc Nat))).Consistent :=
  Inst.lww_depends_on_order

/-! ## Highly available transactions (`sec:hat-instance`)

The opening paragraph (inputs are request sets, outputs are fact sets, both
under inclusion; the isolation level fixes the specification) is the model of
`Inst.factSpec allowed P`: at input `i` expose any fact set `F ⊆ allowed i`
satisfying the isolation predicate `P`.  Its remarks on the response
obligation and on sticky availability as a deployment are pointers to
App. `app:cap-response` and Prop. `thm:complete-cap-deployment`, not claims
proved here. -/

/-- Paragraph "Accumulating facts": one replica exposes
`read(T₁,x,0), commit(T₁)`, the other `read(T₂,y,0), commit(T₂)`; "the union
contains no dirty read.  Under the stated read-committed specification …
later delivery keeps all four facts."  Lean: each side and their union are
read committed, and the read-committed specification satisfies Lifted
Monotonicity and is consistent for any monotone `allowed`. -/
theorem «sec:hat-instance/accumulating-facts» {I : Type} [PO I] (allowed : I → IConf.St Inst.Fact)
    (hmono : Monotone allowed) :
    (Inst.RC Inst.acc1 ∧ Inst.RC Inst.acc2 ∧ Inst.RC (Inst.acc1.union Inst.acc2)) ∧
      (Inst.factSpec allowed Inst.RC Inst.rc_empty).LiftedMono ∧
      (Inst.factSpec allowed Inst.RC Inst.rc_empty).Consistent :=
  ⟨Inst.accumulating_example, Inst.rc_liftedMono_consistent allowed hmono⟩

/-- Paragraph "Serializability and transaction ordering": `T₁` reads `x = 0`,
writes `y = 1`, commits; `T₂` reads `y = 0`, writes `x = 1`, commits.  "The
serialization graph contains a cycle, so no serial order of `T₁` and `T₂`
explains both sets of facts."  Lean: each side is serializable; no fact set
containing both sides (and supported by the requests) is serializable; hence
the serializable specification violates Lifted Monotonicity and is not
consistent. -/
theorem «sec:hat-instance/serializability-cycle» :
    (Inst.Ser Inst.ser1 ∧ Inst.Ser Inst.ser2 ∧
        ∀ G : IConf.St Inst.Fact, Inst.ser1 ≼ G → Inst.ser2 ≼ G → G ≼ Inst.serAllowed → ¬ Inst.Ser G) ∧
      ¬ (Inst.factSpec (fun i : IConf.St Inst.Fact => i) Inst.Ser Inst.ser_empty).LiftedMono ∧
      ¬ (Inst.factSpec (fun i : IConf.St Inst.Fact => i) Inst.Ser Inst.ser_empty).Consistent :=
  ⟨Inst.serializability_cycle, Inst.serializable_spec_not_consistent⟩

/-- Paragraph "Snapshot isolation": for overlapping writers `T₁, T₂` of `x`,
"first-committer-wins … allows no output containing both commit facts."
Lean: each local commit is permitted, no fact set containing both is, and
the specification is not consistent. -/
theorem «sec:hat-instance/snapshot-isolation» :
    Inst.FCW Inst.fcw1 ∧ Inst.FCW Inst.fcw2 ∧
      (∀ G : IConf.St Inst.Fact, Inst.fcw1 ≼ G → Inst.fcw2 ≼ G → ¬ Inst.FCW G) ∧
      ¬ (Inst.factSpec (fun i : IConf.St Inst.Fact => i) Inst.FCW (fun h => h.1)).Consistent :=
  Inst.snapshot_fcw

/-- The boundary paragraph: "A guarantee whose permitted fact sets are closed
under union … has a common outcome for whatever separated replicas expose,
so it stays available.  One that orders or excludes concurrent transactions …
rules out combinations that separated replicas can each expose."  Lean:
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

/-- "A state is reachable in their model when it can be derived from `s₀` by
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

/-- "The inputs are the locally valid histories … a history is valid when
every merge of what it contains satisfies `𝓘` …  The specification `S_𝓘`
lets a replica expose the state of any valid downward-closed sub-history of
its input."  Lean: `IConf.SI M` on inputs `IConf.Inp M` (locally valid
histories, expansion order); full model in `Paper/AppB_InvariantConfluence`. -/
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

/-- The uniqueness example: "Two replicas each observe that username `sam`
is free and allocate it to different accounts.  The history in which neither
allocation saw the other is locally valid and expands both one-allocation
histories, but its state has two owners, so no state it permits covers
both."  Lean: versions are owning accounts, `alloc a` allocates `sam` to `a`
if the replica sees it free, the invariant is "at most one owner"; `jU` has
the unordered events `alloc 1`, `alloc 2`; `oneU n t` is the one-event
history.  Consequently `S_𝓘` fails Lifted Monotonicity and the transactions
are not invariant confluent. -/
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

end Paper
end CC
