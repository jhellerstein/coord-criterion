import CoordCriterion.CALM.Examples
import CoordCriterion.CAP.ResponseForm
import CoordCriterion.CompleteCALM.Theorem
import CoordCriterion.Instances.Examples

/-!
# Refinements of relational-transducer CALM (Section 6.1)

Supports the second paragraph of `sec:query-instance` and the paragraph on
Baccaert and Ketsman that follows it (`sections/instances.tex`).  The
transducer models of those papers are not formalized; this file checks only
the mapping into our frame.

* Weaker monotonicities (Ameloot, Ketsman, Neven, Zinn, TODS 2015).  A query
  is domain-distinct-monotone (resp. domain-disjoint-monotone) when
  `Q(I) ⊆ Q(I ∪ J)` for every `J` whose facts each contain a value not in
  `adom(I)` (resp. are non-nullary and use only such values).  We declare the
  input order "`K` expands `I` when `I ⊆ K` and every fact of `K \ I` is
  admissible for `I`" (`ExtInp`), for an admissibility predicate that is
  antitone in `I` (`Adm`).  Each weaker monotonicity is exactly monotonicity of
  `J ↦ Q(J)` under the matching order (`rmono_iff_monotone`), so Functional
  CALM applies (`rmono_iff_consistent`).  Ordinary inclusion is the case
  where every fact is admissible (`allAdm`).
* The one-fact versions of those definitions (Zinn, CoRR 2012) are strictly
  weaker: the query "no 2-cycle" passes the one-fact domain-distinct test but
  is not domain-disjoint-monotone (`noCycle2_*`).
* Behaviors (Baccaert and Ketsman, PODS 2023; Inf. Syst. 2026).  Inputs are
  located facts, ordered by network expansion (new facts only at new nodes,
  `netAdm`), so the network is read off the input, and a behavior is a
  relational specification on them.  A transducer computes a behavior when
  every run lands in it, so an implementation realizes a sub-behavior; the
  comparison is Complete CAP with that sub-behavior as availability relation
  (`CAP.ConsistentOn`).  Node monotonicity (`NodeMono`) is the
  common-expansion condition asked only of two rows at disjoint networks
  (`nodeMono_iff_disjointPair`), so consistency implies it
  (`nodeMono_of_consistent`).  Choice alone does not separate the two: the
  node-monotone `pick` has a non-directed fiber, yet `pick` is consistent on
  the total sub-behavior `pickTrue`.  Overlapping networks do: for
  spanning-tree behaviors no total sub-behavior is consistent
  (`no_consistentOn_of_triangle`), and the node-monotone `tree` is one
  (`tree_nodeMono`, `tree_no_consistentOn`).  For functional behaviors node
  monotonicity and consistency coincide (`nodeMono_graph_iff`).

Modeling choices.  Instances are `PSet F` (predicates under inclusion, as in
`eq:query-monotonicity`); finiteness plays no role.  The values of a fact are
a predicate `vals : F → V → Prop`; the location of a fact is `loc : F → N`.
Located output facts are `PSet G` under inclusion, so `K₁ ∪ K₂ ⊆ K` is
`K₁ ≼ K ∧ K₂ ≼ K`.
-/

namespace CC
namespace QRef

open CC.CALM (PSet)
open CC.Comp (Monotone graph graph_liftedMono_iff)

theorem PSet.ext' {F : Type} {s t : PSet F} (h : ∀ x, s.mem x ↔ t.mem x) : s = t :=
  PO.antisymm (fun x => (h x).1) (fun x => (h x).2)

/-- Union of instances. -/
def union {F : Type} (I J : PSet F) : PSet F := ⟨fun f => I.mem f ∨ J.mem f⟩

/-! ## Restricted expansion orders -/

/-- An admissibility predicate on new facts, antitone in the instance. -/
structure Adm (F : Type) where
  ok : PSet F → F → Prop
  anti : ∀ {I J : PSet F} {f : F}, I ≼ J → ok J f → ok I f

/-- Instances ordered by admissible expansion. -/
structure ExtInp {F : Type} (a : Adm F) where
  set : PSet F

/-- `I ≼ K` iff `I ⊆ K` and every fact of `K \ I` is admissible for `I`. -/
instance {F : Type} (a : Adm F) : PO (ExtInp a) where
  le I K := I.set ≼ K.set ∧ ∀ f, K.set.mem f → ¬ I.set.mem f → a.ok I.set f
  refl I := ⟨PO.refl _, fun _ h hn => absurd h hn⟩
  trans {I J K} h₁ h₂ := by
    refine ⟨PO.trans h₁.1 h₂.1, fun f hK hI => ?_⟩
    by_cases hJ : J.set.mem f
    · exact h₁.2 f hJ hI
    · exact a.anti h₁.1 (h₂.2 f hK hJ)
  antisymm {I K} h₁ h₂ := by
    have : I.set = K.set := PO.antisymm h₁.1 h₂.1
    cases I; cases K; cases this; rfl

/-- Monotonicity restricted to admissible expansions:
`Q(I) ⊆ Q(I ∪ J)` whenever every fact of `J` is admissible for `I`. -/
def RMono {F A : Type} (a : Adm F) (Q : PSet F → PSet A) : Prop :=
  ∀ I J : PSet F, (∀ f, J.mem f → a.ok I f) → Q I ≼ Q (union I J)

/-- The restricted monotonicity of `Q` is monotonicity of `J ↦ Q(J)` under
the admissible-expansion order. -/
theorem rmono_iff_monotone {F A : Type} (a : Adm F) (Q : PSet F → PSet A) :
    RMono a Q ↔ Monotone (fun I : ExtInp a => Q I.set) := by
  constructor
  · intro h I K hIK
    have hK : union I.set ⟨fun f => K.set.mem f ∧ ¬ I.set.mem f⟩ = K.set :=
      PSet.ext' fun f => ⟨fun h' => h'.elim (hIK.1 f) (·.1), fun hf => by
        by_cases hI : I.set.mem f
        · exact Or.inl hI
        · exact Or.inr ⟨hf, hI⟩⟩
    have := h I.set ⟨fun f => K.set.mem f ∧ ¬ I.set.mem f⟩ fun f hf => hIK.2 f hf.1 hf.2
    rw [hK] at this
    exact this
  · intro h I J hJ
    exact h ⟨I⟩ ⟨union I J⟩ ⟨fun _ hf => Or.inl hf, fun f hf hI => hf.elim (absurd · hI) (hJ f)⟩

/-- By Functional CALM, the graph of `Q` over the admissible-expansion order is
consistent exactly when `Q` is monotone for admissible expansions. -/
theorem rmono_iff_consistent {F A : Type} (a : Adm F) (Q : PSet F → PSet A) :
    (graph (fun I : ExtInp a => Q I.set)).Consistent ↔ RMono a Q := by
  rw [functional_calm (Inst.graph_functional _), Inst.graph_monotoneF_iff]
  exact (rmono_iff_monotone a Q).symm

/-! ## Domain-distinct and domain-disjoint expansion -/

section Domain
variable {F V : Type} (vals : F → V → Prop)

/-- `v ∈ adom(I)`. -/
def InAdom (I : PSet F) (v : V) : Prop := ∃ f, I.mem f ∧ vals f v

/-- `f` is domain distinct from `I`: it has a value not in `adom(I)`. -/
def DistinctFrom (I : PSet F) (f : F) : Prop := ∃ v, vals f v ∧ ¬ InAdom vals I v

/-- `f` is domain disjoint from `I`: it is non-nullary and all its values are
outside `adom(I)` (nullary facts are never domain disjoint, TODS §6). -/
def DisjointFrom (I : PSet F) (f : F) : Prop :=
  (∃ v, vals f v) ∧ ∀ v, vals f v → ¬ InAdom vals I v

theorem inAdom_mono {I J : PSet F} (h : I ≼ J) {v : V} : InAdom vals I v → InAdom vals J v :=
  fun ⟨f, hf, hv⟩ => ⟨f, h f hf, hv⟩

/-- Domain-distinct expansion. -/
def distinctAdm : Adm F where
  ok := DistinctFrom vals
  anti h := fun ⟨v, hv, hn⟩ => ⟨v, hv, fun hI => hn (inAdom_mono vals h hI)⟩

/-- Domain-disjoint expansion. -/
def disjointAdm : Adm F where
  ok := DisjointFrom vals
  anti h := fun ⟨hne, hall⟩ => ⟨hne, fun v hv hI => hall v hv (inAdom_mono vals h hI)⟩

/-- Domain-distinct-monotone (TODS Def. 1). -/
def DistinctMono {A : Type} (Q : PSet F → PSet A) : Prop :=
  ∀ I J : PSet F, (∀ f, J.mem f → DistinctFrom vals I f) → Q I ≼ Q (union I J)

/-- Domain-disjoint-monotone (TODS Def. 1, with TODS §6 for nullary facts). -/
def DisjointMono {A : Type} (Q : PSet F → PSet A) : Prop :=
  ∀ I J : PSet F, (∀ f, J.mem f → DisjointFrom vals I f) → Q I ≼ Q (union I J)

/-- Domain-disjoint facts are domain distinct, so `M_distinct ⊆ M_disjoint`. -/
theorem disjointMono_of_distinctMono {A : Type} {Q : PSet F → PSet A}
    (h : DistinctMono vals Q) : DisjointMono vals Q :=
  fun I J hJ => h I J fun f hf =>
    let ⟨⟨v, hv⟩, hall⟩ := hJ f hf
    ⟨v, hv, hall v hv⟩

/-- Domain-distinct monotonicity is Functional CALM under the
domain-distinct expansion order. -/
theorem distinctMono_iff {A : Type} (Q : PSet F → PSet A) :
    (DistinctMono vals Q ↔ Monotone (fun I : ExtInp (distinctAdm vals) => Q I.set)) ∧
      ((graph (fun I : ExtInp (distinctAdm vals) => Q I.set)).Consistent ↔ DistinctMono vals Q) :=
  ⟨rmono_iff_monotone (distinctAdm vals) Q, rmono_iff_consistent (distinctAdm vals) Q⟩

/-- Domain-disjoint monotonicity is Functional CALM under the
domain-disjoint expansion order. -/
theorem disjointMono_iff {A : Type} (Q : PSet F → PSet A) :
    (DisjointMono vals Q ↔ Monotone (fun I : ExtInp (disjointAdm vals) => Q I.set)) ∧
      ((graph (fun I : ExtInp (disjointAdm vals) => Q I.set)).Consistent ↔ DisjointMono vals Q) :=
  ⟨rmono_iff_monotone (disjointAdm vals) Q, rmono_iff_consistent (disjointAdm vals) Q⟩

end Domain

/-- Every fact admissible: the order is inclusion. -/
def allAdm (F : Type) : Adm F where
  ok _ _ := True
  anti _ h := h

/-- With every fact admissible, restricted monotonicity is ordinary
monotonicity (`Q(I) ⊆ Q(I ∪ J)` for all `J`), the relational-transducer case. -/
theorem allAdm_rmono_iff {F A : Type} (Q : PSet F → PSet A) :
    RMono (allAdm F) Q ↔ ∀ J J' : PSet F, J ≼ J' → Q J ≼ Q J' := by
  constructor
  · intro h J J' hJ
    have hU : union J J' = J' := PSet.ext' fun f => ⟨fun h' => h'.elim (hJ f) id, Or.inr⟩
    have := h J J' fun _ _ => trivial
    rwa [hU] at this
  · intro h I J _
    exact h I (union I J) fun _ hf => Or.inl hf

/-! ## The one-fact versions are weaker

Zinn's report states both weaker monotonicities for one added fact at a time.
The query "the edge relation has no 2-cycle" passes the one-fact
domain-distinct test (hence also the one-fact domain-disjoint test), yet
adding the domain-disjoint instance `{e(0,1), e(1,0)}` to `∅` falsifies it. -/

section OneFact

/-- Values of an edge `e(a, b)`. -/
def edgeVals : Nat × Nat → Nat → Prop := fun e v => v = e.1 ∨ v = e.2

/-- The Boolean query "no 2-cycle" (output `{()}` for true, `∅` for false). -/
def noCycle2 (I : PSet (Nat × Nat)) : PSet Unit :=
  ⟨fun _ => ¬ ∃ a b, a ≠ b ∧ I.mem (a, b) ∧ I.mem (b, a)⟩

/-- One-fact domain-distinct monotonicity. -/
def OneFactDistinctMono {F V A : Type} (vals : F → V → Prop) (Q : PSet F → PSet A) : Prop :=
  ∀ (I : PSet F) (f : F), DistinctFrom vals I f → Q I ≼ Q (union I ⟨fun g => g = f⟩)

theorem noCycle2_oneFact : OneFactDistinctMono edgeVals noCycle2 := by
  intro I f ⟨v, hv, hn⟩ u hI ⟨a, b, hab, h1, h2⟩
  apply hI
  -- every value of a fact of `I` is in `adom(I)`
  have inI : ∀ x y, I.mem (x, y) → InAdom edgeVals I x ∧ InAdom edgeVals I y :=
    fun x y h => ⟨⟨(x, y), h, Or.inl rfl⟩, ⟨(x, y), h, Or.inr rfl⟩⟩
  have fresh : ∀ x y, f = (x, y) → InAdom edgeVals I x → InAdom edgeVals I y → False := by
    intro x y hf hx hy
    subst hf
    rcases hv with rfl | rfl
    · exact hn hx
    · exact hn hy
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact ⟨a, b, hab, h1, h2⟩
  · exact (fresh b a h2.symm (inI a b h1).2 (inI a b h1).1).elim
  · exact (fresh a b h1.symm (inI b a h2).2 (inI b a h2).1).elim
  · have : (a, b) = (b, a) := h1.trans h2.symm
    exact (hab (Prod.mk.inj this).1).elim

theorem noCycle2_not_disjointMono : ¬ DisjointMono edgeVals noCycle2 := by
  intro h
  have := h ⟨fun _ => False⟩ ⟨fun e => e = (0, 1) ∨ e = (1, 0)⟩ (fun f _ =>
    ⟨⟨f.1, Or.inl rfl⟩, fun _ _ ⟨_, hg, _⟩ => hg⟩) () (fun ⟨_, _, _, h, _⟩ => h)
  exact this ⟨0, 1, by decide, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩

theorem noCycle2_not_distinctMono : ¬ DistinctMono edgeVals noCycle2 :=
  fun h => noCycle2_not_disjointMono (disjointMono_of_distinctMono edgeVals h)

end OneFact

/-! ## Behaviors over located facts -/

section Behaviors
variable {F N : Type} (loc : F → N)

/-- `x ∈ netw(H)`. -/
def Netw (H : PSet F) (x : N) : Prop := ∃ f, H.mem f ∧ loc f = x

/-- Network expansion: new facts only at nodes outside `netw(H)`. -/
def netAdm : Adm F where
  ok H f := ¬ Netw loc H (loc f)
  anti h hn := fun ⟨g, hg, hl⟩ => hn ⟨g, h g hg, hl⟩

/-- Node monotonicity (Baccaert–Ketsman, Inf. Syst. 2026, Def. 7): outputs of
a behavior on two disjoint networks have a common refinement at the merged
network. -/
def NodeMono {G : Type} (B : Spec (ExtInp (netAdm loc)) (PSet G)) : Prop :=
  ∀ H₁ H₂ : PSet F, (∀ x, Netw loc H₁ x → ¬ Netw loc H₂ x) →
    ∀ K₁ K₂, B.S ⟨H₁⟩ K₁ → B.S ⟨H₂⟩ K₂ → ∃ K, B.S ⟨union H₁ H₂⟩ K ∧ K₁ ≼ K ∧ K₂ ≼ K

/-- The common-expansion condition asked only of two rows at disjoint
networks: every common expansion `j` of their inputs has a common refinement
of their outputs. -/
def DisjointPairExpansion {G : Type} (B : Spec (ExtInp (netAdm loc)) (PSet G)) : Prop :=
  ∀ H₁ H₂ : PSet F, (∀ x, Netw loc H₁ x → ¬ Netw loc H₂ x) →
    ∀ K₁ K₂, B.S ⟨H₁⟩ K₁ → B.S ⟨H₂⟩ K₂ →
      ∀ j : ExtInp (netAdm loc), (⟨H₁⟩ : ExtInp (netAdm loc)) ≼ j →
        (⟨H₂⟩ : ExtInp (netAdm loc)) ≼ j → ∃ u, B.S j u ∧ K₁ ≼ u ∧ K₂ ≼ u

theorem le_union_left {H₁ H₂ : PSet F} (hd : ∀ x, Netw loc H₁ x → ¬ Netw loc H₂ x) :
    (⟨H₁⟩ : ExtInp (netAdm loc)) ≼ ⟨union H₁ H₂⟩ :=
  ⟨fun _ hf => Or.inl hf, fun f hf hn => hf.elim (absurd · hn) fun h2 h1 => hd _ h1 ⟨f, h2, rfl⟩⟩

theorem le_union_right {H₁ H₂ : PSet F} (hd : ∀ x, Netw loc H₁ x → ¬ Netw loc H₂ x) :
    (⟨H₂⟩ : ExtInp (netAdm loc)) ≼ ⟨union H₁ H₂⟩ :=
  ⟨fun _ hf => Or.inr hf, fun f hf hn => hf.elim (fun h1 h2 => hd _ ⟨f, h1, rfl⟩ h2) (absurd · hn)⟩

/-- Node monotonicity is the common-expansion condition for two rows at
disjoint networks.  The merged network is one common expansion; any other `j`
adds facts only at further new nodes, and node monotonicity with those facts
carries the refinement to `j`. -/
theorem nodeMono_iff_disjointPair {G : Type} (B : Spec (ExtInp (netAdm loc)) (PSet G)) :
    NodeMono loc B ↔ DisjointPairExpansion loc B := by
  constructor
  · intro h H₁ H₂ hd K₁ K₂ h₁ h₂ j hj₁ hj₂
    obtain ⟨K, hK, k1, k2⟩ := h H₁ H₂ hd K₁ K₂ h₁ h₂
    let U := union H₁ H₂
    let R : PSet F := ⟨fun f => j.set.mem f ∧ ¬ U.mem f⟩
    have hdR : ∀ x, Netw loc U x → ¬ Netw loc R x := by
      intro x ⟨g, hg, hgl⟩ ⟨f, ⟨hfj, hfU⟩, hfl⟩
      rcases hg with hg | hg
      · exact hj₁.2 f hfj (fun h' => hfU (Or.inl h')) ⟨g, hg, hgl.trans hfl.symm⟩
      · exact hj₂.2 f hfj (fun h' => hfU (Or.inr h')) ⟨g, hg, hgl.trans hfl.symm⟩
    obtain ⟨KR, hKR⟩ := B.total ⟨R⟩
    obtain ⟨u, hu, ku, _⟩ := h U R hdR K KR hK hKR
    have hset : union U R = j.set :=
      PSet.ext' fun f => ⟨fun h' => h'.elim (fun hU => hU.elim (hj₁.1 f) (hj₂.1 f)) (·.1),
        fun hf => by
          by_cases hU : U.mem f
          · exact Or.inl hU
          · exact Or.inr ⟨hf, hU⟩⟩
    have hj : (⟨union U R⟩ : ExtInp (netAdm loc)) = j := by
      cases j; simp only at hset; rw [hset]
    exact ⟨u, hj ▸ hu, PO.trans k1 ku, PO.trans k2 ku⟩
  · intro h H₁ H₂ hd K₁ K₂ h₁ h₂
    exact h H₁ H₂ hd K₁ K₂ h₁ h₂ _ (le_union_left loc hd) (le_union_right loc hd)

/-- Consistency (equivalently Lifted Monotonicity) implies node monotonicity. -/
theorem nodeMono_of_consistent {G : Type} {B : Spec (ExtInp (netAdm loc)) (PSet G)}
    (hc : B.Consistent) : NodeMono loc B := by
  intro H₁ H₂ hd K₁ K₂ h₁ h₂
  obtain ⟨u, hu, hall⟩ := (complete_calm_commonExpansion B).1 hc [(⟨H₁⟩, K₁), (⟨H₂⟩, K₂)]
    (by simp [h₁, h₂]) ⟨union H₁ H₂⟩ (by simp [le_union_left loc hd, le_union_right loc hd])
  exact ⟨u, hu, hall (⟨H₁⟩, K₁) (by simp), hall (⟨H₂⟩, K₂) (by simp)⟩

/-- For a deterministic behavior `b`, node monotonicity is monotonicity under
network expansion, hence (Functional CALM) consistency. -/
theorem nodeMono_graph_iff {G : Type} (b : ExtInp (netAdm loc) → PSet G) :
    (NodeMono loc (graph b) ↔ Monotone b) ∧ ((graph b).Consistent ↔ Monotone b) := by
  refine ⟨⟨fun h H K hHK => ?_, fun hm H₁ H₂ hd K₁ K₂ h₁ h₂ => ?_⟩, ?_⟩
  · let H₂ : PSet F := ⟨fun f => K.set.mem f ∧ ¬ H.set.mem f⟩
    have hd : ∀ x, Netw loc H.set x → ¬ Netw loc H₂ x := fun x hx ⟨f, hf, hl⟩ =>
      hHK.2 f hf.1 hf.2 (hl ▸ hx)
    have hU : (⟨union H.set H₂⟩ : ExtInp (netAdm loc)) = K := by
      have : union H.set H₂ = K.set :=
        PSet.ext' fun f => ⟨fun h' => h'.elim (hHK.1 f) (·.1), fun hf => by
          by_cases hH : H.set.mem f
          · exact Or.inl hH
          · exact Or.inr ⟨hf, hH⟩⟩
      rw [this]
    obtain ⟨u, hu, h1, _⟩ := h H.set H₂ hd _ _ rfl rfl
    have hu' : u = b K := by rw [← hU]; exact hu
    exact hu' ▸ h1
  · exact ⟨_, rfl, (show K₁ = _ from h₁) ▸ hm _ _ (le_union_left loc hd),
      (show K₂ = _ from h₂) ▸ hm _ _ (le_union_right loc hd)⟩
  · rw [functional_calm (Inst.graph_functional _), Inst.graph_monotoneF_iff]

end Behaviors

/-! ### Node names as input

The examples below take as input a set of node names (`Node@x()`, located at
`x`), so `loc = id` and network expansion is inclusion. -/

/-- The network with node set `P`. -/
def net (P : Nat → Prop) : ExtInp (netAdm (id : Nat → Nat)) := ⟨⟨P⟩⟩

theorem net_le {H K : PSet Nat} (h : ∀ x, H.mem x → K.mem x) :
    (⟨H⟩ : ExtInp (netAdm (id : Nat → Nat))) ≼ ⟨K⟩ :=
  ⟨h, fun f _ hn ⟨g, hg, hgf⟩ => hn ((show g = f from hgf) ▸ hg)⟩

/-! ### Each node picks a Boolean: a choice that a sub-behavior removes

An output is a set of located facts `Pick@x(c)`, at nodes of the input, with
at most one pick per node.  The behavior is node monotone, and its fiber at
`{0}` is not directed, so it fails Lifted Monotonicity.  Baccaert and Ketsman
only ask that an implementation compute it, that is, land in some
sub-behavior.  The sub-behavior "every node picks `true`" is total, and the
behavior is consistent on it, so Complete CAP covers it with that
availability relation. -/

section Pick

/-- The pick behavior. -/
def pick : Spec (ExtInp (netAdm (id : Nat → Nat))) (PSet (Nat × Bool)) where
  S H K := (∀ x c, K.mem (x, c) → H.set.mem x) ∧ ∀ x c c', K.mem (x, c) → K.mem (x, c') → c = c'
  total _ := ⟨⟨fun _ => False⟩, fun _ _ h => h.elim, fun _ _ _ h => h.elim⟩

theorem pick_nodeMono : NodeMono id pick := by
  intro H₁ H₂ hd K₁ K₂ ⟨l₁, u₁⟩ ⟨l₂, u₂⟩
  refine ⟨union K₁ K₂, ⟨fun x c h => h.elim (fun h => Or.inl (l₁ x c h)) fun h => Or.inr (l₂ x c h),
    fun x c c' h h' => ?_⟩, fun _ h => Or.inl h, fun _ h => Or.inr h⟩
  rcases h with h | h <;> rcases h' with h' | h'
  · exact u₁ x c c' h h'
  · exact (hd x ⟨x, l₁ x c h, rfl⟩ ⟨x, l₂ x c' h', rfl⟩).elim
  · exact (hd x ⟨x, l₁ x c' h', rfl⟩ ⟨x, l₂ x c h, rfl⟩).elim
  · exact u₂ x c c' h h'

theorem pick_not_directed : ¬ pick.DirectedOutputs := by
  intro h
  let H : ExtInp (netAdm (id : Nat → Nat)) := ⟨⟨fun x => x = 0⟩⟩
  obtain ⟨u, ⟨_, hu⟩, hall⟩ := h H [⟨fun p => p = (0, true)⟩, ⟨fun p => p = (0, false)⟩] (by simp)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨fun y c hy => by cases hy; rfl, fun y c c' h h' => by cases h; cases h'; rfl⟩
      · exact ⟨fun y c hy => by cases hy; rfl, fun y c c' h h' => by cases h; cases h'; rfl⟩)
  have h1 := hall _ (List.mem_cons_self ..) (0, true) rfl
  have h2 := hall _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (0, false) rfl
  exact absurd (hu 0 true false h1 h2) (by decide)

theorem pick_not_consistent : ¬ pick.Consistent := fun hc =>
  pick_not_directed fun i => (complete_calm pick).1 hc i i (PO.refl i)

/-- The sub-behavior in which every node picks `true`. -/
def pickTrue : Table (ExtInp (netAdm (id : Nat → Nat))) (PSet (Nat × Bool)) :=
  fun H K => K = ⟨fun p => H.set.mem p.1 ∧ p.2 = true⟩

theorem pickTrue_sub : ∀ H K, pickTrue H K → pick.S H K := by
  intro H K h
  subst h
  exact ⟨fun _ _ h => h.1, fun _ _ _ h h' => h.2.trans h'.2.symm⟩

theorem pickTrue_total : ∀ H, ∃ K, pickTrue H K := fun _ => ⟨_, rfl⟩

/-- `pick` is consistent on `pickTrue`. -/
theorem pick_consistentOn_pickTrue : CAP.ConsistentOn pick pickTrue := by
  intro rows hrows j hj
  refine ⟨_, pickTrue_sub j _ rfl, fun r hr => ?_⟩
  rw [show r.2 = _ from hrows r hr]
  exact fun p hp => ⟨(hj r hr).1 _ hp.1, hp.2⟩

end Pick

/-! ### Overlapping networks: no consistent sub-behavior

Baccaert and Ketsman's `Top_span` (Inf. Syst. 2026, Example 8) permits every
spanning tree of the network.  At a two-node network every tree has the one
edge; a tree on three nodes has two edges.  The networks `{0,1}`, `{1,2}`,
`{0,2}` overlap pairwise and have the common expansion `{0,1,2}`, so the
common-expansion condition on any total sub-behavior asks for a tree on
`{0,1,2}` with all three edges (`no_consistentOn_of_triangle`).

`tree` is a concrete such behavior: spanning trees in which every node other
than the least has one parent, smaller than itself.  It is node monotone
(`tree_nodeMono`): across two disjoint networks, the least node of one gains
the least node of the other as parent if that one is smaller.  It has no
total sub-behavior on which it is consistent (`tree_no_consistentOn`).
Output facts `(x, y)` read "the parent of `x` is `y`". -/

section Tree

/-- `x` and `y` are linked in `K`. -/
def Adj (K : PSet (Nat × Nat)) (x y : Nat) : Prop := K.mem (x, y) ∨ K.mem (y, x)

/-- If every output at a two-node network links its nodes, and no output at
`{0,1,2}` links all three pairs, then no total sub-behavior `A` has `B`
consistent on `A`. -/
theorem no_consistentOn_of_triangle
    (B : Spec (ExtInp (netAdm (id : Nat → Nat))) (PSet (Nat × Nat)))
    (hpair : ∀ a b K, a ≠ b → B.S (net fun x => x = a ∨ x = b) K → Adj K a b)
    (htri : ∀ K, B.S (net fun x => x = 0 ∨ x = 1 ∨ x = 2) K →
      ¬ (Adj K 0 1 ∧ Adj K 1 2 ∧ Adj K 0 2))
    (A : Table (ExtInp (netAdm (id : Nat → Nat))) (PSet (Nat × Nat)))
    (hA : ∀ H, ∃ K, A H K) (hsub : ∀ H K, A H K → B.S H K) :
    ¬ CAP.ConsistentOn B A := by
  intro hc
  let H₀₁ := net fun x => x = 0 ∨ x = 1
  let H₁₂ := net fun x => x = 1 ∨ x = 2
  let H₀₂ := net fun x => x = 0 ∨ x = 2
  let J := net fun x => x = 0 ∨ x = 1 ∨ x = 2
  obtain ⟨K₀₁, h₀₁⟩ := hA H₀₁
  obtain ⟨K₁₂, h₁₂⟩ := hA H₁₂
  obtain ⟨K₀₂, h₀₂⟩ := hA H₀₂
  have m₁ : (H₀₁, K₀₁) ∈ [(H₀₁, K₀₁), (H₁₂, K₁₂), (H₀₂, K₀₂)] := List.mem_cons_self ..
  have m₂ : (H₁₂, K₁₂) ∈ [(H₀₁, K₀₁), (H₁₂, K₁₂), (H₀₂, K₀₂)] :=
    List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have m₃ : (H₀₂, K₀₂) ∈ [(H₀₁, K₀₁), (H₁₂, K₁₂), (H₀₂, K₀₂)] :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have cases : ∀ r ∈ [(H₀₁, K₀₁), (H₁₂, K₁₂), (H₀₂, K₀₂)],
      r = (H₀₁, K₀₁) ∨ r = (H₁₂, K₁₂) ∨ r = (H₀₂, K₀₂) := by
    intro r hr; simpa using hr
  obtain ⟨u, hu, hall⟩ := hc [(H₀₁, K₀₁), (H₁₂, K₁₂), (H₀₂, K₀₂)]
    (fun r hr => by rcases cases r hr with rfl | rfl | rfl <;> assumption) J
    (fun r hr => by
      rcases cases r hr with rfl | rfl | rfl <;>
        exact net_le fun x (hx : _ ∨ _) => show _ ∨ _ ∨ _ by omega)
  have tr : ∀ K a b, K ≼ u → Adj K a b → Adj u a b := fun _ _ _ h hab =>
    hab.elim (fun h' => Or.inl (h _ h')) (fun h' => Or.inr (h _ h'))
  exact htri u hu
    ⟨tr _ _ _ (hall _ m₁) (hpair 0 1 _ (by decide) (hsub _ _ h₀₁)),
     tr _ _ _ (hall _ m₂) (hpair 1 2 _ (by decide) (hsub _ _ h₁₂)),
     tr _ _ _ (hall _ m₃) (hpair 0 2 _ (by decide) (hsub _ _ h₀₂))⟩

/-- `m` is the least node of `H`. -/
def IsMin (H : PSet Nat) (m : Nat) : Prop := H.mem m ∧ ∀ z, H.mem z → m ≤ z

theorem exists_isMin {H : PSet Nat} : ∀ z, H.mem z → ∃ m, IsMin H m := by
  intro z
  induction z using Nat.strongRecOn with
  | ind z ih =>
    intro hz
    by_cases h : ∃ w, H.mem w ∧ w < z
    · obtain ⟨w, hw, hlt⟩ := h
      exact ih w hlt hw
    · exact ⟨z, hz, fun w hw => Nat.le_of_not_lt fun hlt => h ⟨w, hw, hlt⟩⟩

theorem isMin_unique {H : PSet Nat} {m m' : Nat} (h : IsMin H m) (h' : IsMin H m') : m = m' :=
  Nat.le_antisymm (h.2 _ h'.1) (h'.2 _ h.1)

/-- Spanning trees with parents smaller than children. -/
def tree : Spec (ExtInp (netAdm (id : Nat → Nat))) (PSet (Nat × Nat)) where
  S H K := (∀ x y, K.mem (x, y) → H.set.mem x ∧ H.set.mem y ∧ y < x) ∧
    (∀ x y y', K.mem (x, y) → K.mem (x, y') → y = y') ∧
    (∀ x z, H.set.mem x → H.set.mem z → z < x → ∃ y, K.mem (x, y))
  total H := ⟨⟨fun p => H.set.mem p.1 ∧ IsMin H.set p.2 ∧ p.2 < p.1⟩,
    fun _ _ h => ⟨h.1, h.2.1.1, h.2.2⟩,
    fun _ _ _ h h' => isMin_unique h.2.1 h'.2.1,
    fun _ z hx hz hlt =>
      let ⟨m, hm⟩ := exists_isMin z hz
      ⟨m, hx, hm, Nat.lt_of_le_of_lt (hm.2 z hz) hlt⟩⟩

theorem tree_nodeMono : NodeMono id tree := by
  intro H₁ H₂ hd K₁ K₂ ⟨l₁, u₁, e₁⟩ ⟨l₂, u₂, e₂⟩
  have hd' : ∀ x, H₁.mem x → H₂.mem x → False := fun x a b => hd x ⟨x, a, rfl⟩ ⟨x, b, rfl⟩
  let K : PSet (Nat × Nat) := ⟨fun p => K₁.mem p ∨ K₂.mem p ∨
    (H₁.mem p.1 ∧ (∀ z, H₁.mem z → ¬ z < p.1) ∧ IsMin H₂ p.2 ∧ p.2 < p.1) ∨
    (H₂.mem p.1 ∧ (∀ z, H₂.mem z → ¬ z < p.1) ∧ IsMin H₁ p.2 ∧ p.2 < p.1)⟩
  refine ⟨K, ⟨?_, ?_, ?_⟩, fun _ h => Or.inl h, fun _ h => Or.inr (Or.inl h)⟩
  · intro x y h
    rcases h with h | h | ⟨a, _, m, lt⟩ | ⟨a, _, m, lt⟩
    · exact ⟨Or.inl (l₁ _ _ h).1, Or.inl (l₁ _ _ h).2.1, (l₁ _ _ h).2.2⟩
    · exact ⟨Or.inr (l₂ _ _ h).1, Or.inr (l₂ _ _ h).2.1, (l₂ _ _ h).2.2⟩
    · exact ⟨Or.inl a, Or.inr m.1, lt⟩
    · exact ⟨Or.inr a, Or.inl m.1, lt⟩
  · intro x y y' h h'
    rcases h with h | h | ⟨a1, n1, m1, _⟩ | ⟨a2, n2, m2, _⟩ <;>
      rcases h' with h' | h' | ⟨a1', n1', m1', _⟩ | ⟨a2', n2', m2', _⟩
    · exact u₁ _ _ _ h h'
    · exact (hd' x (l₁ _ _ h).1 (l₂ _ _ h').1).elim
    · exact (n1' y (l₁ _ _ h).2.1 (l₁ _ _ h).2.2).elim
    · exact (hd' x (l₁ _ _ h).1 a2').elim
    · exact (hd' x (l₁ _ _ h').1 (l₂ _ _ h).1).elim
    · exact u₂ _ _ _ h h'
    · exact (hd' x a1' (l₂ _ _ h).1).elim
    · exact (n2' y (l₂ _ _ h).2.1 (l₂ _ _ h).2.2).elim
    · exact (n1 y' (l₁ _ _ h').2.1 (l₁ _ _ h').2.2).elim
    · exact (hd' x a1 (l₂ _ _ h').1).elim
    · exact isMin_unique m1 m1'
    · exact (hd' x a1 a2').elim
    · exact (hd' x (l₁ _ _ h').1 a2).elim
    · exact (n2 y' (l₂ _ _ h').2.1 (l₂ _ _ h').2.2).elim
    · exact (hd' x a1' a2).elim
    · exact isMin_unique m2 m2'
  · intro x z hx hz hlt
    rcases hx with hx | hx
    · by_cases hs : ∃ w, H₁.mem w ∧ w < x
      · obtain ⟨w, hw, hwx⟩ := hs
        obtain ⟨y, hy⟩ := e₁ x w hx hw hwx
        exact ⟨y, Or.inl hy⟩
      · rcases hz with hz | hz
        · exact (hs ⟨z, hz, hlt⟩).elim
        · obtain ⟨m, hm⟩ := exists_isMin z hz
          exact ⟨m, Or.inr (Or.inr (Or.inl ⟨hx, fun w hw hwx => hs ⟨w, hw, hwx⟩, hm,
            Nat.lt_of_le_of_lt (hm.2 z hz) hlt⟩))⟩
    · by_cases hs : ∃ w, H₂.mem w ∧ w < x
      · obtain ⟨w, hw, hwx⟩ := hs
        obtain ⟨y, hy⟩ := e₂ x w hx hw hwx
        exact ⟨y, Or.inr (Or.inl hy)⟩
      · rcases hz with hz | hz
        · obtain ⟨m, hm⟩ := exists_isMin z hz
          exact ⟨m, Or.inr (Or.inr (Or.inr ⟨hx, fun w hw hwx => hs ⟨w, hw, hwx⟩, hm,
            Nat.lt_of_le_of_lt (hm.2 z hz) hlt⟩))⟩
        · exact (hs ⟨z, hz, hlt⟩).elim

theorem tree_pair : ∀ a b K, a ≠ b → tree.S (net fun x => x = a ∨ x = b) K → Adj K a b := by
  intro a b K hab ⟨l, _, e⟩
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · obtain ⟨y, hy⟩ := e b a (Or.inr rfl) (Or.inl rfl) h
    have := l _ _ hy
    simp only [net] at this
    have hy' : y = a := by omega
    exact Or.inr (hy' ▸ hy)
  · obtain ⟨y, hy⟩ := e a b (Or.inl rfl) (Or.inr rfl) h
    have := l _ _ hy
    simp only [net] at this
    have hy' : y = b := by omega
    exact Or.inl (hy' ▸ hy)

theorem tree_triangle : ∀ K, tree.S (net fun x => x = 0 ∨ x = 1 ∨ x = 2) K →
    ¬ (Adj K 0 1 ∧ Adj K 1 2 ∧ Adj K 0 2) := by
  intro K ⟨l, u, _⟩ ⟨_, h12, h02⟩
  have h21 : K.mem (2, 1) := h12.elim (fun h => absurd (l _ _ h).2.2 (by decide)) id
  have h20 : K.mem (2, 0) := h02.elim (fun h => absurd (l _ _ h).2.2 (by decide)) id
  exact absurd (u _ _ _ h21 h20) (by decide)

theorem tree_no_consistentOn (A : Table (ExtInp (netAdm (id : Nat → Nat))) (PSet (Nat × Nat)))
    (hA : ∀ H, ∃ K, A H K) (hsub : ∀ H K, A H K → tree.S H K) : ¬ CAP.ConsistentOn tree A :=
  no_consistentOn_of_triangle tree tree_pair tree_triangle A hA hsub

end Tree

end QRef
end CC
