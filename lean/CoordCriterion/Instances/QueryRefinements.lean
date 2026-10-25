import CoordCriterion.CALM.Examples
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
* Behaviors (Baccaert and Ketsman, PODS 2023).  Inputs are located facts,
  ordered by network expansion (new facts only at new nodes, `netAdm`), and a
  behavior is a relational specification on them.  Node monotonicity
  (`NodeMono`) follows from consistency (`nodeMono_of_consistent`) but does
  not imply it: letting each node pick one Boolean gives a node-monotone
  behavior with a non-directed fiber (`pick_nodeMono`, `pick_not_consistent`).
  For functional behaviors the two coincide (`nodeMono_graph_iff`).

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

/-- Node monotonicity (Baccaert–Ketsman Def. 6.2): outputs of two behaviors
on disjoint networks have a common refinement at the merged network. -/
def NodeMono {G : Type} (B : Spec (ExtInp (netAdm loc)) (PSet G)) : Prop :=
  ∀ H₁ H₂ : PSet F, (∀ x, Netw loc H₁ x → ¬ Netw loc H₂ x) →
    ∀ K₁ K₂, B.S ⟨H₁⟩ K₁ → B.S ⟨H₂⟩ K₂ → ∃ K, B.S ⟨union H₁ H₂⟩ K ∧ K₁ ≼ K ∧ K₂ ≼ K

theorem le_union_left {H₁ H₂ : PSet F} (hd : ∀ x, Netw loc H₁ x → ¬ Netw loc H₂ x) :
    (⟨H₁⟩ : ExtInp (netAdm loc)) ≼ ⟨union H₁ H₂⟩ :=
  ⟨fun _ hf => Or.inl hf, fun f hf hn => hf.elim (absurd · hn) fun h2 h1 => hd _ h1 ⟨f, h2, rfl⟩⟩

theorem le_union_right {H₁ H₂ : PSet F} (hd : ∀ x, Netw loc H₁ x → ¬ Netw loc H₂ x) :
    (⟨H₂⟩ : ExtInp (netAdm loc)) ≼ ⟨union H₁ H₂⟩ :=
  ⟨fun _ hf => Or.inr hf, fun f hf hn => hf.elim (fun h1 h2 => hd _ ⟨f, h1, rfl⟩ h2) (absurd · hn)⟩

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

/-! ### Node monotone, not consistent: each node picks a Boolean

Input facts are node names (`Node@x()`), located at themselves.  An output is
a set of located facts `Pick@x(c)`, at nodes of the input, with at most one
pick per node.  Disjoint networks never pick at the same node, so the union of
their outputs is permitted: the behavior is node monotone.  At the one-node
network `{0}`, the outputs `{Pick@0(true)}` and `{Pick@0(false)}` have no
common refinement: the fiber is not directed, so the behavior fails Lifted
Monotonicity and is not consistent. -/

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

end Pick

end QRef
end CC
