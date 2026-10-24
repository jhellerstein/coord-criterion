import CoordCriterion.Instances.InvariantConfluence

/-!
# Bailis et al.'s definition of invariant confluence (Section `sec:iconfluence-instance`)

Bailis et al. (VLDB 2015), Def. 5 (I-T-reachability) and Def. 6
(I-confluence over states with a common ancestor) are equivalent to
`CC.IConf.Model.IConfluent`, the reading used in
`Instances/InvariantConfluence.lean`: `ReachFrom`, `bailis_iff`, `Anc`,
`s0_anc`, `bailisAnc_iff`, `reachPlus_iff`.
-/

namespace CC
namespace IConf

open Classical

/-! ## 5. Sec. `sec:iconfluence-instance`: Bailis et al.'s definition

Bailis et al. (VLDB 2015), Def. 5: a state is *I-T-reachable* from a state
`a` when some partially ordered sequence of transaction and merge invocations
starting from `a` yields it, every intermediate state being I-valid; Def. 6:
`T` is *I-confluent* when `Dᵢ ⊔ Dⱼ` is I-valid for all I-T-reachable states
`Dᵢ, Dⱼ` with a common ancestor state.  We formalize two readings of
"common ancestor" and show that both are `CC.IConf.Model.IConfluent`
("every reachable state descends from `s0`"). -/


variable {V Tx : Type} {M : Model V Tx}

/-- Bailis et al., Def. 5: I-T-reachability from `a`. -/
inductive ReachFrom (M : Model V Tx) (a : St V) : St V → Prop where
  | base : ReachFrom M a a
  | tx {s : St V} (t : Tx) : ReachFrom M a s → M.Inv (M.app t s) → ReachFrom M a (M.app t s)
  | merge {s₁ s₂ : St V} : ReachFrom M a s₁ → ReachFrom M a s₂ → M.Inv (s₁.union s₂) →
      ReachFrom M a (s₁.union s₂)

theorem reach_iff_from (s : St V) : IConf.Reach M s ↔ ReachFrom M M.s0 s := by
  constructor
  · intro h
    induction h with
    | init => exact .base
    | tx t _ hi ih => exact .tx t ih hi
    | merge _ _ hi ih1 ih2 => exact .merge ih1 ih2 hi
  · intro h
    induction h with
    | base => exact .init
    | tx t _ hi ih => exact .tx t ih hi
    | merge _ _ hi ih1 ih2 => exact .merge ih1 ih2 hi

/-- States reachable from a reachable state are reachable. -/
theorem reach_of_from {a s : St V} (ha : IConf.Reach M a) (h : ReachFrom M a s) : IConf.Reach M s := by
  induction h with
  | base => exact ha
  | tx t _ hi ih => exact .tx t ih hi
  | merge _ _ hi ih1 ih2 => exact .merge ih1 ih2 hi

/-- Def. 6, read with an explicit common ancestor state `a` (itself reachable
or initial): the merge of any two states I-T-reachable from `a` is I-valid. -/
def BailisIC (M : Model V Tx) : Prop :=
  ∀ a, IConf.Reach M a → ∀ s₁ s₂, ReachFrom M a s₁ → ReachFrom M a s₂ → M.Inv (s₁.union s₂)

theorem bailis_iff : BailisIC M ↔ M.IConfluent := by
  constructor
  · intro h s₁ s₂ h₁ h₂
    exact h M.s0 .init s₁ s₂ ((reach_iff_from _).1 h₁) ((reach_iff_from _).1 h₂)
  · intro h a ha s₁ s₂ h₁ h₂
    exact h s₁ s₂ (reach_of_from ha h₁) (reach_of_from ha h₂)

/-- `Anc a s`: `a` is an ancestor state of `s`, i.e. a state preceding `s` in
some derivation of `s` from `s0` by at least one invocation. -/
inductive Anc (M : Model V Tx) : St V → St V → Prop where
  | txParent {s : St V} (t : Tx) : IConf.Reach M s → M.Inv (M.app t s) → Anc M s (M.app t s)
  | tx {a s : St V} (t : Tx) : Anc M a s → M.Inv (M.app t s) → Anc M a (M.app t s)
  | mergeParentL {s₁ s₂ : St V} : IConf.Reach M s₁ → IConf.Reach M s₂ → M.Inv (s₁.union s₂) →
      Anc M s₁ (s₁.union s₂)
  | mergeParentR {s₁ s₂ : St V} : IConf.Reach M s₁ → IConf.Reach M s₂ → M.Inv (s₁.union s₂) →
      Anc M s₂ (s₁.union s₂)
  | mergeL {a s₁ s₂ : St V} : Anc M a s₁ → IConf.Reach M s₂ → M.Inv (s₁.union s₂) →
      Anc M a (s₁.union s₂)
  | mergeR {a s₁ s₂ : St V} : IConf.Reach M s₁ → Anc M a s₂ → M.Inv (s₁.union s₂) →
      Anc M a (s₁.union s₂)

theorem Anc.reach {a s : St V} (h : Anc M a s) : IConf.Reach M s ∧ IConf.Reach M a := by
  induction h with
  | txParent t hs hi => exact ⟨.tx t hs hi, hs⟩
  | tx t _ hi ih => exact ⟨.tx t ih.1 hi, ih.2⟩
  | mergeParentL h1 h2 hi => exact ⟨.merge h1 h2 hi, h1⟩
  | mergeParentR h1 h2 hi => exact ⟨.merge h1 h2 hi, h2⟩
  | mergeL _ h2 hi ih => exact ⟨.merge ih.1 h2 hi, ih.2⟩
  | mergeR h1 _ hi ih => exact ⟨.merge h1 ih.1 hi, ih.2⟩

theorem union_self (s : St V) : s.union s = s :=
  funext fun _ => propext ⟨fun h => h.elim id id, Or.inl⟩

/-- Every reachable state descends from `s0` (also `s0` itself, as
`s0 ⊔ s0`): `s0` is an ancestor of every reachable state. -/
theorem s0_anc {s : St V} (h : IConf.Reach M s) : Anc M M.s0 s := by
  induction h with
  | init =>
    have := Anc.mergeParentL (M := M) IConf.Reach.init IConf.Reach.init (by rw [union_self]; exact M.init)
    rwa [union_self] at this
  | tx t _ hi ih => exact .tx t ih hi
  | merge _ h2 hi ih1 _ => exact .mergeL ih1 h2 hi

/-- Def. 6, read literally: I-T-reachable states (by at least one invocation)
with a common ancestor state.  The reachability of `Dᵢ, Dⱼ` is implied by
`Anc`. -/
def BailisAnc (M : Model V Tx) : Prop :=
  ∀ a s₁ s₂, Anc M a s₁ → Anc M a s₂ → M.Inv (s₁.union s₂)

theorem bailisAnc_iff : BailisAnc M ↔ M.IConfluent := by
  constructor
  · intro h s₁ s₂ h₁ h₂
    exact h M.s0 s₁ s₂ (s0_anc h₁) (s0_anc h₂)
  · intro h a s₁ s₂ h₁ h₂
    exact h s₁ s₂ h₁.reach.1 h₂.reach.1

/-- The states I-T-reachable from `s0` by at least one invocation are exactly
the reachable states. -/
theorem reachPlus_iff (s : St V) : (∃ a, Anc M a s) ↔ IConf.Reach M s :=
  ⟨fun ⟨_, h⟩ => h.reach.1, fun h => ⟨_, s0_anc h⟩⟩


end IConf
end CC
