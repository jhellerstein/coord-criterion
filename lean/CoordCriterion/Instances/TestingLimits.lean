import CoordCriterion.Appendix.Frontiers
import CoordCriterion.CompleteCALM.Theorem

/-!
# Testing cannot show Lifted Monotonicity (§6.5, "Testing and proof")

Supports the sentence "Testing cannot show that Lifted Monotonicity holds,
since that is a claim about every input."

Testing explores finitely many inputs and records their fibers.  We show that
no finite set of explored inputs suffices: for every finite set `X` of inputs
of a chain of inputs, the spec `base` (one output at every input, Lifted
Monotone) and the spec `spoil X` agree on the fiber at every input of `X`, yet
`spoil X` fails Lifted Monotonicity, at an input outside `X`.

Modeling choices: inputs are stages `0 ≤ 1 ≤ 2 ≤ …` (`Stage`), outputs two
incomparable values (`Front.Disc Bool`); `base` permits only `false`;
`spoil X` permits both values at the stage `bound X` above every stage of `X`.
A finite set of explored inputs is a list.
-/

namespace CC
namespace Testing

open CC.Front (Disc)

/-- Inputs: stages ordered by `≤`. -/
structure Stage where
  n : Nat

instance : PO Stage where
  le a b := a.n ≤ b.n
  refl _ := Nat.le_refl _
  trans h₁ h₂ := Nat.le_trans h₁ h₂
  antisymm {a b} h₁ h₂ := by
    cases a; cases b; simp only [Stage.mk.injEq]; exact Nat.le_antisymm h₁ h₂

/-- One output, `false`, at every input. -/
def base : Spec Stage (Disc Bool) where
  P _ o := o = ⟨false⟩
  total _ := ⟨⟨false⟩, rfl⟩

/-- A stage above every stage of `X`. -/
def bound (X : List Stage) : Stage := ⟨(X.map Stage.n).foldr max 0 + 1⟩

theorem lt_bound (X : List Stage) : ∀ s ∈ X, s.n < (bound X).n := by
  intro s hs
  show s.n < (X.map Stage.n).foldr max 0 + 1
  have : ∀ (l : List Nat), ∀ m ∈ l, m ≤ l.foldr max 0 := by
    intro l
    induction l with
    | nil => intro m h; cases h
    | cons a l ih =>
      intro m h
      rcases List.mem_cons.1 h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih m h) (Nat.le_max_right _ _)
  exact Nat.lt_succ_of_le (this _ s.n (List.mem_map_of_mem hs))

/-- `base`, except that both outputs are permitted at `bound X`. -/
def spoil (X : List Stage) : Spec Stage (Disc Bool) where
  P i o := o = ⟨false⟩ ∨ i = bound X
  total _ := ⟨⟨false⟩, Or.inl rfl⟩

theorem base_liftedMono : base.LiftedMono := by
  intro i j _ Xs _ hX
  exact ⟨⟨false⟩, rfl, fun x hx => (hX x hx).symm ▸ rfl⟩

/-- **Testing cannot show Lifted Monotonicity.**  For every finite set `X` of
explored inputs, `base` and `spoil X` have the same fiber at every input of
`X`; `base` satisfies Lifted Monotonicity and `spoil X` does not. -/
theorem testing_cannot_show (X : List Stage) :
    (∀ s ∈ X, ∀ o, base.P s o ↔ (spoil X).P s o) ∧ base.LiftedMono ∧
      ¬ (spoil X).LiftedMono := by
  refine ⟨fun s hs o => ?_, base_liftedMono, ?_⟩
  · have hne : s ≠ bound X := by
      intro h; have := lt_bound X s hs; rw [h] at this; exact Nat.lt_irrefl _ this
    exact ⟨Or.inl, fun h => h.resolve_right hne⟩
  · intro h
    obtain ⟨u, _, hall⟩ := h (bound X) (bound X) (PO.refl _) [⟨false⟩, ⟨true⟩]
      (by simp) (fun _ _ => Or.inr rfl)
    have h1 : (⟨false⟩ : Disc Bool) = u := hall _ (by simp)
    have h2 : (⟨true⟩ : Disc Bool) = u := hall _ (by simp)
    have := h1.trans h2.symm
    cases this

end Testing
end CC
