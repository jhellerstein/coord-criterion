import CoordCriterion.Appendix.Composition

/-!
# Intersection of specifications (Section 5, `sec:intersection`)

Namespace `CC.Inter`.  Two specifications with the same ordered input and
output domains intersect: the intersection permits the rows that both permit.

* `inter`               — Def. `def:intersection` (the table `P₁ ∩ P₂`, given totality)
* `not_closed`         — Lifted Monotonicity is not closed under intersection
* `inter_liftedMono_of_bound` — Prop. `prop:intersection-bound`: a monotone bound
  that both specifications permit makes the intersection monotone
-/

namespace CC
namespace Inter

open CC.Comp (Monotone)

section
variable {I O : Type} [PO I] [PO O]

/-- The intersection of two specifications over the same ordered domains, when
the intersection of their tables is total. -/
def inter (s₁ s₂ : Spec I O) (htot : ∀ i, ∃ o, s₁.P i o ∧ s₂.P i o) : Spec I O where
  P i o := s₁.P i o ∧ s₂.P i o
  total := htot

/-- **Prop. `prop:intersection-bound`.**  Let `g` be monotone.  If every output
`s₁` permits at `j` lies below `g j`, and both specifications permit `g j` at
every `j`, the intersection is a specification and satisfies Lifted
Monotonicity. -/
theorem inter_liftedMono_of_bound (s₁ s₂ : Spec I O) (g : I → O) (hg : Monotone g)
    (hb : ∀ j o, s₁.P j o → o ≼ g j) (h₁ : ∀ j, s₁.P j (g j)) (h₂ : ∀ j, s₂.P j (g j)) :
    (inter s₁ s₂ fun j => ⟨g j, h₁ j, h₂ j⟩).LiftedMono := by
  intro i j hij X _ hX
  exact ⟨g j, ⟨h₁ j, h₂ j⟩, fun x hx => PO.trans (hb i x (hX x hx).1) (hg i j hij)⟩

end

/-! ## Lifted Monotonicity is not closed under intersection -/

/-- Four outputs: `a` and `b` incomparable, both below `c` and below `d`;
`c` and `d` incomparable. -/
inductive Q4 where
  | a | b | c | d
  deriving DecidableEq

/-- `x ≼ y` when `x = y`, or `x ∈ {a, b}` and `y ∈ {c, d}`. -/
def Q4.le : Q4 → Q4 → Prop
  | .a, .a | .b, .b | .c, .c | .d, .d => True
  | .a, .c | .a, .d | .b, .c | .b, .d => True
  | _, _ => False

instance : PO Q4 where
  le := Q4.le
  refl x := by cases x <;> trivial
  trans {x y z} h h' := by cases x <;> cases y <;> cases z <;> simp_all [Q4.le]
  antisymm {x y} h h' := by cases x <;> cases y <;> simp_all [Q4.le]

/-- The one-point input domain. -/
instance : PO Unit where
  le _ _ := True
  refl _ := trivial
  trans _ _ := trivial
  antisymm {a b} _ _ := by cases a; cases b; rfl

/-- First specification: the fiber `{a, b, c}`. -/
def sC : Spec Unit Q4 where
  P _ o := o ≠ .d
  total _ := ⟨.c, by decide⟩

/-- Second specification: the fiber `{a, b, d}`. -/
def sD : Spec Unit Q4 where
  P _ o := o ≠ .c
  total _ := ⟨.d, by decide⟩

theorem q4_below (o u : Q4) (hu : u = .c ∨ u = .d) (ho : o = .a ∨ o = .b ∨ o = u) : o ≼ u := by
  rcases hu with rfl | rfl <;> rcases ho with rfl | rfl | h <;> (try subst h) <;> trivial

/-- **Lifted Monotonicity is not closed under intersection.**  `sC` and `sD`
satisfy Lifted Monotonicity (`c` and `d` bound their fibers), but their
intersection has the fiber `{a, b}`, and `a` and `b` have no common output
extension in it. -/
theorem not_closed :
    sC.LiftedMono ∧ sD.LiftedMono ∧
      ∀ htot, ¬ (inter sC sD htot).LiftedMono := by
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ _ X _ hX
    refine ⟨.c, (by decide : (Q4.c ≠ .d)), fun x hx => ?_⟩
    have h := hX x hx
    cases x <;> first | trivial | exact absurd rfl h
  · intro _ _ _ X _ hX
    refine ⟨.d, (by decide : (Q4.d ≠ .c)), fun x hx => ?_⟩
    have h := hX x hx
    cases x <;> first | trivial | exact absurd rfl h
  · intro htot h
    obtain ⟨u, ⟨hu₁, hu₂⟩, hall⟩ := h () () trivial [.a, .b] (by simp)
      (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> exact ⟨(by decide : _ ≠ Q4.d), (by decide : _ ≠ Q4.c)⟩)
    have ha := hall .a (by simp)
    have hb := hall .b (by simp)
    cases u <;> simp_all [PO.le, Q4.le, sC, sD]

/-- The intersection of `sC` and `sD` is total: `a` is in both fibers. -/
theorem sCD_total : ∀ i, ∃ o, sC.P i o ∧ sD.P i o :=
  fun _ => ⟨.a, (by decide : Q4.a ≠ .d), (by decide : Q4.a ≠ .c)⟩

end Inter
end CC
