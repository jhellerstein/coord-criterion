import CoordCriterion.Instances.Examples

/-!
# Paper App. D, "Proofs and Details for Composition" (`appendices/composition.tex`)

Statement layer for Appendix `app:composition`.  The results it proves are
stated in Section `sec:composition` and recorded in
`Paper/S5_Composition.lean`; this file holds what appears only in the
appendix: the curried evaluation of independently parameterized composition
and the counterexample to the converse of Corollary `cor:monotone-commitment`.
Unlabeled claims are `«app:composition/<slug>»`.

Library: `Appendix/Composition.lean` (namespace `CC.Comp`) and the examples
at the end of `Instances/Examples.lean` (namespace `CC.Inst`).  Conventions
as in `Paper/S5_Composition.lean`.
-/

namespace CC
namespace Paper

open CC.Comp (Monotone graph)

/-! ## Curried evaluation -/


/-- **Corollary `cor:functional-composition`** (Functional composition): "If
`f : (I,≼_I) → (M,≼_M)` and `g : (M,≼_M) → (O,≼_O)` are monotone, so is
`g ∘ f`."  (Proved in the library through tables of functions and
Lemma `lem:composition`, as in the paper.) -/
theorem «cor:functional-composition» {I M O : Type} [PO I] [PO M] [PO O] {f : I → M} {g : M → O}
    (hf : Monotone f) (hg : Monotone g) : Monotone (g ∘ f) :=
  Comp.functional_composition hf hg

/-- Eq. `eq:curried-fibers`: `F_i = π_{A,B}(F[I=i])`, `G_j = π_{B,C}(G[J=j])`. -/
theorem «eq:curried-fibers» {I J A B C : Type} (F : Table (I × A) B) (G : Table (J × B) C)
    (i : I) (j : J) (a : A) (b : B) (c : C) :
    (Comp.fiberF F i a b ↔ F (i, a) b) ∧ (Comp.fiberG G j b c ↔ G (j, b) c) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- Eq. `eq:curried-query-plan`:
`⋃_{(i,j) ∈ I×J} {((i,j,a),c) : (a,c) ∈ π_{A,C}(F_i ⋈_B G_j)}`. -/
theorem «eq:curried-query-plan» {I J A B C : Type} (F : Table (I × A) B) (G : Table (J × B) C)
    (x : I × (J × A)) (c : C) :
    Comp.curriedPlan F G x c ↔
      ∃ p : I × J, x.1 = p.1 ∧ x.2.1 = p.2 ∧
        Comp.tcomp (Comp.fiberF F p.1) (Comp.fiberG G p.2) x.2.2 c :=
  Iff.rfl

/-- **Proposition `prop:curried-query-plan`** (Curried equijoin plan): "The
table in Equation `eq:parameterized-composition` equals
[Eq. `eq:curried-query-plan`]." -/
theorem «prop:curried-query-plan» {I J A B C : Type} (F : Table (I × A) B) (G : Table (J × B) C) :
    Comp.ptable F G = Comp.curriedPlan F G :=
  Comp.curried_query_plan F G

/-- Eq. `eq:curried-composition`: "For monotone `f : I × A → B` and
`g : J × B → C`, the instance of
Lemma `lem:parameterized-composition` for their tables says that `h(i,j,a) = g(j, f(i,a))`
is monotone; in curried form, `h^♯(i,j) = g^♯(j) ∘ f^♯(i)`, which is the plan
of Proposition `prop:curried-query-plan` on tables of functions."  Lean: (1) `G ⋆ F`
of tables of functions is the table of `h`; (2) `h` is monotone; (3) the curried
form; (4) the curried plan of the two tables of functions is the table of `h`. -/
theorem «eq:curried-composition» {I J A B C : Type} [PO I] [PO J] [PO A] [PO B] [PO C]
    (f : I × A → B) (g : J × B → C) :
    Comp.par (graph f) (graph g) = graph (fun x : I × (J × A) => g (x.2.1, f (x.1, x.2.2))) ∧
      (Monotone f → Monotone g → Monotone (fun x : I × (J × A) => g (x.2.1, f (x.1, x.2.2)))) ∧
      (∀ i j, (fun a => g (j, f (i, a))) = (fun b => g (j, b)) ∘ (fun a => f (i, a))) ∧
      Comp.curriedPlan (graph f).S (graph g).S =
        (graph (fun x : I × (J × A) => g (x.2.1, f (x.1, x.2.2)))).S :=
  ⟨Comp.parameterized_graph f g, fun hf hg => Comp.parameterized_functional_composition hf hg,
    Inst.curried_sharp f g, Inst.curried_plan_graph f g⟩

/-! ## The converse of Corollary `cor:monotone-commitment` -/

/-- "The converse of Corollary `cor:monotone-commitment` fails: let `I = {*}`, `M = {x,y}` discrete,
`S₁ = {(*,x),(*,y)}`, `K = {(*,x)}`, and `S₂ = {(x,x),(y,x),(y,y)}`.  The fiber
`S₂(y) = {x,y}` is not directed, so `S₂` fails Lifted Monotonicity and the
corollary does not apply, but the resolved table `{(*,x)}` is monotone, so the
strategy is proper."  Lean: `anyS`, `kappaX`, `s2NM`; `¬ JointLift (S₂ y) (S₂ y)`
says the fiber `S₂(y)` is not directed. -/
theorem «app:composition/converse-example» :
    (∀ p m, Comp.anyS.S p m) ∧ (∀ p m, Comp.kappaX.K p m ↔ m = Comp.Two.x) ∧
      (∀ m o, Comp.s2NM.S m o ↔
        (m = .x ∧ o = .x) ∨ (m = .y ∧ o = .x) ∨ (m = .y ∧ o = .y)) ∧
      (∀ p o, (Comp.seq Comp.kappaX.spec Comp.s2NM).S p o ↔ o = Comp.Two.x) ∧
      ¬ JointLift (Comp.s2NM.S .y) (Comp.s2NM.S .y) ∧
      ¬ Comp.anyS.LiftedMono ∧ ¬ Comp.s2NM.LiftedMono ∧
      ¬ (Comp.seq Comp.anyS Comp.s2NM).LiftedMono ∧
      Comp.ProperSeq Comp.kappaX Comp.s2NM :=
  Inst.converse_example

end Paper
end CC
