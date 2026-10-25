import CoordCriterion.Instances.Examples

/-!
# Paper App. D, "Proofs and Details for Composition" (`appendices/composition.tex`)

Statement layer for Appendix `app:composition`.  The results it proves are
stated in Section `sec:composition` and recorded in
`Paper/S5_Composition.lean`; this file holds what appears only in the
appendix: composition with independent inputs and its curried evaluation, the
counterexample to the converse of Corollary `cor:monotone-commitment`, and
Example `ex:bare-reads`.  The parameterized forms of Definition
`def:proper-coordination` and Corollaries `thm:proper-coordination` and
`cor:monotone-commitment` are the second conjuncts of the entries in
`Paper/S5_Composition.lean`.
Unlabeled claims are `«app:composition/<slug>»`.

Library: `Appendix/Composition.lean` (namespace `CC.Comp`) and the examples
at the end of `Instances/Examples.lean` (namespace `CC.Inst`).  Conventions
as in `Paper/S5_Composition.lean`.
-/

namespace CC
namespace Paper

open CC.Comp (Monotone graph)

/-! ## Sequential composition -/


/-- **Corollary `cor:functional-composition`** (Functional composition): "If
`f : (I,≼_I) → (M,≼_M)` and `g : (M,≼_M) → (O,≼_O)` are monotone, so is
`g ∘ f`."  (Proved in the library through tables of functions and
Lemma `lem:composition`, as in the paper.) -/
theorem «cor:functional-composition» {I M O : Type} [PO I] [PO M] [PO O] {f : I → M} {g : M → O}
    (hf : Monotone f) (hg : Monotone g) : Monotone (g ∘ f) :=
  Comp.functional_composition hf hg

/-! ## Composition with independent inputs (`sec:parameterized-composition`) -/

/-- Eq. `eq:parameterized-composition`:
`G ⋆ F = π_{I,J,A,C}(F ⋈_B G) = {((i,j,a),c) : ∃ b. ((i,a),b) ∈ F ∧ ((j,b),c) ∈ G}`,
"with the product order on `I × J × A`.  Since `F` is total on `I × A` and `G`
is total on `J × B`, every composed input has a nonempty fiber."  Lean: the
composed input `(i,j,a)` is `(i,(j,a))`; `Comp.par F G` is the specification
with table `ptable`. -/
theorem «eq:parameterized-composition» {I J A B C : Type} [PO I] [PO J] [PO A] [PO B] [PO C]
    (F : Spec (I × A) B) (G : Spec (J × B) C) :
    (∀ (i : I) (j : J) (a : A) (c : C),
        (Comp.par F G).S (i, (j, a)) c ↔ ∃ b, F.S (i, a) b ∧ G.S (j, b) c) ∧
      ∀ x, ∃ c, (Comp.par F G).S x c :=
  ⟨fun _ _ _ _ => Iff.rfl, (Comp.par F G).total⟩

/-- **Lemma `lem:parameterized-composition`** (Independently parameterized
composition): "If `Spec_F` and `Spec_G` satisfy Lifted Monotonicity, then the
specification with table `G ⋆ F` satisfies Lifted Monotonicity." -/
theorem «lem:parameterized-composition» {I J A B C : Type} [PO I] [PO J] [PO A] [PO B] [PO C]
    {F : Spec (I × A) B} {G : Spec (J × B) C} (hF : F.LiftedMono) (hG : G.LiftedMono) :
    (Comp.par F G).LiftedMono :=
  Comp.par_liftedMono hF hG

/-! ### Curried evaluation -/

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

/-! ## Proper Coordination -/

/-- "Definition `def:proper-coordination` and Corollaries
`thm:proper-coordination` and `cor:monotone-commitment` apply to independently
parameterized composition, with `F` in place of `S₁`, `G` in place of `S₂`, and
`G ⋆ K` as the resolved table."  Lean: `Comp.ProperPar κ G` is `Comp.Proper`
on `G ⋆ K`; the two corollaries in parameterized form. -/
theorem «app:composition/parameterized-proper» {I J A B C : Type} [PO I] [PO J] [PO A] [PO B]
    [PO C] {F : Spec (I × A) B} (κ : Comp.CommitTable F) (G : Spec (J × B) C) :
    (Comp.ProperPar κ G ↔ Comp.Proper (Comp.par κ.spec G)) ∧
      (Comp.ProperPar κ G ↔ (Comp.par κ.spec G).LiftedMono) ∧
      ∀ f : I × A → B, κ.K = (graph f).S → Monotone f → G.LiftedMono → Comp.ProperPar κ G :=
  ⟨Iff.rfl, Comp.proper_coordination_par κ G,
    fun f hK hf hG => Comp.monotone_commitment_par κ G f hK hf hG⟩

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

/-- **Example `ex:bare-reads`** (Bare reads), position-tagged responses, for
any deterministic state machine `δ`, read function `rd`, and two distinct
commands: "As in Example `ex:committed-log-composition`, `F` and `G ⋆ F` are
non-monotone, and `K` is the table of a monotone function. … A longer log
never contradicts such a response, so `G` is monotone and bare reads need no
coordination.  By Corollary `cor:monotone-commitment` the log commitments are
proper, and `G ⋆ K` is consistent."  Lean: `I = B = Inst.Pfx Cmd`,
`A = Comp.Pt`, `J = Inst.Pfx Rd`; `logF`, `logK` (`K(i) = i`), `bareG δ rd σ₀`,
whose outputs pair the executed response log with a set (`Inst.Facts`) of
tagged responses `(r, n, v)`, `v` the value `rd` gives after the first `n ≤ |b|`
entries.  "Responses are facts, so a set of them may answer one read more than
once." -/
theorem «ex:bare-reads» {Cmd Stt R Rd V : Type} (δ : Stt → Cmd → Stt × R) (rd : Stt → Rd → V)
    (σ0 : Stt) {c₁ c₂ : Cmd} (hne : c₁ ≠ c₂) :
    ¬ (Inst.logF (Cmd := Cmd)).LiftedMono ∧
      ¬ (Comp.par Inst.logF (Inst.bareG δ rd σ0)).LiftedMono ∧
      (Inst.logK (Cmd := Cmd)).K = (graph fun p : Inst.Pfx Cmd × Comp.Pt => p.1).S ∧
      Monotone (fun p : Inst.Pfx Cmd × Comp.Pt => p.1) ∧ (Inst.bareG δ rd σ0).LiftedMono ∧
      Comp.ProperPar Inst.logK (Inst.bareG δ rd σ0) ∧
      (Comp.par Inst.logK.spec (Inst.bareG δ rd σ0)).Consistent :=
  Inst.bare_read_example δ rd σ0 hne

/-- Inside Example `ex:bare-reads`: "Suppose instead that the specification
demands the latest value, so that a read of `x` must return the value of `x`
after all of `b`.  Then a bare read can be contradicted by an entry it has not
seen, `G` is not monotone, and neither is `G ⋆ K`."  Lean: `latestG δ rd σ₀`
(untagged responses `(r, v)`, `v` the value after all of `b`); "an entry it has
not seen" is a command `c` that changes what read `r` returns.  Not being
monotone, `G ⋆ K` is not proper (Corollary `thm:proper-coordination`). -/
theorem «ex:bare-reads/latest-value» {Cmd Stt R Rd V : Type} (δ : Stt → Cmd → Stt × R)
    (rd : Stt → Rd → V) (σ0 : Stt) {c : Cmd} {r : Rd} (hc : rd (δ σ0 c).1 r ≠ rd σ0 r) :
    ¬ (Inst.latestG δ rd σ0).LiftedMono ∧
      ¬ (Comp.par Inst.logK.spec (Inst.latestG δ rd σ0)).LiftedMono ∧
      ¬ Comp.ProperPar Inst.logK (Inst.latestG δ rd σ0) :=
  ⟨Inst.latestG_not_liftedMono δ rd σ0 hc, Inst.latest_not_proper δ rd σ0 hc⟩

end Paper
end CC
