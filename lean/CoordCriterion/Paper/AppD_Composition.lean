import CoordCriterion.Appendix.Guarded
import CoordCriterion.Appendix.JointMono

/-!
# Paper App. D, "Proofs and Details for Composition" (`appendices/composition.tex`)

Statement layer for Appendix `app:composition`.  The results it proves are
stated in Section `sec:composition` and recorded in
`Paper/S5_Composition.lean`; this file holds what appears only in the
appendix: composition with independent inputs and its curried evaluation, the
component-commitment example, and the Proper Coordination subsection with its
corollaries, the covering argument, the counterexamples, and Examples
`ex:committed-log-composition` and `ex:bare-reads`.
Unlabeled claims are `«app:composition/<slug>»`.

Library: `Appendix/Composition.lean` (namespace `CC.Comp`), the examples at
the end of `Instances/Examples.lean` (namespace `CC.Inst`), and
`Appendix/Guarded.lean` (namespace `CC.Guard`).  Conventions as in
`Paper/S5_Composition.lean`.
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

/-! ## Jointly monotone composites -/

/-- "If every stage satisfies Lifted Monotonicity and `𝒮₁` runs under the
empty basis, the pipeline emits only what `S₂ ∘ S₁` emits under the empty
basis.  Its runs are runs of a Lifted-Monotone specification, at whose states
every output is exposable (Proposition `prop:exposure-boundary`).  So the next
stage again has an empty-basis guard, and by induction no stage of the
pipeline commits."  Lean: `Guard.pipeline_coordination_free`, via
`Guard.exec_execCF`, for any system of `𝒮₂`. -/
theorem «app:composition/all-monotone» {I M O : Type} [PO I] [PO M] [PO O]
    {sp : Spec I M} {sk : Spec M O} (hP : sp.LiftedMono) (hK : sk.LiftedMono) (K : Guard.Sys sk)
    {l' : List O} (h : Guard.GEmits (Guard.Sys.free (fun _ : Commitment sp => False)).emits K l') :
    (Comp.seq sp sk).LiftedMono ∧
      (Guard.Sys.free (fun _ : Commitment (Comp.seq sp sk) => False)).emits l' :=
  Guard.pipeline_coordination_free hP hK h

/-- Proof of Proposition `prop:joint-monotone`: "(1) is Lemma
`lem:composition`, and also the case `D = M` of (2).  (2) Let `D` contain the
outputs of `𝒮₁`. … All of `m_r` and `m` lie in `D`, so the condition for `𝒮₂`
on `D` gives `o ∈ S₂(m)` that refines every `o_r`, and `(j,o) ∈ S₂ ∘ S₁`.  No
closure property of `D` is used.  (3) The table `S₂ ∘ S₁` of Equation
`eq:spec-composition` mentions no order on `M`, and Lifted Monotonicity of the
composite uses only the orders on `I` and `O`.  So the composite under `≼_M` is
the composite under the other order, which satisfies Lifted Monotonicity by
(1).  The same holds after re-encoding the intermediate values.  A re-encoding
is a map `e : M → M'` together with a decoding `e' : M' → M` that recovers
every value, `e'(e(m)) = m`.  Replace `S₁` by `{(i,e(m)) : (i,m) ∈ S₁}` and
`S₂` by `{(m',o) : (e'(m'),o) ∈ S₂}`.  A join through `e(m)` is a join through
`e'(e(m)) = m`, so the composite table is unchanged, whatever the orders on `M`
and `M'`."  Lean: (1) `Comp.seq_liftedMono`, and a Lifted-Monotone `𝒮₂`
satisfies it on all of `M` (`Joint.ceOn_of_ce`); (2)
`Joint.seq_liftedMono_on` (any `D` containing the outputs) and
`Joint.ceOn_iff_restrictTo` ("on `D`" is Lifted Monotonicity of the
restriction to `D`); (3) `Joint.seq_under` (the composite under the given
order `instM` and under another order `inst` is one specification),
`Joint.seq_liftedMono_reorder`, `Joint.reorder_seq` (re-encoding, as
`Joint.pushOut` and `Joint.pullIn`) and `Joint.seq_liftedMono_reencode`. -/
theorem «app:composition/joint-monotone» {I M O : Type} [PO I] [instM : PO M] [PO O] :
    ((∀ {sp1 : Spec I M} {sp2 : Spec M O}, sp1.LiftedMono → sp2.LiftedMono →
        (Comp.seq sp1 sp2).LiftedMono) ∧
      ∀ sp2 : Spec M O, sp2.LiftedMono → Joint.CEOn sp2 (fun _ => True)) ∧
    ((∀ {sp1 : Spec I M} {sp2 : Spec M O} {D : M → Prop}, sp1.LiftedMono →
        (∀ i m, sp1.S i m → D m) → Joint.CEOn sp2 D → (Comp.seq sp1 sp2).LiftedMono) ∧
      ∀ (D : M → Prop) (sp : Spec M O), Joint.CEOn sp D ↔ (Joint.restrictTo D sp).LiftedMono) ∧
    ((∀ (sp1 : Spec I M) (sp2 : Spec M O) (inst : PO M),
        @Comp.seq I M O _ inst _ (Joint.underOut inst sp1) (Joint.underIn inst sp2) =
          @Comp.seq I M O _ instM _ sp1 sp2) ∧
      (∀ {sp1 : Spec I M} {sp2 : Spec M O} (inst : PO M),
        @Spec.LiftedMono I M _ inst (Joint.underOut inst sp1) →
        @Spec.LiftedMono M O inst _ (Joint.underIn inst sp2) →
        (@Comp.seq I M O _ instM _ sp1 sp2).LiftedMono) ∧
      (∀ {M' : Type} [PO M'] (sp1 : Spec I M) (sp2 : Spec M O) (e : M → M') (e' : M' → M),
        (∀ m, e' (e m) = m) →
          Comp.seq (Joint.pushOut sp1 e) (Joint.pullIn sp2 e') = Comp.seq sp1 sp2) ∧
      ∀ {M' : Type} [PO M'] {sp1 : Spec I M} {sp2 : Spec M O} {e : M → M'} {e' : M' → M},
        (∀ m, e' (e m) = m) → (Joint.pushOut sp1 e).LiftedMono →
          (Joint.pullIn sp2 e').LiftedMono → (Comp.seq sp1 sp2).LiftedMono) :=
  ⟨⟨fun h1 h2 => Comp.seq_liftedMono h1 h2,
      fun _ h => Joint.ceOn_of_ce ((liftedMono_iff_commonExpansion _).1 h) _⟩,
    ⟨fun h1 hD h2 => Joint.seq_liftedMono_on h1 hD h2, Joint.ceOn_iff_restrictTo⟩,
    ⟨fun sp1 sp2 inst => Joint.seq_under inst sp1 sp2, fun inst h1 h2 => Joint.seq_liftedMono_reorder inst h1 h2,
      fun sp1 sp2 e e' h => Joint.reorder_seq sp1 sp2 e e' h,
      fun h h1 h2 => Joint.seq_liftedMono_reencode h h1 h2⟩⟩

/-- "The reach of case (3).  Let `f : I → M` and `g : M → O` be functions with
`g(f(·))` monotone.  Place `a` below `b` in `M` when `g(a) ≼ g(b)`.  This
relation is reflexive and transitive.  It makes `g` monotone by construction,
and `f` monotone because `g(f(·))` is.  It can place two distinct values each
below the other, so it is an order only when no such pair exists, in
particular when `g` maps distinct values to distinct values.  Then case (3)
applies.  In general it need not.  Let `I` be the chain `x ⊑ y ⊑ z`,
`M = {p,q}`, `f(x) = f(z) = p`, `f(y) = q`, and `g` constant.  The composite is
constant, hence monotone.  Under any order on `M`, monotonicity of `f` gives
`p ≼_M q ≼_M p`, so `p = q`, a contradiction.  By the exposure test for tables
of functions, `f(i)` is exposable at `σ(i)` exactly when `f(i) ≼_M f(k)` for
every `k ⪰ i`, so the upstream under the empty basis cannot emit at one of the
canonical states of `x` and `y`.  The stages can be repaired only by merging
`p` and `q` into one intermediate value."  Lean: `Joint.preorder_factorization` (the
reflexive, transitive relation, which exists exactly when `g ∘ f` is
monotone); `Joint.injective_characterization` (for one-to-one `g`, stated for
Lifted Monotonicity of the tables, with the pulled-back partial order
`Joint.pullPO`); `Joint.graph_canon_exposable_iff` (the exposure test);
`Joint.no_order_counterexample` (`I = Joint.C3`, `M = Joint.Mid`; the
empty-basis upstream stalls at some canonical state); `Joint.merge_needed`
(any re-encoding `e` of `M`, into any partially ordered set, that makes the
upstream `e ∘ f` monotone has `e(p) = e(q)`). -/
theorem «app:composition/reach» {I M O : Type} [PO I] [PO O] :
    (∀ {f : I → M} {g : M → O}, Monotone (g ∘ f) ↔ ∃ le : M → M → Prop, (∀ a, le a a) ∧
      (∀ a b c, le a b → le b c → le a c) ∧ (∀ x y, x ≼ y → le (f x) (f y)) ∧
      ∀ a b, le a b → g a ≼ g b) ∧
    (∀ {f : I → M} {g : M → O}, (∀ a b, g a = g b → a = b) →
      ((graph (g ∘ f)).LiftedMono ↔ ∃ inst : PO M,
        @Spec.LiftedMono I M _ inst (@graph I M _ inst f) ∧
        @Spec.LiftedMono M O inst _ (@graph M O inst _ g))) ∧
    (∀ (inst : PO M) (f : I → M) (i : I),
      @Exposable I M _ inst _ (@canon I M _ inst (@graph I M _ inst f) i) (f i) ↔
        ∀ k, i ≼ k → @PO.le M inst (f i) (f k)) ∧
    ((∀ _inst : PO Joint.Mid, (Comp.seq (graph Joint.fz) (graph Joint.gz)).LiftedMono) ∧
      (∀ _inst : PO Joint.Mid, ¬ (graph Joint.fz).LiftedMono) ∧
      ∀ _inst : PO Joint.Mid, ∃ i, ∀ γ o τ,
        ¬ SysStep (fun _ => False) (canon (graph Joint.fz) i) (.output γ o) τ) ∧
    ∀ {M' : Type} (inst : PO M') (e : Joint.Mid → M'),
      @Monotone Joint.C3 M' _ inst (e ∘ Joint.fz) → e .p = e .q :=
  ⟨Joint.preorder_factorization, fun hg => Joint.injective_characterization hg,
    fun inst f i => @Joint.graph_canon_exposable_iff I M _ inst f i, Joint.no_order_counterexample,
    fun inst e h => Joint.merge_needed inst e h⟩

/-- "For the capped counter of Section `sec:composite-calm`, let `𝒮₁` be the
table of the function `c(n) = min(n,9)` on `(ℕ, ≤)` and `𝒮₂` the table of the
test `t(n) = [n < 10]`, whose two outputs are incomparable.  `𝒮₂` violates
Lifted Monotonicity, since `[9 < 10]` and `[10 < 10]` differ, but it satisfies
it on `{n ≤ 9}`, so the composite is Lifted-Monotone by case (2).  At
`σ_{𝒮₂}(m)` with `m ≤ 9`, emitting `[m < 10]` must seal the row `(10, false)`,
so `𝒮₂` cannot emit under the empty basis.  The outputs of `𝒮₁` lie in
`{n ≤ 9}`, so the pipeline is proper (Theorem `thm:proper-coordination`(1)).
Under the empty basis, `𝒮₂|_{𝒮₁}` answers every count that `𝒮₁` emits."
Lean: `Joint.thr_ceOn`, `Joint.up_img`, `Joint.threshold` (the rest of the
paragraph is `«sec:composite-calm/filtering»`); answering every count is
`Guard.proper_follows` for this proper pipeline. -/
theorem «app:composition/capped-counter» :
    Joint.CEOn Joint.thr (fun m => ¬ Joint.Big m) ∧ (∀ i m, Joint.up.S i m → ¬ Joint.Big m) ∧
      Guard.Proper Joint.up Joint.thr :=
  ⟨Joint.thr_ceOn, fun _ _ h => Joint.up_img h, Joint.threshold.2.2.2⟩

/-- "For the boolean toggle, let `I`, `M`, and `O` be the booleans with `false`
below `true`, and let both stages be negation.  The table of a function `f`
has `f(i)` exposable at `σ(i)` exactly when `f(i) ≼_M f(k)` for all `k ⪰ i`.
At `i = false` the first stage would emit `true`, which is not below its
output `false` at the larger input, so under the empty basis it cannot emit
there.  Under the reversed order on `M`, negation is monotone in both stages,
and by case (3) the composite is the identity in either order."  Lean:
`Joint.graph_canon_exposable_iff` (the exposure test, in
`«app:composition/reach»`), `Joint.toggle_exposable_iff` (the first stage's
output is exposable at `σ(b)` exactly when `b = true`),
`Joint.toggle_empty_basis`, `Joint.bool_toggle` (in
`«sec:composite-calm/cancellation»`). -/
theorem «app:composition/boolean-toggle» (b : Bool) :
    (Exposable (canon (graph not) b) (!b) ↔ b = true) ∧
    (∀ {γ o τ}, ¬ SysStep (fun _ => False) (canon (graph not) false) (.output γ o) τ) ∧
    Comp.seq (Joint.pushOut (graph not) Joint.Rev.mk) (Joint.pullIn (graph not) Joint.Rev.val) =
      graph (id : Bool → Bool) :=
  ⟨Joint.toggle_exposable_iff b, Joint.toggle_empty_basis,
    Joint.bool_toggle.2.2.2.2.2.trans Joint.bool_toggle.2.1⟩

/-- "Let `𝒮₁` have one input `*` and table `{(*,x),(*,y)}` with `x,y`
incomparable, and let `𝒮₂` be the table of a function `f` that maps both to
one value.  The composite has one row, so it satisfies Lifted Monotonicity. …
every run of `𝒮₁` under the empty basis stays at the canonical state and emits
nothing.  Then `𝒮₂` receives nothing.  Renaming `x,y` to `lo ≼ hi` makes `𝒮₁`
Lifted-Monotone, since `hi` retires `lo`, and by case (3) the composite is
unchanged."  Lean: `𝒮₁ = Dist.spU`; the second conjunct of
`Guard.composite_monotone_not_enough` says such runs emit nothing;
`Guard.noBasis_silent` is the run-level form; the renaming is
`Joint.constant_store_reorder` (on `Comp.anyS`). -/
theorem «app:composition/components-commit» :
    (Guard.comp Dist.spU (fun _ : Dist.B2 => ())).LiftedMono ∧
      (∀ o, ¬ Exposable (canon Dist.spU ()) o) ∧
      (∀ es ρ, SysExec Dist.noBasis (canon Dist.spU ()) es ρ → Guard.emitted es = []) ∧
      (Joint.pushOut Comp.anyS Guard.fLvl).LiftedMono ∧
      Comp.seq (Joint.pushOut Comp.anyS Guard.fLvl) (Joint.pullIn Joint.constK Joint.lvlTwo) =
        Comp.seq Comp.anyS Joint.constK :=
  ⟨Guard.composite_monotone_not_enough.1,
    Dist.spU_not_exposable _ (fun _ _ => ⟨trivial, trivial⟩),
    Guard.composite_monotone_not_enough.2, Joint.constant_store_reorder.2.1,
    Joint.constant_store_reorder.2.2.2.2.1⟩

/-! ## Proper Coordination -/

/-- "For tables `R` of `𝒮₁` and `T` of `𝒮₂` we write
`R ⋈ T = {(k,x) : ∃ m. (k,m) ∈ R ∧ (m,x) ∈ T}`.  The image of a state
`σ = (i,R)` of `𝒮₁` is the state `(i, R ⋈ S₂)` of `S₂ ∘ S₁`.  The image of
`σ_{𝒮₁}(i)` is `σ_{S₂∘S₁}(i)`, since `S₁[in ⪰ i] ⋈ S₂` is the composite table
restricted to the expansions of `i`."  Lean: the image is `Guard.imgK sk σ`;
`Guard.imgK_canon`.  The function case is `Guard.img f σ = Guard.imgK (graph f) σ`
and `Guard.img_canon`. -/
theorem «app:composition/image-canon» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    (sk : Spec M O) (f : M → O) (i : I) :
    (∀ σ : State sp, (Guard.imgK sk σ).cur = σ.cur ∧
      ∀ k x, (Guard.imgK sk σ).R k x ↔ ∃ m, σ.R k m ∧ sk.S m x) ∧
    Guard.imgK sk (canon sp i) = canon (Comp.seq sp sk) i ∧
      (∀ σ : State sp, Guard.img f σ = Guard.imgK (graph f) σ) ∧
      Guard.img f (canon sp i) = canon (Guard.comp sp f) i :=
  ⟨fun _ => ⟨rfl, fun _ _ => Iff.rfl⟩, Guard.imgK_canon sk i, Guard.img_eq_imgK f,
    Guard.img_canon f i⟩

/-- "A run of the pipeline is a run of `𝒮₁` under `ℬ`, together with a run of
`𝒮₂|_{𝒮₁}` from `σ(m₁)`, where `m₁` is the first output of `𝒮₁`.  Each later
output of `𝒮₁` is an input event of `𝒮₂|_{𝒮₁}`.  Between its inputs,
`𝒮₂|_{𝒮₁}` emits any number of outputs, possibly none."  Lean: a run of the
pipeline is `Guard.GRun U K l m esK`: the upstream can emit `l` (`U l`; for a
system `P` for `𝒮₁`, `U = Guard.liftU P`, its output sequences typed as
inputs of `𝒮₂|_{𝒮₁}`), and the downstream system `K` produces `esK` from
`σ(m)`.  The shape `Guard.Shaped` says that the erased trace is a block of
outputs `os`, then, for each later output `m'` of `l` in order, `input(m')`
followed by a block of outputs (`Guard.blk`); each block may be empty. -/
theorem «app:composition/pipeline-run» {M O : Type} [PO M] [PO O] {sk : Spec M O}
    (U : List M → Prop) (K : Guard.Sys sk) (l : List M) (m : M) (esK : List (SEvent sk)) :
    (Guard.GRun U K l m esK ↔ U l ∧ Guard.Shaped l m (esK.filterMap SEvent.erase) ∧
      ∃ ρK, Guard.Produces K m esK ρK) ∧
    (Guard.Shaped l m (esK.filterMap SEvent.erase) ↔ ∃ (os : List O) (ps : List (M × List O)),
      (m :: ps.map Prod.fst) <+: l ∧ esK.filterMap SEvent.erase = os.map Event.output ++ Guard.blk ps) ∧
    ∀ (m' : M) (os : List O) ps,
      Guard.blk ((m', os) :: ps) = .input m' :: (os.map Event.output ++ Guard.blk ps) :=
  ⟨Iff.rfl, Iff.rfl, fun _ _ _ => rfl⟩

/-- "In a proper pipeline, two facts about a state `τ` that `𝒮₂|_{𝒮₁}`
reaches without commitment carry the proofs.  First, every input
`j ⪰_M τ.cur` has a row in `τ` … Second, every output at the current input is
exposable.  A third fact concerns `𝒮₁`.  If an output `m` at the current
input of a state `σ` of `𝒮₁` is exposable, every `o ∈ S₂(m)` is exposable at
the image of `σ`. … Either way
`(k,u)` is a row of the image that retires `(k,x)`."  Lean: the first two hold
at every run state (`Guard.row_at`, `commonExpansion_exposable`, with the
common-expansion condition of `𝒮₂|_{𝒮₁}` from `Guard.proper_iff_ce`); states
reached without commitment are run states (`Guard.isRun_sysExec_empty`); the
third is `Guard.cf_stepK_on`. -/
theorem «app:composition/store-facts» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    {sk : Spec M O} (hP : Guard.Proper sp sk) :
    (∀ τ : State (Guard.rest sp sk), IsRun τ → ∀ j, τ.cur ≼ j → ∃ u, τ.R j u) ∧
    (∀ τ : State (Guard.rest sp sk), IsRun τ → ∀ o, τ.R τ.cur o → Exposable τ o) ∧
    (∀ (σ τ : State (Guard.rest sp sk)) es, SysExec (fun _ => False) σ es τ → IsRun σ → IsRun τ) ∧
    ∀ (σ : State sp) {m : M}, Exposable σ m → sp.S σ.cur m → ∀ {o}, sk.S m o →
      Exposable (Guard.imgK sk σ) o := by
  have hC := Guard.proper_iff_ce.1 hP
  exact ⟨fun _ hτ _ hj => Guard.row_at hC hτ hj,
    fun _ hτ _ ho => commonExpansion_exposable hC hτ ho,
    fun _ _ _ h hσ => Guard.isRun_sysExec_empty h hσ,
    fun σ _ he hm _ ho => Guard.cf_stepK_on (Guard.proper_iff.1 hP)
      (fun k m h => ⟨k, σ.sub k m h⟩) ⟨_, hm⟩ he ho⟩

/-- Proof of Theorem `thm:proper-coordination`(2): "Before the first output of
`𝒮₁` we keep `ρ.cur = σ.cur` and `R_σ ⋈ S₂ ⊆ R_ρ`.  Afterwards we keep
`R_σ ⋈ T ⊆ R_ρ`, and every row `(k,m)` of `R_σ` has `m` above the current
input of `𝒮₂|_{𝒮₁}`. … Each answer `o` has `(m,o) ∈ T`, so `(i,o) ∈ R_ρ`.  The
composite's `output(o)` keeps `R_ρ[out ⪰ o]`, and `𝒮₂|_{𝒮₁}` keeps
`T[out ⪰ o]`, so the join stays inside the composite's table."  Lean, for a
downstream with the common-expansion condition (here `𝒮₂|_{𝒮₁}`, whose inputs
are typed as outputs of `𝒮₁`, `Guard.core_lockstep`): `Guard.Inv`; before the
first output `Guard.merge_inputs`; afterwards `Guard.merge_lockstep`, with the
answers to one input `Guard.answer_run`; assembled in `Guard.composite_run`
and `Guard.proper_run`. -/
theorem «app:composition/guarded-lockstep» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    {sk : Spec M O} (hC : sk.CommonExpansion) {B : Basis sp} {σ ρ : State sp}
    {es : List (SEvent sp)} (h : SysExec B σ es ρ) :
    (Guard.emitted es = [] → ∀ ρ' : State (Comp.seq sp sk), Guard.Inv σ sk.S ρ' →
      ∃ ρ'', Exec ρ' (Guard.merge es []) ρ'' ∧ Guard.Inv ρ sk.S ρ'') ∧
    ∀ (ps : List (M × List O)) (τK ρK : State sk) (esK : List (SEvent sk))
      (ρ' : State (Comp.seq sp sk)), Guard.emitted es = ps.map Prod.fst →
      SysExec (fun _ => False) τK esK ρK → esK.filterMap SEvent.erase = Guard.blk ps → IsRun τK →
      (∀ k m, σ.R k m → τK.cur ≼ m) → Guard.Inv σ τK.R ρ' →
      ∃ ρ'', Exec ρ' (Guard.merge es (ps.map Prod.snd)) ρ'' ∧ Guard.Inv ρ ρK.R ρ'' ∧
        ∀ k m, ρ.R k m → ρK.cur ≼ m :=
  ⟨fun he ρ' hI => Guard.merge_inputs h he ρ' hI, Guard.merge_lockstep hC h⟩

/-- Proof of Theorem `thm:proper-coordination`(3): "The proof of
Proposition `prop:exposure-boundary` derives the common-expansion condition
from exposability at canonical states alone." -/
theorem «app:composition/canonical-states-suffice» {I O : Type} [PO I] [PO O] :
    ∀ {sp : Spec I O}, (∀ i o, sp.S i o → Exposable (canon sp i) o) → sp.CommonExpansion :=
  fun h => Guard.canon_exposable_commonExpansion h

/-- "Properness is needed in (3).  With `𝒮₁` the identity on the booleans and
`𝒮₂` negation, the composite is negation, which violates Lifted Monotonicity,
yet `𝒮₁` needs no commitment."  Lean: `Joint.needs_commit_needs_proper`
(booleans ordered by `Joint.boolPO`, `false ≼ true`). -/
theorem «app:composition/properness-needed» :
    ¬ (Comp.seq (graph (id : Bool → Bool)) (graph not)).LiftedMono ∧
      ∀ τ : State (graph (id : Bool → Bool)), ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  Joint.needs_commit_needs_proper

/-- "The commitment-erased replacement of a system has the empty basis and the
same strategy, with each `Out_δ(x)` replaced by `Out_ε(x)`."  Lean:
`Guard.eraseSys K`; after a local history it allows an event when `K` allows
one with the same erasure (`Guard.eraseC`) after a history with the same
erasure.  It is basis-free, so it applies no commitment. -/
theorem «app:composition/replacement» {M O : Type} [PO M] [PO O] {sk : Spec M O}
    (K : Guard.Sys sk) :
    (Guard.eraseSys K).basis = (fun _ => False) ∧
    (∀ i a' e', (Guard.eraseSys K).strat i a' e' ↔
      ∃ a e, a.map Guard.eraseC = a'.map Guard.eraseC ∧ Guard.eraseC e = Guard.eraseC e' ∧
        K.strat i a e) ∧
    ∀ i es ρ, Guard.Produces (Guard.eraseSys K) i es ρ → ∀ γ x, SEvent.output γ x ∈ es → γ = [] :=
  ⟨rfl, fun _ _ _ => Iff.rfl, fun _ _ _ h => Guard.eraseSys_eps h⟩

/-- **Corollary `cor:empty-store`** (Empty store): "In a proper pipeline, fix
any system for `𝒮₂|_{𝒮₁}`.  For every run of the pipeline, the replacement
has one with the same run of `𝒮₁` and the same inputs and outputs of
`𝒮₂|_{𝒮₁}`.  After each event, the replacement's table contains the
original's."  Lean: `Guard.proper_erase`, for any upstream behaviour `U`
("the same run of `𝒮₁`" is the same upstream output sequence `l`). -/
theorem «cor:empty-store» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M} {sk : Spec M O}
    (hP : Guard.Proper sp sk) (U : List {m // Joint.Img sp m} → Prop)
    (K : Guard.Sys (Guard.rest sp sk)) :
    ∀ l m esK, Guard.GRun U K l m esK →
      Guard.GRun U (Guard.eraseSys K) l m (esK.map Guard.eraseC) ∧
        (esK.map Guard.eraseC).filterMap SEvent.erase = esK.filterMap SEvent.erase ∧
        ∀ ρK, Guard.Produces K m esK ρK → ∃ ρ', Guard.Produces (Guard.eraseSys K) m
          (esK.map Guard.eraseC) ρ' ∧ IsRun ρ' ∧ ∀ k u, ρK.R k u → ρ'.R k u :=
  fun _ _ _ h => Guard.proper_erase hP h

/-- Proof of Corollary `cor:empty-store`: "Let `τ` be a state of the original
and `τ'` a state of the replacement reached without commitment, with the same
current input and `R_τ ⊆ R_τ'`. … If `Out_δ(x)` is legal at `τ`, then `x` is
at the current input of `τ` and so of `τ'`, where it is exposable by the second
fact. … Both start at `σ(m₁)`, so the containment holds after each event.  The
replacement's strategy allows each erased event, since the original's allowed
it before erasure."  Lean: `Guard.erase_lockstep` (for any downstream with the
common-expansion condition) and `Guard.compliant_eraseSys`. -/
theorem «app:composition/empty-store» {M O : Type} [PO M] [PO O] {sk : Spec M O}
    (hC : sk.CommonExpansion) {BK : Basis sk} {σ ρ : State sk}
    {es : List (SEvent sk)} (h : SysExec BK σ es ρ) (σ' : State sk) (hr : IsRun σ')
    (hc : σ'.cur = σ.cur) (hs : ∀ k u, σ.R k u → σ'.R k u) :
    ∃ ρ', SysExec (fun _ => False) σ' (es.map Guard.eraseC) ρ' ∧ IsRun ρ' ∧ ρ'.cur = ρ.cur ∧
      ∀ k u, ρ.R k u → ρ'.R k u :=
  Guard.erase_lockstep hC h σ' hr hc hs

/-- **Corollary `cor:pipelines`** (Pipelines): "In a proper pipeline, with any
systems for `𝒮₁` and `𝒮₂|_{𝒮₁}`, the outputs of every run of the pipeline
are emitted by a run of `S₂ ∘ S₁` under its canonical basis.  So the pipeline
guards a further stage `𝒮₃`, and Theorem `thm:proper-coordination` applies
with `S₂ ∘ S₁` in place of `𝒮₁`."  Lean: `Guard.proper_pipeline_step` (the
outputs of the pipeline's runs, `Guard.GEmits (Guard.liftU P) K`, are emitted
by the canonical-basis system of `S₂ ∘ S₁`); the theorem for `𝒮₃` is
`«thm:proper-coordination»` with `sp := Comp.seq s1 s2`, whose (1) is restated
here.  Associativity is `«sec:composition/associativity»`. -/
theorem «cor:pipelines» {I M O Q : Type} [PO I] [PO M] [PO O] [PO Q] {s1 : Spec I M}
    {s2 : Spec M O} (s3 : Spec O Q) (h12 : Guard.Proper s1 s2) (P : Guard.Sys s1)
    (K2 : Guard.Sys (Guard.rest s1 s2)) :
    (∀ l', Guard.GEmits (Guard.liftU P) K2 l' →
      (Guard.Sys.free (canonBasis (Comp.seq s1 s2))).emits l') ∧
    (Guard.Proper (Comp.seq s1 s2) s3 ↔ Joint.CEOn s3 (Joint.Img (Comp.seq s1 s2))) :=
  ⟨fun _ h => Guard.proper_pipeline_step h12 h, Guard.proper_iff⟩

/-- Proof of Corollary `cor:pipelines`: "By Corollary `cor:empty-store`, every
run of the pipeline has one with the same outputs in which `𝒮₂|_{𝒮₁}` runs
under the empty basis.  Theorem `thm:proper-coordination`(2), applied to it
and a prefix of the run of `𝒮₁`, gives a run of `S₂ ∘ S₁` with these outputs,
and the canonical event for each output (Lemma
`lem:canonical-commitment-normal-form`) makes it a run under the canonical
basis."  Lean: inside `Guard.proper_pipeline_step`, via `Guard.erase_simulates`,
`Guard.emitted_prefix`, `Guard.proper_run`, `exec_canonExec` and
`canonExec_sysExec`; the same step for a Lifted-Monotone downstream and any
of its systems is `Guard.pipeline_step`. -/
theorem «app:composition/pipelines» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    {sk : Spec M O} (hK : sk.LiftedMono) {P : Guard.Sys sp} {K : Guard.Sys sk} {l' : List O}
    (h : Guard.GEmits P.emits K l') : (Guard.Sys.free (canonBasis (Comp.seq sp sk))).emits l' :=
  Guard.pipeline_step ((liftedMono_iff_commonExpansion sk).1 hK) h

/-- "Let `𝒮₁` be the log specification of Example
`ex:committed-log-composition`, under its canonical basis with a strategy that
allows every event, and `𝒮₂` the table of any monotone function `f` of the
log.  Every log is an output of `𝒮₁`, so `𝒮₂|_{𝒮₁}` is `𝒮₂`.  For a set `Q`
of logs, removing every row whose input is in `Q` is a commitment of `𝒮₂` at
any state whose current input is not in `Q` and which has such a row.  It
removes whole fibers, so it seals. … Suppose that the store takes the lock
only once its current log is nonempty.  Every log it can still receive then
has the same first command, so the lock removes no row and is not a
commitment.  Suppose instead that the store takes the lock at the empty log,
ahead of the log.  Its output `f([])` was exposable without the lock, and the
lock seals logs that `𝒮₁` can still offer.  At `σ_{𝒮₁}([b])`, `𝒮₁` can emit
`[]` and then `[b]`.  The replacement emits `f([])`, receives `[b]`, and emits
`f([b])`.  The locking store must take the lock at `[]`, which seals `[b]`, so
it cannot receive `[b]`."  Lean: `𝒮₁ = Inst.smrS1`; every log is an output
(`Guard.smr_img`); the lock is `Guard.sealIn (Guard.bFirst b)` with store basis
`Guard.mutexB b f`; at a nonempty log the lock is undefined
(`Guard.lock_after_log`), so the late-lock store `Guard.lateLock b f` applies no
commitment in any run (`Guard.lateLock_eps`); `f([])` is exposable at every
state with current log `[]` (`Guard.store_exposable`); the early-lock store
`Guard.earlyLock b f` loses a run of its replacement (`Guard.early_lock_strict`,
observable traces `Guard.Obs`). -/
theorem «app:composition/mutex-store» {Cmd O : Type} [PO O] {f : Inst.Pfx Cmd → O}
    (hf : Monotone f) (b : Cmd) :
    (∀ m, Joint.Img (Inst.smrS1 (Cmd := Cmd)) m) ∧
    (∀ (Q : Inst.Pfx Cmd → Prop) (σ τ : State (graph f)), (Guard.sealIn Q).app σ = some τ →
      ¬ Q σ.cur ∧ (∃ k x, σ.R k x ∧ Q k) ∧ ∀ k, Q k → ∀ x, ¬ τ.R k x) ∧
    (∀ σ : State (graph f), σ.cur.l ≠ [] → (Guard.sealIn (Guard.bFirst b)).app σ = none) ∧
    (∀ m esK ρ, Guard.Produces (Guard.lateLock b f) m esK ρ →
      ∀ γ x, SEvent.output γ x ∈ esK → γ = []) ∧
    (∀ σ : State (graph f), σ.cur = ⟨[]⟩ → Exposable σ (f ⟨[]⟩)) ∧
    ∃ l m tr, Guard.Obs (Guard.Sys.free (canonBasis (Inst.smrS1 (Cmd := Cmd)))).emits
        (Guard.eraseSys (Guard.earlyLock b f)) l m tr ∧
      ¬ Guard.Obs (Guard.Sys.free (canonBasis (Inst.smrS1 (Cmd := Cmd)))).emits
        (Guard.earlyLock b f) l m tr := by
  refine ⟨Guard.smr_img, fun Q σ τ h => ?_, Guard.lock_after_log b,
    fun _ _ _ h => Guard.lateLock_eps b h, fun σ hσ => hσ ▸ Guard.store_exposable hf σ,
    Guard.early_lock_strict hf b⟩
  obtain ⟨hn, hex, rfl⟩ := Guard.sealInApp_eq.1 h
  exact ⟨hn, hex, fun _ hQ _ hx => hx.2 hQ⟩

/-- **Proposition `prop:invisible-coordination`** (Invisible coordination):
"Let `f` be monotone, and let `𝒮₁` emit `m` at `σ` by `Out_γ(m)`.  If every
row that `γ` removes has a row with the same input and the same image that `γ`
keeps, then `f(m)` is exposable at `f(σ)`." -/
theorem «prop:invisible-coordination» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    {f : M → O} (hf : Monotone f) {B : Basis sp} {σ τ : State sp} {γ : List (Commitment sp)}
    {m : M} (h : SysStep B σ (.output γ m) τ)
    (hinv : ∀ σc : State sp, ApplySeq γ σ σc →
      ∀ k m', σ.R k m' → ∃ m'', σc.R k m'' ∧ f m'' = f m') :
    Exposable (Guard.img f σ) (f m) :=
  Guard.invisible_step hf h hinv

/-- The covering argument: "The proof covers the composite's commitments by
those of `𝒮₁`. … Let `Out_γ(m)` be legal at `σ`, let `γ` leave `σ_c`, and let
`ρ` be a composite state with `f(R_σ) ⊆ R_ρ`.  No row `(k,f(m'))` with
`(k,m') ∈ R_{σ_c}` is in `Sealed_{f(m)}` or `Rejected_{f(m)}` at `ρ`. … So every
row that the composite's canonical event for `f(m)` removes by commitment has
had every preimage in `R_σ` removed by `γ`."  Lean: `Guard.coverage` (stated
for any `σ_c` at which `m` is exposable and any `ρ` containing `f(R_{σ_c})`)
and `Guard.coverage_step`. -/
theorem «app:composition/coverage» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    {f : M → O} (hf : Monotone f) :
    (∀ {σc : State sp} {m : M}, Exposable σc m → ∀ {ρ : State (Guard.comp sp f)},
      (∀ k o, Guard.imgT f σc.R k o → ρ.R k o) →
      ∀ k x, Guard.imgT f σc.R k x → ¬ Sealed ρ (f m) k x ∧ ¬ Rejected ρ (f m) k x) ∧
    ∀ {B : Basis sp} {σ τ : State sp} {γ : List (Commitment sp)} {m : M},
      SysStep B σ (.output γ m) τ → ∀ {ρ : State (Guard.comp sp f)},
      (∀ k o, Guard.imgT f σ.R k o → ρ.R k o) →
      ∃ σc, ApplySeq γ σ σc ∧
        ∀ k x, (Sealed ρ (f m) k x ∨ Rejected ρ (f m) k x) →
          ∀ m', σ.R k m' → f m' = x → ¬ σc.R k m' :=
  ⟨fun he _ hs => Guard.coverage hf he hs, fun h _ hs => Guard.coverage_step hf h hs⟩

/-- "Consider a store that answers each key from that key's commands, in log
order.  Let `𝒮₁` have one input with fiber `{[a,b],[b,a]}`, for commands `a`
and `b` on different keys, and let `f` send a log to the family of its
subsequences on each key.  The two logs are incomparable with no common
refinement, so `[a,b]` is not exposable, and `𝒮₁` must order them.  But
`f([a,b]) = f([b,a])`, the composite has one row, and `f([a,b])` is
exposable."  Lean: the per-key view `Guard.perKey key` is monotone;
`𝒮₁ = Guard.abSpec a b`. -/
theorem «app:composition/per-key» {Cmd K : Type} [DecidableEq K] (key : Cmd → K)
    {a b : Cmd} (hk : key a ≠ key b) :
    Monotone (Guard.perKey key) ∧ Guard.perKey key ⟨[a, b]⟩ = Guard.perKey key ⟨[b, a]⟩ ∧
      ¬ Exposable (canon (Guard.abSpec a b) Comp.Pt.pt) ⟨[a, b]⟩ ∧
      Exposable (canon (Guard.comp (Guard.abSpec a b) (Guard.perKey key)) Comp.Pt.pt)
        (Guard.perKey key ⟨[a, b]⟩) :=
  ⟨Guard.perKey_monotone key, Guard.perKey_swap key hk, Guard.commute_example key hk⟩

/-- "The commitments of `𝒮₁` do not themselves push forward.  Let `𝒮₁` have
one input with fiber `{x,y}`, `x` and `y` incomparable, and
`f(x) = lo ≼ hi = f(y)`.  The choice `c_y` removes `x` and keeps `y`.  Its
image would remove `lo` and keep `hi`, violating Equation
`eq:commitment-excludes`, so no commitment of the composite has that effect.
In the composite, `hi` is exposable at the canonical state, since it retires
`lo`."  Lean: `𝒮₁ = Comp.anyS`, `f = Guard.fLvl`. -/
theorem «app:composition/no-pushforward» :
    (∃ τ, (choiceC Comp.Two.y).app (canon Comp.anyS Comp.Pt.pt) = some τ ∧
      ∀ c : Commitment (Guard.comp Comp.anyS Guard.fLvl),
        c.app (Guard.img Guard.fLvl (canon Comp.anyS Comp.Pt.pt)) ≠ some (Guard.img Guard.fLvl τ)) ∧
    Exposable (canon (Guard.comp Comp.anyS Guard.fLvl) Comp.Pt.pt) Guard.Lvl.hi :=
  ⟨Guard.push_not_commitment, Guard.choice_becomes_retirement.2⟩

/-- "Monotonicity of `f` is needed.  Let `𝒮₁` be the table of the identity on
`M`, which needs no commitment.  For `m ≼ m'`, its run `output(m)`,
`input(m')`, `output(m')` maps to a run of the composite exactly when
`f(m) ≼ f(m')`." -/
theorem «app:composition/monotone-needed» {M O : Type} [PO M] [PO O] (f : M → O) {m m' : M}
    (hmm : m ≼ m') :
    ExecCF (canon (graph fun x : M => x) m) [.output m, .input m', .output m']
        (canon (graph fun x : M => x) m') ∧
      ((∃ ρ, Exec (canon (Guard.comp (graph fun x : M => x) f) m)
          [.output (f m), .input m', .output (f m')] ρ) ↔ f m ≼ f m') :=
  ⟨Guard.identity_cf hmm, Guard.monotone_necessary f hmm⟩

/-- "A downstream that must itself choose cannot delegate the choice either.
If `𝒮₁` is the identity on one input, it admits no commitment at all.  If
`𝒮₂` relates that input to two incomparable outputs, every output event of
the composite at its canonical state applies a commitment, which `𝒮₁` cannot
make." -/
theorem «app:composition/store-choice» :
    (∀ (c : Commitment (graph fun x : Dist.U1 => x)) σ τ, c.app σ ≠ some τ) ∧
    ∀ (B : Basis (Comp.seq (graph fun x : Dist.U1 => x) Dist.spU)) γ o τ,
      SysStep B (canon _ ()) (.output γ o) τ → γ ≠ [] :=
  Guard.store_choice_not_delegable

/-- **Example `ex:committed-log-composition`** (Replicated store), for any
deterministic state machine `δ` and two distinct commands: "Then `𝒮₁` is
non-monotone, since distinct next entries are incompatible outputs in one
fiber.  So is the key-value store `S₂ ∘ S₁`, since concurrent commands ordered
oppositely give incompatible responses. … Since `f` is monotone, the pipeline
is proper, and by Theorem `thm:proper-coordination`(2) the store under the
empty basis follows every run of the log.  By Theorem
`thm:proper-coordination`(3), the log's commitments cannot be dropped.  By
Corollary `cor:empty-store`, replicas whose store takes locks of its own can
run it with no commitments at all."  Lean: `𝒮₁ = Inst.smrS1`
(`I = M = Inst.Pfx Cmd`, prefix order), `f = Inst.execF δ σ₀` (monotone);
following every run is `«thm:proper-coordination»`(2) and dropping the
store's commitments is `«cor:empty-store»`, both for this proper pipeline. -/
theorem «ex:committed-log-composition» {Cmd Stt R : Type} (δ : Stt → Cmd → Stt × R) (σ0 : Stt)
    {c₁ c₂ : Cmd} (hne : c₁ ≠ c₂) :
    ¬ (Inst.smrS1 (Cmd := Cmd)).LiftedMono ∧
      ¬ (Guard.comp Inst.smrS1 (Inst.execF δ σ0)).LiftedMono ∧
      Monotone (Inst.execF δ σ0) ∧ Guard.Proper Inst.smrS1 (graph (Inst.execF δ σ0)) ∧
      ∃ i m, Inst.smrS1.S i m ∧
        ¬ Exposable (canon (Guard.comp Inst.smrS1 (Inst.execF δ σ0)) i) (Inst.execF δ σ0 m) ∧
        ∀ m', Inst.smrS1.S i m' → Inst.execF δ σ0 m' = Inst.execF δ σ0 m →
          ¬ Exposable (canon Inst.smrS1 i) m' :=
  let h := Guard.smr_proper δ σ0 hne
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

/-- **Example `ex:bare-reads`** (Bare reads), position-tagged responses, for
any deterministic state machine `δ`, read function `rd`, and two distinct
commands: "As in Example `ex:committed-log-composition`, `F` and `G ⋆ F` are
non-monotone. … A longer log never contradicts such a response, so `G` is
monotone.  By Complete CALM and the exposure boundary, every output of `G` at
every state reachable without commitment is exposable, so bare reads need no
commitment of their own."  Lean: `I = B = Inst.Pfx Cmd`, `A = Comp.Pt`,
`J = Inst.Pfx Rd`; `logF`, `bareG δ rd σ₀`, whose outputs pair the executed
response log with a set (`Inst.Facts`) of tagged responses `(r, n, v)`, `v` the
value `rd` gives after the first `n ≤ |b|` entries.  "Responses are facts, so
a set of them may answer one read more than once." -/
theorem «ex:bare-reads» {Cmd Stt R Rd V : Type} (δ : Stt → Cmd → Stt × R) (rd : Stt → Rd → V)
    (σ0 : Stt) {c₁ c₂ : Cmd} (hne : c₁ ≠ c₂) :
    ¬ (Inst.logF (Cmd := Cmd)).LiftedMono ∧
      ¬ (Comp.par Inst.logF (Inst.bareG δ rd σ0)).LiftedMono ∧ (Inst.bareG δ rd σ0).LiftedMono ∧
      ∀ τ : State (Inst.bareG δ rd σ0), ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  Inst.bare_read_example δ rd σ0 hne

/-- Inside Example `ex:bare-reads`: "Suppose instead that the specification
demands the latest value, so that a read of `x` must return the value of `x`
after all of `b`.  Then a bare read can be contradicted by an entry it has not
seen, and `G` is not monotone.  By the exposure boundary some output of `G`
then needs a commitment of the store's own."  Lean: `latestG δ rd σ₀`
(untagged responses `(r, v)`, `v` the value after all of `b`); "an entry it has
not seen" is a command `c` that changes what read `r` returns. -/
theorem «ex:bare-reads/latest-value» {Cmd Stt R Rd V : Type} (δ : Stt → Cmd → Stt × R)
    (rd : Stt → Rd → V) (σ0 : Stt) {c : Cmd} {r : Rd} (hc : rd (δ σ0 c).1 r ≠ rd σ0 r) :
    ¬ (Inst.latestG δ rd σ0).LiftedMono ∧
      ∃ τ : State (Inst.latestG δ rd σ0), ReachableCF τ ∧ ∃ o, τ.R τ.cur o ∧ ¬ Exposable τ o :=
  ⟨Inst.latestG_not_liftedMono δ rd σ0 hc, Inst.latest_needs_store_commitment δ rd σ0 hc⟩

end Paper
end CC
