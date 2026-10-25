import CoordCriterion.Appendix.Guarded
import CoordCriterion.Appendix.JointMono

/-!
# Paper §5, "Composition and Proper Coordination" (`sections/composition.tex`)

Statement layer for Section `sec:composition`.  Read it side by side with
`sections/composition.tex`: the `/-! ## … -/` headers follow the section's
subsections, entries appear in paper order, and each entry quotes the claim
it formalizes.  Numbered results and displayed equations are named by their
LaTeX label; unlabeled claims are `«sec:composition/<slug>»`.  The proofs
are in Appendix `app:composition`; its curried evaluation, the counterexamples, and the
covering argument are in `Paper/AppD_Composition.lean`.

The section has no subsection heading for sequential composition; its label
`sec:sequential-composition` sits after the section opening.  Composition with
independent inputs (`sec:parameterized-composition`) is in Appendix
`app:composition` and `Paper/AppD_Composition.lean`.

Library: `Appendix/Composition.lean` (namespace `CC.Comp`), the examples at
the end of `Instances/Examples.lean` (namespace `CC.Inst`), and guarded
composition in `Appendix/Guarded.lean` (namespace `CC.Guard`).

Conventions: a table is `Table I O := I → O → Prop`; `Spec I O` is a table
total on all of `I` with orders on `I` and `O`; products carry the
componentwise order; the composed input `I × J × A` is `I × (J × A)`;
`Comp.graph f` is the table of `f`, and `Comp.Monotone f` is
`∀ x y, x ≼ y → f x ≼ f y`.  For an upstream `𝒫 : Spec I M` and a store
`f : M → O`, `Guard.comp 𝒫 f` is `𝒦 ∘ 𝒫`, `Guard.img f σ` is the image
state `f(σ)`, and `Guard.obs f` replaces each output `m` by `f(m)` (and
erases commitments).
-/

namespace CC
namespace Paper

open CC.Comp (Monotone graph)

/-! ## Sequential composition (`sec:sequential-composition`) -/

/-- Eq. `eq:spec-composition`:
`S₂ ∘ S₁ = π_{I,O}(S₁ ⋈_M S₂) = {(i,o) : ∃ m. (i,m) ∈ S₁ ∧ (m,o) ∈ S₂}`. -/
theorem «eq:spec-composition» {I M O : Type} (S1 : Table I M) (S2 : Table M O) (i : I) (o : O) :
    Comp.tcomp S1 S2 i o ↔ ∃ m, S1 i m ∧ S2 m o :=
  Iff.rfl

/-- "Since `S₁` is total on `I` and `S₂` is total on `M` (it has a row at
every `m ∈ M`), every `i ∈ I` has a nonempty fiber in `S₂ ∘ S₁`."  Lean: the
composition is the specification `Comp.seq sp1 sp2`, whose table is
`tcomp`; totality is its `total` field. -/
theorem «sec:composition/seq-total» {I M O : Type} [PO I] [PO M] [PO O]
    (sp1 : Spec I M) (sp2 : Spec M O) :
    (Comp.seq sp1 sp2).S = Comp.tcomp sp1.S sp2.S ∧ ∀ i, ∃ o, Comp.tcomp sp1.S sp2.S i o :=
  ⟨rfl, (Comp.seq sp1 sp2).total⟩

/-- Totality of `S₂` on *all* of `M` is needed (not stated in the paper; it
explains the hypothesis above).  If `S₂` is total only on a proper subset of
`M`, Lemma `lem:composition` fails even when the composed table is total. -/
theorem «sec:composition/middle-totality-needed» :
    Comp.s1.LiftedMono ∧ (Comp.restrict Comp.t2).LiftedMono ∧
      (∀ i, ∃ o, Comp.tcomp Comp.s1.S Comp.t2 i o) ∧
      ¬ (Comp.restrict (Comp.tcomp Comp.s1.S Comp.t2)).LiftedMono :=
  Comp.restricted_middle_counterexample

/-- **Lemma `lem:composition`** (Composition): "If `Spec₁` and `Spec₂`
satisfy Lifted Monotonicity, then the ordered specification with table
`S₂ ∘ S₁` satisfies Lifted Monotonicity." -/
theorem «lem:composition» {I M O : Type} [PO I] [PO M] [PO O] {sp1 : Spec I M} {sp2 : Spec M O}
    (h1 : sp1.LiftedMono) (h2 : sp2.LiftedMono) : (Comp.seq sp1 sp2).LiftedMono :=
  Comp.seq_liftedMono h1 h2

/-- "By associativity the lemma extends to finite pipelines." -/
theorem «sec:composition/associativity» {I M O P : Type} (S1 : Table I M) (S2 : Table M O)
    (S3 : Table O P) :
    Comp.tcomp (Comp.tcomp S1 S2) S3 = Comp.tcomp S1 (Comp.tcomp S2 S3) :=
  Comp.tcomp_assoc S1 S2 S3

/-- "For a function `f`, its table `{(i,f(i))}` satisfies
Lifted Monotonicity exactly when `f` is monotone.  Tables of functions are closed
under `∘`."  Lean: the composition of the tables of `f` and `g` is the
table of `g ∘ f`, and the table of `f` satisfies Lifted
Monotonicity iff `f` is monotone. -/
theorem «sec:composition/function-tables» {I M O : Type} [PO I] [PO M] [PO O] (f : I → M) (g : M → O) :
    Comp.seq (graph f) (graph g) = graph (g ∘ f) ∧ ((graph f).LiftedMono ↔ Monotone f) :=
  ⟨Comp.seq_graph f g, Comp.graph_liftedMono_iff f⟩

/-! ## Composite CALM (`sec:composite-calm`) -/

/-- "The composite is itself an ordered specification, so Complete CALM
applies to it directly.  Specification `S₂ ∘ S₁` is consistent exactly when it
satisfies Lifted Monotonicity, and then no output needs a commitment (Theorem
`thm:complete-calm`, Proposition `prop:exposure-boundary`)." -/
theorem «sec:composite-calm/complete-calm» {I M O : Type} [PO I] [PO M] [PO O]
    (sp1 : Spec I M) (sp2 : Spec M O) :
    ((Comp.seq sp1 sp2).Consistent ↔ (Comp.seq sp1 sp2).LiftedMono) ∧
      ((Comp.seq sp1 sp2).LiftedMono →
        ∀ τ : State (Comp.seq sp1 sp2), ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o) :=
  ⟨complete_calm _, fun h =>
    (exposure_boundary _).1 ((liftedMono_iff_commonExpansion _).1 h)⟩

/-- "First, every stage is monotone.  By Lemma `lem:composition` the pipeline
is monotone, and every stage can run with the empty basis, with no seals and
no choices anywhere (Corollary `cor:pipelines`)."  Lean:
`Guard.pipeline_coordination_free` (the base case of the pipeline induction):
the composite is Lifted-Monotone, and the guarded composite of an empty-basis
upstream with any store system emits only what the composite emits under the
empty basis, so it is again an empty-basis guard. -/
theorem «sec:composite-calm/all-monotone» {I M O : Type} [PO I] [PO M] [PO O]
    {sp : Spec I M} {sk : Spec M O} (hP : sp.LiftedMono) (hK : sk.LiftedMono) (K : Guard.Sys sk) :
    (Comp.seq sp sk).LiftedMono ∧
      ∀ l', Guard.GEmits (Guard.Sys.free (fun _ : Commitment sp => False)).emits K l' →
        (Guard.Sys.free (fun _ : Commitment (Comp.seq sp sk) => False)).emits l' :=
  ⟨Comp.seq_liftedMono hP hK, fun _ h => (Guard.pipeline_coordination_free hP hK h).2⟩

/-- "The CRDT observations of Section `sec:crdt-instance` have this shape: a
client query `q` over the replica state `s` is the composition `q ∘ s`, and
compositions of monotone functions are monotone (Corollary
`cor:functional-composition`), so monotonicity of `q` on all of the state domain
suffices."  Lean: the
corollary applied to `s = Inst.st s₀` (monotone by
`«sec:crdt-instance/state-monotone»`) and a monotone `q`. -/
theorem «sec:composite-calm/crdt-query» {D Y : Type} [PO D] [Inst.JSL D] [PO Y] (s0 : D)
    {q : D → Y} (hq : Monotone q) : Monotone (q ∘ (Inst.st s0 : Inst.FSet D → D)) :=
  Comp.functional_composition (Inst.st_mono s0) hq

/-- "Second, the upstream can filter out the inputs on which the downstream is
not monotone.  Consider a counter capped at `9` that feeds a test of whether
the count is below `10`.  On its own the test is not monotone: it answers yes
at `9` and no at `10`.  But the counter never produces `10`, and on the counts
`0` through `9` the test always answers yes.  The downstream need only be
monotone on the values the upstream can produce."  Lean: `Joint.threshold`
(the test is not Lifted-Monotone, the composite is).  Lean also proves the
Appendix D treatment of the test as a store with a basis: it cannot emit under
the empty basis below `10`, and with one seal at its first output
(`Joint.sealStore_follows`) the guarded composite is proper with every upstream
system. -/
theorem «sec:composite-calm/filtering» :
    (¬ Joint.thr.LiftedMono ∧
      (∀ m, m ≤ 9 → ∀ γ o τ, ¬ SysStep (fun _ => False) (canon Joint.thr m) (.output γ o) τ) ∧
      (Comp.seq Joint.up Joint.thr).LiftedMono ∧
      ∀ P : Guard.Sys Joint.up, Guard.Proper P Joint.sealStore) ∧
    ∀ (P : Guard.Sys Joint.up) {m : Nat} {ms : List Nat}, P.emits (m :: ms) →
      ∃ esK rest, Guard.GRun P.emits Joint.sealStore (m :: ms) m esK ∧
        esK = .output [Guard.sealIn Joint.Big] (Joint.below m) :: rest ∧
        esK.map SEvent.erase =
          .output (Joint.below m) :: Guard.storeTr (ms.map fun m => (m, Joint.below m)) :=
  ⟨Joint.threshold, fun P _ _ h => Joint.sealStore_follows P h⟩

/-- "Third, two stages that are each non-monotone can cancel.  Consider a
first stage that receives a growing set `X` from a domain `U` and outputs its
complement `U ∖ X`, the elements not yet seen, and a second stage that
complements again.  The composite returns `X`, which only grows.  Under the
usual order on sets, though, each stage is non-monotone.  As `X` grows, the
first stage's output shrinks, so without commitment it can emit only the empty
set.  … The composite's table never mentions the order on the intermediate
domain `M` between the stages, so the stages can agree on a different one.
Invert it: let `S ≼_M S'` exactly when `S' ⊆ S`.  … both stages are
monotone.  Likewise, suppose the upstream may output
either of two incomparable values `a` and `b`, and the downstream maps both to
the same answer.  The upstream cannot emit either without choosing.  If the
interface places `a` below `b`, the upstream can emit `a` and later supersede
it with `b`, and the composite is unchanged."  Lean:
`Joint.double_complement` (`Joint.Rev` is the reversed order),
`Joint.compl_empty_basis` (under the empty basis every output at a canonical
state is `∅`), `Joint.constant_store_reorder`; the constant store cannot emit
without choosing is `«app:composition/components-commit»`. -/
theorem «sec:composite-calm/cancellation» {U : Type} [Nonempty U] :
    (¬ (graph (Joint.compl (U := U))).LiftedMono ∧
      Comp.seq (graph (Joint.compl (U := U))) (graph Joint.compl) = graph id ∧
      (graph (id : Joint.PSet U → Joint.PSet U)).LiftedMono ∧
      (Joint.pushOut (graph (Joint.compl (U := U))) Joint.Rev.mk).LiftedMono ∧
      (Joint.pullIn (graph (Joint.compl (U := U))) Joint.Rev.val).LiftedMono ∧
      Comp.seq (Joint.pushOut (graph (Joint.compl (U := U))) Joint.Rev.mk)
          (Joint.pullIn (graph Joint.compl) Joint.Rev.val) =
        Comp.seq (graph Joint.compl) (graph Joint.compl)) ∧
    (∀ {X : Joint.PSet U} {γ o τ},
      SysStep (fun _ => False) (canon (graph (Joint.compl (U := U))) X) (.output γ o) τ →
        ∀ u, ¬ o.mem u) ∧
    (¬ Comp.anyS.LiftedMono ∧ (Joint.pushOut Comp.anyS Guard.fLvl).LiftedMono ∧
      Exposable (canon (Joint.pushOut Comp.anyS Guard.fLvl) Comp.Pt.pt) Guard.Lvl.hi ∧
      (Joint.pullIn Joint.constK Joint.lvlTwo).LiftedMono ∧
      Comp.seq (Joint.pushOut Comp.anyS Guard.fLvl) (Joint.pullIn Joint.constK Joint.lvlTwo) =
        Comp.seq Comp.anyS Joint.constK ∧
      (Comp.seq Comp.anyS Joint.constK).LiftedMono) :=
  ⟨Joint.double_complement, fun h => Joint.compl_empty_basis h, Joint.constant_store_reorder⟩

/-- **Proposition `prop:joint-monotone`** (Jointly monotone composites): "(1) If
`𝒮₁` satisfies Lifted Monotonicity and `𝒮₂` satisfies it on the outputs of
`𝒮₁`, then `S₂ ∘ S₁` satisfies Lifted Monotonicity.  (2) Changing the order on
`M` leaves `S₂ ∘ S₁` unchanged.  So does re-encoding the intermediate values,
provided the downstream can decode them.  (3) Let `f : I → M` and
`g : M → O` be functions such that `g(f(x)) ≼ g(f(y))` whenever `x ⊑ y`.  If
`g` is one-to-one (injective), some order on `M` makes both `f` and `g`
monotone.  Otherwise there may be no such order."  And: "We say
that `S₂` satisfies Lifted Monotonicity on a set `D ⊆ M` when the
common-expansion condition holds for its rows with inputs in `D`, at
expansions in `D`."  Lean: `Joint.CEOn` (equivalently, the restriction to `D`
is Lifted-Monotone, `Joint.ceOn_iff_restrictTo`); (1) `Joint.seq_liftedMono_img`;
(2) `Joint.reorder_seq` (encoding `e`, decoding `e'` with `e' (e m) = m`; a
change of order alone is `e = e' = id` between two orders on `M`); (3)
`Joint.preorder_factorization` (the reflexive, transitive relation of the
proof, which exists exactly when `g ∘ f` is monotone),
`Joint.injective_characterization` (stated for Lifted Monotonicity of the
tables), `Joint.no_order_counterexample` ("otherwise there may be no such
order"). -/
theorem «prop:joint-monotone» {I M O : Type} [PO I] [PO M] [PO O] :
    (∀ {sp1 : Spec I M} {sp2 : Spec M O}, sp1.LiftedMono → Joint.CEOn sp2 (Joint.Img sp1) →
      (Comp.seq sp1 sp2).LiftedMono) ∧
    (∀ {M' : Type} [PO M'] (sp1 : Spec I M) (sp2 : Spec M O) (e : M → M') (e' : M' → M),
      (∀ m, e' (e m) = m) → Comp.seq (Joint.pushOut sp1 e) (Joint.pullIn sp2 e') = Comp.seq sp1 sp2) ∧
    (∀ {f : I → M} {g : M → O}, Monotone (g ∘ f) ↔ ∃ le : M → M → Prop, (∀ a, le a a) ∧
      (∀ a b c, le a b → le b c → le a c) ∧ (∀ x y, x ≼ y → le (f x) (f y)) ∧
      ∀ a b, le a b → g a ≼ g b) ∧
    (∀ {f : I → M} {g : M → O}, (∀ a b, g a = g b → a = b) →
      ((graph (g ∘ f)).LiftedMono ↔ ∃ inst : PO M,
        @Spec.LiftedMono I M _ inst (@graph I M _ inst f) ∧
        @Spec.LiftedMono M O inst _ (@graph M O inst _ g))) ∧
    ((∀ _inst : PO Joint.Mid, (Comp.seq (graph Joint.fz) (graph Joint.gz)).LiftedMono) ∧
      (∀ _inst : PO Joint.Mid, ¬ (graph Joint.fz).LiftedMono) ∧
      ∀ _inst : PO Joint.Mid, ∃ i, ∀ γ o τ,
        ¬ SysStep (fun _ => False) (canon (graph Joint.fz) i) (.output γ o) τ) :=
  ⟨fun h1 h2 => Joint.seq_liftedMono_img h1 h2, fun sp1 sp2 e e' h => Joint.reorder_seq sp1 sp2 e e' h,
    Joint.preorder_factorization, fun hg => Joint.injective_characterization hg,
    Joint.no_order_counterexample⟩

/-! ## Proper Coordination (`sec:proper-coordination`) -/

/-- "Let `𝒫 = (I,≼,M,≼,P)` be an upstream specification and
`𝒦 = (M,≼,O,≼,K)` a downstream specification, the store, that satisfies Lifted
Monotonicity.  For a state `σ = (i,R)` of `𝒫`, its image `𝒦(σ)` is the state
`(i, {(k,x) : ∃ m. (k,m) ∈ R ∧ (m,x) ∈ K})` of `𝒦 ∘ 𝒫`. … When `K` is the
table `{(m,f(m))}` of a monotone function `f`, the answer to `m` is `f(m)`, and
we write `f(σ)` for the image."  Lean: `Guard.imgK sk σ`; the function case is
`Guard.img f σ = Guard.imgK (graph f) σ`, and `graph f` is Lifted-Monotone iff
`f` is monotone. -/
theorem «sec:proper-coordination/image» {I M O : Type} [PO I] [PO M] [PO O]
    (sp : Spec I M) (sk : Spec M O) (f : M → O) :
    (∀ σ : State sp, (Guard.imgK sk σ).cur = σ.cur ∧
      ∀ k x, (Guard.imgK sk σ).R k x ↔ ∃ m, σ.R k m ∧ sk.S m x) ∧
    (∀ σ : State sp, Guard.img f σ = Guard.imgK (graph f) σ) ∧
    ((graph f).LiftedMono ↔ Monotone f) :=
  ⟨fun _ => ⟨rfl, fun _ _ => Iff.rfl⟩, Guard.img_eq_imgK f, Comp.graph_liftedMono_iff f⟩

/-- "A commitment of `𝒫` may keep `m'` and remove `m`, with `m` and `m'`
incomparable but `f(m) ≼ f(m')`.  Its image removes a row refined by a row it
keeps, which Equation `eq:commitment-excludes` forbids.  In the composite,
emitting `f(m')` needs no commitment at all, since it retires `f(m)`."
Lean: `𝒫 = Comp.anyS` (fiber `{x, y}`), `f = Guard.fLvl` (`x ↦ lo`,
`y ↦ hi`); the choice `c_y`. -/
theorem «sec:proper-coordination/no-pushforward» :
    (∃ τ, (choiceC Comp.Two.y).app (canon Comp.anyS Comp.Pt.pt) = some τ ∧
      ∀ c : Commitment (Guard.comp Comp.anyS Guard.fLvl),
        c.app (Guard.img Guard.fLvl (canon Comp.anyS Comp.Pt.pt)) ≠ some (Guard.img Guard.fLvl τ)) ∧
    ¬ Exposable (canon Comp.anyS Comp.Pt.pt) Comp.Two.y ∧
      Exposable (canon (Guard.comp Comp.anyS Guard.fLvl) Comp.Pt.pt) Guard.Lvl.hi :=
  ⟨Guard.push_not_commitment, Guard.choice_becomes_retirement⟩

/-- **Definition `def:proper-coordination`** (Proper Coordination): "The store
coordinates redundantly when, in some guarded composite run, one of its output
events applies a commitment that is contradicted (Definition
`def:coordination`) in the runs of `𝒦` on output sequences that `𝒫`'s system
can emit.  The guarded composite coordinates at most once when the store does
not coordinate redundantly.  It coordinates at least once when every output
event `Out_γ(m)` of `𝒫` at a state `σ` such that some `o ∈ K(m)` is not
exposable at `𝒦(σ)` has `γ ≠ ε`.  It is proper when it coordinates at most
once and at least once."  And: "A store commitment is therefore contradicted
when a run of `𝒦` on outputs `𝒫` can emit accepts an input it seals, or emits
an output it chooses against.  We judge it against the runs of the
specification, since a store that has sealed an input never accepts it in its
own runs."  Lean: a system for one participant is `Guard.Sys` (a basis and a
strategy that sees the initial input and the local history), with produced
runs `Guard.Produces` and emitted output sequences `Guard.Sys.emits`.  The
results are stated for any upstream behaviour `U : List M → Prop` (for a
system `P`, `U = P.emits`).  A guarded composite run is `Guard.GRun U K l m esK`:
`U l`, and `K` produces `esK` from `σ_𝒦(m)`, answering a prefix `m :: ms` of
`l` (`Guard.Shaped`).  The reference runs `𝓡` are `Guard.SRun` (runs of `𝒦` on
such prefixes); sealing is `Guard.Accepts`, choosing against `Guard.EmitsAt`. -/
theorem «def:proper-coordination» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    {sk : Spec M O} (P : Guard.Sys sp) (K : Guard.Sys sk) (U : List M → Prop) :
    (Guard.Proper P K ↔ Guard.AtMostOnce P.emits K ∧ Guard.AtLeastOnce P.basis sk) ∧
      (Guard.AtMostOnce U K ↔ ¬ Guard.Redundant U K) ∧
      (Guard.Redundant U K ↔ ∃ l m esK a δ x b σ σc, Guard.GRun U K l m esK ∧
        esK = a ++ .output δ x :: b ∧ SysExec K.basis (canon sk m) a σ ∧
        ApplySeq δ σ σc ∧ Guard.Contradicted U σ σc) ∧
      (∀ σ σc : State sk, Guard.Contradicted U σ σc ↔
        (∃ k, (∃ x, σ.R k x) ∧ (∀ x, ¬ σc.R k x) ∧ Guard.Accepts U sk k) ∨
        (∃ k x, σ.R k x ∧ ¬ σc.R k x ∧ Guard.EmitsAt U sk k x)) ∧
      (Guard.AtLeastOnce P.basis sk ↔ ∀ (σ τ : State sp) γ m, SysStep P.basis σ (.output γ m) τ →
        ∀ o, sk.S m o → ¬ Exposable (Guard.imgK sk σ) o → γ ≠ []) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, fun _ _ => Iff.rfl, Iff.rfl⟩

/-- **Theorem `thm:guarded-runs`** (Guarded runs): "Let `ℬ` be any basis of
`𝒫`.  (1) The outputs `m₁, m₂, …` of a run of `𝒫` under `ℬ` form a chain, and
a store under the empty basis follows it.  Starting at `σ_𝒦(m₁)`, it answers
`m₁`, then receives and answers each later `m_r`, with no commitment.
(2) Replacing each output `m_r` of the run of `𝒫` by the store's answer `o_r`
gives a run of `𝒦 ∘ 𝒫` from the same canonical state.  After each event, the
composite run's table contains the join of the tables of `𝒫` and of the
store.  (3) If finitely many runs of `𝒫` can be brought to a common state with
current input `j`, under any bases, the corresponding composite runs are
confluent at `j`."  Lean, for `𝒦` Lifted-Monotone (via the common-expansion
condition): (1) `Guard.emitted_chain`, `Guard.store_follows`; (2)
`Guard.composite_run` (the trace is `Guard.merge`; "after each event" is the
lockstep `Guard.merge_lockstep`); (3) `Guard.guarded_confluentK`, for any
composite run states containing the joins.  The function case is
`Guard.guarded_run`/`Guard.store_run`/`Guard.guarded_confluent`. -/
theorem «thm:guarded-runs» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M} {sk : Spec M O}
    (hK : sk.LiftedMono) (B : Basis sp) :
    (∀ (σ ρ : State sp) es, SysExec B σ es ρ → Guard.ChainFrom none (Guard.emitted es)) ∧
    (∀ (m : M) ms, Guard.ChainFrom (some m) ms →
      ∃ o ps esK ρ, ps.map Prod.fst = ms ∧ esK.map SEvent.erase = .output o :: Guard.storeTr ps ∧
        Guard.Produces (Guard.noStore sk) m esK ρ ∧ IsRun ρ) ∧
    (∀ i es ρ m ms o ps esK ρK, SysExec B (canon sp i) es ρ → Guard.emitted es = m :: ms →
      ps.map Prod.fst = ms → SysExec (fun _ => False) (canon sk m) esK ρK →
      esK.map SEvent.erase = .output o :: Guard.storeTr ps →
      ∃ ρ', Exec (canon (Comp.seq sp sk) i) (Guard.merge es (o :: ps.map Prod.snd)) ρ' ∧
        ρ'.cur = ρ.cur ∧ (∀ k m x, ρ.R k m → ρK.R m x → ρ'.R k x) ∧ IsRun ρK ∧
        ∀ k m, ρ.R k m → ρK.cur ≼ m) ∧
    (∀ (fam : List (State sp × State sk × State (Comp.seq sp sk))),
      (∀ p ∈ fam, IsRun p.2.2) → (∀ p ∈ fam, IsRun p.2.1) →
      (∀ p ∈ fam, ∀ k m x, p.1.R k m → p.2.1.R m x → p.2.2.R k x) →
      (∀ p ∈ fam, ∀ k m, p.1.R k m → p.2.1.cur ≼ m) →
      ∀ j : I, (∀ p ∈ fam, p.2.2.cur ≼ j) →
      (∃ τ : State sp, τ.cur = j ∧ ∀ p ∈ fam, ∃ (B' : Basis sp) (es : List (SEvent sp)),
        SysExec B' p.1 es τ) →
      ConfluentAt (fam.map fun p => p.2.2) j) := by
  have hC := (liftedMono_iff_commonExpansion sk).1 hK
  exact ⟨fun _ _ _ hx => Guard.emitted_chain hx none (fun _ h => by cases h),
    fun _ _ hc => Guard.store_follows hC hc,
    fun _ _ _ _ _ _ _ _ _ hP he hps hKx htr => Guard.composite_run hC hP he hps hKx htr,
    fun fam h1 h2 h3 h4 j hj hP => Guard.guarded_confluentK hC fam h1 h2 h3 h4 j hj hP⟩

/-- **Theorem `thm:proper-coordination`** (Proper Coordination): "Fix any
system for `𝒫`.  (1) At every state that `𝒦` reaches without commitment, every
output at the current input is exposable.  So wherever a store under any basis
performs `Out_δ(o)`, a store under the empty basis at such a state, with the
same current input and a larger table, can perform `Out_ε(o)` and keep at
least the same rows.  For a function store this holds at every state.
(2) The guarded composite coordinates at least once, for every system for
`𝒦`.  It is proper when `ℬ_𝒦` is empty.  (3) If `𝒦 ∘ 𝒫` violates Lifted
Monotonicity, some output `o` of the composite is not exposable at a canonical
state, and `𝒫` must commit to emit any `m` with `o ∈ K(m)` there."  Lean, for
`𝒦` Lifted-Monotone: (1) `commonExpansion_exposable` (at run states, which
include states reached without commitment), the single step of
`Guard.erase_lockstep`, and for a function store `Guard.store_exposable`;
(2) `Guard.at_least_once`, `Guard.guarded_proper`; (3)
`Guard.composite_needs_commit` ("must commit": no such `m'` is exposable at
`σ_𝒫(i)`, and under the empty basis no output event there emits one). -/
theorem «thm:proper-coordination» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    {sk : Spec M O} (hK : sk.LiftedMono) :
    (∀ τ : State sk, IsRun τ → ∀ o, τ.R τ.cur o → Exposable τ o) ∧
    (∀ (f : M → O), Monotone f → ∀ σ : State (graph f), Exposable σ (f σ.cur)) ∧
    (∀ B : Basis sp, Guard.AtLeastOnce B sk) ∧
    (∀ P : Guard.Sys sp, Guard.Proper P (Guard.noStore sk)) ∧
    (¬ (Comp.seq sp sk).LiftedMono →
      ∃ i m o, sp.S i m ∧ sk.S m o ∧ ¬ Exposable (canon (Comp.seq sp sk) i) o ∧
        (∀ m', sp.S i m' → sk.S m' o → ¬ Exposable (canon sp i) m') ∧
        ∀ γ m' τ, SysStep (fun _ => False) (canon sp i) (.output γ m') τ → ¬ sk.S m' o) := by
  have hC := (liftedMono_iff_commonExpansion sk).1 hK
  exact ⟨fun _ hτ _ ho => commonExpansion_exposable hC hτ ho,
    fun _ hf σ => Guard.store_exposable hf σ, Guard.at_least_once hC,
    Guard.guarded_proper hC, Guard.composite_needs_commit hC⟩

/-- "By Theorem `thm:guarded-runs`(1), a store under the empty basis also
follows every run of `𝒫`.  The theorem holds for every system for `𝒫`."  Lean:
for any upstream behaviour `U` and any chain `m :: ms` with `U (m :: ms)`
(every sequence a system emits is a chain, `Guard.emits_chain`), there is a
guarded composite run in which the empty-basis store answers every output. -/
theorem «sec:proper-coordination/empty-store-follows» {M O : Type} [PO M] [PO O]
    {sk : Spec M O} (hK : sk.LiftedMono) {U : List M → Prop} {m : M} {ms : List M}
    (hU : U (m :: ms)) (hc : Guard.ChainFrom none (m :: ms)) :
    ∃ esK o ps, Guard.GRun U (Guard.noStore sk) (m :: ms) m esK ∧ ps.map Prod.fst = ms ∧
      esK.map SEvent.erase = .output o :: Guard.storeTr ps :=
  Guard.noStore_follows ((liftedMono_iff_commonExpansion sk).1 hK) hU hc

/-- "For a function store, every legal output event removes at least the rows
its canonical event removes (Lemma `lem:canonical-commitment-normal-form`), so
every row that the composite must seal or choose against has lost all its
preimages to `𝒫`'s commitments."  Lean: for a legal `Out_γ(m)` of `𝒫` under
any basis and any composite state whose table contains the image of `𝒫`'s; the
covering argument of Appendix `app:composition` is
`«app:composition/coverage»`. -/
theorem «sec:proper-coordination/any-basis» {I M O : Type} [PO I] [PO M] [PO O]
    {sp : Spec I M} {f : M → O} (hf : Monotone f) {B : Basis sp} {σ τ : State sp}
    {γ : List (Commitment sp)} {m : M} (h : SysStep B σ (.output γ m) τ)
    {ρ : State (Guard.comp sp f)} (hsub : ∀ k o, Guard.imgT f σ.R k o → ρ.R k o) :
    ∃ σc, ApplySeq γ σ σc ∧
      ∀ k x, (Sealed ρ (f m) k x ∨ Rejected ρ (f m) k x) →
        ∀ m', σ.R k m' → f m' = x → ¬ σc.R k m' :=
  Guard.coverage_step hf h hsub

/-- "By Theorem `thm:proper-coordination`(1), none of the store's commitments
is needed.  So it should be safe to replace the store's system with one whose
basis is empty, with no seals or choices allowed.  The commitment-erased
replacement of the store's system has the empty basis and the same strategy,
with each `Out_δ(x)` replaced by `Out_ε(x)`."  Lean: `Guard.eraseSys K`; after
a local history it allows an event when `K` allows one with the same erasure
(`Guard.eraseC`) after a history with the same erasure.  It is basis-free, so
it applies no commitment. -/
theorem «sec:proper-coordination/replacement» {M O : Type} [PO M] [PO O] {sk : Spec M O}
    (K : Guard.Sys sk) :
    (Guard.eraseSys K).basis = (fun _ => False) ∧
    (∀ i a' e', (Guard.eraseSys K).strat i a' e' ↔
      ∃ a e, a.map Guard.eraseC = a'.map Guard.eraseC ∧ Guard.eraseC e = Guard.eraseC e' ∧
        K.strat i a e) ∧
    ∀ i es ρ, Guard.Produces (Guard.eraseSys K) i es ρ → ∀ γ x, SEvent.output γ x ∈ es → γ = [] :=
  ⟨rfl, fun _ _ _ => Iff.rfl, fun _ _ _ h => Guard.eraseSys_eps h⟩

/-- **Corollary `cor:empty-store`** (Empty store): "Fix systems for `𝒫` and
`𝒦`.  (1) For every guarded composite run, the replacement has one with the
same run of `𝒫` and the same store inputs and outputs.  After each event, the
replacement's table contains the original's.  (2) Suppose the store
coordinates at most once, and its strategy ignores the commitments in its
history and never stalls: whenever it offers an output still in its table, it
also offers a legal output event for it.  Then the converse of (1) holds too,
so the store and its replacement have the same observable behaviour."  Lean,
for any upstream behaviour `U` and `𝒦` Lifted-Monotone: (1)
`Guard.erase_simulates` (no at-most-once needed; the lockstep form, after each
event, is `Guard.erase_lockstep`); (2) `Guard.erase_reflects` (needs neither
monotonicity nor at least once) and `Guard.empty_storeU`, with the strategy
hypotheses `Guard.Blind` and `Guard.Live`; for an upstream system,
`Guard.empty_store`.  "Same run of `𝒫`" is the same upstream output sequence
`l`; observable behaviour is `Guard.Obs`.  The replacement itself coordinates
at most once. -/
theorem «cor:empty-store» {M O : Type} [PO M] [PO O] {sk : Spec M O} (hK : sk.LiftedMono)
    (U : List M → Prop) (K : Guard.Sys sk) :
    (∀ l m esK, Guard.GRun U K l m esK →
      Guard.GRun U (Guard.eraseSys K) l m (esK.map Guard.eraseC) ∧
        (esK.map Guard.eraseC).map SEvent.erase = esK.map SEvent.erase ∧
        ∀ ρK, Guard.Produces K m esK ρK → ∃ ρ', Guard.Produces (Guard.eraseSys K) m
          (esK.map Guard.eraseC) ρ' ∧ IsRun ρ' ∧ ∀ k u, ρK.R k u → ρ'.R k u) ∧
    (Guard.AtMostOnce U K → Guard.Blind K → Guard.Live K →
      (∀ l m esK', Guard.GRun U (Guard.eraseSys K) l m esK' →
        ∃ esK, Guard.GRun U K l m esK ∧ esK.map SEvent.erase = esK'.map SEvent.erase) ∧
      Guard.AtMostOnce U (Guard.eraseSys K) ∧
      ∀ l m tr, Guard.Obs U K l m tr ↔ Guard.Obs U (Guard.eraseSys K) l m tr) := by
  have hC := (liftedMono_iff_commonExpansion sk).1 hK
  exact ⟨fun _ _ _ h => Guard.erase_simulates hC h, fun hirr hb hl =>
    ⟨fun _ _ _ h => Guard.erase_reflects hb hl hirr h, Guard.empty_storeU hC hirr hb hl⟩⟩

/-- "The hypotheses of (2) are needed.  A strategy that offers only commitments
undefined at its state never emits, while its replacement does.  If the store
is redundant, the replacement can follow runs of `𝒫` that the store cannot, as
the mutex store below shows."  Lean: with `𝒫 = Inst.smrS1` under its canonical
basis and every strategy, and any monotone `f`: the stalling-lock store
`Guard.stallLock b f` is proper and `Guard.Blind`, yet its replacement follows
a run it cannot (`Guard.stall_lock`), so `Guard.Live` is needed; the redundant
early-lock store loses a run the same way (`Guard.early_lock_strict`). -/
theorem «sec:proper-coordination/hypotheses-needed» {Cmd O : Type} [PO O]
    {f : Inst.Pfx Cmd → O} (hf : Monotone f) (b : Cmd) :
    (Guard.Proper (Guard.Sys.free (canonBasis (Inst.smrS1 (Cmd := Cmd)))) (Guard.stallLock b f) ∧
      Guard.Blind (Guard.stallLock b f) ∧
      ∃ l m tr, Guard.Obs (Guard.Sys.free (canonBasis (Inst.smrS1 (Cmd := Cmd)))).emits
          (Guard.eraseSys (Guard.stallLock b f)) l m tr ∧
        ¬ Guard.Obs (Guard.Sys.free (canonBasis (Inst.smrS1 (Cmd := Cmd)))).emits
          (Guard.stallLock b f) l m tr) ∧
    ∃ l m tr, Guard.Obs (Guard.Sys.free (canonBasis (Inst.smrS1 (Cmd := Cmd)))).emits
        (Guard.eraseSys (Guard.earlyLock b f)) l m tr ∧
      ¬ Guard.Obs (Guard.Sys.free (canonBasis (Inst.smrS1 (Cmd := Cmd)))).emits
        (Guard.earlyLock b f) l m tr :=
  ⟨Guard.stall_lock hf b, Guard.early_lock_strict hf b⟩

/-- "The guarded composite is itself a guard.  Its runs are runs of `𝒦 ∘ 𝒫`
under the canonical basis (Theorem `thm:guarded-runs`(2)), so it can feed a
further stage."  Lean: `Guard.grun_composite` (every guarded composite run,
for any store system, is a run of `𝒦 ∘ 𝒫` on a prefix of `𝒫`'s run) and
`Guard.pipeline_step` (its outputs, `Guard.GEmits`, are emitted by the system
of `𝒦 ∘ 𝒫` under the canonical basis). -/
theorem «sec:proper-coordination/guard-of-guard» {I M O : Type} [PO I] [PO M] [PO O]
    {sp : Spec I M} {sk : Spec M O} (hK : sk.LiftedMono) (P : Guard.Sys sp) (K : Guard.Sys sk) :
    (∀ l m esK, Guard.GRun P.emits K l m esK →
      ∃ i es₀ σ₀ ρ', SysExec P.basis (canon sp i) es₀ σ₀ ∧ Guard.emitted es₀ <+: l ∧
        (Guard.emitted es₀).length = (Guard.outs (esK.map SEvent.erase)).length ∧
        Exec (canon (Comp.seq sp sk) i) (Guard.merge es₀ (Guard.outs (esK.map SEvent.erase))) ρ') ∧
    ∀ l', Guard.GEmits P.emits K l' → (Guard.Sys.free (canonBasis (Comp.seq sp sk))).emits l' := by
  have hC := (liftedMono_iff_commonExpansion sk).1 hK
  exact ⟨fun _ _ _ h => Guard.grun_composite hC h, fun _ h => Guard.pipeline_step hC h⟩

/-- **Corollary `cor:pipelines`** (Pipelines): "Consider a pipeline
`𝒮_n ∘ ⋯ ∘ 𝒮_1` in which `𝒮_1` has any system and `𝒮_2, …, 𝒮_n` satisfy Lifted
Monotonicity.  Every downstream stage can run with the empty basis, and every
guarded run is a run of the full composite.  Replacing the system of a
downstream stage by its commitment-erased replacement loses nothing, and gains
nothing when that stage coordinates at most once and its strategy meets the
hypotheses of Corollary `cor:empty-store`(2)."  Lean: the induction step, for
the two-stage composite `𝒮₂ ∘ 𝒮₁` as the guard of `𝒮₃`.  The outputs of the
guarded composite of `(P, K₂)` are emitted by the canonical-basis system of
`𝒮₂ ∘ 𝒮₁` (`Guard.pipeline_step`); they are chains, so the empty-basis `𝒮₃`
follows each of them (`Guard.noStore_follows`); every guarded run of `𝒮₃`
behind that upstream is a run of `(𝒮₂ ∘ 𝒮₁) ∘ … ` (`Guard.grun_composite`,
`Guard.grun_mono`); and `«cor:empty-store»` holds for `𝒮₃` with
`U = Guard.GEmits P.emits K₂`.  Lean states the step rather than an `n`-ary
pipeline type; associativity is `«sec:composition/associativity»`. -/
theorem «cor:pipelines» {I M O Q : Type} [PO I] [PO M] [PO O] [PO Q] {s1 : Spec I M}
    {s2 : Spec M O} {s3 : Spec O Q} (h2 : s2.LiftedMono) (h3 : s3.LiftedMono)
    (P : Guard.Sys s1) (K2 : Guard.Sys s2) (K3 : Guard.Sys s3) :
    (∀ l', Guard.GEmits P.emits K2 l' → (Guard.Sys.free (canonBasis (Comp.seq s1 s2))).emits l') ∧
    (∀ o os, Guard.GEmits P.emits K2 (o :: os) → ∃ esK, Guard.GRun (Guard.GEmits P.emits K2)
      (Guard.noStore s3) (o :: os) o esK) ∧
    (∀ l m esK, Guard.GRun (Guard.GEmits P.emits K2) K3 l m esK →
      ∃ i es₀ σ₀ ρ', SysExec (canonBasis (Comp.seq s1 s2)) (canon (Comp.seq s1 s2) i) es₀ σ₀ ∧
        Exec (canon (Comp.seq (Comp.seq s1 s2) s3) i)
          (Guard.merge es₀ (Guard.outs (esK.map SEvent.erase))) ρ') ∧
    (Guard.AtMostOnce (Guard.GEmits P.emits K2) K3 → Guard.Blind K3 → Guard.Live K3 →
      ∀ l m tr, Guard.Obs (Guard.GEmits P.emits K2) K3 l m tr ↔
        Guard.Obs (Guard.GEmits P.emits K2) (Guard.eraseSys K3) l m tr) := by
  have hC2 := (liftedMono_iff_commonExpansion s2).1 h2
  have hC3 := (liftedMono_iff_commonExpansion s3).1 h3
  have hstep := fun l' (h : Guard.GEmits P.emits K2 l') => Guard.pipeline_step hC2 h
  refine ⟨hstep, fun o os h => ?_, fun l m esK h => ?_, fun hirr hb hl =>
    (Guard.empty_storeU hC3 hirr hb hl).2⟩
  · obtain ⟨esK, _, _, hg, _⟩ := Guard.noStore_follows hC3 h (Guard.emits_chain (hstep _ h))
    exact ⟨esK, hg⟩
  · obtain ⟨i, es₀, σ₀, ρ', hx, _, _, hx'⟩ := Guard.grun_composite hC3 (Guard.grun_mono hstep h)
    exact ⟨i, es₀, σ₀, ρ', hx, hx'⟩

/-- "Mutexes in the store, behind the log, are another matter.  By Theorem
`thm:proper-coordination`(1) the store never needs a commitment, so each
commitment it applies is redundant once a run on outputs of `𝒫` contradicts
it.  Consider a store that executes a log of writes and locks each key, and
two writes `a` and `b` to one key.  Whether the lock is coordination depends on
the store's strategy.  If the strategy takes the lock only after the log has
placed one of them first, every log the store can still receive agrees with
that order.  The lock removes no row, so it is not a commitment, and the
composite is proper.  The locks are still taken, but they decide nothing.
Suppose instead that the strategy grants the lock to `a` at the empty log,
ahead of the log, and so seals every log in which `b` comes first.  The log
can still decide `b` first and feed the store `[b]`, which contradicts the
lock.  The lock then repeats coordination that the log already does, so the
composite is not proper.  The lock also costs behaviour.  When the log emits
`[]` and then `[b]`, the replacement follows, but the locking store, having
sealed `[b]`, cannot."  Lean: the store is `graph f` for any monotone `f` of
the log; the lock is `Guard.sealIn (Guard.bFirst b)` and the store basis
`Guard.mutexB b f`; at a nonempty log the lock is undefined
(`Guard.lock_after_log`).  The late-lock store `Guard.lateLock b f` is proper
for any upstream system (`Guard.late_lock_proper`).  With `𝒫 = Inst.smrS1`
under its canonical basis and every strategy, the early-lock store
`Guard.earlyLock b f` is redundant (`Guard.mutex_redundant`), and its
replacement follows a run it cannot (`Guard.early_lock_strict`).  The same `𝒫`
with the empty-basis store is proper. -/
theorem «sec:proper-coordination/mutex-store» {I' Cmd O : Type} [PO I'] [PO O]
    {f : Inst.Pfx Cmd → O} (hf : Monotone f) (b : Cmd) :
    (∀ σ : State (graph f), σ.cur.l ≠ [] → (Guard.sealIn (Guard.bFirst b)).app σ = none) ∧
    (∀ (sq : Spec I' (Inst.Pfx Cmd)) (P : Guard.Sys sq), Guard.Proper P (Guard.lateLock b f)) ∧
    (∃ σ : State (graph f), σ.cur = ⟨[]⟩ ∧ Exposable σ (f ⟨[]⟩) ∧
      ∃ σc, ApplySeq [Guard.sealIn (Guard.bFirst b)] σ σc ∧
        Guard.Contradicted (Guard.Sys.free (canonBasis (Inst.smrS1 (Cmd := Cmd)))).emits σ σc) ∧
    Guard.Redundant (Guard.Sys.free (canonBasis (Inst.smrS1 (Cmd := Cmd)))).emits
      (Guard.earlyLock b f) ∧
    ¬ Guard.Proper (Guard.Sys.free (canonBasis (Inst.smrS1 (Cmd := Cmd)))) (Guard.earlyLock b f) ∧
    Guard.Proper (Guard.Sys.free (canonBasis (Inst.smrS1 (Cmd := Cmd)))) (Guard.noStore (graph f)) ∧
    (∃ l m tr, Guard.Obs (Guard.Sys.free (canonBasis (Inst.smrS1 (Cmd := Cmd)))).emits
        (Guard.eraseSys (Guard.earlyLock b f)) l m tr ∧
      ¬ Guard.Obs (Guard.Sys.free (canonBasis (Inst.smrS1 (Cmd := Cmd)))).emits
        (Guard.earlyLock b f) l m tr) :=
  ⟨Guard.lock_after_log b, fun _ P => (Guard.late_lock_proper hf b P).1,
    (Guard.mutex_redundant hf b).1, (Guard.mutex_redundant hf b).2.1,
    (Guard.mutex_redundant hf b).2.2.1, (Guard.mutex_redundant hf b).2.2.2,
    Guard.early_lock_strict hf b⟩

/-- **Proposition `prop:invisible-coordination`** (Invisible coordination):
"Let `f` be monotone, and let `𝒫` emit `m` at `σ` by `Out_γ(m)`.  If every row
that `γ` removes has a row with the same input and the same image that `γ`
keeps, then `f(m)` is exposable at `f(σ)`." -/
theorem «prop:invisible-coordination» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    {f : M → O} (hf : Monotone f) {B : Basis sp} {σ τ : State sp} {γ : List (Commitment sp)}
    {m : M} (h : SysStep B σ (.output γ m) τ)
    (hinv : ∀ σc : State sp, ApplySeq γ σ σc →
      ∀ k m', σ.R k m' → ∃ m'', σc.R k m'' ∧ f m'' = f m') :
    Exposable (Guard.img f σ) (f m) :=
  Guard.invisible_step hf h hinv

/-- "Consider a store that answers each key from that key's commands, in log
order, and two commands `a` and `b` on different keys.  The log must order
them, since `[a,b]` and `[b,a]` have no common refinement.  The store's view of
both logs is the same, so the composite needs no commitment."  Lean: the
per-key view `Guard.perKey key` is monotone; with `𝒫 = Guard.abSpec a b`
(fiber `{[a,b],[b,a]}`), `[a,b]` is not exposable but its image is. -/
theorem «sec:proper-coordination/per-key» {Cmd K : Type} [DecidableEq K] (key : Cmd → K)
    {a b : Cmd} (hk : key a ≠ key b) :
    Monotone (Guard.perKey key) ∧ Guard.perKey key ⟨[a, b]⟩ = Guard.perKey key ⟨[b, a]⟩ ∧
      ¬ Exposable (canon (Guard.abSpec a b) Comp.Pt.pt) ⟨[a, b]⟩ ∧
      Exposable (canon (Guard.comp (Guard.abSpec a b) (Guard.perKey key)) Comp.Pt.pt)
        (Guard.perKey key ⟨[a, b]⟩) :=
  ⟨Guard.perKey_monotone key, Guard.perKey_swap key hk, Guard.commute_example key hk⟩

/-- **Example `ex:committed-log-composition`** (Replicated store), for any
deterministic state machine `δ` and two distinct commands: "Then `𝒫` is
non-monotone, since distinct next entries are incompatible outputs in one
fiber.  So is the key-value store `𝒦 ∘ 𝒫`, since concurrent commands ordered
oppositely give incompatible responses.  …  By Theorems `thm:guarded-runs`
and `thm:proper-coordination`, the store needs no commitment of its own,
and under the empty basis it follows every run of the log.  Because the
composite is not monotone, the log's commitments cannot be dropped.  …  By
Corollary `cor:empty-store`, if the replicas' store takes locks of its own and
the composite stays proper, the replicas can run the store with no commitments
at all."  Lean:
`𝒫 = Inst.smrS1` (`I = M = Inst.Pfx Cmd`, prefix order), `f = Inst.execF δ σ₀`
(monotone); for every system `P` of `𝒫`, with the empty-basis store; following
every run is `«sec:proper-coordination/empty-store-follows»`, and the last
sentence is `«cor:empty-store»`(2). -/
theorem «ex:committed-log-composition» {Cmd Stt R : Type} (δ : Stt → Cmd → Stt × R) (σ0 : Stt)
    {c₁ c₂ : Cmd} (hne : c₁ ≠ c₂) (P : Guard.Sys (Inst.smrS1 (Cmd := Cmd))) :
    ¬ (Inst.smrS1 (Cmd := Cmd)).LiftedMono ∧
      ¬ (Guard.comp Inst.smrS1 (Inst.execF δ σ0)).LiftedMono ∧
      Monotone (Inst.execF δ σ0) ∧ Guard.Proper P (Guard.noStore (graph (Inst.execF δ σ0))) ∧
      ∃ i m, Inst.smrS1.S i m ∧
        ¬ Exposable (canon (Guard.comp Inst.smrS1 (Inst.execF δ σ0)) i) (Inst.execF δ σ0 m) ∧
        ∀ m', Inst.smrS1.S i m' → Inst.execF δ σ0 m' = Inst.execF δ σ0 m →
          ¬ Exposable (canon Inst.smrS1 i) m' :=
  Guard.smr_proper δ σ0 hne P

/-- "There, bare reads need no commitment of their own when each response
records the log position it read from, but they do when the specification
demands the latest value (Example `ex:bare-reads`)."  Lean: with
position-tagged responses (`Inst.bareG`) every output at every state reachable
without commitment is exposable; with latest-value responses (`Inst.latestG`)
some is not, once some command `c` changes what some read `r` returns.  See
`«ex:bare-reads»` in `Paper/AppD_Composition.lean`. -/
theorem «sec:composition/bare-reads» {Cmd Stt R Rd V : Type} (δ : Stt → Cmd → Stt × R)
    (rd : Stt → Rd → V) (σ0 : Stt) :
    (∀ τ : State (Inst.bareG δ rd σ0), ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o) ∧
      ∀ {c : Cmd} {r : Rd}, rd (δ σ0 c).1 r ≠ rd σ0 r →
        ∃ τ : State (Inst.latestG δ rd σ0), ReachableCF τ ∧ ∃ o, τ.R τ.cur o ∧ ¬ Exposable τ o :=
  ⟨(exposure_boundary _).1 ((liftedMono_iff_commonExpansion _).1 (Inst.bareG_liftedMono δ rd σ0)),
    fun hc => Inst.latest_needs_store_commitment δ rd σ0 hc⟩

end Paper
end CC
