import CoordCriterion.Figures
import CoordCriterion.Appendix.Frontiers

/-!
# Paper §3: Complete CALM (`sections/complete-calm.tex`)

Statement layer for Section 3 (`sec:complete-calm`), including
Figure `fig:ambiguity-frames`.

How to read this file: open `sections/complete-calm.tex` next to it.  The
headers below are the paper's subsections, in order.  Every numbered result is
a declaration named by its LaTeX label in guillemets (`«thm:complete-calm»`);
inline claims are named `«<enclosing label>/<slug>»`.  Each docstring quotes
the paper, and, when the Lean reading differs, says how.  Proofs are
one-line pointers into the library.

Conventions are those of `Paper/S2_FunctionalCALM.lean`: `≼` is both orders,
tables are predicates `I → O → Prop`, the fiber at `i` is `sp.P i`, a set of
outputs is a predicate `O → Prop`, and finite sets of outputs or rows are
`List`s.  The two figure specifications are `Figures.Txn.spec` (panel (f): one
input `{A,B}`, modeled by `Unit`, outputs `[A,B]`/`[B,A]` under the equality
order) and `Figures.Trace.spec` (panels (g)–(h): inputs are the nonempty sets
of traced sources among `s` and `t`, `Figures.Trace.Src`, under inclusion;
outputs are route sets under inclusion, and the fiber at a set of sources is
every nonempty set of routes from those sources that contains each prefix of
its routes).
-/

namespace CC.Paper

open CC CC.CALM

/-! ## Nondeterministic specs and Lifted Monotonicity
(`sec:relational-specifications`, `sec:ambiguity-story`,
`sec:lifted-monotonicity`) -/

  /-- Fig. `fig:ambiguity-frames`(f): "(f) After `[A,B]` … no remaining row extends the removed one: a commitment."  After
  `output([A,B])` only `({A,B},[A,B])` remains; `[B,A]` is in `Excluded_o`,
  requires a commitment, and is not subsumed (no row extends both). -/
theorem «fig:ambiguity-frames/f» :
    (∀ k o, outputTable (canon Figures.Txn.spec ()) .ab k o ↔ o = .ab) ∧
      Excluded (canon Figures.Txn.spec ()) .ab () .ba ∧
      ¬ Subsumed (canon Figures.Txn.spec ()) .ab () .ba ∧
      ¬ ∃ u, Figures.Txn.spec.P () u ∧ Figures.Txn.TOut.ab ≼ u ∧ Figures.Txn.TOut.ba ≼ u :=
  ⟨Figures.Txn.after_ab, Figures.Txn.ba_excluded⟩

/-- Fig. `fig:ambiguity-frames`(g): "(g) After `{s→s1}` at input `{s}` … each
removed row is extended by a remaining one at its input: an output
subsumption."  The rows shown are those whose input extends `{s}`: the five
route sets at `{s}` and the eleven at `{s,t}` (`fiber_s`, `fiber_st`).  The
remaining rows are the route sets containing `s→s1`, at both inputs; the
removed ones are `{s→h}` and `{s→h,s→h→s2}` at both inputs and, at `{s,t}`,
`{t→s2}`, `{s→h,t→s2}` and `{s→h,s→h→s2,t→s2}`; each is in `Subsumed_o`,
nothing is in `Excluded_o`, so `{s→s1}` is a legal output. -/
theorem «fig:ambiguity-frames/g» :
    (∀ x, Figures.Trace.inFib .s x ↔ (x = Figures.Trace.rS1 ∨ x = Figures.Trace.rH ∨
        x = Figures.Trace.rH2 ∨ x = Figures.Trace.rS1H ∨ x = Figures.Trace.rAll)) ∧
      (∀ k x, outputTable (canon Figures.Trace.spec .s) Figures.Trace.rS1 k x ↔
        ((k = .s ∨ k = .st) ∧ (x = Figures.Trace.rS1 ∨ x = Figures.Trace.rS1H ∨
            x = Figures.Trace.rAll)) ∨
          (k = .st ∧ (x = Figures.Trace.rS1T ∨ x = Figures.Trace.rS1HT ∨
            x = Figures.Trace.rAllT))) ∧
      (∀ k x, ((canon Figures.Trace.spec .s).R k x ∧
          ¬ outputTable (canon Figures.Trace.spec .s) Figures.Trace.rS1 k x) ↔
        ((k = .s ∨ k = .st) ∧ (x = Figures.Trace.rH ∨ x = Figures.Trace.rH2)) ∨
          (k = .st ∧ (x = Figures.Trace.rT ∨ x = Figures.Trace.rHT ∨ x = Figures.Trace.rH2T))) ∧
      ((∀ k x, (canon Figures.Trace.spec .s).R k x → ¬ Figures.Trace.rS1 ≼ x →
          Subsumed (canon Figures.Trace.spec .s) Figures.Trace.rS1 k x) ∧
        (¬ ∃ k x, Excluded (canon Figures.Trace.spec .s) Figures.Trace.rS1 k x) ∧
        Exposable (canon Figures.Trace.spec .s) Figures.Trace.rS1) :=
  ⟨Figures.Trace.fiber_s, Figures.Trace.after_s1, Figures.Trace.removed,
    Figures.Trace.removed_subsumed⟩

/-- Fig. `fig:ambiguity-frames`(h): "(h) After `input({s,t})` … the emitted
route set `{s→s1}` keeps output extensions at the new input."  From the state of
panel (g), `input({s,t})` is a legal input event; the rows that remain are the
six route sets at `{s,t}` that contain `s→s1`, and the rows at `{s}` are lost. -/
theorem «fig:ambiguity-frames/h» :
    Step Figures.Trace.stateG (.input .st) Figures.Trace.stateH ∧
      ∀ k x, Figures.Trace.stateH.R k x ↔
        (k = .st ∧ (x = Figures.Trace.rS1 ∨ x = Figures.Trace.rS1H ∨ x = Figures.Trace.rAll ∨
          x = Figures.Trace.rS1T ∨ x = Figures.Trace.rS1HT ∨ x = Figures.Trace.rAllT)) :=
  Figures.Trace.after_input

/-- Fig. `fig:ambiguity-frames`, caption: "An output is a nonempty set of
routes from the traced sources that contains each prefix of its routes."  The
fiber at `{s,t}` is the eleven route sets panel (g) prints. -/
theorem «fig:ambiguity-frames/caption» :
    ∀ x, Figures.Trace.inFib .st x ↔ (x = Figures.Trace.rS1 ∨ x = Figures.Trace.rH ∨
      x = Figures.Trace.rH2 ∨ x = Figures.Trace.rS1H ∨ x = Figures.Trace.rAll ∨
      x = Figures.Trace.rT ∨ x = Figures.Trace.rS1T ∨ x = Figures.Trace.rHT ∨
      x = Figures.Trace.rH2T ∨ x = Figures.Trace.rS1HT ∨ x = Figures.Trace.rAllT) :=
  Figures.Trace.fiber_st

/-- §3.1 "Commitment and directedness": "In panel (f) … emitting one
requires an *commitment* that removes the other while the input stays
legal: emitting `[A,B]` excludes `[B,A]`."  `[A,B]` is not a legal output,
every system output event emitting it applies `x_[A,B]` (which must then be
in the system's basis), and the
commitment `x_[A,B]` applies, keeping `[A,B]` and removing `[B,A]`. -/
theorem «sec:ambiguity-story/commitment» :
    (¬ Exposable (canon Figures.Txn.spec ()) .ab ∧
        ∀ (B : CommitmentBasis Figures.Txn.spec) τ,
          SysStep B (canon Figures.Txn.spec ()) (.output .ab) τ →
            B (canonicalCommitment .ab)) ∧
      ((canonicalCommitment (sp := Figures.Txn.spec) .ab).app (canon Figures.Txn.spec ()) =
          some (commitmentState (canon Figures.Txn.spec ()) .ab (Figures.Txn.sR .ab)) ∧
        (commitmentState (canon Figures.Txn.spec ()) .ab (Figures.Txn.sR .ab)).R () .ab ∧
        ¬ (commitmentState (canon Figures.Txn.spec ()) .ab (Figures.Txn.sR .ab)).R () .ba) :=
  ⟨Figures.Txn.ab_not_exposable, Figures.Txn.commitment_applies⟩

  /-- §3.1: "An output event can thus remove rows in two ways: by commitment …
  or by subsuming outputs … Subsuming is not commitment."  The rows ruled out
  by `o` are exactly `Subsumed_o ∪ Excluded_o`, and `o` is a legal output (no
  commitment) iff `Excluded_o` is empty. -/
theorem «sec:ambiguity-story/three-ways» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) :
    (∀ k x, (σ.R k x ∧ ¬ outputTable σ o k x) ↔
        (Subsumed σ o k x ∨ Excluded σ o k x)) ∧
      (Exposable σ o ↔ ∀ k x, ¬ Excluded σ o k x) :=
  ⟨ruledOut_iff σ o, exposable_iff_no_commitment σ o⟩

/-- §3.1: "Two transaction scheduling runs that emit `[A,B]` and `[B,A]` fail
it": they are not confluent at `{A,B}`; the specification is neither directed
nor monotone nor consistent. -/
theorem «sec:ambiguity-story/transactions-fail» :
    ¬ ConfluentAt [outState (canon Figures.Txn.spec ()) .ab (Figures.Txn.sR _),
        outState (canon Figures.Txn.spec ()) .ba (Figures.Txn.sR _)] () ∧
      (¬ CompatibleIn (Figures.Txn.spec.P ()) [.ab, .ba] ∧ ¬ Figures.Txn.spec.DirectedOutputs ∧
        ¬ Figures.Txn.spec.LiftedMono ∧ ¬ Figures.Txn.spec.Consistent) :=
  ⟨Figures.Txn.runs_not_confluent, Figures.Txn.not_monotone⟩


/-- **Def. `def:relational-specification`** (I/O specification).
"`Spec = (I,≼,O,≼,P)`, `P ⊆ I × O`, where `(I,≼)` and
`(O,≼)` are partially ordered sets.  `P` is the specification's *table of
possibilities* and is total on `I`; a row `(i,o) ∈ P` is a possible
input/output pair.  As in Section `sec:functional-specifications`, the fiber
at `i` is `P(i) = {o ∈ O : (i,o) ∈ P}`, and it may contain several outputs.  A functional
specification is the special case `P(i) = {f(i)}`."

Lean: `Spec I O` (orders are the `PO` instances); the fiber `P(i)` is
`sp.P i`; functional is `Spec.Functional`. -/
abbrev «def:relational-specification» (I O : Type) [PO I] [PO O] := Spec I O

/-- **Eq. `eq:relational-specification`**: "`Spec = (I,≼,O,≼,P)`,
`P ⊆ I × O`."  The orders are the `PO` instances; the relation `P ⊆ I × O` is a
`Table I O` (a predicate on pairs).  A `Spec I O` is such a table together with
totality: this is the `P` component. -/
abbrev «eq:relational-specification» (I O : Type) [PO I] [PO O] (sp : Spec I O) : Table I O :=
  sp.P

/-- **Eq. `eq:fiber`**: "`P(i) = {o ∈ O : (i,o) ∈ P}`", as a predicate on
outputs. -/
abbrev «eq:fiber» {I O : Type} [PO I] [PO O] (sp : Spec I O) (i : I) : O → Prop :=
  fun o => sp.P i o

/-- Def. `def:relational-specification`, "nondeterministic": some fiber has
two distinct outputs.  (The library has no named notion; this is the reading.)
Nondeterminism is the negation of the functional dependency. -/
theorem «def:relational-specification/nondeterministic» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    (∃ i o o', sp.P i o ∧ sp.P i o' ∧ o ≠ o') ↔ ¬ sp.Functional :=
  ⟨fun ⟨i, o, o', h, h', hne⟩ hf => hne (hf i o o' h h'),
   fun hn => Classical.byContradiction fun h =>
     hn fun i o o' ho ho' => Classical.byContradiction fun hne => h ⟨i, o, o', ho, ho', hne⟩⟩

/-- **Def. `def:nondeterministic`** (Nondeterministic I/O specification).  "An
I/O specification is *nondeterministic* when some fiber contains more than one
output.  Specification nondeterminism describes which results are permitted, not
how a system chooses among them, and does not by itself imply a
commitment."  Lean reading: there exist `i, o, o'` with `o ≠ o'` and both in
`sp.P i`. -/
abbrev «def:nondeterministic» {I O : Type} [PO I] [PO O] (sp : Spec I O) : Prop :=
  ∃ i o o', sp.P i o ∧ sp.P i o' ∧ o ≠ o'

/-- **Def. `def:relational-monotonicity`** (Relational Monotonicity).
"`i ≼ j, o ∈ P(i) ⟹ ∃ u ∈ P(j) : o ≼ u`." -/
abbrev «def:relational-monotonicity» {I O : Type} [PO I] [PO O] (sp : Spec I O) : Prop :=
  sp.RelMono

/-- **Eq. `eq:relational-monotonicity`**:
"`i ≼ j, o ∈ P(i) ⟹ ∃ u ∈ P(j) : o ≼ u`" is the definition of
`Spec.RelMono`. -/
theorem «eq:relational-monotonicity» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    sp.RelMono ↔ ∀ i j o, i ≼ j → sp.P i o → ∃ u, sp.P j u ∧ o ≼ u :=
  Iff.rfl
/-- After Def. `def:relational-monotonicity`: "In the traceroute spec, tracing
from a second source `t` moves the input from `{s}` to `{s,t}` (Figure
`fig:ambiguity-frames`(h)).  Every route set permitted at `{s}` is still
permitted at `{s,t}`, so Relational Monotonicity holds."  Lean: the fibers grow
with the input (`fib_mono`), and the traceroute spec satisfies Relational
Monotonicity. -/
theorem «sec:lifted-monotonicity/traceroute-relational» :
    (∀ x, Figures.Trace.inFib .s x → Figures.Trace.inFib .st x) ∧
      Figures.Trace.spec.RelMono :=
  ⟨fun x hx => Figures.Trace.fib_mono x (by decide) hx, Figures.Trace.directed.2.1⟩

/-- After Def. `def:relational-monotonicity`: "For singleton fibers this is
functional monotonicity." -/
theorem «def:relational-monotonicity/functional» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) : sp.RelMono ↔ sp.MonotoneF :=
  relMono_iff_monoF hf

/-- "For a set `F ⊆ O` of outputs, outputs `o₁,…,o_k` are *compatible in
`F`* if some `u ∈ F` extends all of them."  Lean: `CompatibleIn F X`, with
the outputs as a list `X`. -/
abbrev «sec:lifted-monotonicity/compatible» {O : Type} [PO O] (F : O → Prop) (X : List O) : Prop :=
  CompatibleIn F X

/-- **Def. `def:fiber-directedness`** (Directed fiber, directed fibers).  "A
fiber `F ⊆ O` is *directed* when every nonempty finite `X ⊆ F` is compatible in
`F`.  A spec has *directed fibers* when every fiber is directed."  Lean: `F` is
directed iff `JointLift F F`; the second sentence is `«def:directed-outputs»`. -/
abbrev «def:fiber-directedness» {O : Type} [PO O] (F : O → Prop) : Prop :=
  JointLift F F

/-- Def. `def:fiber-directedness` (label `def:directed-outputs`), second
sentence: "A spec has *directed fibers* when every fiber is directed."  Lean: `Spec.DirectedOutputs` is `∀ i, JointLift (sp.P i)
(sp.P i)`. -/
abbrev «def:directed-outputs» {I O : Type} [PO I] [PO O] (sp : Spec I O) : Prop :=
  sp.DirectedOutputs

/-- After Def. `def:fiber-directedness`: "A singleton fiber is trivially
directed." -/
theorem «def:fiber-directedness/singleton» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) : sp.DirectedOutputs :=
  functional_directed hf

/-- "Directedness is more permissive than a join-semilattice.  It asks only that
each finite set of outputs in a fiber have some common output extension within
the fiber, while a join-semilattice requires a least one.  For example, the
fiber `{{a},{b},{a,b,c},{a,b,d},{a,b,c,d}}` under inclusion is directed, since
`{a,b,c,d}` extends every member, but `{a}` and `{b}` have no least common
output extension: `{a,b,c}` and `{a,b,d}` are both minimal."  The fiber is the
type `F5` (all of it); the common output extensions of `{a}` and `{b}` are
`{a,b,c}`, `{a,b,d}` and `{a,b,c,d}`; the first two are minimal and
incomparable, so none is least.  "A join-semilattice requires a least one" is
the definition of a join (prose). -/
theorem «sec:lifted-monotonicity/directed-example» :
    JointLift (fun _ : F5 => True) (fun _ : F5 => True) ∧
      (∀ u, (F5.a ≼ u ∧ F5.b ≼ u) ↔ (u = .abc ∨ u = .abd ∨ u = .abcd)) ∧
      (¬ (F5.abc ≼ F5.abd) ∧ ¬ (F5.abd ≼ F5.abc) ∧
        (∀ u, F5.a ≼ u → F5.b ≼ u → u ≼ F5.abc → u = F5.abc) ∧
        (∀ u, F5.a ≼ u → F5.b ≼ u → u ≼ F5.abd → u = F5.abd)) ∧
      CompatibleIn (fun _ : F5 => True) [F5.abc, F5.abd] ∧
      ¬ ∃ u : F5, (F5.a ≼ u ∧ F5.b ≼ u) ∧ ∀ v : F5, F5.a ≼ v → F5.b ≼ v → u ≼ v := by
  refine ⟨f5_directed, f5_common_refinements, f5_minimal_incomparable, f5_compatible, ?_⟩
  rintro ⟨u, ⟨ha, hb⟩, hl⟩
  have h1 := f5_minimal_incomparable.2.2.1 u ha hb (hl _ (by decide) (by decide))
  have h2 := f5_minimal_incomparable.2.2.2 u ha hb (hl _ (by decide) (by decide))
  exact absurd (h1.symm.trans h2) (by decide)

/-- "A singleton fiber is trivially directed.  Each traceroute fiber of Figure
`fig:ambiguity-frames`(g) is directed too: the union of finitely many permitted
route sets is itself a permitted route set, and it contains each of them.  The
two transaction orders in panel (f), by contrast, are incompatible."  Lean: the
union of two permitted route sets is permitted and extends both (finitely many
by induction, packaged as `DirectedOutputs`). -/
theorem «sec:lifted-monotonicity/figure-fibers» :
    (∀ X x y, Figures.Trace.inFib X x → Figures.Trace.inFib X y →
        Figures.Trace.inFib X (x.union y) ∧ x ≼ x.union y ∧ y ≼ x.union y) ∧
      Figures.Trace.spec.DirectedOutputs ∧
      ¬ CompatibleIn (Figures.Txn.spec.P ()) [.ab, .ba] :=
  ⟨Figures.Trace.union_mem, Figures.Trace.directed.1, Figures.Txn.not_monotone.1⟩

/-- **Eq. `eq:joint-output-order`** (joint refinement lift).  "To state both
requirements at once, we lift `≼` from outputs to a relation on sets of
outputs.  For nonempty `A,B ⊆ O`, `A ⊑ B ⟺ every nonempty finite X ⊆ A is
compatible in B` … The lift compares two sets of outputs; Lifted Monotonicity,
defined next, is the property that fibers rise in this relation as input
grows."  Lean:
`JointLift A B`, with `X` a nonempty list. -/
abbrev «eq:joint-output-order» {O : Type} [PO O] (A B : O → Prop) : Prop :=
  JointLift A B

/-- **Def. `def:lifted-monotonicity`** (Lifted Monotonicity).  "for every
`i ≼ j` and every nonempty finite `X ⊆ P(i)`, some `u ∈ P(j)` extends every
member of `X`; that is, … `i ≼ j ⟹ P(i) ⊑ P(j)`." -/
abbrev «def:lifted-monotonicity» {I O : Type} [PO I] [PO O] (sp : Spec I O) : Prop :=
  sp.LiftedMono

/-- **Eq. `eq:lifted-monotonicity`**: "`i ≼ j ⟹ P(i) ⊑ P(j)`" is the
definition of `Spec.LiftedMono`, with `⊑` the joint refinement lift `JointLift`. -/
theorem «eq:lifted-monotonicity» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    sp.LiftedMono ↔ ∀ i j, i ≼ j → JointLift (sp.P i) (sp.P j) :=
  Iff.rfl
/-- After Def. `def:lifted-monotonicity`: "With singleton fibers, Lifted
Monotonicity is functional monotonicity." -/
theorem «def:lifted-monotonicity/functional» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) : sp.LiftedMono ↔ sp.MonotoneF :=
  liftedMono_iff_monoF hf

/-- After Def. `def:lifted-monotonicity`: "In general it is exactly Relational
Monotonicity together with directed fibers.  Taking `X` to be a single output
gives Relational Monotonicity, and taking `j=i` gives directed fibers.
Conversely, take `i ≼ j` and a finite nonempty `X ⊆ P(i)`.  Relational
Monotonicity gives each member of `X` an output extension in `P(j)`, and since
`P(j)` is directed, those output extensions have a common output extension
there." -/
theorem «def:lifted-monotonicity/relmono-directed» {I O : Type} [PO I] [PO O]
    (sp : Spec I O) : sp.LiftedMono ↔ sp.RelMono ∧ sp.DirectedOutputs :=
  liftedMono_iff_relMono_directed sp

/-- After Def. `def:lifted-monotonicity`: "Lifted Monotonicity therefore
constrains a spec even at `j=i`, where it asks that each fiber be directed.  The
transaction fiber of Figure `fig:ambiguity-frames`(f) is not, so that spec
fails Lifted Monotonicity already at `j=i`."  Lean: at `j = i` the joint
refinement lift `P(i) ⊑ P(i)` is by definition directedness of `P(i)`
(Def. `def:fiber-directedness`); the panel (f) fiber `{[A,B],[B,A]}` is not
directed, so `P(i) ⊑ P(i)` fails at `i = {A,B}`. -/
theorem «def:lifted-monotonicity/at-j-eq-i» :
    (∀ (O : Type) [PO O] (A : O → Prop),
        JointLift A A ↔ ∀ X : List O, X ≠ [] → (∀ x ∈ X, A x) → CompatibleIn A X) ∧
      ¬ JointLift (Figures.Txn.spec.P ()) (Figures.Txn.spec.P ()) :=
  ⟨fun _ _ _ => Iff.rfl, fun h => Figures.Txn.not_monotone.2.1 fun _ => h⟩

/-- After Def. `def:lifted-monotonicity`: "In powerdomain terms, Relational
Monotonicity is monotonicity of `i ↦ P(i)` under the Hoare preorder, which
asks only that each output in `A` have an output extension in `B`.  The
joint refinement lift asks that every finite set of them have a common one,
and the two agree when `B` is directed."  Lean: the Hoare preorder is `Front.HoareLe A B`
(`∀ a ∈ A, ∃ b ∈ B, a ≼ b`); (1) Relational Monotonicity is Hoare
monotonicity of the fibers; (2) the joint refinement lift implies the Hoare preorder;
(3) for directed `B` (`JointLift B B`, Def. `def:fiber-directedness`) the two
coincide. -/
theorem «def:lifted-monotonicity/hoare» {I O : Type} [PO I] [PO O] :
    (∀ sp : Spec I O, sp.RelMono ↔ ∀ i j, i ≼ j → Front.HoareLe (sp.P i) (sp.P j)) ∧
      (∀ A B : O → Prop, JointLift A B → Front.HoareLe A B) ∧
      (∀ A B : O → Prop, JointLift B B → (Front.HoareLe A B ↔ JointLift A B)) :=
  ⟨Front.relMono_iff_hoare, fun _ _ => Front.jointLift_hoare,
   fun _ _ => Front.hoare_iff_jointLift_of_directed⟩

/-- After Def. `def:lifted-monotonicity`: "Unlike the Hoare preorder, the joint
refinement lift is not reflexive: `A ⊑ A` holds only when `A` is directed."
Lean: the Hoare preorder is reflexive; `A ⊑ A` is by definition directedness
of `A` (Def. `def:fiber-directedness`); the panel (f) fiber `{[A,B],[B,A]}` is
a set with `¬ A ⊑ A`. -/
theorem «def:lifted-monotonicity/not-reflexive» :
    (∀ (O : Type) [PO O] (A : O → Prop), Front.HoareLe A A) ∧
      (∀ (O : Type) [PO O] (A : O → Prop),
        JointLift A A ↔ ∀ X : List O, X ≠ [] → (∀ x ∈ X, A x) → CompatibleIn A X) ∧
      ¬ JointLift (Figures.Txn.spec.P ()) (Figures.Txn.spec.P ()) :=
  ⟨fun _ _ A => Front.HoareLe.refl A, fun _ _ _ => Iff.rfl,
   fun h => Figures.Txn.not_monotone.2.1 fun _ => h⟩

/-- Before Def. `def:common-expansion-condition`: "In the traceroute spec, one
run may trace from `s` and emit `{s→s1}`, while another traces from a second
source `t` and emits `{t→s2}`.  At their common input extension `{s,t}`, the
route set `{s→s1, t→s2}` is a common output extension of both."  Lean: the
concrete instance (`Figures.Trace.common_extension_example`), and in general
the union of any route set permitted at `{s}` with any permitted at `{t}`
(`Figures.Trace.common_extension`).  The CIDR version quotes the same
sentences. -/
theorem «sec:lifted-monotonicity/traceroute-common-extension» (x y : Figures.Trace.RS)
    (hx : Figures.Trace.inFib .s x) (hy : Figures.Trace.inFib .t y) :
    (Figures.Trace.inFib .s Figures.Trace.rS1 ∧ Figures.Trace.inFib .t Figures.Trace.rT ∧
      Figures.Trace.inFib .st Figures.Trace.rS1T ∧
      Figures.Trace.rS1 ≼ Figures.Trace.rS1T ∧ Figures.Trace.rT ≼ Figures.Trace.rS1T ∧
      Figures.Trace.rS1.union Figures.Trace.rT = Figures.Trace.rS1T) ∧
    (Figures.Trace.inFib .st (x.union y) ∧ x ≼ x.union y ∧ y ≼ x.union y) :=
  ⟨Figures.Trace.common_extension_example, Figures.Trace.common_extension x y hx hy⟩

/-- **Def. `def:common-expansion-condition`** (Common-extension condition).
"For every finite set of rows `(i₁,o₁),…,(i_k,o_k)` of `P` and every common
input extension `j` of `i₁,…,i_k`, some `u ∈ P(j)` extends every `o_r`."  Lean:
`Spec.CommonExpansion`, the rows as a list. -/
abbrev «def:common-expansion-condition» {I O : Type} [PO I] [PO O] (sp : Spec I O) : Prop :=
  sp.CommonExpansion

/-- After Def. `def:common-expansion-condition`: "For the empty set of rows
the condition asks only that `P(j)` be nonempty, which follows from `P` being
total on `I`." -/
theorem «def:common-expansion-condition/empty» {I O : Type} [PO I] [PO O]
    (sp : Spec I O) (j : I) :
    (∃ u, sp.P j u ∧ ∀ r ∈ ([] : List (I × O)), r.2 ≼ u) :=
  let ⟨u, hu⟩ := sp.total j; ⟨u, hu, fun _ h => nomatch h⟩

/-- **Prop. `prop:common-expansion-form`** (Common-extension form of Lifted
Monotonicity).  "An I/O specification satisfies Lifted
Monotonicity if and only if it satisfies the common-extension condition." -/
theorem «prop:common-expansion-form» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    sp.LiftedMono ↔ sp.CommonExpansion :=
  liftedMono_iff_commonExpansion sp

/-! ## Lifted output events (`sec:lifted-output-events`)

The body gives an informal summary; the formal definitions
(`eq:output-subsumptions`, `eq:commitment-removals`,
`def:lifted-output-event`, `eq:canonical-commitment-relational`), the remarks after them, and
Prop. `prop:exposability` with `eq:safe-exposure` are in Appendix
`app:lifted-output-events`, and their entries in
`Paper/AppC_CommitmentBases.lean`. -/

  /-! At an input `k`, the canonical commitment removes only rows in
  `Excluded_o(k)`.  Rows in `Subsumed_o(k)` are removed separately by output
  subsumption and have a kept output extension at `k`, so they cannot cause the
  event to rule out `k`.  This is formalized by
  `«def:canonical-commitment/subsumed-keeps-fiber»`. -/

  /-- §3.2: "Legality is defined as before: `o` is a legal output when
  `output(o)` applies no commitment, that is, when `Excluded_o` is empty.  With
  several outputs at one input, this is more permissive than in the functional
  case, since an output event may remove rows by output subsumption without a
  commitment."

  In the functional case, `Subsumed_o` is empty, so every removed row belongs
to `Excluded_o`; at each such input, the event excludes its sole output and
therefore the input itself. -/
theorem «sec:lifted-output-events/functional» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} (hf : sp.Functional) (σ : State sp) (o : O) (k : I) (x : O) :
    ¬ Subsumed σ o k x :=
  functional_subsumed_empty hf σ o k x

/-! ## The Complete CALM theorem (`sec:complete-calm-theorem`) -/

/-- "Specification states, input events, runs, commitment-free runs, and
consistency are defined as before.  The results of Section `sec:executions`
use output events only through Equation `eq:output-action`, which lifted
output events still satisfy, so the rows-remaining lemma and the Survivor test
apply unchanged." In Lean there is
nothing to lift: the transition system, Lemma `lem:run-residual` and Prop.
`prop:confluence` are stated for arbitrary (relational) specifications from the
start; this
restates the lemma for the record. -/
theorem «sec:complete-calm-theorem/lift-unchanged» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} {i : I} {es : List (Event I O)} {τ : State sp}
    (hx : Exec (canon sp i) es τ) :
    ∀ k u, τ.R k u ↔ (sp.P k u ∧ τ.cur ≼ k ∧ ∀ o ∈ outs es, o ≼ u) :=
  run_residual hx

/-- **Theorem `thm:complete-calm`** (Complete CALM).  "An ordered
specification is consistent if and only if it satisfies Lifted Monotonicity,
equivalently the common-extension condition." -/
theorem «thm:complete-calm» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    (sp.Consistent ↔ sp.LiftedMono) ∧ (sp.Consistent ↔ sp.CommonExpansion) :=
  ⟨complete_calm sp, complete_calm_commonExpansion sp⟩

/-- **Prop. `prop:exposure-boundary`** (No-commitment test).  "An ordered
specification satisfies Lifted Monotonicity if and only if every output at
every state reachable without commitment is a legal output."  The proof sketch
goes through the common-extension condition (Prop.
`prop:common-expansion-form`); `«prop:exposure-boundary/common-expansion»`
is that form. -/
theorem «prop:exposure-boundary» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    sp.LiftedMono ↔
      ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  (liftedMono_iff_commonExpansion sp).trans (exposure_boundary sp)

/-- Prop. `prop:exposure-boundary`, proof sketch: "If the common-extension
condition holds, the spec is consistent by Complete CALM. … Conversely, if
every such output is legal, applying Proposition `prop:exposability` at
canonical states, one row at a time, builds the common output extension that
the condition asks for."  The common-extension
form of the proposition. -/
theorem «prop:exposure-boundary/common-expansion» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    sp.CommonExpansion ↔
      ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  exposure_boundary sp

/-- After Prop. `prop:exposure-boundary`: "For functional specs, Lifted
Monotonicity and the common-extension condition are both functional
monotonicity, so Complete CALM and Proposition `prop:exposure-boundary` reduce to Functional
CALM and Proposition `prop:functional-exposure-boundary`." -/
theorem «prop:exposure-boundary/functional» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) :
    (sp.LiftedMono ↔ sp.MonotoneF) ∧ (sp.CommonExpansion ↔ sp.MonotoneF) :=
  ⟨liftedMono_iff_monoF hf, commonExpansion_iff_monoF hf⟩

end CC.Paper
