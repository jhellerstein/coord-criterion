import CoordCriterion.Figures

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
tables are predicates `I → O → Prop`, the fiber at `i` is `sp.S i`, a set of
outputs is a predicate `O → Prop`, and finite sets of outputs or rows are
`List`s.  The two figure specifications are `Figures.Txn.spec` (panel (f): one
input `{A,B}`, modeled by `Unit`, outputs `[A,B]`/`[B,A]` under the equality
order) and `Figures.Trace.spec` (panel (g): one input `i`, modeled by `Unit`,
the five printed route sets under inclusion).
-/

namespace CC.Paper

open CC CC.CALM

/-! ## Output choice by example (`sec:ambiguity-story`) -/

/-- Fig. `fig:ambiguity-frames`(f): "Transaction ordering, after outputting
`[A,B]` … no remaining row refines the removed one: a commitment."  After
`output([A,B])` only `({A,B},[A,B])` remains; `[B,A]` is in `Rejected_o` (a
choice), neither sealed (the input keeps `[A,B]`) nor retired (no row refines
both). -/
theorem «fig:ambiguity-frames/f» :
    (∀ k o, outputTable (canon Figures.Txn.spec ()) .ab k o ↔ o = .ab) ∧
      Rejected (canon Figures.Txn.spec ()) .ab () .ba ∧
      ¬ Sealed (canon Figures.Txn.spec ()) .ab () .ba ∧
      ¬ Retired (canon Figures.Txn.spec ()) .ab () .ba ∧
      ¬ ∃ u, Figures.Txn.spec.S () u ∧ Figures.Txn.TOut.ab ≼ u ∧ Figures.Txn.TOut.ba ≼ u :=
  ⟨Figures.Txn.after_ab, Figures.Txn.ba_rejected⟩

/-- Fig. `fig:ambiguity-frames`(g): "Traceroute, after outputting
`{s→s1}` … each removed row is refined by a remaining one: an output
retirement."  The remaining rows are `{s→s1}`, `{s→s1,s→a}`,
`{s→s1,s→a,s→a→s2}`; the removed `{s→a}` and `{s→a,s→a→s2}` are in
`Retired_o`; nothing is sealed or rejected, so `{s→s1}` is exposable. -/
theorem «fig:ambiguity-frames/g» :
    (∀ x, outputTable (canon Figures.Trace.spec ()) Figures.Trace.rS1 () x ↔
        (x = Figures.Trace.rS1 ∨ x = Figures.Trace.rS1A ∨ x = Figures.Trace.rAll)) ∧
      ((∀ x, (canon Figures.Trace.spec ()).R () x →
          (¬ outputTable (canon Figures.Trace.spec ()) Figures.Trace.rS1 () x ↔
            (x = Figures.Trace.rA ∨ x = Figures.Trace.rA2))) ∧
        Retired (canon Figures.Trace.spec ()) Figures.Trace.rS1 () Figures.Trace.rA ∧
        Retired (canon Figures.Trace.spec ()) Figures.Trace.rS1 () Figures.Trace.rA2 ∧
        (¬ ∃ k x, Sealed (canon Figures.Trace.spec ()) Figures.Trace.rS1 k x) ∧
        (¬ ∃ k x, Rejected (canon Figures.Trace.spec ()) Figures.Trace.rS1 k x) ∧
        Exposable (canon Figures.Trace.spec ()) Figures.Trace.rS1) :=
  ⟨Figures.Trace.after_s1, Figures.Trace.removed_retired⟩

/-- §3.1 "Output choice and directedness": "In panel (f) … emitting one
requires a *choice commitment* that removes the other while the input stays
legal: emitting `[A,B]` chooses it over `[B,A]`."  `[A,B]` is not exposable,
every legal system output event emitting it carries a commitment, and the
choice `c_[A,B]` applies, keeping `[A,B]` and removing `[B,A]`. -/
theorem «sec:ambiguity-story/choice» :
    (¬ Exposable (canon Figures.Txn.spec ()) .ab ∧
        ∀ (B : Basis Figures.Txn.spec) (γ : List (Commitment Figures.Txn.spec)) τ,
          SysStep B (canon Figures.Txn.spec ()) (.output γ .ab) τ → γ ≠ []) ∧
      ((choiceC (sp := Figures.Txn.spec) .ab).app (canon Figures.Txn.spec ()) =
          some (cmChooseState (canon Figures.Txn.spec ()) .ab) ∧
        (cmChooseState (canon Figures.Txn.spec ()) .ab).R () .ab ∧
        ¬ (cmChooseState (canon Figures.Txn.spec ()) .ab).R () .ba) :=
  ⟨Figures.Txn.ab_not_exposable, Figures.Txn.choice_applies⟩

/-- §3.1: "An output event can thus remove rows in three ways: by sealing
inputs …; by retiring outputs …; or by choosing among outputs … sealing and
choosing are commitments, retiring is not."  The rows ruled out by `o` are
exactly `Sealed_o ∪ Retired_o ∪ Rejected_o`, and `o` is exposable (no
commitment) iff `Sealed_o` and `Rejected_o` are empty. -/
theorem «sec:ambiguity-story/three-ways» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) :
    (∀ k x, (σ.R k x ∧ ¬ outputTable σ o k x) ↔
        (Sealed σ o k x ∨ Retired σ o k x ∨ Rejected σ o k x)) ∧
      (Exposable σ o ↔ (∀ k x, ¬ Sealed σ o k x) ∧ (∀ k x, ¬ Rejected σ o k x)) :=
  ⟨ruledOut_iff σ o, exposable_iff_no_commitment σ o⟩

/-- §3.1: "Two transaction scheduling runs that emit `[A,B]` and `[B,A]` fail
it": they are not confluent at `{A,B}`; the specification is neither directed
nor monotone nor consistent. -/
theorem «sec:ambiguity-story/transactions-fail» :
    ¬ ConfluentAt [outState (canon Figures.Txn.spec ()) .ab (Figures.Txn.sR _),
        outState (canon Figures.Txn.spec ()) .ba (Figures.Txn.sR _)] () ∧
      (¬ CompatibleIn (Figures.Txn.spec.S ()) [.ab, .ba] ∧ ¬ Figures.Txn.spec.DirectedOutputs ∧
        ¬ Figures.Txn.spec.LiftedMono ∧ ¬ Figures.Txn.spec.Consistent) :=
  ⟨Figures.Txn.runs_not_confluent, Figures.Txn.not_monotone⟩

/-- §3.1: "two traceroute runs that emit different route sets pass it, since
their union survives in both." -/
theorem «sec:ambiguity-story/traceroute-passes» (x y : Figures.Trace.RS)
    (hx : Figures.Trace.inFib x) (hy : Figures.Trace.inFib y) :
    (outState (canon Figures.Trace.spec ()) x ((Figures.Trace.canonR x).2 hx)).R () (x.union y) ∧
      (outState (canon Figures.Trace.spec ()) y ((Figures.Trace.canonR y).2 hy)).R () (x.union y) :=
  Figures.Trace.union_survives x y hx hy

/-! ## Relational specifications and states (`sec:relational-specifications`) -/

/-- **Def. `def:relational-specification`** (Ordered relational
specification).  "`Spec = (I,≼,O,≼,S)`, `S ⊆ I × O`, where `(I,≼)` and
`(O,≼)` are partially ordered sets and `S` is total on `I` … The fiber
`S(i) = {o ∈ O : (i,o) ∈ S}` … may now contain several outputs; the
specification is *ambiguous* when some fiber does.  A functional
specification is the special case `S(i) = {f(i)}`."

Lean: `Spec I O` (orders are the `PO` instances); the fiber `S(i)` is
`sp.S i`; functional is `Spec.Functional`. -/
abbrev «def:relational-specification» (I O : Type) [PO I] [PO O] := Spec I O

/-- **Eq. `eq:relational-specification`**: "`Spec = (I,≼,O,≼,S)`,
`S ⊆ I × O`."  The orders are the `PO` instances; the relation `S ⊆ I × O` is a
`Table I O` (a predicate on pairs).  A `Spec I O` is such a table together with
totality: this is the `S` component. -/
abbrev «eq:relational-specification» (I O : Type) [PO I] [PO O] (sp : Spec I O) : Table I O :=
  sp.S

/-- **Eq. `eq:fiber`**: "`S(i) = {o ∈ O : (i,o) ∈ S}`", as a predicate on
outputs. -/
abbrev «eq:fiber» {I O : Type} [PO I] [PO O] (sp : Spec I O) (i : I) : O → Prop :=
  fun o => sp.S i o

/-- Def. `def:relational-specification`, "ambiguous": some fiber has two
distinct outputs.  (The library has no named notion; this is the reading.)
Ambiguity is the negation of the functional dependency. -/
theorem «def:relational-specification/ambiguous» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    (∃ i o o', sp.S i o ∧ sp.S i o' ∧ o ≠ o') ↔ ¬ sp.Functional :=
  ⟨fun ⟨i, o, o', h, h', hne⟩ hf => hne (hf i o o' h h'),
   fun hn => Classical.byContradiction fun h =>
     hn fun i o o' ho ho' => Classical.byContradiction fun hne => h ⟨i, o, o', ho, ho', hne⟩⟩

/-! ## Lifted Monotonicity (`sec:lifted-monotonicity`) -/

/-- **Def. `def:relational-monotonicity`** (Relational Monotonicity).
"`i ≼ j, o ∈ S(i) ⟹ ∃ u ∈ S(j) : o ≼ u`." -/
abbrev «def:relational-monotonicity» {I O : Type} [PO I] [PO O] (sp : Spec I O) : Prop :=
  sp.RelMono

/-- **Eq. `eq:relational-monotonicity`**:
"`i ≼ j, o ∈ S(i) ⟹ ∃ u ∈ S(j) : o ≼ u`" is the definition of
`Spec.RelMono`. -/
theorem «eq:relational-monotonicity» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    sp.RelMono ↔ ∀ i j o, i ≼ j → sp.S i o → ∃ u, sp.S j u ∧ o ≼ u :=
  Iff.rfl
/-- After Def. `def:relational-monotonicity`: "For singleton fibers this is
functional monotonicity." -/
theorem «def:relational-monotonicity/functional» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) : sp.RelMono ↔ sp.MonotoneF :=
  relMono_iff_monoF hf

/-- "For a set `F ⊆ O` of outputs, outputs `o₁,…,o_k` are *compatible in
`F`* if some `u ∈ F` refines all of them."  Lean: `CompatibleIn F X`, with
the outputs as a list `X`. -/
abbrev «sec:lifted-monotonicity/compatible» {O : Type} [PO O] (F : O → Prop) (X : List O) : Prop :=
  CompatibleIn F X

/-- **Def. `def:fiber-directedness`** (Directed fiber, Directed Outputs).  "A
fiber `F ⊆ O` is *directed* when every nonempty finite `X ⊆ F` is compatible
in `F`.  An ordered relational specification has *Directed Outputs* when every
fiber `S(i)` is directed."  Lean: `F` is directed iff `JointLift F F`;
`Spec.DirectedOutputs` is `∀ i, JointLift (sp.S i) (sp.S i)`. -/
abbrev «def:fiber-directedness» {I O : Type} [PO I] [PO O] (sp : Spec I O) : Prop :=
  sp.DirectedOutputs

/-- After Def. `def:fiber-directedness`: "A singleton fiber is trivially
directed." -/
theorem «def:fiber-directedness/singleton» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) : sp.DirectedOutputs :=
  functional_directed hf

/-- "The fiber `{{a},{b},{a,b,c},{a,b,d},{a,b,c,d}}` under inclusion is
directed, since `{a,b,c,d}` refines every member, yet `{a}` and `{b}` have two
incomparable minimal common refinements.  Compatibility likewise does not
require comparability: … as `{a,b,c}` and `{a,b,d}` do."  The fiber is the
type `F5` (all of it). -/
theorem «sec:lifted-monotonicity/directed-example» :
    JointLift (fun _ : F5 => True) (fun _ : F5 => True) ∧
      (∀ u, (F5.a ≼ u ∧ F5.b ≼ u) ↔ (u = .abc ∨ u = .abd ∨ u = .abcd)) ∧
      (¬ (F5.abc ≼ F5.abd) ∧ ¬ (F5.abd ≼ F5.abc) ∧
        (∀ u, F5.a ≼ u → F5.b ≼ u → u ≼ F5.abc → u = F5.abc) ∧
        (∀ u, F5.a ≼ u → F5.b ≼ u → u ≼ F5.abd → u = F5.abd)) ∧
      CompatibleIn (fun _ : F5 => True) [F5.abc, F5.abd] :=
  ⟨f5_directed, f5_common_refinements, f5_minimal_incomparable, f5_compatible⟩

/-- "Thus the traceroute fiber is directed: the union of any finite set of
route sets in it is again in the fiber and refines each of them.  The two
transaction orders in Figure `fig:ambiguity-frames`(f), by contrast, are
incompatible." -/
theorem «sec:lifted-monotonicity/figure-fibers» :
    (∀ x y, Figures.Trace.inFib x → Figures.Trace.inFib y →
        Figures.Trace.inFib (x.union y) ∧ x ≼ x.union y ∧ y ≼ x.union y) ∧
      Figures.Trace.spec.DirectedOutputs ∧
      ¬ CompatibleIn (Figures.Txn.spec.S ()) [.ab, .ba] :=
  ⟨Figures.Trace.union_mem, Figures.Trace.directed.1, Figures.Txn.not_monotone.1⟩

/-- **Eq. `eq:joint-output-order`** (joint lift).  "For nonempty `A,B ⊆ O`,
`A ⊑ B ⟺ every nonempty finite X ⊆ A is compatible in B`."  Lean:
`JointLift A B`, with `X` a nonempty list. -/
abbrev «eq:joint-output-order» {O : Type} [PO O] (A B : O → Prop) : Prop :=
  JointLift A B

/-- **Def. `def:lifted-monotonicity`** (Lifted Monotonicity, monotone
specification).  "`i ≼ j ⟹ S(i) ⊑ S(j)`." -/
abbrev «def:lifted-monotonicity» {I O : Type} [PO I] [PO O] (sp : Spec I O) : Prop :=
  sp.LiftedMono

/-- **Eq. `eq:lifted-monotonicity`**: "`i ≼ j ⟹ S(i) ⊑ S(j)`" is the
definition of `Spec.LiftedMono`, with `⊑` the joint lift `JointLift`. -/
theorem «eq:lifted-monotonicity» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    sp.LiftedMono ↔ ∀ i j, i ≼ j → JointLift (sp.S i) (sp.S j) :=
  Iff.rfl
/-- After Def. `def:lifted-monotonicity`: "With singleton fibers it is
functional monotonicity." -/
theorem «def:lifted-monotonicity/functional» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) : sp.LiftedMono ↔ sp.MonotoneF :=
  liftedMono_iff_monoF hf

/-- After Def. `def:lifted-monotonicity`: "So Lifted Monotonicity holds
exactly when both [Relational Monotonicity and Directed Outputs] do." -/
theorem «def:lifted-monotonicity/relmono-directed» {I O : Type} [PO I] [PO O]
    (sp : Spec I O) : sp.LiftedMono ↔ sp.RelMono ∧ sp.DirectedOutputs :=
  liftedMono_iff_relMono_directed sp

/-- **Def. `def:common-expansion-condition`** (Common-expansion condition).
"For every finite set of rows `(i₁,o₁),…,(i_k,o_k)` of `S` and every common
expansion `j` of `i₁,…,i_k`, some `u ∈ S(j)` refines every `o_r`."  Lean:
`Spec.CommonExpansion`, the rows as a list. -/
abbrev «def:common-expansion-condition» {I O : Type} [PO I] [PO O] (sp : Spec I O) : Prop :=
  sp.CommonExpansion

/-- After Def. `def:common-expansion-condition`: "For the empty set of rows
the condition asks only that `S(j)` be nonempty, which totality
guarantees." -/
theorem «def:common-expansion-condition/empty» {I O : Type} [PO I] [PO O]
    (sp : Spec I O) (j : I) :
    (∃ u, sp.S j u ∧ ∀ r ∈ ([] : List (I × O)), r.2 ≼ u) :=
  let ⟨u, hu⟩ := sp.total j; ⟨u, hu, fun _ h => nomatch h⟩

/-- **Prop. `prop:common-expansion-form`** (Common-expansion form of Lifted
Monotonicity).  "An ordered relational specification satisfies Lifted
Monotonicity if and only if it satisfies the common-expansion condition." -/
theorem «prop:common-expansion-form» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    sp.LiftedMono ↔ sp.CommonExpansion :=
  liftedMono_iff_commonExpansion sp

/-! ## Lifted output events (`sec:lifted-output-events`)

The body gives an informal summary; the formal definitions (`eq:seal-inputs`,
`eq:output-retirements`, `eq:choice-removals`, `def:lifted-output-event`,
`eq:canonical-seal-commitment-relational`), the remarks after them, and
Prop. `prop:exposability` with `eq:safe-exposure` are in Appendix
`app:lifted-output-events`, and their entries in
`Paper/AppC_CommitmentBases.lean`. -/

/-! ## The Complete CALM theorem (`sec:complete-calm-theorem`) -/

/-- "Specification states, input events, runs, commitment-free runs, and
consistency are defined as before, and the results of Section
`sec:executions` … lift unchanged."  In Lean there is nothing to lift: the
transition system, Lemma `lem:run-residual` and Prop. `prop:confluence` are
stated for arbitrary (relational) specifications from the start; this
restates the lemma for the record. -/
theorem «sec:complete-calm-theorem/lift-unchanged» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} {i : I} {es : List (Event I O)} {τ : State sp}
    (hx : Exec (canon sp i) es τ) :
    ∀ k u, τ.R k u ↔ (sp.S k u ∧ τ.cur ≼ k ∧ ∀ o ∈ outs es, o ≼ u) :=
  run_residual hx

/-- **Theorem `thm:complete-calm`** (Complete CALM).  "An ordered
specification is consistent if and only if it satisfies Lifted Monotonicity,
equivalently the common-expansion condition." -/
theorem «thm:complete-calm» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    (sp.Consistent ↔ sp.LiftedMono) ∧ (sp.Consistent ↔ sp.CommonExpansion) :=
  ⟨complete_calm sp, complete_calm_commonExpansion sp⟩

/-- **Prop. `prop:exposure-boundary`** (Exposure boundary).  "An ordered
specification satisfies the common-expansion condition if and only if every
output at every state reachable without commitment is exposable." -/
theorem «prop:exposure-boundary» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    sp.CommonExpansion ↔
      ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  exposure_boundary sp

/-- After Prop. `prop:exposure-boundary`: "With one output per input, Lifted
Monotonicity and the common-expansion condition are both monotonicity, so
Complete CALM and Proposition `prop:exposure-boundary` reduce to Functional
CALM and Proposition `prop:functional-exposure-boundary`." -/
theorem «prop:exposure-boundary/functional» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) :
    (sp.LiftedMono ↔ sp.MonotoneF) ∧ (sp.CommonExpansion ↔ sp.MonotoneF) :=
  ⟨liftedMono_iff_monoF hf, commonExpansion_iff_monoF hf⟩

/-- "One functional result does not carry over. … With several outputs per
input, runs that reach the same input can keep different rows: in Figure
`fig:ambiguity-frames`(g), a run that emitted `{s→s1}` has retired the route
sets that omit it, while a run that emitted nothing keeps them."  The
traceroute specification is consistent, yet the two runs end at the same input
in different states. -/
theorem «sec:complete-calm-theorem/state-by-input-fails» :
    Figures.Trace.spec.Consistent ∧
      (IsRun (outState (canon Figures.Trace.spec ()) Figures.Trace.rS1
          ((Figures.Trace.canonR _).2 (by decide))) ∧
        IsRun (canon Figures.Trace.spec ()) ∧
        (outState (canon Figures.Trace.spec ()) Figures.Trace.rS1
          ((Figures.Trace.canonR _).2 (by decide))).cur = (canon Figures.Trace.spec ()).cur ∧
        ¬ (outState (canon Figures.Trace.spec ()) Figures.Trace.rS1
          ((Figures.Trace.canonR _).2 (by decide))).R () Figures.Trace.rA ∧
        (canon Figures.Trace.spec ()).R () Figures.Trace.rA ∧
        outState (canon Figures.Trace.spec ()) Figures.Trace.rS1
          ((Figures.Trace.canonR _).2 (by decide)) ≠ canon Figures.Trace.spec ()) :=
  ⟨Figures.Trace.directed.2.2, Figures.Trace.state_depends_on_outputs⟩

/-- The same failure on a minimal example: a consistent specification with one
input and outputs `lo ≼ hi` has a run ending at a non-canonical state. -/
theorem «sec:complete-calm-theorem/state-by-input-fails-minimal» :
    specTwo.Consistent ∧ ∃ τ : State specTwo, IsRun τ ∧ τ ≠ canon specTwo τ.cur :=
  state_by_input_fails_relationally

end CC.Paper
