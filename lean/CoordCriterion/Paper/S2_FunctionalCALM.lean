import CoordCriterion.Figures
import CoordCriterion.CompleteCALM.Legality

/-!
# Paper §2: Functional CALM (`sections/functional-calm.tex`)

Statement layer for Section 2 (`sec:functional-calm`), including
Figure `fig:election-frames` and Figure `fig:nonmonotone-frame`.

How to read this file: open `sections/functional-calm.tex` next to it.  The
paper's §2 has two subsections.  §2.1, "The framework by example", carries the
labels `sec:election-story`, `sec:functional-specifications`,
`sec:functional-events` and `sec:executions`; its four paragraphs ("Specs and
monotonicity", "States and input events", "Output events and commitments",
"Runs and consistency") are the `###` headers below.  §2.2 is "The Functional
CALM theorem" (`sec:functional-calm-theorem`).  Declarations follow the paper's
order.  Every numbered result is a declaration named by its LaTeX label in
guillemets (`«thm:functional-calm»`); inline claims are named
`«<enclosing label>/<slug>»`.  Each docstring quotes the paper, and, when the
Lean reading differs, says how.  Proofs are one-line pointers into the
library; the full statement is always written out.

Library conventions used throughout (see `Foundations/Core.lean`):
* `≼` is the input order on `I` and the output order on `O` (`PO.le`);
  `i ≼ j` reads "`j` extends `i`", `o ≼ u` reads "`u` extends `o`";
* a table is a predicate `Table I O := I → O → Prop`; a set of outputs is a
  predicate `O → Prop`; finite families are `List`s;
* a specification `sp : Spec I O` has table `sp.P` and totality `sp.total`;
  its fiber at `i` is `sp.P i`;
* a state `σ : State sp` has current input `σ.cur` and remainder table `σ.R`;
* `R[in ⪰ j]` is `inputTable σ j`, `R[out ⪰ o]` is `outputTable σ o`.

The election itself (`elec`, `elecEq`, ballots `bad = a··`, `bab = ab·`,
`baba = aba`, `baa = aa·`, …) is defined in `CALM/Examples.lean` and
`Figures.lean`; `elec` uses the output-extension order on results (`⊥ ≼` each
winner), `elecEq` the equality order.
-/

namespace CC.Paper

open CC CC.CALM

/-! ## The framework by example (`sec:election-story`, `sec:functional-specifications`, `sec:functional-events`, `sec:executions`) -/

/-- Fig. `fig:election-frames` caption: "The election spec and states reached
from it, limited to rows whose input extends `a··`."  Text: "For brevity, the
figure shows only inputs extending `a··`."  The nine printed pairs
(`Figures.Elec.printed`) are exactly the rows of the election at inputs
`⪰ a··`. -/
theorem «fig:election-frames/printed-rows» (k : Ballots) (o : Res) :
    (k, o) ∈ Figures.Elec.printed ↔ (bad ≼ k ∧ elec.P k o) :=
  Figures.Elec.printed_complete k o

/-- Fig. `fig:election-frames`(a): "Initial state, current input `a··` …
upper fiber `{⊥,a,b}`; undetermined; `⊥` needs no commitment."  Panel (a) is
the canonical state `σ_P(a··)`; "upper fiber `{⊥,a,b}`" is stated as "every
output occurs in some remaining row". -/
theorem «fig:election-frames/a» :
    (∀ o : Res, ∃ k, (canon elec bad).R k o) ∧ ¬ Determined (canon elec bad) ∧
      Exposable (canon elec bad) .bot := by
  refine ⟨fun o => (Figures.Elec.upper_ab o).1, ?_, elec_panels_exposable.1⟩
  rintro ⟨o, h⟩
  obtain ⟨k₁, h₁⟩ := (Figures.Elec.upper_ab .bot).1
  obtain ⟨k₂, h₂⟩ := (Figures.Elec.upper_ab (.win .a)).1
  cases (h _ _ h₁).trans (h _ _ h₂).symm

/-! ### Specs and monotonicity -/

/-- "A spec is a possibility table for a function over ordered types."

**Def. `def:functional-specification`** (Functional I/O specification,
total).  "A *functional I/O specification* is a tuple `Spec = (I, ≼, O, ≼, P)`,
where `(I,≼)` and `(O,≼)` are partially ordered input and output types, and
`P ⊆ I × O` is its *possibility relation*: a typed relation with schema
`(in, out)` in which every input appears in at least one row (`P` is *total* on
`I`) and at most one (a functional dependency):
`(i,o) ∈ P ∧ (i,o') ∈ P ⟹ o = o'`."

Lean: the orders are the `PO` instances, `Spec I O` bundles `P` with
totality, and `Spec.Functional` is the functional dependency. -/
abbrev «def:functional-specification» (I O : Type) [PO I] [PO O] :=
  { sp : Spec I O // sp.Functional }

/-- "The unique output paired with `i` induces the function
`f : (I,≼) → (O,≼)` with `P = {(i, f(i)) : i ∈ I}`."  The library works with
rows rather than with `f`; this states that the two views agree. -/
theorem «def:functional-specification/induced-function» {I O : Type} [PO I] [PO O]
    (sp : Spec I O) : sp.Functional ↔ ∃ f : I → O, ∀ i o, sp.P i o ↔ o = f i := by
  constructor
  · intro hf
    refine ⟨fun i => (sp.total i).choose, fun i o => ⟨fun h => hf i o _ h (sp.total i).choose_spec,
      fun h => h ▸ (sp.total i).choose_spec⟩⟩
  · rintro ⟨f, hf⟩ i o o' h h'
    exact ((hf i o).1 h).trans ((hf i o').1 h').symm

/-- "Inputs grow as ballots arrive: `i ≼ j`, read '`j` *extends* `i`', means
that `j` has everything `i` has and possibly more.  So `ab·` extends `a··`,
while `aa·` and `ab·` are incomparable." -/
theorem «sec:election-story/input-order» :
    bad ≼ bab ∧ ¬ baa ≼ bab ∧ ¬ bab ≼ baa := by decide

/-- "Outputs grow as announcements say more: `o ≼ u`, read '`u` extends `o`',
means that `u` makes every claim `o` makes.  Either winner extends `⊥`, which
claims nothing, while `a` and `b` are incomparable." -/
theorem «sec:election-story/output-order» :
    Res.bot ≼ Res.win .a ∧ Res.bot ≼ Res.win .b ∧
      ¬ Res.win .a ≼ Res.win .b ∧ ¬ Res.win .b ≼ Res.win .a :=
  ⟨Or.inl rfl, Or.inl rfl, (by rintro (h | h) <;> cases h), (by rintro (h | h) <;> cases h)⟩

/-- "A functional spec is monotone when growing input only ever extends its
output:"

**Def. `def:functional-monotonicity`** (Functional monotonicity).  "A
functional I/O specification `Spec`, with induced function `f`, is *monotone*
if `i ≼ j ⟹ f(i) ≼ f(j)`."

Lean: `Spec.MonotoneF` is stated on rows (`i ≼ j`, `(i,o) ∈ P`, `(j,u) ∈ P`
imply `o ≼ u`), which needs no induced function;
`«def:functional-monotonicity/via-f»` shows it is the paper's condition. -/
abbrev «def:functional-monotonicity» {I O : Type} [PO I] [PO O] (sp : Spec I O) : Prop :=
  sp.MonotoneF

/-- **Eq. `eq:functional-monotonicity`**: "`i ≼ j ⟹ f(i) ≼ f(j)`", the
displayed condition on the induced function `f`.  By
`«def:functional-monotonicity/via-f»` it is `Spec.MonotoneF` whenever
`P = {(i, f(i))}`. -/
abbrev «eq:functional-monotonicity» {I O : Type} [PO I] [PO O] (f : I → O) : Prop :=
  ∀ i j : I, i ≼ j → f i ≼ f j

/-- Def. `def:functional-monotonicity`, in terms of the induced function: if
`P = {(i, f(i))}`, then `Spec.MonotoneF` is `i ≼ j ⟹ f(i) ≼ f(j)`. -/
theorem «def:functional-monotonicity/via-f» {I O : Type} [PO I] [PO O]
    (sp : Spec I O) (f : I → O) (hf : ∀ i o, sp.P i o ↔ o = f i) :
    sp.MonotoneF ↔ ∀ i j, i ≼ j → f i ≼ f j :=
  ⟨fun h i j hij => h i j _ _ hij ((hf i _).2 rfl) ((hf j _).2 rfl),
   fun h i j o u hij ho hu => by rw [(hf i o).1 ho, (hf j u).1 hu]; exact h i j hij⟩

/-- "The election is monotone: to give an example, the input sequence
`a·· ≼ ab· ≼ aba` produces the output sequence `⊥ ≼ ⊥ ≼ a`."  The election
(output-extension order) is monotone, and the chain is as stated. -/
theorem «sec:election-story/monotone» :
    elec.MonotoneF ∧
      (bad ≼ bab ∧ bab ≼ baba) ∧
      (winner bad = .bot ∧ winner bab = .bot ∧ winner baba = .win .a) ∧
      (Res.bot ≼ Res.bot ∧ Res.bot ≼ Res.win .a) :=
  ⟨elec_monotone, by decide, by decide, ⟨Or.inl rfl, Or.inl rfl⟩⟩

/-! ### States and input events -/

/-- "Each panel of Figure `fig:election-frames` shows one moment: the ballots
received so far, and the rows that can still be reached from them.  We call such a moment a specification state."

**Def. `def:residual-state`** (Specification state, current input, remainder
table).  "Given a specification `Spec = (I,≼,O,≼,P)`, a *specification state*
is a pair `σ = (i,R)`, where `i ∈ I` is the *current input* and `R ⊆ P` is the
*remainder table*, such that: (1) `R` contains a row with input `i`; and
(2) every row `(k,o) ∈ R` satisfies `i ≼ k`."

Lean: `State sp` with fields `cur`, `R`, `sub` (`R ⊆ P`), `hasCur` (1) and
`above` (2). -/
abbrev «def:residual-state» {I O : Type} [PO I] [PO O] (sp : Spec I O) := State sp

/-- "Not every input can still arrive in a state:"

**Def. `def:legal-input`** (Legal input).  "An input `k` is *legal* at a state
`σ = (i,R)` when `R` contains a row at `k`."  Lean: `∃ u, σ.R k u`. -/
abbrev «def:legal-input» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (k : I) : Prop :=
  ∃ u, σ.R k u

/-- **Eq. `eq:canonical-state`**: the canonical state `σ_P(i) = (i, P[in ⪰ i])`. -/
abbrev «eq:canonical-state» {I O : Type} [PO I] [PO O] (sp : Spec I O) (i : I) : State sp :=
  canon sp i

/-- "A run starts from the *canonical state* at its first input `i`, which
keeps every row of `P` whose input extends `i`: it is the state of a system
that has received `i` and emitted nothing."  Lean: every state's table is
contained in that of the canonical state at its current input. -/
theorem «eq:canonical-state/largest» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) : ∀ k x, σ.R k x → (canon sp σ.cur).R k x :=
  state_le_canon σ

/-- **Eq. `eq:input-event`**: "For a state `(i,R)` and a legal input `j` with
`i ≼ j`, the *input event* `(i,R) --input(j)--> (j, R' = R[in ⪰ j])` makes `j`
current and drops the rows whose input does not extend `j`, which we call
*input loss*."

Lean: `Step σ (.input j) τ` holds exactly when `j` is legal, `τ.cur = j` and
`τ.R = inputTable σ j` (constructor `Step.input`); `inputTable σ j` is
`R[in ⪰ j]`.  Legality already implies `i ≼ j` (`«eq:input-event/legal-expands»`). -/
abbrev «eq:input-event» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (j : I) : Table I O :=
  inputTable σ j

/-- The paper's input event asks for `j` legal *and* `i ≼ j`; the second
follows from the first, since every row of the remainder table is at an input
that extends `i`. -/
theorem «eq:input-event/legal-expands» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (j : I) (h : ∃ u, σ.R j u) : σ.cur ≼ j :=
  legal_above σ j h

/-- Fig. `fig:election-frames`(b): "After `input(ab·)` … upper fiber `{⊥,a,b}`;
undetermined; `⊥` needs no commitment."  Text: "When `v₂`'s ballot for `b`
arrives, rows such as `aa·` no longer extend the input, and they are lost: the
world has moved on, and panel (b) results." and "In panel (b), the first is
`{⊥}` and the second, shaded, is `{⊥,a,b}`."  The input event takes `σ_P(a··)`
to `σ_P(ab·)`; "`⊥` needs no commitment" is "`⊥` is a legal output". -/
theorem «fig:election-frames/b» :
    Step (canon elec bad) (.input bab) (canon elec bab) ∧
      (∀ o : Res, ∃ k, (canon elec bab).R k o) ∧ ¬ Determined (canon elec bab) ∧
      Exposable (canon elec bab) .bot :=
  ⟨Dist.step_canon_input elec (by decide) ⟨_, rfl⟩, fun o => (Figures.Elec.upper_ab o).2,
   elec_panel_b_undetermined, elec_panels_exposable.2.1⟩

/-- Fig. `fig:election-frames`(b), the printed rows; caption: "Gray: lost
after an input event."  Of the rows at inputs `⪰ a··`, exactly `(ab·,⊥)`,
`(aba,a)`, `(abb,b)` remain; every other printed row is gray because its input
does not extend `ab·` (input loss). -/
theorem «fig:election-frames/b-rows» (k : Ballots) (o : Res) (hk : bad ≼ k) :
    ((canon elec bab).R k o ↔
        ((k = bab ∧ o = .bot) ∨ (k = baba ∧ o = .win .a) ∨
          (k = Figures.Elec.babb ∧ o = .win .b))) ∧
      (elec.P k o → ¬ (canon elec bab).R k o → ¬ bab ≼ k) :=
  Figures.Elec.panel_b k o hk

/-- "An input event names the cumulative input `j`: everything received so
far, including all of `i`.  Thus `input(j)` then `input(k)` has the effect of
`input(k)` alone, `input(i)` at `(i,R)` has no effect, …" -/
theorem «sec:functional-events/input-cumulative» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} :
    (∀ {σ τ ρ : State sp} {j k : I},
        Step σ (.input j) τ → Step τ (.input k) ρ → Step σ (.input k) ρ) ∧
      (∀ {σ τ : State sp}, Step σ (.input σ.cur) τ → τ = σ) :=
  ⟨input_input, input_self⟩

/-- "… and an input event from a canonical state leads to another canonical
state." -/
theorem «eq:canonical-state/input-moves-canonical» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} {i j : I} {τ : State sp} (h : Step (canon sp i) (.input j) τ) :
    τ = canon sp j :=
  input_canon h

/-- "Two sets of outputs matter in every state: those at the current
input (its *fiber*), and those at the current input or any input that extends
it (its *upper fiber*).  In panel (b), the first is `{⊥}` and the second,
shaded, is `{⊥,a,b}`."

**Def. `def:fiber`** (Fiber, upper fiber).  "Let `R` be a table and `k` an
input.  The *fiber* of `R` at `k` is `R(k) = π_out(R[in = k])`, the outputs
paired with `k`.  The *upper fiber* of `R` at `k` is `π_out(R[in ⪰ k])`, the
outputs paired with `k` or with any input that extends `k`."

Lean: the fiber is `R k`, a predicate on outputs; the upper fiber is
`fun o => ∃ k', k ≼ k' ∧ R k' o` (`«def:fiber/upper»`). -/
abbrev «def:fiber» {I O : Type} (R : Table I O) (k : I) : O → Prop := R k

/-- Def. `def:fiber`: the upper fiber of `R` at `k`, `π_out(R[in ⪰ k])`. -/
abbrev «def:fiber/upper» {I O : Type} [PO I] (R : Table I O) (k : I) : O → Prop :=
  fun o => ∃ k', k ≼ k' ∧ R k' o

/-- Def. `def:determined`: "The upper fiber of `σ` is `π_out(R[in ⪰ i]) =
π_out(R)`."  Every row of a state's table is at
an input that extends its current input, so the two descriptions agree. -/
theorem «def:fiber/state» {I O : Type} [PO I] [PO O] {sp : Spec I O} (σ : State sp)
    (o : O) : «def:fiber/upper» σ.R σ.cur o ↔ ∃ k, σ.R k o :=
  ⟨fun ⟨k, _, h⟩ => ⟨k, h⟩, fun ⟨k, h⟩ => ⟨k, σ.above k o h, h⟩⟩

/-- **Def. `def:determined`** (Determined state).  "A state is determined when
only one output remains possible, as in panel (c), where input alone has
settled the outcome."  "Let `σ = (i, R)` be a specification state.  The upper
fiber of `σ` is `π_out(R[in ⪰ i]) = π_out(R)`.  We say `σ` is *determined*
when `|π_out(R)| = 1`."  Lean:
`CALM.Determined σ` is `∃ o, ∀ k x, σ.R k x → x = o`; the upper fiber
`π_out(R)` is nonempty, so this is "has exactly one element". -/
abbrev «def:determined» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) : Prop :=
  Determined σ

/-- "Determined": the upper fiber `π_out(R)` has exactly one element. -/
theorem «sec:functional-events/determined-one-element» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} (σ : State sp) :
    Determined σ ↔ ∃ o, (∃ k, σ.R k o) ∧ ∀ k x, σ.R k x → x = o :=
  determined_upper_fiber σ

/-- Fig. `fig:election-frames`(c): "After `input(aa·)` instead … upper fiber
`{a}`; determined; `a` needs no commitment."  Text: "A state is determined when
only one output remains possible, as in panel (c), where input alone has
settled the outcome." -/
theorem «fig:election-frames/c» :
    Step (canon elec bad) (.input baa) (canon elec baa) ∧
      (∀ o, (∃ k, (canon elec baa).R k o) ↔ o = .win .a) ∧
      Determined (canon elec baa) ∧ Exposable (canon elec baa) (.win .a) :=
  ⟨Dist.step_canon_input elec (by decide) ⟨_, rfl⟩, Figures.Elec.upper_c,
   elec_panel_c_determined, elec_panels_exposable.2.2⟩

/-! ### Output events and commitments -/

/-- "At a state `(i,R)`, the current input has a unique row `(i,o)`, so `o`,
the *current output*, is the only output the system may emit.  Emitting `⊥` in
panel (b) is safe, since every output still possible builds on it; emitting
`a` there would not be, since `b` is still possible."

**Def. `def:exposable`** (Legal output).  "The output `o` at `(i,R)` is a
*legal output* when every output in the upper fiber extends `o`."

Lean: `Exposable σ o` says that every row ruled out by `o` is extended by a
kept row at the same input (it is subsumed, not committed away); by
`«def:exposable/no-commitment»` this is "`Excluded_o` is empty", i.e. no
commitment, in the sense of Def. `def:lifted-output-event`. -/
abbrev «def:exposable» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) : Prop :=
  Exposable σ o

/-- Def. `def:exposable`: a legal output applies no commitment. -/
theorem «def:exposable/no-commitment» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) :
    Exposable σ o ↔ ∀ k x, ¬ Excluded σ o k x :=
  exposable_iff_no_commitment σ o

/-- "So `⊥` is legal in panels (a) and (b), and `a` in panel (c)." -/
theorem «sec:election-story/exposable-panels» :
    Exposable (canon elec bad) .bot ∧ Exposable (canon elec bab) .bot ∧
      Exposable (canon elec baa) (.win .a) :=
  elec_panels_exposable

/-- "Possibilities can also be removed deliberately.  Closing the polls in
panel (d) rules out `aba` and `abb`, and no remaining row covers them: this is
the fateful decision of the introduction.  A row `(k,u)` is *extended* by
another row `(k,w)` at the same input when `w` extends `u`."

**Def. `def:commitment`** (Commitment).  "A *commitment* is a partial function
`e` on specification states that removes a nonempty set of rows, none of which
is extended by a row that remains at the same input.  That is, whenever
`e(i,R) = (j,R')`, we have `R' ⊊ R` and
`(k,u) ∈ R ∖ R', (k,w) ∈ R' ⟹ u ⋠ w` (Eq. commitment-unsubsumed).  It leaves
the current input unchanged: `j=i`."

Lean: `Commitment sp`: `app : State sp → Option (State sp)` with fields
`cur_eq`, `sub`, `removes` (`R' ⊊ R`), `unsubsumed` (Eq.
commitment-unsubsumed). -/
abbrev «def:commitment» {I O : Type} [PO I] [PO O] (sp : Spec I O) := Commitment sp

/-- **Eq. `eq:commitment-unsubsumed`**: whenever `c(i,R) = (i,R')`,
"`(k,u) ∈ R ∖ R', (k,w) ∈ R' ⟹ u ⋠ w`" (field `Commitment.unsubsumed`). -/
theorem «eq:commitment-unsubsumed» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (c : Commitment sp) (σ τ : State sp) (h : c.app σ = some τ) :
    ∀ k u w, σ.R k u → ¬ τ.R k u → τ.R k w → ¬ (u ≼ w) :=
  c.unsubsumed σ τ h

/-- After Def. `def:commitment`: "In a functional spec each input has one row,
so the last condition always holds: a commitment rules out the inputs of the
rows it removes."  Lean: in a functional specification, if a commitment
removes the row `(k,u)`, no row at `k` remains. -/
theorem «def:commitment/functional» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) (c : Commitment sp) {σ τ : State sp} (h : c.app σ = some τ)
    {k : I} {u : O} (hu : σ.R k u) (hnu : ¬ τ.R k u) : ∀ w, ¬ τ.R k w := by
  intro w hw
  have hw' : σ.R k w := c.sub σ τ h k w hw
  have : u = w := hf k u w (σ.sub k u hu) (σ.sub k w hw')
  subst this
  exact hnu hw

/-- "When `o` is not legal, we make it legal via a commitment that removes the
rows whose outputs conflict with `o`.  Emitting `o` only once it is legal keeps a
run from contradicting `o` later on, when the environment may already have
acted on it."

**Def. `def:output-event`** (Output event).  "At a state `(i,R)` with current
output `o`, the *output event* `output(o)` atomically keeps only the rows whose
outputs extend `o`, and then emits `o`: `(i,R) --output(o)--> (i, R' = R[out ⪰ o])`."

Lean: `Step σ (.output o) τ` (constructor `Step.output`) requires
`σ.R σ.cur o` and sets `τ.R = outputTable σ o = R[out ⪰ o]`.  The general
definition is used for every specification (it is also Def.
`def:lifted-output-event`); in a functional specification "`R' ≠ R`" is
exactly "some row is in `Excluded_o`" (`«def:output-event/commitment-iff-excluded»`). -/
abbrev «def:output-event» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) : Table I O :=
  outputTable σ o

/-- **Eq. `eq:output-action`**: "`(i,R) --output(o)--> (i, R' = R[out ⪰ o])`".
The new table `R[out ⪰ o]` is `outputTable σ o`: the rows of `R` whose output
extends `o`. -/
theorem «eq:output-action» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) (k : I) (u : O) :
    outputTable σ o k u ↔ σ.R k u ∧ o ≼ u :=
  Iff.rfl

/-- Def. `def:output-event`: in a functional specification, the output event
changes the table (`R' ≠ R`) iff it excludes some row. -/
theorem «def:output-event/commitment-iff-excluded» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) (σ : State sp) (o : O) :
    outputTable σ o ≠ σ.R ↔ ∃ k x, Excluded σ o k x :=
  functional_exclude_iff_excluded hf σ o

/-- **Def. `def:canonical-commitment-functional`** (Canonical commitment).
"When `o` is not legal at `(i,R)`, equivalently `R' ≠ R`, the event first
removes the rows whose outputs do not extend `o`; this removal is `o`'s *canonical commitment* `x_o(i,R) = (i,R')`, after which `o` is legal.  In a
functional table each input has only one row, so `x_o` rules out those rows'
inputs (`x_o` is a commitment)."  Following text: "An output event thus always
emits a legal output, and applies a commitment exactly when its output was not
already legal."

Lean: `canonicalCommitment o : Commitment sp` (`commitmentApp o`): the
commitment that removes the rows in `Excluded_o`, defined at states where
`o ∈ R(i)` and `Excluded_o ≠ ∅`. -/
noncomputable abbrev «def:canonical-commitment-functional» {I O : Type} [PO I] [PO O] {sp : Spec I O} (o : O) :
    Commitment sp :=
  canonicalCommitment o

/-- "The current row `(i,o)` remains, since `o` extends itself, so the event
always ends at a specification state with current input `i`." -/
theorem «sec:functional-events/output-ends-at-state» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} (σ : State sp) (o : O) (h : σ.R σ.cur o) :
    Step σ (.output o) (outputState σ o h) ∧ (outputState σ o h).R σ.cur o ∧
      (outputState σ o h).cur = σ.cur :=
  ⟨step_outputState σ o h, ⟨h, PO.refl o⟩, rfl⟩

/-- "*Determination* is the process of reaching a determined state.  An input
event can achieve it through input loss, as in panel (c), and a commitment can
do so by ruling out inputs that would otherwise remain possible, as in
panel (d)."  The first two conjuncts record that the election is functional
and that panel (b) is undetermined (panel note "undetermined"), so panels (c)
and (d) are genuine determinations. -/
theorem «sec:functional-events/determination-examples» :
    elec.Functional ∧ ¬ Determined (canon elec bab) ∧ Determined (canon elec baa) ∧
      Determined Figures.Elec.panelD :=
  ⟨elec_functional, elec_panel_b_undetermined, elec_panel_c_determined,
   Figures.Elec.panelD_determined.1⟩

/-- "An event from a determined state always leads to another determined state with that output: events only remove rows, and a row at the current input
always remains."  Lean: the next state is determined (first two conjuncts), and
every row it keeps has the determined output `o` of the previous state (third
conjunct). -/
theorem «sec:functional-events/stays-determined» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} :
    (∀ {σ τ : State sp} {e : Event I O}, Step σ e τ → Determined σ → Determined τ) ∧
      (∀ {σ τ : State sp}, Reach σ τ → Determined σ → Determined τ) ∧
      (∀ {σ τ : State sp} {e : Event I O} {o : O}, Step σ e τ →
        (∀ k x, σ.R k x → x = o) → ∀ k x, τ.R k x → x = o) :=
  ⟨step_determined, reach_determined,
   fun hs ho k x hx => ho k x (step_sub hs k x hx)⟩

/-- Fig. `fig:nonmonotone-frame`: "Panel (b) under the equality order, after
`output(⊥)`, wrapped to preserve space."  Panel: "(e) As (b), all outputs
incomparable, `⊥` emitted … upper fiber `{⊥}`; determined."  Under `elecEq`,
`output(⊥)` at `σ_P(ab·)` excludes `aba` and leaves the single row `(ab·,⊥)`. -/
theorem «fig:nonmonotone-frame» :
    Excluded (canon elecEq bab) ⟨.bot⟩ baba ⟨winner baba⟩ ∧
      ∀ k o, outputTable (canon elecEq bab) ⟨.bot⟩ k o ↔ (k = bab ∧ o = ⟨.bot⟩) :=
  ⟨elecEq_bot_excludes, elecEq_bot_single_row⟩

/-- "Under this order (called the *equality order*), no output extends both `⊥` and a future winner, so it is not legal at `ab·`, and emitting it applies `x_⊥`,
which removes `(aba,a)` and `(abb,b)`."  Lean: at `σ_P(ab·)`, `⊥` is not a
legal output under `elecEq`. -/
theorem «sec:election-story/equality-order-commitment» :
    ¬ Exposable (canon elecEq bab) ⟨.bot⟩ :=
  fun h => (exposable_iff_empty _ _).1 h ⟨_, _, elecEq_bot_excludes⟩

/-- Fig. `fig:election-frames`(d): "After (b), then polls closed … upper fiber
`{⊥}`; determined; `⊥` is the result."  Caption: "In (d) the registrar closes
the polls, a commitment that emitting `⊥` does not require, and emits `⊥`."
Text: "Here the system acts as a registrar that, when it emits `⊥` at `ab·`,
also closes the polls, removing the still-possible rows `aba` and `abb` and
keeping the current input unchanged. … After the event, the upper fiber is
determined at `{⊥}`."

Closing the polls is the commitment `Figures.closePolls` (a commitment in the
sense of Def. `def:commitment`, §4.3); the registrar applies it in the
commitment event `apply([closePolls])` and then emits `⊥` by `output(⊥)`, a
run under any basis containing `closePolls`.  It ends at `panelD`, whose only
row is `(ab·,⊥)`; the rows it removes beyond `(b)` are exactly `(aba,a)`,
`(abb,b)` (the struck rows); the state is determined with result `⊥`. -/
theorem «fig:election-frames/d» :
    (Figures.closePolls (sp := elec)).app (canon elec bab) = some Figures.Elec.panelD ∧
      (∀ B : CommitmentBasis elec, B Figures.closePolls →
        SysExec B (canon elec bab) [.commitment [Figures.closePolls], .output .bot]
          Figures.Elec.panelD) ∧
      Figures.Elec.panelD.cur = bab ∧
      (∀ k o, Figures.Elec.panelD.R k o ↔ (k = bab ∧ o = .bot)) ∧
      (∀ k o, ((canon elec bab).R k o ∧ ¬ Figures.Elec.panelD.R k o) ↔
        ((k = baba ∧ o = .win .a) ∨ (k = Figures.Elec.babb ∧ o = .win .b))) ∧
      (Determined Figures.Elec.panelD ∧ ∀ k x, Figures.Elec.panelD.R k x → x = .bot) :=
  ⟨Figures.Elec.close_at_b, Figures.Elec.registrar_step, Figures.Elec.panelD_cur,
   Figures.Elec.panelD_rows, Figures.Elec.panelD_struck, Figures.Elec.panelD_determined⟩

/-- Fig. `fig:election-frames` caption: "Gray: lost after an input event;
struck through if removed by a commitment."  A printed row is absent from
panel (d) iff its input does not extend `ab·` (gray) or it is one of the two
struck rows. -/
theorem «fig:election-frames/d-gray» (k : Ballots) (o : Res) (hk : bad ≼ k) (hS : elec.P k o) :
    ¬ Figures.Elec.panelD.R k o ↔
      (¬ bab ≼ k ∨ (k = baba ∧ o = .win .a) ∨ (k = Figures.Elec.babb ∧ o = .win .b)) :=
  Figures.Elec.panelD_gray k o hk hS

/-- Fig. `fig:election-frames` caption: "a commitment that emitting `⊥` does
not require".  Text: "The output was already legal; every output still
possible extends `⊥`."  At (b), `⊥` is a legal output, `Excluded_o` is empty,
and `output(⊥)` removes no row. -/
theorem «fig:election-frames/bot-alone» :
    Exposable (canon elec bab) .bot ∧ (¬ ∃ k x, Excluded (canon elec bab) .bot k x) ∧
      outputTable (canon elec bab) .bot = (canon elec bab).R :=
  Figures.Elec.bot_alone_at_b

/-- Fig. `fig:nonmonotone-frame` caption: "The registrar's commitment in
Figure `fig:election-frames`(d) is required here."  Panel (d)'s table is the
table left by `output(⊥)` at `σ_P(ab·)` under the equality order. -/
theorem «fig:nonmonotone-frame/matches-d» (k : Ballots) (r : Res) :
    Figures.Elec.panelD.R k r ↔ outputTable (canon elecEq bab) ⟨.bot⟩ k ⟨r⟩ :=
  Figures.Elec.panelD_matches_e k r

/-- "Panel (d) of Figure `fig:election-frames`, by contrast, reflects a
commitment that the spec does not require.  A *system* that implements a spec
may make one through a *commitment event*. … Closing the polls was the
registrar's own fateful decision.  Section `sec:systems` models such choices;
a spec itself has only input and output events, and this section uses only
canonical commitments."  For the registrar of panel (d): its run
`apply([closePolls])`, `output(⊥)` has an observably equivalent `output(⊥)` of
the transition system, whose table contains panel (d)'s.  The general
statement is Lemma `lem:canonical-equivalent` (`CC.canonical_equivalent`,
§4.3). -/
theorem «sec:functional-events/extra-commitments» (B : CommitmentBasis elec) (hB : B Figures.closePolls) :
    ∃ ρ', Exec (canon elec bab) [.output .bot] ρ' ∧ ρ'.cur = bab ∧
      ∀ k u, Figures.Elec.panelD.R k u → ρ'.R k u :=
  Figures.Elec.registrar_canonical B hB

/-! ### Runs and consistency -/

/-- **Def. `def:specification-event`** (Specification event).  "Input and
output events are *specification events*: they change the specification
state.  We call them simply *events* when unambiguous."  Lean: `Event I O`
(two constructors `.input`, `.output`). -/
abbrev «def:specification-event» (I O : Type) := Event I O

/-- **Def. `def:transition-system`** (Transition system).  "The *transition
system* consists of specification states and specification events."  Lean:
`State sp` and `Event I O` together with `Step σ e τ`. -/
abbrev «def:transition-system» {I O : Type} [PO I] [PO O] (sp : Spec I O) : Prop :=
  ∀ (σ : State sp) (e : Event I O), ∃ τ, Step σ e τ ∨ ¬ ∃ τ, Step σ e τ

/-- **Def. `def:run`** (Canonical run).  "A *canonical run*, or just *run*, is
any finite transition sequence of the transition system from the canonical
state `σ_P(i)` at some input `i`."  The following scope convention says: "Runs
range over every behavior the spec permits, not only the behaviors a
particular system happens to produce.  A system that never uses some of the
spec's latitude is better described by a narrower spec.  For the spec as
written, we assume that any permitted behavior may occur."  This is the
paper's modeling convention; it is reflected in `IsRun` ranging over all runs
of the transition system.

Lean: `Exec σ es τ` is execution along the event list `es`; `IsRun τ` says
that `τ` is the final state of some run (`∃ i es, Exec (canon sp i) es τ`). -/
abbrev «def:run» {I O : Type} [PO I] [PO O] {sp : Spec I O} (τ : State sp) : Prop :=
  IsRun τ

/-- "A run is *commitment-free* when none of its output events applies a
commitment.  A state is *reachable without commitment* when some
commitment-free run reaches it."  Lean: `ExecCF` and `ReachableCF`. -/
abbrev «def:run/reachable-without-commitment» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (τ : State sp) : Prop :=
  ReachableCF τ

/-- "Consider the rows `(ab·,⊥)` and `(aba,a)` under the equality order.
Their inputs have the *common input extension* `aba`, an input that extends
both. … No output at `aba` extends both `⊥` and `a`, so the rows have no
*common output extension* there …"  And: "Rows with a common output extension
at `j` are *confluent at* `j`.  A set of rows is *row-consistent* when it is
confluent at every common input extension of its inputs, and
*row-inconsistent* otherwise."  The last conjunct says the two rows are not
confluent at `aba`. -/
theorem «sec:election-story/obstruction» :
    elecEq.P bab ⟨.bot⟩ ∧ elecEq.P baba ⟨.win .a⟩ ∧ bab ≼ baba ∧ baba ≼ baba ∧
      ¬ ∃ u, elecEq.P baba u ∧ (⟨.bot⟩ : ResE) ≼ u ∧ (⟨.win .a⟩ : ResE) ≼ u :=
  ⟨by show _ = _; rw [winner_bab], by show _ = _; rw [winner_baba], bab_le_baba, PO.refl _,
   fun ⟨_, _, h₁, h₂⟩ => by cases (show (⟨.bot⟩ : ResE) = ⟨.win .a⟩ from h₁.trans h₂.symm)⟩

/-- "Suppose one run emits `⊥` at `ab·`, and another receives `aba` and
emits `a`.  … the two runs can never reach a common state."  And: "Our two
rows `(ab·,⊥)` and `(aba,a)` are therefore inconsistent under the equality
order, so a run that emits `⊥` at `ab·` must apply the canonical commitment
`x_⊥`."  (Equality order.)  The two runs end at
`(ab·, P[in ⪰ ab·, out ⪰ ⊥])` and `σ_P(aba)`.  Lean takes the second run
before it emits `a`; emitting `a` only removes rows, so the paper's pair is
not confluent either. -/
theorem «sec:election-story/not-reconciled» :
    ¬ ConfluentAt [outputState (canon elecEq bab) ⟨.bot⟩
        ((elecEq_bot_single_row bab _).2 ⟨rfl, rfl⟩).1, canon elecEq baba] baba :=
  elecEq_not_confluent

/-- "Runs follow the same pattern: they are *confluent at* `j` when they can
reach a common state with current input `j`, and consistent when they are
confluent at every common input extension."

**Def. `def:confluence`** (Confluence at an input).  "A finite family of runs
ending at states `(i₁,R₁),…,(i_k,R_k)` is *confluent at* `j`, a common input
extension of their current inputs, when each can be continued to a common
state with current input `j`."

Lean: `ConfluentAt fam j` (`∃ τ, τ.cur = j ∧ ∀ σ ∈ fam, Reach σ τ`). -/
abbrev «def:confluence» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (fam : List (State sp)) (j : I) : Prop :=
  ConfluentAt fam j

/-- **Def. `def:consistency`** (Consistency).  "The runs of an I/O
specification are *consistent* when every finite family of them is confluent
at every common input extension of their current inputs."  The common input
extension `j` ranges over every `j` above all current inputs, including inputs
at which some run's outputs have removed every row; `Spec.Consistent`
quantifies over exactly these.  Runs may emit any permitted output, legal or
not; commitments are not separate events in this model.  Following text:
"Consistency requires confluence at every common input extension of the runs'
current inputs, not just at some larger common input extension that arrives
later.  Otherwise the runs could emit conflicting outputs before that larger
input arrives, and waiting cannot retract either output from the environment.
Even when later input could bring the runs to a common state, the environment
may already have acted on the outputs through channels the system does not
see, as in Lamport's 'anomalous behavior'.  And even when such a larger input
exists, it might never arrive."  The observability claim is the paper's
modeling rationale.

Lean: `Spec.Consistent`, a property of the spec's runs. -/
abbrev «def:consistency» {I O : Type} [PO I] [PO O] (sp : Spec I O) : Prop :=
  sp.Consistent

/-- After Def. `def:consistency`: "The two uses of confluence agree: runs are
confluent at `j` exactly when the rows of the outputs they have emitted are
confluent at `j` (Lemma `lem:reconciliation`)."  Rows of the emitted outputs
are confluent at `j` when some `u ∈ P(j)` extends every emitted output.
Lean: `reconciliation`; `X` is `emittedAll fam`. -/
theorem «sec:election-story/two-confluences» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (fam : List (RunW sp)) (j : I) (hj : ∀ r ∈ fam, r.fin.cur ≼ j) :
    ConfluentAt (fam.map RunW.fin) j ↔ ∃ u, sp.P j u ∧ ∀ o ∈ emittedAll fam, o ≼ u :=
  reconciliation fam j hj

/-- Closing paragraph of §2.1: "The election shows the arc in miniature. …
An output that is not legal needs a commitment; otherwise, runs that emit it
would diverge for good.  Next, we establish when that happens: when the spec
is not monotone."  Also: "the spec is monotone under the original order …;
under the equality order it is non-monotone, and some outputs can be emitted
only with a commitment."  Lean: the election's runs are consistent under the
output-extension order and not under the equality order. -/
theorem «sec:election-story/consistency» :
    elec.Consistent ∧ ¬ elecEq.Consistent :=
  ⟨elec_consistent, elecEq_not_consistent⟩

/-! ## The Functional CALM theorem (`sec:functional-calm-theorem`) -/

/-- "Events are relational
selections, and selections commute, so a run's remainder table depends only on
its last input and the outputs it emitted:"

**Lemma `lem:run-residual`** (Rows remaining after a run).  "If a run ends at
current input `i` after emitting `o₁,…,oₘ`, its remainder table is
`P[in ⪰ i, out ⪰ o₁, …, out ⪰ oₘ]`, the rows whose input extends `i` and whose
output extends each `o_r`."  Proof sketch: "Input and output events are both
relational selections, and selections commute; successive input selections
reduce to the last, since each input extends the one before."  `outs es` lists
the outputs emitted by the event list `es`. -/
theorem «lem:run-residual» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    {i : I} {es : List (Event I O)} {τ : State sp} (hx : Exec (canon sp i) es τ) :
    ∀ k u, τ.R k u ↔ (sp.P k u ∧ τ.cur ≼ k ∧ ∀ o ∈ outs es, o ≼ u) :=
  run_residual hx

/-- **Eq. `eq:run-residual`**: the table
`P[in ⪰ i, out ⪰ o₁, …, out ⪰ oₘ]`, "the rows whose input extends `i` and
whose output extends each `o_r`"; the emitted outputs are a list.
Lemma `lem:run-residual` says a run's remainder table is this table at its
current input and `outs es`. -/
abbrev «eq:run-residual» {I O : Type} [PO I] [PO O] (sp : Spec I O) (i : I)
    (os : List O) : Table I O :=
  fun k u => sp.P k u ∧ i ≼ k ∧ ∀ o ∈ os, o ≼ u

/-- Example after Lemma `lem:run-residual`: "For example, in the
equality-order variant of Figure `fig:nonmonotone-frame`, a run that emits `⊥`
at `ab·` keeps `P[in ⪰ ab·, out ⪰ ⊥]`: the single row `(ab·,⊥)`, as the figure
shows." -/
theorem «lem:run-residual/example» (k : Ballots) (o : ResE) :
    outputTable (canon elecEq bab) ⟨.bot⟩ k o ↔ (k = bab ∧ o = ⟨.bot⟩) :=
  elecEq_bot_single_row k o

/-- "A set of runs can be continued to a common state exactly when
their current remainder tables share a row at the target input:"

**Prop. `prop:confluence`** (Survivor test).  "Runs ending at states
`(i_r,R_r)`, `r = 1,…,k`, are confluent at a common input extension `j` of
their current inputs if and only if some row `(j,u)` is in every `R_r`.  For
any such `u`, `input(j)` followed by `output(u)` brings every run to the same
state, `(j, P[in ⪰ j, out ⪰ u])`."

Lean: the first conjunct is the equivalence; the second is the explicit
continuation, where `meetState sp j u _` is `(j, P[in ⪰ j, out ⪰ u])`. -/
theorem «prop:confluence» {I O : Type} [PO I] [PO O] {sp : Spec I O} :
    (∀ (fam : List (State sp)), (∀ σ ∈ fam, IsRun σ) → ∀ j : I, (∀ σ ∈ fam, σ.cur ≼ j) →
        (ConfluentAt fam j ↔ ∃ u, sp.P j u ∧ ∀ σ ∈ fam, σ.R j u)) ∧
      (∀ {σ : State sp}, IsRun σ → ∀ {j : I} {u : O} (hju : σ.R j u),
        Exec σ [.input j, .output u] (meetState sp j u (σ.sub _ _ hju))) :=
  ⟨survivor_test, fun h _ _ hju => survivor_exec h hju⟩

/-- Prop. `prop:confluence`, the survivor condition: "some row `(j,u)` is in
every `R_r`", for a family of final states given as a list.  After the
proposition: "In a functional spec the only row at `j` is `(j,f(j))`, so the
test asks whether `(j,f(j))` survives in every run."  (Formerly
`«eq:reconciliation»`, a displayed equation no longer in the paper.) -/
abbrev «prop:confluence/survivor-condition» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (fam : List (State sp)) (j : I) : Prop :=
  ∃ u, sp.P j u ∧ ∀ σ ∈ fam, σ.R j u

/-- Before Lemma `lem:confluence-legality`: "Consistency is a safety property
of the spec's runs: it guarantees that a common state exists, not that a
system reaches it (Section `sec:commitment-conflict`). … With the survivor test, consistency comes down to legality:"  The first sentence is the reading of Def.
`def:consistency` (prose); Lean states the second, which is the lemma in the
form `Spec.Consistent ↔ Spec.RunsLegal`. -/
theorem «sec:functional-calm-theorem/safety-of-runs» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    sp.Consistent ↔ sp.RunsLegal :=
  consistent_iff_runsLegal sp

/-- **Lemma `lem:confluence-legality`** (Confluence and legality).  "The runs
of an I/O specification are consistent if and only if no output event of any
run applies a commitment."  Proof sketch: "First assume the runs are
consistent, and suppose some run's output event `output(o)` applies `x_o`.  It
removes some row `(k,x)` such that no row at `k` extends both `x` and `o`.
Compare that run with one from the state before that event that instead takes
`input(k)` and then emits `x`: the two share no row at `k`, so by the Survivor
test they are not confluent at `k`, a contradiction.  Now assume no output
event applies a commitment, and take a family of runs and a common input
extension `j`.  Each run keeps a row `(i_r,u_r)` at its current input whose
output extends everything it emitted (Lemma `lem:run-residual`), and `u_r` is
legal at `σ_P(i_r)`.  Applying that legality one run at a time gives
`u ∈ P(j)` that extends every `u_r`, and the Survivor test gives confluence."

Lean: the event form is `consistent_iff_noOutputCommitment` (no output event
from a run state has a row in `Excluded_o`, the rows `x_o` removes); it is
`consistent_iff_runsLegal` (`Spec.RunsLegal`: every output at every run state is
`Exposable`) restated.  It holds for every spec, functional or not, with the
lifted legality of §3.2 (`Exposable`), which in a functional spec is Def.
`def:exposable`.  The third conjunct is the bridge used by both CALM proofs:
legality at every run state is the same as legality at every state reachable
without commitment (`runsLegal_iff_legalReachLegal`). -/
theorem «lem:confluence-legality» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    (sp.Consistent ↔
        ∀ τ : State sp, IsRun τ → ∀ o, τ.R τ.cur o → ∀ k x, ¬ Excluded τ o k x) ∧
      (sp.Consistent ↔ sp.RunsLegal) ∧ (sp.RunsLegal ↔ sp.LegalReachLegal) :=
  ⟨consistent_iff_noOutputCommitment sp, consistent_iff_runsLegal sp,
    runsLegal_iff_legalReachLegal sp⟩

/-- Example after Lemma `lem:confluence-legality`: "In the election under the
equality order, emitting `⊥` at `ab·` applies a commitment, since `⊥` is not
legal there, and the two runs of Section `sec:election-story` share no row at
`aba`."  Lean also records the incomparable values `f(ab·) = ⊥`,
`f(aba) = a` and the resulting non-monotonicity; the commitment itself is
`«sec:election-story/equality-order-commitment»`.  (Formerly
`«thm:functional-calm/example»`; the example after the theorem is no longer in
the paper.) -/
theorem «lem:confluence-legality/example» :
    winner bab = .bot ∧ winner baba = .win .a ∧ bab ≼ baba ∧ ¬ elecEq.MonotoneF ∧
      ¬ ConfluentAt [outputState (canon elecEq bab) ⟨.bot⟩
        ((elecEq_bot_single_row bab _).2 ⟨rfl, rfl⟩).1, canon elecEq baba] baba :=
  ⟨winner_bab, winner_baba, bab_le_baba, elecEq_not_monotone, elecEq_not_confluent⟩

/-- "In the functional case, monotonicity has a strong consequence: emitting
outputs never changes the state, which depends only on the input."

**Corollary `cor:state-by-input`** (State is fixed by input).  "In a monotone
functional specification, every run ending at current input `i` is in the
canonical state `σ_P(i)`, whatever outputs it emitted along the way."  Proof
sketch: "By monotonicity, the outputs a run emits remove no row at an input
extension of `i` (Lemma `lem:run-residual`)."

Lean: `run_canon_of_mono`, from the rows-remaining lemma; functionality is
not needed. -/
theorem «cor:state-by-input» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (_hf : sp.Functional) (hm : sp.MonotoneF) {τ : State sp} (hτ : IsRun τ) :
    τ = canon sp τ.cur :=
  run_canon_of_mono hm hτ

/-- After Cor. `cor:state-by-input`: "To be confluent at a common input
extension `j`, each run therefore needs only the single event `input(j)`,
which takes it to `σ_P(j)`, the state of a run that starts with all of the
input." -/
theorem «cor:state-by-input/input-suffices» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) (hm : sp.MonotoneF) {σ : State sp} (hrun : IsRun σ) {j : I}
    (hj : σ.cur ≼ j) : Exec σ [.input j] (canon sp j) :=
  functional_meet_by_input hf (consistent_of_mono hm) hrun hj

/-- "Monotonicity also governs legality:"

**Prop. `prop:functional-exposure-boundary`** (No-commitment test).  "A
functional I/O specification is monotone if and only if every output at every
state reachable without commitment is legal."  "An output at state `τ`" is an
`o` with `(τ.cur, o) ∈ τ.R`. -/
theorem «prop:functional-exposure-boundary» {I O : Type} [PO I] [PO O] (sp : Spec I O)
    (hf : sp.Functional) :
    sp.MonotoneF ↔ ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  functional_exposure_boundary hf

/-- Subsection opening: "Monotonicity is a static property of the spec's
table, and consistency is an operational property of the runs it allows.
Functional CALM bridges the two: the runs are consistent exactly when the spec
is monotone."

**Theorem `thm:functional-calm`** (Functional CALM).  "The runs of a
functional I/O specification are consistent if and only if the spec is
monotone."  Proof sketch: "By Lemma `lem:confluence-legality`, the runs are
consistent exactly when no output event of a run applies a commitment.  First
assume they are consistent, and suppose `f(i) ⋠ f(k)` for some `i ≼ k`.  At
`σ_P(i)` the event `output(f(i))` then applies `x_{f(i)}` and rules out input
`k`, a contradiction, so the spec is monotone.  Now assume the spec is
monotone.  It can emit every current output without commitment (Proposition
`prop:functional-exposure-boundary`), so by induction on its length every run
is commitment-free, and consistency follows."

Lean: `functional_calm_via_legality`, which follows the paper's order
(Lemma `lem:confluence-legality`, the bridge, Prop.
`prop:functional-exposure-boundary`). -/
theorem «thm:functional-calm» {I O : Type} [PO I] [PO O] (sp : Spec I O)
    (hf : sp.Functional) : sp.Consistent ↔ sp.MonotoneF :=
  functional_calm_via_legality hf

/-- From the proof sketch of Theorem `thm:functional-calm`: "suppose
`f(i) ⋠ f(k)` for some `i ≼ k`.  At `σ_P(i)` the event `output(f(i))` then
applies `x_{f(i)}` and rules out input `k`".  ("It can emit every current
output without commitment" is the forward direction of Prop.
`prop:functional-exposure-boundary`.) -/
theorem «prop:functional-exposure-boundary/nonmonotone-excludes» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} (hf : sp.Functional) {i k : I} {o u : O}
    (hik : i ≼ k) (hio : sp.P i o) (hku : sp.P k u) (hn : ¬ o ≼ u) :
    Excluded (canon sp i) o k u :=
  nonmono_excludes hf hik hio hku hn

/-- **Eq. `eq:query-monotonicity`**.  "Classical CALM fits, with inputs `J` as
sets of facts ordered by inclusion and output views `Q(J)` ordered by
inclusion.  Functional monotonicity becomes `J ⊆ J' ⟹ Q(J) ⊆ Q(J')`, the
standard definition of a monotone query; positive Datalog satisfies it, and
negation may not.  Functional CALM generalizes the statement to arbitrary
input and output orders, whatever formalism expresses the spec."

Lean: fact sets and answer sets are `PSet F`, `PSet A` (predicates under
inclusion); `querySpec Q` is the graph of `Q`.  It is functional, its
functional monotonicity is exactly the displayed implication, and hence (by
Functional CALM) it is consistent exactly when the implication holds. -/
theorem «eq:query-monotonicity» {F A : Type} (Q : PSet F → PSet A) :
    (querySpec Q).Functional ∧
    ((querySpec Q).MonotoneF ↔
      ∀ J J' : PSet F, (∀ x, J.mem x → J'.mem x) → ∀ a, (Q J).mem a → (Q J').mem a) ∧
    ((querySpec Q).Consistent ↔
      ∀ J J' : PSet F, (∀ x, J.mem x → J'.mem x) → ∀ a, (Q J).mem a → (Q J').mem a) :=
  ⟨querySpec_functional Q, query_monotone_iff Q, query_consistent_iff Q⟩

end CC.Paper
