import CoordCriterion.Figures
import CoordCriterion.CompleteCALM.Legality

/-!
# Paper §2: Functional CALM (`sections/functional-calm.tex`)

Statement layer for Section 2 (`sec:functional-calm`), including
Figure `fig:election-frames` and Figure `fig:nonmonotone-frame`, followed by
the claims of §7 (`sections/discussion.tex`) about the same election.

How to read this file: open `sections/functional-calm.tex` next to it.  The
headers below are the paper's subsections, in order.  Every numbered result is
a declaration named by its LaTeX label in guillemets (`«thm:functional-calm»`);
inline claims are named `«<enclosing label>/<slug>»`.  Each docstring quotes
the paper, and, when the Lean reading differs, says how.  Proofs are
one-line pointers into the library; the full statement is always written out.

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

/-! ## The framework by example (`sec:election-story`) -/

/-- "The *input order* records accumulated ballots: `ab· ⪰ a··`, while `aa·`
and `ab·` are incomparable." -/
theorem «sec:election-story/input-order» :
    bad ≼ bab ∧ ¬ baa ≼ bab ∧ ¬ bab ≼ baa := by decide

/-- "The *output order* says which announcements are safe to build on: `⊥`
claims nothing, so either winner extends it, while `a` and `b` are
incomparable." -/
theorem «sec:election-story/output-order» :
    Res.bot ≼ Res.win .a ∧ Res.bot ≼ Res.win .b ∧
      ¬ Res.win .a ≼ Res.win .b ∧ ¬ Res.win .b ≼ Res.win .a :=
  ⟨Or.inl rfl, Or.inl rfl, (by rintro (h | h) <;> cases h), (by rintro (h | h) <;> cases h)⟩

/-- "The functional table is *monotone* … Here, for example, the input
sequence `a·· ⪯ ab· ⪯ aba` monotonically produces the output sequence
`⊥ ⪯ ⊥ ⪯ a`."  The election (output-extension order) is monotone, and the chain is
as stated. -/
theorem «sec:election-story/monotone» :
    elec.MonotoneF ∧
      (bad ≼ bab ∧ bab ≼ baba) ∧
      (winner bad = .bot ∧ winner bab = .bot ∧ winner baba = .win .a) ∧
      (Res.bot ≼ Res.bot ∧ Res.bot ≼ Res.win .a) :=
  ⟨elec_monotone, by decide, by decide, ⟨Or.inl rfl, Or.inl rfl⟩⟩

/-- Fig. `fig:election-frames`: "Only rows whose input extends `a··` are
shown."  The nine printed pairs (`Figures.Elec.printed`) are exactly the rows
of the election at inputs `⪰ a··`. -/
theorem «fig:election-frames/printed-rows» (k : Ballots) (o : Res) :
    (k, o) ∈ Figures.Elec.printed ↔ (bad ≼ k ∧ elec.P k o) :=
  Figures.Elec.printed_complete k o

/-- Fig. `fig:election-frames`(a): "Initial state, current input `a··` …
upper fiber `{⊥,a,b}`; undetermined; `⊥` needs no commitment."  Panel (a) is
the canonical state `σ_P(a··)`; "upper fiber is all of `{⊥,a,b}`" is stated
as "every output occurs in some remaining row". -/
theorem «fig:election-frames/a» :
    (∀ o : Res, ∃ k, (canon elec bad).R k o) ∧ ¬ Determined (canon elec bad) ∧
      Exposable (canon elec bad) .bot := by
  refine ⟨fun o => (Figures.Elec.upper_ab o).1, ?_, elec_panels_exposable.1⟩
  rintro ⟨o, h⟩
  obtain ⟨k₁, h₁⟩ := (Figures.Elec.upper_ab .bot).1
  obtain ⟨k₂, h₂⟩ := (Figures.Elec.upper_ab (.win .a)).1
  cases (h _ _ h₁).trans (h _ _ h₂).symm

/-- Fig. `fig:election-frames`(b) and §2.1 "Input and determination": "When
`v₂`'s ballot for `b` arrives, the event `input(ab·)` produces panel (b),
causing the table to lose rows whose inputs no longer extend the ballots received; such inputs
are now illegal. … in panel (b) it is `{⊥,a,b}`."  The CIDR version says "the
input event `input(ab·)`".  Also "`⊥` needs no commitment" (`⊥` is a legal output). -/
theorem «fig:election-frames/b» :
    Step (canon elec bad) (.input bab) (canon elec bab) ∧
      (∀ o : Res, ∃ k, (canon elec bab).R k o) ∧ ¬ Determined (canon elec bab) ∧
      Exposable (canon elec bab) .bot :=
  ⟨Dist.step_canon_input elec (by decide) ⟨_, rfl⟩, fun o => (Figures.Elec.upper_ab o).2,
   elec_panel_b_undetermined, elec_panels_exposable.2.1⟩

/-- Fig. `fig:election-frames`(b), the printed rows: of the rows at inputs
`⪰ a··`, exactly `(ab·,⊥)`, `(aba,a)`, `(abb,b)` remain; every other printed
row is gray because its input does not extend `ab·` (input loss). -/
theorem «fig:election-frames/b-rows» (k : Ballots) (o : Res) (hk : bad ≼ k) :
    ((canon elec bab).R k o ↔
        ((k = bab ∧ o = .bot) ∨ (k = baba ∧ o = .win .a) ∨
          (k = Figures.Elec.babb ∧ o = .win .b))) ∧
      (elec.P k o → ¬ (canon elec bab).R k o → ¬ bab ≼ k) :=
  Figures.Elec.panel_b k o hk

/-- Fig. `fig:election-frames`(c) and §2.1: "If `v₂` instead votes for `a`,
as in panel (c), the upper fiber is `{a}`.  The state is *determined*: input
alone has resolved the outcome, without commitment"; caption: "`a` needs no
commitment". -/
theorem «fig:election-frames/c» :
    Step (canon elec bad) (.input baa) (canon elec baa) ∧
      (∀ o, (∃ k, (canon elec baa).R k o) ↔ o = .win .a) ∧
      Determined (canon elec baa) ∧ Exposable (canon elec baa) (.win .a) :=
  ⟨Dist.step_canon_input elec (by decide) ⟨_, rfl⟩, Figures.Elec.upper_c,
   elec_panel_c_determined, elec_panels_exposable.2.2⟩

/-- Fig. `fig:election-frames`(d) and §2.1: "the system acts as a registrar:
when it emits `⊥` at `ab·`, it also closes the polls.  Its irrevocable
*commitment* removes the still-possible `aba` and `abb` rows but leaves the
current input unchanged, and so makes `⊥` the final result."  Caption: "In (d)
the registrar closes the polls, a commitment that emitting `⊥` does not
require, and emits `⊥`."

Closing the polls is the commitment `Figures.closePolls` (a commitment in the
sense of Def. `def:commitment`, §4.3); the registrar applies it in the
commitment event `apply([closePolls])` and then emits `⊥` by `output(⊥)`, a
run under any basis containing `closePolls`.  It ends at `panelD`, whose only row is
`(ab·,⊥)`; the rows it removes beyond `(b)` are exactly `(aba,a)`, `(abb,b)`
(the struck rows); the state is determined with result `⊥`. -/
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

/-- Fig. `fig:election-frames`(d), legend: "Gray: removed from the remainder
table; struck through if by a commitment, otherwise lost after an input event."  A
printed row is absent from panel (d) iff its input does not extend `ab·`
(gray) or it is one of the two struck rows. -/
theorem «fig:election-frames/d-gray» (k : Ballots) (o : Res) (hk : bad ≼ k) (hS : elec.P k o) :
    ¬ Figures.Elec.panelD.R k o ↔
      (¬ bab ≼ k ∨ (k = baba ∧ o = .win .a) ∨ (k = Figures.Elec.babb ∧ o = .win .b)) :=
  Figures.Elec.panelD_gray k o hk hS

/-- Fig. `fig:election-frames` caption and §2.1: "a commitment that emitting
`⊥` does not require … Emitting `⊥` by itself would need no commitment,
since every output still possible extends it."  At (b), `⊥` is a legal output,
  `Excluded_o` is empty, and `output(⊥)` removes no row. -/
theorem «fig:election-frames/bot-alone» :
    Exposable (canon elec bab) .bot ∧ (¬ ∃ k x, Excluded (canon elec bab) .bot k x) ∧
      outputTable (canon elec bab) .bot = (canon elec bab).R :=
  Figures.Elec.bot_alone_at_b

/-- Fig. `fig:nonmonotone-frame`: "Panel (b) under the equality order, after
`output(⊥)`. … upper fiber `{⊥}`; determined."  Under `elecEq`, `output(⊥)`
at `σ_P(ab·)` excludes `aba` and leaves the single row `(ab·,⊥)`. -/
theorem «fig:nonmonotone-frame» :
    Excluded (canon elecEq bab) ⟨.bot⟩ baba ⟨winner baba⟩ ∧
      ∀ k o, outputTable (canon elecEq bab) ⟨.bot⟩ k o ↔ (k = bab ∧ o = ⟨.bot⟩) :=
  ⟨elecEq_bot_excludes, elecEq_bot_single_row⟩

/-- Fig. `fig:nonmonotone-frame` caption: "The commitment the registrar chose in
Figure `fig:election-frames`(d) is required here." -/
theorem «fig:nonmonotone-frame/matches-d» (k : Ballots) (r : Res) :
    Figures.Elec.panelD.R k r ↔ outputTable (canon elecEq bab) ⟨.bot⟩ k ⟨r⟩ :=
  Figures.Elec.panelD_matches_e k r

/-- §2.1 "Output and consistency": "An output is a *legal output* when every
item in the upper fiber extends it; no future output contradicts it.
Hence `⊥` is a legal output in panels (a) and (b), and `a` in panel (c)." -/
theorem «sec:election-story/exposable-panels» :
    Exposable (canon elec bad) .bot ∧ Exposable (canon elec bab) .bot ∧
      Exposable (canon elec baa) (.win .a) :=
  elec_panels_exposable

/-- §2.1: "under the equality order … `⊥` is incompatible with future
winners, so emitting it requires a commitment": at `σ_P(ab·)`, `⊥` is not
a legal output under `elecEq`. -/
theorem «sec:election-story/equality-order-commitment» :
    ¬ Exposable (canon elecEq bab) ⟨.bot⟩ :=
  fun h => (exposable_iff_empty _ _).1 h ⟨_, _, elecEq_bot_excludes⟩

/-- §2.1: "The need to issue a commitment is a property solely of the table and
its orders.  Rows `(ab·,⊥)` and `(aba,a)` have the common input extension
`aba`, but under
the equality order no output at `aba` extends both outputs `⊥` and `a`." -/
theorem «sec:election-story/obstruction» :
    elecEq.P bab ⟨.bot⟩ ∧ elecEq.P baba ⟨.win .a⟩ ∧ bab ≼ baba ∧ baba ≼ baba ∧
      ¬ ∃ u, elecEq.P baba u ∧ (⟨.bot⟩ : ResE) ≼ u ∧ (⟨.win .a⟩ : ResE) ≼ u :=
  ⟨by show _ = _; rw [winner_bab], by show _ = _; rw [winner_baba], bab_le_baba, PO.refl _,
   fun ⟨_, _, h₁, h₂⟩ => by cases (show (⟨.bot⟩ : ResE) = ⟨.win .a⟩ from h₁.trans h₂.symm)⟩

/-- §2.1: "A run that emits `⊥` at `ab·` and one that receives `aba` cannot be
reconciled at `aba`" (equality order).  The two runs end at
`(ab·, P[in ⪰ ab·, out ⪰ ⊥])` and `σ_P(aba)`. -/
theorem «sec:election-story/not-reconciled» :
    ¬ ConfluentAt [outputState (canon elecEq bab) ⟨.bot⟩
        ((elecEq_bot_single_row bab _).2 ⟨rfl, rfl⟩).1, canon elecEq baba] baba :=
  elecEq_not_confluent

/-- §2.1: "Input and output events form a transition system over
specification states, and the runs of a spec are consistent when they are
confluent … Section `sec:functional-calm-theorem` shows that for functional
tables the runs are consistent exactly when the spec is monotone": the
election's runs are consistent under the output-extension order and not under
the equality order. -/
theorem «sec:election-story/consistency» :
    elec.Consistent ∧ ¬ elecEq.Consistent :=
  ⟨elec_consistent, elecEq_not_consistent⟩

/-! ## Specifications and states (`sec:functional-specifications`) -/

/-- **Def. `def:functional-specification`** (Functional ordered
specification, total).  "A tuple `(I, ≼, O, ≼, P)`, where `(I,≼)` and `(O,≼)` are
partially ordered input and output types, and `P ⊆ I × O` is its *table of
possibilities*: a typed relation … in which every input appears in at least
one row (`P` is total on `I`) and at most one (a functional dependency)."

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

/-- **Def. `def:functional-monotonicity`** (Functional monotonicity,
monotone).  "`Spec`,
with induced function `f`, is *monotone* if `i ≼ j ⟹ f(i) ≼ f(j)`."

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

/-- **Def. `def:residual-state`** (Specification state, current input,
remainder table).  "A pair `σ = (i,R)`, where `i ∈ I` is the *current input*
and `R ⊆ P` is the *remainder table*, such that: (1) `R` contains a row at
`i`; and (2) `R` contains only rows at input extensions of `i`."

Lean: `State sp` with fields `cur`, `R`, `sub` (`R ⊆ P`), `hasCur` (1) and
`above` (2). -/
abbrev «def:residual-state» {I O : Type} [PO I] [PO O] (sp : Spec I O) := State sp

/-- **Def. `def:legal-input`**.  "An input `k` is *legal* at a state `(i,R)`
when `R` contains a row at `k`."  Lean: `∃ u, σ.R k u`. -/
abbrev «def:legal-input» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (k : I) : Prop :=
  ∃ u, σ.R k u

/-- **Eq. `eq:canonical-state`**: the canonical state `σ_P(i) = (i, P[in ⪰ i])`. -/
abbrev «eq:canonical-state» {I O : Type} [PO I] [PO O] (sp : Spec I O) (i : I) : State sp :=
  canon sp i

/-- "The *canonical state at `i`* is the state at `i` with no rows removed: it
keeps every row of `P` at `i` and its input extensions":
every state's table is contained in that of the canonical state at its
current input. -/
theorem «eq:canonical-state/largest» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) : ∀ k x, σ.R k x → (canon sp σ.cur).R k x :=
  state_le_canon σ

/-- "An input event from a canonical state leads to another canonical state." -/
theorem «eq:canonical-state/input-moves-canonical» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} {i j : I} {τ : State sp} (h : Step (canon sp i) (.input j) τ) :
    τ = canon sp j :=
  input_canon h

/-- **Def. `def:fiber`** (Fiber, upper fiber).  "Let `R` be a table and `k`
an input.  The *fiber* of `R` at `k` is `R(k) = π_out(R[in = k])`, the outputs
paired with `k`.  The *upper fiber* of `R` at `k` is `π_out(R[in ⪰ k])`, the
outputs paired with `k` or any of its input extensions."

Lean: the fiber is `R k`, a predicate on outputs; the upper fiber is
`fun o => ∃ k', k ≼ k' ∧ R k' o` (`«def:fiber/upper»`). -/
abbrev «def:fiber» {I O : Type} (R : Table I O) (k : I) : O → Prop := R k

/-- Def. `def:fiber`: the upper fiber of `R` at `k`, `π_out(R[in ⪰ k])`. -/
abbrev «def:fiber/upper» {I O : Type} [PO I] (R : Table I O) (k : I) : O → Prop :=
  fun o => ∃ k', k ≼ k' ∧ R k' o

/-- Def. `def:fiber`: "For a state `(i,R)`, the upper fiber at `i` is
`π_out(R)`: every output still possible."  Every row of a state's table is at an
input extension of its current input, so the two descriptions agree. -/
theorem «def:fiber/state» {I O : Type} [PO I] [PO O] {sp : Spec I O} (σ : State sp)
    (o : O) : «def:fiber/upper» σ.R σ.cur o ↔ ∃ k, σ.R k o :=
  ⟨fun ⟨k, _, h⟩ => ⟨k, h⟩, fun ⟨k, h⟩ => ⟨k, σ.above k o h, h⟩⟩

/-! ## Input and output events (`sec:functional-events`) -/

/-- **Eq. `eq:input-event`**: for a state `(i,R)` and legal `j` with `i ≼ j`,
`(i,R) --input(j)--> (j, R[in ⪰ j])`.

Lean: `Step σ (.input j) τ` holds exactly when `j` is legal, `τ.cur = j` and
`τ.R = inputTable σ j` (constructor `Step.input`); `inputTable σ j` is
`R[in ⪰ j]`.  Legality already implies `i ≼ j` (`«eq:input-event/legal-expands»`). -/
abbrev «eq:input-event» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (j : I) : Table I O :=
  inputTable σ j

/-- The paper's input event asks for `j` legal *and* `i ≼ j`; the second
follows from the first, since the remainder table contains only rows at
input extensions of `i`. -/
theorem «eq:input-event/legal-expands» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (j : I) (h : ∃ u, σ.R j u) : σ.cur ≼ j :=
  legal_above σ j h

/-- "`input(j)` then `input(k)` has the effect of `input(k)` alone; `input(i)`
at `(i,R)` has no effect." -/
theorem «sec:functional-events/input-cumulative» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} :
    (∀ {σ τ ρ : State sp} {j k : I},
        Step σ (.input j) τ → Step τ (.input k) ρ → Step σ (.input k) ρ) ∧
      (∀ {σ τ : State sp}, Step σ (.input σ.cur) τ → τ = σ) :=
  ⟨input_input, input_self⟩

/-- **Def. `def:output-event`** (Output event).  "At a state `(i,R)` with
current output `o`, the *output event* `output(o)` atomically keeps only the rows whose outputs extend `o`,
  and then emits `o`: `(i,R) --output(o)--> (i, R[out ⪰ o])`."

Lean: `Step σ (.output o) τ` (constructor `Step.output`) requires
`σ.R σ.cur o` and sets `τ.R = outputTable σ o = R[out ⪰ o]`.  The general
definition is used for every specification (it is also Def.
`def:lifted-output-event`); in a functional specification "`R' ≠ R`" is
exactly "some row is in `Excluded_o`" (`«def:output-event/commitment-iff-excluded»`). -/
abbrev «def:output-event» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) : Table I O :=
  outputTable σ o

  /-- **Def. `def:canonical-commitment-functional`**.  "When `o` is not legal,
  equivalently `R' ≠ R`, some rows have outputs that do not extend `o`, and the
  transition applies the *canonical commitment* `x_o(i,R) = (i,R')`, which
  removes them.  In a functional table each input has only one row, so `x_o`
  rules out those rows' inputs (`x_o` is a commitment)."

Lean: `canonicalCommitment o : Commitment sp` (`commitmentApp o`): the commitment that removes the
rows in `Excluded_o`, defined at states where `o ∈ R(i)` and `Excluded_o ≠ ∅`. -/
noncomputable abbrev «def:canonical-commitment-functional» {I O : Type} [PO I] [PO O] {sp : Spec I O} (o : O) :
    Commitment sp :=
  canonicalCommitment o

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

/-- "The current row `(i,o)` remains, since `o` extends itself, so the event
always ends at a specification state with current input `i`." -/
theorem «sec:functional-events/output-ends-at-state» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} (σ : State sp) (o : O) (h : σ.R σ.cur o) :
    Step σ (.output o) (outputState σ o h) ∧ (outputState σ o h).R σ.cur o ∧
      (outputState σ o h).cur = σ.cur :=
  ⟨step_outputState σ o h, ⟨h, PO.refl o⟩, rfl⟩

/-- "Systems may issue more commitments than an output requires, as the
registrar does in Figure `fig:election-frames`(d), but such extra commitments
are a system's choice, not the spec's (Section `sec:systems`)."  For the
registrar of panel (d): its run `apply([closePolls])`, `output(⊥)` has an
observably equivalent `output(⊥)` of the transition system, whose table
contains panel (d)'s.  The general statement
is Lemma `lem:canonical-equivalent` (`CC.canonical_equivalent`, §4.3). -/
theorem «sec:functional-events/extra-commitments» (B : CommitmentBasis elec) (hB : B Figures.closePolls) :
    ∃ ρ', Exec (canon elec bab) [.output .bot] ρ' ∧ ρ'.cur = bab ∧
      ∀ k u, Figures.Elec.panelD.R k u → ρ'.R k u :=
  Figures.Elec.registrar_canonical B hB

/-- **Def. `def:exposable`** (Legal output).  "The output `o` at `(i,R)`
is a *legal output* when every output in the upper fiber extends `o`."

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

/-- "Emitting an output can require removing rows that no remaining output
covers.  We call such a removal a commitment:"

**Def. `def:commitment`** (Commitment).  "A commitment is a partial function `e`
on specification states that removes a nonempty set of rows, none of which is
extended by a row that remains at the same input.  That is, whenever
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

/-- §2.3 "Determination": "A state is *determined* when its upper fiber has
one element."  Lean: `CALM.Determined σ` is `∃ o, ∀ k x, σ.R k x → x = o`;
the upper fiber `π_out(R)` is nonempty, so this is "has exactly one element". -/
abbrev «sec:functional-events/determined» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) : Prop :=
  Determined σ

/-- "Determined": upper fiber has exactly one element. -/
theorem «sec:functional-events/determined-one-element» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} (σ : State sp) :
    Determined σ ↔ ∃ o, (∃ k, σ.R k o) ∧ ∀ k x, σ.R k x → x = o :=
  determined_upper_fiber σ

/-- "A spec with multiple distinct outputs can have undetermined states, as in
panel (b) … An input event can achieve determination through input loss, as in
panel (c), and a commitment can do so by ruling out inputs that would otherwise
remain possible, as in panel (d)." -/
theorem «sec:functional-events/determination-examples» :
    elec.Functional ∧ ¬ Determined (canon elec bab) ∧ Determined (canon elec baa) ∧
      Determined Figures.Elec.panelD :=
  ⟨elec_functional, elec_panel_b_undetermined, elec_panel_c_determined,
   Figures.Elec.panelD_determined.1⟩

/-- "An event from a determined state always leads to another determined state
with the same output: events only remove rows, and a row at the current input
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

/-! ## Executions and consistency (`sec:executions`) -/

/-- **Def. `def:specification-event`**.  "Input and output events are
*specification events*: they change the specification state.  We call them
simply *events* when unambiguous."  Lean: `Event I O` (two constructors
`.input`, `.output`). -/
abbrev «def:specification-event» (I O : Type) := Event I O

/-- **Def. `def:transition-system`**.  "The *transition system* consists of
specification states and specification events."  Lean: `State sp` and
`Event I O` together with `Step σ e τ`. -/
abbrev «def:transition-system» {I O : Type} [PO I] [PO O] (sp : Spec I O) : Prop :=
  ∀ (σ : State sp) (e : Event I O), ∃ τ, Step σ e τ ∨ ¬ ∃ τ, Step σ e τ

/-- **Def. `def:run`** (Canonical run).  "A *canonical run*, or just *run*, is any finite transition sequence of
the transition system from the canonical state `σ_P(i)` at some input `i`."
The following scope convention says: "Runs range over every behavior the spec
permits, not only the behaviors a particular system happens to produce.  A
system that never uses some of the spec's latitude is better described by a
narrower spec.  For the spec as written, we assume that any permitted behavior
may occur."  This is the paper's modeling convention; it is reflected in
`IsRun` ranging over all runs of the transition system.

Lean: `Exec σ es τ` is execution along the event list `es`; `IsRun τ` says
that `τ` is the final state of some run (`∃ i es, Exec (canon sp i) es τ`). -/
abbrev «def:run» {I O : Type} [PO I] [PO O] {sp : Spec I O} (τ : State sp) : Prop :=
  IsRun τ

/-- "A run is *commitment-free* when none of its output events applies a
commitment.  A state is
*reachable without commitment* when some commitment-free run reaches it."
Lean: `ExecCF` and `ReachableCF`. -/
abbrev «def:run/reachable-without-commitment» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (τ : State sp) : Prop :=
  ReachableCF τ

/-- **Lemma `lem:run-residual`** (Rows remaining after a run).  "If a run ends
at current input `i` after emitting `o₁,…,oₘ`, its remainder table is
`P[in ⪰ i, out ⪰ o₁, …, out ⪰ oₘ]`."  `outs es` lists the outputs emitted by
the event list `es`. -/
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

/-- Example after Lemma `lem:run-residual`: "in the equality-order variant …
a run that emits `⊥` at `ab·` keeps `P[in ⪰ ab·, out ⪰ ⊥]`: the single row
`(ab·,⊥)`." -/
theorem «lem:run-residual/example» (k : Ballots) (o : ResE) :
    outputTable (canon elecEq bab) ⟨.bot⟩ k o ↔ (k = bab ∧ o = ⟨.bot⟩) :=
  elecEq_bot_single_row k o

/-- **Def. `def:confluence`** (Confluence at an input).  "A finite family of
runs ending at states `(i₁,R₁),…,(i_k,R_k)` is *confluent at* `j`, a common
input extension of their current inputs, when each can be continued to a common
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
not; commitments are not separate events in this model.  "Consistency requires
  confluence at every common input extension of the runs' current inputs, not
  just at some larger common input extension that arrives later.  Otherwise the
  runs could emit conflicting outputs before that larger input arrives.  In the
  equality-order election, `f(ab·)=⊥` and `f(aba)=a` are incomparable.  One run
  can emit `⊥` at `ab·`, while another accepts `aba` and can emit `a`.  The two
  runs are not confluent at their common input extension `aba`, and waiting
  cannot retract either output from the environment.  More generally, even when
  later input could bring the runs to a common state, the environment may
  already have acted on the outputs through channels the system does not see,
  as in Lamport's 'anomalous behavior'.  And even when such a larger input
  exists, it might never arrive."  The observability claim
  is the paper's modeling rationale.

Lean: `Spec.Consistent`, a property of the spec's runs. -/
abbrev «def:consistency» {I O : Type} [PO I] [PO O] (sp : Spec I O) : Prop :=
  sp.Consistent

/-- **Prop. `prop:confluence`** (Survivor test).  "Runs ending at states
`(i_r,R_r)` are confluent at a common input extension `j` of their current inputs if and
only if some row `(j,u)` is in every `R_r`.  For any such `u`, `input(j)`
followed by `output(u)` brings every run to the same state,
`(j, P[in ⪰ j, out ⪰ u])`."

Lean: the first conjunct is the equivalence; the second is the explicit
continuation, where `meetState sp j u _` is `(j, P[in ⪰ j, out ⪰ u])`. -/
theorem «prop:confluence» {I O : Type} [PO I] [PO O] {sp : Spec I O} :
    (∀ (fam : List (State sp)), (∀ σ ∈ fam, IsRun σ) → ∀ j : I, (∀ σ ∈ fam, σ.cur ≼ j) →
        (ConfluentAt fam j ↔ ∃ u, sp.P j u ∧ ∀ σ ∈ fam, σ.R j u)) ∧
      (∀ {σ : State sp}, IsRun σ → ∀ {j : I} {u : O} (hju : σ.R j u),
        Exec σ [.input j, .output u] (meetState sp j u (σ.sub _ _ hju))) :=
  ⟨survivor_test, fun h _ _ hju => survivor_exec h hju⟩

/-- **Eq. `eq:reconciliation`**: "`(j,u) ∈ R_r` for every `r`, for some
`u ∈ P(j)`" — the survivor condition of Prop. `prop:confluence`, for a family
of final states given as a list. -/
abbrev «eq:reconciliation» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (fam : List (State sp)) (j : I) : Prop :=
  ∃ u, sp.P j u ∧ ∀ σ ∈ fam, σ.R j u

/-- Before Lemma `lem:confluence-legality`: "Consistency is a safety property
of the spec's runs: it guarantees that a common state exists, not that a
system reaches it."  "Whether runs are consistent depends on the outputs they
emit.  Confluence fails exactly when some run can emit an output that is not
legal."  The first sentence is the reading of Def. `def:consistency` (prose);
the second is the lemma. -/
theorem «sec:executions/safety-of-runs» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    sp.Consistent ↔ sp.RunsLegal :=
  consistent_iff_runsLegal sp

/-- **Lemma `lem:confluence-legality`** (Confluence and legality).  "The runs
of an I/O specification are consistent if and only if every output that a run
can emit is legal at the state where it is emitted."  Proof sketch: "If a run
can emit an output `o` that is not legal, `output(o)` removes some row `(k,x)`
such that no row at `k` extends both `x` and `o`.  One continuation of the run
emits `o`; another takes `input(k)` and then emits `x`.  The two share no row
at `k`, so by the Survivor test they are not confluent at `k`.  Conversely,
suppose every output is legal, and take a family of runs and a common input
extension `j`.  Pick for each run a row `(i_r,u_r)` remaining at its current
input; `u_r` extends everything that run emitted (Lemma `lem:run-residual`).
Each `u_r` is legal at `σ_P(i_r)`, the canonical state of its input, so every
output at an input extension of `i_r` has an output extension there that also
extends `u_r`.  Taking the runs one at a time gives `u ∈ P(j)` that extends
every `u_r`.  The row `(j,u)` remains in every run, and the Survivor test gives
confluence."

Lean: `consistent_iff_runsLegal` (`Spec.RunsLegal`: every output at every run
state is `Exposable`).  It holds for every spec, functional or not, with the
lifted legality of §3.2 (`Exposable`), which in a functional spec is Def.
`def:exposable`.  The second conjunct is the bridge used by both CALM proofs:
legality at every run state is the same as legality at every state reachable
without commitment (`runsLegal_iff_legalReachLegal`). -/
theorem «lem:confluence-legality» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    (sp.Consistent ↔ sp.RunsLegal) ∧ (sp.RunsLegal ↔ sp.LegalReachLegal) :=
  ⟨consistent_iff_runsLegal sp, runsLegal_iff_legalReachLegal sp⟩

/-! ## The Functional CALM theorem (`sec:functional-calm-theorem`) -/

/-- **Theorem `thm:functional-calm`** (Functional CALM).  "The runs of a
functional I/O specification are consistent if and only if the spec is
monotone."  Proof sketch: "By Lemma `lem:confluence-legality`, the runs are
consistent exactly when every output a run can emit is legal.  If every output
at every state reachable without commitment is legal, every run is reachable
without commitment, so this is the condition of Proposition
`prop:functional-exposure-boundary`, which holds exactly when the spec is
monotone."  Section opening: "Monotonicity is defined by a spec's table and
orders alone, consistency by its runs.  Functional CALM shows that one holds
exactly when the other does.  By Lemma `lem:confluence-legality`, the question
is when every output a run can emit is legal."

Lean: `functional_calm_via_legality`, which follows the paper's order
(Lemma `lem:confluence-legality`, the bridge, Prop.
`prop:functional-exposure-boundary`). -/
theorem «thm:functional-calm» {I O : Type} [PO I] [PO O] (sp : Spec I O)
    (hf : sp.Functional) : sp.Consistent ↔ sp.MonotoneF :=
  functional_calm_via_legality hf

/-- Example after Theorem `thm:functional-calm`: "In the equality-order
election, `f(ab·) = ⊥` and `f(aba) = a` are incomparable: a run that emits `⊥`
at `ab·` and one that accepts `aba` are the two runs … that can never be
reconciled." -/
theorem «thm:functional-calm/example» :
    winner bab = .bot ∧ winner baba = .win .a ∧ bab ≼ baba ∧ ¬ elecEq.MonotoneF ∧
      ¬ ConfluentAt [outputState (canon elecEq bab) ⟨.bot⟩
        ((elecEq_bot_single_row bab _).2 ⟨rfl, rfl⟩).1, canon elecEq baba] baba :=
  ⟨winner_bab, winner_baba, bab_le_baba, elecEq_not_monotone, elecEq_not_confluent⟩

/-- **Corollary `cor:state-by-input`** (State is fixed by input).  "In the
functional case, monotonicity has a strong consequence: emitting outputs never
changes the state, which depends only on the input."  "In a monotone
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

/-- After Cor. `cor:state-by-input`: "To be confluent at a common input extension
`j`, each run therefore needs only the single event `input(j)`, which takes it
to `σ_P(j)`." -/
theorem «cor:state-by-input/input-suffices» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) (hm : sp.MonotoneF) {σ : State sp} (hrun : IsRun σ) {j : I}
    (hj : σ.cur ≼ j) : Exec σ [.input j] (canon sp j) :=
  functional_meet_by_input hf (consistent_of_mono hm) hrun hj

/-- **Prop. `prop:functional-exposure-boundary`** (No-commitment test).  "A
functional I/O specification is monotone if and only if every output at
every state reachable without commitment is a legal output."  "An output at state
`τ`" is an `o` with `(τ.cur, o) ∈ τ.R`. -/
theorem «prop:functional-exposure-boundary» {I O : Type} [PO I] [PO O] (sp : Spec I O)
    (hf : sp.Functional) :
    sp.MonotoneF ↔ ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  functional_exposure_boundary hf

/-- After Prop. `prop:functional-exposure-boundary`: "A monotone spec can
thus emit every current output without commitment. If a spec is non-monotone,
then for some `i ≼ k`, `f(i) ⋠ f(k)`, so at `σ_P(i)` the event `output(f(i))`
applies `x_{f(i)}` and rules out input `k`." -/
theorem «prop:functional-exposure-boundary/nonmonotone-excludes» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} (hf : sp.Functional) {i k : I} {o u : O}
    (hik : i ≼ k) (hio : sp.P i o) (hku : sp.P k u) (hn : ¬ o ≼ u) :
    Excluded (canon sp i) o k u :=
  nonmono_excludes hf hik hio hku hn

/-- **Eq. `eq:query-monotonicity`**.  "Classical CALM fits the pattern with
inputs `J` as sets of facts ordered by inclusion and output tables `Q(J)`
ordered by inclusion.  Functional monotonicity becomes
`J ⊆ J' ⟹ Q(J) ⊆ Q(J')`, the standard definition of a monotone query …
Functional CALM generalizes the statement to arbitrary input and output
orders."

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
