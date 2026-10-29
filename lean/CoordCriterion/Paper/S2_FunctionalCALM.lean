import CoordCriterion.Figures

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
  `i ≼ j` reads "`j` expands `i`", `o ≼ u` reads "`u` refines `o`";
* a table is a predicate `Table I O := I → O → Prop`; a set of outputs is a
  predicate `O → Prop`; finite families are `List`s;
* a specification `sp : Spec I O` has table `sp.S` and totality `sp.total`;
  its fiber at `i` is `sp.S i`;
* a state `σ : State sp` has current input `σ.cur` and remainder table `σ.R`;
* `R[in ⪰ j]` is `inputTable σ j`, `R[out ⪰ o]` is `outputTable σ o`.

The election itself (`elec`, `elecEq`, ballots `bxd = x··`, `bxy = xy·`,
`bxyx = xyx`, `bxx = xx·`, …) is defined in `CALM/Examples.lean` and
`Figures.lean`; `elec` uses the refinement order on results (`⊥ ≼` each
winner), `elecEq` the equality order.
-/

namespace CC.Paper

open CC CC.CALM

/-! ## The framework by example (`sec:election-story`) -/

/-- "The *input order* records accumulated ballots: `xy· ⪰ x··`, while `xx·`
and `xy·` are incomparable." -/
theorem «sec:election-story/input-order» :
    bxd ≼ bxy ∧ ¬ bxx ≼ bxy ∧ ¬ bxy ≼ bxx := by decide

/-- "The *output order* says which announcements are safe to build on: `⊥`
claims nothing, so either winner refines it, while `x` and `y` are
incomparable." -/
theorem «sec:election-story/output-order» :
    Res.bot ≼ Res.win .x ∧ Res.bot ≼ Res.win .y ∧
      ¬ Res.win .x ≼ Res.win .y ∧ ¬ Res.win .y ≼ Res.win .x :=
  ⟨Or.inl rfl, Or.inl rfl, (by rintro (h | h) <;> cases h), (by rintro (h | h) <;> cases h)⟩

/-- "The functional table is *monotone* … Here, for example, the input
sequence `x·· ⪯ xy· ⪯ xyx` monotonically produces the output sequence
`⊥ ⪯ ⊥ ⪯ x`."  The election (refinement order) is monotone, and the chain is
as stated. -/
theorem «sec:election-story/monotone» :
    elec.MonotoneF ∧
      (bxd ≼ bxy ∧ bxy ≼ bxyx) ∧
      (winner bxd = .bot ∧ winner bxy = .bot ∧ winner bxyx = .win .x) ∧
      (Res.bot ≼ Res.bot ∧ Res.bot ≼ Res.win .x) :=
  ⟨elec_monotone, by decide, by decide, ⟨Or.inl rfl, Or.inl rfl⟩⟩

/-- Fig. `fig:election-frames`: "Only rows whose input expands `x··` are
shown."  The nine printed pairs (`Figures.Elec.printed`) are exactly the rows
of the election at inputs `⪰ x··`. -/
theorem «fig:election-frames/printed-rows» (k : Ballots) (o : Res) :
    (k, o) ∈ Figures.Elec.printed ↔ (bxd ≼ k ∧ elec.S k o) :=
  Figures.Elec.printed_complete k o

/-- Fig. `fig:election-frames`(a): "Initial state, current input `x··` …
upper fiber `{⊥,x,y}`; undetermined; `⊥` needs no commitment."  Panel (a) is
the canonical state `σ_S(x··)`; "upper fiber is all of `{⊥,x,y}`" is stated
as "every output occurs in some remaining row". -/
theorem «fig:election-frames/a» :
    (∀ o : Res, ∃ k, (canon elec bxd).R k o) ∧ ¬ Determined (canon elec bxd) ∧
      Exposable (canon elec bxd) .bot := by
  refine ⟨fun o => (Figures.Elec.upper_ab o).1, ?_, elec_panels_exposable.1⟩
  rintro ⟨o, h⟩
  obtain ⟨k₁, h₁⟩ := (Figures.Elec.upper_ab .bot).1
  obtain ⟨k₂, h₂⟩ := (Figures.Elec.upper_ab (.win .x)).1
  cases (h _ _ h₁).trans (h _ _ h₂).symm

/-- Fig. `fig:election-frames`(b) and §2.1 "Input and determination": "When
`v₂`'s ballot for `y` arrives, the event `input(xy·)` produces panel (b),
retiring rows whose inputs no longer expand the ballots received; such inputs
are now illegal. … in panel (b) it is `{⊥,x,y}`."  Also "`⊥` needs no commitment" (`⊥` exposable). -/
theorem «fig:election-frames/b» :
    Step (canon elec bxd) (.input bxy) (canon elec bxy) ∧
      (∀ o : Res, ∃ k, (canon elec bxy).R k o) ∧ ¬ Determined (canon elec bxy) ∧
      Exposable (canon elec bxy) .bot :=
  ⟨Dist.step_canon_input elec (by decide) ⟨_, rfl⟩, fun o => (Figures.Elec.upper_ab o).2,
   elec_panel_b_undetermined, elec_panels_exposable.2.1⟩

/-- Fig. `fig:election-frames`(b), the printed rows: of the rows at inputs
`⪰ x··`, exactly `(xy·,⊥)`, `(xyx,x)`, `(xyy,y)` remain; every other printed
row is gray because its input does not expand `xy·` (input retirement). -/
theorem «fig:election-frames/b-rows» (k : Ballots) (o : Res) (hk : bxd ≼ k) :
    ((canon elec bxy).R k o ↔
        ((k = bxy ∧ o = .bot) ∨ (k = bxyx ∧ o = .win .x) ∨
          (k = Figures.Elec.bxyy ∧ o = .win .y))) ∧
      (elec.S k o → ¬ (canon elec bxy).R k o → ¬ bxy ≼ k) :=
  Figures.Elec.panel_b k o hk

/-- Fig. `fig:election-frames`(c) and §2.1: "If `v₂` instead votes for `x`,
as in panel (c), the upper fiber is `{x}`.  The state is *determined*: input
alone has resolved the outcome, without commitment"; caption: "`x` needs no
commitment". -/
theorem «fig:election-frames/c» :
    Step (canon elec bxd) (.input bxx) (canon elec bxx) ∧
      (∀ o, (∃ k, (canon elec bxx).R k o) ↔ o = .win .x) ∧
      Determined (canon elec bxx) ∧ Exposable (canon elec bxx) (.win .x) :=
  ⟨Dist.step_canon_input elec (by decide) ⟨_, rfl⟩, Figures.Elec.upper_c,
   elec_panel_c_determined, elec_panels_exposable.2.2⟩

/-- Fig. `fig:election-frames`(d) and §2.1: "the system acts as a registrar,
emitting `⊥` and closing the polls at `xy·` in the same output event.  Its
irrevocable *seal commitment* removes the still-possible `xyx` and `xyy` rows
but leaves the current input unchanged, and so makes `⊥` the final result."

Closing the polls is the commitment `Figures.closePolls` (a commitment in the
sense of Def. `def:commitment`, §4.3), and it is a seal; the registrar's
event is the system output event `Out_[closePolls](⊥)` of §4.3, legal under
any basis containing `closePolls`.  It ends at `panelD`, whose only row is
`(xy·,⊥)`; the rows it removes beyond `(b)` are exactly `(xyx,x)`, `(xyy,y)`
(the struck rows); the state is determined with result `⊥`. -/
theorem «fig:election-frames/d» :
    (Figures.closePolls (sp := elec)).app (canon elec bxy) = some Figures.Elec.panelD ∧
      (∀ B : Basis elec, B Figures.closePolls →
        SysStep B (canon elec bxy) (.output [Figures.closePolls] .bot) Figures.Elec.panelD) ∧
      Figures.Elec.panelD.cur = bxy ∧
      (∀ k o, Figures.Elec.panelD.R k o ↔ (k = bxy ∧ o = .bot)) ∧
      (∀ k o, ((canon elec bxy).R k o ∧ ¬ Figures.Elec.panelD.R k o) ↔
        ((k = bxyx ∧ o = .win .x) ∨ (k = Figures.Elec.bxyy ∧ o = .win .y))) ∧
      (Determined Figures.Elec.panelD ∧ ∀ k x, Figures.Elec.panelD.R k x → x = .bot) :=
  ⟨Figures.Elec.close_at_b, Figures.Elec.registrar_step, Figures.Elec.panelD_cur,
   Figures.Elec.panelD_rows, Figures.Elec.panelD_struck, Figures.Elec.panelD_determined⟩

/-- Fig. `fig:election-frames`(d), legend: "Gray: removed from the remainder
table; struck through if by a commitment, otherwise retired by an input event."  A
printed row is absent from panel (d) iff its input does not expand `xy·`
(gray) or it is one of the two struck rows. -/
theorem «fig:election-frames/d-gray» (k : Ballots) (o : Res) (hk : bxd ≼ k) (hS : elec.S k o) :
    ¬ Figures.Elec.panelD.R k o ↔
      (¬ bxy ≼ k ∨ (k = bxyx ∧ o = .win .x) ∨ (k = Figures.Elec.bxyy ∧ o = .win .y)) :=
  Figures.Elec.panelD_gray k o hk hS

/-- Fig. `fig:election-frames` caption and §2.1: "a seal that `output(⊥)`
alone does not require … Emitting `⊥` by itself would need no commitment,
since every output still possible refines it."  At (b), `⊥` is exposable,
`Sealed_⊥` and `Rejected_⊥` are empty, and `output(⊥)` removes no row. -/
theorem «fig:election-frames/bot-alone» :
    Exposable (canon elec bxy) .bot ∧ (¬ ∃ k x, Sealed (canon elec bxy) .bot k x) ∧
      (¬ ∃ k x, Rejected (canon elec bxy) .bot k x) ∧
      outputTable (canon elec bxy) .bot = (canon elec bxy).R :=
  Figures.Elec.bot_alone_at_b

/-- Fig. `fig:nonmonotone-frame`: "Panel (b) under the equality order, after
`output(⊥)`. … upper fiber `{⊥}`; determined."  Under `elecEq`, `output(⊥)`
at `σ_S(xy·)` seals `xyx` and leaves the single row `(xy·,⊥)`. -/
theorem «fig:nonmonotone-frame» :
    Sealed (canon elecEq bxy) ⟨.bot⟩ bxyx ⟨winner bxyx⟩ ∧
      ∀ k o, outputTable (canon elecEq bxy) ⟨.bot⟩ k o ↔ (k = bxy ∧ o = ⟨.bot⟩) :=
  ⟨elecEq_bot_seals, elecEq_bot_single_row⟩

/-- Fig. `fig:nonmonotone-frame` caption: "The seal the registrar chose in
Figure `fig:election-frames`(d) is required here." -/
theorem «fig:nonmonotone-frame/matches-d» (k : Ballots) (r : Res) :
    Figures.Elec.panelD.R k r ↔ outputTable (canon elecEq bxy) ⟨.bot⟩ k ⟨r⟩ :=
  Figures.Elec.panelD_matches_e k r

/-- §2.1 "Output and consistency": "Hence `⊥` is exposable in panels (a)
and (b), and `x` in panel (c)." -/
theorem «sec:election-story/exposable-panels» :
    Exposable (canon elec bxd) .bot ∧ Exposable (canon elec bxy) .bot ∧
      Exposable (canon elec bxx) (.win .x) :=
  elec_panels_exposable

/-- §2.1: "under the equality order … `⊥` is incompatible with future
winners, so emitting it requires a seal": at `σ_S(xy·)`, `⊥` is not
exposable under `elecEq`. -/
theorem «sec:election-story/equality-order-seal» :
    ¬ Exposable (canon elecEq bxy) ⟨.bot⟩ :=
  fun h => ((exposable_iff_empty _ _).1 h).1 ⟨_, _, elecEq_bot_seals⟩

/-- §2.1: "The obstruction is a property solely of the table and its orders.
Rows `(xy·,⊥)` and `(xyx,x)` have the common input expansion `xyx`, but under
the equality order no output at `xyx` refines both outputs `⊥` and `x`." -/
theorem «sec:election-story/obstruction» :
    elecEq.S bxy ⟨.bot⟩ ∧ elecEq.S bxyx ⟨.win .x⟩ ∧ bxy ≼ bxyx ∧ bxyx ≼ bxyx ∧
      ¬ ∃ u, elecEq.S bxyx u ∧ (⟨.bot⟩ : ResE) ≼ u ∧ (⟨.win .x⟩ : ResE) ≼ u :=
  ⟨by show _ = _; rw [winner_bxy], by show _ = _; rw [winner_bxyx], bxy_le_bxyx, PO.refl _,
   fun ⟨_, _, h₁, h₂⟩ => by cases (show (⟨.bot⟩ : ResE) = ⟨.win .x⟩ from h₁.trans h₂.symm)⟩

/-- §2.1: "A run that emits `⊥` at `xy·` and one that receives `xyx` cannot be
reconciled at `xyx`" (equality order).  The two runs end at
`(xy·, S[in ⪰ xy·, out ⪰ ⊥])` and `σ_S(xyx)`. -/
theorem «sec:election-story/not-reconciled» :
    ¬ ConfluentAt [outputState (canon elecEq bxy) ⟨.bot⟩
        ((elecEq_bot_single_row bxy _).2 ⟨rfl, rfl⟩).1, canon elecEq bxyx] bxyx :=
  elecEq_not_confluent

/-- §2.1: "Input and output events form a transition system, and the
specification is consistent when its runs are confluent.  For functional
tables this corresponds exactly to monotonicity": the election is consistent
under the refinement order and not under the equality order. -/
theorem «sec:election-story/consistency» :
    elec.Consistent ∧ ¬ elecEq.Consistent :=
  ⟨elec_consistent, elecEq_not_consistent⟩

/-! ## Specifications and states (`sec:functional-specifications`) -/

/-- **Def. `def:functional-specification`** (Functional ordered
specification, total).  "A tuple `(I, ≼, O, ≼, S)`, where `(I,≼)` and `(O,≼)` are
partially ordered input and output types, and `S ⊆ I × O` is a typed relation
… in which every input appears in at least one row (`S` is total on `I`) and
at most one (a functional dependency)."

Lean: the orders are the `PO` instances, `Spec I O` bundles `S` with
totality, and `Spec.Functional` is the functional dependency. -/
abbrev «def:functional-specification» (I O : Type) [PO I] [PO O] :=
  { sp : Spec I O // sp.Functional }

/-- "The unique output paired with `i` induces the function
`f : (I,≼) → (O,≼)` with `S = {(i, f(i)) : i ∈ I}`."  The library works with
rows rather than with `f`; this states that the two views agree. -/
theorem «def:functional-specification/induced-function» {I O : Type} [PO I] [PO O]
    (sp : Spec I O) : sp.Functional ↔ ∃ f : I → O, ∀ i o, sp.S i o ↔ o = f i := by
  constructor
  · intro hf
    refine ⟨fun i => (sp.total i).choose, fun i o => ⟨fun h => hf i o _ h (sp.total i).choose_spec,
      fun h => h ▸ (sp.total i).choose_spec⟩⟩
  · rintro ⟨f, hf⟩ i o o' h h'
    exact ((hf i o).1 h).trans ((hf i o').1 h').symm

/-- "Neither need be unique or least: for example, two independent
transactions `a` and `b`, with schedules ordered by subsequence, have two
incomparable minimal common expansions, `ab` and `ba`."

Lean: schedules `Sched T` are lists ordered by `List.Sublist` (a `PO`
instance); "independent" is read as `a ≠ b`.  Both `ab` and `ba` are common
expansions of `a` and `b`, each minimal among common expansions, and they are
incomparable. -/
theorem «sec:functional-specifications/subsequence-example» {T : Type} {a b : T}
    (hab : a ≠ b) :
    (∀ s t : Sched T, s ≼ t ↔ s.txs.Sublist t.txs) ∧
    ((⟨[a]⟩ : Sched T) ≼ ⟨[a, b]⟩ ∧ (⟨[b]⟩ : Sched T) ≼ ⟨[a, b]⟩ ∧
      ∀ u : Sched T, (⟨[a]⟩ : Sched T) ≼ u → (⟨[b]⟩ : Sched T) ≼ u →
        u ≼ ⟨[a, b]⟩ → u = ⟨[a, b]⟩) ∧
    ((⟨[a]⟩ : Sched T) ≼ ⟨[b, a]⟩ ∧ (⟨[b]⟩ : Sched T) ≼ ⟨[b, a]⟩ ∧
      ∀ u : Sched T, (⟨[a]⟩ : Sched T) ≼ u → (⟨[b]⟩ : Sched T) ≼ u →
        u ≼ ⟨[b, a]⟩ → u = ⟨[b, a]⟩) ∧
    ¬ (⟨[a, b]⟩ : Sched T) ≼ ⟨[b, a]⟩ ∧ ¬ (⟨[b, a]⟩ : Sched T) ≼ ⟨[a, b]⟩ :=
  ⟨sched_le_iff, sched_two_minimal hab⟩

/-- **Def. `def:functional-monotonicity`** (Functional monotonicity,
monotone).  "`Spec`,
with induced function `f`, is *monotone* if `i ≼ j ⟹ f(i) ≼ f(j)`."

Lean: `Spec.MonotoneF` is stated on rows (`i ≼ j`, `(i,o) ∈ S`, `(j,u) ∈ S`
imply `o ≼ u`), which needs no induced function;
`«def:functional-monotonicity/via-f»` shows it is the paper's condition. -/
abbrev «def:functional-monotonicity» {I O : Type} [PO I] [PO O] (sp : Spec I O) : Prop :=
  sp.MonotoneF

/-- **Eq. `eq:functional-monotonicity`**: "`i ≼ j ⟹ f(i) ≼ f(j)`", the
displayed condition on the induced function `f`.  By
`«def:functional-monotonicity/via-f»` it is `Spec.MonotoneF` whenever
`S = {(i, f(i))}`. -/
abbrev «eq:functional-monotonicity» {I O : Type} [PO I] [PO O] (f : I → O) : Prop :=
  ∀ i j : I, i ≼ j → f i ≼ f j

/-- Def. `def:functional-monotonicity`, in terms of the induced function: if
`S = {(i, f(i))}`, then `Spec.MonotoneF` is `i ≼ j ⟹ f(i) ≼ f(j)`. -/
theorem «def:functional-monotonicity/via-f» {I O : Type} [PO I] [PO O]
    (sp : Spec I O) (f : I → O) (hf : ∀ i o, sp.S i o ↔ o = f i) :
    sp.MonotoneF ↔ ∀ i j, i ≼ j → f i ≼ f j :=
  ⟨fun h i j hij => h i j _ _ hij ((hf i _).2 rfl) ((hf j _).2 rfl),
   fun h i j o u hij ho hu => by rw [(hf i o).1 ho, (hf j u).1 hu]; exact h i j hij⟩

/-- **Def. `def:residual-state`** (Specification state, current input,
remainder table, legal input).  "A pair
`σ = (i,R)`, where `i ∈ I` is the *current input* and `R ⊆ S` is the
*remainder table*, such that: (1) `R` contains a row at `i`; and (2) `R`
contains only rows at expansions of `i`."  An input `k` is *legal* at `σ`
when `∃ u, σ.R k u`.

Lean: `State sp` with fields `cur`, `R`, `sub` (`R ⊆ S`), `hasCur` (1) and
`above` (2). -/
abbrev «def:residual-state» {I O : Type} [PO I] [PO O] (sp : Spec I O) := State sp

/-- **Eq. `eq:canonical-state`**: the canonical state `σ_S(i) = (i, S[in ⪰ i])`. -/
abbrev «eq:canonical-state» {I O : Type} [PO I] [PO O] (sp : Spec I O) (i : I) : State sp :=
  canon sp i

/-- "The *canonical state at `i`* is the state at `i` with no rows removed: it
keeps every row of `S` at `i` and its expansions":
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
expansions of `i`. -/
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

/-- **Def. `def:output-event`** (Output event, seal, commitment).  "Let
`(i,R)` be a state and `(i,o)` its row at the current input.  The *output
event* `output(o)` … restricts the remainder table to exactly the rows whose
outputs refine `o`, and emits `o`: `(i,R) --output(o)--> (i, R[out ⪰ o])`.
When `R' ≠ R`, removing some row at an input `j ⪰ i`, we call this
transition the *seal* … it is a *commitment*."

Lean: `Step σ (.output o) τ` (constructor `Step.output`) requires
`σ.R σ.cur o` and sets `τ.R = outputTable σ o = R[out ⪰ o]`.  The general
definition is used for every specification (it is also Def.
`def:lifted-output-event`); in a functional specification "`R' ≠ R`" is
exactly "some row is in `Sealed_o`" (`«def:output-event/commit-iff-seal»`). -/
abbrev «def:output-event» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) : Table I O :=
  outputTable σ o

/-- **Eq. `eq:output-action`**: "`(i,R) --output(o)--> (i, R' = R[out ⪰ o])`".
The new table `R[out ⪰ o]` is `outputTable σ o`: the rows of `R` whose output
refines `o`. -/
theorem «eq:output-action» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) (k : I) (u : O) :
    outputTable σ o k u ↔ σ.R k u ∧ o ≼ u :=
  Iff.rfl

/-- Def. `def:output-event`: in a functional specification, the output event
changes the table (`R' ≠ R`) iff it seals some row. -/
theorem «def:output-event/commit-iff-seal» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) (σ : State sp) (o : O) :
    outputTable σ o ≠ σ.R ↔ ∃ k x, Sealed σ o k x :=
  functional_commit_iff_sealed hf σ o

/-- "The current row `(i,o)` remains, since `o` refines itself, so the event
always ends at a state." -/
theorem «sec:functional-events/output-ends-at-state» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} (σ : State sp) (o : O) (h : σ.R σ.cur o) :
    Step σ (.output o) (outputState σ o h) ∧ (outputState σ o h).R σ.cur o :=
  ⟨step_outputState σ o h, ⟨h, PO.refl o⟩⟩

/-- "Systems may issue more commitments than an output requires, as the
registrar does in Figure `fig:election-frames`(d), but extra commitments only
restrict behavior (Section `sec:systems`)."  For the registrar of panel (d): its
event `Out_[closePolls](⊥)` has an observably equivalent `output(⊥)` of the
transition system, whose table contains panel (d)'s.  The general statement
is Lemma `lem:canonical-equivalent` (`CC.canonical_equivalent`, §4.3). -/
theorem «sec:functional-events/extra-commitments» (B : Basis elec) (hB : B Figures.closePolls) :
    ∃ ρ', Exec (canon elec bxy) [.output .bot] ρ' ∧ ρ'.cur = bxy ∧
      ∀ k u, Figures.Elec.panelD.R k u → ρ'.R k u :=
  Figures.Elec.registrar_canonical B hB

/-- **Def. `def:exposable`** (Exposable output).  "The output `o` at `(i,R)`
is *exposable* when `output(o)` applies no commitment."

Lean: `Exposable σ o` says that every row ruled out by `o` is refined by a
kept row at the same input (it is retired, not sealed or chosen away); by
`«def:exposable/no-commitment»` this is "`Sealed_o` and `Rejected_o` are
empty", i.e. no commitment, in the sense of Def. `def:lifted-output-event`. -/
abbrev «def:exposable» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) : Prop :=
  Exposable σ o

/-- Def. `def:exposable`: exposable ⇔ the event applies neither a seal nor a
choice. -/
theorem «def:exposable/no-commitment» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) (o : O) :
    Exposable σ o ↔ (∀ k x, ¬ Sealed σ o k x) ∧ (∀ k x, ¬ Rejected σ o k x) :=
  exposable_iff_no_commitment σ o

/-- "In a functional specification this means `R[out ⪰ o] = R`: the event
removes nothing.  As the only row at a legal input `j` is `(j, f(j))`, `o` is
exposable exactly when `f(j)` refines `o` for every legal `j`." -/
theorem «sec:functional-events/functional-exposable» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} (hf : sp.Functional) (σ : State sp) (o : O) :
    (Exposable σ o ↔ outputTable σ o = σ.R) ∧ (Exposable σ o ↔ ∀ k x, σ.R k x → o ≼ x) :=
  ⟨exposable_iff_functional hf σ o, exposable_iff_refines_all hf σ o⟩

/-- §2.3 "Determination": "A state is *determined* when its upper fiber has
one element."  Lean: `CALM.Determined σ` is `∃ o, ∀ k x, σ.R k x → x = o`;
the upper fiber `out(R)` is nonempty, so this is "has exactly one element". -/
abbrev «sec:functional-events/determined» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (σ : State sp) : Prop :=
  Determined σ

/-- "Determined": upper fiber has exactly one element. -/
theorem «sec:functional-events/determined-one-element» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} (σ : State sp) :
    Determined σ ↔ ∃ o, (∃ k, σ.R k o) ∧ ∀ k x, σ.R k x → x = o :=
  determined_upper_fiber σ

/-- "A functional specification can therefore have undetermined states, as in
panel (b) … An input event may [reach a determined state] by retiring rows …
and a commitment by sealing inputs …, as in panels (c) and (d)." -/
theorem «sec:functional-events/determination-examples» :
    elec.Functional ∧ ¬ Determined (canon elec bxy) ∧ Determined (canon elec bxx) ∧
      Determined Figures.Elec.panelD :=
  ⟨elec_functional, elec_panel_b_undetermined, elec_panel_c_determined,
   Figures.Elec.panelD_determined.1⟩

/-- "An event from a determined state always leads to another determined
state: events only remove rows, and a row at the current input always
remains." -/
theorem «sec:functional-events/stays-determined» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} :
    (∀ {σ τ : State sp} {e : Event I O}, Step σ e τ → Determined σ → Determined τ) ∧
      (∀ {σ τ : State sp}, Reach σ τ → Determined σ → Determined τ) :=
  ⟨step_determined, reach_determined⟩

/-! ## Executions and consistency (`sec:executions`) -/

/-- **Def. `def:run`** (Transition system, run).  "A *run* is any finite
transition sequence from the canonical state `σ_S(i)` at some input `i`."

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
`S[in ⪰ i, out ⪰ o₁, …, out ⪰ oₘ]`."  `outs es` lists the outputs emitted by
the event list `es`. -/
theorem «lem:run-residual» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    {i : I} {es : List (Event I O)} {τ : State sp} (hx : Exec (canon sp i) es τ) :
    ∀ k u, τ.R k u ↔ (sp.S k u ∧ τ.cur ≼ k ∧ ∀ o ∈ outs es, o ≼ u) :=
  run_residual hx

/-- **Eq. `eq:run-residual`**: the table
`S[in ⪰ i, out ⪰ o₁, …, out ⪰ oₘ]`, "the rows whose input expands `i` and
whose output refines each `o_r`"; the emitted outputs are a list.
Lemma `lem:run-residual` says a run's remainder table is this table at its
current input and `outs es`. -/
abbrev «eq:run-residual» {I O : Type} [PO I] [PO O] (sp : Spec I O) (i : I)
    (os : List O) : Table I O :=
  fun k u => sp.S k u ∧ i ≼ k ∧ ∀ o ∈ os, o ≼ u

/-- Example after Lemma `lem:run-residual`: "in the equality-order variant …
a run that emits `⊥` at `xy·` keeps `S[in ⪰ xy·, out ⪰ ⊥]`: the single row
`(xy·,⊥)`." -/
theorem «lem:run-residual/example» (k : Ballots) (o : ResE) :
    outputTable (canon elecEq bxy) ⟨.bot⟩ k o ↔ (k = bxy ∧ o = ⟨.bot⟩) :=
  elecEq_bot_single_row k o

/-- **Def. `def:consistency`** (Consistency, confluence at an input).  "An ordered specification is
*consistent* when every finite family of runs is confluent: if the runs end
at states `(i₁,R₁),…,(i_k,R_k)` and `j` is a common expansion of their current
inputs, each can be continued to a common state with current input `j`.
They are then *confluent at* `j`."

Lean: `Spec.Consistent`; finite families are lists of run end states, and
"confluent at `j`" is `ConfluentAt fam j` (`∃ τ, τ.cur = j ∧ ∀ σ ∈ fam,
Reach σ τ`). -/
abbrev «def:consistency» {I O : Type} [PO I] [PO O] (sp : Spec I O) : Prop :=
  sp.Consistent

/-- **Prop. `prop:confluence`** (Survivor test).  "Runs ending at states
`(i_r,R_r)` are confluent at `j` if and only if some row at `j` survives in
every final state … For any such `u`, `input(j)` followed by `output(u)` takes
every final state to the state `(j, S[in ⪰ j, out ⪰ u])`."

Lean: the first conjunct is the equivalence; the second is the explicit
continuation, where `meetState sp j u _` is `(j, S[in ⪰ j, out ⪰ u])`. -/
theorem «prop:confluence» {I O : Type} [PO I] [PO O] {sp : Spec I O} :
    (∀ (fam : List (State sp)), (∀ σ ∈ fam, IsRun σ) → ∀ j : I, (∀ σ ∈ fam, σ.cur ≼ j) →
        (ConfluentAt fam j ↔ ∃ u, sp.S j u ∧ ∀ σ ∈ fam, σ.R j u)) ∧
      (∀ {σ : State sp}, IsRun σ → ∀ {j : I} {u : O} (hju : σ.R j u),
        Exec σ [.input j, .output u] (meetState sp j u (σ.sub _ _ hju))) :=
  ⟨survivor_test, fun h _ _ hju => survivor_exec h hju⟩

/-- **Eq. `eq:reconciliation`**: "`(j,u) ∈ R_r` for every `r`, for some
`u ∈ S(j)`" — the survivor condition of Prop. `prop:confluence`, for a family
of final states given as a list. -/
abbrev «eq:reconciliation» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (fam : List (State sp)) (j : I) : Prop :=
  ∃ u, sp.S j u ∧ ∀ σ ∈ fam, σ.R j u

/-! ## The Functional CALM theorem (`sec:functional-calm-theorem`) -/

/-- **Theorem `thm:functional-calm`** (Functional CALM).  "A functional ordered
specification is consistent if and only if it is monotone." -/
theorem «thm:functional-calm» {I O : Type} [PO I] [PO O] (sp : Spec I O)
    (hf : sp.Functional) : sp.Consistent ↔ sp.MonotoneF :=
  functional_calm hf

/-- Example after Theorem `thm:functional-calm`: "In the equality-order
election, `f(xy·) = ⊥` and `f(xyx) = x` are incomparable: a run that emits `⊥`
at `xy·` and one that accepts `xyx` are the two runs … that can never be
reconciled." -/
theorem «thm:functional-calm/example» :
    winner bxy = .bot ∧ winner bxyx = .win .x ∧ bxy ≼ bxyx ∧ ¬ elecEq.MonotoneF ∧
      ¬ ConfluentAt [outputState (canon elecEq bxy) ⟨.bot⟩
        ((elecEq_bot_single_row bxy _).2 ⟨rfl, rfl⟩).1, canon elecEq bxyx] bxyx :=
  ⟨winner_bxy, winner_bxyx, bxy_le_bxyx, elecEq_not_monotone, elecEq_not_confluent⟩

/-- **Corollary `cor:state-by-input`** (State is fixed by input).  "In a
consistent functional specification, every run ending at current input `i` is
in the canonical state `σ_S(i)`, whatever outputs it emitted along the way." -/
theorem «cor:state-by-input» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) (hc : sp.Consistent) {τ : State sp} (hτ : IsRun τ) :
    τ = canon sp τ.cur :=
  state_by_input hf hc hτ

/-- After Cor. `cor:state-by-input`: "To be confluent at a common expansion
`j`, each run therefore needs only the single event `input(j)`, which takes it
to `σ_S(j)`." -/
theorem «cor:state-by-input/input-suffices» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hf : sp.Functional) (hc : sp.Consistent) {σ : State sp} (hrun : IsRun σ) {j : I}
    (hj : σ.cur ≼ j) : Exec σ [.input j] (canon sp j) :=
  functional_meet_by_input hf hc hrun hj

/-- **Prop. `prop:functional-exposure-boundary`** (Exposure boundary).  "A
functional ordered specification is monotone if and only if every output at
every state reachable without commitment is exposable."  "An output at state
`τ`" is an `o` with `(τ.cur, o) ∈ τ.R`. -/
theorem «prop:functional-exposure-boundary» {I O : Type} [PO I] [PO O] (sp : Spec I O)
    (hf : sp.Functional) :
    sp.MonotoneF ↔ ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  functional_exposure_boundary hf

/-- After Prop. `prop:functional-exposure-boundary`: "A monotone specification
can thus emit every current output without commitment; if monotonicity fails at
`i ≼ k` with `f(i) ⋠ f(k)`, then at `σ_S(i)` the event `output(f(i))` applies
`s_{f(i)}`, sealing `k`." -/
theorem «prop:functional-exposure-boundary/nonmonotone-seals» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} (hf : sp.Functional) {i k : I} {o u : O}
    (hik : i ≼ k) (hio : sp.S i o) (hku : sp.S k u) (hn : ¬ o ≼ u) :
    Sealed (canon sp i) o k u :=
  nonmono_seals hf hik hio hku hn

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

/-! ## Cross-references from §7 (`sections/discussion.tex`) -/

/-- §7.1, "Design lessons": "useful output need not wait for
determination: the election can emit `⊥` while either candidate may still
win."  At `σ_S(xy·)`, `⊥` is exposable and rows with output `x` and with output `y` both remain. -/
theorem «sec:discussion/emit-before-determination» :
    Exposable (canon elec bxy) .bot ∧ (∃ k, (canon elec bxy).R k (.win .x)) ∧
      (∃ k, (canon elec bxy).R k (.win .y)) :=
  ⟨elec_panels_exposable.2.1, (Figures.Elec.upper_ab _).2, (Figures.Elec.upper_ab _).2⟩

/-- §7.1, "Design lessons": "Receiving a decisive ballot and closing the
polls both leave a single result.  The first retires rows by input; the
second removes rows that input still permits, a commitment."

(1) `input(xx·)` at `σ_S(x··)` reaches a determined state, and every row it
removes has an input that does not expand `xx·`; (2) closing the polls at (b)
reaches a determined state, and every row it removes is at a legal input
strictly expanding the current one; (3)–(4) in the election the two never
leave the *same* result: closing the polls at any undetermined canonical
state leaves only `⊥`, while every determined canonical state has a winner. -/
theorem «sec:discussion/decisive-vs-close» :
    (Step (canon elec bxd) (.input bxx) (canon elec bxx) ∧ Determined (canon elec bxx) ∧
        ∀ k u, (canon elec bxd).R k u → ¬ (canon elec bxx).R k u → ¬ bxx ≼ k) ∧
      (Determined Figures.Elec.panelD ∧ ∀ k u, (canon elec bxy).R k u →
        ¬ Figures.Elec.panelD.R k u → bxy ≼ k ∧ k ≠ bxy) ∧
      (∀ i, ¬ Determined (canon elec i) →
        (Figures.closePolls (sp := elec)).app (canon elec i) =
            some (Figures.closeState (canon elec i)) ∧
          ∀ k x, (Figures.closeState (canon elec i)).R k x → x = .bot) ∧
      (∀ i, Determined (canon elec i) → ∃ c, winner i = .win c) :=
  Figures.Elec.decisive_vs_close

end CC.Paper
