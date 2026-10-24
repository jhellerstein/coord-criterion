import CoordCriterion.Foundations.Runs

/-!
# A conflict confined to the current input (Section 4.4)

Supports the remark after Prop. `thm:commitments-require-coordination`
("Conflicting output events cannot be reconciled") in
`sections/distributed.tex`: the conflict is confined to the current input.

The specification: inputs `i ≺ j` (a two-element chain), outputs `o`, `x`,
`u` with `o ≼ u`, `x ≼ u` and `o`, `x` incomparable; `S(i) = {o, x}` and
`S(j) = {u}`.  From the canonical state `σ_S(i)`:

* `output(o)` and `output(x)` are legal (`step_o`, `step_x`);
* after `output(o)` no output at `i` refines `x` (`tO_no_refine_x`), so the
  two states cannot reach a common state with current input `i`
  (`not_meet_at_i`);
* yet both perform `input(j)` and reach the same state `σ_S(j)`
  (`step_j_o`, `step_j_x`, `confluent_at_j`);
* the specification is nonetheless not consistent (`not_consistent`): Directed
  Outputs fails at `i` (`not_directedOutputs`), hence Lifted Monotonicity
  fails (`not_liftedMono`).

Modeling choice: the orders are given by Boolean tests so that every case is
decided by `decide`.
-/

namespace CC
namespace CALM
namespace Transient

/-- Inputs: the chain `i ≺ j`. -/
inductive In | i | j
  deriving DecidableEq

/-- Outputs: `o`, `x` below `u`, `o` and `x` incomparable. -/
inductive Out | o | x | u
  deriving DecidableEq

def inLe : In → In → Bool
  | .i, _ => true
  | .j, .j => true
  | .j, .i => false

def outLe : Out → Out → Bool
  | _, .u => true
  | .o, .o => true
  | .x, .x => true
  | _, _ => false

instance : PO In where
  le a b := inLe a b = true
  refl a := by cases a <;> rfl
  trans {a b c} h1 h2 := by cases a <;> cases b <;> cases c <;> simp_all [inLe]
  antisymm {a b} h1 h2 := by cases a <;> cases b <;> simp_all [inLe]

instance : PO Out where
  le a b := outLe a b = true
  refl a := by cases a <;> rfl
  trans {a b c} h1 h2 := by cases a <;> cases b <;> cases c <;> simp_all [outLe]
  antisymm {a b} h1 h2 := by cases a <;> cases b <;> simp_all [outLe]

instance (a b : In) : Decidable (a ≼ b) := inferInstanceAs (Decidable (inLe a b = true))
instance (a b : Out) : Decidable (a ≼ b) := inferInstanceAs (Decidable (outLe a b = true))

/-- `o` and `x` are incomparable; both lie below `u`. -/
theorem out_order : ¬ (Out.o ≼ Out.x) ∧ ¬ (Out.x ≼ Out.o) ∧ Out.o ≼ Out.u ∧ Out.x ≼ Out.u := by
  decide

/-- `i ≺ j`. -/
theorem in_order : In.i ≼ In.j ∧ ¬ (In.j ≼ In.i) := by decide

def rows : In → Out → Bool
  | .i, .o => true
  | .i, .x => true
  | .j, .u => true
  | _, _ => false

/-- `S(i) = {o, x}`, `S(j) = {u}`. -/
def spec : Spec In Out where
  S k y := rows k y = true
  total k := by cases k
                · exact ⟨.o, rfl⟩
                · exact ⟨.u, rfl⟩

instance (k : In) (y : Out) : Decidable (spec.S k y) :=
  inferInstanceAs (Decidable (rows k y = true))

/-- The canonical state `σ_S(i)`. -/
abbrev σi : State spec := canon spec .i

/-- The state after `output(o)` at `σ_S(i)`: rows `(i,o)`, `(j,u)`. -/
def tO : State spec where
  cur := .i
  R := outputTable σi .o
  sub := fun _ _ h => h.1.1
  hasCur := ⟨.o, ⟨rfl, rfl⟩, rfl⟩
  above := fun _ _ h => h.1.2

/-- The state after `output(x)` at `σ_S(i)`: rows `(i,x)`, `(j,u)`. -/
def tX : State spec where
  cur := .i
  R := outputTable σi .x
  sub := fun _ _ h => h.1.1
  hasCur := ⟨.x, ⟨rfl, rfl⟩, rfl⟩
  above := fun _ _ h => h.1.2

/-- `output(o)` is legal at `σ_S(i)`. -/
theorem step_o : Step σi (.output .o) tO := .output _ _ _ ⟨rfl, rfl⟩ rfl rfl

/-- `output(x)` is legal at `σ_S(i)`. -/
theorem step_x : Step σi (.output .x) tX := .output _ _ _ ⟨rfl, rfl⟩ rfl rfl

/-- After `output(o)`, no output at `i` refines `x`. -/
theorem tO_no_refine_x : ∀ y, tO.R .i y → ¬ (Out.x ≼ y) := by
  intro y h
  have h' : rows .i y = true := h.1.1
  have h'' : outLe .o y = true := h.2
  cases y
  · decide
  · exact absurd h'' (by decide)
  · exact absurd h' (by decide)

/-- The two states cannot be brought to a common state with current input `i`. -/
theorem not_meet_at_i : ¬ ∃ ρ : State spec, ρ.cur = .i ∧ Reach tO ρ ∧ Reach tX ρ := by
  rintro ⟨ρ, hc, h1, h2⟩
  obtain ⟨w, hw⟩ := ρ.hasCur
  rw [hc] at hw
  exact tO_no_refine_x w (reach_sub h1 _ _ hw) (reach_sub h2 _ _ hw).2

/-- `input(j)` from either state gives the table of `σ_S(j)`. -/
theorem inputTable_eq_o : inputTable tO .j = (canon spec .j).R := by
  funext k y
  cases k <;> cases y <;> simp [inputTable, tO, outputTable, canon, spec, rows] <;> decide

theorem inputTable_eq_x : inputTable tX .j = (canon spec .j).R := by
  funext k y
  cases k <;> cases y <;> simp [inputTable, tX, outputTable, canon, spec, rows] <;> decide

/-- After `output(o)`, `input(j)` reaches `σ_S(j)`. -/
theorem step_j_o : Step tO (.input .j) (canon spec .j) :=
  .input _ _ _ ⟨.u, ⟨⟨rfl, rfl⟩, rfl⟩⟩ rfl inputTable_eq_o.symm

/-- After `output(x)`, `input(j)` reaches `σ_S(j)`. -/
theorem step_j_x : Step tX (.input .j) (canon spec .j) :=
  .input _ _ _ ⟨.u, ⟨⟨rfl, rfl⟩, rfl⟩⟩ rfl inputTable_eq_x.symm

/-- The two runs are confluent at `j`. -/
theorem confluent_at_j : ConfluentAt [tO, tX] .j := by
  refine ⟨canon spec .j, rfl, ?_⟩
  intro σ hσ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl
  · exact ⟨[.input .j], .cons step_j_o (.nil _)⟩
  · exact ⟨[.input .j], .cons step_j_x (.nil _)⟩

/-- Both states end runs. -/
theorem tO_isRun : IsRun tO := ⟨.i, [.output .o], .cons step_o (.nil _)⟩
theorem tX_isRun : IsRun tX := ⟨.i, [.output .x], .cons step_x (.nil _)⟩

/-- The specification is not consistent: the two runs are not confluent at `i`. -/
theorem not_consistent : ¬ spec.Consistent := by
  intro h
  have hfam : ∀ σ ∈ [tO, tX], IsRun σ := by
    intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl
    · exact tO_isRun
    · exact tX_isRun
  have hle : ∀ σ ∈ [tO, tX], σ.cur ≼ In.i := by
    intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl <;> exact PO.refl _
  obtain ⟨ρ, hc, hr⟩ := h [tO, tX] hfam .i hle
  exact not_meet_at_i ⟨ρ, hc, hr tO (by simp), hr tX (by simp)⟩

/-- `o` and `x` have no common refinement in `S(i)`. -/
theorem no_bound_at_i : ¬ CompatibleIn (spec.S .i) [.o, .x] := by
  rintro ⟨w, hw, hb⟩
  have h1 := hb .o (by simp)
  have h2 := hb .x (by simp)
  revert hw h1 h2
  cases w <;> decide

/-- Directed Outputs fails at `i`. -/
theorem not_directedOutputs : ¬ spec.DirectedOutputs := fun h =>
  no_bound_at_i (h .i [.o, .x] (by simp) (by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> rfl))

/-- Lifted Monotonicity fails (take `i ≼ i`). -/
theorem not_liftedMono : ¬ spec.LiftedMono := fun h =>
  not_directedOutputs fun k => h k k (PO.refl k)

end Transient
end CALM
end CC
