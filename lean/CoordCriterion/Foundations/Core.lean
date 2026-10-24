

/-!
# Core definitions (Sections 2–3, Appendix A)

Supports `sections/functional-calm.tex`, `sections/complete-calm.tex` and the
notation of `appendices/notation.tex`: partial orders (`PO`), ordered
specifications (`Spec`) and tables, states `(i, R)` (`State`), input/output
events and their transition relation (`Event`, `Step`, `Exec`, `Reach`), the
canonical state `σ_S(i)` (`canon`), exposability, Functional / Relational /
Lifted Monotonicity, Directed Outputs, the common-expansion condition
(`Spec.CommonExpansion`), consistency (`Spec.Consistent`), the
Sealed/Retired/Rejected rows of a lifted output event, and commitment-free
executions (`ExecCF`, `ReachableCF`).  Paper
correspondences are noted on each definition.

Modeling choice: the library uses Lean 4 core only (no Mathlib), so it defines
the little order theory it needs (`PO`, with `≼`).  Sets are predicates and
finite families are `List`s.
-/

namespace CC

universe u

/-- A partial order.  `le a b` reads "`b` expands/refines `a`". -/
class PO (α : Type u) where
  le : α → α → Prop
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c
  antisymm : ∀ {a b}, le a b → le b a → a = b

infix:50 " ≼ " => PO.le

/-- A table: a set of rows `(i, o)`. -/
abbrev Table (I O : Type) := I → O → Prop

section
variable {I O : Type} [PO I] [PO O]

/-- Ordered relational specification (Def. relational specification):
a table total on inputs. -/
structure Spec (I O : Type) [PO I] [PO O] where
  S : Table I O
  total : ∀ i, ∃ o, S i o

/-- Functional dependency (Def. functional specification). -/
def Spec.Functional (sp : Spec I O) : Prop :=
  ∀ i o o', sp.S i o → sp.S i o' → o = o'

/-- Functional monotonicity (Def. functional monotonicity), stated on rows. -/
def Spec.MonotoneF (sp : Spec I O) : Prop :=
  ∀ i j o u, i ≼ j → sp.S i o → sp.S j u → o ≼ u

/-- Specification state (Def. specification state). -/
structure State (sp : Spec I O) where
  cur : I
  R : Table I O
  sub : ∀ k u, R k u → sp.S k u
  hasCur : ∃ o, R cur o
  above : ∀ k u, R k u → cur ≼ k

/-- States are determined by current input and remainder table. -/
theorem State.ext' {sp : Spec I O} {σ τ : State sp}
    (h1 : σ.cur = τ.cur) (h2 : σ.R = τ.R) : σ = τ := by
  cases σ; cases τ; cases h1; cases h2; rfl

/-- Canonical state at `i` (Eq. canonical-state). -/
def canon (sp : Spec I O) (i : I) : State sp where
  cur := i
  R := fun k u => sp.S k u ∧ i ≼ k
  sub := fun _ _ h => h.1
  hasCur := by
    obtain ⟨o, ho⟩ := sp.total i
    exact ⟨o, ho, PO.refl i⟩
  above := fun _ _ h => h.2

/-- Events of the transition system. -/
inductive Event (I O : Type) where
  | input (j : I)
  | output (o : O)

/-- Remainder table after `input j` (Eq. input-event). -/
def inputTable {sp : Spec I O} (σ : State sp) (j : I) : Table I O :=
  fun k u => σ.R k u ∧ j ≼ k

/-- Remainder table after `output o` (Eq. output-action; also the lifted
output event). -/
def outputTable {sp : Spec I O} (σ : State sp) (o : O) : Table I O :=
  fun k u => σ.R k u ∧ o ≼ u

/-- One step of the transition system.  An input event is legal when the
target input has a row; an output event emits an output of the current
input's fiber. -/
inductive Step {sp : Spec I O} : State sp → Event I O → State sp → Prop where
  | input (σ τ : State sp) (j : I) :
      (∃ u, σ.R j u) → τ.cur = j → τ.R = inputTable σ j → Step σ (.input j) τ
  | output (σ τ : State sp) (o : O) :
      σ.R σ.cur o → τ.cur = σ.cur → τ.R = outputTable σ o → Step σ (.output o) τ

/-- Execution along a list of events. -/
inductive Exec {sp : Spec I O} : State sp → List (Event I O) → State sp → Prop where
  | nil (σ : State sp) : Exec σ [] σ
  | cons {σ τ ρ : State sp} {e : Event I O} {es : List (Event I O)} :
      Step σ e τ → Exec τ es ρ → Exec σ (e :: es) ρ

/-- `τ` is reachable from `σ`. -/
def Reach {sp : Spec I O} (σ τ : State sp) : Prop := ∃ es, Exec σ es τ

/-- A run ends at `τ` (Def. run): reachable from some canonical state. -/
def IsRun {sp : Spec I O} (τ : State sp) : Prop := ∃ i, Reach (canon sp i) τ

/-- Runs ending at the states of `fam` are confluent at `j`. -/
def ConfluentAt {sp : Spec I O} (fam : List (State sp)) (j : I) : Prop :=
  ∃ τ : State sp, τ.cur = j ∧ ∀ σ ∈ fam, Reach σ τ

/-- Consistency (Def. consistency). -/
def Spec.Consistent (sp : Spec I O) : Prop :=
  ∀ fam : List (State sp), (∀ σ ∈ fam, IsRun σ) →
    ∀ j : I, (∀ σ ∈ fam, σ.cur ≼ j) → ConfluentAt fam j

/-! ### Relational notions (Section 3) -/

/-- Outputs `X` are compatible in `F`. -/
def CompatibleIn (F : O → Prop) (X : List O) : Prop :=
  ∃ u, F u ∧ ∀ x ∈ X, x ≼ u

/-- Joint lift of the output order (Eq. joint-output-order). -/
def JointLift (A B : O → Prop) : Prop :=
  ∀ X : List O, X ≠ [] → (∀ x ∈ X, A x) → CompatibleIn B X

/-- Lifted Monotonicity (Def. lifted-monotonicity). -/
def Spec.LiftedMono (sp : Spec I O) : Prop :=
  ∀ i j, i ≼ j → JointLift (sp.S i) (sp.S j)

/-- Relational Monotonicity. -/
def Spec.RelMono (sp : Spec I O) : Prop :=
  ∀ i j o, i ≼ j → sp.S i o → ∃ u, sp.S j u ∧ o ≼ u

/-- Directed Outputs: every fiber is directed. -/
def Spec.DirectedOutputs (sp : Spec I O) : Prop :=
  ∀ i, JointLift (sp.S i) (sp.S i)

/-- Common-expansion condition (Def. common-expansion-condition). -/
def Spec.CommonExpansion (sp : Spec I O) : Prop :=
  ∀ rows : List (I × O), (∀ r ∈ rows, sp.S r.1 r.2) →
    ∀ j : I, (∀ r ∈ rows, r.1 ≼ j) → ∃ u, sp.S j u ∧ ∀ r ∈ rows, r.2 ≼ u

/-- The three classes of rows ruled out by `o` (Eqs. seal-inputs,
output-retirements, choice-removals). -/
def Sealed {sp : Spec I O} (σ : State sp) (o : O) : Table I O :=
  fun k x => σ.R k x ∧ ¬ ∃ u, σ.R k u ∧ o ≼ u

def Retired {sp : Spec I O} (σ : State sp) (o : O) : Table I O :=
  fun k x => σ.R k x ∧ ¬ (o ≼ x) ∧ ∃ u, σ.R k u ∧ o ≼ u ∧ x ≼ u

def Rejected {sp : Spec I O} (σ : State sp) (o : O) : Table I O :=
  fun k x => σ.R k x ∧ ¬ (o ≼ x) ∧ ¬ Sealed σ o k x ∧ ¬ Retired σ o k x

/-- Exposable (Def. exposable): the output event applies no commitment,
i.e. every ruled-out row is retired. -/
def Exposable {sp : Spec I O} (σ : State sp) (o : O) : Prop :=
  ∀ k x, σ.R k x → ¬ (o ≼ x) → ∃ u, σ.R k u ∧ o ≼ u ∧ x ≼ u

/-- Commitment-free execution: every output event emits an exposable output. -/
inductive ExecCF {sp : Spec I O} : State sp → List (Event I O) → State sp → Prop where
  | nil (σ : State sp) : ExecCF σ [] σ
  | input {σ τ ρ : State sp} {j : I} {es : List (Event I O)} :
      Step σ (.input j) τ → ExecCF τ es ρ → ExecCF σ (.input j :: es) ρ
  | output {σ τ ρ : State sp} {o : O} {es : List (Event I O)} :
      Step σ (.output o) τ → Exposable σ o → ExecCF τ es ρ → ExecCF σ (.output o :: es) ρ

/-- Reachable without commitment. -/
def ReachableCF {sp : Spec I O} (τ : State sp) : Prop :=
  ∃ i es, ExecCF (canon sp i) es τ

end

end CC
