/-
Run lemmas shared by every part: Lemma run-residual and the survivor test
(Proposition confluence).  These hold for arbitrary (relational) ordered
specifications.
-/
import CoordCriterion.Core

namespace CC

variable {I O : Type} [PO I] [PO O]

/-- The outputs emitted along a list of events. -/
def outs : List (Event I O) → List O
  | [] => []
  | .input _ :: es => outs es
  | .output o :: es => o :: outs es

/-- A state's table has the residual shape for emitted outputs `E`. -/
def Residual {sp : Spec I O} (σ : State sp) (E : List O) : Prop :=
  ∀ k u, σ.R k u ↔ (sp.S k u ∧ σ.cur ≼ k ∧ ∀ o ∈ E, o ≼ u)

theorem residual_canon (sp : Spec I O) (i : I) : Residual (canon sp i) [] := by
  intro k u
  simp [canon]

theorem residual_step {sp : Spec I O} {σ τ : State sp} {e : Event I O} {E : List O}
    (hσ : Residual σ E) (hs : Step σ e τ) :
    Residual τ (E ++ outs [e]) := by
  cases hs with
  | input _ j hleg hcur hR =>
    obtain ⟨u0, hu0⟩ := hleg
    have hcj : σ.cur ≼ j := σ.above _ _ hu0
    intro k u
    rw [hR, hcur]
    simp only [inputTable, outs, List.append_nil]
    constructor
    · rintro ⟨h, hjk⟩
      obtain ⟨hS, _, hE⟩ := (hσ k u).1 h
      exact ⟨hS, hjk, hE⟩
    · rintro ⟨hS, hjk, hE⟩
      exact ⟨(hσ k u).2 ⟨hS, PO.trans hcj hjk, hE⟩, hjk⟩
  | output _ o hleg hcur hR =>
    intro k u
    rw [hR, hcur]
    simp only [outputTable, outs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨h, hou⟩
      obtain ⟨hS, hk, hE⟩ := (hσ k u).1 h
      refine ⟨hS, hk, ?_⟩
      rintro x (hx | rfl)
      · exact hE x hx
      · exact hou
    · rintro ⟨hS, hk, hE⟩
      exact ⟨(hσ k u).2 ⟨hS, hk, fun x hx => hE x (Or.inl hx)⟩, hE o (Or.inr rfl)⟩

omit [PO I] [PO O] in
theorem outs_cons (e : Event I O) (es : List (Event I O)) :
    outs (e :: es) = outs [e] ++ outs es := by
  cases e <;> simp [outs]

theorem residual_exec {sp : Spec I O} {σ τ : State sp} {es : List (Event I O)} {E : List O}
    (hσ : Residual σ E) (hx : Exec σ es τ) : Residual τ (E ++ outs es) := by
  induction hx generalizing E with
  | nil => simpa [outs] using hσ
  | @cons σ τ ρ e es hs _ ih =>
    have h1 := residual_step hσ hs
    have h2 := ih h1
    rw [outs_cons, ← List.append_assoc]
    exact h2

/-- **Lemma run-residual.** A run ending at current input `τ.cur` after
emitting `outs es` has remainder table
`S[in ⪰ τ.cur, out ⪰ o₁, …, out ⪰ oₘ]`. -/
theorem run_residual {sp : Spec I O} {i : I} {es : List (Event I O)} {τ : State sp}
    (hx : Exec (canon sp i) es τ) :
    ∀ k u, τ.R k u ↔ (sp.S k u ∧ τ.cur ≼ k ∧ ∀ o ∈ outs es, o ≼ u) := by
  have := residual_exec (residual_canon sp i) hx
  simpa [Residual] using this

/-- Every run state has the residual shape for some list of emitted outputs. -/
theorem IsRun.residual {sp : Spec I O} {τ : State sp} (h : IsRun τ) :
    ∃ E : List O, Residual τ E := by
  obtain ⟨i, es, hx⟩ := h
  exact ⟨outs es, run_residual hx⟩

/-- Steps only remove rows. -/
theorem step_sub {sp : Spec I O} {σ τ : State sp} {e : Event I O}
    (hs : Step σ e τ) : ∀ k u, τ.R k u → σ.R k u := by
  cases hs with
  | input _ j _ _ hR => intro k u h; rw [hR] at h; exact h.1
  | output _ o _ _ hR => intro k u h; rw [hR] at h; exact h.1

theorem reach_sub {sp : Spec I O} {σ τ : State sp} (h : Reach σ τ) :
    ∀ k u, τ.R k u → σ.R k u := by
  obtain ⟨es, hx⟩ := h
  induction hx with
  | nil => exact fun _ _ h => h
  | cons hs _ ih => exact fun k u h => step_sub hs k u (ih k u h)

/-- The state reached by `input j; output u` from a residual state whose
table contains `(j,u)`. -/
def meetState (sp : Spec I O) (j : I) (u : O) (hju : sp.S j u) : State sp where
  cur := j
  R := fun k x => sp.S k x ∧ j ≼ k ∧ u ≼ x
  sub := fun _ _ h => h.1
  hasCur := ⟨u, hju, PO.refl j, PO.refl u⟩
  above := fun _ _ h => h.2.1

theorem reach_meet {sp : Spec I O} {σ : State sp} {E : List O} (hσ : Residual σ E)
    {j : I} {u : O} (hju : σ.R j u) :
    Reach σ (meetState sp j u (σ.sub _ _ hju)) := by
  have hcj : σ.cur ≼ j := σ.above _ _ hju
  -- intermediate state after input j
  let τ1 : State sp :=
    { cur := j
      R := inputTable σ j
      sub := fun k x h => σ.sub k x h.1
      hasCur := ⟨u, hju, PO.refl j⟩
      above := fun _ _ h => h.2 }
  have s1 : Step σ (.input j) τ1 := Step.input σ τ1 j ⟨u, hju⟩ rfl rfl
  have s2 : Step τ1 (.output u) (meetState sp j u (σ.sub _ _ hju)) := by
    refine Step.output τ1 _ u ⟨hju, PO.refl j⟩ rfl ?_
    funext k x
    apply propext
    simp only [meetState, outputTable, inputTable, τ1]
    constructor
    · rintro ⟨hS, hjk, hux⟩
      have hEu : ∀ o ∈ E, o ≼ u := ((hσ j u).1 hju).2.2
      refine ⟨⟨(hσ k x).2 ⟨hS, PO.trans hcj hjk, fun o ho => PO.trans (hEu o ho) hux⟩, hjk⟩, hux⟩
    · rintro ⟨⟨h, hjk⟩, hux⟩
      exact ⟨σ.sub _ _ h, hjk, hux⟩
  exact ⟨[.input j, .output u], Exec.cons s1 (Exec.cons s2 (Exec.nil _))⟩

/-- **Proposition (Survivor test).** Runs ending at the states of `fam`,
with common expansion `j`, are confluent at `j` iff some row at `j`
survives in every final state. -/
theorem survivor_test {sp : Spec I O} (fam : List (State sp))
    (hrun : ∀ σ ∈ fam, IsRun σ) (j : I) (_hj : ∀ σ ∈ fam, σ.cur ≼ j) :
    ConfluentAt fam j ↔ ∃ u, sp.S j u ∧ ∀ σ ∈ fam, σ.R j u := by
  constructor
  · rintro ⟨τ, hτ, hreach⟩
    obtain ⟨u, hu⟩ := τ.hasCur
    rw [hτ] at hu
    exact ⟨u, τ.sub _ _ hu, fun σ hσ => reach_sub (hreach σ hσ) j u hu⟩
  · rintro ⟨u, hju, hall⟩
    refine ⟨meetState sp j u hju, rfl, fun σ hσ => ?_⟩
    obtain ⟨E, hE⟩ := (hrun σ hσ).residual
    have := reach_meet hE (hall σ hσ)
    exact this

end CC
