import CoordCriterion.Foundations.Runs

/-!
# Commitments and coordination (Sections 4.3–4.4, Appendix C `app:bases`)

Namespace `CC`.  Further claims of these sections are in
`Distributed/Systems.lean`.

* `Commitment`                         — Def. commitment (eq. commitment-unsubsumed)
* `canonicalCommitment`                 — the canonical commitment `x_o`
* `commitmentState`, `commitmentApp`          — its resulting state and application
* `SEvent`, `SysStep`, `SysExec`       — Def. system output event (the canonical
                                         `output(o)`; `x_o` from the basis when `o`
                                         is not legal), commitment events `apply(γ)`
                                         (a nonempty basis sequence, applied without
                                         emitting), run under a basis; `SEvent.erase`
                                         (commitment events erase to nothing)
* `containment`, `outputTable_mono`,
  `exposable_iff_empty`                — Lemma output-containment (1)–(3)
* `canonical_support`, `eps_step_iff`  — the canonical event under `B_P`; outputs
                                         under the empty basis are legal outputs
* `split_output`                       — commitments followed by a legal output
* `composite`, `applySeq_composite`    — Lemma compound-commitment
* `commitment_effect`                  — the two effects of a commitment
* `CoordFree`, `coordFree_execCF`, `execCF_coordFree` — coordination-free runs
                                         (executions under the empty basis)
* `canonical_equivalent`               — Lemma canonical-equivalent (the canonical run
                                         skips commitment events)
* `conflicting_outputs`                — Prop. prop:commitment-conflict
-/

namespace CC

open Classical

variable {I O : Type} [PO I] [PO O]

section
variable {sp : Spec I O}

/-! ### Def. commitment -/

/-- **Def. commitment.**  A partial function on specification states that keeps
the current input, only removes rows, removes at least one row, and satisfies
eq. commitment-unsubsumed, judged at the resulting table. -/
structure Commitment (sp : Spec I O) where
  app : State sp → Option (State sp)
  cur_eq : ∀ σ τ, app σ = some τ → τ.cur = σ.cur
  sub : ∀ σ τ, app σ = some τ → ∀ k u, τ.R k u → σ.R k u
  removes : ∀ σ τ, app σ = some τ → ∃ k u, σ.R k u ∧ ¬ τ.R k u
  unsubsumed : ∀ σ τ, app σ = some τ →
    ∀ k u w, σ.R k u → ¬ τ.R k u → τ.R k w → ¬ (u ≼ w)

/-! ### The canonical commitment -/

theorem subsumed_keep {σ τ : State sp} {o : O}
    (hsub : ∀ k u, τ.R k u → σ.R k u)
    (hkeep : ∀ k u, σ.R k u → o ≼ u → τ.R k u) {k : I} {x : O} (hτ : τ.R k x) :
    Subsumed τ o k x ↔ Subsumed σ o k x := by
  constructor
  · rintro ⟨_, hox, u, hu, hou, hxu⟩
    exact ⟨hsub _ _ hτ, hox, u, hsub _ _ hu, hou, hxu⟩
  · rintro ⟨_, hox, u, hu, hou, hxu⟩
    exact ⟨hτ, hox, u, hkeep _ _ hu hou, hou, hxu⟩

theorem excluded_keep {σ τ : State sp} {o : O}
    (hsub : ∀ k u, τ.R k u → σ.R k u)
    (hkeep : ∀ k u, σ.R k u → o ≼ u → τ.R k u) {k : I} {x : O} (hτ : τ.R k x) :
    Excluded τ o k x ↔ Excluded σ o k x := by
  unfold Excluded
  rw [subsumed_keep hsub hkeep hτ]
  exact ⟨fun h => ⟨hsub _ _ hτ, h.2⟩, fun h => ⟨hτ, h.2⟩⟩

theorem not_excluded_of_ge {σ : State sp} {o : O} {k : I} {u : O}
    (hou : o ≼ u) : ¬ Excluded σ o k u :=
  fun he => he.2.1 hou

/-- `(i, R ∖ Excluded_o)`. -/
def commitmentState (σ : State sp) (o : O) (ho : σ.R σ.cur o) : State sp where
  cur := σ.cur
  R := fun k x => σ.R k x ∧ ¬ Excluded σ o k x
  sub := fun k x h => σ.sub k x h.1
  hasCur := ⟨o, ho, not_excluded_of_ge (PO.refl o)⟩
  above := fun k x h => σ.above k x h.1

theorem commitmentState_keep (σ : State sp) (o : O) (ho : σ.R σ.cur o) :
    ∀ k u, σ.R k u → o ≼ u → (commitmentState σ o ho).R k u :=
  fun _ _ h hou => ⟨h, not_excluded_of_ge hou⟩

noncomputable def commitmentApp (o : O) (σ : State sp) : Option (State sp) :=
  if h : σ.R σ.cur o ∧ ∃ k x, Excluded σ o k x then some (commitmentState σ o h.1) else none

theorem commitmentApp_eq {o : O} {σ τ : State sp} :
    commitmentApp o σ = some τ ↔
      ∃ h : σ.R σ.cur o, (∃ k x, Excluded σ o k x) ∧ commitmentState σ o h = τ := by
  unfold commitmentApp
  split
  · rename_i h
    simp only [Option.some.injEq]
    exact ⟨fun e => ⟨h.1, h.2, e⟩, fun ⟨_, _, e⟩ => e⟩
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    rintro ⟨h1, h2, _⟩
    exact h ⟨h1, h2⟩

/-- The canonical commitment for `o`, defined when `o` is in the current fiber
and `Excluded_o` is nonempty. -/
noncomputable def canonicalCommitment (o : O) : Commitment sp where
  app := commitmentApp o
  cur_eq := by
    intro σ τ h; obtain ⟨_, _, rfl⟩ := commitmentApp_eq.1 h; rfl
  sub := by
    intro σ τ h k u hu; obtain ⟨_, _, rfl⟩ := commitmentApp_eq.1 h; exact hu.1
  removes := by
    intro σ τ h
    obtain ⟨_, ⟨k, x, he⟩, rfl⟩ := commitmentApp_eq.1 h
    exact ⟨k, x, he.1, fun h' => h'.2 he⟩
  unsubsumed := by
    intro σ τ h k u w hu hnu hw huw
    obtain ⟨_, _, rfl⟩ := commitmentApp_eq.1 h
    have he : Excluded σ o k u := Classical.byContradiction fun hn => hnu ⟨hu, hn⟩
    obtain ⟨hw, hnw⟩ := hw
    apply he.2.2
    by_cases how : o ≼ w
    · exact ⟨hu, he.2.1, w, hw, how, huw⟩
    · have hsw : Subsumed σ o k w := Classical.byContradiction fun hs => hnw ⟨hw, how, hs⟩
      obtain ⟨_, _, v, hv, hov, hwv⟩ := hsw
      exact ⟨hu, he.2.1, v, hv, hov, PO.trans huw hwv⟩

theorem commitmentState_no_excluded (σ : State sp) (o : O) (ho : σ.R σ.cur o) :
    ∀ k x, ¬ Excluded (commitmentState σ o ho) o k x := by
  intro k x he
  have hx := he.1
  exact hx.2 ((excluded_keep (σ := σ) (τ := commitmentState σ o ho)
    (fun _ _ h => h.1) (commitmentState_keep σ o ho) hx).1 he)

/-! ### Sequences of commitments and the events of a system -/

/-- Apply `c₁ ⋯ cₙ` in order, each defined at the state its predecessors leave. -/
inductive ApplySeq : List (Commitment sp) → State sp → State sp → Prop where
  | nil (σ : State sp) : ApplySeq [] σ σ
  | cons {c : Commitment sp} {cs : List (Commitment sp)} {σ τ ρ : State sp} :
      c.app σ = some τ → ApplySeq cs τ ρ → ApplySeq (c :: cs) σ ρ

theorem ApplySeq.cur_eq {γ : List (Commitment sp)} {σ ρ : State sp}
    (h : ApplySeq γ σ ρ) : ρ.cur = σ.cur := by
  induction h with
  | nil => rfl
  | @cons c _ σ τ _ hc _ ih => rw [ih, c.cur_eq σ τ hc]

theorem ApplySeq.sub {γ : List (Commitment sp)} {σ ρ : State sp}
    (h : ApplySeq γ σ ρ) : ∀ k u, ρ.R k u → σ.R k u := by
  induction h with
  | nil => exact fun _ _ h => h
  | @cons c _ σ τ _ hc _ ih => exact fun k u h => c.sub σ τ hc k u (ih k u h)

theorem ApplySeq.det {γ : List (Commitment sp)} {σ ρ₁ ρ₂ : State sp}
    (h₁ : ApplySeq γ σ ρ₁) (h₂ : ApplySeq γ σ ρ₂) : ρ₁ = ρ₂ := by
  induction h₁ generalizing ρ₂ with
  | nil => cases h₂; rfl
  | cons hc _ ih =>
    cases h₂ with
    | cons hc' h' =>
      rw [hc] at hc'
      cases hc'
      exact ih h'

/-- Events of a system: input events, output events `output(o)` (the lifted
output event of Section 3), and commitment events `apply(γ)`, which apply a
commitment sequence without emitting. -/
inductive SEvent (sp : Spec I O) where
  | input (j : I)
  | output (o : O)
  | commitment (γ : List (Commitment sp))

/-- What the environment observes: commitment events are unobservable and
erase to nothing.  A list of events erases to `es.filterMap SEvent.erase`. -/
def SEvent.erase : SEvent sp → Option (Event I O)
  | .input j => some (.input j)
  | .output o => some (.output o)
  | .commitment _ => none

/-- A commitment basis. -/
abbrev CommitmentBasis (sp : Spec I O) := Commitment sp → Prop

/-- **Def. system output event** (with input events unchanged).  A system's
output event `output(o)` is the lifted output event of Section 3 (`Step`): it
needs `o ∈ R(i)` and ends at `(i, R[out ⪰ o])`.  When `o` is not legal
(`¬ Exposable σ o`), it applies the canonical commitment `x_o`, which must then
belong to the basis. -/
inductive SysStep (B : CommitmentBasis sp) : State sp → SEvent sp → State sp → Prop where
  | input {σ τ : State sp} {j : I} : Step σ (.input j) τ → SysStep B σ (.input j) τ
  | output {σ τ : State sp} {o : O} :
      Step σ (.output o) τ → (Exposable σ o ∨ B (canonicalCommitment o)) →
      SysStep B σ (.output o) τ
  /-- **Commitment event** `apply(γ)`: a nonempty sequence of basis commitments,
  each defined at the state its predecessors leave; it ends at the state the
  sequence leaves, subsumes nothing and emits nothing. -/
  | commitment {σ τ : State sp} {γ : List (Commitment sp)} :
      (∀ c ∈ γ, B c) → γ ≠ [] → ApplySeq γ σ τ → SysStep B σ (.commitment γ) τ

/-- Executions under a basis. -/
inductive SysExec (B : CommitmentBasis sp) : State sp → List (SEvent sp) → State sp → Prop where
  | nil (σ : State sp) : SysExec B σ [] σ
  | cons {σ τ ρ : State sp} {e : SEvent sp} {es : List (SEvent sp)} :
      SysStep B σ e τ → SysExec B τ es ρ → SysExec B σ (e :: es) ρ

/-- **Def. run under a basis**: an execution under `B` from a canonical state. -/
def RunUnder (B : CommitmentBasis sp) (es : List (SEvent sp)) (τ : State sp) : Prop :=
  ∃ i, SysExec B (canon sp i) es τ

theorem SysStep.sub {B : CommitmentBasis sp} {σ τ : State sp} {e : SEvent sp}
    (h : SysStep B σ e τ) : ∀ k u, τ.R k u → σ.R k u := by
  cases h with
  | input hs => exact step_sub hs
  | output hs _ => exact step_sub hs
  | commitment _ _ hγ => exact hγ.sub

/-- A commitment event keeps the current input. -/
theorem SysStep.commitment_cur {B : CommitmentBasis sp} {σ τ : State sp} {γ : List (Commitment sp)}
    (h : SysStep B σ (.commitment γ) τ) : τ.cur = σ.cur := by
  cases h with
  | commitment _ _ hγ => exact hγ.cur_eq

theorem SysExec.sub {B : CommitmentBasis sp} {σ τ : State sp} {es : List (SEvent sp)}
    (h : SysExec B σ es τ) : ∀ k u, τ.R k u → σ.R k u := by
  induction h with
  | nil => exact fun _ _ h => h
  | cons hs _ ih => exact fun k u h => hs.sub k u (ih k u h)

/-- Events of a system are deterministic. -/
theorem SysStep.det {B B' : CommitmentBasis sp} {σ τ τ' : State sp} {e : SEvent sp}
    (h : SysStep B σ e τ) (h' : SysStep B' σ e τ') : τ = τ' := by
  cases h with
  | input hs => cases h' with | input hs' => exact step_det hs hs'
  | output hs _ => cases h' with | output hs' _ => exact step_det hs hs'
  | commitment _ _ hγ => cases h' with | commitment _ _ hγ' => exact hγ.det hγ'

theorem SysExec.det {B B' : CommitmentBasis sp} {σ τ τ' : State sp} {es : List (SEvent sp)}
    (h : SysExec B σ es τ) (h' : SysExec B' σ es τ') : τ = τ' := by
  induction h generalizing τ' with
  | nil => cases h'; rfl
  | cons hs _ ih =>
    cases h' with
    | cons hs' hr' => exact ih ((hs.det hs') ▸ hr')

/-- A larger basis allows more events. -/
theorem SysStep.mono {B B' : CommitmentBasis sp} (hB : ∀ c, B c → B' c) {σ τ : State sp}
    {e : SEvent sp} (h : SysStep B σ e τ) : SysStep B' σ e τ := by
  cases h with
  | input hs => exact .input hs
  | output hs hb => exact .output hs (hb.imp_right (hB _))
  | commitment hb hne hγ => exact .commitment (fun c hc => hB c (hb c hc)) hne hγ

theorem SysExec.mono {B B' : CommitmentBasis sp} (hB : ∀ c, B c → B' c) {σ τ : State sp}
    {es : List (SEvent sp)} (h : SysExec B σ es τ) : SysExec B' σ es τ := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (hs.mono hB) ih

theorem SysExec.append {B : CommitmentBasis sp} {σ τ ρ : State sp} {a b : List (SEvent sp)}
    (ha : SysExec B σ a τ) (hb : SysExec B τ b ρ) : SysExec B σ (a ++ b) ρ := by
  induction ha with
  | nil => exact hb
  | cons hs _ ih => exact .cons hs (ih hb)

theorem SysExec.append_inv {B : CommitmentBasis sp} {σ ρ : State sp} {a b : List (SEvent sp)}
    (h : SysExec B σ (a ++ b) ρ) : ∃ τ, SysExec B σ a τ ∧ SysExec B τ b ρ := by
  induction a generalizing σ with
  | nil => exact ⟨σ, .nil σ, h⟩
  | cons e a ih =>
    cases h with
    | cons hs hr =>
      obtain ⟨τ, h1, h2⟩ := ih hr
      exact ⟨τ, .cons hs h1, h2⟩

/-! ### Lemma output-containment -/

/-- The state `(i, R[out ⪰ o])`. -/
def outState (σ : State sp) (o : O) (ho : σ.R σ.cur o) : State sp where
  cur := σ.cur
  R := outputTable σ o
  sub := fun k x h => σ.sub k x h.1
  hasCur := ⟨o, ho, PO.refl o⟩
  above := fun k x h => σ.above k x h.1

theorem step_output_outState {σ : State sp} {o : O} (ho : σ.R σ.cur o) :
    Step σ (.output o) (outState σ o ho) :=
  Step.output σ _ o ho rfl rfl

theorem step_output_iff {σ τ : State sp} {o : O} :
    Step σ (.output o) τ ↔ σ.R σ.cur o ∧ τ.cur = σ.cur ∧ τ.R = outputTable σ o := by
  constructor
  · intro h; cases h with | output _ _ h1 h2 h3 => exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact Step.output σ τ o h1 h2 h3

/-- **Lemma output-containment, (1).**  An output event `output(o)` needs
`o ∈ R(i)`, keeps the current input, and ends at `(i, R[out ⪰ o])`.  The last
component is the table equation itself. -/
theorem containment {B : CommitmentBasis sp} {σ τ : State sp} {o : O}
    (h : SysStep B σ (.output o) τ) :
    τ.cur = σ.cur ∧ σ.R σ.cur o ∧ (∀ k u, τ.R k u → σ.R k u ∧ o ≼ u) ∧
      τ.R = outputTable σ o := by
  cases h with
  | output hs _ =>
    obtain ⟨ho, hcur, hR⟩ := step_output_iff.1 hs
    exact ⟨hcur, ho, fun k u hu => by rw [hR] at hu; exact hu, hR⟩

/-- **Lemma output-containment, (2).**  If `R ⊆ R̂` at the same current input,
then `R[out ⪰ o] ⊆ R̂[out ⪰ o]`. -/
theorem outputTable_mono {σ σ' : State sp} (hsub : ∀ k u, σ.R k u → σ'.R k u) (o : O) :
    ∀ k u, outputTable σ o k u → outputTable σ' o k u :=
  fun k u h => ⟨hsub k u h.1, h.2⟩

/-- `Exposable` is exactly `Excluded_o = ∅`: `output(o)` applies a commitment,
`x_o`, exactly when `o` is not legal. -/
theorem exposable_iff_empty (σ : State sp) (o : O) :
    Exposable σ o ↔ ¬ ∃ k x, Excluded σ o k x := by
  constructor
  · intro h ⟨k, x, he⟩
    exact he.2.2 ⟨he.1, he.2.1, h k x he.1 he.2.1⟩
  · intro he k x hx hnx
    exact Classical.byContradiction fun hn =>
      he ⟨k, x, hx, hnx, fun hs => hn hs.2.2⟩

/-- When `o ∈ R(i)` is not legal, `x_o` applies and leaves the table
`R ∖ Excluded_o`; the output event then subsumes the rest. -/
theorem canonicalCommitment_applies {σ : State sp} {o : O} (ho : σ.R σ.cur o)
    (hn : ¬ Exposable σ o) :
    (canonicalCommitment o).app σ = some (commitmentState σ o ho) := by
  have he : ∃ k x, Excluded σ o k x :=
    Classical.byContradiction fun h => hn ((exposable_iff_empty σ o).2 h)
  exact commitmentApp_eq.2 ⟨ho, he, rfl⟩

/-- The canonical basis `B_P`. -/
def canonCommitmentBasis (sp : Spec I O) : CommitmentBasis sp := fun c =>
  ∃ o : O, c = canonicalCommitment o ∧
    ∃ σ τ : State sp, (canonicalCommitment o).app σ = some τ

/-- Under any basis containing `B_P` (in particular `B_P` itself) the output
event `output(o)` is available for every `o ∈ R(i)`. -/
theorem canonical_support_of {B : CommitmentBasis sp}
    (hB : ∀ c, canonCommitmentBasis sp c → B c) (σ : State sp) (o : O)
    (ho : σ.R σ.cur o) : SysStep B σ (.output o) (outState σ o ho) := by
  refine SysStep.output (step_output_outState ho) ?_
  by_cases hx : Exposable σ o
  · exact Or.inl hx
  · exact Or.inr (hB _ ⟨o, rfl, σ, _, canonicalCommitment_applies ho hx⟩)

/-- The canonical event `output(o)` is available under `B_P` and ends at
`(i, R[out ⪰ o])`. -/
theorem canonical_support (σ : State sp) (o : O) (ho : σ.R σ.cur o) :
    SysStep (canonCommitmentBasis sp) σ (.output o) (outState σ o ho) :=
  canonical_support_of (fun _ h => h) σ o ho

/-- Under any basis, a legal output's event is available. -/
theorem legal_output_step {B : CommitmentBasis sp} {σ τ : State sp} {o : O}
    (hs : Step σ (.output o) τ) (hexp : Exposable σ o) : SysStep B σ (.output o) τ :=
  SysStep.output hs (Or.inl hexp)

/-- Under the empty basis an output event is available exactly for a legal
output, and then it ends at `(i, R[out ⪰ o])`. -/
theorem eps_step_iff {σ τ : State sp} {o : O} :
    SysStep (fun _ => False) σ (.output o) τ ↔
      σ.R σ.cur o ∧ Exposable σ o ∧ τ.cur = σ.cur ∧ τ.R = outputTable σ o := by
  constructor
  · intro h
    cases h with
    | output hs hb =>
      obtain ⟨ho, hcur, hR⟩ := step_output_iff.1 hs
      exact ⟨ho, hb.resolve_right id, hcur, hR⟩
  · rintro ⟨ho, hleg, hcur, hR⟩
    exact SysStep.output (Step.output σ τ o ho hcur hR) (Or.inl hleg)

/-- An output event of the old compound form (commitments `γ` from `B`
followed by emitting an `o` that is legal after them) is a commitment event
followed by a legal output event. -/
theorem split_output {B : CommitmentBasis sp} {σ σc τ : State sp} {γ : List (Commitment sp)}
    {o : O} (hB : ∀ c ∈ γ, B c) (hγ : ApplySeq γ σ σc) (ho : σc.R σc.cur o)
    (hleg : Exposable σc o) (hcur : τ.cur = σ.cur) (hR : τ.R = outputTable σc o) :
    SysExec B σ ((if γ = [] then [] else [.commitment γ]) ++ [.output o]) τ := by
  have hout : SysStep B σc (.output o) τ :=
    legal_output_step (Step.output σc τ o ho (hcur.trans hγ.cur_eq.symm) hR) hleg
  by_cases hne : γ = []
  · subst hne; cases hγ
    simpa using SysExec.cons hout (.nil _)
  · simp only [hne, ite_false]
    exact .cons (.commitment hB hne hγ) (.cons hout (.nil _))

/-! ### Lemma compound-commitment -/

/-- Apply a sequence as one partial function. -/
noncomputable def compApp : List (Commitment sp) → State sp → Option (State sp)
  | [], σ => some σ
  | c :: cs, σ => (c.app σ).bind (compApp cs)

theorem compApp_iff {cs : List (Commitment sp)} {σ ρ : State sp} :
    compApp cs σ = some ρ ↔ ApplySeq cs σ ρ := by
  induction cs generalizing σ with
  | nil =>
    simp only [compApp, Option.some.injEq]
    exact ⟨fun h => h ▸ ApplySeq.nil _, fun h => by cases h; rfl⟩
  | cons c cs ih =>
    simp only [compApp]
    constructor
    · intro h
      cases hc : c.app σ with
      | none => rw [hc] at h; simp at h
      | some τ =>
        rw [hc] at h
        exact ApplySeq.cons hc (ih.1 h)
    · intro h
      cases h with
      | cons hc h' => rw [hc]; exact ih.2 h'

theorem applySeq_unsubsumed {cs : List (Commitment sp)} {σ ρ : State sp}
    (h : ApplySeq cs σ ρ) :
    ∀ k u w, σ.R k u → ¬ ρ.R k u → ρ.R k w → ¬ (u ≼ w) := by
  induction h with
  | nil => exact fun _ _ _ hu hnu _ => absurd hu hnu
  | @cons c _ σ τ _ hc hrest ih =>
    intro k u w hu hnu hw
    by_cases hτ : τ.R k u
    · exact ih k u w hτ hnu hw
    · exact c.unsubsumed σ τ hc k u w hu hτ (hrest.sub k w hw)

/-- **Lemma compound-commitment.**  The composite of a nonempty sequence of
commitments is a commitment. -/
noncomputable def composite (c : Commitment sp) (cs : List (Commitment sp)) :
    Commitment sp where
  app := compApp (c :: cs)
  cur_eq := fun _ _ h => (compApp_iff.1 h).cur_eq
  sub := fun _ _ h => (compApp_iff.1 h).sub
  removes := by
    intro σ ρ h
    have h' := compApp_iff.1 h
    cases h' with
    | @cons _ _ _ τ _ hc hrest =>
      obtain ⟨k, u, hu, hnu⟩ := c.removes σ τ hc
      exact ⟨k, u, hu, fun hρ => hnu (hrest.sub k u hρ)⟩
  unsubsumed := fun _ _ h => applySeq_unsubsumed (compApp_iff.1 h)

/-- A compound commitment sequence has the same effect as its composite alone. -/
theorem applySeq_composite (c : Commitment sp) (cs : List (Commitment sp))
    (σ σc : State sp) :
    ApplySeq (c :: cs) σ σc ↔ ApplySeq [composite c cs] σ σc := by
  constructor
  · intro h
    exact ApplySeq.cons (compApp_iff.2 h) (ApplySeq.nil _)
  · intro h
    cases h with
    | cons hc hn => cases hn; exact compApp_iff.1 hc

/-! ### Effect of a commitment at an input -/

/-- At an input where a commitment removes rows, it either removes the whole
fiber or leaves a row; in the latter case no removed row extends a survivor. -/
theorem commitment_effect (c : Commitment sp) {σ τ : State sp} (h : c.app σ = some τ)
  (k : I) (_hk : ∃ u, σ.R k u ∧ ¬ τ.R k u) :
  ((∀ u, ¬ τ.R k u) ∨
    (∃ w, τ.R k w ∧ ∀ u, σ.R k u → ¬ τ.R k u → ¬ (u ≼ w))) ∧
  ¬ ((∀ u, ¬ τ.R k u) ∧ ∃ w, τ.R k w) := by
  refine ⟨?_, fun ⟨h1, w, hw⟩ => h1 w hw⟩
  by_cases hrem : ∃ w, τ.R k w
  · obtain ⟨w, hw⟩ := hrem
    exact Or.inr ⟨w, hw, fun u hu hnu => c.unsubsumed σ τ h k u w hu hnu hw⟩
  · exact Or.inl fun u hu => hrem ⟨u, hu⟩

/-- A commitment never empties the current fiber. -/
theorem commitment_preserves_current_fiber (c : Commitment sp) {σ τ : State sp}
  (h : c.app σ = some τ) : ∃ w, τ.R σ.cur w := by
  have := τ.hasCur; rwa [c.cur_eq σ τ h] at this

/-- In a functional specification, removing one row empties its fiber. -/
theorem functional_commitment_empties_fiber (hf : sp.Functional) (c : Commitment sp)
  {σ τ : State sp} (_h : c.app σ = some τ) (k : I) (hk : ∃ u, σ.R k u ∧ ¬ τ.R k u) :
  ∀ w, ¬ τ.R k w := by
  intro w hw
  obtain ⟨u, hu, hnu⟩ := hk
  have : u = w := hf k u w (σ.sub _ _ hu) (τ.sub _ _ hw)
  exact hnu (this ▸ hw)

/-! ### Def. coordination -/

/-- The empty basis. -/
abbrev noBasis (sp : Spec I O) : CommitmentBasis sp := fun _ => False

/-- A run from `σ` is coordination-free (commitment-free) when no event
applies a commitment: it has no commitment event and every output event emits
a legal output.  These are exactly the executions under the empty basis. -/
def CoordFree (σ : State sp) (es : List (SEvent sp)) : Prop :=
  ∃ τ, SysExec (noBasis sp) σ es τ

/-- A run from `σ` coordinates when some event applies a commitment. -/
def Coordinates (σ : State sp) (es : List (SEvent sp)) : Prop := ¬ CoordFree σ es

theorem coordFree_iff_not (σ : State sp) (es : List (SEvent sp)) :
    CoordFree σ es ↔ ¬ Coordinates σ es :=
  ⟨fun h hn => hn h, fun h => Classical.byContradiction h⟩

/-- An execution under the empty basis has no commitment event. -/
theorem SysExec.noCommit_of_empty {σ τ : State sp} {es : List (SEvent sp)}
    (h : SysExec (noBasis sp) σ es τ) : ∀ γ, SEvent.commitment γ ∉ es := by
  induction h with
  | nil => intro _ h; cases h
  | cons hs _ ih =>
    intro γ hm
    rcases List.mem_cons.1 hm with rfl | hm
    · cases hs with
      | commitment hb hne _ =>
        cases γ with
        | nil => exact hne rfl
        | cons c _ => exact hb c List.mem_cons_self
    · exact ih γ hm

/-- Coordination-free executions are commitment-free executions (`ExecCF`) of
the erased events. -/
theorem coordFree_execCF {σ τ : State sp} {es : List (SEvent sp)}
    (h : SysExec (noBasis sp) σ es τ) : ExecCF σ (es.filterMap SEvent.erase) τ := by
  induction h with
  | nil => exact ExecCF.nil _
  | @cons σ τ ρ e es hs _ ih =>
    cases e with
    | input j =>
      cases hs with
      | input hs => exact ExecCF.input hs ih
    | output o =>
      obtain ⟨ho, hexp, hcur, hR⟩ := eps_step_iff.1 hs
      exact ExecCF.output (Step.output _ _ o ho hcur hR) hexp ih
    | commitment γ =>
      cases hs with
      | commitment hb hne _ =>
        cases γ with
        | nil => exact absurd rfl hne
        | cons c _ => exact (hb c List.mem_cons_self).elim

/-- A coordination-free run under any basis erases to a commitment-free
execution to the same final state. -/
theorem CoordFree.execCF {B : CommitmentBasis sp} {σ τ : State sp} {es : List (SEvent sp)}
    (h : SysExec B σ es τ) (hf : CoordFree σ es) : ExecCF σ (es.filterMap SEvent.erase) τ := by
  obtain ⟨τ', h'⟩ := hf
  have := h'.det h
  subst this
  exact coordFree_execCF h'

theorem execCF_coordFree (B : CommitmentBasis sp) {σ τ : State sp} {es : List (Event I O)}
    (h : ExecCF σ es τ) :
    ∃ es' : List (SEvent sp), es'.filterMap SEvent.erase = es ∧ CoordFree σ es' ∧
      SysExec B σ es' τ := by
  suffices ∃ es' : List (SEvent sp), es'.filterMap SEvent.erase = es ∧
      SysExec (noBasis sp) σ es' τ by
    obtain ⟨es', he, hx⟩ := this
    exact ⟨es', he, ⟨τ, hx⟩, hx.mono (fun _ h => h.elim)⟩
  induction h with
  | nil => exact ⟨[], rfl, SysExec.nil _⟩
  | @input σ τ ρ j es hs _ ih =>
    obtain ⟨es', he, hx⟩ := ih
    exact ⟨.input j :: es', by simp [he, SEvent.erase], SysExec.cons (SysStep.input hs) hx⟩
  | @output σ τ ρ o es hs hexp _ ih =>
    obtain ⟨es', he, hx⟩ := ih
    exact ⟨.output o :: es', by simp [he, SEvent.erase],
      SysExec.cons (legal_output_step hs hexp) hx⟩

/-! ### Canonical runs and Lemma canonical-equivalent -/

/-- A canonical step: a step under `B_P` that is not a commitment event.
Every output event of a system is canonical, so canonical runs are the runs
under `B_P` with no commitment events. -/
def CanonStep (σ : State sp) (e : SEvent sp) (τ : State sp) : Prop :=
  SysStep (canonCommitmentBasis sp) σ e τ ∧ ∀ γ, e ≠ .commitment γ

inductive CanonExec : State sp → List (SEvent sp) → State sp → Prop where
  | nil (σ : State sp) : CanonExec σ [] σ
  | cons {σ τ ρ : State sp} {e : SEvent sp} {es : List (SEvent sp)} :
      CanonStep σ e τ → CanonExec τ es ρ → CanonExec σ (e :: es) ρ

/-- Canonical steps are exactly the steps of Sections 2–3. -/
theorem canonStep_step {σ τ : State sp} {e : SEvent sp} (h : CanonStep σ e τ) :
    ∃ e' : Event I O, e.erase = some e' ∧ Step σ e' τ := by
  obtain ⟨hs, hnc⟩ := h
  cases e with
  | input j => cases hs with | input hs => exact ⟨_, rfl, hs⟩
  | output o => cases hs with | output hs _ => exact ⟨_, rfl, hs⟩
  | commitment γ => exact absurd rfl (hnc γ)

theorem step_canonStep {σ τ : State sp} {e : Event I O} (h : Step σ e τ) :
    ∃ e' : SEvent sp, e'.erase = some e ∧ CanonStep σ e' τ := by
  match h with
  | .input _ _ j hleg hc hR =>
    exact ⟨.input j, rfl, SysStep.input (Step.input _ _ j hleg hc hR), fun _ h => by cases h⟩
  | .output _ _ o ho hc hR =>
    refine ⟨.output o, rfl, ?_, fun _ h => by cases h⟩
    have h0 := canonical_support σ o ho
    have : τ = outState σ o ho := State.ext' hc hR
    rw [this]; exact h0

theorem canonExec_exec {σ τ : State sp} {es : List (SEvent sp)} (h : CanonExec σ es τ) :
    Exec σ (es.filterMap SEvent.erase) τ := by
  induction h with
  | nil => exact Exec.nil _
  | cons hs _ ih =>
    obtain ⟨e', he, hst⟩ := canonStep_step hs
    rw [List.filterMap_cons_some he]
    exact Exec.cons hst ih

theorem exec_canonExec {σ τ : State sp} {es : List (Event I O)} (h : Exec σ es τ) :
    ∃ es' : List (SEvent sp), es'.filterMap SEvent.erase = es ∧ CanonExec σ es' τ := by
  induction h with
  | nil => exact ⟨[], rfl, CanonExec.nil _⟩
  | cons hs _ ih =>
    obtain ⟨e', he, hc⟩ := step_canonStep hs
    obtain ⟨es', hes, hx⟩ := ih
    exact ⟨e' :: es', by rw [List.filterMap_cons_some he, hes], CanonExec.cons hc hx⟩

theorem canonExec_sysExec {σ τ : State sp} {es : List (SEvent sp)} (h : CanonExec σ es τ) :
    SysExec (canonCommitmentBasis sp) σ es τ := by
  induction h with
  | nil => exact SysExec.nil _
  | cons hs _ ih => exact SysExec.cons hs.1 ih

/-- A canonical run performs no commitment event. -/
theorem canonExec_noCommit {σ τ : State sp} {es : List (SEvent sp)} (h : CanonExec σ es τ) :
    ∀ γ, SEvent.commitment γ ∉ es := by
  induction h with
  | nil => intro _ h; cases h
  | cons hs _ ih =>
    intro γ hm
    rcases List.mem_cons.1 hm with he | hm
    · exact hs.2 γ he.symm
    · exact ih γ hm

/-- Two runs in lockstep: the original under `B`, the other canonical; at
every observable step the events agree after erasure, current inputs agree,
and the canonical table contains the original's.  A commitment event of the
original is matched by no canonical event (the canonical run stays put, and
the invariant still holds). -/
inductive Lockstep (B : CommitmentBasis sp) :
    State sp → List (SEvent sp) → State sp → State sp → List (SEvent sp) → State sp → Prop where
  | nil (σ σ' : State sp) : Lockstep B σ [] σ σ' [] σ'
  | cons {σ τ ρ σ' τ' ρ' : State sp} {e e' : SEvent sp} {es es' : List (SEvent sp)} :
      SysStep B σ e τ → CanonStep σ' e' τ' → e.erase = e'.erase →
      τ.cur = τ'.cur → (∀ k u, τ.R k u → τ'.R k u) →
      Lockstep B τ es ρ τ' es' ρ' → Lockstep B σ (e :: es) ρ σ' (e' :: es') ρ'
  | commitment {σ τ ρ σ' ρ' : State sp} {γ : List (Commitment sp)} {es es' : List (SEvent sp)} :
      SysStep B σ (.commitment γ) τ → τ.cur = σ'.cur → (∀ k u, τ.R k u → σ'.R k u) →
      Lockstep B τ es ρ σ' es' ρ' → Lockstep B σ (.commitment γ :: es) ρ σ' es' ρ'

theorem Lockstep.left {B : CommitmentBasis sp} {σ ρ σ' ρ' : State sp} {es es' : List (SEvent sp)}
    (h : Lockstep B σ es ρ σ' es' ρ') : SysExec B σ es ρ := by
  induction h with
  | nil => exact SysExec.nil _
  | cons hs _ _ _ _ _ ih => exact SysExec.cons hs ih
  | commitment hs _ _ _ ih => exact SysExec.cons hs ih

theorem Lockstep.right {B : CommitmentBasis sp} {σ ρ σ' ρ' : State sp} {es es' : List (SEvent sp)}
    (h : Lockstep B σ es ρ σ' es' ρ') : CanonExec σ' es' ρ' := by
  induction h with
  | nil => exact CanonExec.nil _
  | cons _ hc _ _ _ _ ih => exact CanonExec.cons hc ih
  | commitment _ _ _ _ ih => exact ih

theorem Lockstep.erase {B : CommitmentBasis sp} {σ ρ σ' ρ' : State sp} {es es' : List (SEvent sp)}
    (h : Lockstep B σ es ρ σ' es' ρ') :
    es.filterMap SEvent.erase = es'.filterMap SEvent.erase := by
  induction h with
  | nil => rfl
  | @cons _ _ _ _ _ _ e e' _ _ _ _ he _ _ _ ih =>
    rw [List.filterMap_cons, List.filterMap_cons, he]
    cases e'.erase <;> simp [ih]
  | commitment _ _ _ _ ih => rw [List.filterMap_cons_none rfl]; exact ih

/-- Generalized inductive step of Lemma canonical-equivalent: from any pair of
states with equal current input and `R ⊆ R̂`. -/
theorem canonical_equivalent_gen {B : CommitmentBasis sp} {σ ρ : State sp} {es : List (SEvent sp)}
    (h : SysExec B σ es ρ) :
    ∀ σ' : State sp, σ'.cur = σ.cur → (∀ k u, σ.R k u → σ'.R k u) →
      ∃ es' ρ', Lockstep B σ es ρ σ' es' ρ' := by
  induction h with
  | nil σ => exact fun σ' _ _ => ⟨[], σ', Lockstep.nil σ σ'⟩
  | @cons σ τ ρ e es hs _ ih =>
    intro σ' hc hsub
    cases e with
    | input j =>
      match hs with
      | .input (.input _ _ _ hleg hcur hR) =>
        obtain ⟨u, hu⟩ := hleg
        let τ' : State sp :=
          { cur := j
            R := inputTable σ' j
            sub := fun k x h => σ'.sub k x h.1
            hasCur := ⟨u, hsub _ _ hu, PO.refl j⟩
            above := fun _ _ h => h.2 }
        have hst' : Step σ' (.input j) τ' := Step.input σ' τ' j ⟨u, hsub _ _ hu⟩ rfl rfl
        have hsub' : ∀ k x, τ.R k x → τ'.R k x := by
          intro k x hx; rw [hR] at hx; exact ⟨hsub _ _ hx.1, hx.2⟩
        obtain ⟨es', ρ', hl⟩ := ih τ' hcur.symm hsub'
        exact ⟨.input j :: es', ρ', Lockstep.cons
          (SysStep.input (Step.input _ _ j ⟨u, hu⟩ hcur hR))
          ⟨SysStep.input hst', fun _ h => by cases h⟩
          rfl hcur hsub' hl⟩
    | output o =>
      -- output containment: `R ⊆ R̂` gives `R[out ⪰ o] ⊆ R̂[out ⪰ o]`
      obtain ⟨hcur', ho', hin, _⟩ := containment hs
      have ho'' : σ'.R σ'.cur o := by rw [hc]; exact hsub _ _ ho'
      let τ' := outState σ' o ho''
      have hsub' : ∀ k x, τ.R k x → τ'.R k x := by
        intro k x hx
        obtain ⟨a, b⟩ := hin k x hx
        exact ⟨hsub _ _ a, b⟩
      have hct : τ.cur = τ'.cur := by rw [hcur']; exact hc.symm
      obtain ⟨es', ρ', hl⟩ := ih τ' hct.symm hsub'
      exact ⟨.output o :: es', ρ', Lockstep.cons hs
        ⟨canonical_support σ' o ho'', fun _ h => by cases h⟩
        rfl hct hsub' hl⟩
    | commitment γ =>
      -- the canonical run does nothing; the invariant survives since a
      -- commitment event keeps the current input and only removes rows
      have hct : τ.cur = σ'.cur := by rw [hs.commitment_cur]; exact hc.symm
      have hsub' : ∀ k x, τ.R k x → σ'.R k x := fun k x hx => hsub _ _ (hs.sub k x hx)
      obtain ⟨es', ρ', hl⟩ := ih σ' hct.symm hsub'
      exact ⟨es', ρ', Lockstep.commitment hs hct hsub' hl⟩

/-- **Lemma canonical-equivalent.**  Every run under any basis `B` (from the
canonical state `σ_P(i)`) has an observably equivalent canonical run from the
same canonical state, in lockstep: after each event the canonical run's table
contains the original's.  The canonical run is a run of Sections 2–3; it
skips the original's commitment events, which are unobservable. -/
theorem canonical_equivalent {B : CommitmentBasis sp} {i : I} {es : List (SEvent sp)} {ρ : State sp}
    (h : SysExec B (canon sp i) es ρ) :
    ∃ es' ρ', Lockstep B (canon sp i) es ρ (canon sp i) es' ρ' ∧
      es.filterMap SEvent.erase = es'.filterMap SEvent.erase ∧
      Exec (canon sp i) (es.filterMap SEvent.erase) ρ' ∧
      ρ'.cur = ρ.cur ∧ (∀ k u, ρ.R k u → ρ'.R k u) := by
  obtain ⟨es', ρ', hl⟩ := canonical_equivalent_gen h (canon sp i) rfl (fun _ _ h => h)
  have he := hl.erase
  refine ⟨es', ρ', hl, he, he ▸ canonExec_exec hl.right, ?_⟩
  -- final-state relation from the lockstep
  clear h he
  suffices ∀ {σ σ' : State sp} {es es'}, Lockstep B σ es ρ σ' es' ρ' →
      σ'.cur = σ.cur → (∀ k u, σ.R k u → σ'.R k u) →
      ρ'.cur = ρ.cur ∧ ∀ k u, ρ.R k u → ρ'.R k u from
    this hl rfl (fun _ _ h => h)
  intro σ σ' es es' hl' hc hs
  clear hl
  induction hl' with
  | nil => exact ⟨hc, hs⟩
  | cons _ _ _ hct hsub _ ih => exact ih hct.symm hsub
  | commitment _ hct hsub _ ih => exact ih hct.symm hsub

/-! ### Proposition prop:commitment-conflict -/

/-- **Prop. conflicting output events cannot be reconciled.**  Let `x ∈ R(i)`.
If `output(o)` takes `σ` to `σ'` with no output in `R'(i)` extending `x`, then
`o` is not legal (the event applies `x_o`); and if `output(x)` takes `σ` to
`t`, then no state with current input `i` is reachable (under any basis) from
both `σ'` and `t`. -/
theorem conflicting_outputs {B B' B'' : CommitmentBasis sp} {σ σ' t : State sp}
    {o x : O}
    (h1 : SysStep B σ (.output o) σ') (hno : ∀ w, σ'.R σ.cur w → ¬ x ≼ w)
    (h2 : SysStep B' σ (.output x) t) :
    ¬ Exposable σ o ∧
    ¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧
        (∃ es, SysExec B'' σ' es ρ) ∧ (∃ es, SysExec B'' t es ρ) := by
  obtain ⟨_, hx, ht, _⟩ := containment h2
  refine ⟨?_, ?_⟩
  · intro hexp
    obtain ⟨_, _, _, hR⟩ := containment h1
    by_cases hox : o ≼ x
    · exact hno x (by rw [hR]; exact ⟨hx, hox⟩) (PO.refl x)
    · obtain ⟨u, hu, hou, hxu⟩ := hexp _ _ hx hox
      exact hno u (by rw [hR]; exact ⟨hu, hou⟩) hxu
  · rintro ⟨ρ, hc, ⟨es1, hx1⟩, ⟨es2, hx2⟩⟩
    obtain ⟨w, hw⟩ := ρ.hasCur
    rw [hc] at hw
    exact hno w (hx1.sub _ _ hw) (ht _ _ (hx2.sub _ _ hw)).2

/-- The same with reachability by the transition system of Sections 2–3. -/
theorem conflicting_outputs_reach {B B' : CommitmentBasis sp} {σ σ' t : State sp}
    {o x : O}
    (_h1 : SysStep B σ (.output o) σ') (hno : ∀ w, σ'.R σ.cur w → ¬ x ≼ w)
    (h2 : SysStep B' σ (.output x) t) :
    ¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧ Reach σ' ρ ∧ Reach t ρ := by
  obtain ⟨_, _, ht, _⟩ := containment h2
  rintro ⟨ρ, hc, h1r, h2r⟩
  obtain ⟨w, hw⟩ := ρ.hasCur
  rw [hc] at hw
  exact hno w (reach_sub h1r _ _ hw) (ht _ _ (reach_sub h2r _ _ hw)).2

end

end CC
