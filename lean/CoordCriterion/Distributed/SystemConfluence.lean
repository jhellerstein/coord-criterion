import CoordCriterion.Appendix.DeploymentSystems
import CoordCriterion.CAP.Model
import CoordCriterion.Figures

/-!
# System confluence (Prop. `prop:system-confluence`, Section 4.3)

A run under a basis and its canonical run (Lemma `lem:canonical-equivalent`)
accept the same inputs and emit the same outputs.  Input and output events
remove the same rows from both tables, so the system's table is the canonical
table minus the rows that the system's own commitment events removed
(`table_decomp`).  Confluence of runs under any bases, by continuations that
may apply any commitments, is the Survivor test for those tables
(`sysConfluentAt_iff`): some row at `k` survives in every final table.  The
backward direction reaches the state `single k u` whose rows are `(k,u)` and
its equivalents (just `(k,u)` for an antisymmetric output order), by
`input(k)`, `output(u)`, and the commitment `keepOnly k u` that removes every
other row.  Since orders are preorders, this uses that run states are
`EqClosed`: a commitment never separates equivalent outputs at one input.

* `Removed`             — a commitment event of the run removed the row.
* `table_decomp`        — `R = R̂ \ Δ`.
* `SysConfluentAt`, `sysConfluentAt_iff` — the Survivor test for runs under bases.
* `system_confluence`   — Prop. `prop:system-confluence` (1)–(2).
* `confluentCut_iff`, `cut_confluence` — the participant runs at a consistent
  cut (continuations as in `CAP.ConfluentCut`).
* `own_iff`, `own_row`  — the system's own continuations.
* `commitment_conflict_of_system_confluence` — Prop. `prop:commitment-conflict`
  as the two-run case.
* `registrar_delta`     — the registrar's `Δ` is the rows with a late ballot.
* `registrar_silent`    — the registrar with a strategy that never announces a
  winner after `ab·`: no commitment event, so `Δ` is empty, the row `(aba, a)`
  stays in its table, and the Survivor test passes with a canonical run that
  accepts `aba` and emits `a`.
-/

namespace CC
namespace Dist

open Classical

variable {I O : Type} [PO I] [PO O] {sp : Spec I O}

/-! ### The rows removed by a run's commitment events -/

/-- `Removed B σ es k u`: some commitment event of the execution `es` from `σ`
under `B` removes the row `(k,u)` (it is present before the event and absent
after it). -/
inductive Removed (B : CommitmentBasis sp) : State sp → List (SEvent sp) → I → O → Prop where
  | here {σ τ : State sp} {γ : List (Commitment sp)} {es : List (SEvent sp)} {k : I} {u : O} :
      SysStep B σ (.commitment γ) τ → σ.R k u → ¬ τ.R k u →
      Removed B σ (.commitment γ :: es) k u
  | later {σ τ : State sp} {e : SEvent sp} {es : List (SEvent sp)} {k : I} {u : O} :
      SysStep B σ e τ → Removed B τ es k u → Removed B σ (e :: es) k u

theorem removed_cons_iff {B : CommitmentBasis sp} {σ τ : State sp} {e : SEvent sp}
    {es : List (SEvent sp)} (hs : SysStep B σ e τ) (k : I) (u : O) :
    Removed B σ (e :: es) k u ↔
      ((∃ γ, e = .commitment γ) ∧ σ.R k u ∧ ¬ τ.R k u) ∨ Removed B τ es k u := by
  constructor
  · intro h
    cases h with
    | here hs' h1 h2 =>
      have := SysStep.det hs hs'
      subst this
      exact Or.inl ⟨⟨_, rfl⟩, h1, h2⟩
    | later hs' h' =>
      have := SysStep.det hs hs'
      subst this
      exact Or.inr h'
  · rintro (⟨⟨γ, rfl⟩, h1, h2⟩ | h)
    · exact Removed.here hs h1 h2
    · exact Removed.later hs h

/-- Generalized decomposition: if `σ`'s table is `σ'`'s minus `D`, then after
the run `es` from `σ` and its erasure from `σ'`, the table is the canonical
one minus `D` and the rows removed by commitment events. -/
theorem table_decomp_gen {B : CommitmentBasis sp} {σ ρ : State sp} {es : List (SEvent sp)}
    (h : SysExec B σ es ρ) :
    ∀ (σ' ρ' : State sp) (D : I → O → Prop), (∀ k u, σ.R k u ↔ σ'.R k u ∧ ¬ D k u) →
      Exec σ' (es.filterMap SEvent.erase) ρ' →
      ∀ k u, ρ.R k u ↔ ρ'.R k u ∧ ¬ (D k u ∨ Removed B σ es k u) := by
  induction h with
  | nil σ =>
    intro σ' ρ' D hD hx k u
    cases hx
    rw [hD k u]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h.elim h2 (fun h' => by cases h')⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 (Or.inl h)⟩
  | @cons σ τ ρ e es hs hr ih =>
    intro σ' ρ' D hD hx k u
    cases e with
    | input j =>
      cases hx with
      | cons hs' hr' =>
        rename_i τ'
        cases hs with
        | input hst =>
          obtain ⟨_, hc, hR⟩ := CAP.step_input_inv hst
          obtain ⟨_, hc', hR'⟩ := CAP.step_input_inv hs'
          have hD' : ∀ k u, τ.R k u ↔ τ'.R k u ∧ ¬ D k u := by
            intro k u
            rw [hR, hR']
            simp only [inputTable]
            rw [hD k u]
            constructor
            · rintro ⟨⟨a, b⟩, c⟩; exact ⟨⟨a, c⟩, b⟩
            · rintro ⟨⟨a, c⟩, b⟩; exact ⟨⟨a, b⟩, c⟩
          rw [ih τ' ρ' D hD' hr' k u, removed_cons_iff (SysStep.input hst) k u]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨h1, ?_⟩
            rintro (h | (⟨⟨γ, hγ⟩, _⟩ | h))
            · exact h2 (Or.inl h)
            · cases hγ
            · exact h2 (Or.inr h)
          · rintro ⟨h1, h2⟩
            exact ⟨h1, fun h => h.elim (fun h => h2 (Or.inl h)) (fun h => h2 (Or.inr (Or.inr h)))⟩
    | output o =>
      cases hx with
      | cons hs' hr' =>
        rename_i τ'
        cases hs with
        | output hst hb =>
          obtain ⟨_, _, hR⟩ := step_output_iff.1 hst
          obtain ⟨_, _, hR'⟩ := step_output_iff.1 hs'
          have hD' : ∀ k u, τ.R k u ↔ τ'.R k u ∧ ¬ D k u := by
            intro k u
            rw [hR, hR']
            simp only [outputTable]
            rw [hD k u]
            constructor
            · rintro ⟨⟨a, b⟩, c⟩; exact ⟨⟨a, c⟩, b⟩
            · rintro ⟨⟨a, c⟩, b⟩; exact ⟨⟨a, b⟩, c⟩
          rw [ih τ' ρ' D hD' hr' k u, removed_cons_iff (SysStep.output hst hb) k u]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨h1, ?_⟩
            rintro (h | (⟨⟨γ, hγ⟩, _⟩ | h))
            · exact h2 (Or.inl h)
            · cases hγ
            · exact h2 (Or.inr h)
          · rintro ⟨h1, h2⟩
            exact ⟨h1, fun h => h.elim (fun h => h2 (Or.inl h)) (fun h => h2 (Or.inr (Or.inr h)))⟩
    | commitment γ =>
      have hx' : Exec σ' (es.filterMap SEvent.erase) ρ' := by
        simpa [List.filterMap_cons, SEvent.erase] using hx
      let D' : I → O → Prop := fun k u => D k u ∨ (σ.R k u ∧ ¬ τ.R k u)
      have hD' : ∀ k u, τ.R k u ↔ σ'.R k u ∧ ¬ D' k u := by
        intro k u
        constructor
        · intro h
          have h0 := (hD k u).1 (hs.sub k u h)
          exact ⟨h0.1, fun h' => h'.elim h0.2 (fun h'' => h''.2 h)⟩
        · rintro ⟨h1, h2⟩
          refine Classical.byContradiction fun hn => ?_
          have h0 : σ.R k u := (hD k u).2 ⟨h1, fun h => h2 (Or.inl h)⟩
          exact h2 (Or.inr ⟨h0, hn⟩)
      rw [ih σ' ρ' D' hD' hx' k u, removed_cons_iff hs k u]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rintro (h | (⟨_, h3, h4⟩ | h))
        · exact h2 (Or.inl (Or.inl h))
        · exact h2 (Or.inl (Or.inr ⟨h3, h4⟩))
        · exact h2 (Or.inr h)
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rintro ((h | ⟨h3, h4⟩) | h)
        · exact h2 (Or.inl h)
        · exact h2 (Or.inr (Or.inl ⟨⟨γ, rfl⟩, h3, h4⟩))
        · exact h2 (Or.inr (Or.inr h))

/-- **Prop. `prop:system-confluence` (1).**  A run under a basis from `σ`, and
the canonical run of its erasure from `σ`: the system's table is the canonical
table minus the rows that one of the run's commitment events removed. -/
theorem table_decomp {B : CommitmentBasis sp} {σ ρ ρh : State sp} {es : List (SEvent sp)}
    (h : SysExec B σ es ρ) (hc : Exec σ (es.filterMap SEvent.erase) ρh) :
    ∀ k u, ρ.R k u ↔ ρh.R k u ∧ ¬ Removed B σ es k u := by
  intro k u
  rw [table_decomp_gen h σ ρh (fun _ _ => False) (fun k u => ⟨fun h => ⟨h, id⟩, fun h => h.1⟩)
    hc k u]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (Or.inr h)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h.elim id h2⟩

/-! ### Rows closed under equivalent outputs

Orders are preorders, so two outputs may each extend the other.  A commitment
cannot remove a row `(k,x)` while keeping a row `(k,w)` with `x ≼ w`; so in
every state reached from a canonical state, the rows at each input are closed
under equivalent permitted outputs (`EqClosed`).  For an antisymmetric output
order this holds of every state (`eqClosed_of_antisymm`). -/

/-- The rows at each input are closed under equivalent permitted outputs. -/
def EqClosed (σ : State sp) : Prop :=
  ∀ k x y, σ.R k x → sp.P k y → x ≼ y → y ≼ x → σ.R k y

theorem eqClosed_of_antisymm [PO.Antisymm O] (σ : State sp) : EqClosed σ :=
  fun _ _ _ hx _ h1 h2 => PO.antisymm h1 h2 ▸ hx

theorem canon_eqClosed (i : I) : EqClosed (canon sp i) :=
  fun _ _ _ hx hy _ _ => ⟨hy, hx.2⟩

theorem step_eqClosed {σ τ : State sp} {e : Event I O} (h : Step σ e τ) (hσ : EqClosed σ) :
    EqClosed τ := by
  cases h with
  | input _ _ _ _ hR =>
    intro k x y hx hy h1 h2
    rw [hR] at hx ⊢
    exact ⟨hσ k x y hx.1 hy h1 h2, hx.2⟩
  | output _ _ _ _ hR =>
    intro k x y hx hy h1 h2
    rw [hR] at hx ⊢
    exact ⟨hσ k x y hx.1 hy h1 h2, PO.trans hx.2 h1⟩

theorem commitment_eqClosed (c : Commitment sp) {σ τ : State sp} (h : c.app σ = some τ)
    (hσ : EqClosed σ) : EqClosed τ := by
  intro k x y hx hy h1 h2
  exact Classical.byContradiction fun hn =>
    c.unsubsumed σ τ h k y x (hσ k x y (c.sub σ τ h k x hx) hy h1 h2) hn hx h2

theorem applySeq_eqClosed {γ : List (Commitment sp)} {σ τ : State sp} (h : ApplySeq γ σ τ)
    (hσ : EqClosed σ) : EqClosed τ := by
  induction h with
  | nil => exact hσ
  | cons ha _ ih => exact ih (commitment_eqClosed _ ha hσ)

theorem sysStep_eqClosed {B : CommitmentBasis sp} {σ τ : State sp} {e : SEvent sp}
    (h : SysStep B σ e τ) (hσ : EqClosed σ) : EqClosed τ := by
  cases h with
  | input hs => exact step_eqClosed hs hσ
  | output hs _ => exact step_eqClosed hs hσ
  | commitment _ _ ha => exact applySeq_eqClosed ha hσ

theorem sysExec_eqClosed {B : CommitmentBasis sp} {σ τ : State sp} {es : List (SEvent sp)}
    (h : SysExec B σ es τ) (hσ : EqClosed σ) : EqClosed τ := by
  induction h with
  | nil => exact hσ
  | cons hs _ ih => exact ih (sysStep_eqClosed hs hσ)

/-- Every state of a run under a basis has `EqClosed` rows. -/
theorem sysExec_eqClosed_canon {B : CommitmentBasis sp} {i : I} {τ : State sp}
    {es : List (SEvent sp)} (h : SysExec B (canon sp i) es τ) : EqClosed τ :=
  sysExec_eqClosed h (canon_eqClosed i)

/-! ### The state whose only rows are `(k,u)` and its equivalents -/

/-- The state at `k` whose rows are the permitted `(k,x)` with `x` equivalent
to `u`.  For an antisymmetric output order this is `(k, {(k,u)})`
(`single_R_iff`). -/
def single (k : I) (u : O) (hu : sp.P k u) : State sp where
  cur := k
  R := fun k' x => k' = k ∧ sp.P k x ∧ u ≼ x ∧ x ≼ u
  sub := fun _ _ h => by rw [h.1]; exact h.2.1
  hasCur := ⟨u, rfl, hu, PO.refl u, PO.refl u⟩
  above := fun _ _ h => by rw [h.1]; exact PO.refl k

theorem single_R_iff [PO.Antisymm O] {k : I} {u : O} (hu : sp.P k u) (k' : I) (x : O) :
    (single k u hu).R k' x ↔ k' = k ∧ x = u := by
  constructor
  · rintro ⟨h1, _, h3, h4⟩; exact ⟨h1, PO.antisymm h4 h3⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, hu, PO.refl _, PO.refl _⟩

/-- The domain of `keepOnly k u`: current input `k`, the row `(k,u)` and every
permitted equivalent of it, no row at `k` below `u` other than equivalents of
`u`, and some row outside `single k u`. -/
def KeepCond (k : I) (u : O) (hu : sp.P k u) (σ : State sp) : Prop :=
  σ.cur = k ∧ σ.R k u ∧ (∀ x, σ.R k x → x ≼ u → u ≼ x) ∧
    (∀ x, sp.P k x → u ≼ x → x ≼ u → σ.R k x) ∧ ∃ k' x, σ.R k' x ∧ ¬ (single k u hu).R k' x

/-- The commitment that keeps only the rows of `single k u` (the row `(k,u)`
and its equivalents).  It is defined on `KeepCond k u`. -/
noncomputable def keepOnly (k : I) (u : O) (hu : sp.P k u) : Commitment sp where
  app σ := if _h : KeepCond k u hu σ then some (single k u hu) else none
  cur_eq σ τ h := by
    by_cases hc : KeepCond k u hu σ
    · rw [dite_eq_left_of_eq_true (eq_true hc)] at h; cases h; exact hc.1.symm
    · rw [dite_eq_right_of_eq_false (eq_false hc)] at h; cases h
  sub σ τ h := by
    by_cases hc : KeepCond k u hu σ
    · rw [dite_eq_left_of_eq_true (eq_true hc)] at h; cases h
      rintro k' x ⟨rfl, hx, h1, h2⟩
      exact hc.2.2.2.1 x hx h1 h2
    · rw [dite_eq_right_of_eq_false (eq_false hc)] at h; cases h
  removes σ τ h := by
    by_cases hc : KeepCond k u hu σ
    · rw [dite_eq_left_of_eq_true (eq_true hc)] at h; cases h
      exact hc.2.2.2.2
    · rw [dite_eq_right_of_eq_false (eq_false hc)] at h; cases h
  unsubsumed σ τ h := by
    by_cases hc : KeepCond k u hu σ
    · rw [dite_eq_left_of_eq_true (eq_true hc)] at h; cases h
      rintro k' x w hx hnx ⟨rfl, _, hw1, hw2⟩ hxw
      have hxu : x ≼ u := PO.trans hxw hw2
      exact hnx ⟨rfl, σ.sub _ _ hx, hc.2.2.1 x hx hxu, hxu⟩
    · rw [dite_eq_right_of_eq_false (eq_false hc)] at h; cases h

/-- After `input(k)` and `output(u)` from an `EqClosed` state `σ` below `k`
with the row `(k,u)`: either `keepOnly k u` applies and yields `single k u`, or
the state already is `single k u`. -/
theorem after_input_output {σ : State sp} {k : I} {u : O} (hu : sp.P k u)
    (hcl : EqClosed σ) (hku : σ.R k u) (τ2 : State sp) (hc : τ2.cur = k)
    (hτ2 : ∀ k' x, τ2.R k' x ↔ (σ.R k' x ∧ k ≼ k') ∧ u ≼ x) :
    (keepOnly k u hu).app τ2 = some (single k u hu) ∨ τ2 = single k u hu := by
  by_cases hrest : ∃ k' x, τ2.R k' x ∧ ¬ (single k u hu).R k' x
  · left
    have hcond : KeepCond k u hu τ2 :=
      ⟨hc, (hτ2 k u).2 ⟨⟨hku, PO.refl k⟩, PO.refl u⟩,
        fun x hx _ => ((hτ2 k x).1 hx).2,
        fun x hx h1 h2 => (hτ2 k x).2 ⟨⟨hcl k u x hku hx h1 h2, PO.refl k⟩, h1⟩, hrest⟩
    exact dite_eq_left_of_eq_true (eq_true hcond)
  · right
    refine State.ext' hc ?_
    funext k' x
    apply propext
    constructor
    · intro h
      exact Classical.byContradiction fun hn => hrest ⟨k', x, h, hn⟩
    · rintro ⟨rfl, hx, h1, h2⟩
      exact (hτ2 k' x).2 ⟨⟨hcl k' u x hku hx h1 h2, PO.refl k'⟩, h1⟩

/-- From any `EqClosed` state with current input below `k` and the row
`(k,u)`, `input(k)`, `output(u)`, and, if other rows remain, the commitment
event `apply(keepOnly k u)` reach `single k u`. -/
theorem reach_single {σ : State sp} {k : I} {u : O} (hu : sp.P k u) (hcl : EqClosed σ)
    (_hk : σ.cur ≼ k) (hku : σ.R k u) :
    ∃ es : List (SEvent sp), SysExec (fun _ => True) σ es (single k u hu) := by
  let τ1 : State sp :=
    { cur := k
      R := inputTable σ k
      sub := fun k' x h => σ.sub k' x h.1
      hasCur := ⟨u, hku, PO.refl k⟩
      above := fun _ _ h => h.2 }
  have s1 : Step σ (.input k) τ1 := Step.input σ τ1 k ⟨u, hku⟩ rfl rfl
  have ho : τ1.R τ1.cur u := ⟨hku, PO.refl k⟩
  let τ2 := outState τ1 u ho
  have s2 : Step τ1 (.output u) τ2 := step_output_outState ho
  have e12 : SysExec (fun _ => True) σ [.input k, .output u] τ2 :=
    .cons (.input s1) (.cons (.output s2 (Or.inr trivial)) (.nil _))
  rcases after_input_output hu hcl hku τ2 rfl (fun _ _ => Iff.rfl) with happ | heq
  · exact ⟨_, SysExec.append e12 (.cons (.commitment (fun _ _ => trivial) (List.cons_ne_nil _ _)
      (.cons happ (.nil _))) (.nil _))⟩
  · exact ⟨_, heq ▸ e12⟩

/-! ### The Survivor test for runs under bases -/

/-- States `fam` can be continued, by events that may apply any commitments, to
a common state with current input `k`. -/
def SysConfluentAt (fam : List (State sp)) (k : I) : Prop :=
  ∃ τ : State sp, τ.cur = k ∧ ∀ σ ∈ fam, ∃ (B : CommitmentBasis sp) (es : List (SEvent sp)),
    SysExec B σ es τ

/-- The forward direction of `sysConfluentAt_iff`, for any order: a common
state at `k` leaves a row at `k` that survives in every member. -/
theorem SysConfluentAt.survivor {fam : List (State sp)} {k : I} (h : SysConfluentAt fam k) :
    ∃ u, sp.P k u ∧ ∀ σ ∈ fam, σ.R k u := by
  obtain ⟨τ, hτ, hall⟩ := h
  obtain ⟨u, hu⟩ := τ.hasCur
  rw [hτ] at hu
  refine ⟨u, τ.sub _ _ hu, fun σ hσ => ?_⟩
  obtain ⟨B, es, hx⟩ := hall σ hσ
  exact hx.sub k u hu

/-- **Survivor test for runs under bases.**  `EqClosed` states (every state of
a run under a basis, `sysExec_eqClosed_canon`; every state at all for an
antisymmetric output order, `eqClosed_of_antisymm`) with current inputs below
`k` are confluent at `k`, by continuations that may apply any commitments, iff
some row at `k` survives in every one of them. -/
theorem sysConfluentAt_iff (fam : List (State sp)) (k : I) (hk : ∀ σ ∈ fam, σ.cur ≼ k)
    (hcl : ∀ σ ∈ fam, EqClosed σ) :
    SysConfluentAt fam k ↔ ∃ u, sp.P k u ∧ ∀ σ ∈ fam, σ.R k u := by
  constructor
  · exact SysConfluentAt.survivor
  · rintro ⟨u, hu, hall⟩
    refine ⟨single k u hu, rfl, fun σ hσ => ?_⟩
    obtain ⟨es, hx⟩ := reach_single hu (hcl σ hσ) (hk σ hσ) (hall σ hσ)
    exact ⟨_, es, hx⟩

/-- **Prop. `prop:system-confluence`.**  Runs `ρ r` under bases `B r` from
`σ_P(i r)`, with canonical runs (their erasures) ending at `ρh r`: (0) the
canonical run has the same current input; (1) `R_r = R̂_r \ Δ(ρ_r)`; (2) at a
common input extension `k`, the runs are confluent, by continuations that may
apply any commitments, iff some row at `k` lies in every `R̂_r` and in no
`Δ(ρ_r)`. -/
theorem system_confluence {m : Nat} (B : Fin m → CommitmentBasis sp) (i : Fin m → I)
    (es : Fin m → List (SEvent sp)) (ρ ρh : Fin m → State sp)
    (hrun : ∀ r, SysExec (B r) (canon sp (i r)) (es r) (ρ r))
    (hcan : ∀ r, Exec (canon sp (i r)) ((es r).filterMap SEvent.erase) (ρh r)) :
    (∀ r, (ρh r).cur = (ρ r).cur) ∧
    (∀ r k u, (ρ r).R k u ↔ (ρh r).R k u ∧ ¬ Removed (B r) (canon sp (i r)) (es r) k u) ∧
    ∀ k, (∀ r, (ρ r).cur ≼ k) →
      ((∃ τ : State sp, τ.cur = k ∧ ∀ r, ∃ (B' : CommitmentBasis sp) (es' : List (SEvent sp)),
          SysExec B' (ρ r) es' τ) ↔
        ∃ u, sp.P k u ∧ ∀ r, (ρh r).R k u ∧ ¬ Removed (B r) (canon sp (i r)) (es r) k u) := by
  have hdec : ∀ r k u, (ρ r).R k u ↔ (ρh r).R k u ∧ ¬ Removed (B r) (canon sp (i r)) (es r) k u :=
    fun r => table_decomp (hrun r) (hcan r)
  refine ⟨fun r => ?_, hdec, fun k hk => ?_⟩
  · obtain ⟨_, ρ', _, _, hx, hc, _⟩ := canonical_equivalent (hrun r)
    rw [exec_det (hcan r) hx]; exact hc
  · have h := sysConfluentAt_iff (List.ofFn ρ) k (by
      intro σ hσ; obtain ⟨r, rfl⟩ := List.mem_ofFn.1 hσ; exact hk r) (by
      intro σ hσ; obtain ⟨r, rfl⟩ := List.mem_ofFn.1 hσ; exact sysExec_eqClosed_canon (hrun r))
    constructor
    · rintro ⟨τ, hτ, hall⟩
      obtain ⟨u, hu, hall'⟩ := h.1 ⟨τ, hτ, fun σ hσ => by
        obtain ⟨r, rfl⟩ := List.mem_ofFn.1 hσ; exact hall r⟩
      exact ⟨u, hu, fun r => (hdec r k u).1 (hall' _ (List.mem_ofFn.2 ⟨r, rfl⟩))⟩
    · rintro ⟨u, hu, hall⟩
      obtain ⟨τ, hτ, hall'⟩ := h.2 ⟨u, hu, fun σ hσ => by
        obtain ⟨r, rfl⟩ := List.mem_ofFn.1 hσ; exact (hdec r k u).2 (hall r)⟩
      exact ⟨τ, hτ, fun r => hall' _ (List.mem_ofFn.2 ⟨r, rfl⟩)⟩

/-! ### Participant runs at a consistent cut -/

section cut

variable {D : Type} {n : Nat}

theorem capApplySeq_eqClosed : ∀ (γ : List (CAP.Commitment sp)) (σ τ : State sp),
    CAP.applySeq σ γ = some τ → EqClosed σ → EqClosed τ
  | [], σ, τ, h, hσ => by simp [CAP.applySeq] at h; subst h; exact hσ
  | c :: cs, σ, τ, h, hσ => by
    simp only [CAP.applySeq] at h
    split at h
    · rename_i τ1 h1
      exact capApplySeq_eqClosed cs τ1 τ h (commitment_eqClosed (ofCAP c) h1 hσ)
    · cases h

theorem lrun_eqClosed {σ τ : State sp} {l : List (CAP.LEv sp D n)} (h : CAP.LRun σ l τ)
    (hσ : EqClosed σ) : EqClosed τ := by
  induction h with
  | nil => exact hσ
  | inp hs _ ih => exact ih (step_eqClosed hs hσ)
  | out hs _ ih => exact ih (step_eqClosed hs hσ)
  | commitment _ ha _ ih => exact ih (capApplySeq_eqClosed _ _ _ ha hσ)
  | send _ ih => exact ih hσ
  | recv _ ih => exact ih hσ

/-- `CAP.LRun` form of `reach_single`, with no receive. -/
theorem lrun_single {σ : State sp} {k : I} {u : O} (hu : sp.P k u) (hcl : EqClosed σ)
    (_hk : σ.cur ≼ k) (hku : σ.R k u) :
    ∃ l : List (CAP.LEv sp D n), CAP.LRun σ l (single k u hu) ∧ ∀ q k j d, CAP.LEv.recv q k j d ∉ l := by
  let τ1 : State sp :=
    { cur := k
      R := inputTable σ k
      sub := fun k' x h => σ.sub k' x h.1
      hasCur := ⟨u, hku, PO.refl k⟩
      above := fun _ _ h => h.2 }
  have s1 : Step σ (.input k) τ1 := Step.input σ τ1 k ⟨u, hku⟩ rfl rfl
  have ho : τ1.R τ1.cur u := ⟨hku, PO.refl k⟩
  let τ2 := outState τ1 u ho
  have s2 : Step τ1 (.output u) τ2 := step_output_outState ho
  rcases after_input_output hu hcl hku τ2 rfl (fun _ _ => Iff.rfl) with happ | heq
  · have hc : CAP.applySeq τ2 [toCAP (keepOnly k u hu)] = some (single k u hu) := by
      show (match (keepOnly k u hu).app τ2 with
        | some τ => CAP.applySeq τ [] | none => none) = _
      rw [happ]; rfl
    refine ⟨[.inp k, .out u, .commitment [toCAP (keepOnly k u hu)]],
      .inp s1 (.out s2 (.commitment (List.cons_ne_nil _ _) hc (.nil _))), ?_⟩
    intro q k j d h
    simp at h
  · refine ⟨[.inp k, .out u], heq ▸ .inp s1 (.out s2 (.nil _)), ?_⟩
    intro q k j d h
    simp at h

/-- **Prop. `prop:system-confluence` for the participant runs at a consistent
cut.**  A consistent cut whose participants' current inputs lie below `k` is
confluent at `k` (some well-formed continuation, whose events may apply any
commitments, brings every participant to one state at `k`) iff some row at `k`
survives in every participant's table. -/
theorem confluentCut_iff {init : Fin n → I} {H : CAP.History sp D n} {c : Fin n → Nat}
    (hwf : CAP.WF init H) (hcut : CAP.IsCut H c) {k : I}
    (hk : ∀ p σ, CAP.LRun (canon sp (init p)) ((H p).take (c p)) σ → σ.cur ≼ k) :
    CAP.ConfluentCut init H c k ↔
      ∃ u, sp.P k u ∧ ∀ p σ, CAP.LRun (canon sp (init p)) ((H p).take (c p)) σ → σ.R k u := by
  constructor
  · rintro ⟨H', ext, τ, hext, _, hτ, hrun⟩
    obtain ⟨u, hu⟩ := τ.hasCur
    rw [hτ] at hu
    refine ⟨u, τ.sub _ _ hu, fun p σ hσ => ?_⟩
    have h1 := hrun p
    rw [hext p] at h1
    obtain ⟨σ', h2, h3⟩ := CAP.lrun_append.1 h1
    rw [CAP.lrun_det hσ h2]
    exact (CAP.lrun_mono h3).2 k u hu
  · rintro ⟨u, hu, hall⟩
    have hX : ∀ p, ∃ σ : State sp, CAP.LRun (canon sp (init p)) ((H p).take (c p)) σ := by
      intro p
      obtain ⟨τ, hτ⟩ := hwf.runs p
      exact CAP.lrun_take hτ (c p)
    let σs := fun p => Classical.choose (hX p)
    have hσs : ∀ p, CAP.LRun (canon sp (init p)) ((H p).take (c p)) (σs p) :=
      fun p => Classical.choose_spec (hX p)
    have hL : ∀ p, ∃ l : List (CAP.LEv sp D n), CAP.LRun (σs p) l (single k u hu) ∧
        ∀ q k j d, CAP.LEv.recv q k j d ∉ l :=
      fun p => lrun_single hu (lrun_eqClosed (hσs p) (canon_eqClosed _)) (hk p _ (hσs p))
        (hall p _ (hσs p))
    let ext := fun p => Classical.choose (hL p)
    have hext' : ∀ p, _ := fun p => Classical.choose_spec (hL p)
    have hext : CAP.Extends H c (fun q => (H q).take (c q) ++ ext q) ext := fun _ => rfl
    have hrun : ∀ p, CAP.LRun (canon sp (init p)) ((H p).take (c p) ++ ext p) (single k u hu) :=
      fun p => CAP.lrun_append.2 ⟨σs p, hσs p, (hext' p).1⟩
    exact ⟨_, ext, single k u hu, hext,
      CAP.wf_extend hwf hcut hext (fun p => (hext' p).2) (fun p => ⟨_, hrun p⟩), rfl, hrun⟩

/-- **The participant-run form with `Δ`.**  Each participant run up to the cut
is a run under the full basis (`Deploy.toS`); its canonical run is the
erasure.  The cut is confluent at `k` iff some row at `k` lies in every
participant's canonical table and was removed by no commitment event of any
participant run. -/
theorem cut_confluence {init : Fin n → I} {H : CAP.History sp D n} {c : Fin n → Nat}
    (hwf : CAP.WF init H) (hcut : CAP.IsCut H c) {k : I}
    (hk : ∀ p σ, CAP.LRun (canon sp (init p)) ((H p).take (c p)) σ → σ.cur ≼ k)
    (ρh : Fin n → State sp)
    (hcan : ∀ p, Exec (canon sp (init p))
      ((Deploy.toS ((H p).take (c p))).filterMap SEvent.erase) (ρh p)) :
    CAP.ConfluentCut init H c k ↔
      ∃ u, sp.P k u ∧ ∀ p, (ρh p).R k u ∧
        ¬ Removed (fun _ => True) (canon sp (init p)) (Deploy.toS ((H p).take (c p))) k u := by
  rw [confluentCut_iff hwf hcut hk]
  have hX : ∀ p, ∃ σ : State sp, CAP.LRun (canon sp (init p)) ((H p).take (c p)) σ := by
    intro p
    obtain ⟨τ, hτ⟩ := hwf.runs p
    exact CAP.lrun_take hτ (c p)
  constructor
  · rintro ⟨u, hu, hall⟩
    refine ⟨u, hu, fun p => ?_⟩
    obtain ⟨σ, hσ⟩ := hX p
    exact (table_decomp (Deploy.lrun_sysExec hσ) (hcan p) k u).1 (hall p σ hσ)
  · rintro ⟨u, hu, hall⟩
    exact ⟨u, hu, fun p σ hσ => (table_decomp (Deploy.lrun_sysExec hσ) (hcan p) k u).2 (hall p)⟩

end cut

/-! ### The system's own continuations -/

/-- A continuation under any basis that ends with `output(u)` at input `k`
needs the row `(k,u)` in the starting table. -/
theorem own_row {B : CommitmentBasis sp} {σ τ : State sp} {es : List (SEvent sp)} {k : I} {u : O}
    (h : SysExec B σ (es ++ [.output u]) τ) (hk : τ.cur = k) : σ.R k u := by
  obtain ⟨α, h1, h2⟩ := SysExec.append_inv h
  cases h2 with
  | cons hs hr =>
    cases hr
    cases hs with
    | output hst _ =>
      obtain ⟨ho, hc, _⟩ := step_output_iff.1 hst
      rw [← hc, hk] at ho
      exact h1.sub k u ho

/-- **The system's own continuations.**  `Can σ u`: the system can continue
from `σ` to input `k` and emit `u` there (any such continuation is a run
under some basis ending with `output(u)` at `k`).  If, from each final state,
the system can do so for every output whose row at `k` remains in its table,
then it can bring every run to input `k` with one common output exactly when
some row at `k` survives in every table. -/
theorem own_iff (fam : List (State sp)) (k : I) (Can : State sp → O → Prop)
    (hsound : ∀ σ u, Can σ u → ∃ (B : CommitmentBasis sp) (es : List (SEvent sp)) (τ : State sp),
      SysExec B σ (es ++ [.output u]) τ ∧ τ.cur = k)
    (hcomplete : ∀ σ ∈ fam, ∀ u, σ.R k u → Can σ u) :
    (∃ u, ∀ σ ∈ fam, Can σ u) ↔ ∃ u, ∀ σ ∈ fam, σ.R k u := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, fun σ hσ => ?_⟩
    obtain ⟨B, es, τ, hx, hτ⟩ := hsound σ u (hu σ hσ)
    exact own_row hx hτ
  · rintro ⟨u, hu⟩
    exact ⟨u, fun σ hσ => hcomplete σ hσ u (hu σ hσ)⟩

/-- A row that survives in a run's table under any basis extends every output
the run emitted: the common output of `own_iff` extends everything the runs
emitted. -/
theorem surviving_row_extends {B : CommitmentBasis sp} {i : I} {es : List (SEvent sp)}
    {ρ : State sp} (h : SysExec B (canon sp i) es ρ) {k : I} {u : O} (hku : ρ.R k u) :
    ∀ o ∈ outs (es.filterMap SEvent.erase), o ≼ u := by
  obtain ⟨_, ρ', _, _, hx, _, hsub⟩ := canonical_equivalent h
  exact ((run_residual hx k u).1 (hsub k u hku)).2.2

/-! ### Prop. `prop:commitment-conflict` as the two-run case -/

/-- Prop. `prop:commitment-conflict` from Prop. `prop:system-confluence`: a run
whose table lies within the state left by a commitment that removed `(k,x)`,
and any run ending with `input(k)` and `output(x)`, are not confluent at `k`
by continuations that may apply any commitments.  No row at `k` survives in
both: every row of the second at `k` extends `x`, and the commitment left no
such row. -/
theorem commitment_conflict_of_system_confluence {c : Commitment sp} {σ σc σ' τ0 τ : State sp}
    {k : I} {x : O} {B' : CommitmentBasis sp}
    (happ : c.app σ = some σc) (hx : σ.R k x) (hnx : ¬ σc.R k x)
    (hsub : ∀ k w, σ'.R k w → σc.R k w) (_hk : σ'.cur ≼ k)
    (h2 : SysExec B' τ0 [.input k, .output x] τ) :
    ¬ SysConfluentAt [σ', τ] k := by
  have hτk : ∀ w, τ.R k w → x ≼ w := by
    intro w hw
    cases h2 with
    | cons _ h3 =>
      cases h3 with
      | cons s2 h4 =>
        cases h4
        cases s2 with
        | output hst _ =>
          obtain ⟨_, _, hR⟩ := step_output_iff.1 hst
          rw [hR] at hw
          exact hw.2
  intro hconf
  obtain ⟨w, _, hall⟩ := hconf.survivor
  have h1 := hall σ' (by simp)
  have h2' := hall τ (by simp)
  exact c.unsubsumed σ σc happ k x w hx hnx (hsub k w h1) (hτk w h2')

/-! ### Examples -/

/-- A run with no commitment event removes no row by commitment: `Δ` is empty. -/
theorem removed_mem {B : CommitmentBasis sp} {σ : State sp} {es : List (SEvent sp)} {k : I} {u : O}
    (h : Removed B σ es k u) : ∃ γ, SEvent.commitment γ ∈ es := by
  induction h with
  | here => exact ⟨_, List.mem_cons_self ..⟩
  | later _ _ ih => obtain ⟨γ, hγ⟩ := ih; exact ⟨γ, List.mem_cons_of_mem _ hγ⟩

/-- The registrar (Fig. `fig:election-frames`(d)): from `σ_P(ab·)` it closes
the polls and emits `⊥`.  Its canonical run emits `⊥`.  The rows of the
canonical table that the commitment event removed are exactly `(aba, a)` and
`(abb, b)`, and its own table has no row at `aba`. -/
theorem registrar_delta (B : CommitmentBasis CALM.elec) (hB : B Figures.closePolls)
    (ρh : State CALM.elec) (hρh : Exec (canon CALM.elec CALM.bab) [.output .bot] ρh) :
    (∀ k o, (ρh.R k o ∧ Removed B (canon CALM.elec CALM.bab)
        [.commitment [Figures.closePolls], .output .bot] k o) ↔
      ((k = CALM.baba ∧ o = .win .a) ∨ (k = Figures.Elec.babb ∧ o = .win .b))) ∧
    ∀ o, ¬ Figures.Elec.panelD.R CALM.baba o := by
  have hd := table_decomp (Figures.Elec.registrar_step B hB) hρh
  have hR : ∀ k o, ρh.R k o ↔ (canon CALM.elec CALM.bab).R k o := by
    cases hρh with
    | cons hs hr =>
      cases hr
      obtain ⟨_, _, h⟩ := step_output_iff.1 hs
      intro k o
      rw [h, Figures.Elec.bot_alone_at_b.2.2]
  refine ⟨fun k o => ?_, fun o h => ?_⟩
  · rw [← Figures.Elec.panelD_struck k o]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hR k o).1 h1, fun hp => ((hd k o).1 hp).2 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(hR k o).2 h1, Classical.byContradiction fun hn => h2 ((hd k o).2 ⟨(hR k o).2 h1, hn⟩)⟩
  · have := ((Figures.Elec.panelD_rows _ _).1 h).1
    exact absurd this (by decide)

/-- The registrar with a silent strategy: from `σ_P(ab·)` it emits `⊥` and
applies no commitment, so `Δ` is empty and its table keeps the row
`(aba, a)`.  A canonical run from the same state accepts `aba` and emits `a`,
and the two states pass the Survivor test at `aba`: a common state is
reachable by continuations that may apply any commitments.  That the
registrar's strategy never announces a winner after `ab·` is the example's
description of the strategy, not a property of the run. -/
theorem registrar_silent :
    ∃ ρ τ : State CALM.elec,
      SysExec (fun _ => True) (canon CALM.elec CALM.bab) [.output .bot] ρ ∧
      (∀ k o, ¬ Removed (fun _ => True) (canon CALM.elec CALM.bab) [.output .bot] k o) ∧
      ρ.R CALM.baba (.win .a) ∧
      Exec (canon CALM.elec CALM.bab) [.input CALM.baba, .output (.win .a)] τ ∧
      SysConfluentAt [ρ, τ] CALM.baba := by
  let σ0 := canon CALM.elec CALM.bab
  have h0 : σ0.R σ0.cur .bot := ⟨CALM.winner_bab.symm, PO.refl _⟩
  have h1 : σ0.R CALM.baba (.win .a) := ⟨CALM.winner_baba.symm, CALM.bab_le_baba⟩
  let ρ := outState σ0 .bot h0
  let τ1 := CALM.inputState σ0 CALM.baba (.win .a) h1
  have h2 : τ1.R τ1.cur (.win .a) := ⟨h1, PO.refl _⟩
  let τ := CALM.outputState τ1 (.win .a) h2
  have hρ : ρ.R CALM.baba (.win .a) := ⟨h1, Or.inl rfl⟩
  have hτ : τ.R CALM.baba (.win .a) := ⟨⟨h1, PO.refl _⟩, PO.refl _⟩
  refine ⟨ρ, τ, .cons (.output (step_output_outState h0) (Or.inr trivial)) (.nil _),
    fun k o h => ?_, hρ,
    .cons (CALM.step_inputState σ0 _ _ h1) (.cons (CALM.step_outputState τ1 _ h2) (.nil _)), ?_⟩
  · obtain ⟨γ, hγ⟩ := removed_mem h
    simp at hγ
  · have hk : ∀ σ ∈ [ρ, τ], σ.cur ≼ CALM.baba := by
      intro σ hσ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
      rcases hσ with rfl | rfl
      · exact CALM.bab_le_baba
      · exact PO.refl _
    refine (sysConfluentAt_iff [ρ, τ] CALM.baba hk fun σ _ => eqClosed_of_antisymm σ).2 ⟨.win .a, CALM.winner_baba.symm, ?_⟩
    intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl
    · exact hρ
    · exact hτ

end Dist
end CC
