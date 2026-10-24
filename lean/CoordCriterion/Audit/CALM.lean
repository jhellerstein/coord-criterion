/-
# Audit A: Functional CALM, Complete CALM, and their deferred proofs

Conformance audit of `sections/functional-calm.tex`, `sections/complete-calm.tex`
and `appendices/proof-machinery.tex` (except `app:iconfluence`).  The main
theorems are already in `Runs`, `FunctionalCALM` and `CompleteCALM`; this file
adds the items those files do not cover, and re-proves the theorems whose
paper proof now takes a different route, so that the route itself is checked:

* event facts used in the text: the target states of input/output events
  exist (`inputState`, `outputState`), events are deterministic
  (`step_det`), `input j; input k` = `input k` (`input_input`), `input i` at
  `(i,R)` is a no-op (`input_self`), determined states stay determined
  (`step_determined`, `reach_determined`);
* the explicit form of the survivor test, "`input(j)` then `output(u)` takes
  every final state to `(j, S[in ⪰ j, out ⪰ u])`" (`survivor_exec`);
* functional remarks: exposability is "`f(j)` refines `o` at every legal `j`"
  (`exposable_iff_refines_all`); a functional output event commits iff it
  seals (`functional_commit_iff_sealed`); failure of monotonicity at
  `i ≼ k` makes `output(f(i))` at `σ_S(i)` seal `k` (`nonmono_seals`);
  RelMono / Lifted Monotonicity / the common-expansion condition are
  functional monotonicity for singleton fibers (`relMono_iff_monoF`,
  `liftedMono_iff_monoF`, `commonExpansion_iff_monoF`); in a consistent
  functional spec `input(j)` alone takes every run to `σ_S(j)`
  (`functional_meet_by_input`);
* the non-carry-over remark: a consistent relational specification with a run
  state that is not canonical (`state_by_input_fails_relationally`);
* **Lemma `lem:reconciliation`** (`reconciliation`), stated over families of
  runs with their event lists; consistency over such families
  (`consistent_iff_runs`);
* **Thm. Complete CALM by the paper's route** through the reconciliation lemma
  (`complete_calm_paper`, `complete_calm_paper_lm`);
* **Prop. exposure boundary by the paper's route** (forward direction via
  consistency and the survivor test, `exposable_of_consistent`, which holds
  at every run state, not only commitment-free ones;
  `exposure_boundary_paper`);
* **Pairs suffice** (`pairs_iff_commonExpansion`, from `CC.Deploy.ce_of_pairs`),
  necessity of the rows at `j` (`rowsAtJ_needed`), and the `k`-set agreement
  example of `app:additional-applications`
  (`KSet.proposal_row`, `KSet.any_k_compatible`, `KSet.not_all_compatible`,
  `KSet.not_commonExpansion`, `KSet.not_liftedMono`,
  `KSet.atomic_k_at_a_time`).
* examples: the election (`elec_monotone`, `elec_consistent`,
  `elecEq_not_monotone`, `elecEq_not_consistent`, `elec_panels_exposable`,
  `elec_panel_b_undetermined`, `elec_panel_c_determined`, `elecEq_bot_seals`,
  `elecEq_bot_single_row`, `elecEq_not_confluent`) and the directed fiber
  `{{a},{b},{a,b,c},{a,b,d},{a,b,c,d}}` (`f5_directed`,
  `f5_common_refinements`, `f5_minimal_incomparable`, `f5_compatible`);
  canonical states are largest and input events move between them
  (`state_le_canon`, `input_canon`).

Not formalized (informal in the paper): the transaction-ordering and
traceroute panels of Fig. `fig:ambiguity-frames`, the registrar seal of
Fig. `fig:election-frames`(d), and the classical query / CRDT readings.
(The figure panels are now checked in `Audit/Remaining.lean`.)
-/
import CoordCriterion.Core
import CoordCriterion.Runs
import CoordCriterion.FunctionalCALM
import CoordCriterion.CompleteCALM
import CoordCriterion.Deployment

namespace CC
namespace AuditA

section Generic
variable {I O : Type} [PO I] [PO O]

/-! ## 1. Events -/

/-- The state after `input j` at `σ`, for a legal `j` (witness row `(j,u)`). -/
def inputState {sp : Spec I O} (σ : State sp) (j : I) (u : O) (h : σ.R j u) : State sp where
  cur := j
  R := inputTable σ j
  sub := fun k x h' => σ.sub k x h'.1
  hasCur := ⟨u, h, PO.refl j⟩
  above := fun _ _ h' => h'.2

/-- The state after `output o` at `σ`, for `o ∈ R(cur)`: the current row
remains, so the event always ends at a state. -/
def outputState {sp : Spec I O} (σ : State sp) (o : O) (h : σ.R σ.cur o) : State sp where
  cur := σ.cur
  R := outputTable σ o
  sub := fun k x h' => σ.sub k x h'.1
  hasCur := ⟨o, h, PO.refl o⟩
  above := fun k x h' => σ.above k x h'.1

theorem step_inputState {sp : Spec I O} (σ : State sp) (j : I) (u : O) (h : σ.R j u) :
    Step σ (.input j) (inputState σ j u h) :=
  Step.input _ _ j ⟨u, h⟩ rfl rfl

theorem step_outputState {sp : Spec I O} (σ : State sp) (o : O) (h : σ.R σ.cur o) :
    Step σ (.output o) (outputState σ o h) :=
  Step.output _ _ o h rfl rfl

/-- The paper's input event requires `j` legal *and* `i ≼ j`; Lean's `Step`
asks only legality, which implies `i ≼ j`. -/
theorem legal_above {sp : Spec I O} (σ : State sp) (j : I) (h : ∃ u, σ.R j u) : σ.cur ≼ j := by
  obtain ⟨u, hu⟩ := h
  exact σ.above _ _ hu

/-- Events are deterministic. -/
theorem step_det {sp : Spec I O} {σ τ τ' : State sp} {e : Event I O}
    (h : Step σ e τ) (h' : Step σ e τ') : τ = τ' := by
  cases h with
  | input _ j _ hc hR =>
    cases h' with
    | input _ _ _ hc' hR' => exact State.ext' (hc.trans hc'.symm) (hR.trans hR'.symm)
  | output _ o _ hc hR =>
    cases h' with
    | output _ _ _ hc' hR' => exact State.ext' (hc.trans hc'.symm) (hR.trans hR'.symm)

/-- "Applying `input(j)` and then `input(k)` has the same effect as applying
`input(k)` directly." -/
theorem input_input {sp : Spec I O} {σ τ ρ : State sp} {j k : I}
    (h1 : Step σ (.input j) τ) (h2 : Step τ (.input k) ρ) : Step σ (.input k) ρ := by
  cases h1 with
  | input _ _ _ hc hR =>
    cases h2 with
    | input _ _ hl2 hc2 hR2 =>
      obtain ⟨u, hu⟩ := hl2
      rw [hR] at hu
      refine Step.input _ _ _ ⟨u, hu.1⟩ hc2 ?_
      rw [hR2]
      funext a b
      apply propext
      simp only [inputTable, hR]
      constructor
      · rintro ⟨⟨h, _⟩, hk⟩; exact ⟨h, hk⟩
      · rintro ⟨h, hk⟩; exact ⟨⟨h, PO.trans hu.2 hk⟩, hk⟩

/-- "`input(i)` at `(i,R)` has no effect." -/
theorem input_self {sp : Spec I O} {σ τ : State sp} (h : Step σ (.input σ.cur) τ) : τ = σ := by
  cases h with
  | input _ _ _ hc hR =>
    refine State.ext' hc ?_
    rw [hR]
    funext a b
    apply propext
    exact ⟨fun h => h.1, fun h => ⟨h, σ.above _ _ h⟩⟩

/-- "The largest state at input `i` ... is the canonical state": every state
with current input `i` has its table inside `S[in ⪰ i]`. -/
theorem state_le_canon {sp : Spec I O} (σ : State sp) :
    ∀ k x, σ.R k x → (canon sp σ.cur).R k x :=
  fun k x h => ⟨σ.sub k x h, σ.above k x h⟩

/-- "Input events alone move between canonical states." -/
theorem input_canon {sp : Spec I O} {i j : I} {τ : State sp}
    (h : Step (canon sp i) (.input j) τ) : τ = canon sp j := by
  cases h with
  | input _ _ hl hc hR =>
    obtain ⟨u, hu⟩ := hl
    refine State.ext' hc ?_
    rw [hR]
    funext a b
    apply propext
    simp only [inputTable, canon]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, PO.trans hu.2 h.2⟩, h.2⟩⟩

/-- Determined state: the upper fiber `out(R)` has exactly one element
(it is nonempty by `hasCur`). -/
def Determined {sp : Spec I O} (σ : State sp) : Prop :=
  ∃ o, ∀ k x, σ.R k x → x = o

theorem determined_upper_fiber {sp : Spec I O} (σ : State sp) :
    Determined σ ↔ ∃ o, (∃ k, σ.R k o) ∧ ∀ k x, σ.R k x → x = o := by
  constructor
  · rintro ⟨o, h⟩
    obtain ⟨x, hx⟩ := σ.hasCur
    have := h _ _ hx
    subst this
    exact ⟨x, ⟨_, hx⟩, h⟩
  · rintro ⟨o, _, h⟩; exact ⟨o, h⟩

/-- "A determined state stays determined." -/
theorem step_determined {sp : Spec I O} {σ τ : State sp} {e : Event I O}
    (hs : Step σ e τ) (hd : Determined σ) : Determined τ := by
  obtain ⟨o, h⟩ := hd
  exact ⟨o, fun k x hx => h k x (step_sub hs k x hx)⟩

theorem reach_determined {sp : Spec I O} {σ τ : State sp}
    (hr : Reach σ τ) (hd : Determined σ) : Determined τ := by
  obtain ⟨o, h⟩ := hd
  exact ⟨o, fun k x hx => h k x (reach_sub hr k x hx)⟩

/-- Executions extend by one step. -/
theorem exec_snoc {sp : Spec I O} {σ τ ρ : State sp} {es : List (Event I O)} {e : Event I O}
    (hx : Exec σ es τ) (hs : Step τ e ρ) : Exec σ (es ++ [e]) ρ := by
  induction hx with
  | nil => exact Exec.cons hs (Exec.nil _)
  | cons h _ ih => exact Exec.cons h (ih hs)

theorem isRun_step {sp : Spec I O} {τ ρ : State sp} {e : Event I O}
    (h : IsRun τ) (hs : Step τ e ρ) : IsRun ρ := by
  obtain ⟨i, es, hx⟩ := h
  exact ⟨i, es ++ [e], exec_snoc hx hs⟩

/-! ## 2. The survivor test, explicit form -/

/-- Prop. `prop:confluence`, second sentence: for a surviving row `(j,u)`,
`input(j)` followed by `output(u)` takes every run state to
`(j, S[in ⪰ j, out ⪰ u])` (`meetState`). -/
theorem survivor_exec {sp : Spec I O} {σ : State sp} (hrun : IsRun σ) {j : I} {u : O}
    (hju : σ.R j u) : Exec σ [.input j, .output u] (meetState sp j u (σ.sub _ _ hju)) := by
  obtain ⟨E, hσ⟩ := hrun.residual
  have hcj : σ.cur ≼ j := σ.above _ _ hju
  let τ1 := inputState σ j u hju
  have s2 : Step τ1 (.output u) (meetState sp j u (σ.sub _ _ hju)) := by
    refine Step.output τ1 _ u ⟨hju, PO.refl j⟩ rfl ?_
    funext k x
    apply propext
    simp only [meetState, outputTable, inputTable, τ1, inputState]
    constructor
    · rintro ⟨hS, hjk, hux⟩
      have hEu : ∀ o ∈ E, o ≼ u := ((hσ j u).1 hju).2.2
      exact ⟨⟨(hσ k x).2 ⟨hS, PO.trans hcj hjk, fun o ho => PO.trans (hEu o ho) hux⟩, hjk⟩, hux⟩
    · rintro ⟨⟨h, hjk⟩, hux⟩
      exact ⟨σ.sub _ _ h, hjk, hux⟩
  exact Exec.cons (step_inputState σ j u hju) (Exec.cons s2 (Exec.nil _))

/-! ## 3. Functional remarks -/

/-- Remark after Def. `def:exposable`: in a functional specification, `o` is
exposable at `(i,R)` iff `f(j)` refines `o` at every legal input `j`. -/
theorem exposable_iff_refines_all {sp : Spec I O} (hf : sp.Functional) (σ : State sp) (o : O) :
    Exposable σ o ↔ ∀ k x, σ.R k x → o ≼ x := by
  constructor
  · intro he k x h
    apply Classical.byContradiction
    intro hn
    obtain ⟨u, hu, hou, _⟩ := he k x h hn
    have : u = x := hf k u x (σ.sub _ _ hu) (σ.sub _ _ h)
    subst this
    exact hn hou
  · intro h k x hx hn
    exact absurd (h k x hx) hn

/-- Def. `def:output-event` vs. Def. `def:lifted-output-event`: in a
functional specification the output event commits (`R' ≠ R`) iff it seals
some row. -/
theorem functional_commit_iff_sealed {sp : Spec I O} (hf : sp.Functional) (σ : State sp) (o : O) :
    outputTable σ o ≠ σ.R ↔ ∃ k x, Sealed σ o k x := by
  constructor
  · intro hne
    apply Classical.byContradiction
    intro hno
    have he : Exposable σ o := (exposable_iff_no_commitment σ o).2
      ⟨fun k x hs => hno ⟨k, x, hs⟩,
       fun k x hr => (functional_retired_rejected_empty hf σ o k x).2 hr⟩
    exact hne ((exposable_iff_functional hf σ o).1 he)
  · rintro ⟨k, x, hs⟩ heq
    have he := (exposable_iff_functional hf σ o).2 heq
    exact ((exposable_iff_no_commitment σ o).1 he).1 k x hs

/-- Paragraph after Prop. `prop:functional-exposure-boundary`: if
monotonicity fails at `i ≼ k`, then at `σ_S(i)` the event `output(f(i))` seals
`k`. -/
theorem nonmono_seals {sp : Spec I O} (hf : sp.Functional) {i k : I} {o u : O}
    (hik : i ≼ k) (_hio : sp.S i o) (hku : sp.S k u) (hn : ¬ o ≼ u) :
    Sealed (canon sp i) o k u := by
  refine ⟨⟨hku, hik⟩, ?_⟩
  rintro ⟨u', hu', hou'⟩
  have : u' = u := hf k u' u hu'.1 hku
  subst this
  exact hn hou'

/-- "For singleton fibers [Relational Monotonicity] is functional
monotonicity." -/
theorem relMono_iff_monoF {sp : Spec I O} (hf : sp.Functional) : sp.RelMono ↔ sp.MonotoneF := by
  constructor
  · intro h i j o u hij hio hju
    obtain ⟨u', hu', hou'⟩ := h i j o hij hio
    rw [hf j u' u hu' hju] at hou'
    exact hou'
  · intro h i j o hij hio
    obtain ⟨u, hu⟩ := sp.total j
    exact ⟨u, hu, h i j o u hij hio hu⟩

/-- Singleton fibers are directed. -/
theorem functional_directed {sp : Spec I O} (hf : sp.Functional) : sp.DirectedOutputs := by
  intro i X hne hX
  match X, hne with
  | x :: X', _ =>
    refine ⟨x, hX x (List.mem_cons_self ..), fun y hy => ?_⟩
    rw [hf i y x (hX y hy) (hX x (List.mem_cons_self ..))]
    exact PO.refl x

/-- "With singleton fibers [Lifted Monotonicity] is functional
monotonicity." -/
theorem liftedMono_iff_monoF {sp : Spec I O} (hf : sp.Functional) :
    sp.LiftedMono ↔ sp.MonotoneF := by
  rw [liftedMono_iff_relMono_directed, ← relMono_iff_monoF hf]
  exact ⟨fun h => h.1, fun h => ⟨h, functional_directed hf⟩⟩

/-- "With one output per input, Lifted Monotonicity and the common-expansion
condition are both monotonicity." -/
theorem commonExpansion_iff_monoF {sp : Spec I O} (hf : sp.Functional) :
    sp.CommonExpansion ↔ sp.MonotoneF := by
  rw [← liftedMono_iff_commonExpansion, liftedMono_iff_monoF hf]

/-- Paragraph after Cor. `cor:state-by-input`: in a consistent functional
specification, confluence at a common expansion `j` needs only `input(j)`:
every run state below `j` reaches `σ_S(j)` by that one event. -/
theorem functional_meet_by_input {sp : Spec I O} (hf : sp.Functional) (hc : sp.Consistent)
    {σ : State sp} (hrun : IsRun σ) {j : I} (hj : σ.cur ≼ j) :
    Exec σ [.input j] (canon sp j) := by
  have hcan := state_by_input hf hc hrun
  have hR : σ.R = (canon sp σ.cur).R := congrArg State.R hcan
  obtain ⟨u, hu⟩ := sp.total j
  have hleg : ∃ u, σ.R j u := ⟨u, by rw [hR]; exact ⟨hu, hj⟩⟩
  refine Exec.cons (Step.input σ (canon sp j) j hleg rfl ?_) (Exec.nil _)
  funext k x
  apply propext
  simp only [inputTable, canon, hR]
  constructor
  · rintro ⟨hS, hjk⟩; exact ⟨⟨hS, PO.trans hj hjk⟩, hjk⟩
  · rintro ⟨⟨hS, _⟩, hjk⟩; exact ⟨hS, hjk⟩

/-! ## 4. Lemma reconciliation and Complete CALM by the paper's route -/

/-- A run with its witness: start input, event list, final state. -/
structure RunW (sp : Spec I O) where
  start : I
  evs : List (Event I O)
  fin : State sp
  exec : Exec (canon sp start) evs fin

/-- `E`: the outputs emitted on any run of the family. -/
def emittedAll {sp : Spec I O} (fam : List (RunW sp)) : List O :=
  fam.flatMap (fun r => outs r.evs)

/-- **Lemma `lem:reconciliation`.** Runs ending at `(i_r,R_r)` with common
expansion `j` are confluent at `j` iff some `u ∈ S(j)` refines every output
emitted on any of them. -/
theorem reconciliation {sp : Spec I O} (fam : List (RunW sp)) (j : I)
    (hj : ∀ r ∈ fam, r.fin.cur ≼ j) :
    ConfluentAt (fam.map RunW.fin) j ↔ ∃ u, sp.S j u ∧ ∀ o ∈ emittedAll fam, o ≼ u := by
  have hrun : ∀ σ ∈ fam.map RunW.fin, IsRun σ := by
    intro σ hσ
    obtain ⟨r, _, rfl⟩ := List.mem_map.1 hσ
    exact ⟨r.start, r.evs, r.exec⟩
  have hj' : ∀ σ ∈ fam.map RunW.fin, σ.cur ≼ j := by
    intro σ hσ
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hσ
    exact hj r hr
  rw [survivor_test _ hrun j hj']
  constructor
  · rintro ⟨u, hu, hall⟩
    refine ⟨u, hu, fun o ho => ?_⟩
    obtain ⟨r, hr, hor⟩ := List.mem_flatMap.1 ho
    have := hall r.fin (List.mem_map.2 ⟨r, hr, rfl⟩)
    exact ((run_residual r.exec j u).1 this).2.2 o hor
  · rintro ⟨u, hu, hall⟩
    refine ⟨u, hu, fun σ hσ => ?_⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hσ
    exact (run_residual r.exec j u).2
      ⟨hu, hj r hr, fun o ho => hall o (List.mem_flatMap.2 ⟨r, hr, ho⟩)⟩

/-- Consistency, stated over families of runs (with their events) rather
than of run states. -/
theorem consistent_iff_runs {sp : Spec I O} :
    sp.Consistent ↔ ∀ fam : List (RunW sp), ∀ j : I,
      (∀ r ∈ fam, r.fin.cur ≼ j) → ConfluentAt (fam.map RunW.fin) j := by
  constructor
  · intro hc fam j hj
    apply hc
    · intro σ hσ
      obtain ⟨r, _, rfl⟩ := List.mem_map.1 hσ
      exact ⟨r.start, r.evs, r.exec⟩
    · intro σ hσ
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hσ
      exact hj r hr
  · intro h fam hrun j hj
    let mk : {σ // σ ∈ fam} → RunW sp := fun x =>
      ⟨(hrun x.1 x.2).choose, (hrun x.1 x.2).choose_spec.choose, x.1,
       (hrun x.1 x.2).choose_spec.choose_spec⟩
    have hmap : (fam.attach.map mk).map RunW.fin = fam := by
      rw [List.map_map]
      exact List.attach_map_subtype_val fam
    have := h (fam.attach.map mk) j (by
      intro r hr
      obtain ⟨x, _, rfl⟩ := List.mem_map.1 hr
      exact hj x.1 x.2)
    rwa [hmap] at this

/-- Collect, for outputs each emitted at some input below `j`, a finite list
of rows of `S` covering them. -/
theorem rows_of_outputs {sp : Spec I O} {j : I} :
    ∀ E : List O, (∀ o ∈ E, ∃ c, sp.S c o ∧ c ≼ j) →
      ∃ rows : List (I × O), (∀ r ∈ rows, sp.S r.1 r.2) ∧ (∀ r ∈ rows, r.1 ≼ j) ∧
        ∀ o ∈ E, ∃ r ∈ rows, r.2 = o := by
  intro E
  induction E with
  | nil => intro _; exact ⟨[], by simp, by simp, by simp⟩
  | cons o E ih =>
    intro h
    obtain ⟨c, hc, hcj⟩ := h o (List.mem_cons_self ..)
    obtain ⟨rows, h1, h2, h3⟩ := ih (fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))
    refine ⟨(c, o) :: rows, ?_, ?_, ?_⟩
    · intro r hr
      rcases List.mem_cons.1 hr with rfl | hr
      · exact hc
      · exact h1 r hr
    · intro r hr
      rcases List.mem_cons.1 hr with rfl | hr
      · exact hcj
      · exact h2 r hr
    · intro o' ho'
      rcases List.mem_cons.1 ho' with rfl | ho'
      · exact ⟨(c, o'), List.mem_cons_self .., rfl⟩
      · obtain ⟨r, hr, e⟩ := h3 o' ho'
        exact ⟨r, List.mem_cons_of_mem _ hr, e⟩

/-- Thm. Complete CALM (⇐), paper route: each emitted output `o` was emitted
at some `i_o ≼ j`, the condition supplies `u ∈ S(j)` refining all of them,
and the reconciliation lemma gives confluence. -/
theorem consistent_of_ce_paper {sp : Spec I O} (hC : sp.CommonExpansion) : sp.Consistent := by
  rw [consistent_iff_runs]
  intro fam j hj
  rw [reconciliation fam j hj]
  have hE : ∀ o ∈ emittedAll fam, ∃ c, sp.S c o ∧ c ≼ j := by
    intro o ho
    obtain ⟨r, hr, hor⟩ := List.mem_flatMap.1 ho
    obtain ⟨c, hc, hcr⟩ := (exec_emitted r.exec).2 o hor
    exact ⟨c, hc, PO.trans hcr (hj r hr)⟩
  obtain ⟨rows, hS, hJ, hcov⟩ := rows_of_outputs _ hE
  obtain ⟨u, hu, hall⟩ := hC rows hS j hJ
  refine ⟨u, hu, fun o ho => ?_⟩
  obtain ⟨r, hr, rfl⟩ := hcov o ho
  exact hall r hr

/-- Thm. Complete CALM (⇒), paper route: apply consistency and the
reconciliation lemma to the runs that start at `σ_S(i_r)` and emit `o_r`
(one `output` event each).  The empty family needs no separate case here
(consistency of the empty family plus reconciliation gives `S(j) ≠ ∅`); the
paper's appeal to totality is equally valid. -/
theorem ce_of_consistent_paper {sp : Spec I O} (hc : sp.Consistent) : sp.CommonExpansion := by
  intro rows hS j hJ
  let mk : {r // r ∈ rows} → RunW sp := fun x =>
    { start := x.1.1
      evs := [.output x.1.2]
      fin := outputState (canon sp x.1.1) x.1.2 ⟨hS x.1 x.2, PO.refl _⟩
      exec := Exec.cons (step_outputState _ _ _) (Exec.nil _) }
  let fam := rows.attach.map mk
  have hj : ∀ r ∈ fam, r.fin.cur ≼ j := by
    intro r hr
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 hr
    exact hJ x.1 x.2
  obtain ⟨u, hu, hall⟩ := (reconciliation fam j hj).1 ((consistent_iff_runs.1 hc) fam j hj)
  refine ⟨u, hu, fun r hr => hall r.2 ?_⟩
  refine List.mem_flatMap.2 ⟨mk ⟨r, hr⟩, List.mem_map.2 ⟨⟨r, hr⟩, List.mem_attach _ _, rfl⟩, ?_⟩
  simp [mk, outs]

/-- **Thm. Complete CALM** (common-expansion form), by the paper's route. -/
theorem complete_calm_paper (sp : Spec I O) : sp.Consistent ↔ sp.CommonExpansion :=
  ⟨ce_of_consistent_paper, consistent_of_ce_paper⟩

/-- **Thm. Complete CALM** (Lifted Monotonicity form), by the paper's route. -/
theorem complete_calm_paper_lm (sp : Spec I O) : sp.Consistent ↔ sp.LiftedMono := by
  rw [liftedMono_iff_commonExpansion]; exact complete_calm_paper sp

/-! ## 5. Exposure boundary by the paper's route -/

/-- Prop. `prop:exposure-boundary` (⇒), paper route: extend the run by
`output(o)` and by `input(j); output(x)`; consistency makes the two extended
runs confluent at `j`; the survivor row `(j,u)` lies in both tables, both
contained in `R`, so `u ∈ R(j)` refines `o` and `x`; the lifted exposure test
then makes `o` exposable.  Holds at every run state. -/
theorem exposable_of_consistent {sp : Spec I O} (hc : sp.Consistent)
    {τ : State sp} (hτ : IsRun τ) {o : O} (ho : τ.R τ.cur o) : Exposable τ o := by
  rw [lifted_exposure_test]
  intro j hij x hx
  let τ1 := outputState τ o ho
  let τ2a := inputState τ j x hx
  have hx2 : τ2a.R τ2a.cur x := ⟨hx, PO.refl j⟩
  let τ2 := outputState τ2a x hx2
  have r1 : IsRun τ1 := isRun_step hτ (step_outputState _ _ _)
  have r2 : IsRun τ2 := isRun_step (isRun_step hτ (step_inputState _ _ _ _)) (step_outputState _ _ _)
  have hrun : ∀ σ ∈ [τ1, τ2], IsRun σ := by
    intro σ hσ
    rcases List.mem_cons.1 hσ with rfl | hσ
    · exact r1
    · rcases List.mem_cons.1 hσ with rfl | hσ
      · exact r2
      · cases hσ
  have hcur : ∀ σ ∈ [τ1, τ2], σ.cur ≼ j := by
    intro σ hσ
    rcases List.mem_cons.1 hσ with rfl | hσ
    · exact hij
    · rcases List.mem_cons.1 hσ with rfl | hσ
      · exact PO.refl j
      · cases hσ
  obtain ⟨u, _, hall⟩ := (survivor_test _ hrun j hcur).1 (hc _ hrun j hcur)
  have h1 : τ1.R j u := hall τ1 (List.mem_cons_self ..)
  have h2 : τ2.R j u := hall τ2 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  exact ⟨u, h1.1, h1.2, h2.2⟩

/-- **Prop. `prop:exposure-boundary`**, with the forward direction by the
paper's route; the converse is `CC.exposure_boundary`, whose proof is the
paper's (exposure test at `σ_S(i_r)`, one row at a time). -/
theorem exposure_boundary_paper (sp : Spec I O) :
    sp.CommonExpansion ↔
      ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  ⟨fun hC _ hτ _ ho => exposable_of_consistent ((complete_calm_paper sp).2 hC) hτ.isRun ho,
   (exposure_boundary sp).2⟩

/-! ## 6. Pairs suffice -/

/-- The pair condition, over all rows of `S` (including rows at `j`). -/
def Pairs (sp : Spec I O) : Prop :=
  ∀ i₁ o₁ i₂ o₂ j, sp.S i₁ o₁ → sp.S i₂ o₂ → i₁ ≼ j → i₂ ≼ j →
    ∃ u, sp.S j u ∧ o₁ ≼ u ∧ o₂ ≼ u

/-- Paragraph `app:pairs-suffice`: pairs suffice for the common-expansion
condition (`CC.Deploy.ce_of_pairs`; its proof is the paper's: fold a row at
`j` into the family one row at a time). -/
theorem pairs_iff_commonExpansion (sp : Spec I O) : Pairs sp ↔ sp.CommonExpansion := by
  constructor
  · intro h; exact CC.Deploy.ce_of_pairs h
  · intro hC i₁ o₁ i₂ o₂ j h₁ h₂ hj₁ hj₂
    obtain ⟨u, hu, hall⟩ := hC [(i₁, o₁), (i₂, o₂)] (by simp [h₁, h₂]) j (by simp [hj₁, hj₂])
    exact ⟨u, hu, hall _ (List.mem_cons_self ..), hall _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩

end Generic

/-! ## 7. The `k`-set agreement example (`app:additional-applications`)

Instance: participants `p_r = r` and values `v_r = r` for `r : Fin (k+1)`
(the paper allows further participants and values; one instance suffices for
the counterexample).  An input is a finite set of proposals, at most one per
participant, i.e. a partial map `P ⇀ Val`, ordered by inclusion (= extension);
an output is a partial decision map ordered by extension.  Both are
`PMap (k+1)`.  "Range has at most `k` values" is stated literally: the range
is contained in a list of at most `k` values. -/

/-- Partial maps `Fin n ⇀ Fin n`, ordered by extension. -/
def PMap (n : Nat) := Fin n → Option (Fin n)

instance (n : Nat) : PO (PMap n) where
  le m m' := ∀ p v, m p = some v → m' p = some v
  refl _ _ _ h := h
  trans h1 h2 p v h := h2 p v (h1 p v h)
  antisymm {a b} h1 h2 := by
    funext p
    cases ha : a p with
    | none =>
      cases hb : b p with
      | none => rfl
      | some w => rw [h2 p w hb] at ha; cases ha
    | some v => exact (h1 p v ha).symm

namespace KSet
variable (k : Nat)

theorem le_def {n : Nat} (m m' : PMap n) : m ≼ m' ↔ ∀ p v, m p = some v → m' p = some v :=
  Iff.rfl

/-- At input `I`, `m` is permitted when it decides only participants that
propose in `I`, every value in its range is proposed in `I`, and its range has
at most `k` values. -/
def Perm (I m : PMap (k+1)) : Prop :=
  (∀ p v, m p = some v → ∃ w, I p = some w) ∧
  (∀ p v, m p = some v → ∃ q, I q = some v) ∧
  ∃ L : List (Fin (k+1)), L.length ≤ k ∧ ∀ p v, m p = some v → v ∈ L

/-- The `k`-set agreement specification (total: the empty map is permitted). -/
def spec : Spec (PMap (k+1)) (PMap (k+1)) where
  S := Perm k
  total _ := ⟨fun _ => none, by simp, by simp, [], by simp, by simp⟩

/-- The single proposal / single decision `{p ↦ v}`. -/
def atom {n : Nat} (p v : Fin n) : PMap n := fun q => if q = p then some v else none

/-- The union of the proposal inputs `{(p_r, v_r)}`. -/
def J (n : Nat) : PMap n := fun p => some p

/-- `J` minus participant `r₀`. -/
def allBut {n : Nat} (r₀ : Fin n) : PMap n := fun p => if p = r₀ then none else some p

theorem atom_some {n : Nat} {p v q w : Fin n} (h : atom p v q = some w) : q = p ∧ w = v := by
  unfold atom at h
  by_cases hq : q = p
  · simp only [hq, ↓reduceIte] at h; cases h; exact ⟨hq, rfl⟩
  · simp only [hq, ↓reduceIte] at h; cases h

theorem atom_le_J {n : Nat} (r : Fin n) : atom r r ≼ J n := by
  intro p v h
  obtain ⟨rfl, rfl⟩ := atom_some h
  rfl

/-- At `p_r`'s proposal input, `{p_r ↦ v_r}` is permitted (`k ≥ 1`). -/
theorem proposal_row (hk : 1 ≤ k) (r : Fin (k+1)) : (spec k).S (atom r r) (atom r r) := by
  refine ⟨fun p v h => ⟨v, h⟩, fun p v h => ⟨p, h⟩, [r], by simpa using hk, ?_⟩
  intro p v h
  obtain ⟨_, rfl⟩ := atom_some h
  simp

/-- The union of the proposal inputs is a common expansion. -/
theorem J_common (r : Fin (k+1)) : atom r r ≼ J (k+1) := atom_le_J r

/-- Pigeonhole: a list of fewer than `n` elements of `Fin n` misses one. -/
theorem missing {n : Nat} (L : List (Fin n)) (h : L.length < n) : ∃ x, x ∉ L := by
  apply Classical.byContradiction
  intro hc
  have hs : List.finRange n ⊆ L := fun x _ =>
    Classical.byContradiction fun hx => hc ⟨x, hx⟩
  have := List.Nodup.length_le_of_subset (List.nodup_finRange n) hs
  rw [List.length_finRange] at this
  omega

/-- `J` minus one participant is permitted at `J`. -/
theorem allBut_perm (r₀ : Fin (k+1)) : (spec k).S (J (k+1)) (allBut r₀) := by
  refine ⟨fun p _ _ => ⟨p, rfl⟩, ?_, (List.finRange (k+1)).erase r₀, ?_, ?_⟩
  · intro p v h
    unfold allBut at h
    by_cases hp : p = r₀
    · simp only [hp, ↓reduceIte] at h; cases h
    · simp only [hp, ↓reduceIte] at h; cases h; exact ⟨p, rfl⟩
  · rw [List.length_erase_of_mem (List.mem_finRange r₀), List.length_finRange]; omega
  · intro p v h
    unfold allBut at h
    by_cases hp : p = r₀
    · simp only [hp, ↓reduceIte] at h; cases h
    · simp only [hp, ↓reduceIte] at h; cases h
      exact (List.mem_erase_of_ne hp).2 (List.mem_finRange p)

/-- "Any `k` of these `k+1` rows have a common refinement there": any list of
at most `k` proposal rows is compatible in `S(J)`. -/
theorem any_k_compatible (L : List (Fin (k+1))) (hL : L.length ≤ k) :
    ∃ u, (spec k).S (J (k+1)) u ∧ ∀ r ∈ L, atom r r ≼ u := by
  obtain ⟨r₀, hr₀⟩ := missing L (by omega)
  refine ⟨allBut r₀, allBut_perm k r₀, fun r hr p v h => ?_⟩
  obtain ⟨hp, hv⟩ := atom_some h
  have : r ≠ r₀ := fun e => hr₀ (e ▸ hr)
  rw [hp, hv]
  simp [allBut, this]

/-- "All `k+1` do not, since it would have `k+1` values." -/
theorem not_all_compatible :
    ¬ ∃ u, (spec k).S (J (k+1)) u ∧ ∀ r : Fin (k+1), atom r r ≼ u := by
  rintro ⟨u, ⟨_, _, L, hL, hran⟩, hall⟩
  have hs : List.finRange (k+1) ⊆ L := fun r _ =>
    hran r r (hall r r r (by simp [atom]))
  have := List.Nodup.length_le_of_subset (List.nodup_finRange (k+1)) hs
  rw [List.length_finRange] at this
  omega

/-- "So the common-expansion condition fails" (`k ≥ 1`). -/
theorem not_commonExpansion (hk : 1 ≤ k) : ¬ (spec k).CommonExpansion := by
  intro hC
  obtain ⟨u, hu, hall⟩ := hC ((List.finRange (k+1)).map fun r => (atom r r, atom r r))
    (by
      intro x hx
      obtain ⟨r, _, rfl⟩ := List.mem_map.1 hx
      exact proposal_row k hk r)
    (J (k+1))
    (by
      intro x hx
      obtain ⟨r, _, rfl⟩ := List.mem_map.1 hx
      exact atom_le_J r)
  exact not_all_compatible k ⟨u, hu, fun r =>
    hall (atom r r, atom r r) (List.mem_map.2 ⟨r, List.mem_finRange r, rfl⟩)⟩

/-- "... and the specification is not monotone." -/
theorem not_liftedMono (hk : 1 ≤ k) : ¬ (spec k).LiftedMono := by
  rw [liftedMono_iff_commonExpansion]; exact not_commonExpansion k hk

/-- A permitted output at a single-proposal input is contained in it. -/
theorem perm_atom_le {p v : Fin (k+1)} {o : PMap (k+1)} (h : (spec k).S (atom p v) o)
    {q w : Fin (k+1)} (hq : o q = some w) : q = p ∧ w = v := by
  obtain ⟨h1, h2, _⟩ := h
  obtain ⟨w', hw'⟩ := h1 q w hq
  obtain ⟨hqp, _⟩ := atom_some hw'
  obtain ⟨q', hq'⟩ := h2 q w hq
  obtain ⟨_, hwv⟩ := atom_some hq'
  exact ⟨hqp, hwv⟩

open Classical in
/-- Paragraph `app:pairs-suffice`: "restricting the families to rows at
minimal inputs does not suffice, even `k` rows at a time".  In this
specification *every* family of at most `k` rows at single-proposal inputs
(the minimal nonempty inputs), with any common expansion `j`, is compatible
in `S(j)`; yet the common-expansion condition fails (`not_commonExpansion`).
(Rows at the least input `∅` carry only the empty map, which every output
refines, so adding them changes nothing.)  A row is `(p, v, o)`, at input
`{(p,v)}`. -/
theorem atomic_k_at_a_time (rows : List (Fin (k+1) × Fin (k+1) × PMap (k+1)))
    (hlen : rows.length ≤ k)
    (hS : ∀ r ∈ rows, (spec k).S (atom r.1 r.2.1) r.2.2)
    (j : PMap (k+1)) (hj : ∀ r ∈ rows, atom r.1 r.2.1 ≼ j) :
    ∃ u, (spec k).S j u ∧ ∀ r ∈ rows, r.2.2 ≼ u := by
  let u : PMap (k+1) := fun q =>
    if ∃ r ∈ rows, (r.2.2 q).isSome then j q else none
  -- each decided coordinate of a row output is that row's proposal, present in `j`
  have key : ∀ r ∈ rows, ∀ q w, r.2.2 q = some w → q = r.1 ∧ w = r.2.1 ∧ j q = some w := by
    intro r hr q w hq
    obtain ⟨hq1, hw1⟩ := perm_atom_le k (hS r hr) hq
    refine ⟨hq1, hw1, hj r hr q w ?_⟩
    rw [hq1, hw1]
    simp [atom]
  have hu : ∀ q w, u q = some w → j q = some w ∧ ∃ r ∈ rows, w = r.2.1 := by
    intro q w h
    simp only [u] at h
    by_cases hc : ∃ r ∈ rows, (r.2.2 q).isSome
    · simp only [hc, ↓reduceIte] at h
      obtain ⟨r, hr, hs⟩ := hc
      cases hq : r.2.2 q with
      | none => rw [hq] at hs; cases hs
      | some w' =>
        obtain ⟨_, hw', hjq⟩ := key r hr q w' hq
        rw [hjq] at h; cases h
        exact ⟨hjq, r, hr, hw'⟩
    · simp only [hc, ↓reduceIte] at h; cases h
  refine ⟨u, ⟨?_, ?_, rows.map (fun r => r.2.1), by simpa using hlen, ?_⟩, ?_⟩
  · intro q w h; exact ⟨w, (hu q w h).1⟩
  · intro q w h; exact ⟨q, (hu q w h).1⟩
  · intro q w h
    obtain ⟨_, r, hr, rfl⟩ := hu q w h
    exact List.mem_map.2 ⟨r, hr, rfl⟩
  · intro r hr q w hq
    obtain ⟨_, _, hjq⟩ := key r hr q w hq
    have hc : ∃ r ∈ rows, (r.2.2 q).isSome := ⟨r, hr, by simp [hq]⟩
    show (if ∃ r ∈ rows, (r.2.2 q).isSome then j q else none) = some w
    simp [hc, hjq]

end KSet

/-! ## 8. "The pairs must range over all rows of `S`, including those at `j`"

A four-input specification: three incomparable inputs `a, b, c` below `top`.
At `a, b, c` the only output is the corresponding singleton; at `top` the
permitted outputs are the sub-maps of `J` that omit some participant.  Every
two rows *not at the common expansion* are compatible there, but the
common-expansion condition fails. -/

inductive In4 | a | b | c | top
  deriving DecidableEq

instance : PO In4 where
  le x y := x = y ∨ y = In4.top
  refl _ := Or.inl rfl
  trans := by
    intro x y z h1 h2
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp
  antisymm := by
    intro x y h1 h2
    rcases h1 with rfl | rfl
    · rfl
    · rcases h2 with h | h <;> simp_all

def In4.idx : In4 → Fin 3
  | .a => 0 | .b => 1 | .c => 2 | .top => 0

def spec4 : Spec In4 (PMap 3) where
  S i o := match i with
    | .top => (∀ p v, o p = some v → v = p) ∧ ∃ w, o w = none
    | i => o = KSet.atom i.idx i.idx
  total i := by
    cases i
    case top => exact ⟨fun _ => none, by simp, 0, rfl⟩
    all_goals exact ⟨_, rfl⟩

/-- The pair condition restricted to rows whose inputs differ from the common
expansion `j` holds. -/
theorem spec4_pairs_off_j :
    ∀ i₁ o₁ i₂ o₂ j, i₁ ≠ j → i₂ ≠ j → spec4.S i₁ o₁ → spec4.S i₂ o₂ → i₁ ≼ j → i₂ ≼ j →
      ∃ u, spec4.S j u ∧ o₁ ≼ u ∧ o₂ ≼ u := by
  intro i₁ o₁ i₂ o₂ j n1 n2 h1 h2 l1 l2
  have hj : j = .top := by
    rcases l1 with h | h
    · exact absurd h n1
    · exact h
  subst hj
  have ht1 : i₁ ≠ .top := n1
  have ht2 : i₂ ≠ .top := n2
  -- the third participant, omitted by `u`
  have hw : ∃ w : Fin 3, w ≠ i₁.idx ∧ w ≠ i₂.idx := by
    cases i₁ <;> cases i₂ <;> first
      | exact absurd rfl ht1 | exact absurd rfl ht2
      | exact ⟨2, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩
      | exact ⟨0, by decide, by decide⟩
  obtain ⟨w, hw1, hw2⟩ := hw
  have e1 : o₁ = KSet.atom i₁.idx i₁.idx := by cases i₁ <;> first | exact h1 | exact absurd rfl ht1
  have e2 : o₂ = KSet.atom i₂.idx i₂.idx := by cases i₂ <;> first | exact h2 | exact absurd rfl ht2
  subst e1; subst e2
  refine ⟨KSet.allBut w, ⟨?_, w, by simp [KSet.allBut]⟩, ?_, ?_⟩
  · intro p v h
    unfold KSet.allBut at h
    by_cases hp : p = w
    · simp only [hp, ↓reduceIte] at h; cases h
    · simp only [hp, ↓reduceIte] at h; cases h; rfl
  · intro p v h
    obtain ⟨rfl, rfl⟩ := KSet.atom_some h
    have : i₁.idx ≠ w := fun e => hw1 e.symm
    simp [KSet.allBut, this]
  · intro p v h
    obtain ⟨rfl, rfl⟩ := KSet.atom_some h
    have : i₂.idx ≠ w := fun e => hw2 e.symm
    simp [KSet.allBut, this]

theorem spec4_not_ce : ¬ spec4.CommonExpansion := by
  intro hC
  obtain ⟨u, ⟨_, w, hw⟩, hall⟩ :=
    hC [(.a, KSet.atom 0 0), (.b, KSet.atom 1 1), (.c, KSet.atom 2 2)]
      (by intro r hr; simp at hr; rcases hr with rfl | rfl | rfl <;> rfl) .top
      (by intro r hr; simp at hr; rcases hr with rfl | rfl | rfl <;> exact Or.inr rfl)
  have h0 := hall _ (List.mem_cons_self ..) 0 0 (by simp [KSet.atom])
  have h1 := hall _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) 1 1 (by simp [KSet.atom])
  have h2 := hall _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    2 2 (by simp [KSet.atom])
  have : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases this w with rfl | rfl | rfl
  · rw [h0] at hw; cases hw
  · rw [h1] at hw; cases hw
  · rw [h2] at hw; cases hw

/-- Pairs not ranging over rows at `j` do not suffice. -/
theorem rowsAtJ_needed :
    (∀ i₁ o₁ i₂ o₂ j, i₁ ≠ j → i₂ ≠ j → spec4.S i₁ o₁ → spec4.S i₂ o₂ → i₁ ≼ j → i₂ ≼ j →
      ∃ u, spec4.S j u ∧ o₁ ≼ u ∧ o₂ ≼ u) ∧ ¬ spec4.CommonExpansion :=
  ⟨spec4_pairs_off_j, spec4_not_ce⟩

/-! ## 9. Corollary state-by-input does not carry over to relational specs -/

inductive Pt | pt
inductive Two | lo | hi

instance : PO Pt where
  le _ _ := True
  refl _ := trivial
  trans _ _ := trivial
  antisymm {a b} _ _ := by cases a; cases b; rfl

instance : PO Two where
  le x y := x = .lo ∨ y = .hi
  refl x := by cases x <;> simp
  trans := by
    intro x y z h1 h2
    cases x <;> cases y <;> cases z <;> simp_all
  antisymm := by
    intro x y h1 h2
    cases x <;> cases y <;> simp_all

/-- One input, two outputs `lo ≼ hi`, both permitted. -/
def specTwo : Spec Pt Two where
  S _ _ := True
  total _ := ⟨.lo, trivial⟩

/-- Section `sec:complete-calm-theorem`, last paragraph: a consistent
relational specification in which a run ends at a non-canonical state
(emitting `hi` retires the row `(pt, lo)`). -/
theorem state_by_input_fails_relationally :
    specTwo.Consistent ∧ ∃ τ : State specTwo, IsRun τ ∧ τ ≠ canon specTwo τ.cur := by
  refine ⟨?_, ?_⟩
  · rw [complete_calm_paper]
    intro rows _ _ _
    exact ⟨.hi, trivial, fun r _ => Or.inr rfl⟩
  · let τ := outputState (canon specTwo .pt) .hi ⟨trivial, trivial⟩
    refine ⟨τ, ⟨.pt, _, Exec.cons (step_outputState _ _ _) (Exec.nil _)⟩, fun h => ?_⟩
    have hR : τ.R .pt .lo := by
      rw [h]; exact ⟨trivial, trivial⟩
    rcases hR.2 with h | h <;> cases h

/-! ## 10. The election example (Section `sec:election-story`)

Three voters, ballots for `x` or `y`; the input is the ballots received so
far (`none` = dot), ordered by extension; the output is the candidate with
two ballots, or `⊥`.  `Res` carries the refinement order (`⊥ ≼` everything,
`x`, `y` incomparable); `ResE` the equality order. -/

inductive Cand | x | y
  deriving DecidableEq

structure Ballots where
  b1 : Option Cand
  b2 : Option Cand
  b3 : Option Cand
  deriving DecidableEq

abbrev oleq (a b : Option Cand) : Prop := a = none ∨ a = b

abbrev bLe (i j : Ballots) : Prop := oleq i.b1 j.b1 ∧ oleq i.b2 j.b2 ∧ oleq i.b3 j.b3

theorem oleq_trans {a b c : Option Cand} (h1 : oleq a b) (h2 : oleq b c) : oleq a c := by
  rcases h1 with rfl | rfl
  · exact Or.inl rfl
  · exact h2

theorem oleq_antisymm {a b : Option Cand} (h1 : oleq a b) (h2 : oleq b a) : a = b := by
  rcases h1 with rfl | rfl
  · rcases h2 with rfl | rfl <;> rfl
  · rfl

theorem oleq_some {c : Cand} {d : Option Cand} (h : oleq (some c) d) : d = some c := by
  rcases h with h | h
  · cases h
  · exact h.symm

instance : PO Ballots where
  le := bLe
  refl _ := ⟨Or.inr rfl, Or.inr rfl, Or.inr rfl⟩
  trans h1 h2 := ⟨oleq_trans h1.1 h2.1, oleq_trans h1.2.1 h2.2.1, oleq_trans h1.2.2 h2.2.2⟩
  antisymm {a b} h1 h2 := by
    cases a; cases b
    simp only [Ballots.mk.injEq]
    exact ⟨oleq_antisymm h1.1 h2.1, oleq_antisymm h1.2.1 h2.2.1, oleq_antisymm h1.2.2 h2.2.2⟩

instance (i j : Ballots) : Decidable (i ≼ j) := inferInstanceAs (Decidable (bLe i j))

inductive Res | bot | win (c : Cand)
  deriving DecidableEq

abbrev resLe (a b : Res) : Prop := a = .bot ∨ a = b

instance : PO Res where
  le := resLe
  refl _ := Or.inr rfl
  trans := by
    intro a b c h1 h2
    rcases h1 with rfl | rfl
    · exact Or.inl rfl
    · exact h2
  antisymm := by
    intro a b h1 h2
    rcases h1 with rfl | rfl
    · rcases h2 with h | h <;> simp_all
    · rfl

structure ResE where
  r : Res
  deriving DecidableEq

instance : PO ResE where
  le a b := a = b
  refl _ := rfl
  trans h1 h2 := h1.trans h2
  antisymm h _ := h

def cnt (c : Cand) (i : Ballots) : Nat :=
  (if i.b1 = some c then 1 else 0) + (if i.b2 = some c then 1 else 0) +
  (if i.b3 = some c then 1 else 0)

def winner (i : Ballots) : Res :=
  if 2 ≤ cnt .x i then .win .x else if 2 ≤ cnt .y i then .win .y else .bot

/-- The election, under the refinement order. -/
def elec : Spec Ballots Res where
  S i o := o = winner i
  total _ := ⟨_, rfl⟩

/-- The election, under the equality order. -/
def elecEq : Spec Ballots ResE where
  S i o := o = ⟨winner i⟩
  total _ := ⟨_, rfl⟩

theorem elec_functional : elec.Functional := fun _ _ _ h h' => h.trans h'.symm
theorem elecEq_functional : elecEq.Functional := fun _ _ _ h h' => h.trans h'.symm

theorem winner_mono_raw : ∀ i j : Ballots, bLe i j → resLe (winner i) (winner j) := by
  intro ⟨a1, a2, a3⟩ ⟨c1, c2, c3⟩
  rcases a1 with _ | _ | _ <;> rcases a2 with _ | _ | _ <;> rcases a3 with _ | _ | _ <;>
  rcases c1 with _ | _ | _ <;> rcases c2 with _ | _ | _ <;> rcases c3 with _ | _ | _ <;>
  decide

/-- The election is monotone, hence consistent (Functional CALM). -/
theorem elec_monotone : elec.MonotoneF := by
  intro i j o u hij hio hju
  subst hio; subst hju
  exact winner_mono_raw i j hij

theorem elec_consistent : elec.Consistent := (functional_calm elec_functional).2 elec_monotone

def bxd : Ballots := ⟨some .x, none, none⟩          -- x··
def bxy : Ballots := ⟨some .x, some .y, none⟩       -- xy·
def bxyx : Ballots := ⟨some .x, some .y, some .x⟩   -- xyx
def bxx : Ballots := ⟨some .x, some .x, none⟩       -- xx·

/-- `xy· ≼ xyx`, `f(xy·) = ⊥`, `f(xyx) = x`. -/
theorem bxy_le_bxyx : bxy ≼ bxyx := by decide
theorem winner_bxy : winner bxy = .bot := by decide
theorem winner_bxyx : winner bxyx = .win .x := by decide

/-- Under the equality order the election is not monotone, hence not
consistent. -/
theorem elecEq_not_monotone : ¬ elecEq.MonotoneF := by
  intro h
  have := h bxy bxyx ⟨winner bxy⟩ ⟨winner bxyx⟩ bxy_le_bxyx rfl rfl
  rw [winner_bxy, winner_bxyx] at this
  cases this

theorem elecEq_not_consistent : ¬ elecEq.Consistent := fun h =>
  elecEq_not_monotone ((functional_calm elecEq_functional).1 h)

/-- Panels (a)–(c): `⊥` is exposable at `σ_S(x··)` and `σ_S(xy·)`, and `x` at
`σ_S(xx·)` (monotone order). -/
theorem elec_panels_exposable :
    Exposable (canon elec bxd) .bot ∧ Exposable (canon elec bxy) .bot ∧
      Exposable (canon elec bxx) (.win .x) := by
  have hb := (functional_exposure_boundary elec_functional).1 elec_monotone
  refine ⟨hb _ ⟨_, [], ExecCF.nil _⟩ _ ⟨(by decide : Res.bot = winner bxd), PO.refl _⟩,
          hb _ ⟨_, [], ExecCF.nil _⟩ _ ⟨(by decide : Res.bot = winner bxy), PO.refl _⟩,
          hb _ ⟨_, [], ExecCF.nil _⟩ _ ⟨(by decide : Res.win .x = winner bxx), PO.refl _⟩⟩

/-- Panel (b) is undetermined (`⊥` at `xy·` and `x` at `xyx` remain). -/
theorem elec_panel_b_undetermined : ¬ Determined (canon elec bxy) := by
  rintro ⟨o, h⟩
  have h1 := h bxy (winner bxy) ⟨rfl, PO.refl _⟩
  have h2 := h bxyx (winner bxyx) ⟨rfl, bxy_le_bxyx⟩
  rw [winner_bxy] at h1; rw [winner_bxyx, ← h1] at h2
  cases h2

/-- Panel (c) is determined: every row at an expansion of `xx·` has output `x`. -/
theorem elec_panel_c_determined : Determined (canon elec bxx) := by
  refine ⟨.win .x, fun k u hk => ?_⟩
  obtain ⟨hS, hle⟩ := hk
  subst hS
  obtain ⟨c1, c2, c3⟩ := k
  obtain ⟨h1, h2, _⟩ := hle
  simp only [bxx] at h1 h2
  have e1 := oleq_some h1
  have e2 := oleq_some h2
  subst e1; subst e2
  rcases c3 with _ | _ | _ <;> decide

/-- Equality-order variant (Fig. `fig:nonmonotone-frame`): `output(⊥)` at
`σ_S(xy·)` seals `xyx` ... -/
theorem elecEq_bot_seals : Sealed (canon elecEq bxy) ⟨.bot⟩ bxyx ⟨winner bxyx⟩ :=
  nonmono_seals elecEq_functional bxy_le_bxyx
    (show (⟨Res.bot⟩ : ResE) = ⟨winner bxy⟩ by rw [winner_bxy]) rfl
    (by rw [winner_bxyx]; intro h; cases h)

/-- ... and leaves the single row `(xy·, ⊥)`
(`S[in ⪰ xy·, out ⪰ ⊥]`, the example after Lemma `lem:run-residual`). -/
theorem elecEq_bot_single_row (k : Ballots) (o : ResE) :
    outputTable (canon elecEq bxy) ⟨.bot⟩ k o ↔ (k = bxy ∧ o = ⟨.bot⟩) := by
  constructor
  · rintro ⟨⟨hS, hle⟩, hbo⟩
    subst hbo
    obtain ⟨c1, c2, c3⟩ := k
    obtain ⟨h1, h2, h3⟩ := hle
    have e1 := oleq_some h1
    have e2 := oleq_some h2
    subst e1; subst e2
    have hS' : (⟨Res.bot⟩ : ResE) = ⟨winner ⟨some .x, some .y, c3⟩⟩ := hS
    rcases c3 with _ | _ | _
    · exact ⟨rfl, rfl⟩
    · exact absurd hS' (by decide)
    · exact absurd hS' (by decide)
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨by show (⟨Res.bot⟩ : ResE) = ⟨winner bxy⟩; rw [winner_bxy], PO.refl _⟩, rfl⟩

/-- "A run that emits `⊥` at `xy·` and one that receives `xyx` cannot be
reconciled at `xyx`" (equality order). -/
theorem elecEq_not_confluent :
    ¬ ConfluentAt [outputState (canon elecEq bxy) ⟨.bot⟩ ((elecEq_bot_single_row bxy _).2 ⟨rfl, rfl⟩).1,
                   canon elecEq bxyx] bxyx := by
  intro h
  have hrun : ∀ σ ∈ [outputState (canon elecEq bxy) ⟨.bot⟩
      ((elecEq_bot_single_row bxy _).2 ⟨rfl, rfl⟩).1, canon elecEq bxyx], IsRun σ := by
    intro σ hσ
    rcases List.mem_cons.1 hσ with rfl | hσ
    · exact ⟨bxy, _, Exec.cons (step_outputState _ _ _) (Exec.nil _)⟩
    · rcases List.mem_cons.1 hσ with rfl | hσ
      · exact ⟨bxyx, [], Exec.nil _⟩
      · cases hσ
  have hcur : ∀ σ ∈ [outputState (canon elecEq bxy) ⟨.bot⟩
      ((elecEq_bot_single_row bxy _).2 ⟨rfl, rfl⟩).1, canon elecEq bxyx], σ.cur ≼ bxyx := by
    intro σ hσ
    rcases List.mem_cons.1 hσ with rfl | hσ
    · exact bxy_le_bxyx
    · rcases List.mem_cons.1 hσ with rfl | hσ
      · exact PO.refl _
      · cases hσ
  obtain ⟨u, _, hall⟩ := (survivor_test _ hrun bxyx hcur).1 h
  have := (elecEq_bot_single_row bxyx u).1 (hall _ (List.mem_cons_self ..))
  exact absurd this.1 (by decide)

/-! ## 11. The directed-fiber example (Section `sec:lifted-monotonicity`)

The fiber `{{a},{b},{a,b,c},{a,b,d},{a,b,c,d}}` under inclusion. -/

inductive F5 | a | b | abc | abd | abcd
  deriving DecidableEq

/-- Membership of `a, b, c, d` (as `0,1,2,3`). -/
def F5.mem : F5 → Fin 4 → Bool
  | .a, n => n == 0
  | .b, n => n == 1
  | .abc, n => n == 0 || n == 1 || n == 2
  | .abd, n => n == 0 || n == 1 || n == 3
  | .abcd, _ => true

/-- Inclusion, as a decidable proposition. -/
abbrev F5.sub (s t : F5) : Prop :=
  (s.mem 0 → t.mem 0) ∧ (s.mem 1 → t.mem 1) ∧ (s.mem 2 → t.mem 2) ∧ (s.mem 3 → t.mem 3)

instance : PO F5 where
  le := F5.sub
  refl s := by cases s <;> decide
  trans := by intro s t w; cases s <;> cases t <;> cases w <;> decide
  antisymm := by intro s t; cases s <;> cases t <;> decide

instance (s t : F5) : Decidable (s ≼ t) := inferInstanceAs (Decidable (F5.sub s t))

/-- The fiber is directed: `{a,b,c,d}` refines every member. -/
theorem f5_directed : JointLift (fun _ : F5 => True) (fun _ : F5 => True) := by
  intro X _ _
  exact ⟨.abcd, trivial, fun x _ => by cases x <;> decide⟩

/-- `{a}` and `{b}` have exactly the common refinements `{a,b,c}`, `{a,b,d}`,
`{a,b,c,d}` in the fiber; the two minimal ones are incomparable. -/
theorem f5_common_refinements (u : F5) : (F5.a ≼ u ∧ F5.b ≼ u) ↔ (u = .abc ∨ u = .abd ∨ u = .abcd) := by
  cases u <;> decide

theorem f5_minimal_incomparable :
    ¬ (F5.abc ≼ F5.abd) ∧ ¬ (F5.abd ≼ F5.abc) ∧
    (∀ u, F5.a ≼ u → F5.b ≼ u → u ≼ F5.abc → u = F5.abc) ∧
    (∀ u, F5.a ≼ u → F5.b ≼ u → u ≼ F5.abd → u = F5.abd) := by
  refine ⟨by decide, by decide, ?_, ?_⟩ <;> intro u <;> cases u <;> decide

/-- `{a,b,c}` and `{a,b,d}` are incomparable but compatible. -/
theorem f5_compatible : CompatibleIn (fun _ : F5 => True) [F5.abc, F5.abd] :=
  ⟨.abcd, trivial, fun x hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · decide
    · rcases List.mem_cons.1 hx with rfl | hx
      · decide
      · cases hx⟩

end AuditA
end CC
