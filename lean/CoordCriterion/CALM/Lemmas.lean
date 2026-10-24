import CoordCriterion.FunctionalCALM.Theorem
import CoordCriterion.CompleteCALM.Theorem

/-!
# Supporting lemmas for Sections 2–3 and Appendix B (`app:proofs`)

Supports `sections/functional-calm.tex`, `sections/complete-calm.tex` and the
deferred proofs of `appendices/proof-machinery.tex` (except `app:iconfluence`,
which is in `Instances/InvariantConfluence.lean`).  The main theorems are in
`FunctionalCALM/Theorem.lean` and `CompleteCALM/Theorem.lean`; this file adds
the remaining claims of the text and re-proves the theorems along the paper's
own proof routes:

* event facts used in the text: the target states of input/output events
  exist (`inputState`, `outputState`), `input j; input k` = `input k`
  (`input_input`), `input i` at `(i,R)` is a no-op (`input_self`), determined
  states stay determined (`step_determined`, `reach_determined`), canonical
  states are largest and input events move between them (`state_le_canon`,
  `input_canon`); determinism of events is `CC.step_det` (`Foundations/Runs`);
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
* **Lemma `lem:reconciliation`** (`reconciliation`), stated over families of
  runs with their event lists; consistency over such families
  (`consistent_iff_runs`);
* **Thm. Complete CALM by the paper's route** through the reconciliation lemma
  (`complete_calm_paper`, `complete_calm_paper_lm`);
* **Prop. exposure boundary by the paper's route** (forward direction via
  consistency and the survivor test, `exposable_of_consistent`, which holds
  at every run state, not only commitment-free ones;
  `exposure_boundary_paper`);
* **Pairs suffice** (`app:pairs-suffice`): `pairs_iff_commonExpansion`, from
  `CC.ce_of_pairs` (`CompleteCALM/Theorem.lean`).

The examples of these sections are in `CALM/Examples.lean`.
-/

namespace CC
namespace CALM

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
condition (`CC.ce_of_pairs`; its proof is the paper's: fold a row at
`j` into the family one row at a time). -/
theorem pairs_iff_commonExpansion (sp : Spec I O) : Pairs sp ↔ sp.CommonExpansion := by
  constructor
  · intro h; exact CC.ce_of_pairs h
  · intro hC i₁ o₁ i₂ o₂ j h₁ h₂ hj₁ hj₂
    obtain ⟨u, hu, hall⟩ := hC [(i₁, o₁), (i₂, o₂)] (by simp [h₁, h₂]) j (by simp [hj₁, hj₂])
    exact ⟨u, hu, hall _ (List.mem_cons_self ..), hall _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩

end Generic

end CALM
end CC
