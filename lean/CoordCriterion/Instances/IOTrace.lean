import CoordCriterion.Foundations.IOAutomata
import CoordCriterion.Appendix.Guarded
import CoordCriterion.CompleteCALM.Cofinal
import CoordCriterion.Distributed.SystemConfluence

/-!
# Projecting an I/O automaton onto a specification, and the automaton as a system (§6.5)

Namespace `CC.IOT`.  `M : IOA.Automaton A` is any Lynch–Tuttle I/O automaton
(input-enabled, with a nonempty set of start states; `Foundations/IOAutomata.lean`).
Its input actions are the requests it receives and its output actions the
replies it sends.  No observation function and no order on reply values is
assumed.

## The projection (Def. `def:projection`, Prop. `prop:projection`)

* `recvs M β`, `replies M β` — the receive sequence and the reply sequence of
  a schedule `β` (its input actions, its output actions, in order).
* `Wd p` — finite sequences of actions satisfying `p`, ordered by prefix;
  `InS M`, `OutS M` — receive sequences and reply sequences.
* `spec M : Spec (InS M) (OutS M)` — the projected spec: `(w, t)` is a row iff
  some finite execution has receive sequence `w` and reply sequence `t`.
* `evs M β` — the events of an execution: one input event per receive (the
  receive sequence so far), one output event per reply (the reply sequence so
  far), nothing for an internal action.
* `exec_run` — every execution is a run of the projected spec, action by
  action, ending in the canonical state for its receive and reply sequences
  (`Canon`).  `evs_inj` — the events determine the trace.
* `relMono` — Relational Monotonicity always holds (input-enabledness).
* `consistent_iff` — the projected spec is consistent iff, at every receive
  sequence, any two reply sequences of its fiber are one a prefix of the other.

## The automaton as a system (Def. `def:automaton-system`, Prop. `prop:automaton-system`)

* `Live M β s` — the rows an execution with schedule `β` ending in state `s`
  can still reach.  `live_closed` (the legality lemma): `Live` keeps every
  row below a kept row at the same input, so narrowing to it is a commitment.
* `narrow M X` — the commitment that keeps only the rows in `X`;
  `basis M` — the canonical commitments and `narrow M (Live M β s)` for
  finite executions.
* `Corr M l β` — the history `l` (commitment events dropped) carries the
  receives and replies of the schedule `β` in order; one input event may
  carry several consecutive receives (or none).
* `sys M : Guard.Sys (spec M)` — the system: after a local history, its
  strategy allows the output events and the narrowing that some matching
  execution allows next.
* `sound`, `complete`, `catchup` — every history of the system corresponds
  to an execution whose reachable rows its table keeps; every execution
  corresponds to a history whose table is exactly those rows; one commitment
  event always brings the table down to them.
* `sys_consistent_iff` — the system's histories are consistent (confluent
  under any continuation) iff the automaton is confluent (`Confluent`).
* `consistent_of_confluent`, `confluent_iff_diff` — a confluent automaton
  has a consistent projected spec; confluence fails exactly when the rows the
  automaton's commitments removed from the canonical tables cover every
  common row.

## Examples

* `Poll` — closing the polls early: consistent projected spec, not confluent;
  a run of the projected spec that no execution produces.
* `Hid` / `Vis` — the same traces, but an internal choice of `Hid` appears as
  a commitment event that `Vis`'s system never makes.
* `Race` / `Queue` — a counter whose report races with arrivals (inconsistent
  projected spec) and one that records the count at each arrival (consistent
  projected spec, confluent automaton).
* `realizability_alone`, `domination_alone` — neither obligation of
  Prop. `prop:declared-specification` suffices alone.
-/

namespace CC
namespace IOT

open Classical

/-! ## Sequences ordered by prefix -/

/-- Finite sequences of actions satisfying `p`. -/
structure Wd {A : Type} (p : A → Prop) where
  val : List A
  prop : ∀ a ∈ val, p a

theorem Wd.ext {A : Type} {p : A → Prop} {a b : Wd p} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

/-- The prefix order. -/
instance Wd.instPO {A : Type} (p : A → Prop) : PO (Wd p) where
  le a b := a.val <+: b.val
  refl a := List.prefix_refl a.val
  trans h1 h2 := List.IsPrefix.trans h1 h2
  antisymm {_ _} h1 h2 := Wd.ext (List.IsPrefix.eq_of_length h1
    (Nat.le_antisymm (List.IsPrefix.length_le h1) (List.IsPrefix.length_le h2)))

theorem Wd.le_iff {A : Type} {p : A → Prop} {a b : Wd p} : a ≼ b ↔ a.val <+: b.val := Iff.rfl

theorem prefix_comparable {A : Type} {a b c : List A} (ha : a <+: c) (hb : b <+: c) :
    a <+: b ∨ b <+: a :=
  List.prefix_or_prefix_of_prefix ha hb

variable {A : Type} (M : IOA.Automaton A)

/-! ## Receive and reply sequences -/

/-- The receive sequence of a schedule: its input actions, in order. -/
noncomputable def recvs (β : List A) : List A := β.filter fun a => decide (M.sig.inp a)

/-- The reply sequence of a schedule: its output actions, in order. -/
noncomputable def replies (β : List A) : List A := β.filter fun a => decide (M.sig.out a)

/-- Receive sequences. -/
abbrev InS := Wd M.sig.inp
/-- Reply sequences. -/
abbrev OutS := Wd M.sig.out

variable {M}

theorem recvs_append (β γ : List A) : recvs M (β ++ γ) = recvs M β ++ recvs M γ :=
  List.filter_append _ _

theorem replies_append (β γ : List A) : replies M (β ++ γ) = replies M β ++ replies M γ :=
  List.filter_append _ _

theorem mem_recvs {β : List A} {a : A} : a ∈ recvs M β ↔ a ∈ β ∧ M.sig.inp a := by
  simp [recvs, List.mem_filter]

theorem mem_replies {β : List A} {a : A} : a ∈ replies M β ↔ a ∈ β ∧ M.sig.out a := by
  simp [replies, List.mem_filter]

theorem recvs_nil : recvs M [] = [] := rfl
theorem replies_nil : replies M [] = [] := rfl

theorem recvs_single_of {a : A} (h : M.sig.inp a) : recvs M [a] = [a] := by
  simp [recvs, h]

theorem recvs_single_not {a : A} (h : ¬ M.sig.inp a) : recvs M [a] = [] := by
  simp [recvs, h]

theorem replies_single_of {a : A} (h : M.sig.out a) : replies M [a] = [a] := by
  simp [replies, h]

theorem replies_single_not {a : A} (h : ¬ M.sig.out a) : replies M [a] = [] := by
  simp [replies, h]

/-- A list of input actions is its own receive sequence. -/
theorem recvs_of_inputs {d : List A} (h : ∀ a ∈ d, M.sig.inp a) : recvs M d = d := by
  unfold recvs
  rw [List.filter_eq_self]
  intro a ha; simpa using h a ha

/-- A list of input actions has no replies. -/
theorem replies_of_inputs {d : List A} (h : ∀ a ∈ d, M.sig.inp a) : replies M d = [] := by
  unfold replies
  rw [List.filter_eq_nil_iff]
  intro a ha; simpa using M.sig.inp_out a (h a ha)

theorem recvs_recvs (β : List A) : recvs M (recvs M β) = recvs M β :=
  recvs_of_inputs fun _ ha => (mem_recvs.1 ha).2

variable (M)

/-- The receive sequence of `β`, as an element of `InS M`. -/
noncomputable def inW (β : List A) : InS M := ⟨recvs M β, fun _ ha => (mem_recvs.1 ha).2⟩

/-- The reply sequence of `β`, as an element of `OutS M`. -/
noncomputable def outW (β : List A) : OutS M := ⟨replies M β, fun _ ha => (mem_replies.1 ha).2⟩

variable {M}

theorem inW_val (β : List A) : (inW M β).val = recvs M β := rfl
theorem outW_val (β : List A) : (outW M β).val = replies M β := rfl

theorem inW_le_append (β γ : List A) : inW M β ≼ inW M (β ++ γ) := by
  show recvs M β <+: recvs M (β ++ γ)
  rw [recvs_append]; exact List.prefix_append _ _

theorem outW_le_append (β γ : List A) : outW M β ≼ outW M (β ++ γ) := by
  show replies M β <+: replies M (β ++ γ)
  rw [replies_append]; exact List.prefix_append _ _

theorem inW_nil_le (w : InS M) : inW M [] ≼ w := List.nil_prefix
theorem outW_nil_le (t : OutS M) : outW M [] ≼ t := List.nil_prefix

theorem inW_snoc_not {β : List A} {a : A} (h : ¬ M.sig.inp a) : inW M (β ++ [a]) = inW M β :=
  Wd.ext (by simp [inW_val, recvs_append, recvs_single_not h])

theorem outW_snoc_not {β : List A} {a : A} (h : ¬ M.sig.out a) : outW M (β ++ [a]) = outW M β :=
  Wd.ext (by simp [outW_val, replies_append, replies_single_not h])

/-! ## Executions on inputs -/

/-- Input-enabledness: every list of input actions can be received from any
state. -/
theorem run_inputs : ∀ (s : M.St) (d : List A), (∀ a ∈ d, M.sig.inp a) → ∃ t, IOA.Run M s d t
  | s, [], _ => ⟨s, .nil s⟩
  | s, a :: d, h => by
    obtain ⟨s', hs'⟩ := M.input_enabled s a (h a (List.mem_cons_self ..))
    obtain ⟨t, ht⟩ := run_inputs s' d fun b hb => h b (List.mem_cons_of_mem _ hb)
    exact ⟨t, .cons hs' ht⟩

theorem execution_append {β γ : List A} {s t : M.St} (h : IOA.Execution M β s)
    (hr : IOA.Run M s γ t) : IOA.Execution M (β ++ γ) t := by
  obtain ⟨s0, hs0, h0⟩ := h
  exact ⟨s0, hs0, (IOA.run_append_iff β γ).2 ⟨s, h0, hr⟩⟩

theorem execution_snoc {β : List A} {a : A} {s t : M.St} (h : IOA.Execution M β s)
    (ht : M.trans s a t) : IOA.Execution M (β ++ [a]) t :=
  IOA.execution_snoc_iff.2 ⟨s, h, ht⟩

/-- Every action of a step is an input, output, or internal action. -/
theorem act_cases {s t : M.St} {a : A} (h : M.trans s a t) :
    M.sig.inp a ∨ M.sig.out a ∨ M.sig.int a := M.trans_acts s a t h

/-! ## The projected spec -/

variable (M)

/-- The rows of the projection: `(w, t)` is a row when some finite execution
has receive sequence `w` and reply sequence `t`. -/
def Row (w : InS M) (t : OutS M) : Prop :=
  ∃ β s, IOA.Execution M β s ∧ inW M β = w ∧ outW M β = t

theorem row_total (w : InS M) : ∃ t, Row M w t := by
  obtain ⟨s0, hs0⟩ := M.start_nonempty
  obtain ⟨t, ht⟩ := run_inputs s0 w.val w.prop
  exact ⟨outW M w.val, w.val, t, ⟨s0, hs0, ht⟩, Wd.ext (recvs_of_inputs w.prop), rfl⟩

/-- **The projected spec** (Def. `def:projection`). -/
def spec : Spec (InS M) (OutS M) where
  P := Row M
  total := row_total M

variable {M}

theorem spec_row {β : List A} {s : M.St} (h : IOA.Execution M β s) :
    (spec M).P (inW M β) (outW M β) := ⟨β, s, h, rfl, rfl⟩

/-! ## Executions are runs of the projected spec -/

variable (M)

/-- The events of the actions `γ` following the prefix `pre`. -/
noncomputable def evsFrom : List A → List A → List (Event (InS M) (OutS M))
  | _, [] => []
  | pre, a :: r =>
    (if M.sig.inp a then [Event.input (inW M (pre ++ [a]))]
     else if M.sig.out a then [Event.output (outW M (pre ++ [a]))] else []) ++
      evsFrom (pre ++ [a]) r

/-- The events of an execution: an input event per receive, carrying the
receive sequence so far; an output event per reply, carrying the reply
sequence so far; nothing for an internal action. -/
noncomputable def evs (β : List A) : List (Event (InS M) (OutS M)) := evsFrom M [] β

theorem evsFrom_append : ∀ (pre γ δ : List A),
    evsFrom M pre (γ ++ δ) = evsFrom M pre γ ++ evsFrom M (pre ++ γ) δ
  | pre, [], δ => by simp [evsFrom]
  | pre, a :: γ, δ => by
    simp only [List.cons_append, evsFrom, List.append_assoc]
    rw [evsFrom_append (pre ++ [a]) γ δ]
    simp

/-- The events of one action: an input event carrying the receive sequence so
far, an output event carrying the reply sequence so far, or nothing for an
internal action. -/
theorem evsFrom_cons (pre : List A) (a : A) (r : List A) :
    (M.sig.inp a → evsFrom M pre (a :: r) = .input (inW M (pre ++ [a])) :: evsFrom M (pre ++ [a]) r) ∧
    (M.sig.out a → evsFrom M pre (a :: r) = .output (outW M (pre ++ [a])) :: evsFrom M (pre ++ [a]) r) ∧
    (M.sig.int a → evsFrom M pre (a :: r) = evsFrom M (pre ++ [a]) r) := by
  refine ⟨fun h => by simp [evsFrom, h], fun h => ?_, fun h => ?_⟩
  · have hi : ¬ M.sig.inp a := fun h' => M.sig.inp_out a h' h
    simp [evsFrom, h, hi]
  · have hi : ¬ M.sig.inp a := fun h' => M.sig.inp_int a h' h
    have ho : ¬ M.sig.out a := fun h' => M.sig.out_int a h' h
    simp [evsFrom, hi, ho]

/-- The canonical table after an execution: the rows at receive sequences
extending its receive sequence with reply sequences extending its reply
sequence. -/
def Canon (β : List A) : Table (InS M) (OutS M) :=
  fun k u => (spec M).P k u ∧ inW M β ≼ k ∧ outW M β ≼ u

variable {M}

/-- The state reached by the events of `pre` is the canonical state for its
receive and reply sequences. -/
def Inv (pre : List A) (σ : State (spec M)) : Prop :=
  σ.cur = inW M pre ∧ ∀ k u, σ.R k u ↔ Canon M pre k u

theorem inv_step {pre γ : List A} {s t : M.St} (hx : IOA.Execution M pre s)
    (hr : IOA.Run M s γ t) {σ : State (spec M)} (hσ : Inv pre σ) :
    ∃ σ', Exec σ (evsFrom M pre γ) σ' ∧ Inv (pre ++ γ) σ' := by
  induction hr generalizing pre σ with
  | nil s => exact ⟨σ, .nil σ, by simpa using hσ⟩
  | @cons s s' t a β htr _ ih =>
    have hx' := execution_snoc hx htr
    have heq : pre ++ a :: β = (pre ++ [a]) ++ β := by simp
    rcases act_cases htr with hi | ho | hn
    · -- an input action
      have hno : ¬ M.sig.out a := M.sig.inp_out a hi
      have hrow : σ.R (inW M (pre ++ [a])) (outW M pre) := by
        rw [hσ.2]
        refine ⟨?_, inW_le_append _ _, PO.refl _⟩
        rw [← outW_snoc_not hno]; exact spec_row hx'
      let τ := Guard.inState σ (inW M (pre ++ [a])) (outW M pre) hrow
      have hst : Step σ (.input (inW M (pre ++ [a]))) τ := Step.input σ τ _ ⟨_, hrow⟩ rfl rfl
      have hτ : Inv (pre ++ [a]) τ := by
        refine ⟨rfl, fun k u => ?_⟩
        show (σ.R k u ∧ _) ↔ _
        rw [hσ.2]
        unfold Canon
        rw [outW_snoc_not hno]
        exact ⟨fun ⟨⟨h1, _, h3⟩, h4⟩ => ⟨h1, h4, h3⟩,
          fun ⟨h1, h2, h3⟩ => ⟨⟨h1, PO.trans (inW_le_append pre [a]) h2, h3⟩, h2⟩⟩
      obtain ⟨σ', h1, h2⟩ := ih hx' hτ
      refine ⟨σ', ?_, by rw [heq]; exact h2⟩
      simp only [evsFrom, ↓reduceIte, hi, List.singleton_append]
      exact .cons hst h1
    · -- an output action
      have hni : ¬ M.sig.inp a := fun h => M.sig.inp_out a h ho
      have hrow : σ.R σ.cur (outW M (pre ++ [a])) := by
        rw [hσ.2, hσ.1]
        refine ⟨?_, PO.refl _, outW_le_append _ _⟩
        rw [← inW_snoc_not hni]; exact spec_row hx'
      let τ := outState σ (outW M (pre ++ [a])) hrow
      have hst : Step σ (.output (outW M (pre ++ [a]))) τ := step_output_outState hrow
      have hτ : Inv (pre ++ [a]) τ := by
        refine ⟨by show σ.cur = _; rw [hσ.1, inW_snoc_not hni], fun k u => ?_⟩
        show (σ.R k u ∧ _) ↔ _
        rw [hσ.2]
        unfold Canon
        rw [inW_snoc_not hni]
        exact ⟨fun ⟨⟨h1, h2, _⟩, h4⟩ => ⟨h1, h2, h4⟩,
          fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2, PO.trans (outW_le_append pre [a]) h3⟩, h3⟩⟩
      obtain ⟨σ', h1, h2⟩ := ih hx' hτ
      refine ⟨σ', ?_, by rw [heq]; exact h2⟩
      simp only [evsFrom, ↓reduceIte, hni, ho, List.singleton_append]
      exact .cons hst h1
    · -- an internal action
      have hni : ¬ M.sig.inp a := fun h => M.sig.inp_int a h hn
      have hno : ¬ M.sig.out a := fun h => M.sig.out_int a h hn
      have hτ : Inv (pre ++ [a]) σ := by
        refine ⟨by rw [hσ.1, inW_snoc_not hni], fun k u => ?_⟩
        rw [hσ.2]; unfold Canon; rw [inW_snoc_not hni, outW_snoc_not hno]
      obtain ⟨σ', h1, h2⟩ := ih hx' hτ
      refine ⟨σ', ?_, by rw [heq]; exact h2⟩
      simp only [evsFrom, ↓reduceIte, hni, hno, List.nil_append]
      exact h1

/-- **Executions are runs** (Prop. `prop:projection`).  The events of every
finite execution form a run of the projected spec from the canonical state at
the empty receive sequence, one event per receive or reply; it ends at the
execution's receive sequence, keeping exactly the rows at extensions of its
receive sequence whose reply sequences extend its own. -/
theorem exec_run {β : List A} {s : M.St} (h : IOA.Execution M β s) :
    ∃ σ, Exec (canon (spec M) (inW M [])) (evs M β) σ ∧ σ.cur = inW M β ∧
      ∀ k u, σ.R k u ↔ Canon M β k u := by
  obtain ⟨s0, hs0, hr⟩ := h
  have h0 : Inv ([] : List A) (canon (spec M) (inW M [])) :=
    ⟨rfl, fun k u => ⟨fun ⟨h1, h2⟩ => ⟨h1, h2, outW_nil_le u⟩, fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩⟩⟩
  obtain ⟨σ, h1, h2⟩ := inv_step (pre := []) ⟨s0, hs0, .nil s0⟩ hr h0
  exact ⟨σ, h1, by simpa using h2.1, by simpa using h2.2⟩

/-- The action an event carries: the last receive or reply in its value. -/
def lastAct : Event (InS M) (OutS M) → Option A
  | .input w => w.val.getLast?
  | .output t => t.val.getLast?

variable (M) in
/-- The trace of a schedule: its external actions. -/
noncomputable def trace (β : List A) : List A :=
  β.filter fun a => decide (M.sig.inp a ∨ M.sig.out a)

theorem lastAct_evsFrom : ∀ (pre γ : List A),
    (evsFrom M pre γ).filterMap lastAct = trace M γ
  | _, [] => rfl
  | pre, a :: r => by
    have ih := lastAct_evsFrom (pre ++ [a]) r
    by_cases hi : M.sig.inp a
    · simp only [evsFrom, ↓reduceIte, hi, List.singleton_append, List.filterMap_cons, ih]
      simp [trace, hi, lastAct, inW_val, recvs_append, recvs_single_of hi]
    · by_cases ho : M.sig.out a
      · simp only [evsFrom, ↓reduceIte, hi, ho, List.singleton_append, List.filterMap_cons, ih]
        simp [trace, ho, lastAct, outW_val, replies_append, replies_single_of ho]
      · simp only [evsFrom, ↓reduceIte, hi, ho, List.nil_append, ih]
        simp [trace, hi, ho]

/-- The events of an execution determine its trace. -/
theorem evs_inj {β β' : List A} (h : evs M β = evs M β') : trace M β = trace M β' := by
  have h1 := lastAct_evsFrom (M := M) [] β
  have h2 := lastAct_evsFrom (M := M) [] β'
  unfold evs at h
  rw [← h1, ← h2, h]

/-! ## Consistency of the projected spec -/

/-- **Relational Monotonicity always holds**: an execution can receive any
further requests before replying again. -/
theorem relMono : (spec M).RelMono := by
  rintro i j o ⟨d, hd⟩ ⟨β, s, hx, rfl, rfl⟩
  have hdi : ∀ a ∈ d, M.sig.inp a := fun a ha => j.prop a (hd ▸ List.mem_append_right _ ha)
  obtain ⟨t, ht⟩ := run_inputs s d hdi
  refine ⟨outW M β, ⟨β ++ d, t, execution_append hx ht, ?_, ?_⟩, PO.refl _⟩
  · exact Wd.ext (by rw [inW_val, recvs_append, recvs_of_inputs hdi]; exact hd)
  · exact Wd.ext (by rw [outW_val, outW_val, replies_append, replies_of_inputs hdi]; simp)

/-- A finite list of pairwise comparable outputs has a largest element. -/
theorem max_of_comparable {F : OutS M → Prop}
    (hc : ∀ t t', F t → F t' → t ≼ t' ∨ t' ≼ t) :
    ∀ X : List (OutS M), X ≠ [] → (∀ x ∈ X, F x) → ∃ u ∈ X, ∀ x ∈ X, x ≼ u
  | [x], _, _ => ⟨x, by simp, fun y hy => by simp at hy; subst hy; exact PO.refl _⟩
  | x :: y :: X, _, hX => by
    obtain ⟨u, hu, hall⟩ := max_of_comparable hc (y :: X) (by simp)
      fun z hz => hX z (List.mem_cons_of_mem _ hz)
    rcases hc x u (hX x (List.mem_cons_self ..)) (hX u (List.mem_cons_of_mem _ hu)) with h | h
    · refine ⟨u, List.mem_cons_of_mem _ hu, fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact h
      · exact hall z hz
    · refine ⟨x, List.mem_cons_self .., fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact PO.refl _
      · exact PO.trans (hall z hz) h

/-- **Consistency of the projected spec** (Prop. `prop:projection`): the
projected spec is consistent exactly when, at every receive sequence, any two
reply sequences in the fiber are one a prefix of the other. -/
theorem consistent_iff : (spec M).Consistent ↔
    ∀ w t t', (spec M).P w t → (spec M).P w t' → t ≼ t' ∨ t' ≼ t := by
  rw [complete_calm, liftedMono_iff_relMono_directed]
  constructor
  · rintro ⟨_, hD⟩ w t t' ht ht'
    obtain ⟨u, _, hall⟩ := hD w [t, t'] (by simp) (by simp [ht, ht'])
    exact prefix_comparable (hall t (by simp)) (hall t' (by simp))
  · intro hc
    refine ⟨relMono, fun w X hne hX => ?_⟩
    obtain ⟨u, hu, hall⟩ := max_of_comparable (hc w) X hne hX
    exact ⟨u, hX u hu, hall⟩


/-! ## Rows an execution can still reach -/

variable (M) in
/-- The rows an execution with schedule `β`, ending in state `s`, can still
reach: the receive and reply sequences of its continuations from `s`. -/
def Live (β : List A) (s : M.St) : Table (InS M) (OutS M) :=
  fun k u => ∃ γ t, IOA.Run M s γ t ∧ inW M (β ++ γ) = k ∧ outW M (β ++ γ) = u

theorem live_self (β : List A) (s : M.St) : Live M β s (inW M β) (outW M β) :=
  ⟨[], s, .nil s, by simp, by simp⟩

theorem live_row {β : List A} {s : M.St} (hx : IOA.Execution M β s) {k : InS M} {u : OutS M}
    (h : Live M β s k u) : (spec M).P k u := by
  obtain ⟨γ, t, hr, rfl, rfl⟩ := h
  exact spec_row (execution_append hx hr)

theorem live_above {β : List A} {s : M.St} {k : InS M} {u : OutS M}
    (h : Live M β s k u) : inW M β ≼ k ∧ outW M β ≼ u := by
  obtain ⟨γ, t, _, rfl, rfl⟩ := h
  exact ⟨inW_le_append _ _, outW_le_append _ _⟩

/-- Rows reachable after a further run were reachable before it. -/
theorem live_run {β δ : List A} {s s' : M.St} (hr : IOA.Run M s δ s') {k : InS M} {u : OutS M}
    (h : Live M (β ++ δ) s' k u) : Live M β s k u := by
  obtain ⟨γ, t, hr', rfl, rfl⟩ := h
  exact ⟨δ ++ γ, t, (IOA.run_append_iff δ γ).2 ⟨s', hr, hr'⟩, by simp, by simp⟩

theorem live_step {β : List A} {a : A} {s s' : M.St} (ht : M.trans s a s') {k : InS M}
    {u : OutS M} (h : Live M (β ++ [a]) s' k u) : Live M β s k u :=
  live_run (.cons ht (.nil s')) h

/-- A schedule can be cut where its replies reach any prefix of its reply
sequence. -/
theorem cut_replies : ∀ (γ e : List A), e <+: replies M γ →
    ∃ γ₁ γ₂, γ = γ₁ ++ γ₂ ∧ replies M γ₁ = e
  | γ, [], _ => ⟨[], γ, rfl, rfl⟩
  | [], b :: e, h => by simp [replies_nil] at h
  | a :: r, b :: e, h => by
    by_cases ho : M.sig.out a
    · have hr : replies M (a :: r) = a :: replies M r := by
        simp [replies, ho]
      rw [hr, List.cons_prefix_cons] at h
      obtain ⟨rfl, h2⟩ := h
      obtain ⟨γ₁, γ₂, rfl, he⟩ := cut_replies r e h2
      exact ⟨b :: γ₁, γ₂, rfl, by simp [replies, ho] at he ⊢; exact he⟩
    · have hr : replies M (a :: r) = replies M r := by
        simp [replies, ho]
      rw [hr] at h
      obtain ⟨γ₁, γ₂, rfl, he⟩ := cut_replies r (b :: e) h
      exact ⟨a :: γ₁, γ₂, rfl, by simp [replies, ho] at he ⊢; exact he⟩

/-- **Legality lemma.**  If an execution can reach `(k, w)`, it can reach
`(k, u)` for every `u` below `w` that extends its reply sequence: it stops
replying at `u` and receives the rest of `k`. -/
theorem live_closed {β : List A} {s : M.St} {k : InS M} {u w : OutS M}
    (hw : Live M β s k w) (hlo : outW M β ≼ u) (huw : u ≼ w) : Live M β s k u := by
  obtain ⟨γ, t, hr, rfl, rfl⟩ := hw
  obtain ⟨e, he⟩ := hlo
  have hpre : e <+: replies M γ := by
    have h' := huw
    change u.val <+: replies M (β ++ γ) at h'
    rw [← he, replies_append] at h'
    exact (List.prefix_append_right_inj _).1 h'
  obtain ⟨γ₁, γ₂, rfl, he1⟩ := cut_replies γ e hpre
  obtain ⟨m, h1, _⟩ := (IOA.run_append_iff γ₁ γ₂).1 hr
  have hd : ∀ a ∈ recvs M γ₂, M.sig.inp a := fun a ha => (mem_recvs.1 ha).2
  obtain ⟨t', ht'⟩ := run_inputs m (recvs M γ₂) hd
  refine ⟨γ₁ ++ recvs M γ₂, t', (IOA.run_append_iff _ _).2 ⟨m, h1, ht'⟩, ?_, ?_⟩
  · apply Wd.ext
    simp only [inW_val, recvs_append, recvs_recvs]
  · apply Wd.ext
    rw [outW_val, ← he, replies_append, replies_append, replies_of_inputs hd, he1]
    simp [outW_val]

/-! ## The narrowing commitment -/

/-- The state keeping only the rows of `σ` in `X`. -/
def narrowState (σ : State (spec M)) (X : Table (InS M) (OutS M))
    (h : ∃ o, σ.R σ.cur o ∧ X σ.cur o) : State (spec M) where
  cur := σ.cur
  R k u := σ.R k u ∧ X k u
  sub k u h' := σ.sub k u h'.1
  hasCur := by obtain ⟨o, h1, h2⟩ := h; exact ⟨o, h1, h2⟩
  above k u h' := σ.above k u h'.1

/-- When narrowing `σ` to `X` is a commitment: it removes a row, keeps a row
at the current input, and removes no row below a kept row at the same
input. -/
def NarrowOK (σ : State (spec M)) (X : Table (InS M) (OutS M)) : Prop :=
  (∃ k u, σ.R k u ∧ ¬ X k u) ∧ (∃ o, σ.R σ.cur o ∧ X σ.cur o) ∧
    ∀ k u w, σ.R k u → ¬ X k u → σ.R k w → X k w → ¬ u ≼ w

variable (M) in
/-- **The narrowing commitment** to `X`: keep only the rows in `X`. -/
noncomputable def narrow (X : Table (InS M) (OutS M)) : Commitment (spec M) where
  app σ := if h : NarrowOK σ X then some (narrowState σ X h.2.1) else none
  cur_eq σ τ h := by
    split at h
    · cases h; rfl
    · cases h
  sub σ τ h k u hu := by
    split at h
    · cases h; exact hu.1
    · cases h
  removes σ τ h := by
    split at h
    · rename_i hok; cases h
      obtain ⟨k, u, h1, h2⟩ := hok.1
      exact ⟨k, u, h1, fun h' => h2 h'.2⟩
    · cases h
  unsubsumed σ τ h k u w hu hnu hw := by
    split at h
    · rename_i hok; cases h
      exact hok.2.2 k u w hu (fun hx => hnu ⟨hu, hx⟩) hw.1 hw.2
    · cases h

theorem narrow_app {X : Table (InS M) (OutS M)} {σ τ : State (spec M)}
    (h : (narrow M X).app σ = some τ) : ∀ k u, τ.R k u ↔ σ.R k u ∧ X k u := by
  simp only [narrow] at h
  split at h
  · cases h; exact fun _ _ => Iff.rfl
  · cases h

theorem narrow_app_of {X : Table (InS M) (OutS M)} {σ : State (spec M)} (h : NarrowOK σ X) :
    (narrow M X).app σ = some (narrowState σ X h.2.1) := by
  simp only [narrow, h, ↓reduceDIte]

variable (M) in
/-- **The basis**: the canonical commitments, and the narrowing to the rows a
finite execution can still reach. -/
def basis : CommitmentBasis (spec M) := fun c =>
  (∃ o, c = canonicalCommitment o) ∨ ∃ β s, IOA.Execution M β s ∧ c = narrow M (Live M β s)

/-! ## Histories and executions -/

variable (M) in
/-- `Corr M l β`: the input and output events of the history `l` carry the
receives and replies of the schedule `β`, in order.  One input event may
carry several consecutive receives, or none; commitment events and internal
actions carry nothing. -/
inductive Corr : List (SEvent (spec M)) → List A → Prop
  | nil : Corr [] []
  | input {l : List (SEvent (spec M))} {β d : List A} {j : InS M} :
      Corr l β → j.val = recvs M β ++ d → Corr (l ++ [.input j]) (β ++ d)
  | output {l : List (SEvent (spec M))} {β : List A} {b : A} :
      Corr l β → M.sig.out b → Corr (l ++ [.output (outW M (β ++ [b]))]) (β ++ [b])
  | commit {l : List (SEvent (spec M))} {β : List A} {γ : List (Commitment (spec M))} :
      Corr l β → Corr (l ++ [.commitment γ]) β
  | internal {l : List (SEvent (spec M))} {β : List A} {a : A} :
      Corr l β → M.sig.int a → Corr l (β ++ [a])

/-- The current input after a history, starting from `c`. -/
def curStep (c : InS M) : SEvent (spec M) → InS M
  | .input j => j
  | _ => c

/-- The last output emitted by a history, starting from `o`. -/
def outStep (o : OutS M) : SEvent (spec M) → OutS M
  | .output t => t
  | _ => o

theorem sysExec_cur {B : CommitmentBasis (spec M)} {σ0 σ : State (spec M)}
    {l : List (SEvent (spec M))} (h : SysExec B σ0 l σ) : σ.cur = l.foldl curStep σ0.cur := by
  induction h with
  | nil => rfl
  | @cons σ τ ρ e es hs _ ih =>
    rw [ih, List.foldl_cons]
    congr 1
    cases hs with
    | input hs => cases hs with | input _ _ _ h2 _ => exact h2
    | output hs _ => cases hs with | output _ _ _ h2 _ => exact h2
    | commitment _ _ hγ => exact hγ.cur_eq

theorem sysExec_out {B : CommitmentBasis (spec M)} {σ0 σ : State (spec M)}
    {l : List (SEvent (spec M))} (h : SysExec B σ0 l σ) :
    ∀ o0 : OutS M, (∀ k u, σ0.R k u → o0 ≼ u) → ∀ k u, σ.R k u → l.foldl outStep o0 ≼ u := by
  induction h with
  | nil => exact fun o0 h => h
  | @cons σ τ ρ e es hs _ ih =>
    intro o0 h0
    rw [List.foldl_cons]
    apply ih
    intro k u hu
    cases hs with
    | input hs => exact h0 k u (step_sub hs k u hu)
    | output hs _ =>
      cases hs with
      | output _ _ _ _ hR => rw [hR] at hu; exact hu.2
    | commitment _ _ hγ => exact h0 k u (hγ.sub k u hu)

theorem corr_cur {l : List (SEvent (spec M))} {β : List A} (h : Corr M l β) :
    l.foldl curStep (inW M []) = inW M β := by
  induction h with
  | nil => rfl
  | @input l β d j _ hj ih =>
    have hdi : ∀ a ∈ d, M.sig.inp a := fun a ha => j.prop a (hj ▸ List.mem_append_right _ ha)
    rw [List.foldl_append]; simp only [List.foldl_cons, List.foldl_nil, curStep]
    apply Wd.ext
    rw [hj, inW_val, recvs_append, recvs_of_inputs hdi]
  | output _ hb ih =>
    rw [List.foldl_append]; simp only [List.foldl_cons, List.foldl_nil, curStep]
    rw [ih, inW_snoc_not fun h => M.sig.inp_out _ h hb]
  | commit _ ih => rw [List.foldl_append]; simp only [List.foldl_cons, List.foldl_nil, curStep]; exact ih
  | internal _ ha ih => rw [ih, inW_snoc_not fun h => M.sig.inp_int _ h ha]

theorem corr_out {l : List (SEvent (spec M))} {β : List A} (h : Corr M l β) :
    l.foldl outStep (outW M []) = outW M β := by
  induction h with
  | nil => rfl
  | @input l β d j _ hj ih =>
    have hdi : ∀ a ∈ d, M.sig.inp a := fun a ha => j.prop a (hj ▸ List.mem_append_right _ ha)
    rw [List.foldl_append]; simp only [List.foldl_cons, List.foldl_nil, outStep]
    rw [ih]
    apply Wd.ext
    rw [outW_val, outW_val, replies_append, replies_of_inputs hdi, List.append_nil]
  | output _ _ ih => rw [List.foldl_append]; simp only [List.foldl_cons, List.foldl_nil, outStep]
  | commit _ ih => rw [List.foldl_append]; simp only [List.foldl_cons, List.foldl_nil, outStep]; exact ih
  | internal _ ha ih => rw [ih, outW_snoc_not fun h => M.sig.out_int _ h ha]

/-! ## The system of an automaton -/

/-- An execution *matches* a history ending in state `σ`: the history carries
its receives and replies, and `σ` keeps every row the execution can still
reach. -/
def Matches (l : List (SEvent (spec M))) (σ : State (spec M)) (β : List A) (s : M.St) : Prop :=
  IOA.Execution M β s ∧ Corr M l β ∧ ∀ k u, Live M β s k u → σ.R k u

variable (M) in
/-- **The system of an automaton** (Def. `def:automaton-system`).  One
participant runs over the projected spec with `basis M`.  After a local
history, its strategy allows an output event when some matching execution can
send the reply next, and the narrowing to the rows a matching execution can
still reach.  Input events come from the environment. -/
noncomputable def sys : Guard.Sys (spec M) where
  basis := basis M
  strat _ l e := ∃ σ β s, SysExec (basis M) (canon (spec M) (inW M [])) l σ ∧
    Matches l σ β s ∧
    match e with
    | .output o => ∃ b s', M.trans s b s' ∧ M.sig.out b ∧ o = outW M (β ++ [b])
    | .commitment γ => γ = [narrow M (Live M β s)]
    | .input _ => True

/-- A produced history ends in a state whose rows extend the history's last
output and current input. -/
theorem produced_cur_out {l : List (SEvent (spec M))} {σ : State (spec M)}
    (h : SysExec (basis M) (canon (spec M) (inW M [])) l σ) :
    σ.cur = l.foldl curStep (inW M []) ∧ ∀ k u, σ.R k u → l.foldl outStep (outW M []) ≼ u :=
  ⟨sysExec_cur h, sysExec_out h _ fun _ u _ => outW_nil_le u⟩

/-- Narrowing to the reachable rows of a matching execution is a commitment
whenever it removes a row. -/
theorem narrowOK_of_matches {l : List (SEvent (spec M))} {σ : State (spec M)} {β : List A}
    {s : M.St} (hp : SysExec (basis M) (canon (spec M) (inW M [])) l σ) (hm : Matches l σ β s)
    (hs : ∃ k u, σ.R k u ∧ ¬ Live M β s k u) : NarrowOK σ (Live M β s) := by
  obtain ⟨hc, ho⟩ := produced_cur_out hp
  rw [corr_cur hm.2.1] at hc
  rw [corr_out hm.2.1] at ho
  refine ⟨hs, ⟨outW M β, ?_, ?_⟩, fun k u w hu hnu _ hw huw => hnu (live_closed hw (ho k u hu) huw)⟩
  · rw [hc]; exact hm.2.2 _ _ (live_self β s)
  · rw [hc]; exact live_self β s

theorem produces_snoc {l : List (SEvent (spec M))} {σ τ : State (spec M)} {e : SEvent (spec M)}
    (h : Guard.Produces (sys M) (inW M []) l σ) (hs : SysStep (basis M) σ e τ)
    (ha : Guard.Allowed (sys M) (inW M []) l e) :
    Guard.Produces (sys M) (inW M []) (l ++ [e]) τ :=
  ⟨Guard.sysExec_snoc h.1 hs, Guard.compliant_snoc h.2 ha⟩

theorem produces_inv {l : List (SEvent (spec M))} {e : SEvent (spec M)} {σ : State (spec M)}
    (h : Guard.Produces (sys M) (inW M []) (l ++ [e]) σ) :
    ∃ τ, Guard.Produces (sys M) (inW M []) l τ ∧ SysStep (basis M) τ e σ ∧
      Guard.Allowed (sys M) (inW M []) l e := by
  obtain ⟨hx, hc⟩ := h
  obtain ⟨τ, h1, h2⟩ := Guard.sysExec_append_inv hx
  cases h2 with
  | cons hs hr =>
    cases hr
    refine ⟨τ, ⟨h1, fun a e' b hab => hc a e' (b ++ [e]) (by rw [hab]; simp)⟩, hs,
      hc l e [] rfl⟩

theorem snoc_ind {α : Type} {p : List α → Prop} (h0 : p []) (h1 : ∀ l a, p l → p (l ++ [a])) :
    ∀ l, p l := by
  intro l
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact h0
  | cons a r ih => rw [List.reverse_cons]; exact h1 _ a ih

/-- **Soundness** (Prop. `prop:automaton-system`).  Every history of the system
is matched by an execution: the history carries its receives and replies in
order, and its table keeps every row the execution can still reach. -/
theorem sound : ∀ (l : List (SEvent (spec M))) (σ : State (spec M)),
    Guard.Produces (sys M) (inW M []) l σ → ∃ β s, Matches l σ β s := by
  refine snoc_ind (p := fun l => ∀ σ, Guard.Produces (sys M) (inW M []) l σ → ∃ β s, Matches l σ β s)
    ?_ ?_
  · intro σ h
    have := h.1; cases this
    obtain ⟨s0, hs0⟩ := M.start_nonempty
    exact ⟨[], s0, ⟨s0, hs0, .nil s0⟩, .nil, fun k u hk =>
      ⟨live_row ⟨s0, hs0, .nil s0⟩ hk, (live_above hk).1⟩⟩
  · intro l e ih σ h
    obtain ⟨τ, hτ, hs, ha⟩ := produces_inv h
    cases e with
    | input j =>
      obtain ⟨β, s, hx, hc, hl⟩ := ih τ hτ
      cases hs with
      | input hst =>
        cases hst with
        | input _ _ hrow hcur hR =>
          obtain ⟨u, hu⟩ := hrow
          have hcj : τ.cur ≼ j := τ.above _ _ hu
          rw [(produced_cur_out hτ.1).1, corr_cur hc] at hcj
          obtain ⟨d, hd⟩ := hcj
          have hdi : ∀ a ∈ d, M.sig.inp a := fun a ha => j.prop a (hd ▸ List.mem_append_right _ ha)
          obtain ⟨t, ht⟩ := run_inputs s d hdi
          refine ⟨β ++ d, t, execution_append hx ht, .input hc hd.symm, fun k u hk => ?_⟩
          rw [hR]
          refine ⟨hl k u (live_run ht hk), ?_⟩
          have := (live_above hk).1
          have hj : inW M (β ++ d) = j := Wd.ext (by rw [inW_val, recvs_append, recvs_of_inputs hdi]; exact hd)
          rw [hj] at this; exact this
    | output o =>
      obtain ⟨σ1, β, s, h1, ⟨hx, hc, hl⟩, b, s', ht, hb, rfl⟩ := ha
      have h1eq : σ1 = τ := SysExec.det h1 hτ.1
      subst h1eq
      refine ⟨β ++ [b], s', execution_snoc hx ht, .output hc hb, fun k u hk => ?_⟩
      cases hs with
      | output hst _ =>
        cases hst with
        | output _ _ _ _ hR =>
          rw [hR]
          exact ⟨hl k u (live_step ht hk), (live_above hk).2⟩
    | commitment γ =>
      obtain ⟨σ1, β, s, h1, ⟨hx, hc, hl⟩, rfl⟩ := ha
      have h1eq : σ1 = τ := SysExec.det h1 hτ.1
      subst h1eq
      refine ⟨β, s, hx, .commit hc, fun k u hk => ?_⟩
      cases hs with
      | commitment _ _ hγ =>
        cases hγ with
        | cons happ hrest =>
          cases hrest
          exact (narrow_app happ k u).2 ⟨hl k u hk, hk⟩

/-- **Catching up** (Prop. `prop:automaton-system`).  After a history matched by
an execution, one commitment event brings the table down to exactly the rows
the execution can still reach, unless it is there already. -/
theorem catchup {l : List (SEvent (spec M))} {σ : State (spec M)} {β : List A} {s : M.St}
    (hp : Guard.Produces (sys M) (inW M []) l σ) (hm : Matches l σ β s) :
    (∀ k u, σ.R k u ↔ Live M β s k u) ∨
      ∃ σ', Guard.Produces (sys M) (inW M []) (l ++ [.commitment [narrow M (Live M β s)]]) σ' ∧
        Matches (l ++ [.commitment [narrow M (Live M β s)]]) σ' β s ∧
        ∀ k u, σ'.R k u ↔ Live M β s k u := by
  by_cases hs : ∃ k u, σ.R k u ∧ ¬ Live M β s k u
  · right
    have hok := narrowOK_of_matches hp.1 hm hs
    let σ' := narrowState σ (Live M β s) hok.2.1
    have hstep : SysStep (basis M) σ (.commitment [narrow M (Live M β s)]) σ' :=
      .commitment (fun c hc => by
          simp at hc; subst hc; exact Or.inr ⟨β, s, hm.1, rfl⟩)
        (by simp) (.cons (narrow_app_of hok) (.nil _))
    have hallow : Guard.Allowed (sys M) (inW M []) l (.commitment [narrow M (Live M β s)]) :=
      ⟨σ, β, s, hp.1, hm, rfl⟩
    refine ⟨σ', produces_snoc hp hstep hallow, ⟨hm.1, .commit hm.2.1, fun k u hk => ⟨hm.2.2 k u hk, hk⟩⟩,
      fun k u => ⟨fun h => h.2, fun h => ⟨hm.2.2 k u h, h⟩⟩⟩
  · left
    intro k u
    exact ⟨fun h => Classical.byContradiction fun hn => hs ⟨k, u, h, hn⟩, hm.2.2 k u⟩

theorem upd {β : List A} {s : M.St} {l : List (SEvent (spec M))} {σ : State (spec M)}
    (hp : Guard.Produces (sys M) (inW M []) l σ) (hm : Matches l σ β s)
    (he : l.filterMap SEvent.erase = evs M β) :
    ∃ l σ, Guard.Produces (sys M) (inW M []) l σ ∧ Matches l σ β s ∧
      (∀ k u, σ.R k u ↔ Live M β s k u) ∧ l.filterMap SEvent.erase = evs M β := by
  rcases catchup hp hm with heq | ⟨σ', h1, h2, h3⟩
  · exact ⟨l, σ, hp, hm, heq, he⟩
  · refine ⟨_, σ', h1, h2, h3, ?_⟩
    rw [List.filterMap_append, he]; simp [SEvent.erase]

/-- **Completeness** (Prop. `prop:automaton-system`).  Every execution is matched
by a history of the system whose table is exactly the rows the execution can
still reach.  The history has an input event per receive, an output event per
reply, and a commitment event after each step that loses reachable rows,
internal steps included. -/
theorem complete : ∀ (β : List A) (s : M.St), IOA.Execution M β s →
    ∃ l σ, Guard.Produces (sys M) (inW M []) l σ ∧ Matches l σ β s ∧
      (∀ k u, σ.R k u ↔ Live M β s k u) ∧ l.filterMap SEvent.erase = evs M β := by
  refine snoc_ind (p := fun β => ∀ s, IOA.Execution M β s → ∃ l σ,
    Guard.Produces (sys M) (inW M []) l σ ∧ Matches l σ β s ∧ (∀ k u, σ.R k u ↔ Live M β s k u) ∧
      l.filterMap SEvent.erase = evs M β) ?_ ?_
  · intro s h
    exact upd (l := []) ⟨.nil _, Guard.compliant_nil⟩
      ⟨h, .nil, fun k u hk => ⟨live_row h hk, (live_above hk).1⟩⟩ rfl
  · intro β a ih s' h
    obtain ⟨m, hxm, ht⟩ := IOA.execution_snoc_iff.1 h
    obtain ⟨l, σ, hp, hm, heq, hev⟩ := ih m hxm
    have hevs : evs M (β ++ [a]) = evs M β ++ evsFrom M β [a] := by
      unfold evs; rw [evsFrom_append]; simp
    have hsing : IOA.Run M m [a] s' := .cons ht (.nil s')
    rcases act_cases ht with hi | ho | hn
    · have hno : ¬ M.sig.out a := M.sig.inp_out a hi
      have hrow : σ.R (inW M (β ++ [a])) (outW M β) :=
        (heq _ _).2 ⟨[a], s', hsing, rfl, outW_snoc_not hno⟩
      let τ := Guard.inState σ (inW M (β ++ [a])) (outW M β) hrow
      have hst : SysStep (basis M) σ (.input (inW M (β ++ [a]))) τ :=
        .input (Step.input σ τ _ ⟨_, hrow⟩ rfl rfl)
      refine upd (produces_snoc hp hst trivial) ⟨h, .input hm.2.1 ?_, fun k u hk => ?_⟩ ?_
      · rw [inW_val, recvs_append, recvs_single_of hi]
      · exact ⟨(heq k u).2 (live_step ht hk), (live_above hk).1⟩
      · rw [List.filterMap_append, hev, hevs]; simp [evsFrom, hi, SEvent.erase]
    · have hni : ¬ M.sig.inp a := fun h => M.sig.inp_out a h ho
      have hc : σ.cur = inW M β := by rw [(produced_cur_out hp.1).1, corr_cur hm.2.1]
      have hrow : σ.R σ.cur (outW M (β ++ [a])) := by
        rw [hc]; exact (heq _ _).2 ⟨[a], s', hsing, inW_snoc_not hni, rfl⟩
      have hst : SysStep (basis M) σ (.output (outW M (β ++ [a]))) (outState σ _ hrow) :=
        .output (step_output_outState hrow) (Or.inr (Or.inl ⟨_, rfl⟩))
      have hal : Guard.Allowed (sys M) (inW M []) l (.output (outW M (β ++ [a]))) :=
        ⟨σ, β, m, hp.1, hm, a, s', ht, ho, rfl⟩
      refine upd (produces_snoc hp hst hal) ⟨h, .output hm.2.1 ho, fun k u hk => ?_⟩ ?_
      · exact ⟨(heq k u).2 (live_step ht hk), (live_above hk).2⟩
      · rw [List.filterMap_append, hev, hevs]; simp [evsFrom, hni, ho, SEvent.erase]
    · have hni : ¬ M.sig.inp a := fun h => M.sig.inp_int a h hn
      have hno : ¬ M.sig.out a := fun h => M.sig.out_int a h hn
      refine upd hp ⟨h, .internal hm.2.1 hn, fun k u hk => (heq k u).2 (live_step ht hk)⟩ ?_
      rw [hev, hevs]; simp [evsFrom, hni, hno]

/-! ## Confluence of the automaton and of its system -/


variable (M) in
/-- **A confluent automaton** (Def. `def:confluent-automaton`): for finitely
many executions and every receive sequence extending each of theirs, some
reply sequence is reachable at it from each. -/
def Confluent : Prop :=
  ∀ fam : List (List A × M.St), (∀ e ∈ fam, IOA.Execution M e.1 e.2) →
    ∀ j : InS M, (∀ e ∈ fam, inW M e.1 ≼ j) → ∃ u, ∀ e ∈ fam, Live M e.1 e.2 j u

/-- The histories of the system of `M`. -/
def SysRun (σ : State (spec M)) : Prop := ∃ l, Guard.Produces (sys M) (inW M []) l σ

theorem matches_cur {l : List (SEvent (spec M))} {σ : State (spec M)} {β : List A} {s : M.St}
    (hp : Guard.Produces (sys M) (inW M []) l σ) (hm : Matches l σ β s) : σ.cur = inW M β := by
  rw [(produced_cur_out hp.1).1, corr_cur hm.2.1]

/-- **The system is confluent exactly when the automaton is**
(Prop. `prop:automaton-system`): every finite family of the system's
histories can be continued, under any commitments, to a common state at every
common extension of their current inputs, exactly when the automaton is
confluent. -/
theorem sys_consistent_iff : Guard.SysConsistent (SysRun (M := M)) ↔ Confluent M := by
  constructor
  · intro hS fam hx j hj
    have hch : ∀ e ∈ fam, ∃ σ : State (spec M), (∃ l, Guard.Produces (sys M) (inW M []) l σ ∧
        Matches l σ e.1 e.2) ∧ ∀ k u, σ.R k u ↔ Live M e.1 e.2 k u := by
      intro e he
      obtain ⟨l, σ, h1, h2, h3, _⟩ := complete e.1 e.2 (hx e he)
      exact ⟨σ, ⟨l, h1, h2⟩, h3⟩
    obtain ⟨L, hL1, hL2⟩ := choose_list' fam hch
    obtain ⟨τ, hτ, hall⟩ := hS (L.map Prod.snd)
      (fun σ hσ => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hσ
        obtain ⟨⟨l, h1, _⟩, _⟩ := hL2 q hq
        exact ⟨l, h1⟩) j
      (fun σ hσ => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hσ
        obtain ⟨⟨l, h1, h2⟩, _⟩ := hL2 q hq
        rw [matches_cur h1 h2]
        exact hj q.1 (hL1 ▸ List.mem_map_of_mem hq))
    obtain ⟨u, _, hsurv⟩ := (Dist.sysConfluentAt_iff (L.map Prod.snd) j (fun σ hσ => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hσ
        obtain ⟨⟨l, h1, h2⟩, _⟩ := hL2 q hq
        rw [matches_cur h1 h2]
        exact hj q.1 (hL1 ▸ List.mem_map_of_mem hq))).1 ⟨τ, hτ, hall⟩
    refine ⟨u, fun e he => ?_⟩
    rw [← hL1] at he
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he
    exact ((hL2 q hq).2 j u).1 (hsurv q.2 (List.mem_map_of_mem hq))
  · intro hC fam hR j hj
    have hch : ∀ σ ∈ fam, ∃ x : List A × M.St,
        ∃ l, Guard.Produces (sys M) (inW M []) l σ ∧ Matches l σ x.1 x.2 := by
      intro σ hσ
      obtain ⟨l, hl⟩ := hR σ hσ
      obtain ⟨β, s, hm⟩ := sound l σ hl
      exact ⟨(β, s), l, hl, hm⟩
    obtain ⟨L, hL1, hL2⟩ := choose_list' fam hch
    obtain ⟨u, hu⟩ := hC (L.map Prod.snd)
      (fun e he => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he
        obtain ⟨l, _, hm⟩ := hL2 q hq
        exact hm.1) j
      (fun e he => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he
        obtain ⟨l, h1, hm⟩ := hL2 q hq
        rw [← matches_cur h1 hm]
        exact hj q.1 (hL1 ▸ List.mem_map_of_mem hq))
    have hrow : ∀ σ ∈ fam, σ.R j u ∧ (spec M).P j u := by
      intro σ hσ
      rw [← hL1] at hσ
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hσ
      obtain ⟨l, _, hm⟩ := hL2 q hq
      have hlive := hu q.2 (List.mem_map_of_mem hq)
      exact ⟨hm.2.2 j u hlive, live_row hm.1 hlive⟩
    by_cases hne : ∃ σ, σ ∈ fam
    · obtain ⟨σ0, hσ0⟩ := hne
      exact (Dist.sysConfluentAt_iff fam j hj).2
        ⟨u, (hrow σ0 hσ0).2, fun σ hσ => (hrow σ hσ).1⟩
    · exact ⟨canon (spec M) j, rfl, fun σ hσ => absurd ⟨σ, hσ⟩ hne⟩

/-- **A confluent automaton has a consistent projected spec**
(Prop. `prop:automaton-confluence`). -/
theorem consistent_of_confluent (h : Confluent M) : (spec M).Consistent := by
  rw [complete_calm_commonExpansion]
  intro rows hrows j hj
  have hch : ∀ r ∈ rows, ∃ x : List A × M.St,
      IOA.Execution M x.1 x.2 ∧ inW M x.1 = r.1 ∧ outW M x.1 = r.2 := by
    intro r hr
    obtain ⟨β, s, hx, h1, h2⟩ := hrows r hr
    exact ⟨(β, s), hx, h1, h2⟩
  obtain ⟨L, hL1, hL2⟩ := choose_list' rows hch
  obtain ⟨u, hu⟩ := h (L.map Prod.snd)
    (fun e he => by obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he; exact (hL2 q hq).1) j
    (fun e he => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he
      rw [(hL2 q hq).2.1]
      exact hj q.1 (hL1 ▸ List.mem_map_of_mem hq))
  have hb : ∀ r ∈ rows, (spec M).P j u ∧ r.2 ≼ u := by
    intro r hr
    rw [← hL1] at hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
    have hl := hu q.2 (List.mem_map_of_mem hq)
    obtain ⟨hx, _, h2⟩ := hL2 q hq
    exact ⟨live_row hx hl, h2 ▸ (live_above hl).2⟩
  by_cases hne : ∃ r, r ∈ rows
  · obtain ⟨r0, hr0⟩ := hne
    exact ⟨u, (hb r0 hr0).1, fun r hr => (hb r hr).2⟩
  · obtain ⟨u', hu'⟩ := (spec M).total j
    exact ⟨u', hu', fun r hr => absurd ⟨r, hr⟩ hne⟩

variable (M) in
/-- The rows the automaton's own commitments have removed from the canonical
table of an execution: rows of the canonical table it can no longer reach. -/
def Removed (β : List A) (s : M.St) : Table (InS M) (OutS M) :=
  fun k u => Canon M β k u ∧ ¬ Live M β s k u

theorem live_canon {β : List A} {s : M.St} (hx : IOA.Execution M β s) {k : InS M} {u : OutS M}
    (h : Live M β s k u) : Canon M β k u :=
  ⟨live_row hx h, live_above h⟩

/-- **Confluence and removed rows** (Prop. `prop:automaton-confluence`): the
automaton is confluent exactly when, for finitely many executions and every
common extension `j` of their receive sequences, some row at `j` lies in every
canonical table and in none of the sets of removed rows. -/
theorem confluent_iff_removed : Confluent M ↔
    ∀ fam : List (List A × M.St), (∀ e ∈ fam, IOA.Execution M e.1 e.2) →
      ∀ j : InS M, (∀ e ∈ fam, inW M e.1 ≼ j) →
        ∃ u, ∀ e ∈ fam, Canon M e.1 j u ∧ ¬ Removed M e.1 e.2 j u := by
  constructor
  · intro h fam hx j hj
    obtain ⟨u, hu⟩ := h fam hx j hj
    exact ⟨u, fun e he => ⟨live_canon (hx e he) (hu e he), fun hr => hr.2 (hu e he)⟩⟩
  · intro h fam hx j hj
    obtain ⟨u, hu⟩ := h fam hx j hj
    exact ⟨u, fun e he => Classical.byContradiction fun hn => (hu e he).2 ⟨(hu e he).1, hn⟩⟩

/-- **The two tables of an execution.**  The history of the system that
matches it keeps exactly the rows it can still reach; the canonical run of
that history's input and output events (its events as a run of the projected
spec) keeps the canonical table.  `Removed` is then the set `Δ` of
Prop. `prop:system-confluence` for that history, restricted to the canonical
table: the rows of the canonical table that one of its commitment events
removed. -/
theorem tables {β : List A} {s : M.St} (hx : IOA.Execution M β s) :
    ∃ l σ ρh, Guard.Produces (sys M) (inW M []) l σ ∧ Matches l σ β s ∧
      l.filterMap SEvent.erase = evs M β ∧
      Exec (canon (spec M) (inW M [])) (l.filterMap SEvent.erase) ρh ∧
      (∀ k u, σ.R k u ↔ Live M β s k u) ∧ (∀ k u, ρh.R k u ↔ Canon M β k u) ∧
      ∀ k u, Removed M β s k u ↔
        ρh.R k u ∧ Dist.Removed (basis M) (canon (spec M) (inW M [])) l k u := by
  obtain ⟨l, σ, hp, hm, heq, he⟩ := complete β s hx
  obtain ⟨ρh, h1, _, h3⟩ := exec_run hx
  rw [← he] at h1
  have hdec := Dist.table_decomp hp.1 h1
  refine ⟨l, σ, ρh, hp, hm, he, h1, heq, h3, fun k u => ?_⟩
  unfold Removed
  rw [← h3, ← heq, hdec]
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨h, Classical.byContradiction fun hd => hn ⟨h, hd⟩⟩
  · rintro ⟨h, hd⟩
    exact ⟨h, fun h' => h'.2 hd⟩

/-! ## Testing and declared specs -/

/-- **Refutation by testing.**  The projected spec is inconsistent exactly when
two executions have the same receive sequence and reply sequences neither of
which is a prefix of the other. -/
theorem not_consistent_iff : ¬ (spec M).Consistent ↔
    ∃ β s β' s', IOA.Execution M β s ∧ IOA.Execution M β' s' ∧ inW M β = inW M β' ∧
      ¬ (outW M β ≼ outW M β' ∨ outW M β' ≼ outW M β) := by
  rw [consistent_iff]
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    apply h
    rintro w t t' ⟨β, s, hx, rfl, rfl⟩ ⟨β', s', hx', hw, rfl⟩
    exact Classical.byContradiction fun hc => hn ⟨β, s, β', s', hx, hx', hw.symm, hc⟩
  · rintro ⟨β, s, β', s', hx, hx', hw, hc⟩ h
    exact hc (h _ _ _ (spec_row hx) (hw ▸ spec_row hx'))

/-- **Declared specs** (Prop. `prop:declared-specification`).  If `D`'s inputs
correspond to receive sequences by `φ`, `D` allows only reply sequences of
executions with the corresponding receive sequence (Realizability), and each
execution's reply sequence is a prefix of one that `D` allows at its receive
sequence (Domination), then `D` is consistent exactly when the projected spec
is. -/
theorem declared {J : Type} [PO J] (φ : InS M → J) (D : Spec J (OutS M))
    (h : CofinalAlong φ D (spec M)) : D.Consistent ↔ (spec M).Consistent :=
  (liftedMono_iff_of_cofinalAlong h).2

/-- A receive sequence with no replies is a row. -/
theorem row_inputs (w : InS M) : (spec M).P w (outW M []) := by
  obtain ⟨s0, hs0⟩ := M.start_nonempty
  obtain ⟨t, ht⟩ := run_inputs s0 w.val w.prop
  exact ⟨w.val, t, ⟨s0, hs0, ht⟩, Wd.ext (recvs_of_inputs w.prop),
    Wd.ext (replies_of_inputs w.prop)⟩

/-- Automata without internal actions: the schedule of an execution is its
trace. -/
theorem trace_eq_of_noint (hn : ∀ a, ¬ M.sig.int a) {β : List A} {s : M.St}
    (h : IOA.Execution M β s) : trace M β = β := by
  obtain ⟨s0, -, hr⟩ := h
  unfold trace
  rw [List.filter_eq_self]
  intro a ha
  induction hr with
  | nil => cases ha
  | cons ht _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · rcases act_cases ht with h | h | h
      · simp [h]
      · simp [h]
      · exact absurd h (hn _)
    · exact ih ha

theorem run_cons_inv {s t : M.St} {a : A} {β : List A} (h : IOA.Run M s (a :: β) t) :
    ∃ s', M.trans s a s' ∧ IOA.Run M s' β t := by
  cases h with
  | cons h1 h2 => exact ⟨_, h1, h2⟩

/-- A map of states preserving start states and transitions, action by
action, maps executions to executions with the same schedule. -/
theorem execution_sim {N : IOA.Automaton A} (f : M.St → N.St) (hs : ∀ s, M.start s → N.start (f s))
    (ht : ∀ s a t, M.trans s a t → N.trans (f s) a (f t)) {β : List A} {s : M.St}
    (h : IOA.Execution M β s) : IOA.Execution N β (f s) := by
  obtain ⟨s0, h0, hr⟩ := h
  refine ⟨f s0, hs s0 h0, ?_⟩
  clear h0
  induction hr with
  | nil => exact .nil _
  | cons htr _ ih => exact .cons (ht _ _ _ htr) (ih)

end IOT
end CC
