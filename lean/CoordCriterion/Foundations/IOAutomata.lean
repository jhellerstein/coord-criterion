/-!
# Input/output automata (Lynch and Tuttle)

Generic I/O automata, following Lynch and Tuttle, "Hierarchical correctness
proofs for distributed algorithms" (PODC 1987) and "An introduction to
input/output automata" (CWI Quarterly 1989):

* `Sig` — an action signature: disjoint input, output, and internal actions;
* `Automaton` — a signature, a set of states with a nonempty set of start
  states, and a transition relation over the signature's actions that is
  *input-enabled* (every input action is enabled in every state);
* `Run M s β t` — an execution fragment from `s` to `t` with schedule `β`;
  `Execution M β t` — an execution (fragment from a start state);
* `Compatible F`, `compose F hc` — composition of a family of automata whose
  outputs are pairwise disjoint and whose internal actions are private; an
  action of the composite moves every component that has it in its
  signature and leaves the others unchanged;
* `run_proj`, `execution_proj` — the projection of an execution of the
  composite onto a component (its schedule restricted to the component's
  actions) is an execution of the component; `run_of_proj` and
  `execution_iff_proj` give the converse (Lynch–Tuttle, Prop. 3), so an
  execution of the composite is exactly a schedule over the components'
  actions whose projections are component executions.

Modeling choices.  All automata of a family share one action universe `A`;
signatures are predicates on `A`.  Lynch–Tuttle's executions are alternating
sequences `s₀ a₁ s₁ ⋯`; `Run` records the schedule `a₁ a₂ ⋯` and the end
state, and the intermediate states exist by construction.  Only finite
executions are used, so the partition of locally controlled actions (needed
for fairness) is omitted.  The composite's index set is an arbitrary type;
for finite executions no finiteness condition is needed.
-/

namespace CC
namespace IOA

universe u

variable {A : Type}

/-- An action signature: input, output, and internal actions, pairwise
disjoint. -/
structure Sig (A : Type) where
  inp : A → Prop
  out : A → Prop
  int : A → Prop
  inp_out : ∀ a, inp a → ¬ out a
  inp_int : ∀ a, inp a → ¬ int a
  out_int : ∀ a, out a → ¬ int a

/-- The actions of a signature. -/
def Sig.acts (σ : Sig A) (a : A) : Prop := σ.inp a ∨ σ.out a ∨ σ.int a

/-- An input/output automaton. -/
structure Automaton (A : Type) where
  St : Type
  sig : Sig A
  start : St → Prop
  start_nonempty : ∃ s, start s
  trans : St → A → St → Prop
  trans_acts : ∀ s a s', trans s a s' → sig.acts a
  input_enabled : ∀ s a, sig.inp a → ∃ s', trans s a s'

/-- An execution fragment from `s` to `t` with schedule `β`. -/
inductive Run (M : Automaton A) : M.St → List A → M.St → Prop where
  | nil (s : M.St) : Run M s [] s
  | cons {s s' t : M.St} {a : A} {β : List A} :
      M.trans s a s' → Run M s' β t → Run M s (a :: β) t

/-- An execution with schedule `β` ending in `t`: a fragment from a start
state. -/
def Execution (M : Automaton A) (β : List A) (t : M.St) : Prop :=
  ∃ s, M.start s ∧ Run M s β t

section runs
variable {M : Automaton A}

theorem run_append_iff : ∀ {s t : M.St} (β γ : List A),
    Run M s (β ++ γ) t ↔ ∃ m, Run M s β m ∧ Run M m γ t
  | s, _, [], _ => ⟨fun h => ⟨s, .nil s, h⟩, fun ⟨_, h1, h2⟩ => by cases h1; exact h2⟩
  | _, _, a :: β, γ => by
    constructor
    · intro h
      cases h with
      | cons hs hr =>
        obtain ⟨m, h1, h2⟩ := (run_append_iff β γ).1 hr
        exact ⟨m, .cons hs h1, h2⟩
    · rintro ⟨m, h1, h2⟩
      cases h1 with
      | cons hs hr => exact .cons hs ((run_append_iff β γ).2 ⟨m, hr, h2⟩)

theorem run_single_iff {s t : M.St} {a : A} : Run M s [a] t ↔ M.trans s a t := by
  constructor
  · intro h
    cases h with
    | cons hs hr => cases hr; exact hs
  · intro h; exact .cons h (.nil _)

theorem execution_nil_iff {t : M.St} : Execution M [] t ↔ M.start t := by
  constructor
  · rintro ⟨s, hs, h⟩; cases h; exact hs
  · intro h; exact ⟨t, h, .nil t⟩

/-- Executions grow one action at a time. -/
theorem execution_snoc_iff {β : List A} {a : A} {t : M.St} :
    Execution M (β ++ [a]) t ↔ ∃ m, Execution M β m ∧ M.trans m a t := by
  constructor
  · rintro ⟨s, hs, h⟩
    obtain ⟨m, h1, h2⟩ := (run_append_iff β [a]).1 h
    exact ⟨m, ⟨s, hs, h1⟩, run_single_iff.1 h2⟩
  · rintro ⟨m, ⟨s, hs, h1⟩, h2⟩
    exact ⟨s, hs, (run_append_iff β [a]).2 ⟨m, h1, run_single_iff.2 h2⟩⟩

/-- Every prefix of an execution is an execution. -/
theorem execution_prefix {β γ : List A} {t : M.St} (h : Execution M (β ++ γ) t) :
    ∃ m, Execution M β m := by
  obtain ⟨s, hs, h⟩ := h
  obtain ⟨m, h1, _⟩ := (run_append_iff β γ).1 h
  exact ⟨m, s, hs, h1⟩

end runs

/-! ### Composition -/

section compose
variable {ι : Type} (F : ι → Automaton A)

/-- Compatibility (Lynch–Tuttle): no action is an output of two components,
and an internal action of a component is an action of no other component. -/
structure Compatible : Prop where
  out_disj : ∀ i j a, (F i).sig.out a → (F j).sig.out a → i = j
  int_disj : ∀ i j a, (F i).sig.int a → (F j).sig.acts a → i = j

variable {F}

/-- The composite signature: outputs and internal actions of the
components, and as inputs the components' inputs that no component
outputs. -/
def composeSig (hc : Compatible F) : Sig A where
  inp a := (∃ i, (F i).sig.inp a) ∧ ¬ ∃ i, (F i).sig.out a
  out a := ∃ i, (F i).sig.out a
  int a := ∃ i, (F i).sig.int a
  inp_out _ h := h.2
  inp_int a h := by
    rintro ⟨j, hj⟩
    obtain ⟨⟨i, hi⟩, _⟩ := h
    have := hc.int_disj j i a hj (Or.inl hi)
    subst this
    exact (F j).sig.inp_int a hi hj
  out_int a h := by
    rintro ⟨j, hj⟩
    obtain ⟨i, hi⟩ := h
    have := hc.int_disj j i a hj (Or.inr (Or.inl hi))
    subst this
    exact (F j).sig.out_int a hi hj

/-- An input of the composite is an input of every component that has it. -/
theorem compose_inp_acts (hc : Compatible F) {a : A} (h : (composeSig hc).inp a) (i : ι)
    (hi : (F i).sig.acts a) : (F i).sig.inp a := by
  rcases hi with hi | hi | hi
  · exact hi
  · exact absurd ⟨i, hi⟩ h.2
  · obtain ⟨⟨j, hj⟩, _⟩ := h
    have := hc.int_disj i j a hi (Or.inl hj)
    subst this
    exact absurd hi ((F i).sig.inp_int a hj)

open Classical in
/-- The composition of a compatible family. -/
noncomputable def compose (F : ι → Automaton A) (hc : Compatible F) : Automaton A where
  St := ∀ i, (F i).St
  sig := composeSig hc
  start s := ∀ i, (F i).start (s i)
  start_nonempty := ⟨fun i => Classical.choose (F i).start_nonempty,
    fun i => Classical.choose_spec (F i).start_nonempty⟩
  trans s a s' := (∃ i, (F i).sig.acts a) ∧
    ∀ i, ((F i).sig.acts a → (F i).trans (s i) a (s' i)) ∧
      (¬ (F i).sig.acts a → s' i = s i)
  trans_acts s a s' h := by
    obtain ⟨⟨i, hi⟩, _⟩ := h
    rcases hi with hi | hi | hi
    · by_cases ho : ∃ j, (F j).sig.out a
      · exact Or.inr (Or.inl ho)
      · exact Or.inl ⟨⟨i, hi⟩, ho⟩
    · exact Or.inr (Or.inl ⟨i, hi⟩)
    · exact Or.inr (Or.inr ⟨i, hi⟩)
  input_enabled s a ha := by
    have hex : ∀ i, (F i).sig.acts a → ∃ t, (F i).trans (s i) a t := fun i hi =>
      (F i).input_enabled (s i) a (compose_inp_acts hc ha i hi)
    refine ⟨fun i => if h : (F i).sig.acts a then Classical.choose (hex i h) else s i,
      ?_, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
    · obtain ⟨⟨i, hi⟩, _⟩ := ha
      exact ⟨i, Or.inl hi⟩
    · simp only [h, dite_true]
      exact Classical.choose_spec (hex i h)
    · simp only [h, dite_false]

open Classical in
/-- The projection of a schedule onto component `i`: the actions in `i`'s
signature. -/
noncomputable def proj (F : ι → Automaton A) (i : ι) (β : List A) : List A :=
  β.filter fun a => decide ((F i).sig.acts a)

theorem proj_cons_of (i : ι) {a : A} (β : List A) (h : (F i).sig.acts a) :
    proj F i (a :: β) = a :: proj F i β := by
  classical
  simp [proj, h]

theorem proj_cons_of_not (i : ι) {a : A} (β : List A) (h : ¬ (F i).sig.acts a) :
    proj F i (a :: β) = proj F i β := by
  classical
  simp [proj, h]

/-- **Projection.** An execution fragment of the composite projects onto an
execution fragment of each component. -/
theorem run_proj (hc : Compatible F) {s t : (compose F hc).St} {β : List A}
    (h : Run (compose F hc) s β t) (i : ι) : Run (F i) (s i) (proj F i β) (t i) := by
  induction h with
  | nil s => exact .nil _
  | @cons s s' t a β hs _ ih =>
    by_cases hi : (F i).sig.acts a
    · rw [proj_cons_of i β hi]
      exact .cons ((hs.2 i).1 hi) ih
    · rw [proj_cons_of_not i β hi, ← (hs.2 i).2 hi]
      exact ih

/-- Every action of a composite schedule belongs to some component. -/
theorem run_owned (hc : Compatible F) {s t : (compose F hc).St} {β : List A}
    (h : Run (compose F hc) s β t) : ∀ a ∈ β, ∃ i, (F i).sig.acts a := by
  induction h with
  | nil => intro a ha; cases ha
  | cons hs _ ih =>
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hs.1
    · exact ih a ha

/-- **Converse of projection** (Lynch–Tuttle, Prop. 3): a schedule of
component actions whose projections are execution fragments of the
components is an execution fragment of the composite. -/
theorem run_of_proj (hc : Compatible F) :
    ∀ {s t : (compose F hc).St} {β : List A}, (∀ a ∈ β, ∃ i, (F i).sig.acts a) →
      (∀ i, Run (F i) (s i) (proj F i β) (t i)) → Run (compose F hc) s β t
  | s, t, [], _, h => by
    have : s = t := funext fun i => by
      have hi := h i
      simp only [proj, List.filter_nil] at hi
      generalize s i = x at hi
      cases hi; rfl
    subst this; exact .nil _
  | s, t, a :: β, ho, h => by
    classical
    have hm : ∀ i, (F i).sig.acts a →
        ∃ m, (F i).trans (s i) a m ∧ Run (F i) m (proj F i β) (t i) := by
      intro i hi
      have := h i
      rw [proj_cons_of i β hi] at this
      cases this with
      | cons hs hr => exact ⟨_, hs, hr⟩
    let m : (compose F hc).St := fun i =>
      if hi : (F i).sig.acts a then Classical.choose (hm i hi) else s i
    refine .cons (s' := m) ⟨ho a (List.mem_cons_self ..), fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
      (run_of_proj hc (fun b hb => ho b (List.mem_cons_of_mem _ hb)) fun i => ?_)
    · simp only [m, hi, dite_true]
      exact (Classical.choose_spec (hm i hi)).1
    · simp only [m, hi, dite_false]
    · by_cases hi : (F i).sig.acts a
      · simp only [m, hi, dite_true]
        exact (Classical.choose_spec (hm i hi)).2
      · simp only [m, hi, dite_false]
        have := h i
        rwa [proj_cons_of_not i β hi] at this

/-- Execution fragments of the composite are exactly the schedules of
component actions whose projections are component execution fragments. -/
theorem run_iff_proj (hc : Compatible F) {s t : (compose F hc).St} {β : List A} :
    Run (compose F hc) s β t ↔
      (∀ a ∈ β, ∃ i, (F i).sig.acts a) ∧ ∀ i, Run (F i) (s i) (proj F i β) (t i) :=
  ⟨fun h => ⟨run_owned hc h, run_proj hc h⟩, fun ⟨h1, h2⟩ => run_of_proj hc h1 h2⟩

/-- Projection of executions. -/
theorem execution_proj (hc : Compatible F) {t : (compose F hc).St} {β : List A}
    (h : Execution (compose F hc) β t) (i : ι) : Execution (F i) (proj F i β) (t i) := by
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s i, hs i, run_proj hc h i⟩

/-- Executions of the composite are exactly the schedules of component
actions whose projections are component executions. -/
theorem execution_iff_proj (hc : Compatible F) {t : (compose F hc).St} {β : List A} :
    Execution (compose F hc) β t ↔
      (∀ a ∈ β, ∃ i, (F i).sig.acts a) ∧ ∀ i, Execution (F i) (proj F i β) (t i) := by
  constructor
  · intro h
    obtain ⟨_, _, hr⟩ := id h
    exact ⟨run_owned hc hr, execution_proj hc h⟩
  · rintro ⟨ho, hx⟩
    refine ⟨fun i => Classical.choose (hx i), fun i => (Classical.choose_spec (hx i)).1,
      run_of_proj hc ho fun i => (Classical.choose_spec (hx i)).2⟩

end compose

end IOA
end CC
