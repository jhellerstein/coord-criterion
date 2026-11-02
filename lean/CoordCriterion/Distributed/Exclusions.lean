import CoordCriterion.Foundations.Runs

/-!
# Exclusions and coordination (Sections 4.3–4.4, Appendix C `app:bases`)

Namespace `CC`.  Further claims of these sections are in
`Distributed/Systems.lean`.

* `Exclusion`                         — Def. exclusion (eq. exclusion-excludes)
* `canonicalExclusion`                 — the canonical exclusion `x_o`
* `excludeState`, `excludeApp`          — its resulting state and application
* `SEvent`, `SysStep`, `SysExec`       — Def. output event of a system (`Out_γ(o)`), commit
                                         events `Exclude(γ)` (a nonempty basis sequence,
                                         applied without emitting), run under a basis;
                                         `SEvent.erase` (exclusion events erase to nothing)
* `containment`, `canonical_support`,
  `eps_step_iff`                       — Lemma canonical-exclusion-normal-form (1)–(3)
* `composite`, `applySeq_composite`    — Lemma compound-exclusion
* `exclusion_effect`                     — the two effects of an exclusion
* `coordFree_execCF`, `execCF_coordFree` — Def. coordination vs. exclusion-free runs
* `canonical_equivalent`               — Lemma canonical-equivalent (the canonical run
                                         skips exclusion events)
* `conflicting_outputs`                — Prop. thm:exclusions-require-coordination
-/

namespace CC

open Classical

variable {I O : Type} [PO I] [PO O]

section
variable {sp : Spec I O}

/-! ### Def. exclusion -/

/-- **Def. exclusion.**  A partial function on specification states that keeps
the current input, only removes rows, removes at least one row, and satisfies
eq. exclusion-excludes, judged at the resulting table. -/
structure Exclusion (sp : Spec I O) where
  app : State sp → Option (State sp)
  cur_eq : ∀ σ τ, app σ = some τ → τ.cur = σ.cur
  sub : ∀ σ τ, app σ = some τ → ∀ k u, τ.R k u → σ.R k u
  removes : ∀ σ τ, app σ = some τ → ∃ k u, σ.R k u ∧ ¬ τ.R k u
  excludes : ∀ σ τ, app σ = some τ →
    ∀ k u w, σ.R k u → ¬ τ.R k u → τ.R k w → ¬ (u ≼ w)

/-! ### The canonical exclusion -/

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
def excludeState (σ : State sp) (o : O) (ho : σ.R σ.cur o) : State sp where
  cur := σ.cur
  R := fun k x => σ.R k x ∧ ¬ Excluded σ o k x
  sub := fun k x h => σ.sub k x h.1
  hasCur := ⟨o, ho, not_excluded_of_ge (PO.refl o)⟩
  above := fun k x h => σ.above k x h.1

theorem excludeState_keep (σ : State sp) (o : O) (ho : σ.R σ.cur o) :
    ∀ k u, σ.R k u → o ≼ u → (excludeState σ o ho).R k u :=
  fun _ _ h hou => ⟨h, not_excluded_of_ge hou⟩

noncomputable def excludeApp (o : O) (σ : State sp) : Option (State sp) :=
  if h : σ.R σ.cur o ∧ ∃ k x, Excluded σ o k x then some (excludeState σ o h.1) else none

theorem excludeApp_eq {o : O} {σ τ : State sp} :
    excludeApp o σ = some τ ↔
      ∃ h : σ.R σ.cur o, (∃ k x, Excluded σ o k x) ∧ excludeState σ o h = τ := by
  unfold excludeApp
  split
  · rename_i h
    simp only [Option.some.injEq]
    exact ⟨fun e => ⟨h.1, h.2, e⟩, fun ⟨_, _, e⟩ => e⟩
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    rintro ⟨h1, h2, _⟩
    exact h ⟨h1, h2⟩

/-- The canonical exclusion for `o`, defined when `o` is in the current fiber
and `Excluded_o` is nonempty. -/
noncomputable def canonicalExclusion (o : O) : Exclusion sp where
  app := excludeApp o
  cur_eq := by
    intro σ τ h; obtain ⟨_, _, rfl⟩ := excludeApp_eq.1 h; rfl
  sub := by
    intro σ τ h k u hu; obtain ⟨_, _, rfl⟩ := excludeApp_eq.1 h; exact hu.1
  removes := by
    intro σ τ h
    obtain ⟨_, ⟨k, x, he⟩, rfl⟩ := excludeApp_eq.1 h
    exact ⟨k, x, he.1, fun h' => h'.2 he⟩
  excludes := by
    intro σ τ h k u w hu hnu hw huw
    obtain ⟨_, _, rfl⟩ := excludeApp_eq.1 h
    have he : Excluded σ o k u := Classical.byContradiction fun hn => hnu ⟨hu, hn⟩
    obtain ⟨hw, hnw⟩ := hw
    apply he.2.2
    by_cases how : o ≼ w
    · exact ⟨hu, he.2.1, w, hw, how, huw⟩
    · have hsw : Subsumed σ o k w := Classical.byContradiction fun hs => hnw ⟨hw, how, hs⟩
      obtain ⟨_, _, v, hv, hov, hwv⟩ := hsw
      exact ⟨hu, he.2.1, v, hv, hov, PO.trans huw hwv⟩

theorem excludeState_no_excluded (σ : State sp) (o : O) (ho : σ.R σ.cur o) :
    ∀ k x, ¬ Excluded (excludeState σ o ho) o k x := by
  intro k x he
  have hx := he.1
  exact hx.2 ((excluded_keep (σ := σ) (τ := excludeState σ o ho)
    (fun _ _ h => h.1) (excludeState_keep σ o ho) hx).1 he)

/-! ### Sequences of exclusions and the output event of a system -/

/-- Apply `c₁ ⋯ cₙ` in order, each defined at the state its predecessors leave. -/
inductive ApplySeq : List (Exclusion sp) → State sp → State sp → Prop where
  | nil (σ : State sp) : ApplySeq [] σ σ
  | cons {c : Exclusion sp} {cs : List (Exclusion sp)} {σ τ ρ : State sp} :
      c.app σ = some τ → ApplySeq cs τ ρ → ApplySeq (c :: cs) σ ρ

theorem ApplySeq.cur_eq {γ : List (Exclusion sp)} {σ ρ : State sp}
    (h : ApplySeq γ σ ρ) : ρ.cur = σ.cur := by
  induction h with
  | nil => rfl
  | @cons c _ σ τ _ hc _ ih => rw [ih, c.cur_eq σ τ hc]

theorem ApplySeq.sub {γ : List (Exclusion sp)} {σ ρ : State sp}
    (h : ApplySeq γ σ ρ) : ∀ k u, ρ.R k u → σ.R k u := by
  induction h with
  | nil => exact fun _ _ h => h
  | @cons c _ σ τ _ hc _ ih => exact fun k u h => c.sub σ τ hc k u (ih k u h)

theorem ApplySeq.det {γ : List (Exclusion sp)} {σ ρ₁ ρ₂ : State sp}
    (h₁ : ApplySeq γ σ ρ₁) (h₂ : ApplySeq γ σ ρ₂) : ρ₁ = ρ₂ := by
  induction h₁ generalizing ρ₂ with
  | nil => cases h₂; rfl
  | cons hc _ ih =>
    cases h₂ with
    | cons hc' h' =>
      rw [hc] at hc'
      cases hc'
      exact ih h'

/-- Events of a system: output events carry their exclusion sequence `γ`;
exclusion events `Exclude(γ)` apply an exclusion sequence without emitting. -/
inductive SEvent (sp : Spec I O) where
  | input (j : I)
  | output (γ : List (Exclusion sp)) (o : O)
  | exclude (γ : List (Exclusion sp))

/-- Erase exclusion sequences (what the environment observes): exclusion events
are unobservable and erase to nothing.  A list of events erases to
`es.filterMap SEvent.erase`. -/
def SEvent.erase : SEvent sp → Option (Event I O)
  | .input j => some (.input j)
  | .output _ o => some (.output o)
  | .exclude _ => none

/-- An exclusion basis. -/
abbrev ExclusionBasis (sp : Spec I O) := Exclusion sp → Prop

/-- **Def. output event of a system** (with input events unchanged).  The output
event `Out_γ(o)` applies `γ` (from the basis) to reach `σc`, is legal when
`(i,o) ∈ R_c` and eq. lifted-validity holds at `R_c` (which is exactly
`Exposable σc o`), and ends at `(i, R_c[out ⪰ o])`. -/
inductive SysStep (B : ExclusionBasis sp) : State sp → SEvent sp → State sp → Prop where
  | input {σ τ : State sp} {j : I} : Step σ (.input j) τ → SysStep B σ (.input j) τ
  | output {σ σc τ : State sp} {γ : List (Exclusion sp)} {o : O} :
      (∀ c ∈ γ, B c) → ApplySeq γ σ σc → σc.R σc.cur o → Exposable σc o →
      τ.cur = σ.cur → τ.R = outputTable σc o → SysStep B σ (.output γ o) τ
  /-- **Exclusion event** `Exclude(γ)`: a nonempty sequence of basis exclusions,
  each defined at the state its predecessors leave; it ends at the state the
  sequence leaves, subsumes nothing and emits nothing. -/
  | exclude {σ τ : State sp} {γ : List (Exclusion sp)} :
      (∀ c ∈ γ, B c) → γ ≠ [] → ApplySeq γ σ τ → SysStep B σ (.exclude γ) τ

/-- Executions under a basis. -/
inductive SysExec (B : ExclusionBasis sp) : State sp → List (SEvent sp) → State sp → Prop where
  | nil (σ : State sp) : SysExec B σ [] σ
  | cons {σ τ ρ : State sp} {e : SEvent sp} {es : List (SEvent sp)} :
      SysStep B σ e τ → SysExec B τ es ρ → SysExec B σ (e :: es) ρ

/-- **Def. run under a basis**: an execution under `B` from a canonical state. -/
def RunUnder (B : ExclusionBasis sp) (es : List (SEvent sp)) (τ : State sp) : Prop :=
  ∃ i, SysExec B (canon sp i) es τ

theorem SysStep.sub {B : ExclusionBasis sp} {σ τ : State sp} {e : SEvent sp}
    (h : SysStep B σ e τ) : ∀ k u, τ.R k u → σ.R k u := by
  cases h with
  | input hs => exact step_sub hs
  | output _ hγ _ _ _ hR =>
    intro k u hu; rw [hR] at hu; exact hγ.sub k u hu.1
  | exclude _ _ hγ => exact hγ.sub

/-- An exclusion event keeps the current input. -/
theorem SysStep.exclude_cur {B : ExclusionBasis sp} {σ τ : State sp} {γ : List (Exclusion sp)}
    (h : SysStep B σ (.exclude γ) τ) : τ.cur = σ.cur := by
  cases h with
  | exclude _ _ hγ => exact hγ.cur_eq

theorem SysExec.sub {B : ExclusionBasis sp} {σ τ : State sp} {es : List (SEvent sp)}
    (h : SysExec B σ es τ) : ∀ k u, τ.R k u → σ.R k u := by
  induction h with
  | nil => exact fun _ _ h => h
  | cons hs _ ih => exact fun k u h => hs.sub k u (ih k u h)

/-! ### Lemma canonical-exclusion-normal-form -/

/-- A legal output event's exclusions remove every row in `Excluded_o`. -/
theorem containment {B : ExclusionBasis sp} {σ τ : State sp} {γ : List (Exclusion sp)} {o : O}
    (h : SysStep B σ (.output γ o) τ) :
    τ.cur = σ.cur ∧ σ.R σ.cur o ∧ (∀ k u, τ.R k u → σ.R k u ∧ o ≼ u) ∧
    ∃ σc, ApplySeq γ σ σc ∧ ∀ k x, Excluded σ o k x → ¬ σc.R k x := by
  cases h with
  | output _ hγ ho hleg hcur hR =>
    have hsub := hγ.sub
    refine ⟨hcur, ?_, ?_, _, hγ, ?_⟩
    · have := hsub _ _ ho; rwa [hγ.cur_eq] at this
    · intro k u hu; rw [hR] at hu; exact ⟨hsub _ _ hu.1, hu.2⟩
    · intro k x he hc
      obtain ⟨u, hu, hou, hxu⟩ := hleg k x hc he.2.1
      exact he.2.2 ⟨he.1, he.2.1, u, hsub _ _ hu, hou, hxu⟩

/-- If `Excluded_o` is nonempty, the output event applies an exclusion. -/
theorem containment_nonempty {B : ExclusionBasis sp} {σ τ : State sp} {γ : List (Exclusion sp)}
    {o : O} (h : SysStep B σ (.output γ o) τ)
    (hne : ∃ k x, Excluded σ o k x) : γ ≠ [] := by
  rintro rfl
  obtain ⟨_, _, _, σc, hγ, hrm⟩ := containment h
  cases hγ
  obtain ⟨k, x, hx⟩ := hne
  exact hrm k x hx hx.1

/-- The canonical basis `B_P`. -/
def canonExclusionBasis (sp : Spec I O) : ExclusionBasis sp := fun c =>
  ∃ o : O, c = canonicalExclusion o ∧
    ∃ σ τ : State sp, (canonicalExclusion o).app σ = some τ

/-- `κ_o` is empty or the singleton canonical exclusion. -/
noncomputable def kappa (σ : State sp) (o : O) : List (Exclusion sp) :=
  if ∃ k x, Excluded σ o k x then [canonicalExclusion o] else []

theorem kappa_apply (σ : State sp) (o : O) (ho : σ.R σ.cur o) :
    (∀ c ∈ kappa σ o, canonExclusionBasis sp c) ∧
    ∃ σc, ApplySeq (kappa σ o) σ σc ∧ σc.cur = σ.cur ∧ σc.R = (excludeState σ o ho).R := by
  by_cases he : ∃ k x, Excluded σ o k x
  · have happ : (canonicalExclusion o).app σ = some (excludeState σ o ho) :=
      excludeApp_eq.2 ⟨ho, he, rfl⟩
    refine ⟨?_, excludeState σ o ho, ?_, rfl, rfl⟩
    · simp only [kappa, he, ite_true, List.mem_cons, List.not_mem_nil, or_false]
      rintro c rfl
      exact ⟨o, rfl, σ, excludeState σ o ho, happ⟩
    · simp only [kappa, he, ite_true]
      exact ApplySeq.cons happ (ApplySeq.nil _)
  · refine ⟨?_, σ, ?_, rfl, ?_⟩
    · simp [kappa, he]
    · simp only [kappa, he, ite_false]
      exact ApplySeq.nil _
    · funext k x
      apply propext
      exact ⟨fun h => ⟨h, fun hx => he ⟨k, x, hx⟩⟩, fun h => h.1⟩

/-- The state `(i, R[out ⪰ o])`. -/
def outState (σ : State sp) (o : O) (ho : σ.R σ.cur o) : State sp where
  cur := σ.cur
  R := outputTable σ o
  sub := fun k x h => σ.sub k x h.1
  hasCur := ⟨o, ho, PO.refl o⟩
  above := fun k x h => σ.above k x h.1

theorem excluded_out (σ : State sp) (o : O) (ho : σ.R σ.cur o) (σc : State sp)
    (hR : σc.R = (excludeState σ o ho).R) :
    outputTable σc o = outputTable σ o := by
  funext k u
  apply propext
  simp only [outputTable, hR, excludeState]
  exact ⟨fun ⟨⟨a, _⟩, b⟩ => ⟨a, b⟩,
    fun ⟨a, b⟩ => ⟨⟨a, not_excluded_of_ge b⟩, b⟩⟩

/-- The canonical event is legal and ends at `(i, R[out ⪰ o])`. -/
theorem canonical_support (σ : State sp) (o : O) (ho : σ.R σ.cur o) :
    SysStep (canonExclusionBasis sp) σ (.output (kappa σ o) o) (outState σ o ho) := by
  obtain ⟨hB, σc, hγ, hc, hR⟩ := kappa_apply σ o ho
  refine SysStep.output hB hγ ?_ ?_ rfl ?_
  · rw [hR, hc]
    exact ⟨ho, not_excluded_of_ge (PO.refl o)⟩
  · intro k x hx hnx
    rw [hR] at hx
    obtain ⟨hx, he⟩ := hx
    have hs : Subsumed σ o k x := Classical.byContradiction fun hn => he ⟨hx, hnx, hn⟩
    obtain ⟨_, _, u, hu, hou, hxu⟩ := hs
    exact ⟨u, hR ▸ excludeState_keep σ o ho k u hu hou, hou, hxu⟩
  · exact (excluded_out σ o ho σc hR).symm

/-- Every legal output event keeps only rows that the canonical event keeps. -/
theorem canonical_maximal {B : ExclusionBasis sp} {σ τ : State sp} {γ : List (Exclusion sp)} {o : O}
    (h : SysStep B σ (.output γ o) τ) : ∀ k u, τ.R k u → outputTable σ o k u :=
  (containment h).2.2.1

theorem kappa_step_eq {B : ExclusionBasis sp} {σ τ : State sp} {o : O}
    (h : SysStep B σ (.output (kappa σ o) o) τ) :
    τ.cur = σ.cur ∧ τ.R = outputTable σ o := by
  have ho := (containment h).2.1
  obtain ⟨_, σc', hγ', _, hR'⟩ := kappa_apply σ o ho
  cases h with
    | output _ hγ _ _ hcur hR =>
      refine ⟨hcur, ?_⟩
      rw [hR, hγ.det hγ', excluded_out σ o ho σc' hR']

/-- `Exposable` is exactly `Excluded_o = ∅`. -/
theorem exposable_iff_empty (σ : State sp) (o : O) :
    Exposable σ o ↔ ¬ ∃ k x, Excluded σ o k x := by
  constructor
  · intro h ⟨k, x, he⟩
    exact he.2.2 ⟨he.1, he.2.1, h k x he.1 he.2.1⟩
  · intro he k x hx hnx
    exact Classical.byContradiction fun hn =>
      he ⟨k, x, hx, hnx, fun hs => hn hs.2.2⟩

/-- **Lemma containment, (3).**  `Out_ε(o)` is legal (under any basis) exactly
when `o ∈ R(i)` is exposable, and then it ends at `(i, R[out ⪰ o])`. -/
theorem eps_step_iff {B : ExclusionBasis sp} {σ τ : State sp} {o : O} :
    SysStep B σ (.output [] o) τ ↔
      σ.R σ.cur o ∧ Exposable σ o ∧ τ.cur = σ.cur ∧ τ.R = outputTable σ o := by
  constructor
  · intro h
    cases h with
    | output _ hγ ho hleg hcur hR =>
      cases hγ
      exact ⟨ho, hleg, hcur, hR⟩
  · rintro ⟨ho, hleg, hcur, hR⟩
    exact SysStep.output (fun _ h => by simp at h) (ApplySeq.nil _) ho hleg hcur hR

/-! ### Lemma compound-exclusion -/

/-- Apply a sequence as one partial function. -/
noncomputable def compApp : List (Exclusion sp) → State sp → Option (State sp)
  | [], σ => some σ
  | c :: cs, σ => (c.app σ).bind (compApp cs)

theorem compApp_iff {cs : List (Exclusion sp)} {σ ρ : State sp} :
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

theorem applySeq_excludes {cs : List (Exclusion sp)} {σ ρ : State sp}
    (h : ApplySeq cs σ ρ) :
    ∀ k u w, σ.R k u → ¬ ρ.R k u → ρ.R k w → ¬ (u ≼ w) := by
  induction h with
  | nil => exact fun _ _ _ hu hnu _ => absurd hu hnu
  | @cons c _ σ τ _ hc hrest ih =>
    intro k u w hu hnu hw
    by_cases hτ : τ.R k u
    · exact ih k u w hτ hnu hw
    · exact c.excludes σ τ hc k u w hu hτ (hrest.sub k w hw)

/-- **Lemma compound-exclusion.**  The composite of a nonempty sequence of
exclusions is an exclusion. -/
noncomputable def composite (c : Exclusion sp) (cs : List (Exclusion sp)) :
    Exclusion sp where
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
  excludes := fun _ _ h => applySeq_excludes (compApp_iff.1 h)

/-- A compound output event has the same effect as one applying the composite. -/
theorem applySeq_composite (c : Exclusion sp) (cs : List (Exclusion sp))
    (σ σc : State sp) :
    ApplySeq (c :: cs) σ σc ↔ ApplySeq [composite c cs] σ σc := by
  constructor
  · intro h
    exact ApplySeq.cons (compApp_iff.2 h) (ApplySeq.nil _)
  · intro h
    cases h with
    | cons hc hn => cases hn; exact compApp_iff.1 hc

/-! ### Effect of an exclusion at an input -/

/-- At an input where an exclusion removes rows, it either removes the whole
fiber or leaves a row; in the latter case no removed row refines a survivor. -/
theorem exclusion_effect (c : Exclusion sp) {σ τ : State sp} (h : c.app σ = some τ)
  (k : I) (_hk : ∃ u, σ.R k u ∧ ¬ τ.R k u) :
  ((∀ u, ¬ τ.R k u) ∨
    (∃ w, τ.R k w ∧ ∀ u, σ.R k u → ¬ τ.R k u → ¬ (u ≼ w))) ∧
  ¬ ((∀ u, ¬ τ.R k u) ∧ ∃ w, τ.R k w) := by
  refine ⟨?_, fun ⟨h1, w, hw⟩ => h1 w hw⟩
  by_cases hrem : ∃ w, τ.R k w
  · obtain ⟨w, hw⟩ := hrem
    exact Or.inr ⟨w, hw, fun u hu hnu => c.excludes σ τ h k u w hu hnu hw⟩
  · exact Or.inl fun u hu => hrem ⟨u, hu⟩

/-- An exclusion never empties the current fiber. -/
theorem exclusion_preserves_current_fiber (c : Exclusion sp) {σ τ : State sp}
  (h : c.app σ = some τ) : ∃ w, τ.R σ.cur w := by
  have := τ.hasCur; rwa [c.cur_eq σ τ h] at this

/-- In a functional specification, removing one row empties its fiber. -/
theorem functional_exclusion_empties_fiber (hf : sp.Functional) (c : Exclusion sp)
  {σ τ : State sp} (_h : c.app σ = some τ) (k : I) (hk : ∃ u, σ.R k u ∧ ¬ τ.R k u) :
  ∀ w, ¬ τ.R k w := by
  intro w hw
  obtain ⟨u, hu, hnu⟩ := hk
  have : u = w := hf k u w (σ.sub _ _ hu) (τ.sub _ _ hw)
  exact hnu (this ▸ hw)

/-! ### Def. coordination -/

/-- A run (event list) coordinates: some event applies an exclusion, i.e.
some output event applies a nonempty sequence, or the run has an exclusion event. -/
def Coordinates (es : List (SEvent sp)) : Prop :=
  (∃ γ o, SEvent.output γ o ∈ es ∧ γ ≠ []) ∨ ∃ γ, SEvent.exclude γ ∈ es

/-- Coordination-free (exclusion-free): every output event is `Out_ε(o)`,
and there is no exclusion event. -/
def CoordFree (es : List (SEvent sp)) : Prop :=
  (∀ γ o, SEvent.output γ o ∈ es → γ = []) ∧ ∀ γ, SEvent.exclude γ ∉ es

theorem coordFree_iff_not (es : List (SEvent sp)) : CoordFree es ↔ ¬ Coordinates es := by
  constructor
  · rintro ⟨h, hc⟩ (⟨γ, o, hm, hne⟩ | ⟨γ, hm⟩)
    · exact hne (h γ o hm)
    · exact hc γ hm
  · intro h
    exact ⟨fun γ o hm => Classical.byContradiction fun hne => h (Or.inl ⟨γ, o, hm, hne⟩),
      fun γ hm => h (Or.inr ⟨γ, hm⟩)⟩

theorem CoordFree.tail {e : SEvent sp} {es : List (SEvent sp)} (h : CoordFree (e :: es)) :
    CoordFree es :=
  ⟨fun γ o hm => h.1 γ o (List.mem_cons_of_mem _ hm),
   fun γ hm => h.2 γ (List.mem_cons_of_mem _ hm)⟩

/-- Coordination-free executions under any basis are exclusion-free
executions (`ExecCF`) of the erased events. -/
theorem coordFree_execCF {B : ExclusionBasis sp} {σ τ : State sp} {es : List (SEvent sp)}
    (h : SysExec B σ es τ) (hf : CoordFree es) : ExecCF σ (es.filterMap SEvent.erase) τ := by
  induction h with
  | nil => exact ExecCF.nil _
  | @cons σ τ ρ e es hs _ ih =>
    have hf' : CoordFree es := hf.tail
    cases e with
    | input j =>
      cases hs with
      | input hs => exact ExecCF.input hs (ih hf')
    | output γ o =>
      have hγe : γ = [] := hf.1 γ o List.mem_cons_self
      subst hγe
      obtain ⟨ho, hexp, hcur, hR⟩ := eps_step_iff.1 hs
      exact ExecCF.output (Step.output _ _ o ho hcur hR) hexp (ih hf')
    | exclude γ => exact absurd List.mem_cons_self (hf.2 γ)

theorem execCF_coordFree (B : ExclusionBasis sp) {σ τ : State sp} {es : List (Event I O)}
    (h : ExecCF σ es τ) :
    ∃ es' : List (SEvent sp), es'.filterMap SEvent.erase = es ∧ CoordFree es' ∧
      SysExec B σ es' τ := by
  induction h with
  | nil => exact ⟨[], rfl, ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩, SysExec.nil _⟩
  | @input σ τ ρ j es hs _ ih =>
    obtain ⟨es', he, hf, hx⟩ := ih
    refine ⟨.input j :: es', by simp [he, SEvent.erase], ⟨?_, ?_⟩,
      SysExec.cons (SysStep.input hs) hx⟩
    · intro γ o hm
      simp only [List.mem_cons, reduceCtorEq, false_or] at hm
      exact hf.1 γ o hm
    · intro γ hm
      simp only [List.mem_cons, reduceCtorEq, false_or] at hm
      exact hf.2 γ hm
  | @output σ τ ρ o es hs hexp _ ih =>
    obtain ⟨es', he, hf, hx⟩ := ih
    match hs with
    | .output _ _ _ ho hcur hR =>
    refine ⟨.output [] o :: es', by simp [he, SEvent.erase], ⟨?_, ?_⟩,
      SysExec.cons (eps_step_iff.2 ⟨ho, hexp, hcur, hR⟩) hx⟩
    · intro γ o' hm
      simp only [List.mem_cons, SEvent.output.injEq] at hm
      rcases hm with ⟨rfl, _⟩ | hm
      · rfl
      · exact hf.1 γ o' hm
    · intro γ hm
      simp only [List.mem_cons, reduceCtorEq, false_or] at hm
      exact hf.2 γ hm

/-! ### Canonical runs and Lemma canonical-equivalent -/

/-- A canonical step: a step under `B_P` whose output events are canonical
`Out_{κ_o}(o)` at the state where they occur; canonical runs have no commit
events. -/
def CanonStep (σ : State sp) (e : SEvent sp) (τ : State sp) : Prop :=
  SysStep (canonExclusionBasis sp) σ e τ ∧ (∀ γ o, e = .output γ o → γ = kappa σ o) ∧
    ∀ γ, e ≠ .exclude γ

inductive CanonExec : State sp → List (SEvent sp) → State sp → Prop where
  | nil (σ : State sp) : CanonExec σ [] σ
  | cons {σ τ ρ : State sp} {e : SEvent sp} {es : List (SEvent sp)} :
      CanonStep σ e τ → CanonExec τ es ρ → CanonExec σ (e :: es) ρ

/-- Canonical steps are exactly the steps of Sections 2–3. -/
theorem canonStep_step {σ τ : State sp} {e : SEvent sp} (h : CanonStep σ e τ) :
    ∃ e' : Event I O, e.erase = some e' ∧ Step σ e' τ := by
  obtain ⟨hs, hk, hnc⟩ := h
  cases e with
  | input j => cases hs with | input hs => exact ⟨_, rfl, hs⟩
  | output γ o =>
    have hγ := hk γ o rfl
    subst hγ
    have ho := (containment hs).2.1
    obtain ⟨hc, hR⟩ := kappa_step_eq hs
    exact ⟨_, rfl, Step.output _ _ o ho hc hR⟩
  | exclude γ => exact absurd rfl (hnc γ)

theorem step_canonStep {σ τ : State sp} {e : Event I O} (h : Step σ e τ) :
    ∃ e' : SEvent sp, e'.erase = some e ∧ CanonStep σ e' τ := by
  match h with
  | .input _ _ j hleg hc hR =>
    exact ⟨.input j, rfl, SysStep.input (Step.input _ _ j hleg hc hR),
      ⟨(fun _ _ h => by cases h), fun _ h => by cases h⟩⟩
  | .output _ _ o ho hc hR =>
    refine ⟨.output (kappa σ o) o, rfl, ?_, ⟨(fun γ o' h => by cases h; rfl), fun _ h => by cases h⟩⟩
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
    SysExec (canonExclusionBasis sp) σ es τ := by
  induction h with
  | nil => exact SysExec.nil _
  | cons hs _ ih => exact SysExec.cons hs.1 ih

/-- A canonical run performs no exclusion event. -/
theorem canonExec_noCommit {σ τ : State sp} {es : List (SEvent sp)} (h : CanonExec σ es τ) :
    ∀ γ, SEvent.exclude γ ∉ es := by
  induction h with
  | nil => intro _ h; cases h
  | cons hs _ ih =>
    intro γ hm
    rcases List.mem_cons.1 hm with he | hm
    · exact hs.2.2 γ he.symm
    · exact ih γ hm

/-- Two runs in lockstep: the original under `B`, the other canonical; at
every observable step the events agree after erasure, current inputs agree,
and the canonical table contains the original's.  An exclusion event of the
original is matched by no canonical event (the canonical run stays put, and
the invariant still holds). -/
inductive Lockstep (B : ExclusionBasis sp) :
    State sp → List (SEvent sp) → State sp → State sp → List (SEvent sp) → State sp → Prop where
  | nil (σ σ' : State sp) : Lockstep B σ [] σ σ' [] σ'
  | cons {σ τ ρ σ' τ' ρ' : State sp} {e e' : SEvent sp} {es es' : List (SEvent sp)} :
      SysStep B σ e τ → CanonStep σ' e' τ' → e.erase = e'.erase →
      τ.cur = τ'.cur → (∀ k u, τ.R k u → τ'.R k u) →
      Lockstep B τ es ρ τ' es' ρ' → Lockstep B σ (e :: es) ρ σ' (e' :: es') ρ'
  | exclude {σ τ ρ σ' ρ' : State sp} {γ : List (Exclusion sp)} {es es' : List (SEvent sp)} :
      SysStep B σ (.exclude γ) τ → τ.cur = σ'.cur → (∀ k u, τ.R k u → σ'.R k u) →
      Lockstep B τ es ρ σ' es' ρ' → Lockstep B σ (.exclude γ :: es) ρ σ' es' ρ'

theorem Lockstep.left {B : ExclusionBasis sp} {σ ρ σ' ρ' : State sp} {es es' : List (SEvent sp)}
    (h : Lockstep B σ es ρ σ' es' ρ') : SysExec B σ es ρ := by
  induction h with
  | nil => exact SysExec.nil _
  | cons hs _ _ _ _ _ ih => exact SysExec.cons hs ih
  | exclude hs _ _ _ ih => exact SysExec.cons hs ih

theorem Lockstep.right {B : ExclusionBasis sp} {σ ρ σ' ρ' : State sp} {es es' : List (SEvent sp)}
    (h : Lockstep B σ es ρ σ' es' ρ') : CanonExec σ' es' ρ' := by
  induction h with
  | nil => exact CanonExec.nil _
  | cons _ hc _ _ _ _ ih => exact CanonExec.cons hc ih
  | exclude _ _ _ _ ih => exact ih

theorem Lockstep.erase {B : ExclusionBasis sp} {σ ρ σ' ρ' : State sp} {es es' : List (SEvent sp)}
    (h : Lockstep B σ es ρ σ' es' ρ') :
    es.filterMap SEvent.erase = es'.filterMap SEvent.erase := by
  induction h with
  | nil => rfl
  | @cons _ _ _ _ _ _ e e' _ _ _ _ he _ _ _ ih =>
    rw [List.filterMap_cons, List.filterMap_cons, he]
    cases e'.erase <;> simp [ih]
  | exclude _ _ _ _ ih => rw [List.filterMap_cons_none rfl]; exact ih

/-- Generalized inductive step of Lemma canonical-equivalent: from any pair of
states with equal current input and `R ⊆ R̂`. -/
theorem canonical_equivalent_gen {B : ExclusionBasis sp} {σ ρ : State sp} {es : List (SEvent sp)}
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
          ⟨SysStep.input hst', ⟨(fun _ _ h => by cases h), fun _ h => by cases h⟩⟩
          rfl hcur hsub' hl⟩
    | output γ o =>
      obtain ⟨hcur', ho', hin, _⟩ := containment hs
      have ho'' : σ'.R σ'.cur o := by rw [hc]; exact hsub _ _ ho'
      let τ' := outState σ' o ho''
      have hsub' : ∀ k x, τ.R k x → τ'.R k x := by
        intro k x hx
        obtain ⟨a, b⟩ := hin k x hx
        exact ⟨hsub _ _ a, b⟩
      have hct : τ.cur = τ'.cur := by rw [hcur']; exact hc.symm
      obtain ⟨es', ρ', hl⟩ := ih τ' hct.symm hsub'
      exact ⟨.output (kappa σ' o) o :: es', ρ', Lockstep.cons hs
        ⟨canonical_support σ' o ho'', ⟨(fun γ o' h => by cases h; rfl), fun _ h => by cases h⟩⟩
        rfl hct hsub' hl⟩
    | exclude γ =>
      -- the canonical run does nothing; the invariant survives since a
      -- exclusion event keeps the current input and only removes rows
      have hct : τ.cur = σ'.cur := by rw [hs.exclude_cur]; exact hc.symm
      have hsub' : ∀ k x, τ.R k x → σ'.R k x := fun k x hx => hsub _ _ (hs.sub k x hx)
      obtain ⟨es', ρ', hl⟩ := ih σ' hct.symm hsub'
      exact ⟨es', ρ', Lockstep.exclude hs hct hsub' hl⟩

/-- **Lemma canonical-equivalent.**  Every run under any basis `B` (from the
canonical state `σ_P(i)`) has an observably equivalent canonical run from the
same canonical state, in lockstep: after each event the canonical run's table
contains the original's.  The canonical run is a run of Sections 2–3; it
skips the original's exclusion events, which are unobservable. -/
theorem canonical_equivalent {B : ExclusionBasis sp} {i : I} {es : List (SEvent sp)} {ρ : State sp}
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
  | exclude _ hct hsub _ ih => exact ih hct.symm hsub

/-! ### Proposition thm:exclusions-require-coordination -/

/-- **Prop. conflicting output events cannot be reconciled.**  Let `x ∈ R(i)`.  If
`Out_γ(o)` takes `σ` to `σ'` with no output in `R'(i)` refining `x`, then
`γ ≠ ε`; and if `Out_γ'(x)` takes `σ` to `t`, then no state with current input
`i` is reachable (under any basis) from both `σ'` and `t`. -/
theorem conflicting_outputs {B B' B'' : ExclusionBasis sp} {σ σ' t : State sp}
    {γ γ' : List (Exclusion sp)} {o x : O}
    (h1 : SysStep B σ (.output γ o) σ') (hno : ∀ w, σ'.R σ.cur w → ¬ x ≼ w)
    (h2 : SysStep B' σ (.output γ' x) t) :
    γ ≠ [] ∧
    ¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧
        (∃ es, SysExec B'' σ' es ρ) ∧ (∃ es, SysExec B'' t es ρ) := by
  obtain ⟨_, hx, ht, _⟩ := containment h2
  refine ⟨?_, ?_⟩
  · rintro rfl
    obtain ⟨_, hexp, _, hR⟩ := eps_step_iff.1 h1
    by_cases hox : o ≼ x
    · exact hno x (by rw [hR]; exact ⟨hx, hox⟩) (PO.refl x)
    · obtain ⟨u, hu, hou, hxu⟩ := hexp _ _ hx hox
      exact hno u (by rw [hR]; exact ⟨hu, hou⟩) hxu
  · rintro ⟨ρ, hc, ⟨es1, hx1⟩, ⟨es2, hx2⟩⟩
    obtain ⟨w, hw⟩ := ρ.hasCur
    rw [hc] at hw
    exact hno w (hx1.sub _ _ hw) (ht _ _ (hx2.sub _ _ hw)).2

/-- The same with reachability by the transition system of Sections 2–3. -/
theorem conflicting_outputs_reach {B B' : ExclusionBasis sp} {σ σ' t : State sp}
    {γ γ' : List (Exclusion sp)} {o x : O}
    (_h1 : SysStep B σ (.output γ o) σ') (hno : ∀ w, σ'.R σ.cur w → ¬ x ≼ w)
    (h2 : SysStep B' σ (.output γ' x) t) :
    ¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧ Reach σ' ρ ∧ Reach t ρ := by
  obtain ⟨_, _, ht, _⟩ := containment h2
  rintro ⟨ρ, hc, h1r, h2r⟩
  obtain ⟨w, hw⟩ := ρ.hasCur
  rw [hc] at hw
  exact hno w (reach_sub h1r _ _ hw) (ht _ _ (reach_sub h2r _ _ hw)).2

end

end CC
