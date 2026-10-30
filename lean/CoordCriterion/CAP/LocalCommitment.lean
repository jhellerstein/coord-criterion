import CoordCriterion.CAP.AvailabilityFor

/-!
# Local commitments and coordination relative to a system

Coordination, relative to a system, is a commitment that some run of the
system contradicts.  An output event of a participant removes rows from its
state (by its commitments `γ`) and may seal inputs (remove every row at them).
The event is *local* when no participant of any history the system produces
emits a removed row's output at that row's input (`SysEmits`), and none
accepts a sealed input (`SysAccepts`).  The same applies to a commit event,
which applies commitments without emitting.  A system is *coordination-free*
when every output event and every commit event of every history it produces
is local.

* `respSystem_coordinationFree`: if `S` is consistent on `A`, the canonical
  system `respSystem A` of `complete_cap_for` is coordination-free.  Its
  canonical output events seal nothing, and the rows they remove lie outside
  `A`, which it never emits.
* `every_row_emitted`: a system with Availability emits every row of `S`, so
  every removal is contradicted; `availability_coordinationFree_iff`: such a
  system is coordination-free exactly when the commitments of its output and
  commit events remove no row; so it performs no commit event
  (`availability_coordinationFree_noCommit`).
-/

namespace CC
namespace CAP

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type}

/-- Some participant of some well-formed history the system produces emits `x`
at current input `k`. -/
def SysEmits (Sys : System sp D) (k : I) (x : O) : Prop :=
  ∃ (n : Nat) (init : Fin n → I) (H : History sp D n) (q : Fin n)
    (a b : List (LEv sp D n)) (γ : List (Commitment sp)) (σ : State sp),
    WF init H ∧ Produced Sys n init H ∧ H q = a ++ LEv.out γ x :: b ∧
    LRun (canon sp (init q)) a σ ∧ σ.cur = k

/-- Some participant of some well-formed history the system produces records
`input(k)`. -/
def SysAccepts (Sys : System sp D) (k : I) : Prop :=
  ∃ (n : Nat) (init : Fin n → I) (H : History sp D n) (q : Fin n)
    (a b : List (LEv sp D n)),
    WF init H ∧ Produced Sys n init H ∧ H q = a ++ LEv.inp k :: b

/-- An output event's commitments, taking `σ` to `σc`, are *local* to the
system: no run of the system emits the output of a removed row at its input,
and none accepts a sealed input.  (The same condition is applied to the
commitments of a commit event.) -/
def LocalEvent (Sys : System sp D) (σ σc : State sp) : Prop :=
  (∀ k x, σ.R k x → ¬ σc.R k x → ¬ SysEmits Sys k x) ∧
  (∀ k, (∃ x, σ.R k x) → (∀ x, ¬ σc.R k x) → ¬ SysAccepts Sys k)

/-- Runs that emit `emits k x` (output `x` at current input `k`) and accept
`accepts k` *contradict* the commitments taking `σ` to `σc`: they emit the
output of a removed row at its input, or accept a sealed input (one whose
remaining rows are all removed). -/
def Contradicts (emits : I → O → Prop) (accepts : I → Prop) (σ σc : State sp) : Prop :=
  (∃ k x, σ.R k x ∧ ¬ σc.R k x ∧ emits k x) ∨
  (∃ k, (∃ x, σ.R k x) ∧ (∀ x, ¬ σc.R k x) ∧ accepts k)

/-- An event is local exactly when no run of the system contradicts its
commitments. -/
theorem localEvent_iff_not_contradicts (Sys : System sp D) (σ σc : State sp) :
    LocalEvent Sys σ σc ↔ ¬ Contradicts (SysEmits Sys) (SysAccepts Sys) σ σc := by
  constructor
  · rintro ⟨h1, h2⟩ (⟨k, x, hx, hnx, he⟩ | ⟨k, hk, hall, ha⟩)
    · exact h1 k x hx hnx he
    · exact h2 k hk hall ha
  · intro h
    exact ⟨fun k x hx hnx he => h (Or.inl ⟨k, x, hx, hnx, he⟩),
      fun k hk hall ha => h (Or.inr ⟨k, hk, hall, ha⟩)⟩

/-- A system is coordination-free when every output event and every commit
event of every history it produces is local. -/
def System.CoordinationFree (Sys : System sp D) : Prop :=
  (∀ (n : Nat) (init : Fin n → I) (H : History sp D n), WF init H → Produced Sys n init H →
    ∀ (q : Fin n) (a b : List (LEv sp D n)) (γ : List (Commitment sp)) (o : O)
      (σ σc : State sp),
      H q = a ++ LEv.out γ o :: b → LRun (canon sp (init q)) a σ → applySeq σ γ = some σc →
      LocalEvent Sys σ σc) ∧
  (∀ (n : Nat) (init : Fin n → I) (H : History sp D n), WF init H → Produced Sys n init H →
    ∀ (q : Fin n) (a b : List (LEv sp D n)) (γ : List (Commitment sp)) (σ σc : State sp),
      H q = a ++ LEv.cmt γ :: b → LRun (canon sp (init q)) a σ → applySeq σ γ = some σc →
      LocalEvent Sys σ σc)

/-- An output event with no commitment is local. -/
theorem localEvent_nil (Sys : System sp D) {σ σc : State sp}
    (h : applySeq σ ([] : List (Commitment sp)) = some σc) : LocalEvent Sys σ σc := by
  simp [applySeq] at h; subst h
  exact ⟨fun _ _ hx hnx => absurd hx hnx, fun _ ⟨x, hx⟩ hall => absurd hx (hall x)⟩

theorem compliant_of_eq_append {E : Type} {A : List E → E → Prop} {l a b : List E} {e : E}
    (h : Compliant A l) (hl : l = a ++ e :: b) : Compliant A a :=
  compliant_prefix (y := e :: b) (hl ▸ h)

/-- `respSystem A` emits only outputs of `A` at the current input. -/
theorem resp_emits_A {A : Table I O} {k : I} {x : O}
    (h : SysEmits (respSystem (sp := sp) (D := D) A) k x) : A k x := by
  obtain ⟨n, init, H, q, a, b, γ, σ, _, hp, hH, hrun, hcur⟩ := h
  have hAl := hp q a (.out γ x) b hH
  obtain ⟨_, _, hAx, _⟩ := hAl
  obtain ⟨h1, _⟩ := rinv_of_produced A (compliant_of_eq_append (hp q) hH) hrun
  rw [← hcur, h1]; exact hAx

/-- **If `S` is consistent on `A`, `respSystem A` is coordination-free.**  Its
output events are canonical events for outputs of `A`; they seal nothing, and
every row they remove lies outside `A`, so no run of the system emits it. -/
theorem respSystem_coordinationFree (A : Table I O) (hcons : ConsistentOn sp A) :
    (respSystem (sp := sp) (D := D) A).CoordinationFree := by
  refine ⟨?_, fun n init H _ hp q a b γ σ σc hH _ _ => ?_⟩
  rotate_left
  · -- `respSystem A` performs no commit event
    have := (hp q a (.cmt γ) b hH).2
    simp [respSystem, respF, LEv.erase] at this
  intro n init H _ hp q a b γ o σ σc hH hrun hap
  have hAl := hp q a (.out γ o) b hH
  obtain ⟨_, hγ, hAo, hge⟩ := hAl
  obtain ⟨hcur, hres, _, _⟩ :=
    rinv_of_produced A (compliant_of_eq_append (hp q) hH) hrun
  rw [← hcur] at hAo
  -- rows refining `o` at expansions of the current input are still present
  have hkeep : ∀ k u, sp.S k u → σ.cur ≼ k → o ≼ u → σ.R k u := fun k u hSu hk hou =>
    (hres k u).2 ⟨hSu, hk, fun e he => PO.trans (hge e he) hou⟩
  rcases hγ with rfl | rfl
  · exact localEvent_nil _ hap
  · obtain ⟨hu, rfl⟩ := kc_apply_some hap
    constructor
    · intro k x hx hnx hemit
      have hAx := resp_emits_A hemit
      obtain ⟨_, hk, _⟩ := (hres k x).1 hx
      obtain ⟨u, hSu, hall⟩ := hcons [(σ.cur, o), (k, x)]
        (by intro r hr; simp at hr; rcases hr with rfl | rfl
            · exact hAo
            · exact hAx) k
        (by intro r hr; simp at hr; rcases hr with rfl | rfl
            · exact hk
            · exact PO.refl k)
      have hou : o ≼ u := hall (σ.cur, o) (by simp)
      have hxu : x ≼ u := hall (k, x) (by simp)
      have hRu := hkeep k u hSu hk hou
      apply hnx
      refine ⟨hx, ?_⟩
      rintro (⟨_, hs⟩ | ⟨_, hn, _, hret⟩)
      · exact hs ⟨u, hRu, hou⟩
      · exact hret ⟨hx, hn, u, hRu, hou, hxu⟩
    · rintro k ⟨x, hx⟩ hall _
      obtain ⟨_, hk, _⟩ := (hres k x).1 hx
      obtain ⟨u, hSu, hu'⟩ := hcons [(σ.cur, o)]
        (by intro r hr; simp at hr; subst hr; exact hAo) k
        (by intro r hr; simp at hr; subst hr; exact hk)
      have hou : o ≼ u := hu' (σ.cur, o) (by simp)
      have hRu := hkeep k u hSu hk hou
      exact hall u ⟨hRu, not_rm_of_le hRu hou⟩

/-- A system with Availability emits every row of `S`: two participants start
at `k` in separate blocks, and the first emits `x` locally, at current
input `k`. -/
theorem every_row_emitted (Sys : System sp D) (hA : AvailabilityAtEnd Sys) :
    ∀ k x, sp.S k x → SysEmits Sys k x := by
  intro k x hkx
  let init : Fin 2 → I := fun _ => k
  let H0 : History sp D 2 := fun _ => []
  have hwf0 : WF init H0 :=
    ⟨fun p => ⟨_, .nil _⟩, by intro p a q k j d b h; simp [H0] at h⟩
  have hprod0 : Produced Sys 2 init H0 := fun p a e b h => by simp [H0] at h
  have hpart0 : Partitioned H0 (fun q => q.val) :=
    ⟨⟨0, 1, by simp⟩, by intro p a q k j d b h; simp [H0] at h⟩
  have ho : (canon sp (init 0)).R (canon sp (init 0)).cur x := ⟨hkx, PO.refl k⟩
  obtain ⟨ext, hwf', hprod', _, _, hni, γ, hγ⟩ :=
    hA 2 init H0 (fun q => q.val) hwf0 hprod0 hpart0 0 _ (.nil _) x ho
  obtain ⟨a, b, hab⟩ := List.append_of_mem hγ
  have hH : (fun q => H0 q ++ ext q) 0 = a ++ LEv.out γ x :: b := by
    show [] ++ ext 0 = _; rw [List.nil_append]; exact hab
  obtain ⟨τ, hτ⟩ := hwf'.1 0
  rw [hH] at hτ
  obtain ⟨σ, hσ, _⟩ := lrun_append.1 hτ
  have hcur : σ.cur = k :=
    lrun_noinp hσ (fun j hj => hni 0 j (by rw [hab]; exact List.mem_append_left _ hj))
  exact ⟨2, init, _, 0, a, b, γ, σ, hwf', hprod', hH, hσ, hcur⟩

/-- With Availability (`A = S`), coordination is commitment: a system with
Availability is coordination-free exactly when the commitments of its output
events and commit events remove no row. -/
theorem availability_coordinationFree_iff (Sys : System sp D) (hA : AvailabilityAtEnd Sys) :
    Sys.CoordinationFree ↔
      (∀ (n : Nat) (init : Fin n → I) (H : History sp D n), WF init H → Produced Sys n init H →
        ∀ (q : Fin n) (a b : List (LEv sp D n)) (γ : List (Commitment sp)) (o : O)
          (σ σc : State sp),
          H q = a ++ LEv.out γ o :: b → LRun (canon sp (init q)) a σ →
          applySeq σ γ = some σc → ∀ k x, σ.R k x → σc.R k x) ∧
      (∀ (n : Nat) (init : Fin n → I) (H : History sp D n), WF init H → Produced Sys n init H →
        ∀ (q : Fin n) (a b : List (LEv sp D n)) (γ : List (Commitment sp)) (σ σc : State sp),
          H q = a ++ LEv.cmt γ :: b → LRun (canon sp (init q)) a σ →
          applySeq σ γ = some σc → ∀ k x, σ.R k x → σc.R k x) := by
  have keep : ∀ {σ σc : State sp}, LocalEvent Sys σ σc → ∀ k x, σ.R k x → σc.R k x :=
    fun {σ} {_} hl k x hx => Classical.byContradiction fun hnx =>
      hl.1 k x hx hnx (every_row_emitted Sys hA k x (σ.sub _ _ hx))
  have loc : ∀ {σ σc : State sp}, (∀ k x, σ.R k x → σc.R k x) → LocalEvent Sys σ σc :=
    fun hkeep => ⟨fun k x hx hnx => absurd (hkeep k x hx) hnx,
      fun k ⟨x, hx⟩ hall => absurd (hkeep k x hx) (hall x)⟩
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun n init H hw hp q a b γ o σ σc hH hrun hap =>
        keep (h1 n init H hw hp q a b γ o σ σc hH hrun hap),
      fun n init H hw hp q a b γ σ σc hH hrun hap =>
        keep (h2 n init H hw hp q a b γ σ σc hH hrun hap)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun n init H hw hp q a b γ o σ σc hH hrun hap =>
        loc (h1 n init H hw hp q a b γ o σ σc hH hrun hap),
      fun n init H hw hp q a b γ σ σc hH hrun hap =>
        loc (h2 n init H hw hp q a b γ σ σc hH hrun hap)⟩

/-- Hence a coordination-free system with Availability performs no commit
event: a commit event's (nonempty) commitments remove a row, which some run
of the system emits. -/
theorem availability_coordinationFree_noCommit (Sys : System sp D) (hA : AvailabilityAtEnd Sys)
    (hcf : Sys.CoordinationFree) {n : Nat} {init : Fin n → I} {H : History sp D n}
    (hw : WF init H) (hp : Produced Sys n init H) (q : Fin n) (γ : List (Commitment sp)) :
    LEv.cmt γ ∉ H q := by
  intro hm
  obtain ⟨a, b, hH⟩ := List.append_of_mem hm
  obtain ⟨τ, hτ⟩ := hw.1 q
  rw [hH] at hτ
  obtain ⟨σ, hσ, hrest⟩ := lrun_append.1 hτ
  cases hrest with
  | cmt hne hap _ =>
    obtain ⟨k, x, hx, hnx⟩ := applySeq_removes hne hap
    exact hnx (((availability_coordinationFree_iff Sys hA).1 hcf).2 n init H hw hp q a b γ σ _
      hH hσ hap k x hx)

/-! ## Specifications: every commitment is contradicted by a canonical run -/

/-- For a specification, every commitment is contradicted by some canonical
run: from `σ_S(i)` with `i ≼ k`, the canonical run `input(k) output(x)`
accepts `k` (when `i ≺ k`) and emits any `x ∈ S(k)` at current input `k`.  A
commitment at a state with current input `i` seals only inputs `k ≻ i` and
chooses only against rows `(k,x)` with `i ≼ k`, so some canonical run
performs an event it rules out. -/
theorem canonical_run_contradicts {i k : I} {x : O} (hik : i ≼ k) (hx : sp.S k x) :
    ∃ τ : State sp, Exec (canon sp i) [.input k, .output x] τ ∧ τ.cur = k := by
  have hju : (canon sp i).R k x := ⟨hx, hik⟩
  let σ := canon sp i
  let τ1 : State sp :=
    { cur := k
      R := inputTable σ k
      sub := fun k' x' h => σ.sub k' x' h.1
      hasCur := ⟨x, hju, PO.refl k⟩
      above := fun _ _ h => h.2 }
  have s1 : Step σ (.input k) τ1 := Step.input σ τ1 k ⟨x, hju⟩ rfl rfl
  let τ2 : State sp :=
    { cur := k
      R := outputTable τ1 x
      sub := fun k' x' h => τ1.sub k' x' h.1
      hasCur := ⟨x, ⟨hju, PO.refl k⟩, PO.refl x⟩
      above := fun k' x' h => τ1.above k' x' h.1 }
  have s2 : Step τ1 (.output x) τ2 := Step.output τ1 τ2 x ⟨hju, PO.refl k⟩ rfl rfl
  exact ⟨τ2, Exec.cons s1 (Exec.cons s2 (Exec.nil _)), rfl⟩

end CAP
end CC
