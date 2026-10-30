import CoordCriterion.CAP.LocalCommitment

/-!
# Coordination within a history

`System.CoordinationFree` (`CAP/LocalCommitment.lean`) counts a commitment as
contradicted when *any* run of the system performs an event it rules out,
including the same participant's alternative runs.  The paper's notion is
narrower: a commitment is contradicted when *another participant of the same
history* accepts an input it seals, or emits, at the same input, an output it
chose against.  `System.CoordinationFreeH` is that notion, for the
commitments of output events and of commit events alike.

* `coordinationFree_to_H`: the older notion implies the new one; hence
  `respSystem_coordinationFreeH`.
* `availability_contradicts_removal` (output events) and
  `availability_contradicts_commit` (commit events): with Availability
  (`A = S`), a row removed by a participant whose prefix is receive-free is
  emitted, in the same history, by any other participant whose initial input
  lies below the row's input; so such a system is not coordination-free in
  this sense (`availability_not_coordinationFreeH`,
  `availability_not_coordinationFreeH_commit`).
* Shared nothing (`ordSpec`): one owner choosing an order is coordination-free
  (`ownerSys_coordinationFreeH`), although its choice is a commitment
  (`ordSpec_ab_not_exposable`); two owners choosing are not
  (`twoOwnerSys_not_coordinationFreeH`).
* Local choice (`lcSpec`, `lcA`): `S` is consistent on `A = {o}`, emitting `o`
  must commit against `x`, and `respSystem A` is coordination-free.
-/

namespace CC
namespace CAP

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type}

/-- The commitments taking `σ` to `σc`, applied by participant `p` of `H`, are
contradicted by no other participant of `H`: none emits a removed row's output
at its input, and none accepts a sealed input. -/
def LocalInH {n : Nat} (init : Fin n → I) (H : History sp D n) (p : Fin n) (σ σc : State sp) :
    Prop :=
  (∀ k x, σ.R k x → ¬ σc.R k x →
    ¬ ∃ (q : Fin n) (a' b' : List (LEv sp D n)) (γ' : List (Commitment sp)) (σ' : State sp),
      q ≠ p ∧ H q = a' ++ LEv.out γ' x :: b' ∧ LRun (canon sp (init q)) a' σ' ∧ σ'.cur = k) ∧
  (∀ k, (∃ x, σ.R k x) → (∀ x, ¬ σc.R k x) →
    ¬ ∃ (q : Fin n) (a' b' : List (LEv sp D n)), q ≠ p ∧ H q = a' ++ LEv.inp k :: b')

/-- Some participant `q ≠ p` of `H` emits `x` at current input `k`. -/
def OtherEmits {n : Nat} (init : Fin n → I) (H : History sp D n) (p : Fin n) (k : I) (x : O) :
    Prop :=
  ∃ (q : Fin n) (a' b' : List (LEv sp D n)) (γ' : List (Commitment sp)) (σ' : State sp),
    q ≠ p ∧ H q = a' ++ LEv.out γ' x :: b' ∧ LRun (canon sp (init q)) a' σ' ∧ σ'.cur = k

/-- Some participant `q ≠ p` of `H` accepts `k`. -/
def OtherAccepts {n : Nat} (H : History sp D n) (p : Fin n) (k : I) : Prop :=
  ∃ (q : Fin n) (a' b' : List (LEv sp D n)), q ≠ p ∧ H q = a' ++ LEv.inp k :: b'

/-- `p`'s commitments are local to `H` exactly when no other participant of
`H` contradicts them. -/
theorem localInH_iff_not_contradicts {n : Nat} (init : Fin n → I) (H : History sp D n)
    (p : Fin n) (σ σc : State sp) :
    LocalInH init H p σ σc ↔ ¬ Contradicts (OtherEmits init H p) (OtherAccepts H p) σ σc := by
  constructor
  · rintro ⟨h1, h2⟩ (⟨k, x, hx, hnx, he⟩ | ⟨k, hk, hall, ha⟩)
    · exact h1 k x hx hnx he
    · exact h2 k hk hall ha
  · intro h
    exact ⟨fun k x hx hnx he => h (Or.inl ⟨k, x, hx, hnx, he⟩),
      fun k hk hall ha => h (Or.inr ⟨k, hk, hall, ha⟩)⟩

/-- Coordination-free within histories: no output event's or commit event's
commitments are contradicted by another participant of the same history. -/
def System.CoordinationFreeH (Sys : System sp D) : Prop :=
  (∀ (n : Nat) (init : Fin n → I) (H : History sp D n), WF init H → Produced Sys n init H →
    ∀ (p : Fin n) (a b : List (LEv sp D n)) (γ : List (Commitment sp)) (o : O)
      (σ σc : State sp),
      H p = a ++ LEv.out γ o :: b → LRun (canon sp (init p)) a σ → applySeq σ γ = some σc →
      LocalInH init H p σ σc) ∧
  (∀ (n : Nat) (init : Fin n → I) (H : History sp D n), WF init H → Produced Sys n init H →
    ∀ (p : Fin n) (a b : List (LEv sp D n)) (γ : List (Commitment sp)) (σ σc : State sp),
      H p = a ++ LEv.cmt γ :: b → LRun (canon sp (init p)) a σ → applySeq σ γ = some σc →
      LocalInH init H p σ σc)

theorem localEvent_to_H {Sys : System sp D} {n : Nat} {init : Fin n → I} {H : History sp D n}
    (hw : WF init H) (hp : Produced Sys n init H) (p : Fin n) {σ σc : State sp}
    (hl : LocalEvent Sys σ σc) : LocalInH init H p σ σc := by
  refine ⟨fun k x hx hnx ⟨q, a', b', γ', σ', _, hq, hr, hc⟩ => ?_,
    fun k hk hall ⟨q, a', b', _, hq⟩ => ?_⟩
  · exact hl.1 k x hx hnx ⟨n, init, H, q, a', b', γ', σ', hw, hp, hq, hr, hc⟩
  · exact hl.2 k hk hall ⟨n, init, H, q, a', b', hw, hp, hq⟩

/-- A contradiction within a history is a contradiction by a run of the
system. -/
theorem coordinationFree_to_H {Sys : System sp D} (h : Sys.CoordinationFree) :
    Sys.CoordinationFreeH :=
  ⟨fun n init H hw hp p a b γ o σ σc hH hrun hap =>
    localEvent_to_H hw hp p (h.1 n init H hw hp p a b γ o σ σc hH hrun hap),
   fun n init H hw hp p a b γ σ σc hH hrun hap =>
    localEvent_to_H hw hp p (h.2 n init H hw hp p a b γ σ σc hH hrun hap)⟩

theorem respSystem_coordinationFreeH (A : Table I O) (hcons : ConsistentOn sp A) :
    (respSystem (sp := sp) (D := D) A).CoordinationFreeH :=
  coordinationFree_to_H (respSystem_coordinationFree A hcons)

/-! ## With Availability, removals are contradicted in the same history -/

/-- With Availability, for any row `(k,x)` of a state `σ` of `p` and any
non-receive event `e` of `p` whose local prefix is receive-free, `x` is
emitted at input `k` by another participant `q` of a history that keeps `p`'s
prefix and event `e`: `q` (initial input below
`k`) records `input(k)` and then, by Availability, emits `x` locally.  The
participants are placed in separate blocks.  (Receive-freedom of `p`'s
prefix lets the history drop everything else.) -/
theorem availability_contradicts_gen (Sys : System sp D) (hA : AvailabilityAtEnd Sys)
    {n : Nat} {init : Fin n → I} {H : History sp D n} (hw : WF init H)
    (hp : Produced Sys n init H) {p q : Fin n} (hqp : q ≠ p)
    {a b : List (LEv sp D n)} {e : LEv sp D n} {σ : State sp}
    (hH : H p = a ++ e :: b) (hnr : ∀ q' k j d, LEv.recv q' k j d ∉ a)
    (hne : ∀ q' k j d, e ≠ LEv.recv q' k j d)
    {k : I} {x : O} (hx : σ.R k x) (hqk : init q ≼ k) :
    ∃ H' : History sp D n, WF init H' ∧ Produced Sys n init H' ∧
      H' p = a ++ [e] ∧
      ∃ (a' b' : List (LEv sp D n)) (γ' : List (Commitment sp)) (σ' : State sp),
        H' q = a' ++ LEv.out γ' x :: b' ∧ LRun (canon sp (init q)) a' σ' ∧ σ'.cur = k := by
  classical
  let H1 : History sp D n := fun r =>
    if r = p then a ++ [e] else if r = q then [LEv.inp k] else []
  have h1p : H1 p = a ++ [e] := by simp [H1]
  have h1q : H1 q = [LEv.inp k] := by simp [H1, hqp]
  have h1r : ∀ r, r ≠ p → r ≠ q → H1 r = [] := fun r h1 h2 => by simp [H1, h1, h2]
  have hpre : H p = (a ++ [e]) ++ b := by rw [hH]; simp
  -- no receives in `H1`
  have hnrecv : ∀ r a'' q' kk j d b'', H1 r ≠ a'' ++ LEv.recv q' kk j d :: b'' := by
    intro r a'' q' kk j d b'' h
    have hm : LEv.recv q' kk j d ∈ H1 r := by rw [h]; simp
    by_cases hr : r = p
    · subst hr; rw [h1p] at hm
      rcases List.mem_append.1 hm with hm | hm
      · exact hnr q' kk j d hm
      · simp at hm; exact hne q' kk j d hm.symm
    · by_cases hr' : r = q
      · subst hr'; rw [h1q] at hm; simp at hm
      · rw [h1r r hr hr'] at hm; simp at hm
  -- `q`'s state after `input(k)`
  have hRk : (canon sp (init q)).R k x := ⟨σ.sub _ _ hx, hqk⟩
  let τ1 : State sp :=
    { cur := k
      R := inputTable (canon sp (init q)) k
      sub := fun k' x' h => (canon sp (init q)).sub k' x' h.1
      hasCur := ⟨x, hRk, PO.refl k⟩
      above := fun _ _ h => h.2 }
  have s1 : Step (canon sp (init q)) (.input k) τ1 := Step.input _ τ1 k ⟨x, hRk⟩ rfl rfl
  have hlq : LRun (D := D) (n := n) (canon sp (init q)) [LEv.inp k] τ1 := .inp s1 (.nil _)
  have hw1 : WF init H1 := by
    refine ⟨fun r => ?_, fun r a'' q' kk j d b'' h => absurd h (hnrecv r a'' q' kk j d b'')⟩
    by_cases hr : r = p
    · subst hr; rw [h1p]
      obtain ⟨τ, hτ⟩ := hw.1 r
      rw [hpre] at hτ
      obtain ⟨τ', h', _⟩ := lrun_append.1 hτ
      exact ⟨τ', h'⟩
    · by_cases hr' : r = q
      · subst hr'; rw [h1q]; exact ⟨τ1, hlq⟩
      · rw [h1r r hr hr']; exact ⟨_, .nil _⟩
  have hp1 : Produced Sys n init H1 := by
    intro r
    by_cases hr : r = p
    · subst hr; rw [h1p]
      have := hp r; rw [hpre] at this; exact compliant_prefix this
    · by_cases hr' : r = q
      · subst hr'; rw [h1q]
        intro a'' e b'' h
        cases a'' with
        | nil => simp at h; obtain ⟨rfl, _⟩ := h; trivial
        | cons _ _ => simp at h
      · rw [h1r r hr hr']; intro a'' e b'' h; simp at h
  let comp : Fin n → Nat := fun r => r.val
  have hpart1 : Partitioned H1 comp :=
    ⟨⟨p, q, fun h => hqp (Fin.ext h).symm⟩,
      fun r a'' q' kk j d b'' h => absurd h (hnrecv r a'' q' kk j d b'')⟩
  have hτ1 : LRun (canon sp (init q)) (H1 q) τ1 := by rw [h1q]; exact hlq
  have hxτ : τ1.R τ1.cur x := ⟨hRk, PO.refl k⟩
  obtain ⟨ext, hw', hp', _, hloc, hni, γ', hγ'⟩ :=
    hA n init H1 comp hw1 hp1 hpart1 q τ1 hτ1 x hxτ
  refine ⟨fun r => H1 r ++ ext r, hw', hp', ?_, ?_⟩
  · have : ext p = [] := hloc p (fun h => hqp (Fin.ext h).symm)
    show H1 p ++ ext p = _
    rw [this, h1p, List.append_nil]
  · obtain ⟨a2, b2, hab⟩ := List.append_of_mem hγ'
    refine ⟨LEv.inp k :: a2, b2, γ', ?_⟩
    have hHq : (fun r => H1 r ++ ext r) q = (LEv.inp k :: a2) ++ LEv.out γ' x :: b2 := by
      show H1 q ++ ext q = _; rw [h1q, hab]; simp
    obtain ⟨τ, hτ⟩ := hw'.1 q
    rw [hHq] at hτ
    obtain ⟨σ', hσ', _⟩ := lrun_append.1 hτ
    refine ⟨σ', hHq, hσ', ?_⟩
    have hσ'' := hσ'
    cases hσ'' with
    | inp hs hrest =>
      have hc := lrun_noinp hrest (fun j hj => hni q j (by rw [hab]; exact List.mem_append_left _ hj))
      rw [hc]
      obtain ⟨_, hcur, _⟩ := step_input_inv hs
      exact hcur

/-- With Availability, a row `(k,x)` removed by an output event of `p`, whose
local prefix is receive-free, is emitted at input `k` by another participant
`q` of a history that keeps `p`'s prefix and event: `q` (initial input below
`k`) records `input(k)` and then, by Availability, emits `x` locally.  The
participants are placed in separate blocks.  (Receive-freedom of `p`'s
prefix lets the history drop everything else.) -/
theorem availability_contradicts_removal (Sys : System sp D) (hA : AvailabilityAtEnd Sys)
    {n : Nat} {init : Fin n → I} {H : History sp D n} (hw : WF init H)
    (hp : Produced Sys n init H) {p q : Fin n} (hqp : q ≠ p)
    {a b : List (LEv sp D n)} {γ : List (Commitment sp)} {o : O} {σ σc : State sp}
    (hH : H p = a ++ LEv.out γ o :: b) (hnr : ∀ q' k j d, LEv.recv q' k j d ∉ a)
    (_hrun : LRun (canon sp (init p)) a σ) (_hap : applySeq σ γ = some σc)
    {k : I} {x : O} (hx : σ.R k x) (hqk : init q ≼ k) :
    ∃ H' : History sp D n, WF init H' ∧ Produced Sys n init H' ∧
      H' p = a ++ [LEv.out γ o] ∧
      ∃ (a' b' : List (LEv sp D n)) (γ' : List (Commitment sp)) (σ' : State sp),
        H' q = a' ++ LEv.out γ' x :: b' ∧ LRun (canon sp (init q)) a' σ' ∧ σ'.cur = k :=
  availability_contradicts_gen Sys hA hw hp hqp hH hnr (fun _ _ _ _ h => by cases h) hx hqk

/-- The same for a commit event: with Availability, a row `(k,x)` removed by
a commit event `Commit(γ)` of `p`, whose local prefix is receive-free, is
emitted at input `k` by another participant `q` (initial input below `k`) of a
history that keeps `p`'s prefix and commit event. -/
theorem availability_contradicts_commit (Sys : System sp D) (hA : AvailabilityAtEnd Sys)
    {n : Nat} {init : Fin n → I} {H : History sp D n} (hw : WF init H)
    (hp : Produced Sys n init H) {p q : Fin n} (hqp : q ≠ p)
    {a b : List (LEv sp D n)} {γ : List (Commitment sp)} {σ σc : State sp}
    (hH : H p = a ++ LEv.cmt γ :: b) (hnr : ∀ q' k j d, LEv.recv q' k j d ∉ a)
    (_hrun : LRun (canon sp (init p)) a σ) (_hap : applySeq σ γ = some σc)
    {k : I} {x : O} (hx : σ.R k x) (hqk : init q ≼ k) :
    ∃ H' : History sp D n, WF init H' ∧ Produced Sys n init H' ∧
      H' p = a ++ [LEv.cmt γ] ∧
      ∃ (a' b' : List (LEv sp D n)) (γ' : List (Commitment sp)) (σ' : State sp),
        H' q = a' ++ LEv.out γ' x :: b' ∧ LRun (canon sp (init q)) a' σ' ∧ σ'.cur = k :=
  availability_contradicts_gen Sys hA hw hp hqp hH hnr (fun _ _ _ _ h => by cases h) hx hqk

/-- Consequently a system with Availability whose output event removes a row
(receive-free prefix, another participant below the row's input) is not
coordination-free within histories. -/
theorem availability_not_coordinationFreeH (Sys : System sp D) (hA : AvailabilityAtEnd Sys)
    {n : Nat} {init : Fin n → I} {H : History sp D n} (hw : WF init H)
    (hp : Produced Sys n init H) {p q : Fin n} (hqp : q ≠ p)
    {a b : List (LEv sp D n)} {γ : List (Commitment sp)} {o : O} {σ σc : State sp}
    (hH : H p = a ++ LEv.out γ o :: b) (hnr : ∀ q' k j d, LEv.recv q' k j d ∉ a)
    (hrun : LRun (canon sp (init p)) a σ) (hap : applySeq σ γ = some σc)
    {k : I} {x : O} (hx : σ.R k x) (hnx : ¬ σc.R k x) (hqk : init q ≼ k) :
    ¬ Sys.CoordinationFreeH := by
  intro hcf
  obtain ⟨H', hw', hp', hH', a', b', γ', σ', hq, hr, hc⟩ :=
    availability_contradicts_removal Sys hA hw hp hqp hH hnr hrun hap hx hqk
  exact (hcf.1 n init H' hw' hp' p a [] γ o σ σc hH' hrun hap).1 k x hx hnx
    ⟨q, a', b', γ', σ', hqp, hq, hr, hc⟩

/-- Likewise a system with Availability whose commit event removes a row
(receive-free prefix, another participant below the row's input) is not
coordination-free within histories. -/
theorem availability_not_coordinationFreeH_commit (Sys : System sp D)
    (hA : AvailabilityAtEnd Sys)
    {n : Nat} {init : Fin n → I} {H : History sp D n} (hw : WF init H)
    (hp : Produced Sys n init H) {p q : Fin n} (hqp : q ≠ p)
    {a b : List (LEv sp D n)} {γ : List (Commitment sp)} {σ σc : State sp}
    (hH : H p = a ++ LEv.cmt γ :: b) (hnr : ∀ q' k j d, LEv.recv q' k j d ∉ a)
    (hrun : LRun (canon sp (init p)) a σ) (hap : applySeq σ γ = some σc)
    {k : I} {x : O} (hx : σ.R k x) (hnx : ¬ σc.R k x) (hqk : init q ≼ k) :
    ¬ Sys.CoordinationFreeH := by
  intro hcf
  obtain ⟨H', hw', hp', hH', a', b', γ', σ', hq, hr, hc⟩ :=
    availability_contradicts_commit Sys hA hw hp hqp hH hnr hrun hap hx hqk
  exact (hcf.2 n init H' hw' hp' p a [] γ σ σc hH' hrun hap).1 k x hx hnx
    ⟨q, a', b', γ', σ', hqp, hq, hr, hc⟩

/-! ## Removed rows of a canonical event -/

/-- A row removed by the canonical commitment for `u` has no common refinement
with `u` in the state. -/
theorem rm_no_common {σ : State sp} {u : O} {k : I} {x : O} (h : Rm σ u k x) :
    ¬ ∃ w, σ.R k w ∧ u ≼ w ∧ x ≼ w := by
  rintro ⟨w, hw, huw, hxw⟩
  rcases h with ⟨_, hs⟩ | ⟨hx, hn, _, hret⟩
  · exact hs ⟨w, hw, huw⟩
  · exact hret ⟨hx, hn, w, hw, huw, hxw⟩

/-- What a canonical output event's commitments remove. -/
theorem canonical_removed {σ σc : State sp} {u : O} {γ : List (Commitment sp)}
    (hγ : γ = [] ∨ γ = [kc u]) (hap : applySeq σ γ = some σc) {k : I} {x : O}
    (hx : σ.R k x) (hnx : ¬ σc.R k x) : Rm σ u k x ∧ ∃ hu : σ.R σ.cur u, σc = kcState σ u hu := by
  rcases hγ with rfl | rfl
  · simp [applySeq] at hap; subst hap; exact absurd hx hnx
  · obtain ⟨hu, rfl⟩ := kc_apply_some hap
    refine ⟨Classical.byContradiction fun h => hnx ⟨hx, h⟩, hu, rfl⟩

/-! ## Shared nothing: one owner orders, or two -/

/-- Orders of two transactions: undecided, `A` before `B`, `B` before `A`. -/
inductive Ord3 where
  | bot | ab | ba
  deriving DecidableEq

def Ord3.le : Ord3 → Ord3 → Prop
  | x, y => x = y ∨ x = .bot

instance : PO Ord3 where
  le := Ord3.le
  refl := fun _ => Or.inl rfl
  trans := by
    intro x y z h1 h2
    unfold Ord3.le at *
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp
  antisymm := by
    intro x y h1 h2
    unfold Ord3.le at *
    cases x <;> cases y <;> simp_all

theorem ord3_le_iff (x y : Ord3) : x ≼ y ↔ (x = y ∨ x = .bot) := Iff.rfl

/-- One input; every order is permitted. -/
def ordSpec : Spec Unit Ord3 where
  S := fun _ _ => True
  total := fun _ => ⟨.bot, trivial⟩

theorem canon_ord_R (k : Unit) (x : Ord3) : (canon ordSpec ()).R k x :=
  ⟨trivial, trivial⟩

/-- Emitting `A before B` is a commitment: it is not exposable, since it must
choose against `B before A`. -/
theorem ordSpec_ab_not_exposable : ¬ Exposable (canon ordSpec ()) .ab := by
  intro h
  obtain ⟨u, _, h1, h2⟩ := h () .ba (canon_ord_R _ _) (by
    rw [ord3_le_iff]; simp)
  rw [ord3_le_iff] at h1 h2
  rcases h1 with rfl | h1 <;> simp_all

/-- The owner (participant `0`) may emit any order; every other participant
may emit only `bot`.  Output events are canonical. -/
noncomputable def ownerSys (D : Type) : System ordSpec D where
  basis := fun c => ∃ u, c = kc u
  strat := fun _ _ p _ e =>
    match e with
    | .out γ u => (γ = [] ∨ γ = [kc u]) ∧ (u = .bot ∨ p.val = 0)
    | _ => False

/-- Two owners: every participant may emit any order. -/
noncomputable def twoOwnerSys (D : Type) : System ordSpec D where
  basis := fun c => ∃ u, c = kc u
  strat := fun _ _ _ _ e =>
    match e with
    | .out γ u => γ = [] ∨ γ = [kc u]
    | _ => False

/-- `bot` is never removed by a canonical event (it is refined by the emitted
output), and nothing is removed when `bot` is emitted. -/
theorem ord_removed {σ : State ordSpec} {u x : Ord3} (h : Rm σ u () x) (hu : σ.R () u) :
    u ≠ .bot ∧ x ≠ .bot := by
  have hx : σ.R () x := by rcases h with h | h <;> exact h.1
  constructor
  · rintro rfl
    exact rm_no_common h ⟨x, hx, by rw [ord3_le_iff]; exact Or.inr rfl, PO.refl _⟩
  · rintro rfl
    exact rm_no_common h ⟨u, hu, PO.refl _, by rw [ord3_le_iff]; exact Or.inr rfl⟩

/-- **One owner is coordination-free.**  Only the owner chooses an order, and
no other participant emits one. -/
theorem ownerSys_coordinationFreeH (D : Type) : (ownerSys D).CoordinationFreeH := by
  refine ⟨?_, fun n init H _ hp p a b γ σ σc hH _ _ => (hp p a (.cmt γ) b hH).2.elim⟩
  intro n init H _ hp p a b γ o σ σc hH _ hap
  have hAl := hp p a (.out γ o) b hH
  obtain ⟨_, hγ, hown⟩ := hAl
  refine ⟨fun k x hx hnx => ?_, fun k ⟨x, hx⟩ hall => ?_⟩
  · rintro ⟨q, a', b', γ', σ', hqp, hq, _, _⟩
    obtain ⟨hrm, hu, _⟩ := canonical_removed hγ hap hx hnx
    cases k
    obtain ⟨hob, hxb⟩ := ord_removed hrm hu
    have hp0 : p.val = 0 := hown.resolve_left hob
    obtain ⟨_, _, hqx⟩ := hp q a' (.out γ' x) b' hq
    have hq0 : q.val = 0 := hqx.resolve_left hxb
    exact hqp (Fin.ext (hq0.trans hp0.symm))
  · rintro ⟨q, a', b', _, _⟩
    cases k
    rcases hγ with rfl | rfl
    · simp [applySeq] at hap; subst hap; exact hall x hx
    · obtain ⟨hu', rfl⟩ := kc_apply_some hap
      exact hall o ⟨hu', not_rm_of_le hu' (PO.refl o)⟩

/-- A canonical output event of `u` at `σ_S(())`, as a one-event participant
history. -/
theorem ord_emit (u : Ord3) :
    ∃ γ τ, (γ = [] ∨ γ = [kc u]) ∧ applySeq (canon ordSpec ()) γ = some τ ∧
      Exposable τ u ∧ ∃ ρ, LRun (D := D) (n := 2) (canon ordSpec ()) [LEv.out γ u] ρ := by
  have hu : (canon ordSpec ()).R (canon ordSpec ()).cur u := canon_ord_R _ _
  obtain ⟨γ, σc, hγ, ha, hcu, hexp⟩ := kc_legal hu
  let τ : State ordSpec :=
    { cur := σc.cur, R := outputTable σc u, sub := fun k x h => σc.sub k x h.1,
      hasCur := ⟨u, hcu, PO.refl u⟩, above := fun k x h => σc.above k x h.1 }
  exact ⟨γ, σc, hγ, ha, hexp, τ, .out ha (Step.output σc τ u hcu rfl rfl) hexp (.nil τ)⟩

/-- **Two owners coordinate.**  Participant `0` emits `A before B`, choosing
against `B before A`, which participant `1` emits in the same history. -/
theorem twoOwnerSys_not_coordinationFreeH (D : Type) : ¬ (twoOwnerSys D).CoordinationFreeH := by
  intro hcf
  obtain ⟨γ0, σ0, hγ0, ha0, hex0, ρ0, hr0⟩ := ord_emit (D := D) .ab
  obtain ⟨γ1, _, hγ1, _, _, ρ1, hr1⟩ := ord_emit (D := D) .ba
  let init : Fin 2 → Unit := fun _ => ()
  let H : History ordSpec D 2 := fun r => if r.val = 0 then [LEv.out γ0 .ab] else [LEv.out γ1 .ba]
  have hH0 : H 0 = [] ++ LEv.out γ0 .ab :: [] := rfl
  have hH1 : H 1 = [] ++ LEv.out γ1 .ba :: [] := rfl
  have hfin : ∀ r : Fin 2, r = 0 ∨ r = 1 := by decide
  have hnr : ∀ r a q k j d b, H r ≠ a ++ LEv.recv q k j d :: b := by
    intro r a q k j d b h
    have hm : LEv.recv q k j d ∈ H r := by rw [h]; simp
    rcases hfin r with rfl | rfl
    · rw [hH0] at hm; simp at hm
    · rw [hH1] at hm; simp at hm
  have hw : WF init H := by
    refine ⟨fun r => ?_, fun r a q k j d b h => absurd h (hnr r a q k j d b)⟩
    rcases hfin r with rfl | rfl
    · exact ⟨ρ0, hr0⟩
    · exact ⟨ρ1, hr1⟩
  have hbasis : ∀ (u : Ord3) (γ : List (Commitment ordSpec)), (γ = [] ∨ γ = [kc u]) →
      ∀ c ∈ γ, (twoOwnerSys D).basis c := by
    intro u γ hγ c hc
    rcases hγ with rfl | rfl
    · cases hc
    · simp at hc; exact ⟨u, hc⟩
  have hp : Produced (twoOwnerSys D) 2 init H := by
    intro r a e b h
    rcases hfin r with rfl | rfl
    · rw [hH0] at h
      cases a with
      | nil => simp at h; obtain ⟨rfl, _⟩ := h; exact ⟨hbasis _ _ hγ0, hγ0⟩
      | cons _ _ => simp at h
    · rw [hH1] at h
      cases a with
      | nil => simp at h; obtain ⟨rfl, _⟩ := h; exact ⟨hbasis _ _ hγ1, hγ1⟩
      | cons _ _ => simp at h
  -- after participant 0's commitments the row `((), ba)` is gone
  have hgone : ¬ σ0.R () .ba := by
    intro hba
    obtain ⟨u, _, h1, h2⟩ := hex0 () .ba hba (by rw [ord3_le_iff]; simp)
    rw [ord3_le_iff] at h1 h2
    rcases h1 with rfl | h1 <;> simp_all
  exact (hcf.1 2 init H hw hp 0 [] [] γ0 .ab (canon ordSpec ()) σ0 hH0 (.nil _) ha0).1
    () .ba (canon_ord_R _ _) hgone ⟨1, [], [], γ1, canon ordSpec (), by decide, hH1, .nil _, rfl⟩

/-! ## A local choice -/

/-- Two incomparable outputs. -/
inductive Two where
  | o | x
  deriving DecidableEq

instance : PO Two where
  le := fun a b => a = b
  refl := fun _ => rfl
  trans := fun h1 h2 => h1.trans h2
  antisymm := fun h _ => h

/-- One input, both outputs permitted. -/
def lcSpec : Spec Unit Two where
  S := fun _ _ => True
  total := fun _ => ⟨.o, trivial⟩

/-- Only `o` must stay available. -/
def lcA : Table Unit Two := fun _ v => v = .o

theorem lcSpec_consistentOn : ConsistentOn lcSpec lcA := by
  intro rows hrows _ _
  exact ⟨.o, trivial, fun r hr => (hrows r hr : r.2 = .o) ▸ rfl⟩

/-- Emitting `o` must commit: it chooses against `x`. -/
theorem lcSpec_o_not_exposable : ¬ Exposable (canon lcSpec ()) .o := by
  intro h
  obtain ⟨u, _, h1, h2⟩ := h () .x ⟨trivial, trivial⟩ (by intro h; cases h)
  have : (Two.o : Two) = .x := h1.trans h2.symm
  cases this

/-- Yet the system that keeps `A` available is coordination-free. -/
theorem lc_coordinationFreeH (D : Type) :
    (respSystem (sp := lcSpec) (D := D) lcA).CoordinationFreeH :=
  respSystem_coordinationFreeH lcA lcSpec_consistentOn

/-! ## One owner coordinates, but not distributedly -/

/-- A history in which the owner (participant `0`) emits `u` by its canonical
output event and participant `1` is idle. -/
theorem owner_history (D : Type) (u : Ord3) :
    ∃ (γ : List (Commitment ordSpec)) (σc : State ordSpec) (H : History ordSpec D 2),
      (γ = [] ∨ γ = [kc u]) ∧ applySeq (canon ordSpec ()) γ = some σc ∧ Exposable σc u ∧
      WF (fun _ => ()) H ∧ Produced (ownerSys D) 2 (fun _ => ()) H ∧
      H 0 = [] ++ LEv.out γ u :: [] := by
  obtain ⟨γ, σc, hγ, ha, hex, ρ, hr⟩ := ord_emit (D := D) u
  let H : History ordSpec D 2 := fun r => if r.val = 0 then [LEv.out γ u] else []
  have hH0 : H 0 = [] ++ LEv.out γ u :: [] := rfl
  have hH1 : H 1 = [] := rfl
  have hfin : ∀ r : Fin 2, r = 0 ∨ r = 1 := by decide
  have hnr : ∀ r a q k j d b, H r ≠ a ++ LEv.recv q k j d :: b := by
    intro r a q k j d b h
    have hm : LEv.recv q k j d ∈ H r := by rw [h]; simp
    rcases hfin r with rfl | rfl
    · rw [hH0] at hm; simp at hm
    · rw [hH1] at hm; simp at hm
  refine ⟨γ, σc, H, hγ, ha, hex, ⟨fun r => ?_, fun r a q k j d b h => absurd h (hnr r a q k j d b)⟩,
    ?_, hH0⟩
  · rcases hfin r with rfl | rfl
    · exact ⟨ρ, hr⟩
    · exact ⟨_, .nil _⟩
  · intro r a e b h
    rcases hfin r with rfl | rfl
    · rw [hH0] at h
      cases a with
      | nil =>
        simp at h; obtain ⟨rfl, _⟩ := h
        refine ⟨fun c hc => ?_, hγ, Or.inr rfl⟩
        rcases hγ with rfl | rfl
        · cases hc
        · simp at hc; exact ⟨u, hc⟩
      | cons _ _ => simp at h
    · rw [hH1] at h; simp at h

/-- **One owner coordinates.**  The owner's choice of `A before B` is
contradicted by another run of the same system, in which the owner chooses
`B before A`: locking on a single participant is coordination, though not
distributed coordination (`ownerSys_coordinationFreeH`). -/
theorem ownerSys_not_coordinationFree (D : Type) : ¬ (ownerSys D).CoordinationFree := by
  intro hcf
  obtain ⟨γ0, σ0, H, _, ha0, hex0, hw, hp, hH0⟩ := owner_history D .ab
  obtain ⟨γ1, _, H', _, _, _, hw', hp', hH0'⟩ := owner_history D .ba
  have hgone : ¬ σ0.R () .ba := by
    intro hba
    obtain ⟨u, _, h1, h2⟩ := hex0 () .ba hba (by rw [ord3_le_iff]; simp)
    rw [ord3_le_iff] at h1 h2
    rcases h1 with rfl | h1 <;> simp_all
  exact (hcf.1 2 _ H hw hp 0 [] [] γ0 .ab (canon ordSpec ()) σ0 hH0 (.nil _) ha0).1
    () .ba (canon_ord_R _ _) hgone ⟨2, _, H', 0, [], [], γ1, canon ordSpec (), hw', hp', hH0', .nil _, rfl⟩

end CAP
end CC
