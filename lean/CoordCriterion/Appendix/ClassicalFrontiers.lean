import CoordCriterion.Appendix.Classical
import CoordCriterion.Appendix.ProductFrontier
import CoordCriterion.Appendix.Frontiers
import CoordCriterion.Appendix.Guarded
import CoordCriterion.CALM.Lemmas
import CoordCriterion.Appendix.DeploymentCAP

/-!
# Classical problems: leader election, snapshots, queues, search structures (Appendix G)

Namespace `CC.Apps`.  Supports the subsections of
`paper/app-classical-problems.tex` on queues, search structures, and
snapshots.

* **The causal queue.**  Inputs are causal histories of enqueues (`Hist`); an
  output is a `DReport`: a set `D` of dequeued enqueues with a strict order
  that the queue guarantees among them, ordered by `DReport.le` (more items,
  more order, and earlier items stay a down-set).  `cqSpec` reports exactly the
  causal order on a causally closed set; it satisfies Lifted Monotonicity
  (`cqSpec_liftedMono`).  Maximality: in any spec with a directed fiber at `h`
  that lets each enqueue be dequeued together with exactly its causal past,
  every reported order is causal (`directed_orders_causal`); with complete
  reporting this pins the spec down to `cqSpec` (`cq_unique`); a spec that
  reports a total order on two concurrent enqueues is not directed there
  (`total_report_not_directed`).
* **Search structures.**  Claim sets bounded by a validity map
  (`boundSpec`) satisfy Lifted Monotonicity iff the map grows
  (`boundSpec_liftedMono_iff`).  The least growing map containing `X` is the
  remembered map (`remembered_*`); among maps that depend only on the current
  state it is `stateRemembered` (`stateRemembered_*`), under state-determined
  continuations (`StateDet`).  For restructuring histories of
  `Appendix/Frontiers.lean`, continuations are state-determined
  (`restr_stateDet`), so forward reachability contains the state-remembered
  exact claims (`fwd_contains_stateRemembered`), with equality exactly under
  the earlier-exactness condition (`fwd_eq_iff`).
* **Snapshots.**  Histories of updates and scans labeled by participant
  (`proc`) and kind (`scan`).  A global-snapshot view of `p` assigns to each
  of `p`'s scans a cut (`ClCut`); the product of these views (`clSpec`) is
  monotone across partitions under the owner deployment (`cl_monoAcross`,
  `cl_cap`).  The atomic snapshot (`atSpec`, via the strengthening
  `atomicStr`) selects the tuples that one strict total order of all events
  explains (`LinExt`, which always exists: `linExt_exists`); its views are
  global-snapshot views (`atomicView_cl`).  With two participants and four
  events as in `Four`, it is not monotone across partitions under the owner
  deployment (`atomic_not_monoAcross`, `atomic_no_cap`), through the local
  form `local_not_monoAcross` of Theorem `thm:product-frontier`(2).
* **Leader election.**  Outputs `Flat`: `⊥` below incomparable leaders.  With
  the participant list `All` fixed in the spec, max-candidate election is
  functional and monotone (`leaderAll_mono`, `leaderAll_consistent`); with
  only the candidates heard, election is not monotone (`leader_not_monotone`).
* **Memory as one participant.**  A stage that is a monotone function of the
  upstream's outputs makes the pipeline proper (`monotone_stage_proper`).
-/

namespace CC
namespace Apps

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The causal queue -/

section CausalQueue
variable {Ev : Type}

/-- A dequeue report: a set of dequeued enqueues with the order the queue
guarantees among them. -/
structure DReport (Ev : Type) where
  D : Ev → Prop
  lt : Ev → Ev → Prop
  supp : ∀ a b, lt a b → D a ∧ D b

/-- `x ⪯ y`: `y` dequeues at least the items of `x`, guarantees the same order
among them, and places no new item before an item of `x`. -/
def DReport.le (x y : DReport Ev) : Prop :=
  (∀ a, x.D a → y.D a) ∧ (∀ a b, x.D a → x.D b → (x.lt a b ↔ y.lt a b)) ∧
  ∀ a b, x.D b → y.lt a b → x.D a

theorem DReport.ext' {x y : DReport Ev} (h1 : x.D = y.D) (h2 : x.lt = y.lt) : x = y := by
  cases x; cases y; cases h1; cases h2; rfl

theorem DReport.lt_of_le {x y : DReport Ev} (h : DReport.le x y) {a b : Ev} (hab : x.lt a b) :
    y.lt a b :=
  ((h.2.1 a b (x.supp a b hab).1 (x.supp a b hab).2).1 hab)

instance instPODReport (Ev : Type) : PO (DReport Ev) where
  le := DReport.le
  refl x := ⟨fun _ h => h, fun _ _ _ _ => Iff.rfl, fun a b _ hab => (x.supp a b hab).1⟩
  trans {x y z} h1 h2 := by
    refine ⟨fun a h => h2.1 a (h1.1 a h), fun a b ha hb => ?_, fun a b hb hab => ?_⟩
    · exact (h1.2.1 a b ha hb).trans (h2.2.1 a b (h1.1 a ha) (h1.1 b hb))
    · have hya := h2.2.2 a b (h1.1 b hb) hab
      have hy : y.lt a b := (h2.2.1 a b hya (h1.1 b hb)).2 hab
      exact h1.2.2 a b hb hy

instance (Ev : Type) : PO.Antisymm (DReport Ev) where
  antisymm {x y} h1 h2 :=
    DReport.ext' (funext fun a => propext ⟨h1.1 a, h2.1 a⟩)
      (funext fun a => funext fun b => propext ⟨fun h => DReport.lt_of_le h1 h,
        fun h => DReport.lt_of_le h2 h⟩)

/-- The causal queue's report at `h`: a causally closed set of enqueues of `h`,
ordered exactly by causality. -/
def CQ (h : Hist Ev) (x : DReport Ev) : Prop :=
  (∀ a, x.D a → h.s.1 a) ∧ (∀ a b, x.D b → h.lt a b → x.D a) ∧
  ∀ a b, x.lt a b ↔ (x.D a ∧ x.D b ∧ h.lt a b)

/-- The report of a causally closed set `D` of `h`, with the causal order. -/
def causalReport (h : Hist Ev) (D : Ev → Prop) : DReport Ev where
  D := D
  lt a b := D a ∧ D b ∧ h.lt a b
  supp _ _ h := ⟨h.1, h.2.1⟩

/-- The causal queue specification. -/
def cqSpec (Ev : Type) : Spec (Hist Ev) (DReport Ev) where
  P := CQ
  total h := ⟨causalReport h (fun _ => False),
    fun _ hx => hx.elim, fun _ _ hb => hb.elim, fun _ _ => Iff.rfl⟩

theorem cq_commonExpansion : (cqSpec Ev).CommonExpansion := by
  intro rows hrows j hj
  let D : Ev → Prop := fun a => ∃ r ∈ rows, r.2.D a
  refine ⟨causalReport j D, ⟨?_, ?_, fun _ _ => Iff.rfl⟩, ?_⟩
  · rintro a ⟨r, hr, ha⟩
    exact (hj r hr).1 a ((hrows r hr).1 a ha)
  · rintro a b ⟨r, hr, hb⟩ hab
    have hsb := (hrows r hr).1 b hb
    have hsa := (hj r hr).2.1 a b hsb hab
    exact ⟨r, hr, (hrows r hr).2.1 a b hb (((hj r hr).2.2 a b hsa hsb).2 hab)⟩
  · intro r hr
    have hq := hrows r hr
    refine ⟨fun a ha => ⟨r, hr, ha⟩, fun a b ha hb => ?_, fun a b hb hab => ?_⟩
    · rw [hq.2.2 a b]
      show _ ↔ (∃ r ∈ rows, r.2.D a) ∧ (∃ r ∈ rows, r.2.D b) ∧ j.lt a b
      have e := (hj r hr).2.2 a b (hq.1 a ha) (hq.1 b hb)
      exact ⟨fun ⟨_, _, hl⟩ => ⟨⟨r, hr, ha⟩, ⟨r, hr, hb⟩, e.1 hl⟩,
        fun ⟨_, _, hl⟩ => ⟨ha, hb, e.2 hl⟩⟩
    · obtain ⟨_, _, hl⟩ := hab
      have hsb := hq.1 b hb
      have hsa := (hj r hr).2.1 a b hsb hl
      exact hq.2.1 a b hb (((hj r hr).2.2 a b hsa hsb).2 hl)

/-- **The causal queue satisfies Lifted Monotonicity.** -/
theorem cqSpec_liftedMono : (cqSpec Ev).LiftedMono :=
  (liftedMono_iff_commonExpansion _).2 cq_commonExpansion

/-- The causal past of `b`, with `b`. -/
def below (h : Hist Ev) (b : Ev) : Ev → Prop := fun a => a = b ∨ h.lt a b

/-- **Maximality of the causal queue.**  Let a spec have a directed fiber at
`h` (as every monotone spec does), and let it permit at `h`, for each enqueue
`b` of `h`, some report whose dequeued set is `b` with its causal past.  Then
every order between distinct items that a report permitted at `h` guarantees
is causal. -/
theorem directed_orders_causal (T : Spec (Hist Ev) (DReport Ev)) (h : Hist Ev)
    (hdir : JointLift (T.P h) (T.P h))
    (hdown : ∀ b, h.s.1 b → ∃ x, T.P h x ∧ x.D = below h b)
    {x : DReport Ev} (hx : T.P h x) {a b : Ev} (hab : x.lt a b) (hne : a ≠ b)
    (hb : h.s.1 b) : h.lt a b := by
  obtain ⟨xb, hxb, hD⟩ := hdown b hb
  obtain ⟨u, _, hall⟩ := hdir [x, xb] (by simp) (by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact hx
    · exact hxb)
  have hxu : x ≼ u := hall x (by simp)
  have hbu : xb ≼ u := hall xb (by simp)
  have hu : u.lt a b := DReport.lt_of_le hxu hab
  have hbb : xb.D b := by rw [hD]; exact Or.inl rfl
  have ha : xb.D a := hbu.2.2 a b hbb hu
  rw [hD] at ha
  rcases ha with rfl | hlt
  · exact absurd rfl hne
  · exact hlt

/-- The same, for any spec satisfying Lifted Monotonicity. -/
theorem monotone_orders_causal (T : Spec (Hist Ev) (DReport Ev)) (hT : T.LiftedMono)
    (h : Hist Ev) (hdown : ∀ b, h.s.1 b → ∃ x, T.P h x ∧ x.D = below h b)
    {x : DReport Ev} (hx : T.P h x) {a b : Ev} (hab : x.lt a b) (hne : a ≠ b)
    (hb : h.s.1 b) : h.lt a b :=
  directed_orders_causal T h (hT h h (PO.refl h)) hdown hx hab hne hb

/-- `b` with its causal past is causally closed. -/
theorem below_closed (h : Hist Ev) {b : Ev} (hb : h.s.1 b) :
    (∀ a, below h b a → h.s.1 a) ∧ ∀ a c, below h b c → h.lt a c → below h b a := by
  refine ⟨fun a ha => ?_, fun a c hc hac => ?_⟩
  · rcases ha with rfl | hlt
    · exact hb
    · exact (h.supp _ _ hlt).1
  · rcases hc with rfl | hlt
    · exact Or.inr hac
    · exact Or.inr (h.trans _ _ _ hac hlt)

/-- **The causal queue is the only monotone queue spec with complete
reporting.**  Suppose a spec satisfies Lifted Monotonicity; its reports list
only enqueues of the input, never skip a causal predecessor, guarantee at
least the causal order, and order no item before itself; and every causally
closed set of enqueues is the set of some report it permits.  Then it
permits exactly the reports of the causal queue. -/
theorem cq_unique (T : Spec (Hist Ev) (DReport Ev)) (hT : T.LiftedMono)
    (hsupp : ∀ h x, T.P h x → ∀ a, x.D a → h.s.1 a)
    (hclosed : ∀ h x, T.P h x → ∀ a b, x.D b → h.lt a b → x.D a)
    (hfifo : ∀ h x, T.P h x → ∀ a b, x.D a → x.D b → h.lt a b → x.lt a b)
    (hirr : ∀ h x, T.P h x → ∀ a, ¬ x.lt a a)
    (hall : ∀ h (D : Ev → Prop), (∀ a, D a → h.s.1 a) → (∀ a b, D b → h.lt a b → D a) →
      ∃ x, T.P h x ∧ x.D = D) :
    ∀ h x, T.P h x ↔ (cqSpec Ev).P h x := by
  have hdown : ∀ h b, h.s.1 b → ∃ x, T.P h x ∧ x.D = below h b :=
    fun h b hb => hall h _ (below_closed h hb).1 (below_closed h hb).2
  have hord : ∀ h x, T.P h x → ∀ a b, x.lt a b ↔ (x.D a ∧ x.D b ∧ h.lt a b) := by
    intro h x hx a b
    constructor
    · intro hab
      have hs := x.supp a b hab
      by_cases hne : a = b
      · subst hne; exact absurd hab (hirr h x hx a)
      · exact ⟨hs.1, hs.2,
          monotone_orders_causal T hT h (hdown h) hx hab hne (hsupp h x hx b hs.2)⟩
    · rintro ⟨ha, hb, hl⟩; exact hfifo h x hx a b ha hb hl
  intro h x
  constructor
  · intro hx; exact ⟨hsupp h x hx, hclosed h x hx, hord h x hx⟩
  · intro hq
    obtain ⟨y, hy, hyD⟩ := hall h x.D hq.1 hq.2.1
    have : y = x := by
      apply DReport.ext' hyD
      funext a b
      apply propext
      rw [hord h y hy, hq.2.2 a b, hyD]
    rw [← this]; exact hy

/-- **Total reports.**  If a spec permits at `h`, for each enqueue, a report
of exactly that enqueue and its causal past, and also a report that orders
two concurrent enqueues of `h` (as a total dequeue order does), then its
fiber at `h` is not directed, so the spec does not satisfy Lifted
Monotonicity. -/
theorem total_report_not_directed (T : Spec (Hist Ev) (DReport Ev)) (h : Hist Ev)
    (hdown : ∀ b, h.s.1 b → ∃ x, T.P h x ∧ x.D = below h b)
    {a b : Ev} (ha : h.s.1 a) (hb : h.s.1 b) (hne : a ≠ b)
    (hca : ¬ h.lt a b) (hcb : ¬ h.lt b a)
    {x : DReport Ev} (hx : T.P h x) (hord : x.lt a b ∨ x.lt b a) :
    ¬ JointLift (T.P h) (T.P h) ∧ ¬ T.LiftedMono := by
  have key : ¬ JointLift (T.P h) (T.P h) := by
    intro hdir
    rcases hord with hab | hba
    · exact hca (directed_orders_causal T h hdir hdown hx hab hne hb)
    · exact hcb (directed_orders_causal T h hdir hdown hx hba (Ne.symm hne) ha)
  exact ⟨key, fun hT => key (hT h h (PO.refl h))⟩

end CausalQueue

/-! ## Search structures: bounded claim sets and remembered claims -/

section Lookup
variable {I C : Type} [PO I]

/-- The spec whose outputs at `i` are the sets of claims valid under `V`
at `i`, ordered by inclusion. -/
def boundSpec (V : I → C → Prop) : Spec I (ESet C) where
  P i S := ∀ c, S.mem c → V i c
  total _ := ⟨⟨fun _ => False⟩, fun _ h => h.elim⟩

/-- `V` grows with the input. -/
def Grows (V : I → C → Prop) : Prop := ∀ i j, i ≼ j → ∀ c, V i c → V j c

/-- **Bounded claim sets satisfy Lifted Monotonicity exactly when the validity
map grows.** -/
theorem boundSpec_liftedMono_iff (V : I → C → Prop) :
    (boundSpec V).LiftedMono ↔ Grows V := by
  constructor
  · intro hL i j hij c hc
    obtain ⟨u, hu, hall⟩ := hL i j hij [⟨fun d => d = c⟩] (by simp) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx
      intro d hd; rw [hd]; exact hc)
    exact hu c (hall ⟨fun d => d = c⟩ (List.mem_singleton_self _) c rfl)
  · intro hG i j hij X _ hX
    refine ⟨⟨fun c => ∃ x ∈ X, x.mem c⟩, fun c ⟨x, hx, hc⟩ => hG i j hij c (hX x hx c hc),
      fun x hx c hc => ⟨x, hx, hc⟩⟩

/-- Claims valid at some input below `i`. -/
def remembered (X : I → C → Prop) : I → C → Prop := fun i c => ∃ j, j ≼ i ∧ X j c

theorem remembered_contains (X : I → C → Prop) (i : I) (c : C) (h : X i c) :
    remembered X i c := ⟨i, PO.refl i, h⟩

theorem remembered_grows (X : I → C → Prop) : Grows (remembered X) :=
  fun _ _ hij _ ⟨j, hj, hx⟩ => ⟨j, PO.trans hj hij, hx⟩

/-- **The remembered map is the least growing map containing `X`.** -/
theorem remembered_least (X V : I → C → Prop) (hXV : ∀ i c, X i c → V i c) (hV : Grows V)
    (i : I) (c : C) (h : remembered X i c) : V i c := by
  obtain ⟨j, hj, hx⟩ := h
  exact hV j i hj c (hXV j c hx)

variable {S : Type}

/-- Continuations depend only on the current state `g i`. -/
def StateDet (g : I → S) : Prop :=
  ∀ h h' k, g h = g h' → h ≼ k → ∃ k', h' ≼ k' ∧ g k' = g k

/-- Claims valid at some input below an input with the same state as `i`. -/
def stateRemembered (g : I → S) (X : I → C → Prop) : I → C → Prop :=
  fun i c => ∃ i0 i', i0 ≼ i' ∧ g i' = g i ∧ X i0 c

theorem stateRemembered_contains (g : I → S) (X : I → C → Prop) (i : I) (c : C)
    (h : X i c) : stateRemembered g X i c := ⟨i, i, PO.refl i, rfl, h⟩

theorem stateRemembered_state (g : I → S) (X : I → C → Prop) {i i' : I}
    (h : g i = g i') (c : C) : stateRemembered g X i c ↔ stateRemembered g X i' c := by
  constructor
  · rintro ⟨a, b, hab, hb, hx⟩; exact ⟨a, b, hab, hb.trans h, hx⟩
  · rintro ⟨a, b, hab, hb, hx⟩; exact ⟨a, b, hab, hb.trans h.symm, hx⟩

theorem stateRemembered_grows (g : I → S) (hdet : StateDet g) (X : I → C → Prop) :
    Grows (stateRemembered g X) := by
  rintro i j hij c ⟨i0, i', h0, hg, hx⟩
  obtain ⟨k', hk', hgk⟩ := hdet i i' j hg.symm hij
  exact ⟨i0, k', PO.trans h0 hk', hgk, hx⟩

/-- **The state-remembered map is the least growing map containing `X` that
depends only on the state.** -/
theorem stateRemembered_least (g : I → S) (X : I → C → Prop) (F : S → C → Prop)
    (hX : ∀ i c, X i c → F (g i) c) (hF : Grows (fun i => F (g i)))
    (i : I) (c : C) (h : stateRemembered g X i c) : F (g i) c := by
  obtain ⟨i0, i', h0, hg, hx⟩ := h
  have : F (g i') c := hF i0 i' h0 c (hX i0 c hx)
  rw [hg] at this; exact this

end Lookup

section Restructuring
open CC.Front
variable {K P : Type}

theorem lastSnap_append (g : Snap K P) (l t : List (Snap K P)) :
    lastSnap g (l ++ t) = lastSnap (lastSnap g l) t := by
  induction l generalizing g with
  | nil => rfl
  | cons x l ih => exact ih x

theorem chain_concat {st : Snap K P → Snap K P → Prop} :
    ∀ {g : Snap K P} (l t : List (Snap K P)), Front.Chain st g l →
      Front.Chain st (lastSnap g l) t → Front.Chain st g (l ++ t)
  | _, [], _, _, h2 => h2
  | _, _ :: l, t, h1, h2 => by
    cases h1 with
    | cons hs h1' => exact Front.Chain.cons hs (chain_concat l t h1' h2)

/-- The current snapshot of a restructuring history. -/
def curSnap (Rs : Restructuring K P) (h : Rs.Hist) : Snap K P := lastSnap Rs.init h.1

/-- **Continuations of a restructuring history depend only on its current
snapshot.** -/
theorem restr_stateDet (Rs : Restructuring K P) : StateDet (curSnap Rs) := by
  rintro h h' k hg ⟨t, ht⟩
  have hk : Front.Chain Rs.step Rs.init (h.1 ++ t) := by rw [ht]; exact k.2
  have htail := chain_append h.1 t hk
  have htail' : Front.Chain Rs.step (lastSnap Rs.init h'.1) t := by
    have : lastSnap Rs.init h.1 = lastSnap Rs.init h'.1 := hg
    rw [← this]; exact htail
  refine ⟨⟨h'.1 ++ t, chain_concat _ _ h'.2 htail'⟩, ⟨t, rfl⟩, ?_⟩
  show lastSnap Rs.init (h'.1 ++ t) = lastSnap Rs.init k.1
  rw [← ht, lastSnap_append, lastSnap_append]
  exact congrArg (fun g => lastSnap g t) hg.symm

/-- Forward-reachability claims as a validity map. -/
def fwdV (Rs : Restructuring K P) : Rs.Hist → K × P → Prop := fun h c => Rs.R h c.1 c.2

theorem fwdV_grows (Rs : Restructuring K P) : Grows (fwdV Rs) :=
  fun _ _ hle c hc => persistent_forwarding Rs hle c.1 c.2 hc

/-- **Forward reachability contains every state-remembered exact claim**:
every claim valid at the current snapshot of some history with the same
current snapshot, or at a snapshot before it, as long as exact claims are
valid claims. -/
theorem fwd_contains_stateRemembered (Rs : Restructuring K P)
    (X : Rs.Hist → K × P → Prop) (hX : ∀ h c, X h c → fwdV Rs h c)
    (h : Rs.Hist) (c : K × P) (hc : stateRemembered (curSnap Rs) X h c) : fwdV Rs h c :=
  stateRemembered_least (curSnap Rs) X (fun G c => claims G c.1 c.2) hX
    (fun i j hij c hc => persistent_forwarding Rs hij c.1 c.2 hc) h c hc

/-- **Forward reachability equals the least state-determined relaxation
exactly when every forwarding claim was exact earlier on some history with
the same current snapshot.** -/
theorem fwd_eq_iff (Rs : Restructuring K P)
    (X : Rs.Hist → K × P → Prop) (hX : ∀ h c, X h c → fwdV Rs h c) :
    (∀ h c, fwdV Rs h c ↔ stateRemembered (curSnap Rs) X h c) ↔
      (∀ h c, fwdV Rs h c → stateRemembered (curSnap Rs) X h c) :=
  ⟨fun H h c => (H h c).1,
   fun H h c => ⟨H h c, fwd_contains_stateRemembered Rs X hX h c⟩⟩

end Restructuring

/-! ## Snapshots -/

section Snapshots
open CC.Deploy
variable {Ev : Type} {n : Nat} (proc : Ev → Fin n) (scan : Ev → Prop)

/-- A Chandy–Lamport cut for scan `s` at `h`: a set of updates of `h`,
causally closed among updates, containing every update causally before `s`
and none causally after it. -/
def ClCut (h : Hist Ev) (s : Ev) (C : ESet Ev) : Prop :=
  (∀ u, C.mem u → h.s.1 u ∧ ¬ scan u) ∧
  (∀ u w, C.mem w → ¬ scan u → h.lt u w → C.mem u) ∧
  (∀ u, ¬ scan u → h.lt u s → C.mem u) ∧
  (∀ u, C.mem u → ¬ h.lt s u)

/-- `s` is a scan of `p` in `h`. -/
def ScanOf (h : Hist Ev) (p : Fin n) (s : Ev) : Prop := h.s.1 s ∧ scan s ∧ proc s = p

/-- A Chandy–Lamport view of `p` at `h`: a cut for each scan of `p`, and
nothing else. -/
def ClView (p : Fin n) (h : Hist Ev) (v : PMap Ev (ESet Ev)) : Prop :=
  (∀ s, v.f s ≠ none ↔ ScanOf proc scan h p s) ∧
  ∀ s C, v.f s = some C → ClCut scan h s C

/-- The updates causally before `s`. -/
def pastU (h : Hist Ev) (s : Ev) : ESet Ev := ⟨fun u => ¬ scan u ∧ h.lt u s⟩

theorem pastU_cut (h : Hist Ev) (s : Ev) : ClCut scan h s (pastU scan h s) := by
  refine ⟨fun u hu => ⟨(h.supp _ _ hu.2).1, hu.1⟩, fun u w hw hu huw => ⟨hu, h.trans _ _ _ huw hw.2⟩,
    fun u hu hus => ⟨hu, hus⟩, fun u hu hsu => h.irrefl _ (h.trans _ _ _ hu.2 hsu)⟩

open Classical in
/-- The view in which each scan of `p` takes its causal past. -/
noncomputable def pastView (h : Hist Ev) (p : Fin n) : PMap Ev (ESet Ev) :=
  ⟨fun s => if ScanOf proc scan h p s then some (pastU scan h s) else none⟩

theorem pastView_cl (h : Hist Ev) (p : Fin n) : ClView proc scan p h (pastView proc scan h p) := by
  classical
  refine ⟨fun s => ?_, fun s C hs => ?_⟩
  · by_cases hsp : ScanOf proc scan h p s <;> simp [pastView, hsp]
  · by_cases hsp : ScanOf proc scan h p s
    · simp only [pastView, hsp, if_true, Option.some.injEq] at hs
      subst hs; exact pastU_cut scan h s
    · simp [pastView, hsp] at hs

theorem clCut_grow {h h' : Hist Ev} (hle : h ≼ h') {s : Ev} (hs : h.s.1 s) {C : ESet Ev}
    (hC : ClCut scan h s C) : ClCut scan h' s C := by
  obtain ⟨h1, h2, h3, h4⟩ := hC
  refine ⟨fun u hu => ⟨hle.1 u (h1 u hu).1, (h1 u hu).2⟩, fun u w hw hu huw => ?_,
    fun u hu hus => ?_, fun u hu hsu => ?_⟩
  · have hw' := (h1 w hw).1
    have hu' := hle.2.1 u w hw' huw
    exact h2 u w hw hu ((hle.2.2 u w hu' hw').2 huw)
  · have hu' := hle.2.1 u s hs hus
    exact h3 u hu ((hle.2.2 u s hu' hs).2 hus)
  · exact h4 u hu ((hle.2.2 s u hs (h1 u hu).1).2 hsu)

open Classical in
/-- **Chandy–Lamport views continue.** -/
theorem cl_continue : Continue (W := fun _ : Fin n => PMap Ev (ESet Ev))
    (fun p h v => ClView proc scan p h v) := by
  intro p i j v hij hv
  let w : PMap Ev (ESet Ev) :=
    ⟨fun s => if v.f s ≠ none then v.f s else (pastView proc scan j p).f s⟩
  have hw : ∀ s, w.f s = if v.f s ≠ none then v.f s else (pastView proc scan j p).f s :=
    fun _ => rfl
  refine ⟨w, ⟨fun s => ?_, fun s C hs => ?_⟩, fun s C hs => ?_⟩
  · by_cases hvs : v.f s ≠ none
    · rw [hw, if_pos hvs]
      refine ⟨fun _ => ?_, fun _ => hvs⟩
      obtain ⟨h1, h2, h3⟩ := (hv.1 s).1 hvs
      exact ⟨hij.1 s h1, h2, h3⟩
    · rw [hw, if_neg hvs]
      exact ((pastView_cl proc scan j p).1 s)
  · by_cases hvs : v.f s ≠ none
    · rw [hw, if_pos hvs] at hs
      exact clCut_grow scan hij ((hv.1 s).1 hvs).1 (hv.2 s C hs)
    · rw [hw, if_neg hvs] at hs
      exact (pastView_cl proc scan j p).2 s C hs
  · have hvs : v.f s ≠ none := by rw [hs]; simp
    rw [hw, if_pos hvs, hs]

theorem cl_nonempty : ∀ (p : Fin n) (h : Hist Ev), ∃ v, ClView proc scan p h v :=
  fun p h => ⟨_, pastView_cl proc scan h p⟩

/-- **Views of one participant at one input form an antichain**: they are
defined on the same scans. -/
theorem cl_antichain : Antichain (W := fun _ : Fin n => PMap Ev (ESet Ev))
    (fun p h v => ClView proc scan p h v) := by
  intro p i v w hv hw hvw
  apply PO.antisymm hvw
  intro s C hs
  have hws : w.f s ≠ none := by rw [hs]; simp
  have hvs : v.f s ≠ none := (hv.1 s).2 ((hw.1 s).1 hws)
  cases hv' : v.f s with
  | none => exact absurd hv' hvs
  | some C' =>
    have := hvw s C' hv'
    rw [this] at hs; rw [← hs]

/-- The Chandy–Lamport product interface: one view per participant. -/
noncomputable def clSpec : Spec (Hist Ev) (PTd (fun _ : Fin n => PMap Ev (ESet Ev))) :=
  prodSpec (fun p h v => ClView proc scan p h v) (cl_nonempty proc scan)

/-- **The Chandy–Lamport snapshot is monotone across partitions under the owner
deployment** (Theorem `thm:product-frontier`(1)). -/
theorem cl_monoAcross : MonoAcrossPartitions (ownerD (clSpec proc scan)) :=
  product_monoAcross _ (cl_nonempty proc scan) (cl_continue proc scan)

/-- A strict total order of the events of `h` that extends causality. -/
def LinExt (h : Hist Ev) (L : Ev → Ev → Prop) : Prop :=
  (∀ a, ¬ L a a) ∧ (∀ a b c, L a b → L b c → L a c) ∧
  (∀ a b, h.s.1 a → h.s.1 b → a ≠ b → L a b ∨ L b a) ∧ (∀ a b, h.lt a b → L a b)

/-- The updates before `s` in `L`. -/
def beforeU (h : Hist Ev) (L : Ev → Ev → Prop) (s : Ev) : ESet Ev :=
  ⟨fun u => h.s.1 u ∧ ¬ scan u ∧ L u s⟩

open Classical in
/-- The view of `p` that the order `L` explains. -/
noncomputable def atomicView (h : Hist Ev) (L : Ev → Ev → Prop) (p : Fin n) : PMap Ev (ESet Ev) :=
  ⟨fun s => if ScanOf proc scan h p s then some (beforeU scan h L s) else none⟩

/-- **Views explained by one order are Chandy–Lamport views.** -/
theorem atomicView_cl (h : Hist Ev) (L : Ev → Ev → Prop) (hL : LinExt h L) (p : Fin n) :
    ClView proc scan p h (atomicView proc scan h L p) := by
  classical
  obtain ⟨hirr, htr, _, hext⟩ := hL
  refine ⟨fun s => ?_, fun s C hs => ?_⟩
  · by_cases hsp : ScanOf proc scan h p s <;> simp [atomicView, hsp]
  · by_cases hsp : ScanOf proc scan h p s
    · simp only [atomicView, hsp, if_true, Option.some.injEq] at hs
      subst hs
      refine ⟨fun u hu => ⟨hu.1, hu.2.1⟩, fun u w hw hu huw => ⟨(h.supp _ _ huw).1, hu,
        htr _ _ _ (hext _ _ huw) hw.2.2⟩, fun u hu hus => ⟨(h.supp _ _ hus).1, hu, hext _ _ hus⟩,
        fun u hu hsu => hirr _ (htr _ _ _ hu.2.2 (hext _ _ hsu))⟩
    · simp [atomicView, hsp] at hs

/-- Linear extensions exist (from a causally sorted listing). -/
theorem linExt_exists (h : Hist Ev) : ∃ L, LinExt h L := by
  classical
  obtain ⟨l, hl, hm⟩ := h.s.2
  obtain ⟨τ, hτn, hτm, hτs⟩ := exists_sorted h l hl
  let L : Ev → Ev → Prop := fun a b => a ∈ τ ∧ b ∈ τ ∧ τ.idxOf a < τ.idxOf b
  have hget : ∀ a (ha : a ∈ τ), τ[τ.idxOf a]'(List.idxOf_lt_length_of_mem ha) = a :=
    fun a ha => List.getElem_idxOf _
  have hinj : ∀ a b, a ∈ τ → b ∈ τ → τ.idxOf a = τ.idxOf b → a = b := by
    intro a b ha hb he
    have e1 := hget a ha
    have e2 := hget b hb
    have : τ[τ.idxOf a]'(List.idxOf_lt_length_of_mem ha) =
        τ[τ.idxOf b]'(List.idxOf_lt_length_of_mem hb) := by simp only [he]
    rw [e1, e2] at this; exact this
  have hmemτ : ∀ x, h.s.1 x ↔ x ∈ τ := fun x => (hm x).trans (hτm x).symm
  refine ⟨L, fun a h => Nat.lt_irrefl _ h.2.2, fun a b c h1 h2 => ⟨h1.1, h2.2.1,
    Nat.lt_trans h1.2.2 h2.2.2⟩, fun a b ha hb hne => ?_, fun a b hab => ?_⟩
  · have ha' := (hmemτ a).1 ha
    have hb' := (hmemτ b).1 hb
    rcases Nat.lt_trichotomy (τ.idxOf a) (τ.idxOf b) with hlt | heq | hgt
    · exact Or.inl ⟨ha', hb', hlt⟩
    · exact absurd (hinj a b ha' hb' heq) hne
    · exact Or.inr ⟨hb', ha', hgt⟩
  · have hs := h.supp a b hab
    have ha' := (hmemτ a).1 hs.1
    have hb' := (hmemτ b).1 hs.2
    refine ⟨ha', hb', ?_⟩
    rcases Nat.lt_trichotomy (τ.idxOf a) (τ.idxOf b) with hlt | heq | hgt
    · exact hlt
    · exact absurd (hinj a b ha' hb' heq ▸ hab) (h.irrefl b)
    · have hp := (List.pairwise_iff_getElem.1 hτs) (τ.idxOf b) (τ.idxOf a)
        (List.idxOf_lt_length_of_mem hb') (List.idxOf_lt_length_of_mem ha') hgt
      rw [hget b hb', hget a ha'] at hp
      exact absurd hab hp

/-- The atomic snapshot as a normalized strengthening of the Chandy–Lamport
product interface: it selects the tuples of views that one strict total order
of all operations, extending causality, explains. -/
noncomputable def atomicStr : NormStr (W := fun _ : Fin n => PMap Ev (ESet Ev))
    (fun p h v => ClView proc scan p h v) where
  sel h y := ∃ L, LinExt h L ∧ ∀ p, y p = atomicView proc scan h L p
  sub h y := by
    rintro ⟨L, hL, hy⟩ p
    rw [hy p]; exact atomicView_cl proc scan h L hL p

/-- The atomic snapshot specification: restrictions of selected tuples. -/
noncomputable def atSpec : Spec (Hist Ev) (PTd (fun _ : Fin n => PMap Ev (ESet Ev))) where
  P := (atomicStr proc scan).table
  total h := by
    obtain ⟨L, hL⟩ := linExt_exists h
    exact ⟨⟨fun _ => none⟩, fun p => atomicView proc scan h L p, ⟨L, hL, fun _ => rfl⟩,
      fun _ => Or.inl rfl⟩

/-- Local form of Theorem `thm:product-frontier`(2): a tuple of views whose
single-coordinate restrictions are each rows at `i`, while no row at `i`
extends them all, shows that the spec is not monotone across partitions
under the owner deployment. -/
theorem local_not_monoAcross {I : Type} [PO I] {W : Fin n → Type} [∀ p, PO (W p)]
    (hn : 2 ≤ n) (sp : Spec I (PTd W)) (i : I) (y : (p : Fin n) → W p)
    (hrow : ∀ p, sp.P i (restrictTo y p))
    (hno : ¬ ∃ u, sp.P i u ∧ ∀ p, restrictTo y p ≼ u) :
    ¬ MonoAcrossPartitions (ownerD sp) := by
  intro hM
  have hauth : ∀ p, (ownerD sp).A p i (restrictTo y p) :=
    fun p => ⟨hrow p, fun q hq => by simp [restrictTo, hq]⟩
  let p0 : Fin n := ⟨0, by omega⟩
  let p1 : Fin n := ⟨1, by omega⟩
  let F : Family sp n := fun p => some (oneShot sp i (restrictTo y p) (hrow p))
  have hem : ∀ p r, Emits F p r ↔ r = (i, restrictTo y p) := by
    intro p r
    rw [emits_some (rfl : F p = _)]; simp
  have hAuth : Authorized (ownerD sp) F := by
    intro p r hr
    rw [hem] at hr; subst hr
    exact hauth p
  have hSep : Separable F (fun p => p.val) :=
    Or.inl ⟨p0, p1, _, _, (hem _ _).2 rfl, (hem _ _).2 rfl, by simp [p0, p1]⟩
  have hub : UB F i := by
    intro p m hm
    cases hm
    exact PO.refl i
  obtain ⟨u, hu, hall⟩ := hM _ ⟨p0, p1, by simp [p0, p1]⟩ F hAuth hSep i hub
  exact hno ⟨u, hu, fun p => hall p _ ((hem _ _).2 rfl)⟩


end Snapshots

/-! ### The two-process witness -/

section Witness
open CC.Deploy CC.Txn Classical

variable {Ev : Type} {proc : Ev → Fin 2} {scan : Ev → Prop}

/-- Two updates and two scans: update `up` and scan `sp` at participant `0`,
update `uq` and scan `sq` at participant `1`, all distinct. -/
structure Four (proc : Ev → Fin 2) (scan : Ev → Prop) where
  up : Ev
  sp : Ev
  uq : Ev
  sq : Ev
  d1 : up ≠ sp
  d2 : up ≠ uq
  d3 : up ≠ sq
  d4 : sp ≠ uq
  d5 : sp ≠ sq
  d6 : uq ≠ sq
  pup : proc up = 0
  psp : proc sp = 0
  puq : proc uq = 1
  psq : proc sq = 1
  nup : ¬ scan up
  ssp : scan sp
  nuq : ¬ scan uq
  ssq : scan sq

variable (w : Four proc scan)

/-- The history: `up → sp` and `uq → sq`, the two participants concurrent. -/
def Four.hist : Hist Ev where
  s := FinSet.ofList [w.up, w.sp, w.uq, w.sq] (by
    simp [w.d1, w.d2, w.d3, w.d4, w.d5, w.d6])
  lt a b := (a = w.up ∧ b = w.sp) ∨ (a = w.uq ∧ b = w.sq)
  irrefl a h := by
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact w.d1 h
    · exact w.d6 h
  trans a b c h1 h2 := by
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨h, _⟩ | ⟨h, _⟩
    · exact absurd h.symm w.d1
    · exact absurd h w.d4
    · exact absurd h.symm w.d3
    · exact absurd h.symm w.d6
  supp a b h := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [FinSet.ofList]

/-- Ranks of the orders `up sp uq sq` and `uq sq up sp`. -/
noncomputable def Four.rk0 (x : Ev) : Nat :=
  if x = w.up then 0 else if x = w.sp then 1 else if x = w.uq then 2 else 3
noncomputable def Four.rk1 (x : Ev) : Nat :=
  if x = w.uq then 0 else if x = w.sq then 1 else if x = w.up then 2 else 3

theorem Four.mem (x : Ev) (hx : w.hist.s.1 x) : x = w.up ∨ x = w.sp ∨ x = w.uq ∨ x = w.sq := by
  simpa [Four.hist, FinSet.ofList] using hx

theorem Four.rk0_vals : w.rk0 w.up = 0 ∧ w.rk0 w.sp = 1 ∧ w.rk0 w.uq = 2 ∧ w.rk0 w.sq = 3 := by
  simp [Four.rk0, w.d1, w.d2, w.d3, w.d4, w.d5, w.d6, Ne.symm w.d1, Ne.symm w.d2, Ne.symm w.d3,
    Ne.symm w.d4, Ne.symm w.d5, Ne.symm w.d6]

theorem Four.rk1_vals : w.rk1 w.uq = 0 ∧ w.rk1 w.sq = 1 ∧ w.rk1 w.up = 2 ∧ w.rk1 w.sp = 3 := by
  simp [Four.rk1, w.d1, w.d2, w.d3, w.d4, w.d5, w.d6, Ne.symm w.d1, Ne.symm w.d2, Ne.symm w.d3,
    Ne.symm w.d4, Ne.symm w.d5, Ne.symm w.d6]

theorem Four.rk_linExt (rk : Ev → Nat)
    (hinj : ∀ a b, w.hist.s.1 a → w.hist.s.1 b → rk a = rk b → a = b)
    (hup : rk w.up < rk w.sp) (huq : rk w.uq < rk w.sq) :
    LinExt w.hist (fun a b => rk a < rk b) := by
  refine ⟨fun a => Nat.lt_irrefl _, fun a b c => Nat.lt_trans, fun a b ha hb hne => ?_,
    fun a b hab => ?_⟩
  · rcases Nat.lt_trichotomy (rk a) (rk b) with h | h | h
    · exact Or.inl h
    · exact absurd (hinj a b ha hb h) hne
    · exact Or.inr h
  · rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hup
    · exact huq

theorem Four.inj_of_vals (rk : Ev → Nat) (a b c d : Nat)
    (h : rk w.up = a ∧ rk w.sp = b ∧ rk w.uq = c ∧ rk w.sq = d)
    (hd : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) :
    ∀ x y, w.hist.s.1 x → w.hist.s.1 y → rk x = rk y → x = y := by
  intro x y hx hy he
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hd
  rcases w.mem x hx with rfl | rfl | rfl | rfl <;> rcases w.mem y hy with rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | (exfalso; simp only [h1, h2, h3, h4] at he; omega)

theorem Four.rk0_linExt : LinExt w.hist (fun a b => w.rk0 a < w.rk0 b) := by
  have hv := w.rk0_vals
  refine w.rk_linExt _ (w.inj_of_vals _ 0 1 2 3 hv (by omega)) ?_ ?_
  · rw [hv.1, hv.2.1]; omega
  · rw [hv.2.2.1, hv.2.2.2]; omega

theorem Four.rk1_linExt : LinExt w.hist (fun a b => w.rk1 a < w.rk1 b) := by
  have hv := w.rk1_vals
  refine w.rk_linExt _ (w.inj_of_vals _ 2 3 0 1 ⟨hv.2.2.1, hv.2.2.2, hv.1, hv.2.1⟩ (by omega)) ?_ ?_
  · rw [hv.2.2.1, hv.2.2.2]; omega
  · rw [hv.1, hv.2.1]; omega

/-- The witness tuple: participant `0` answers its scan with `{up}` (the view
of order `up sp uq sq`), participant `1` answers with `{uq}` (order
`uq sq up sp`). -/
noncomputable def Four.y : (p : Fin 2) → PMap Ev (ESet Ev) := fun p =>
  if p = 0 then atomicView proc scan w.hist (fun a b => w.rk0 a < w.rk0 b) p
  else atomicView proc scan w.hist (fun a b => w.rk1 a < w.rk1 b) p

theorem Four.memh (x : Ev) (hx : x = w.up ∨ x = w.sp ∨ x = w.uq ∨ x = w.sq) : w.hist.s.1 x := by
  rcases hx with rfl | rfl | rfl | rfl <;> simp [Four.hist, FinSet.ofList]

theorem atomicView_at' {h : Hist Ev} {L : Ev → Ev → Prop} {p : Fin 2} {s : Ev}
    (hs : ScanOf proc scan h p s) :
    (atomicView proc scan h L p).f s = some (beforeU scan h L s) := by
  simp only [atomicView]; rw [if_pos hs]

theorem Four.row (p : Fin 2) : (atSpec proc scan).P w.hist (restrictTo w.y p) := by
  have key : ∀ (L : Ev → Ev → Prop), LinExt w.hist L →
      w.y p = atomicView proc scan w.hist L p →
      (atSpec proc scan).P w.hist (restrictTo w.y p) := by
    intro L hL he
    refine ⟨fun q => atomicView proc scan w.hist L q, ⟨L, hL, fun _ => rfl⟩, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq; right; simp [restrictTo, he]
    · left; simp [restrictTo, hq]
  by_cases hp : p = 0
  · exact key _ w.rk0_linExt (by simp [Four.y, hp])
  · exact key _ w.rk1_linExt (by simp [Four.y, hp])

theorem Four.no_common :
    ¬ ∃ u, (atSpec proc scan).P w.hist u ∧ ∀ p, restrictTo w.y p ≼ u := by
  rintro ⟨u, ⟨z, ⟨L, hL, hz⟩, hzu⟩, hall⟩
  have hle : ∀ p, w.y p ≼ z p := by
    intro p
    have h1 : OLe ((restrictTo w.y p).t p) (u.t p) := hall p p
    have e : (restrictTo w.y p).t p = some (w.y p) := by simp [restrictTo]
    rw [e] at h1
    rcases hzu p with h0 | h0 <;> rw [h0] at h1
    · exact False.elim h1
    · exact h1
  have hsp : ScanOf proc scan w.hist 0 w.sp := ⟨w.memh _ (by simp), w.ssp, w.psp⟩
  have hsq : ScanOf proc scan w.hist 1 w.sq := ⟨w.memh _ (by simp), w.ssq, w.psq⟩
  have e0 : beforeU scan w.hist (fun a b => w.rk0 a < w.rk0 b) w.sp =
      beforeU scan w.hist L w.sp := by
    have h1 := hle 0 _ _ (show (w.y 0).f w.sp = _ by
      simp only [Four.y, if_pos rfl]; exact atomicView_at' hsp)
    rw [hz 0, atomicView_at' hsp] at h1
    exact (Option.some.inj h1).symm
  have e1 : beforeU scan w.hist (fun a b => w.rk1 a < w.rk1 b) w.sq =
      beforeU scan w.hist L w.sq := by
    have h1 := hle 1 _ _ (show (w.y 1).f w.sq = _ by
      simp only [Four.y, if_neg (by decide : (1 : Fin 2) ≠ 0)]; exact atomicView_at' hsq)
    rw [hz 1, atomicView_at' hsq] at h1
    exact (Option.some.inj h1).symm
  have m : ∀ {A B : ESet Ev}, A = B → ∀ x, A.mem x → B.mem x := fun h x hx => h ▸ hx
  have v0 := w.rk0_vals
  have v1 := w.rk1_vals
  have hup : L w.up w.sp :=
    (m e0 w.up ⟨w.memh _ (by simp), w.nup, show w.rk0 w.up < w.rk0 w.sp by rw [v0.1, v0.2.1]; omega⟩).2.2
  have hnuq : ¬ L w.uq w.sp := fun h => by
    have := (m e0.symm w.uq ⟨w.memh _ (by simp), w.nuq, h⟩).2.2
    simp only [v0.2.2.1, v0.2.1] at this; omega
  have huq : L w.uq w.sq :=
    (m e1 w.uq ⟨w.memh _ (by simp), w.nuq, show w.rk1 w.uq < w.rk1 w.sq by rw [v1.1, v1.2.1]; omega⟩).2.2
  have hnup : ¬ L w.up w.sq := fun h => by
    have := (m e1.symm w.up ⟨w.memh _ (by simp), w.nup, h⟩).2.2
    simp only [v1.2.2.1, v1.2.1] at this; omega
  obtain ⟨hirr, htr, htot, _⟩ := hL
  have h2 : L w.sp w.uq :=
    (htot _ _ (w.memh _ (by simp)) (w.memh _ (by simp)) w.d4).resolve_right hnuq
  have h3 : L w.sq w.up :=
    (htot _ _ (w.memh _ (by simp)) (w.memh _ (by simp)) (Ne.symm w.d3)).resolve_right hnup
  exact hirr _ (htr _ _ _ hup (htr _ _ _ h2 (htr _ _ _ huq h3)))

/-- **The atomic snapshot is not monotone across partitions under the owner
deployment**: with two participants, each performing an update and then a
scan, and no messages between them, the answers `{up}` to `sp` and `{uq}` to
`sq` are each permitted, but no single order explains both.  This holds for
every event universe that contains such four events. -/
theorem atomic_not_monoAcross (w : Four proc scan) :
    ¬ MonoAcrossPartitions (ownerD (atSpec proc scan)) :=
  local_not_monoAcross (Nat.le_refl 2) _ w.hist w.y w.row w.no_common

/-- The global-snapshot spec permits the two answers together. -/
theorem Four.cl_row : (clSpec proc scan).P w.hist ⟨fun p => some (w.y p)⟩ := by
  refine ⟨w.y, fun p => ?_, fun p => Or.inr rfl⟩
  by_cases hp : p = 0
  · simp only [Four.y, hp, if_true]; exact atomicView_cl _ _ w.hist _ w.rk0_linExt 0
  · simp only [Four.y, hp, if_false]; exact atomicView_cl _ _ w.hist _ w.rk1_linExt p

/-- **Consequence for the global snapshot** (Proposition
`prop:deployment-complete-cap`): with at least two participants, the owner
deployment's canonical system has Deployment Availability and Partition
Consistency. -/
theorem cl_cap {Ev : Type} {n : Nat} (proc : Ev → Fin n) (scan : Ev → Prop) (hn : 2 ≤ n)
    (D : Type) :
    ∃ Sys : CAP.System (clSpec proc scan) D,
      DeploymentAvailability Sys (ownerD (clSpec proc scan)) ∧ PartitionConsistencyAt Sys n :=
  deployment_complete_cap_exists hn _ (cl_monoAcross proc scan)

/-- **Consequence for the atomic snapshot**: no system has Deployment
Availability and Partition Consistency under the owner deployment. -/
theorem atomic_no_cap (w : Four proc scan) (D : Type) :
    ¬ ∃ Sys : CAP.System (atSpec proc scan) D,
      DeploymentAvailability Sys (ownerD (atSpec proc scan)) ∧ PartitionConsistencyAt Sys 2 :=
  fun h => atomic_not_monoAcross w ((deployment_complete_cap_iff (Nat.le_refl 2) _).1 h)

end Witness

/-! ## Leader election -/

section Leader
open CC.Txn

/-- Leader outputs: `none` (no leader yet) below every leader, and leaders
incomparable. -/
structure Flat (α : Type) where
  v : Option α

instance instPOFlat (α : Type) : PO (Flat α) where
  le x y := x.v = none ∨ x = y
  refl _ := Or.inr rfl
  trans {x y z} h1 h2 := by
    rcases h1 with h1 | rfl
    · exact Or.inl h1
    · exact h2

instance (α : Type) : PO.Antisymm (Flat α) where
  antisymm {x y} h1 h2 := by
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · cases x; cases y; simp only at h1 h2; subst h1; subst h2; rfl
      · exact h2.symm
    · exact h1

/-- With the list `All` of all participants in every input: an input records,
for some participants, whether each is a candidate; once every participant
of `All` has reported, the leader is the largest candidate. -/
def maxLeader (All : List Nat) (x : PMap Nat Bool) : Flat Nat :=
  if All.all (fun p => (x.f p).isSome) then
    ⟨(All.filter (fun p => x.f p == some true)).max?⟩
  else ⟨none⟩

/-- The election spec with the participant list in the input. -/
def leaderAllSpec (All : List Nat) : Spec (PMap Nat Bool) (Flat Nat) where
  P x o := o = maxLeader All x
  total x := ⟨_, rfl⟩

theorem leaderAllSpec_functional (All : List Nat) : (leaderAllSpec All).Functional :=
  fun _ _ _ h h' => h.trans h'.symm

/-- **With the participant list in the input, max-candidate election is
monotone**: once every participant has reported, more input changes no
report, and before that the output is `none`. -/
theorem leaderAll_mono (All : List Nat) : (leaderAllSpec All).MonotoneF := by
  intro x x' o o' hle ho ho'
  subst ho; subst ho'
  unfold maxLeader
  by_cases hc : All.all (fun p => (x.f p).isSome) = true
  · have hagree : ∀ p ∈ All, x'.f p = x.f p := by
      intro p hp
      have := (List.all_eq_true.1 hc) p hp
      cases hx : x.f p with
      | none => rw [hx] at this; simp at this
      | some b => exact hle p b hx
    have hc' : All.all (fun p => (x'.f p).isSome) = true := by
      apply List.all_eq_true.2
      intro p hp; rw [hagree p hp]; exact (List.all_eq_true.1 hc) p hp
    rw [if_pos hc, if_pos hc']
    right
    congr 2
    exact List.filter_congr (fun p hp => by rw [hagree p hp])
  · rw [if_neg hc]; exact Or.inl rfl

/-- Hence (Functional CALM) its runs are consistent, and it satisfies Lifted
Monotonicity. -/
theorem leaderAll_consistent (All : List Nat) :
    (leaderAllSpec All).Consistent ∧ (leaderAllSpec All).LiftedMono :=
  ⟨consistent_of_mono (leaderAll_mono All),
   (CALM.liftedMono_iff_monoF (leaderAllSpec_functional All)).2 (leaderAll_mono All)⟩

/-- Without the participant list: an input is the set of candidates heard so
far, and an output is no leader yet or one candidate heard. -/
def leaderSpec : Spec (FinSet Nat) (Flat Nat) where
  P S o := o.v = none ∨ ∃ l, o.v = some l ∧ S.1 l
  total _ := ⟨⟨none⟩, Or.inl rfl⟩

/-- **Without the participant list, election is not monotone**: two
candidates, each elected where it alone has been heard, have no common
output extension where both have.  So no system has Availability for `P`
and Partition Consistency. -/
theorem leader_not_monotone (D : Type) :
    ¬ leaderSpec.LiftedMono ∧
      ¬ ∃ Sys : CAP.System leaderSpec D, CAP.Availability Sys ∧ CAP.PartitionConsistency Sys := by
  have h : ¬ leaderSpec.LiftedMono := by
    intro hL
    have hce := (liftedMono_iff_commonExpansion _).1 hL
    let S1 : FinSet Nat := FinSet.ofList [1] (by decide)
    let S2 : FinSet Nat := FinSet.ofList [2] (by decide)
    let S12 : FinSet Nat := FinSet.ofList [1, 2] (by decide)
    obtain ⟨u, _, hall⟩ := hce [(S1, ⟨some 1⟩), (S2, ⟨some 2⟩)] (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inr ⟨1, rfl, by simp [S1, FinSet.ofList]⟩
      · exact Or.inr ⟨2, rfl, by simp [S2, FinSet.ofList]⟩) S12 (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        · intro x hx; simp [S1, S2, S12, FinSet.ofList] at hx ⊢; omega)
    have h1 := hall _ (List.mem_cons_self ..)
    have h2 := hall _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rcases h1 with h1 | h1
    · simp at h1
    rcases h2 with h2 | h2
    · simp at h2
    have := h1.trans h2.symm
    simp at this
  exact ⟨h, no_cap_of_not_liftedMono h D⟩

end Leader

/-! ## Memory as one participant -/

section Memory
open CC.Joint CC.Guard

/-- The functional spec of a map. -/
def funSpec {I O : Type} [PO I] [PO O] (d : I → O) : Spec I O where
  P i o := o = d i
  total i := ⟨_, rfl⟩

/-- **A decision stage that is a monotone function of the upstream's outputs
needs no commitment**: whatever stage guards it (for example a memory whose
outputs are logs of responses), the pipeline is proper. -/
theorem monotone_stage_proper {I M O : Type} [PO I] [PO M] [PO O] (sp : Spec I M) (d : M → O)
    (hd : ∀ m m', m ≼ m' → d m ≼ d m') : Proper sp (funSpec d) := by
  apply proper_iff.2
  apply ceOn_of_ce
  apply (CALM.commonExpansion_iff_monoF (sp := funSpec d) (fun _ _ _ h h' => h.trans h'.symm)).2
  intro m m' o o' hle ho ho'
  subst ho; subst ho'; exact hd m m' hle

end Memory

end Apps
end CC
