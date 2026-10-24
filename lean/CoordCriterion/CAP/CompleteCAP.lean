import CoordCriterion.CAP.Model

/-!
# Complete CAP (Section 4.5, Theorem `thm:complete-cap`)

On top of the system model of `CAP/Model.lean`:

* the commitment-free system (`cfSystem`, defined in `CAP/Model.lean`) and its Availability and Partition
  Consistency under Lifted Monotonicity (`cf_availability`,
  `cf_partitionConsistency`);
* necessity: Availability ∧ Partition Consistency ⇒ Lifted Monotonicity
  (`cap_necessary`);
* Theorem `thm:complete-cap` in both directions, including the "moreover"
  clause (`complete_cap`, `complete_cap_cf`);
* a counterexample showing that the (⇐) direction needs nondeterministic
  strategies (`deterministic_not_available`; see modeling choice 5 of
  `CAP/Model.lean`).

The strengthened (2)⇒(1) direction with commitment-free, receive-free
confluence continuations is `complete_cap_strong` in
`CAP/ResponseAvailability.lean`.
-/

namespace CC
namespace CAP

variable {I O : Type} [PO I] [PO O]
variable {sp : Spec I O} {D : Type} {n : Nat}

/-! ## The commitment-free system -/

theorem cf_allowed {N : Nat} {init : Fin N → I} {p : Fin N} {pre : List (LEv sp D N)}
    {e : LEv sp D N} (he : ∀ γ o, e = .out γ o → γ = []) :
    Allowed (cfSystem sp D) N init p pre e := by
  cases e with
  | inp => trivial
  | out γ o =>
    have := he γ o rfl; subst this
    exact ⟨by simp, trivial⟩
  | send => trivial
  | recv => trivial

theorem compliant_cf_out {N : Nat} {init : Fin N → I} {p : Fin N} {l : List (LEv sp D N)}
    (h : Compliant (Allowed (cfSystem sp D) N init p) l) :
    ∀ γ o, LEv.out γ o ∈ l → γ = [] := by
  intro γ o hm
  obtain ⟨a, b, hab⟩ := List.append_of_mem hm
  have := (h a _ b hab).1
  cases γ with
  | nil => rfl
  | cons c _ => exact absurd (this c (List.mem_cons_self ..)) id

/-- Every history the commitment-free system produces is coordination-free
(Def. `def:coordination`): each output event is some `Out ε o`. -/
theorem cfSystem_coordinationFree {N : Nat} {init : Fin N → I} {H : History sp D N}
    (h : Produced (cfSystem sp D) N init H) : ∀ p γ o, LEv.out γ o ∈ H p → γ = [] :=
  fun p => compliant_cf_out (h p)

theorem cf_availability (hlm : sp.LiftedMono) : Availability (cfSystem sp D) := by
  have hce := (liftedMono_iff_commonExpansion _).1 hlm
  intro N init H comp hwf hprod hpart c hcut p σ hσ o ho
  classical
  obtain ⟨es, hx⟩ := lrun_cf hσ (compliant_cf_out (compliant_take (hprod p) (c p)))
  have hres : Residual σ (outs es) := run_residual hx
  have hexp : Exposable σ o := ce_exposable hce hres ho
  let τ : State sp :=
    { cur := σ.cur
      R := outputTable σ o
      sub := fun k u h => σ.sub k u h.1
      hasCur := ⟨o, ho, PO.refl o⟩
      above := fun k u h => σ.above k u h.1 }
  have hstep : Step σ (.output o) τ := Step.output σ τ o ho rfl rfl
  let ext : Fin N → List (LEv sp D N) := fun q => if q = p then [.out [] o] else []
  have hnr : ∀ p' q k j d, LEv.recv q k j d ∉ ext p' := by
    intro p' q k j d; simp only [ext]; split <;> simp
  have hext : Extends H c (fun q => (H q).take (c q) ++ ext q) ext := fun _ => rfl
  refine ⟨_, ext, hext, ⟨?_, recvMatched_extend hwf.2 hcut hext hnr⟩, ?_,
    partitioned_extend hpart hext hnr, ?_, ?_, ⟨[], by simp [ext]⟩⟩
  · intro q
    obtain ⟨τq, hq⟩ := hwf.1 q
    by_cases hqp : q = p
    · subst hqp
      refine ⟨τ, lrun_append.2 ⟨σ, hσ, ?_⟩⟩
      have hq : ext q = [.out [] o] := by simp [ext]
      rw [hq]
      exact .out rfl hstep hexp (.nil τ)
    · obtain ⟨σq, hσq⟩ := lrun_take hq (c q)
      refine ⟨σq, ?_⟩
      have hq' : ext q = [] := by simp [ext, hqp]
      show LRun _ ((H q).take (c q) ++ ext q) σq
      rw [hq', List.append_nil]; exact hσq
  · intro q
    apply compliant_append (compliant_take (hprod q) (c q))
    intro a e b he
    apply cf_allowed
    intro γ o' hγ
    subst hγ
    have hm : LEv.out γ o' ∈ ext q := by rw [he]; simp
    simp only [ext] at hm; split at hm <;> simp at hm
    exact hm.1
  · intro q hq
    have : q ≠ p := fun h => hq (h ▸ rfl)
    simp [ext, this]
  · intro q j; simp only [ext]; split <;> simp

theorem cf_partitionConsistency (hlm : sp.LiftedMono) :
    PartitionConsistency (cfSystem sp D) := by
  have hce := (liftedMono_iff_commonExpansion _).1 hlm
  intro N init H comp hwf hprod _ c hcut j hj
  classical
  have hX : ∀ p, ∃ x : State sp × List (I × O),
      LRun (canon sp (init p)) ((H p).take (c p)) x.1 ∧ Residual x.1 (x.2.map Prod.snd) ∧
      ∀ r ∈ x.2, sp.S r.1 r.2 ∧ r.1 ≼ x.1.cur := by
    intro p
    obtain ⟨τp, hp⟩ := hwf.1 p
    obtain ⟨σ, hσ⟩ := lrun_take hp (c p)
    obtain ⟨es, hx⟩ := lrun_cf hσ (compliant_cf_out (compliant_take (hprod p) (c p)))
    obtain ⟨rows, hm, hr⟩ := exec_rows hx
    refine ⟨(σ, rows), hσ, ?_, hr⟩
    show Residual σ (rows.map Prod.snd)
    rw [hm]; exact run_residual hx
  let X := fun p => Classical.choose (hX p)
  have hXs : ∀ p, _ := fun p => Classical.choose_spec (hX p)
  let all := (List.finRange N).flatMap (fun p => (X p).2)
  obtain ⟨u, hju, hu⟩ := hce all
    (by intro r hr; simp only [all, List.mem_flatMap] at hr
        obtain ⟨p, _, hr⟩ := hr; exact ((hXs p).2.2 r hr).1) j
    (by intro r hr; simp only [all, List.mem_flatMap] at hr
        obtain ⟨p, _, hr⟩ := hr
        exact PO.trans ((hXs p).2.2 r hr).2 (hj p _ (hXs p).1))
  have hin : ∀ p, (X p).1.R j u := by
    intro p
    refine ((hXs p).2.1 j u).2 ⟨hju, hj p _ (hXs p).1, ?_⟩
    intro o ho
    simp only [List.mem_map] at ho
    obtain ⟨r, hr, rfl⟩ := ho
    exact hu r (by simp only [all, List.mem_flatMap]; exact ⟨p, List.mem_finRange p, hr⟩)
  have hE : ∀ p, ∃ es, Exec (X p).1 es (meetState sp j u hju) :=
    fun p => reach_meet (hXs p).2.1 (hin p)
  let ext : Fin N → List (LEv sp D N) := fun p => toL (Classical.choose (hE p))
  have hnr : ∀ p q k j d, LEv.recv q k j d ∉ ext p := fun p => toL_norecv _
  have hext : Extends H c (fun q => (H q).take (c q) ++ ext q) ext := fun _ => rfl
  have hrun : ∀ p, LRun (canon sp (init p)) ((H p).take (c p) ++ ext p) (meetState sp j u hju) :=
    fun p => lrun_append.2 ⟨(X p).1, (hXs p).1,
      exec_to_lrun hce (Classical.choose_spec (hE p)) (hXs p).2.1⟩
  exact ⟨_, ext, meetState sp j u hju, hext,
    ⟨fun p => ⟨_, hrun p⟩, recvMatched_extend hwf.2 hcut hext hnr⟩, rfl, hrun⟩


/-! ## Necessity: Availability ∧ Partition Consistency ⇒ Lifted Monotonicity -/

/-- (1)⇒(2) of Theorem `thm:complete-cap`, for an arbitrary system (any
basis, any local nondeterministic strategies). -/
theorem cap_necessary (Sys : System sp D) (hA : Availability Sys)
    (hP : PartitionConsistency Sys) : sp.LiftedMono := by
  apply (liftedMono_iff_commonExpansion _).2
  intro rows hrows j hj
  classical
  by_cases hne : rows = []
  · subst hne; obtain ⟨u, hu⟩ := sp.total j; exact ⟨u, hu, by simp⟩
  have hlen : 0 < rows.length := by
    cases rows with
    | nil => exact absurd rfl hne
    | cons => simp
  -- one participant per row, plus one participant at `j`
  let N := rows.length + 1
  let init : Fin N → I := fun p => if h : p.val < rows.length then (rows[p.val]'h).1 else j
  let comp : Fin N → Nat := fun p => p.val
  have hcomp2 : ∃ p q : Fin N, comp p ≠ comp q :=
    ⟨⟨0, by omega⟩, ⟨rows.length, by omega⟩, by simp [comp]; omega⟩
  let H0 : History sp D N := fun _ => []
  have hwf0 : WF init H0 :=
    ⟨fun p => ⟨_, .nil _⟩, by intro p a q k j d b h; simp [H0] at h⟩
  have hprod0 : Produced Sys N init H0 := fun p a e b h => by simp [H0] at h
  have hpart0 : Partitioned H0 comp := ⟨hcomp2, by intro p a q k j d b h; simp [H0] at h⟩
  have hcut0 : IsCut H0 (fun _ => 0) :=
    ⟨fun _ => Nat.zero_le _, by intro p a q k j d b h; simp at h⟩
  -- Availability at the empty cut: each `p_r` emits `o_r` alone in its component
  have hL : ∀ p : Fin N, ∃ L : List (LEv sp D N),
      (∃ τ, LRun (canon sp (init p)) L τ) ∧ (∀ (q : Fin N) k j d, LEv.recv q k j d ∉ L) ∧
      Compliant (Allowed Sys N init p) L ∧ (∀ j, LEv.inp j ∉ L) ∧
      ∀ h : p.val < rows.length, ∃ γ, LEv.out γ (rows[p.val]'h).2 ∈ L := by
    intro p
    by_cases hp : p.val < rows.length
    · have hσ : LRun (canon sp (init p)) ((H0 p).take 0) (canon sp (init p)) := .nil _
      have hinit : init p = (rows[p.val]'hp).1 := by simp [init, hp]
      have ho : (canon sp (init p)).R (canon sp (init p)).cur (rows[p.val]'hp).2 := by
        show sp.S (init p) _ ∧ init p ≼ init p
        rw [hinit]; exact ⟨hrows _ (List.getElem_mem ..), PO.refl _⟩
      obtain ⟨H', ext, hext, hwf', hprod', hpart', _, hnoinp, γ, hγ⟩ :=
        hA N init H0 comp hwf0 hprod0 hpart0 (fun _ => 0) hcut0 p _ hσ _ ho
      have hH' : H' p = ext p := by rw [hext p]; simp [H0]
      refine ⟨ext p, ?_, ?_, ?_, hnoinp p, fun _ => ⟨γ, hγ⟩⟩
      · obtain ⟨τ, h⟩ := hwf'.1 p; exact ⟨τ, hH' ▸ h⟩
      · intro q k j d hm
        obtain ⟨a, b, hab⟩ := List.append_of_mem hm
        rw [← hH'] at hab
        exact (hwf'.2 p a q k j d b hab).1 (Fin.ext (hpart'.2 p a q k j d b hab))
      · have := hprod' p; rw [hH'] at this; exact this
    · exact ⟨[], ⟨_, .nil _⟩, by simp, fun a e b h => by simp at h, by simp,
        fun h => absurd h hp⟩
  let Lf : History sp D N := fun p => Classical.choose (hL p)
  have hLs : ∀ p, _ := fun p => Classical.choose_spec (hL p)
  have hnrecv : ∀ (p : Fin N) a (q : Fin N) k (j' : Option I) (d : D) b,
      Lf p ≠ a ++ LEv.recv q k j' d :: b := by
    intro p a q k j' d b h
    have hm : LEv.recv q k j' d ∈ Lf p := by rw [h]; simp
    exact (hLs p).2.1 q k j' d hm
  -- glue the local runs into one partitioned, produced history
  have hwfc : WF init Lf :=
    ⟨fun p => (hLs p).1, fun p a q k j' d b h => absurd h (hnrecv p a q k j' d b)⟩
  have hprodc : Produced Sys N init Lf := fun p => (hLs p).2.2.1
  have hpartc : Partitioned Lf comp :=
    ⟨hcomp2, fun p a q k j' d b h => absurd h (hnrecv p a q k j' d b)⟩
  have hcutc : IsCut Lf (fun p => (Lf p).length) :=
    ⟨fun _ => Nat.le_refl _, fun p a q k j' d b h => by
      rw [List.take_length] at h; exact absurd h (hnrecv p a q k j' d b)⟩
  have hjall : ∀ p σ, LRun (canon sp (init p)) ((Lf p).take (Lf p).length) σ → σ.cur ≼ j := by
    intro p σ h
    rw [List.take_length] at h
    rw [lrun_noinp h (hLs p).2.2.2.1]
    show init p ≼ j
    simp only [init]
    split
    · exact hj _ (List.getElem_mem ..)
    · exact PO.refl j
  -- Partition Consistency at the final cut
  obtain ⟨H'', ext'', τ, hext'', _, hτj, hτ⟩ :=
    hP N init Lf comp hwfc hprodc hpartc _ hcutc j hjall
  obtain ⟨u, hu⟩ := τ.hasCur
  rw [hτj] at hu
  refine ⟨u, τ.sub _ _ hu, fun r hr => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  let p : Fin N := ⟨i, by omega⟩
  have h1 := hτ p
  rw [hext'' p, List.take_length] at h1
  obtain ⟨σ', h2, h3⟩ := lrun_append.1 h1
  obtain ⟨γ, hγ⟩ := (hLs p).2.2.2.2 hi
  exact lrun_out_mem h2 hγ j u ((lrun_mono h3).2 j u hu)

/-! ## Theorem `thm:complete-cap` -/

/-- **Complete CAP.**  Some system has Availability and Partition Consistency
iff the specification satisfies Lifted Monotonicity; moreover the
commitment-free system then has both. -/
theorem complete_cap (sp : Spec I O) (D : Type) :
    (∃ Sys : System sp D, Availability Sys ∧ PartitionConsistency Sys) ↔ sp.LiftedMono :=
  ⟨fun ⟨Sys, hA, hP⟩ => cap_necessary Sys hA hP,
   fun h => ⟨cfSystem sp D, cf_availability h, cf_partitionConsistency h⟩⟩

/-- The "moreover" clause of Theorem `thm:complete-cap`. -/
theorem complete_cap_cf (sp : Spec I O) (D : Type) (h : sp.LiftedMono) :
    Availability (cfSystem sp D) ∧ PartitionConsistency (cfSystem sp D) :=
  ⟨cf_availability h, cf_partitionConsistency h⟩


/-! ## Discrepancy: deterministic strategies

Def. `def:system` speaks of "a rule that chooses the participant's next
events".  If that rule is a *function* of the local history, the (2)⇒(1)
direction of Theorem `thm:complete-cap` fails: a participant alone in its
component has a single possible future, so it cannot have two incomparable
outputs of its fiber both available.  We give a three-output counterexample
satisfying Lifted Monotonicity.  The formalization above (and Appendix
`app:cap-response`) therefore reads strategies as nondeterministic. -/

/-- A strategy is deterministic when it allows at most one next event after
any local history. -/
def System.Deterministic (Sys : System sp D) : Prop :=
  ∀ n init p pre e e', Sys.strat n init p pre e → Sys.strat n init p pre e' → e = e'

/-- An output emitted after `o` on a run expands `o`. -/
theorem lrun_emit_row {σ τ : State sp} {l : List (LEv sp D n)} (h : LRun σ l τ)
    {γ : List (Commitment sp)} {o : O} (hm : LEv.out γ o ∈ l) : ∃ k, σ.R k o := by
  induction h with
  | nil => cases hm
  | inp hs _ ih =>
    obtain ⟨k, hk⟩ := ih (by simpa using hm); exact ⟨k, step_sub hs k o hk⟩
  | @out σ σc τ' ρ γ' o' es ha hs _ _ ih =>
    have hsub := (applySeq_spec γ' σ σc ha).2
    rcases List.mem_cons.1 hm with he | hm'
    · cases he; exact ⟨_, hsub _ _ (step_output_inv hs).1⟩
    · obtain ⟨k, hk⟩ := ih hm'; exact ⟨k, hsub _ _ (step_sub hs k o hk)⟩
  | send _ ih => exact ih (by simpa using hm)
  | recv _ ih => exact ih (by simpa using hm)

theorem lrun_later_le {σ τ : State sp} {l1 l2 : List (LEv sp D n)}
    {γ γ' : List (Commitment sp)} {o o' : O}
    (h : LRun σ (l1 ++ LEv.out γ o :: l2) τ) (hm : LEv.out γ' o' ∈ l2) : o ≼ o' := by
  obtain ⟨σ1, _, h2⟩ := lrun_append.1 h
  cases h2 with
  | out ha hs _ hr =>
    obtain ⟨k, hk⟩ := lrun_emit_row hr hm
    rw [(step_output_inv hs).2.2] at hk; exact hk.2

/-- A participant run cannot emit two incomparable outputs. -/
theorem lrun_no_incomparable {σ τ : State sp} {l : List (LEv sp D n)} (h : LRun σ l τ)
    {γ γ' : List (Commitment sp)} {o o' : O} (hm : LEv.out γ o ∈ l) (hm' : LEv.out γ' o' ∈ l)
    (h1 : ¬ o ≼ o') (h2 : ¬ o' ≼ o) : False := by
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hm
  rcases List.mem_append.1 hm' with hin | hin
  · obtain ⟨m1, m2, rfl⟩ := List.append_of_mem hin
    have : LRun σ (m1 ++ LEv.out γ' o' :: (m2 ++ LEv.out γ o :: l2)) τ := by simpa using h
    exact h2 (lrun_later_le (γ' := γ) this (by simp))
  · rcases List.mem_cons.1 hin with he | hin'
    · cases he; exact h1 (PO.refl _)
    · exact h1 (lrun_later_le h hin')

theorem det_prefix (Sys : System sp D) (hdet : Sys.Deterministic) {N : Nat} {init : Fin N → I}
    {p : Fin N} : ∀ (L1 L2 pre : List (LEv sp D N)),
    (∀ a e b, L1 = a ++ e :: b → Sys.strat N init p (pre ++ a) e) →
    (∀ a e b, L2 = a ++ e :: b → Sys.strat N init p (pre ++ a) e) →
    (∃ t, L2 = L1 ++ t) ∨ (∃ t, L1 = L2 ++ t)
  | [], L2, _, _, _ => Or.inl ⟨L2, rfl⟩
  | _ :: _, [], _, _, _ => Or.inr ⟨_, rfl⟩
  | e1 :: L1, e2 :: L2, pre, h1, h2 => by
    have he : e1 = e2 :=
      hdet N init p _ e1 e2 (by simpa using h1 [] e1 L1 rfl) (by simpa using h2 [] e2 L2 rfl)
    subst he
    have ih := det_prefix Sys hdet L1 L2 (pre ++ [e1])
      (fun a e b hab => by simpa using h1 (e1 :: a) e b (by simp [hab]))
      (fun a e b hab => by simpa using h2 (e1 :: a) e b (by simp [hab]))
    rcases ih with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact Or.inl ⟨t, by simp [ht]⟩
    · exact Or.inr ⟨t, by simp [ht]⟩

theorem compliant_strat {Sys : System sp D} {N : Nat} {init : Fin N → I} {p : Fin N}
    {L : List (LEv sp D N)} (hc : Compliant (Allowed Sys N init p) L)
    (hn : ∀ j, LEv.inp j ∉ L) :
    ∀ a e b, L = a ++ e :: b → Sys.strat N init p ([] ++ a) e := by
  intro a e b h
  have hA := hc a e b h
  cases e with
  | inp j => exact absurd (by rw [h]; simp) (hn j)
  | out γ o => exact by simpa using hA.2
  | send => simpa [Allowed] using hA
  | recv => simpa [Allowed] using hA

/-- Three outputs `a`, `b` incomparable, both below `top`. -/
inductive Tri where
  | a | b | top
  deriving DecidableEq

def Tri.le : Tri → Tri → Prop
  | x, y => x = y ∨ y = .top

instance : PO Tri where
  le := Tri.le
  refl := fun x => Or.inl rfl
  trans := by
    intro x y z h1 h2
    unfold Tri.le at *
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp
  antisymm := by
    intro x y h1 h2
    unfold Tri.le at *
    cases x <;> cases y <;> simp_all

instance : PO Unit where
  le := fun _ _ => True
  refl := fun _ => trivial
  trans := fun _ _ => trivial
  antisymm := fun {a b} _ _ => by cases a; cases b; rfl

/-- One input, fiber `{a, b, top}`. -/
def triSpec : Spec Unit Tri where
  S := fun _ _ => True
  total := fun _ => ⟨.a, trivial⟩

theorem triSpec_liftedMono : triSpec.LiftedMono := by
  intro i j _ X _ _
  exact ⟨.top, trivial, fun x _ => Or.inr rfl⟩

/-- **Counterexample** to (2)⇒(1) of Theorem `thm:complete-cap` under a
deterministic reading of strategies: `triSpec` satisfies Lifted Monotonicity,
yet no system with deterministic strategies has Availability. -/
theorem deterministic_not_available (D : Type) (Sys : System triSpec D)
    (hdet : Sys.Deterministic) : ¬ Availability Sys := by
  intro hA
  let init : Fin 2 → Unit := fun _ => ()
  let comp : Fin 2 → Nat := fun p => p.val
  let H0 : History triSpec D 2 := fun _ => []
  have hwf0 : WF init H0 :=
    ⟨fun p => ⟨_, .nil _⟩, by intro p a q k j d b h; simp [H0] at h⟩
  have hprod0 : Produced Sys 2 init H0 := fun p a e b h => by simp [H0] at h
  have hpart0 : Partitioned H0 comp :=
    ⟨⟨0, 1, by simp [comp]⟩, by intro p a q k j d b h; simp [H0] at h⟩
  have hcut0 : IsCut H0 (fun _ => 0) :=
    ⟨fun _ => Nat.zero_le _, by intro p a q k j d b h; simp at h⟩
  have hσ : LRun (canon triSpec (init 0)) ((H0 0).take 0) (canon triSpec (init 0)) := .nil _
  have hav : ∀ o : Tri, ∃ L : List (LEv triSpec D 2),
      (∃ τ, LRun (canon triSpec (init 0)) L τ) ∧ Compliant (Allowed Sys 2 init 0) L ∧
      (∀ j, LEv.inp j ∉ L) ∧ ∃ γ, LEv.out γ o ∈ L := by
    intro o
    obtain ⟨H', ext, hext, hwf', hprod', _, _, hnoinp, γ, hγ⟩ :=
      hA 2 init H0 comp hwf0 hprod0 hpart0 (fun _ => 0) hcut0 0 _ hσ o ⟨trivial, trivial⟩
    have hH' : H' 0 = ext 0 := by rw [hext 0]; simp [H0]
    refine ⟨ext 0, ?_, ?_, hnoinp 0, γ, hγ⟩
    · obtain ⟨τ, h⟩ := hwf'.1 0; exact ⟨τ, hH' ▸ h⟩
    · have := hprod' 0; rw [hH'] at this; exact this
  obtain ⟨La, ⟨τa, hra⟩, hca, hna, γa, hγa⟩ := hav .a
  obtain ⟨Lb, ⟨τb, hrb⟩, hcb, hnb, γb, hγb⟩ := hav .b
  have hab : ¬ (Tri.a ≼ Tri.b) := by
    show ¬ Tri.le .a .b; simp [Tri.le]
  have hba : ¬ (Tri.b ≼ Tri.a) := by
    show ¬ Tri.le .b .a; simp [Tri.le]
  rcases det_prefix Sys hdet La Lb [] (compliant_strat hca hna) (compliant_strat hcb hnb) with
    ⟨t, ht⟩ | ⟨t, ht⟩
  · subst ht
    exact lrun_no_incomparable hrb (List.mem_append_left _ hγa) hγb hab hba
  · subst ht
    exact lrun_no_incomparable hra hγa (List.mem_append_left _ hγb) hab hba


end CAP
end CC
