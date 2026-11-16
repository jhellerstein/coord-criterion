import CoordCriterion.Appendix.DeploymentFor
import CoordCriterion.Appendix.DeploymentExamples
import CoordCriterion.CAP.AvailabilityFor

/-!
# The existence half of the deployment form of Complete CAP (Appendix `app:deployment`)

Prop. `thm:complete-cap-deployment` (`Deploy.partition_compatibility`,
`Deploy.partition_compatibility_confluent`) characterizes, for a deployment,
when separable participant run families are confluent.  This file adds the
existence half, in the shape of Complete CAP for an explicit relation
(`CAP.complete_cap_for`, whose sufficiency uses `CAP.respSystem`):

* `compatible_of_monoAcrossPartitions`: with at least two participants, a
  deployment that is monotone across partitions makes *every* authorized
  participant run family compatible at every common input extension, separable
  or not (two emitters can be put on different sides of a partition; a single
  emitter's outputs form a chain whose last row, paired with a silent
  participant on another side, is a separable family).
  `monoAcrossPartitions_iff_compatible` is the resulting equivalence.
* `depSystem Dp`: participant `p` runs the canonical response strategy of
  `respSystem (Dp.A p)`: it emits, by its output event, any authorized output
  at its current input that extends its earlier outputs.
* `deployment_complete_cap`: if the deployment is monotone across partitions
  (and `2 ≤ n`), `depSystem Dp` has Deployment Availability and Partition
  Consistency on histories over the deployment's participants
  (`PartitionConsistencyAt`); `deployment_complete_cap_exists` states the
  existence.
-/

namespace CC
namespace Deploy

open CC.CAP

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {n : Nat} {D : Type}

/-! ## Every authorized family is compatible -/

/-- With at least two participants, monotonicity across partitions makes every
authorized participant run family compatible at every common input extension. -/
theorem compatible_of_monoAcrossPartitions (hn : 2 ≤ n) (Dp : Deployment sp n)
    (h : MonoAcrossPartitions Dp) (F : Family sp n) (hA : Authorized Dp F) (j : I)
    (hj : UB F j) : ∃ u, sp.P j u ∧ ∀ p r, Emits F p r → r.2 ≼ u := by
  classical
  by_cases h2 : ∃ p q r r', Emits F p r ∧ Emits F q r' ∧ p ≠ q
  · obtain ⟨p, q, r, r', hp, hq, hpq⟩ := h2
    let comp : Fin n → Nat := fun x => if x = p then 0 else 1
    have hcq : comp q = 1 := by simp [comp, Ne.symm hpq]
    have hcp : comp p = 0 := by simp [comp]
    exact h comp ⟨p, q, by rw [hcp, hcq]; decide⟩ F hA
      (Or.inl ⟨p, q, r, r', hp, hq, by rw [hcp, hcq]; decide⟩) j hj
  · by_cases h1 : ∃ p r, Emits F p r
    · obtain ⟨p, r, hpr⟩ := h1
      have honly : ∀ q r', Emits F q r' → q = p := fun q r' hq =>
        Classical.byContradiction fun hne => h2 ⟨p, q, r, r', hpr, hq, fun e => hne e.symm⟩
      obtain ⟨m, hm, hrm⟩ := hpr
      obtain ⟨r₀, hr₀, hmax⟩ := rows_max m (List.ne_nil_of_mem hrm)
      have he₀ : Emits F p r₀ := ⟨m, hm, hr₀⟩
      obtain ⟨hP₀, hle₀⟩ := emits_le hj he₀
      let q : Fin n := if p.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hqp : q ≠ p := by
        intro e; have := congrArg Fin.val e
        by_cases h0 : p.val = 0 <;> simp [q, h0] at this <;> omega
      let G : Family sp n := fun x =>
        if x = p then some (oneShot sp r₀.1 r₀.2 hP₀)
        else if x = q then some (silentRun sp j) else none
      have hGp : G p = some (oneShot sp r₀.1 r₀.2 hP₀) := by simp [G]
      have hGq : G q = some (silentRun sp j) := by simp [G, hqp]
      have hGemit : ∀ x r', Emits G x r' → x = p ∧ r' = r₀ := by
        rintro x r' ⟨m', hm', hr'⟩
        by_cases hx : x = p
        · subst hx; rw [hGp] at hm'; cases hm'; simp at hr'; exact ⟨rfl, hr'⟩
        · by_cases hxq : x = q
          · subst hxq; rw [hGq] at hm'; cases hm'; simp at hr'
          · simp [G, hx, hxq] at hm'
      let comp : Fin n → Nat := fun x => if x = p then 0 else 1
      have hcq : comp q = 1 := by simp [comp, hqp]
      have hcp : comp p = 0 := by simp [comp]
      have hAG : Authorized Dp G := by
        intro x r' he
        obtain ⟨hx, hr⟩ := hGemit x r' he
        rw [hx, hr]; exact hA p r₀ he₀
      have hsep : Separable G comp :=
        Or.inr ⟨r₀, p, q, ⟨_, hGp, by simp⟩, fun x r' he => (hGemit x r' he).2,
          ⟨_, hGq, rfl⟩, by rw [hcp, hcq]; decide⟩
      have hub : UB G j := by
        intro x m' hm'
        by_cases hx : x = p
        · subst hx; rw [hGp] at hm'; cases hm'; exact hle₀
        · by_cases hxq : x = q
          · subst hxq; rw [hGq] at hm'; cases hm'; exact PO.refl j
          · simp [G, hx, hxq] at hm'
      obtain ⟨u, hu, hall⟩ := h comp ⟨p, q, by rw [hcp, hcq]; decide⟩ G hAG hsep j hub
      refine ⟨u, hu, fun x r' he => ?_⟩
      have hx := honly x r' he
      subst hx
      obtain ⟨m', hm', hr'⟩ := he
      rw [hm] at hm'; cases hm'
      exact PO.trans (hmax r' hr') (hall _ r₀ ⟨_, hGp, by simp⟩)
    · obtain ⟨u, hu⟩ := sp.total j
      exact ⟨u, hu, fun p r he => absurd ⟨p, r, he⟩ h1⟩

/-- With at least two participants: monotone across partitions iff every
authorized participant run family is compatible at every common input
extension. -/
theorem monoAcrossPartitions_iff_compatible (hn : 2 ≤ n) (Dp : Deployment sp n) :
    MonoAcrossPartitions Dp ↔
      ∀ F : Family sp n, Authorized Dp F → ∀ j, UB F j →
        ∃ u, sp.P j u ∧ ∀ p r, Emits F p r → r.2 ≼ u :=
  ⟨fun h F hA j hj => compatible_of_monoAcrossPartitions hn Dp h F hA j hj,
   fun h _ _ F hA _ j hj => h F hA j hj⟩

/-! ## The deployment's canonical system -/

/-- Participant `p` of `Fin n` follows the canonical response strategy for its
authorized table `Dp.A p`; numbers outside `Fin n` do nothing. -/
noncomputable def depSystem (Dp : Deployment sp n) : System sp D where
  basis := fun c => ∃ u, c = kc u
  rule := fun k x pre e => if h : k < n then respF (Dp.A ⟨k, h⟩) x pre e else False

theorem allowed_dep (Dp : Deployment sp n) (init : Fin n → I) (p : Fin n) :
    Allowed (depSystem (D := D) Dp) n init p = Allowed (respSystem (Dp.A p)) n init p := by
  funext pre e
  cases e <;> simp [Allowed, System.strat, depSystem, respSystem, p.isLt]

theorem depSystem_canonical (Dp : Deployment sp n) : CanonicalSystem (depSystem (D := D) Dp) := by
  intro m init p pre γ h
  simp only [System.strat, depSystem] at h
  split at h
  · exact h
  · exact h

/-- Partition Consistency (at the end of histories) on histories over `Fin n`. -/
def PartitionConsistencyAt (Sys : System sp D) (n : Nat) : Prop :=
  ∀ (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ j : I, (∀ p σ, LRun (canon sp (init p)) (H p) σ → σ.cur ≼ j) →
    ∃ τ : State sp, τ.cur = j ∧ ∃ ext : Fin n → List (LEv sp D n),
      WF init (fun q => H q ++ ext q) ∧ ∀ p, LRun (canon sp (init p)) (H p ++ ext p) τ

/-- `depSystem Dp` has Deployment Availability (for any deployment). -/
theorem depSystem_availability (Dp : Deployment sp n) :
    DeploymentAvailability (depSystem (D := D) Dp) Dp := by
  rw [deploymentAvailability_iff_end]
  intro init H comp hwf hprod hpart p σ hσ o hR hAo
  classical
  let c : Fin n → Nat := fun q => (H q).length
  have hcut : IsCut H c := isCut_full hwf
  have hσ' : LRun (canon sp (init p)) ((H p).take (c p)) σ := by
    simp only [c, List.take_length]; exact hσ
  have hcomp : Compliant (Allowed (respSystem (D := D) (Dp.A p)) n init p) ((H p).take (c p)) := by
    rw [← allowed_dep]; exact compliant_take (hprod p) (c p)
  obtain ⟨h1, h2, _, _⟩ := rinv_of_produced (Dp.A p) hcomp hσ'
  have hge : ∀ o' ∈ emittedOf (((H p).take (c p)).map LEv.erase), o' ≼ o :=
    ((h2 _ _).1 hR).2.2
  have hstep := step_output_outState hR
  obtain ⟨H', ext, hext, hwf', hprod', hpart', hp, hq⟩ :=
    extend_single (depSystem (D := D) Dp) hwf hprod hpart hcut hσ' (e := .out o)
      (by intro q k j d h; cases h) (.out hstep (.nil _))
      (by rw [allowed_dep]; exact ⟨fun _ _ => Or.inr ⟨o, rfl⟩, by rw [← h1]; exact hAo, hge⟩)
  have hH' : H' = fun q => H q ++ ext q := by
    funext q; rw [hext q]; simp [c]
  subst hH'
  refine ⟨ext, hwf', hprod', hpart', fun q hq' => hq q (fun h => hq' (h ▸ rfl)), ?_, ?_⟩
  · intro q j
    by_cases hqp : q = p
    · subst hqp; rw [hp]; simp
    · rw [hq q hqp]; simp
  · rw [hp]; simp

/-- If the deployment is monotone across partitions (with `2 ≤ n`), `depSystem Dp`
has Partition Consistency on histories over `Fin n`. -/
theorem depSystem_pc (hn : 2 ≤ n) (Dp : Deployment sp n) (hmono : MonoAcrossPartitions Dp) :
    PartitionConsistencyAt (depSystem (D := D) Dp) n := by
  intro init H comp hwf hprod hpart j hj
  classical
  let c : Fin n → Nat := fun q => (H q).length
  have hcut : IsCut H c := isCut_full hwf
  have hj' : ∀ p σ, LRun (canon sp (init p)) ((H p).take (c p)) σ → σ.cur ≼ j := by
    intro p σ h; simp only [c, List.take_length] at h; exact hj p σ h
  -- each participant's emitted outputs are dominated by one authorized row
  have hdom : ∀ p : Fin n, emittedOf (((H p).take (c p)).map LEv.erase) = [] ∨
      ∃ i om, Dp.A p i om ∧ i ≼ j ∧
        ∀ o ∈ emittedOf (((H p).take (c p)).map LEv.erase), o ≼ om := by
    intro p
    obtain ⟨τp, hp⟩ := hwf.1 p
    obtain ⟨σ, hσ⟩ := lrun_take hp (c p)
    have hcomp : Compliant (Allowed (respSystem (D := D) (Dp.A p)) n init p) ((H p).take (c p)) := by
      rw [← allowed_dep]; exact compliant_take (hprod p) (c p)
    obtain ⟨_, _, _, h4⟩ := rinv_of_produced (Dp.A p) hcomp hσ
    rcases h4 with h4 | ⟨i, om, hA, hi, hall⟩
    · exact Or.inl h4
    · exact Or.inr ⟨i, om, hA, PO.trans hi (hj' p σ hσ), hall⟩
  let F : Family sp n := fun p =>
    if h : ∃ i om, Dp.A p i om ∧ i ≼ j ∧
        ∀ o ∈ emittedOf (((H p).take (c p)).map LEv.erase), o ≼ om then
      some (oneShot sp (Classical.choose h) (Classical.choose (Classical.choose_spec h))
        (Dp.sub _ _ _ (Classical.choose_spec (Classical.choose_spec h)).1))
    else none
  have hFrows : ∀ p m, F p = some m → ∃ i om, m.rows = [(i, om)] ∧ Dp.A p i om ∧ i ≼ j ∧
      m.fin.cur = i ∧ ∀ o ∈ emittedOf (((H p).take (c p)).map LEv.erase), o ≼ om := by
    intro p m hm
    simp only [F] at hm
    split at hm
    · rename_i h
      cases hm
      obtain ⟨hA, hi, hall⟩ := Classical.choose_spec (Classical.choose_spec h)
      exact ⟨_, _, by simp, hA, hi, by simp, hall⟩
    · cases hm
  have hauth : Authorized Dp F := by
    rintro p r ⟨m, hm, hr⟩
    obtain ⟨i, om, hrows, hA, -⟩ := hFrows p m hm
    rw [hrows] at hr; simp at hr; subst hr; exact hA
  have hub : UB F j := by
    intro p m hm
    obtain ⟨i, om, -, -, hi, hcur, -⟩ := hFrows p m hm
    rw [hcur]; exact hi
  obtain ⟨u, hu, hall⟩ := compatible_of_monoAcrossPartitions hn Dp hmono F hauth j hub
  have hrpc : RPCAt H c j := by
    refine ⟨u, hu, fun p o hm => ?_⟩
    have ho := mem_emittedOf hm
    rcases hdom p with h0 | hex
    · rw [h0] at ho; cases ho
    · have hFp : ∃ m, F p = some m := by simp only [F, dif_pos hex]; exact ⟨_, rfl⟩
      obtain ⟨m, hm'⟩ := hFp
      obtain ⟨i, om, hrows, -, -, -, hle⟩ := hFrows p m hm'
      exact PO.trans (hle o ho) (hall p (i, om) ⟨m, hm', by rw [hrows]; simp⟩)
  obtain ⟨H', ext, τ, hext, hw', hτ, hrun⟩ :=
    (canonical_rpc_iff_confluent (depSystem_canonical Dp) hwf hprod hcut hj').1 hrpc
  have hH' : H' = fun q => H q ++ ext q := by
    funext q; rw [hext q]; simp [c]
  subst hH'
  exact ⟨τ, hτ, ext, hw', hrun⟩

/-- **Existence half of Prop. `thm:complete-cap-deployment`.**  For a
deployment over at least two participants that is monotone across partitions,
the deployment's canonical system has Deployment Availability and Partition
Consistency (on histories over the deployment's participants). -/
theorem deployment_complete_cap (hn : 2 ≤ n) (Dp : Deployment sp n)
    (hmono : MonoAcrossPartitions Dp) :
    DeploymentAvailability (depSystem (D := D) Dp) Dp ∧
      PartitionConsistencyAt (depSystem (D := D) Dp) n :=
  ⟨depSystem_availability Dp, depSystem_pc hn Dp hmono⟩

theorem deployment_complete_cap_exists (hn : 2 ≤ n) (Dp : Deployment sp n)
    (hmono : MonoAcrossPartitions Dp) :
    ∃ Sys : System sp D, DeploymentAvailability Sys Dp ∧ PartitionConsistencyAt Sys n :=
  ⟨_, deployment_complete_cap hn Dp hmono⟩


/-! ## Necessity for authorized rows -/

/-- From the empty history, a participant alone on its side emits an authorized
row at its initial input. -/
theorem da_emit {Dp : Deployment sp n} (Sys : System sp D) (hDA : DeploymentAvailability Sys Dp)
    (comp : Fin n → Nat) (hcomp : ∃ p q, comp p ≠ comp q) (init : Fin n → I) (p : Fin n) (o : O)
    (ho : Dp.A p (init p) o) :
    ∃ ext : History sp D n, WF init ext ∧ Produced Sys n init ext ∧ Partitioned ext comp ∧
      (∀ q, comp q ≠ comp p → ext q = []) ∧ (∀ q j, LEv.inp j ∉ ext q) ∧ LEv.out o ∈ ext p := by
  let H0 : History sp D n := fun _ => []
  have hwf0 : WF init H0 :=
    wf_of_ne (fun p => ⟨_, .nil _⟩) (by intro p a q k j d b h; simp [H0] at h)
  have hprod0 : Produced Sys n init H0 := fun p a e b h => by simp [H0] at h
  have hpart0 : Partitioned H0 comp := ⟨hcomp, by intro p a q k j d b h; simp [H0] at h⟩
  have hcut : IsCut H0 (fun _ => 0) :=
    ⟨fun _ => Nat.zero_le _, by intro p a q k j d b h; simp at h⟩
  have hσ : LRun (canon sp (init p)) ((H0 p).take 0) (canon sp (init p)) := .nil _
  obtain ⟨H', ext, hext, hwf, hprod, hpart, hout, hnoinp, hγ⟩ :=
    hDA init H0 comp hwf0 hprod0 hpart0 _ hcut p _ hσ o ⟨Dp.sub _ _ _ ho, PO.refl _⟩ ho
  have e : H' = ext := funext fun q => by rw [hext q]; simp [H0]
  subst e
  exact ⟨H', hwf, hprod, hpart, hout, hnoinp, hγ⟩

/-- **Necessity in deployment form.**  If a system has Deployment Availability and
Partition Consistency (over `n ≥ 2` participants), then authorized rows of
different participants, at inputs with a common input extension `j`, have a
common output extension in `P(j)`: each participant, alone on its side, emits
its row, and Partition Consistency reconciles them.  This is the deployment
counterpart of `CAP.consistentOn_of_availabilityFor`. -/
theorem authorized_reconciled (hn : 2 ≤ n) {Dp : Deployment sp n} (Sys : System sp D)
    (hDA : DeploymentAvailability Sys Dp) (hPC : PartitionConsistencyAt Sys n)
    (init : Fin n → I) (o : Fin n → Option O) (ho : ∀ p v, o p = some v → Dp.A p (init p) v)
    (j : I) (hj : ∀ p, init p ≼ j) : ∃ u, sp.P j u ∧ ∀ p v, o p = some v → v ≼ u := by
  classical
  let comp : Fin n → Nat := fun p => p.val
  have hcomp : ∃ p q : Fin n, comp p ≠ comp q :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [comp]⟩
  have hL : ∀ p, ∃ L : List (LEv sp D n), (∃ τ, LRun (canon sp (init p)) L τ) ∧
      (∀ q k j d, LEv.recv q k j d ∉ L) ∧ Compliant (Allowed Sys n init p) L ∧
      (∀ j, LEv.inp j ∉ L) ∧ ∀ v, o p = some v → LEv.out v ∈ L := by
    intro p
    cases hop : o p with
    | none =>
      exact ⟨[], ⟨_, .nil _⟩, by simp, fun a e b h => by simp at h, by simp,
        fun v h => by cases h⟩
    | some v =>
      obtain ⟨ext, hwf, hprod, hpart, -, hni, hout⟩ :=
        da_emit Sys hDA comp hcomp init p v (ho p v hop)
      refine ⟨ext p, hwf.runs p, ?_, hprod p, hni p, fun v' h => by cases h; exact hout⟩
      intro q k j d hm
      obtain ⟨a, b, hab⟩ := List.append_of_mem hm
      exact (hwf.matched p a q k j d b hab).1 (Fin.ext (hpart.2 p a q k j d b hab))
  let L : History sp D n := fun p => Classical.choose (hL p)
  have hLs : ∀ p, _ := fun p => Classical.choose_spec (hL p)
  have hnr : ∀ p q k j d, LEv.recv q k j d ∉ L p := fun p => (hLs p).2.1
  have hwf : WF init L := wf_of_noRecv (fun p => (hLs p).1) hnr
  have hprod : Produced Sys n init L := fun p => (hLs p).2.2.1
  have hpart : Partitioned L comp :=
    ⟨hcomp, fun p a q k j d b h => absurd (by rw [h]; simp) (hnr p q k j d)⟩
  have hj' : ∀ p σ, LRun (canon sp (init p)) (L p) σ → σ.cur ≼ j := by
    intro p σ h; rw [lrun_noinp h (hLs p).2.2.2.1]; exact hj p
  obtain ⟨τ, hτj, ext, -, hτ⟩ := hPC init L comp hwf hprod hpart j hj'
  obtain ⟨u, hu⟩ := τ.hasCur
  rw [hτj] at hu
  refine ⟨u, τ.sub _ _ hu, fun p v hv => ?_⟩
  obtain ⟨σ', h2, h3⟩ := lrun_append.1 (hτ p)
  exact lrun_out_mem h2 ((hLs p).2.2.2.2 v hv) j u ((lrun_mono h3).2 j u hu)


/-- Deployment Availability and Partition Consistency make every authorized
participant run family compatible at every common input extension (each
participant's last emitted row dominates its earlier ones). -/
theorem compatible_of_system (hn : 2 ≤ n) {Dp : Deployment sp n} (Sys : System sp D)
    (hDA : DeploymentAvailability Sys Dp) (hPC : PartitionConsistencyAt Sys n)
    (F : Family sp n) (hA : Authorized Dp F) (j : I) (hj : UB F j) :
    ∃ u, sp.P j u ∧ ∀ p r, Emits F p r → r.2 ≼ u := by
  classical
  have hlast : ∀ p, (∃ r₀, Emits F p r₀ ∧ ∀ r, Emits F p r → r.2 ≼ r₀.2) ∨ ∀ r, ¬ Emits F p r := by
    intro p
    cases hp : F p with
    | none => exact Or.inr fun r ⟨m, hm, _⟩ => by rw [hp] at hm; cases hm
    | some m =>
      by_cases hne : m.rows = []
      · exact Or.inr fun r ⟨m', hm', hr⟩ => by
          rw [hp] at hm'; cases hm'; rw [hne] at hr; cases hr
      · obtain ⟨r₀, hr₀, hmax⟩ := rows_max m hne
        exact Or.inl ⟨r₀, ⟨m, hp, hr₀⟩, fun r ⟨m', hm', hr⟩ => by
          rw [hp] at hm'; cases hm'; exact hmax r hr⟩
  let init : Fin n → I := fun p =>
    if h : ∃ r₀, Emits F p r₀ ∧ ∀ r, Emits F p r → r.2 ≼ r₀.2 then (Classical.choose h).1 else j
  let o : Fin n → Option O := fun p =>
    if h : ∃ r₀, Emits F p r₀ ∧ ∀ r, Emits F p r → r.2 ≼ r₀.2 then some (Classical.choose h).2
    else none
  have ho : ∀ p v, o p = some v → Dp.A p (init p) v := by
    intro p v hv
    simp only [o] at hv
    split at hv
    · rename_i h
      cases hv
      simp only [init, dif_pos h]
      exact hA p _ (Classical.choose_spec h).1
    · cases hv
  have hji : ∀ p, init p ≼ j := by
    intro p
    simp only [init]
    split
    · rename_i h; exact (emits_le hj (Classical.choose_spec h).1).2
    · exact PO.refl j
  obtain ⟨u, hu, hall⟩ := authorized_reconciled hn Sys hDA hPC init o ho j hji
  refine ⟨u, hu, fun p r hr => ?_⟩
  rcases hlast p with h | h
  · have hsome : o p = some (Classical.choose h).2 := by simp only [o, dif_pos h]
    exact PO.trans ((Classical.choose_spec h).2 r hr) (hall p _ hsome)
  · exact absurd hr (h r)

/-- **The deployment form of Complete CAP.**  For a deployment over at least two
participants, some system has Deployment Availability and Partition Consistency
if and only if the specification is monotone across partitions under the
deployment. -/
theorem deployment_complete_cap_iff (hn : 2 ≤ n) (Dp : Deployment sp n) :
    (∃ Sys : System sp D, DeploymentAvailability Sys Dp ∧ PartitionConsistencyAt Sys n) ↔
      MonoAcrossPartitions Dp := by
  constructor
  · rintro ⟨Sys, hDA, hPC⟩ comp _ F hA _ j hj
    exact compatible_of_system hn Sys hDA hPC F hA j hj
  · exact deployment_complete_cap_exists hn Dp

end Deploy
end CC
