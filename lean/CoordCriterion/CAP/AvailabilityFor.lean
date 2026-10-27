import CoordCriterion.CAP.Forced
import CoordCriterion.CAP.ResponseAvailability

/-!
# Complete CAP for a declared availability relation

A guarantee may declare, besides its specification `S`, an *availability
relation* `A ⊆ S`: the outputs a system must keep emittable.  Availability for
`A` asks that each participant can emit, in a continuation local to it, every
output of `A` at its current input that is still in its fiber.  Partition
Consistency is unchanged and measured in `S`.

`complete_cap_for`: some system has Availability for `A` and Partition
Consistency iff `S` is consistent on `A` (every finite family of rows of `A`
with a common expansion `j` has a common refinement in `S(j)`).  The paper
calls this condition *Lifted Monotonicity for `A`* (Def. `def:lm-for-A`); the
library keeps the name `ConsistentOn`.

* `A = S` is the interface form: consistency on `S` is the common-expansion
  condition, i.e. Lifted Monotonicity (`availabilityFor_S`).
* Necessity uses only a common refinement of the emitted outputs
  (`CommonRefinementAtEnd`), and holds for any system.
* Sufficiency uses the canonical system `respSystem A`, which emits any output
  of `A` in its current fiber by the canonical event.
-/

namespace CC
namespace CAP

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type}

/-- Availability for `A`, at the end of histories. -/
def AvailabilityFor (A : Table I O) (Sys : System sp D) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) (H p) σ →
    ∀ o, σ.R σ.cur o → A σ.cur o →
    ∃ ext : Fin n → List (LEv sp D n),
      WF init (fun q => H q ++ ext q) ∧ Produced Sys n init (fun q => H q ++ ext q) ∧
      Partitioned (fun q => H q ++ ext q) comp ∧
      (∀ q, comp q ≠ comp p → ext q = []) ∧
      (∀ q j, LEv.inp j ∉ ext q) ∧
      ∃ γ, LEv.out γ o ∈ ext p

/-- With `A = S`, Availability for `A` is the paper's Availability. -/
theorem availabilityFor_S (Sys : System sp D) :
    AvailabilityFor sp.S Sys ↔ AvailabilityAtEnd Sys :=
  ⟨fun h n init H comp hw hp hpt p σ hσ o ho => h n init H comp hw hp hpt p σ hσ o ho (σ.sub _ _ ho),
   fun h n init H comp hw hp hpt p σ hσ o ho _ => h n init H comp hw hp hpt p σ hσ o ho⟩

/-! ## Necessity -/

/-- (⇒): if some system keeps `A` available and the emitted outputs
reconcilable, `S` is consistent on `A`.  One participant per row, each alone
in its component, plus one at `j`. -/
theorem consistentOn_of_availabilityFor (A : Table I O) (hAS : ∀ i o, A i o → sp.S i o)
    (Sys : System sp D) (hA : AvailabilityFor A Sys) (hC : CommonRefinementAtEnd Sys) :
    ConsistentOn sp A := by
  intro rows hrows j hj
  classical
  by_cases hne : rows = []
  · subst hne; obtain ⟨u, hu⟩ := sp.total j; exact ⟨u, hu, by simp⟩
  have hlen : 0 < rows.length := List.length_pos_iff.2 hne
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
  -- each `p_r` emits `o_r` alone in its component
  have hL : ∀ p : Fin N, ∃ L : List (LEv sp D N),
      (∃ τ, LRun (canon sp (init p)) L τ) ∧ (∀ (q : Fin N) k j d, LEv.recv q k j d ∉ L) ∧
      Compliant (Allowed Sys N init p) L ∧ (∀ j, LEv.inp j ∉ L) ∧
      ∀ h : p.val < rows.length, ∃ γ, LEv.out γ (rows[p.val]'h).2 ∈ L := by
    intro p
    by_cases hp : p.val < rows.length
    · have hinit : init p = (rows[p.val]'hp).1 := by simp [init, hp]
      have hArow : A (rows[p.val]'hp).1 (rows[p.val]'hp).2 := hrows _ (List.getElem_mem ..)
      have ho : (canon sp (init p)).R (canon sp (init p)).cur (rows[p.val]'hp).2 := by
        show sp.S (init p) _ ∧ init p ≼ init p
        rw [hinit]; exact ⟨hAS _ _ hArow, PO.refl _⟩
      have hAo : A (canon sp (init p)).cur (rows[p.val]'hp).2 := by
        show A (init p) _; rw [hinit]; exact hArow
      obtain ⟨ext, hwf', hprod', hpart', _, hnoinp, γ, hγ⟩ :=
        hA N init H0 comp hwf0 hprod0 hpart0 p _ (.nil _) _ ho hAo
      have hH' : H0 p ++ ext p = ext p := by simp [H0]
      refine ⟨ext p, ?_, ?_, ?_, hnoinp p, fun _ => ⟨γ, hγ⟩⟩
      · obtain ⟨τ, h⟩ := hwf'.1 p; exact ⟨τ, hH' ▸ h⟩
      · intro q k j d hm
        obtain ⟨a, b, hab⟩ := List.append_of_mem hm
        have hab' : (fun q => H0 q ++ ext q) p = a ++ LEv.recv q k j d :: b := by
          show H0 p ++ ext p = _; rw [hH']; exact hab
        exact (hwf'.2 p a q k j d b hab').1 (Fin.ext (hpart'.2 p a q k j d b hab'))
      · have := hprod' p; simp only [H0, List.nil_append] at this; exact this
    · exact ⟨[], ⟨_, .nil _⟩, by simp, fun a e b h => by simp at h, by simp,
        fun h => absurd h hp⟩
  let Lf : History sp D N := fun p => Classical.choose (hL p)
  have hLs : ∀ p, _ := fun p => Classical.choose_spec (hL p)
  have hnrecv : ∀ (p : Fin N) a (q : Fin N) k (j' : Option I) (d : D) b,
      Lf p ≠ a ++ LEv.recv q k j' d :: b := by
    intro p a q k j' d b h
    have hm : LEv.recv q k j' d ∈ Lf p := by rw [h]; simp
    exact (hLs p).2.1 q k j' d hm
  have hwfc : WF init Lf :=
    ⟨fun p => (hLs p).1, fun p a q k j' d b h => absurd h (hnrecv p a q k j' d b)⟩
  have hprodc : Produced Sys N init Lf := fun p => (hLs p).2.2.1
  have hpartc : Partitioned Lf comp :=
    ⟨hcomp2, fun p a q k j' d b h => absurd h (hnrecv p a q k j' d b)⟩
  have hjall : ∀ p σ, LRun (canon sp (init p)) (Lf p) σ → σ.cur ≼ j := by
    intro p σ h
    rw [lrun_noinp h (hLs p).2.2.2.1]
    show init p ≼ j
    simp only [init]
    split
    · exact hj _ (List.getElem_mem ..)
    · exact PO.refl j
  obtain ⟨u, hu, hall⟩ := hC N init Lf comp hwfc hprodc hpartc j hjall
  refine ⟨u, hu, fun r hr => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  obtain ⟨γ, hγ⟩ := (hLs ⟨i, by omega⟩).2.2.2.2 hi
  exact hall _ γ _ hγ

/-! ## Sufficiency -/

/-- (⇐): if `S` is consistent on `A`, the canonical system `respSystem A`
keeps `A` available. -/
theorem availabilityFor_resp (A : Table I O) :
    AvailabilityFor A (respSystem (sp := sp) (D := D) A) := by
  intro N init H comp hwf hprod hpart p σ hσ o hR hAo
  classical
  let c : Fin N → Nat := fun q => (H q).length
  have hcut : IsCut H c := isCut_full hwf
  have hσ' : LRun (canon sp (init p)) ((H p).take (c p)) σ := by
    simp only [c, List.take_length]; exact hσ
  obtain ⟨h1, h2, _, _⟩ := rinv_of_produced A (compliant_take (hprod p) (c p)) hσ'
  have hge : ∀ o' ∈ emittedOf (((H p).take (c p)).map LEv.erase), o' ≼ o :=
    ((h2 _ _).1 hR).2.2
  obtain ⟨γ, σc, hγ, ha, hco, hexp⟩ := kc_legal hR
  let τ : State sp :=
    { cur := σc.cur, R := outputTable σc o, sub := fun k x h => σc.sub k x h.1,
      hasCur := ⟨o, hco, PO.refl o⟩, above := fun k x h => σc.above k x h.1 }
  have hstep : Step σc (.output o) τ := Step.output σc τ o hco rfl rfl
  obtain ⟨H', ext, hext, hwf', hprod', hpart', hp, hq⟩ :=
    extend_single (respSystem A) hwf hprod hpart hcut hσ' (e := .out γ o)
      (by intro q k j d h; cases h) (.out ha hstep hexp (.nil τ))
      ⟨by intro c' hc'; rcases hγ with rfl | rfl
          · cases hc'
          · simp at hc'; exact ⟨o, hc'⟩,
       hγ, by rw [← h1]; exact hAo, hge⟩
  have hH' : H' = fun q => H q ++ ext q := by
    funext q; rw [hext q]; simp [c]
  subst hH'
  refine ⟨ext, hwf', hprod', hpart', fun q hq' => hq q (fun h => hq' (h ▸ rfl)), ?_, γ, ?_⟩
  · intro q j
    by_cases hqp : q = p
    · subst hqp; rw [hp]; simp
    · rw [hq q hqp]; simp
  · rw [hp]; simp

/-- (⇐): if `S` is consistent on `A`, `respSystem A` has Partition
Consistency: its emitted outputs are rows of `A`, so they have a common
refinement, and for a canonical system that is confluence. -/
theorem pc_resp (A : Table I O) (hcons : ConsistentOn sp A) :
    PartitionConsistencyAtEnd (respSystem (sp := sp) (D := D) A) := by
  apply (partitionConsistency_iff_atEnd _).1
  intro N init H comp hwf hprod _ c hcut j hj
  apply (canonical_rpc_iff_confluent (respSystem_canonical A) hwf hprod hcut hj).1
  let L : List O := (List.finRange N).flatMap
    (fun p => emittedOf (((H p).take (c p)).map LEv.erase))
  obtain ⟨u, hu, hall⟩ := consistentOn_outs hcons (j := j) L (by
    intro o ho
    simp only [L, List.mem_flatMap] at ho
    obtain ⟨p, _, ho⟩ := ho
    obtain ⟨τp, hp⟩ := hwf.1 p
    obtain ⟨σ, hσ⟩ := lrun_take hp (c p)
    obtain ⟨_, _, h3, _⟩ := rinv_of_produced A (compliant_take (hprod p) (c p)) hσ
    obtain ⟨i, hi, hle⟩ := h3 o ho
    exact ⟨i, hi, PO.trans hle (hj p σ hσ)⟩)
  refine ⟨u, hu, fun p γ o hm => hall o ?_⟩
  simp only [L, List.mem_flatMap]
  exact ⟨p, List.mem_finRange p, mem_emittedOf hm⟩

/-! ## The theorem -/

/-- **Complete CAP for an availability relation.**  For `A ⊆ S`: some system
has Availability for `A` and Partition Consistency iff `S` is consistent on
`A`.  The forward direction needs only a common refinement of the emitted
outputs, for any system. -/
theorem complete_cap_for (sp : Spec I O) (D : Type) (A : Table I O)
    (hAS : ∀ i o, A i o → sp.S i o) :
    (∃ Sys : System sp D, AvailabilityFor A Sys ∧ PartitionConsistencyAtEnd Sys) ↔
      ConsistentOn sp A :=
  ⟨fun ⟨Sys, hA, hP⟩ => consistentOn_of_availabilityFor A hAS Sys hA (commonRefinement_of_pc hP),
   fun h => ⟨respSystem A, availabilityFor_resp A, pc_resp A h⟩⟩

/-- With `A = S` this is Theorem `thm:complete-cap`. -/
theorem complete_cap_for_S (sp : Spec I O) (D : Type) :
    (∃ Sys : System sp D, AvailabilityFor sp.S Sys ∧ PartitionConsistencyAtEnd Sys) ↔
      sp.LiftedMono := by
  rw [complete_cap_for sp D sp.S (fun _ _ h => h)]
  exact (liftedMono_iff_commonExpansion sp).symm

end CAP
end CC
