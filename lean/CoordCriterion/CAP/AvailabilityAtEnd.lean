import CoordCriterion.CAP.Model

/-!
# Availability at the end of a history

`Availability` (Def. `def:partition-notions`(4)) quantifies over every
consistent cut of every produced partitioned history.  The cuts are redundant:
restricting a produced partitioned history to a consistent cut gives another
produced partitioned history, so it suffices to ask at the end of every such
history.  `availability_iff_atEnd` proves the equivalence.
-/

namespace CC
namespace CAP

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type} {n : Nat}

/-- Availability stated at the end of each produced partitioned history: each
participant `p`, in state `σ = (i,R)` after its whole local history, can emit
each `o ∈ R(i)` in a continuation local to `p`. -/
def AvailabilityAtEnd (Sys : System sp D) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) (H p) σ →
    ∀ o, σ.R σ.cur o →
    ∃ ext : Fin n → List (LEv sp D n),
      WF init (fun q => H q ++ ext q) ∧ Produced Sys n init (fun q => H q ++ ext q) ∧
      Partitioned (fun q => H q ++ ext q) comp ∧
      (∀ q, comp q ≠ comp p → ext q = []) ∧
      (∀ q j, LEv.inp j ∉ ext q) ∧
      ∃ γ, LEv.out γ o ∈ ext p

/-- The history restricted to a cut. -/
def cutHist (H : History sp D n) (c : Fin n → Nat) : History sp D n :=
  fun p => (H p).take (c p)

theorem wf_cutHist {init : Fin n → I} {H : History sp D n} {c : Fin n → Nat}
    (hw : WF init H) (hc : IsCut H c) : WF init (cutHist H c) := by
  refine ⟨fun p => ?_, ?_⟩
  · obtain ⟨τ, hτ⟩ := hw.1 p
    exact lrun_take hτ (c p)
  · intro p a q k j d b h
    have hk := hc.2 p a q k j d b h
    obtain ⟨hne, hs⟩ := hw.2 p a q k j d _ (take_split h)
    refine ⟨hne, ?_⟩
    show ((H q).take (c q))[k]? = _
    rw [List.getElem?_take]; simp [hk, hs]

theorem produced_cutHist {Sys : System sp D} {init : Fin n → I} {H : History sp D n}
    (hp : Produced Sys n init H) (c : Fin n → Nat) : Produced Sys n init (cutHist H c) :=
  fun p => compliant_take (hp p) (c p)

theorem partitioned_cutHist {H : History sp D n} {comp : Fin n → Nat}
    (hp : Partitioned H comp) (c : Fin n → Nat) : Partitioned (cutHist H c) comp :=
  ⟨hp.1, fun p a q k j d _ h => hp.2 p a q k j d _ (take_split h)⟩

theorem isCut_full {init : Fin n → I} {H : History sp D n} (hw : WF init H) :
    IsCut H (fun p => (H p).length) := by
  refine ⟨fun _ => Nat.le_refl _, ?_⟩
  intro p a q k j d b h
  rw [List.take_length] at h
  obtain ⟨_, hs⟩ := hw.2 p a q k j d b h
  exact (List.getElem?_eq_some_iff.1 hs).1

/-- Availability at every consistent cut is the same as Availability at the
end of every history. -/
theorem availability_iff_atEnd (Sys : System sp D) :
    Availability Sys ↔ AvailabilityAtEnd Sys := by
  constructor
  · intro hA n init H comp hw hp hpt p σ hσ o ho
    have hσ' : LRun (canon sp (init p)) ((H p).take (H p).length) σ := by
      rw [List.take_length]; exact hσ
    obtain ⟨H', ext, hext, hw', hp', hpt', hloc, hni, hout⟩ :=
      hA n init H comp hw hp hpt _ (isCut_full hw) p σ hσ' o ho
    have hH' : H' = fun q => H q ++ ext q := by
      funext q; rw [hext q, List.take_length]
    subst hH'
    exact ⟨ext, hw', hp', hpt', hloc, hni, hout⟩
  · intro hE n init H comp hw hp hpt c hc p σ hσ o ho
    obtain ⟨ext, hw', hp', hpt', hloc, hni, hout⟩ :=
      hE n init (cutHist H c) comp (wf_cutHist hw hc) (produced_cutHist hp c)
        (partitioned_cutHist hpt c) p σ hσ o ho
    exact ⟨fun q => cutHist H c q ++ ext q, ext, fun q => rfl, hw', hp', hpt', hloc, hni, hout⟩

/-- Partition Consistency stated at the end of each produced partitioned
history: its final cut is confluent at every common expansion of the
participants' current inputs. -/
def PartitionConsistencyAtEnd (Sys : System sp D) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ j : I, (∀ p σ, LRun (canon sp (init p)) (H p) σ → σ.cur ≼ j) →
    ∃ τ : State sp, τ.cur = j ∧ ∃ ext : Fin n → List (LEv sp D n),
      WF init (fun q => H q ++ ext q) ∧ ∀ p, LRun (canon sp (init p)) (H p ++ ext p) τ

/-- Partition Consistency at every consistent cut is the same as Partition
Consistency at the end of every history. -/
theorem partitionConsistency_iff_atEnd (Sys : System sp D) :
    PartitionConsistency Sys ↔ PartitionConsistencyAtEnd Sys := by
  constructor
  · intro hC n init H comp hw hp hpt j hj
    have hj' : ∀ p σ, LRun (canon sp (init p)) ((H p).take (H p).length) σ → σ.cur ≼ j := by
      intro p σ h; rw [List.take_length] at h; exact hj p σ h
    obtain ⟨H', ext, τ, hext, hw', hτ, hrun⟩ :=
      hC n init H comp hw hp hpt _ (isCut_full hw) j hj'
    have hH' : H' = fun q => H q ++ ext q := by
      funext q; rw [hext q, List.take_length]
    subst hH'
    exact ⟨τ, hτ, ext, hw', hrun⟩
  · intro hE n init H comp hw hp hpt c hc j hj
    obtain ⟨τ, hτ, ext, hw', hrun⟩ :=
      hE n init (cutHist H c) comp (wf_cutHist hw hc) (produced_cutHist hp c)
        (partitioned_cutHist hpt c) j hj
    exact ⟨fun q => cutHist H c q ++ ext q, ext, τ, fun q => rfl, hw', hτ, hrun⟩

end CAP
end CC
