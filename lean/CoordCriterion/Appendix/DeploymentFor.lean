import CoordCriterion.Appendix.Deployment
import CoordCriterion.CAP.Coordination

/-!
# Appendix E: a deployment as one availability relation per participant

Appendix `app:deployment` reads a deployment `(A_p)` as Theorem
`thm:complete-cap`'s availability relation, chosen per participant.  This file
proves the facts that connect the two:

* Deployment Availability at the end of histories agrees with the cut form of
  `Appendix/Deployment.lean` (`deploymentAvailability_iff_end`);
* for the uniform deployment `A_p = A`, Deployment Availability is
  Availability for `A` over the deployment's participant set
  (`deploymentAvailability_uniform`);
* consistency on any relation containing every `A_p` implies monotonicity
  across partitions (`monoAcrossPartitions_of_consistentOn`); in particular
  consistency on `A` does for the uniform deployment, and Lifted Monotonicity
  does for every deployment;
* when only one participant may emit, no choice is distributed coordination
  (`sole_emitter_choices`).
-/

namespace CC
namespace Deploy

open CC.CAP

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {n : Nat} {D : Type}

/-- Def. `def:deployment-availability`, at the end of histories over `Fin n`. -/
def DeploymentAvailabilityEnd (Sys : System sp D) (Dp : Deployment sp n) : Prop :=
  ∀ (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) (H p) σ →
    ∀ o, σ.R σ.cur o → Dp.A p σ.cur o →
    ∃ ext : Fin n → List (LEv sp D n),
      WF init (fun q => H q ++ ext q) ∧ Produced Sys n init (fun q => H q ++ ext q) ∧
      Partitioned (fun q => H q ++ ext q) comp ∧
      (∀ q, comp q ≠ comp p → ext q = []) ∧
      (∀ q j, LEv.inp j ∉ ext q) ∧
      ∃ γ, LEv.out γ o ∈ ext p

theorem deploymentAvailability_iff_end (Sys : System sp D) (Dp : Deployment sp n) :
    DeploymentAvailability Sys Dp ↔ DeploymentAvailabilityEnd Sys Dp := by
  constructor
  · intro h init H comp hw hp hpt p σ hσ o ho hA
    have hσ' : LRun (canon sp (init p)) ((H p).take (H p).length) σ := by
      rw [List.take_length]; exact hσ
    obtain ⟨H', ext, hext, hw', hp', hpt', hloc, hni, hout⟩ :=
      h init H comp hw hp hpt _ (isCut_full hw) p σ hσ' o ho hA
    have hH' : H' = fun q => H q ++ ext q := by funext q; rw [hext q, List.take_length]
    subst hH'
    exact ⟨ext, hw', hp', hpt', hloc, hni, hout⟩
  · intro h init H comp hw hp hpt c hc p σ hσ o ho hA
    obtain ⟨ext, hw', hp', hpt', hloc, hni, hout⟩ := h init (cutHist H c) comp
      (wf_cutHist hw hc) (produced_cutHist hp c) (partitioned_cutHist hpt c) p σ hσ o ho hA
    exact ⟨fun q => cutHist H c q ++ ext q, ext, fun q => rfl, hw', hp', hpt', hloc, hni, hout⟩

/-- The uniform deployment: every participant may emit the rows of `A`. -/
def Deployment.uniform (A : Table I O) (hAS : ∀ i o, A i o → sp.S i o) : Deployment sp n where
  A := fun _ => A
  sub := fun _ => hAS

/-- Availability for `A` (Section `sec:complete-cap`) restricted to histories
over `Fin n`; `AvailabilityFor A` is `∀ n, AvailabilityForAt A · n`. -/
def AvailabilityForAt (A : Table I O) (Sys : System sp D) (n : Nat) : Prop :=
  ∀ (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) (H p) σ →
    ∀ o, σ.R σ.cur o → A σ.cur o →
    ∃ ext : Fin n → List (LEv sp D n),
      WF init (fun q => H q ++ ext q) ∧ Produced Sys n init (fun q => H q ++ ext q) ∧
      Partitioned (fun q => H q ++ ext q) comp ∧
      (∀ q, comp q ≠ comp p → ext q = []) ∧
      (∀ q j, LEv.inp j ∉ ext q) ∧
      ∃ γ, LEv.out γ o ∈ ext p

theorem availabilityFor_iff_at (A : Table I O) (Sys : System sp D) :
    AvailabilityFor A Sys ↔ ∀ n, AvailabilityForAt A Sys n := Iff.rfl

/-- For the uniform deployment `A_p = A`, Deployment Availability is
Availability for `A` over the deployment's participant set. -/
theorem deploymentAvailability_uniform (Sys : System sp D) (A : Table I O)
    (hAS : ∀ i o, A i o → sp.S i o) :
    DeploymentAvailabilityEnd Sys (Deployment.uniform (n := n) A hAS) ↔
      AvailabilityForAt A Sys n := Iff.rfl

/-- Consistency on any relation `B` containing every `A_p` implies
monotonicity across partitions. -/
theorem monoAcrossPartitions_of_consistentOn (Dp : Deployment sp n) (B : Table I O)
    (hB : ∀ p i o, Dp.A p i o → B i o) (hc : ConsistentOn sp B) :
    MonoAcrossPartitions Dp := by
  intro comp _ F hauth _ j hj
  obtain ⟨u, hu, hall⟩ := hc (allRows F)
    (by
      intro r hr
      obtain ⟨p, he⟩ := (mem_allRows F r).1 hr
      exact hB p r.1 r.2 (hauth p r he)) j
    (by
      intro r hr
      obtain ⟨p, m, hm, hr⟩ := (mem_allRows F r).1 hr
      exact PO.trans (m.rows_spec.2 r hr).2 (hj p m hm))
  exact ⟨u, hu, fun p r he => hall r ((mem_allRows F r).2 ⟨p, he⟩)⟩

/-- For the uniform deployment, consistency on `A` implies monotonicity across
partitions. -/
theorem monoAcrossPartitions_uniform (A : Table I O) (hAS : ∀ i o, A i o → sp.S i o)
    (hc : ConsistentOn sp A) : MonoAcrossPartitions (Deployment.uniform (n := n) A hAS) :=
  monoAcrossPartitions_of_consistentOn _ A (fun _ _ _ h => h) hc

/-! ## Single authority: choices are not distributed coordination -/

/-- The choice clause of `System.CoordinationFreeH`: no row removed by an
output event is emitted, at the same input, by another participant of the
same history. -/
def ChoicesNotDistributed (Sys : System sp D) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n), WF init H → Produced Sys n init H →
    ∀ (p : Fin n) (a b : List (LEv sp D n)) (γ : List (Commitment sp)) (o : O)
      (σ σc : State sp),
      H p = a ++ LEv.out γ o :: b → LRun (canon sp (init p)) a σ → applySeq σ γ = some σc →
      ∀ k x, σ.R k x → ¬ σc.R k x →
        ¬ ∃ (q : Fin n) (a' b' : List (LEv sp D n)) (γ' : List (Commitment sp)) (σ' : State sp),
          q ≠ p ∧ H q = a' ++ LEv.out γ' x :: b' ∧ LRun (canon sp (init q)) a' σ' ∧ σ'.cur = k

/-- If only one participant (index `0`) may perform output events, no choice
is distributed coordination. -/
theorem sole_emitter_choices (Sys : System sp D)
    (hsole : ∀ n init (p : Fin n) pre γ o, Sys.strat n init p pre (LEv.out γ o) → p.val = 0) :
    ChoicesNotDistributed Sys := by
  intro n init H _ hp p a b γ o σ σc hH _ _ k x _ _
  rintro ⟨q, a', b', γ', σ', hqp, hq, _, _⟩
  have h1 := hsole n init p a γ o (hp p a _ b hH).2
  have h2 := hsole n init q a' γ' x (hp q a' _ b' hq).2
  exact hqp (Fin.ext (h2.trans h1.symm))

/-- `System.CoordinationFreeH` includes the choice clause. -/
theorem choicesNotDistributed_of_H {Sys : System sp D} (h : Sys.CoordinationFreeH) :
    ChoicesNotDistributed Sys :=
  fun n init H hw hp p a b γ o σ σc hH hr ha k x hx hnx =>
    (h n init H hw hp p a b γ o σ σc hH hr ha).1 k x hx hnx

end Deploy
end CC
