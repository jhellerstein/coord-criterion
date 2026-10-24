import CoordCriterion.CAP.LocalCommitment
import CoordCriterion.CAP.AsyncGilbertLynch

/-!
# Appendix F: the response form as a chosen availability relation

Appendix `app:cap-response` states its definitions at the end of every
partitioned history, as Section `sec:complete-cap` does.  This file proves
that these end-of-history forms agree with the cut forms of
`CAP/ResponseForm.lean` and `CAP/ResponseAvailability.lean`, and proves the
facts that connect the response form with Theorem `thm:complete-cap`:

* Response Partition Consistency, at the end of histories, is exactly the
  common-refinement condition `CommonRefinementAtEnd` that the converse of
  Theorem `thm:complete-cap` uses (`responsePC_iff_commonRefinement`), and
  Theorem `thm:complete-cap` holds with it in place of Partition Consistency
  (`complete_cap_for_rpc`);
* in the system of the proof of Theorem `thm:complete-cap` for a response
  interface `T`, every participant's fiber meets `T` (`resp_fiber_meets`), so
  its Availability for `T` gives Answering (`respSystem_answering`);
* the response form is Theorem `thm:complete-cap` applied to a chosen
  availability relation (`response_form_iff_chosen`);
* Lemma `lem:forced-answer` and Corollary `cor:gilbert-lynch` at the end of
  histories (`forced_answer_end`, `gilbert_lynch_client_end`).
-/

namespace CC
namespace CAP

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type}

/-! ## Continuations within a component, at the end of histories -/

/-- Def. `def:response-availability`, at the end of histories.  Both
continuations are produced, partitioned by the same components, and add only
events of `p`'s component; Answering adds no input event at `p`. -/
def ResponseAvailabilityEnd (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) (H p) σ →
      (∃ ext : Fin n → List (LEv sp D n),
        WF init (fun q => H q ++ ext q) ∧ Produced Sys n init (fun q => H q ++ ext q) ∧
        Partitioned (fun q => H q ++ ext q) comp ∧
        (∀ q, comp q ≠ comp p → ext q = []) ∧ (∀ j, LEv.inp j ∉ ext p) ∧
        ∃ γ o, Q n p σ.cur o ∧ LEv.out γ o ∈ ext p) ∧
      (∀ j, σ.cur ≼ j → ∃ ext : Fin n → List (LEv sp D n),
        WF init (fun q => H q ++ ext q) ∧ Produced Sys n init (fun q => H q ++ ext q) ∧
        Partitioned (fun q => H q ++ ext q) comp ∧
        (∀ q, comp q ≠ comp p → ext q = []) ∧ LEv.inp j ∈ ext p)

/-- The Answering clause alone, at the end of histories. -/
def AnsweringEnd (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) (H p) σ →
      ∃ ext : Fin n → List (LEv sp D n),
        WF init (fun q => H q ++ ext q) ∧ Produced Sys n init (fun q => H q ++ ext q) ∧
        Partitioned (fun q => H q ++ ext q) comp ∧
        (∀ q, comp q ≠ comp p → ext q = []) ∧ (∀ j, LEv.inp j ∉ ext p) ∧
        ∃ γ o, Q n p σ.cur o ∧ LEv.out γ o ∈ ext p

theorem lrun_full {init : I} {L : List (LEv sp D n)} {σ : State sp} :
    LRun (canon sp init) (L.take L.length) σ ↔ LRun (canon sp init) L σ := by
  rw [List.take_length]

theorem hist_of_extends {H H' : History sp D n} {ext : Fin n → List (LEv sp D n)}
    (h : Extends H (fun p => (H p).length) H' ext) : H' = fun q => H q ++ ext q := by
  funext q; rw [h q, List.take_length]

theorem responseAvailability_iff_end (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O) :
    ResponseAvailability Sys Q ↔ ResponseAvailabilityEnd Sys Q := by
  constructor
  · intro h n init H comp hw hp hpt p σ hσ
    obtain ⟨hAns, hAcc⟩ := h n init H comp hw hp hpt _ (isCut_full hw) p σ (lrun_full.2 hσ)
    refine ⟨?_, fun j hj => ?_⟩
    · obtain ⟨H', ext, hext, hw', hp', hpt', hloc, hni, hout⟩ := hAns
      have := hist_of_extends hext; subst this
      exact ⟨ext, hw', hp', hpt', hloc, hni, hout⟩
    · obtain ⟨H', ext, hext, hw', hp', hpt', hloc, hin⟩ := hAcc j hj
      have := hist_of_extends hext; subst this
      exact ⟨ext, hw', hp', hpt', hloc, hin⟩
  · intro h n init H comp hw hp hpt c hc p σ hσ
    obtain ⟨hAns, hAcc⟩ := h n init (cutHist H c) comp (wf_cutHist hw hc) (produced_cutHist hp c)
      (partitioned_cutHist hpt c) p σ hσ
    refine ⟨?_, fun j hj => ?_⟩
    · obtain ⟨ext, hw', hp', hpt', hloc, hni, hout⟩ := hAns
      exact ⟨fun q => cutHist H c q ++ ext q, ext, fun q => rfl, hw', hp', hpt', hloc, hni, hout⟩
    · obtain ⟨ext, hw', hp', hpt', hloc, hin⟩ := hAcc j hj
      exact ⟨fun q => cutHist H c q ++ ext q, ext, fun q => rfl, hw', hp', hpt', hloc, hin⟩

theorem answering_iff_end (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O) :
    Answering Sys Q ↔ AnsweringEnd Sys Q := by
  constructor
  · intro h n init H comp hw hp hpt p σ hσ
    obtain ⟨H', ext, hext, hw', hp', hpt', hloc, hni, hout⟩ :=
      h n init H comp hw hp hpt _ (isCut_full hw) p σ (lrun_full.2 hσ)
    have := hist_of_extends hext; subst this
    exact ⟨ext, hw', hp', hpt', hloc, hni, hout⟩
  · intro h n init H comp hw hp hpt c hc p σ hσ
    obtain ⟨ext, hw', hp', hpt', hloc, hni, hout⟩ := h n init (cutHist H c) comp
      (wf_cutHist hw hc) (produced_cutHist hp c) (partitioned_cutHist hpt c) p σ hσ
    exact ⟨fun q => cutHist H c q ++ ext q, ext, fun q => rfl, hw', hp', hpt', hloc, hni, hout⟩

/-! ## Response Partition Consistency is the common-refinement condition -/

/-- Def. `def:response-partition-consistency`, at the end of histories, is
`CommonRefinementAtEnd`: the condition the converse of Theorem
`thm:complete-cap` uses. -/
theorem responsePC_iff_commonRefinement (Sys : System sp D) :
    ResponsePC Sys ↔ CommonRefinementAtEnd Sys := by
  constructor
  · intro h n init H comp hw hp hpt j hj
    obtain ⟨u, hu, hall⟩ := h n init H comp hw hp hpt _ (isCut_full hw) j
      (fun p σ hσ => hj p σ (lrun_full.1 hσ))
    exact ⟨u, hu, fun p γ o hm => hall p γ o (by rw [List.take_length]; exact hm)⟩
  · intro h n init H comp hw hp hpt c hc j hj
    obtain ⟨u, hu, hall⟩ := h n init (cutHist H c) comp (wf_cutHist hw hc)
      (produced_cutHist hp c) (partitioned_cutHist hpt c) j hj
    exact ⟨u, hu, fun p γ o hm => hall p γ o hm⟩

/-- Theorem `thm:complete-cap` with Response Partition Consistency in place of
Partition Consistency. -/
theorem complete_cap_for_rpc (sp : Spec I O) (D : Type) (A : Table I O)
    (hAS : ∀ i o, A i o → sp.S i o) :
    (∃ Sys : System sp D, AvailabilityFor A Sys ∧ CommonRefinementAtEnd Sys) ↔
      ConsistentOn sp A :=
  ⟨fun ⟨Sys, hA, hC⟩ => consistentOn_of_availabilityFor A hAS Sys hA hC,
   fun h => ⟨respSystem A, availabilityFor_resp A, commonRefinement_of_pc (pc_resp A h)⟩⟩

/-! ## A response interface as an availability relation -/

/-- In the system of the proof of Theorem `thm:complete-cap` for a total,
self-continuing `T ⊆ S`, every participant's current fiber meets `T`: some
output of `T` at the current input refines everything the participant has
emitted. -/
theorem resp_fiber_meets (T : Table I O) (hTS : ∀ i o, T i o → sp.S i o)
    (hTtot : ∀ i, ∃ o, T i o) (hTcont : ∀ i o j, T i o → i ≼ j → ∃ u, T j u ∧ o ≼ u)
    {n : Nat} {init : Fin n → I} {H : History sp D n}
    (hp : Produced (respSystem (sp := sp) (D := D) T) n init H) {p : Fin n} {σ : State sp}
    (hσ : LRun (canon sp (init p)) (H p) σ) : ∃ o, σ.R σ.cur o ∧ T σ.cur o := by
  obtain ⟨_, h2, _, h4⟩ := rinv_of_produced T (hp p) hσ
  have : ∃ u, T σ.cur u ∧ ∀ o ∈ emittedOf ((H p).map LEv.erase), o ≼ u := by
    rcases h4 with h4 | ⟨i, om, hom, hi, hall⟩
    · obtain ⟨u, hu⟩ := hTtot σ.cur; exact ⟨u, hu, by rw [h4]; simp⟩
    · obtain ⟨u, hu, hle⟩ := hTcont i om σ.cur hom hi
      exact ⟨u, hu, fun o ho => PO.trans (hall o ho) hle⟩
  obtain ⟨u, hu, hge⟩ := this
  exact ⟨u, (h2 _ _).2 ⟨hTS _ _ hu, PO.refl _, hge⟩, hu⟩

/-- If every participant's fiber meets `T ⊆ Q` at the end of every produced
history, Availability for `T` gives Answering for `Q`. -/
theorem answeringEnd_of_availabilityFor {T : Table I O} {Q : Table I O}
    (hTQ : ∀ i o, T i o → Q i o) {Sys : System sp D} (hA : AvailabilityFor T Sys)
    (hmeet : ∀ (n : Nat) (init : Fin n → I) (H : History sp D n), WF init H →
      Produced Sys n init H → ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) (H p) σ →
      ∃ o, σ.R σ.cur o ∧ T σ.cur o) :
    AnsweringEnd Sys (fun _ _ => Q) := by
  intro n init H comp hw hp hpt p σ hσ
  obtain ⟨o, hR, hT⟩ := hmeet n init H hw hp p σ hσ
  obtain ⟨ext, hw', hp', hpt', hloc, hni, γ, hγ⟩ := hA n init H comp hw hp hpt p σ hσ o hR hT
  exact ⟨ext, hw', hp', hpt', hloc, fun j => hni p j, γ, o, hTQ _ _ hT, hγ⟩

/-- For a response interface `T`, the system of the proof of Theorem
`thm:complete-cap` for `A = T` has Answering: totality and self-continuation
turn its Availability for `T` into Answering. -/
theorem respSystem_answering (Q : Obligation sp) (T : Table I O) (hT : ResponseInterface Q T) :
    AnsweringEnd (respSystem (sp := sp) (D := D) T) (fun _ _ => Q.Q) := by
  obtain ⟨hTQ, hTtot, hTcont⟩ := hT
  exact answeringEnd_of_availabilityFor hTQ (availabilityFor_resp T)
    (fun _ _ _ _ hp _ _ hσ => resp_fiber_meets T (fun i o h => Q.sub i o (hTQ i o h))
      hTtot hTcont hp hσ)


/-- The system of the proof of Theorem `thm:complete-cap` for a response
interface `T` has Response Availability; no consistency on `T` is needed. -/
theorem respSystem_RA (Q : Obligation sp) (T : Table I O) (hT : ResponseInterface Q T) :
    ResponseAvailability (respSystem (sp := sp) (D := D) T) (fun _ _ => Q.Q) := by
  obtain ⟨hTQ, hTtot, hTcont⟩ := hT
  intro N init H comp hwf hprod hpart c hcut p σ hσ
  obtain ⟨h1, h2, _, h4⟩ := rinv_of_produced T (compliant_take (hprod p) (c p)) hσ
  have havail : ∀ k, σ.cur ≼ k → ∃ u, T k u ∧
      ∀ o ∈ emittedOf (((H p).take (c p)).map LEv.erase), o ≼ u := by
    intro k hk
    rcases h4 with h4 | ⟨i, om, hom, hi, hall⟩
    · obtain ⟨u, hu⟩ := hTtot k; exact ⟨u, hu, by rw [h4]; simp⟩
    · obtain ⟨u, hu, hle⟩ := hTcont i om k hom (PO.trans hi hk)
      exact ⟨u, hu, fun o ho => PO.trans (hall o ho) hle⟩
  constructor
  · obtain ⟨u, hu, hge⟩ := havail σ.cur (PO.refl _)
    have hRu : σ.R σ.cur u :=
      (h2 _ _).2 ⟨Q.sub _ _ (hTQ _ _ hu), PO.refl _, hge⟩
    obtain ⟨γ, σc, hγ, ha, hcu, hexp⟩ := kc_legal hRu
    let τ : State sp :=
      { cur := σc.cur, R := outputTable σc u, sub := fun k x h => σc.sub k x h.1,
        hasCur := ⟨u, hcu, PO.refl u⟩, above := fun k x h => σc.above k x h.1 }
    have hstep : Step σc (.output u) τ := Step.output σc τ u hcu rfl rfl
    obtain ⟨H', ext, hext, hwf', hprod', hpart', hp, hq⟩ :=
      extend_single (respSystem T) hwf hprod hpart hcut hσ (e := .out γ u)
        (by intro q k j d h; cases h) (.out ha hstep hexp (.nil τ))
        ⟨by intro c' hc'; rcases hγ with rfl | rfl
            · cases hc'
            · simp at hc'; exact ⟨u, hc'⟩,
         hγ, by rw [← h1]; exact hu, hge⟩
    refine ⟨H', ext, hext, hwf', hprod', hpart', fun q hq' => hq q (fun h => hq' (h ▸ rfl)),
      by rw [hp]; simp, γ, u, hTQ _ _ hu, by rw [hp]; simp⟩
  · intro j hj
    obtain ⟨w, hw, hge⟩ := havail j hj
    have hRw : σ.R j w := (h2 _ _).2 ⟨Q.sub _ _ (hTQ _ _ hw), hj, hge⟩
    let τ : State sp :=
      { cur := j, R := inputTable σ j, sub := fun k x h => σ.sub k x h.1,
        hasCur := ⟨w, hRw, PO.refl j⟩, above := fun k x h => h.2 }
    have hstep : Step σ (.input j) τ := Step.input σ τ j ⟨w, hRw⟩ rfl rfl
    obtain ⟨H', ext, hext, hwf', hprod', hpart', hp, hq⟩ :=
      extend_single (respSystem T) hwf hprod hpart hcut hσ (e := .inp j)
        (by intro q k j d h; cases h) (.inp hstep (.nil τ)) trivial
    exact ⟨H', ext, hext, hwf', hprod', hpart', fun q hq' => hq q (fun h => hq' (h ▸ rfl)),
      by rw [hp]; simp⟩

/-- The response form is Theorem `thm:complete-cap` applied to a chosen
availability relation: `S` is consistent on some response interface iff some
response interface `T` admits a system with Availability for `T` and
Partition Consistency. -/
theorem response_form_iff_chosen (sp : Spec I O) (D : Type) (Q : Obligation sp) :
    (∃ T, ResponseInterface Q T ∧ ConsistentOn sp T) ↔
      ∃ T, ResponseInterface Q T ∧
        ∃ Sys : System sp D, AvailabilityFor T Sys ∧ PartitionConsistencyAtEnd Sys := by
  constructor
  · rintro ⟨T, hT, hc⟩
    exact ⟨T, hT, (complete_cap_for sp D T (fun i o h => Q.sub i o (hT.1 i o h))).2 hc⟩
  · rintro ⟨T, hT, hs⟩
    exact ⟨T, hT, (complete_cap_for sp D T (fun i o h => Q.sub i o (hT.1 i o h))).1 hs⟩


/-! ## The response form, at the end of histories -/

/-- Item (1) of Theorem `thm:complete-cap-response`, at the end of histories. -/
def ResponseForm (sp : Spec I O) (D : Type) (Q : Obligation sp) : Prop :=
  ∃ Sys : System sp D, Sys.Replicated ∧ ResponseAvailabilityEnd Sys (fun _ _ => Q.Q) ∧
    CommonRefinementAtEnd Sys

theorem responseForm_iff_cuts (sp : Spec I O) (D : Type) (Q : Obligation sp) :
    ResponseForm sp D Q ↔
      ∃ Sys : System sp D, Sys.Replicated ∧ ResponseAvailability Sys (fun _ _ => Q.Q) ∧
        ResponsePC Sys := by
  constructor
  · rintro ⟨Sys, h1, h2, h3⟩
    exact ⟨Sys, h1, (responseAvailability_iff_end _ _).2 h2,
      (responsePC_iff_commonRefinement _).2 h3⟩
  · rintro ⟨Sys, h1, h2, h3⟩
    exact ⟨Sys, h1, (responseAvailability_iff_end _ _).1 h2,
      (responsePC_iff_commonRefinement _).1 h3⟩

/-- Theorem `thm:complete-cap-response`, (1) ⇔ (2), at the end of histories. -/
theorem complete_cap_response_end (sp : Spec I O) (D : Type) (Q : Obligation sp) :
    ResponseForm sp D Q ↔ ∃ T, ResponseInterface Q T ∧ ConsistentOn sp T :=
  (responseForm_iff_cuts sp D Q).trans (complete_cap_response sp D Q)

/-! ## Lemma `lem:forced-answer` at the end of histories -/

/-- Lemma `lem:forced-answer`, at the end of histories. -/
theorem forced_answer_end (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O)
    (hAns : AnsweringEnd Sys Q) {n : Nat} {init : Fin n → I} {H : History sp D n}
    {comp : Fin n → Nat} (hwf : WF init H) (hprod : Produced Sys n init H)
    (hpart : Partitioned H comp) {q : Fin n}
    (halone : ∀ p, comp p = comp q → p = q) {σq : State sp}
    (hσq : LRun (canon sp (init q)) (H q) σq) {j : I}
    (hj : ∀ p σ, LRun (canon sp (init p)) (H p) σ → σ.cur ≼ j)
    (hno : ∀ o, Q n q σq.cur o → ¬ ∃ u, sp.S j u ∧ o ≼ u) :
    ∃ ext : Fin n → List (LEv sp D n),
      WF init (fun p => H p ++ ext p) ∧ Produced Sys n init (fun p => H p ++ ext p) ∧
      Partitioned (fun p => H p ++ ext p) comp ∧
      (∀ p, p ≠ q → ext p = []) ∧ (∀ p j, LEv.inp j ∉ ext p) ∧
      (∀ p σ, LRun (canon sp (init p)) (H p ++ ext p) σ → σ.cur ≼ j) ∧
      ¬ ∃ u, sp.S j u ∧ ∀ p γ o, LEv.out γ o ∈ H p ++ ext p → o ≼ u := by
  obtain ⟨H', ext, hext, hwf', hprod', hpart', hoth, hni, _, hj', hno'⟩ :=
    forced_answer Sys Q ((answering_iff_end Sys Q).2 hAns) hwf hprod hpart (isCut_full hwf)
      halone (lrun_full.2 hσq) (fun p σ h => hj p σ (lrun_full.1 h)) hno
  have := hist_of_extends hext; subst this
  refine ⟨ext, hwf', hprod', hpart', hoth, hni, fun p σ h => hj' p σ (lrun_full.2 h), ?_⟩
  rintro ⟨u, hu, hall⟩
  exact hno' ⟨u, hu, fun p γ o hm => hall p γ o (by rw [List.take_length] at hm; exact hm)⟩

end CAP

/-! ## Corollary `cor:gilbert-lynch` at the end of client histories -/

namespace AsyncGL

open CC.CAP CC.GL

/-- Answering for the register's obligation, required at the end of client
histories of two participants. -/
def AnsweringCEnd {D : Type} (Sys : System regSpec D) : Prop :=
  ∀ (H : RHist D 2) (comp : Fin 2 → Nat), WF init0 H → Produced Sys 2 init0 H →
    Partitioned H comp → ClientH H →
    ∀ (p : Fin 2) (σ : State regSpec), LRun (canon regSpec (init0 p)) (H p) σ →
      ∃ ext : Fin 2 → List (LEv regSpec D 2),
        WF init0 (fun q => H q ++ ext q) ∧ Produced Sys 2 init0 (fun q => H q ++ ext q) ∧
        Partitioned (fun q => H q ++ ext q) comp ∧
        (∀ q, comp q ≠ comp p → ext q = []) ∧ (∀ j, LEv.inp j ∉ ext p) ∧
        ∃ γ o, regQ p.val σ.cur o ∧ LEv.out γ o ∈ ext p

/-- A cut of a client history is a client history, so Answering at the end of
client histories gives it at their cuts. -/
theorem answeringC_of_end {D : Type} {Sys : System regSpec D} (h : AnsweringCEnd Sys) :
    AnsweringC Sys := by
  intro H comp hw hp hpt hcl c hc p σ hσ
  obtain ⟨ext, hw', hp', hpt', hloc, hni, hout⟩ := h (cutHist H c) comp (wf_cutHist hw hc)
    (produced_cutHist hp c) (partitioned_cutHist hpt c) (fun q => clientLocal_take (hcl q) (c q))
    p σ hσ
  exact ⟨fun q => cutHist H c q ++ ext q, ext, fun q => rfl, hw', hp', hpt', hloc, hni, hout⟩


/-- Answering at the end of client histories is Answering at their cuts. -/
theorem answeringC_iff_end {D : Type} (Sys : System regSpec D) :
    AnsweringC Sys ↔ AnsweringCEnd Sys := by
  refine ⟨fun h H comp hw hp hpt hcl p σ hσ => ?_, answeringC_of_end⟩
  obtain ⟨H', ext, hext, hw', hp', hpt', hloc, hni, hout⟩ :=
    h H comp hw hp hpt hcl _ (isCut_full hw) p σ (by rw [List.take_length]; exact hσ)
  have := hist_of_extends hext; subst this
  exact ⟨ext, hw', hp', hpt', hloc, hni, hout⟩

/-- Response Availability for the register's obligation gives Answering at the
end of client histories. -/
theorem answeringCEnd_of_RAEnd {D : Type} {Sys : System regSpec D}
    (h : ResponseAvailabilityEnd Sys regQn) : AnsweringCEnd Sys :=
  fun H comp hw hp hpt _ p σ hσ => (h 2 init0 H comp hw hp hpt p σ hσ).1

/-- **Corollary `cor:gilbert-lynch`**, with Answering at the end of client
histories. -/
theorem gilbert_lynch_client_end {D : Type} (Sys : System regSpec D) :
    ¬ (AnsweringCEnd Sys ∧ RealizedRPCC Sys) :=
  fun ⟨hA, hR⟩ => gilbert_lynch_client Sys ⟨answeringC_of_end hA, hR⟩

end AsyncGL
end CC
