import CoordCriterion.Foundations.Core
import CoordCriterion.Foundations.Runs
import CoordCriterion.CAP.ResponseForm
import CoordCriterion.CAP.Register

/-!
# Response availability and the remaining claims of Section 4.5 / Appendix F

Claims of Section `sec:complete-cap` and Appendix `app:cap-response` beyond
the theorems of `CAP/CompleteCAP.lean` and `CAP/ResponseForm.lean`, in the
framework of `CC.CAP` (histories, systems, cuts, `ResponseAvailability`,
`RPCAt`, …).  The Gilbert–Lynch part uses the register of
`CAP/Register.lean`.

Contents (paper item ↦ Lean):

* Partition Consistency with *commitment-free, receive-free* continuations
  for the commitment-free system (strong reading of Def. `def:partition-consistency`,
  where the confluence continuation is a history of Section `sec:histories`):
  `cf_partitionConsistencyCF`, `complete_cap_strong`.
* Remark after Def. `def:response-partition-consistency`:
  confluence ⇒ RPC (`rpc_of_confluent`); for a canonical system they coincide
  (`canonical_rpc_iff_confluent`); with other commitments the converse fails
  (`rpc_not_confluent`).
* "Input acceptance says that `p` never seals an expansion of its current
  input": `input_acceptance_iff`.
* "It excludes specifications whose answers require such a seal, such as the
  election under the equality order": `ra_excludes_forced_seal`,
  `election_eq_no_ra`.
* "if an output permitted at every input answers, every specification is
  available": `trivially_available`.
* Lemma `lem:locality`: `locality_glue`, `locality_transfer`.
* Remark after Def. `def:response-interface`: `consistentOn_S`,
  `consistentOn_iff_confluent`.
* Remark "Without replication": as stated it is false under
  the system assumption after Def. `def:partitioned-history` (`without_replication_counterexample`); it
  holds for a fixed participant set when each strategy depends on the initial
  inputs only through its own (`without_replication`).
* "Relationship to the interface form": `lm_response_interface`,
  `lm_response_form`, `converse_counterexample`, `functional_response_iff`,
  `functional_forms_coincide`, `subspec_lm_interface`,
  `subspec_counterexample`.
* Lemma `lem:forced-answer` (the continuation adds only `q`'s events and no
  input event), from Answering alone: `forced_answer`.
* Corollary `cor:gilbert-lynch`, proved along the paper's route through
  `forced_answer`, from Answering alone: `gilbert_lynch_answering`,
  `gilbert_lynch_via_forced_answer`.
* "a single emitted output has no refinement in the fiber at some expansion of
  its input, a failure of Relational Monotonicity": `reg_not_relMono`; `Q_p`
  is an obligation (`regQ_obligation`).
-/

namespace CC
namespace CAP

open CAP

section General

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type} {n : Nat}

theorem full_cut' {init : Fin n → I} {H : History sp D n} (hwf : WF init H) :
    IsCut H (fun p => (H p).length) := by
  refine ⟨fun _ => Nat.le_refl _, ?_⟩
  intro p a q k j d b h
  rw [List.take_length] at h
  obtain ⟨_, hs⟩ := hwf.2 p a q k j d b h
  exact (List.getElem?_eq_some_iff.1 hs).1

/-! ## Partition Consistency with commitment-free continuations -/

/-- Def. `def:partition-consistency`, strong reading: the confluence
continuation adds only commitment-free output events and no receives (so it is
a history of Section `sec:histories`). -/
def PartitionConsistencyCF (Sys : System sp D) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ c, IsCut H c →
    ∀ j : I, (∀ p σ, LRun (canon sp (init p)) ((H p).take (c p)) σ → σ.cur ≼ j) →
    ∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)) (τ : State sp),
      Extends H c H' ext ∧ WF init H' ∧ τ.cur = j ∧
      (∀ p, LRun (canon sp (init p)) (H' p) τ) ∧
      (∀ p γ o, LEv.out γ o ∈ ext p → γ = []) ∧
      (∀ p q k j d, LEv.recv q k j d ∉ ext p)

theorem partitionConsistency_of_CF {Sys : System sp D} (h : PartitionConsistencyCF Sys) :
    PartitionConsistency Sys := by
  intro n init H comp hwf hprod hpart c hc j hj
  obtain ⟨H', ext, τ, hext, hwf', hτ, hrun, _, _⟩ := h n init H comp hwf hprod hpart c hc j hj
  exact ⟨H', ext, τ, hext, hwf', hτ, hrun⟩

theorem toL_out : ∀ (es : List (Event I O)) (γ : List (Commitment sp)) (o : O),
    LEv.out γ o ∈ toL (sp := sp) (D := D) (n := n) es → γ = []
  | [], _, _, h => by simp [toL] at h
  | .input _ :: es, γ, o, h => by
      simp only [toL, List.mem_cons] at h
      rcases h with h | h
      · cases h
      · exact toL_out es γ o h
  | .output _ :: es, γ, o, h => by
      simp only [toL, List.mem_cons] at h
      rcases h with h | h
      · cases h; rfl
      · exact toL_out es γ o h

/-- (2)⇒(1) of Theorem `thm:complete-cap`, Partition Consistency part, with
commitment-free confluence continuations. -/
theorem cf_partitionConsistencyCF (hlm : sp.LiftedMono) :
    PartitionConsistencyCF (cfSystem sp D) := by
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
      (compliant_cf_cmt (compliant_take (hprod p) (c p)))
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
    ⟨fun p => ⟨_, hrun p⟩, recvMatched_extend hwf.2 hcut hext hnr⟩, rfl, hrun,
    fun p γ o h => toL_out _ γ o h, hnr⟩

/-- Theorem `thm:complete-cap` with the strong reading of Partition
Consistency in direction (2)⇒(1) (and the weak reading as the hypothesis of
(1)⇒(2), which is the stronger statement there). -/
theorem complete_cap_strong (sp : Spec I O) (D : Type) :
    ((∃ Sys : System sp D, Availability Sys ∧ PartitionConsistency Sys) → sp.LiftedMono) ∧
    (sp.LiftedMono → Availability (cfSystem sp D) ∧ PartitionConsistencyCF (cfSystem sp D)) :=
  ⟨fun ⟨Sys, hA, hP⟩ => cap_necessary Sys hA hP,
   fun h => ⟨cf_availability h, cf_partitionConsistencyCF h⟩⟩

/-! ## Confluence and Response Partition Consistency -/

/-- Confluence of a cut at `j` implies Response Partition Consistency at `j`
(Cor. `cor:reconciliation-any-basis` at the distributed level; any
commitments, before and after the cut). -/
theorem rpc_of_confluent {init : Fin n → I} {H : History sp D n} {c : Fin n → Nat} {j : I}
    (h : ConfluentCut init H c j) : RPCAt H c j := by
  obtain ⟨H', ext, τ, hext, _, hτj, hτ⟩ := h
  obtain ⟨u, hu⟩ := τ.hasCur
  rw [hτj] at hu
  refine ⟨u, τ.sub _ _ hu, fun p γ o hm => ?_⟩
  have h1 := hτ p
  rw [hext p] at h1
  obtain ⟨σ, h2, h3⟩ := lrun_append.1 h1
  exact lrun_out_mem h2 hm j u ((lrun_mono h3).2 j u hu)

/-- Every output event of `l` is a canonical event `Out κ_o o` (`κ_o = kc o`)
or `Out ε o`, and `l` has no commit event. -/
def CanonOut (l : List (LEv sp D n)) : Prop :=
  (∀ γ o, LEv.out γ o ∈ l → γ = [] ∨ γ = [kc o]) ∧ ∀ γ, LEv.cmt γ ∉ l

/-- Def. `def:canonical-system`: every output event a strategy allows is a
canonical event, and strategies allow no commit event. -/
def CanonicalSystem (Sys : System sp D) : Prop :=
  (∀ n init p pre γ o, Sys.strat n init p pre (LEv.out γ o) → γ = [] ∨ γ = [kc o]) ∧
  ∀ n init p pre γ, ¬ Sys.strat n init p pre (LEv.cmt γ)

theorem lrun_canon_exec {σ τ : State sp} {l : List (LEv sp D n)} (h : LRun σ l τ)
    (hc : CanonOut l) : ∃ es, Exec σ es τ ∧ ∀ o ∈ outs es, ∃ γ, LEv.out γ o ∈ l := by
  induction h with
  | nil σ => exact ⟨[], .nil σ, by simp [outs]⟩
  | @inp σ τ' ρ j es hs _ ih =>
    obtain ⟨es', hx, hm⟩ := ih ⟨fun γ o h => hc.1 γ o (List.mem_cons_of_mem _ h),
      fun γ h => hc.2 γ (List.mem_cons_of_mem _ h)⟩
    refine ⟨_, .cons hs hx, fun o ho => ?_⟩
    simp only [outs] at ho
    obtain ⟨γ, h⟩ := hm o ho
    exact ⟨γ, List.mem_cons_of_mem _ h⟩
  | @out σ σc τ' ρ γ o es ha hs _ _ ih =>
    obtain ⟨es', hx, hm⟩ := ih ⟨fun γ o h => hc.1 γ o (List.mem_cons_of_mem _ h),
      fun γ h => hc.2 γ (List.mem_cons_of_mem _ h)⟩
    have hst := kc_effect (hc.1 γ o (List.mem_cons_self ..)) ha hs
    refine ⟨_, .cons hst hx, fun o' ho => ?_⟩
    simp only [outs, List.mem_cons] at ho
    rcases ho with rfl | ho
    · exact ⟨γ, List.mem_cons_self ..⟩
    · obtain ⟨γ', h⟩ := hm o' ho; exact ⟨γ', List.mem_cons_of_mem _ h⟩
  | cmt _ _ _ _ => exact absurd (List.mem_cons_self ..) (hc.2 _)
  | @send σ ρ j d es _ ih =>
    obtain ⟨es', hx, hm⟩ := ih ⟨fun γ o h => hc.1 γ o (List.mem_cons_of_mem _ h),
      fun γ h => hc.2 γ (List.mem_cons_of_mem _ h)⟩
    exact ⟨es', hx, fun o ho => by
      obtain ⟨γ, h⟩ := hm o ho; exact ⟨γ, List.mem_cons_of_mem _ h⟩⟩
  | @recv σ ρ q k j d es _ ih =>
    obtain ⟨es', hx, hm⟩ := ih ⟨fun γ o h => hc.1 γ o (List.mem_cons_of_mem _ h),
      fun γ h => hc.2 γ (List.mem_cons_of_mem _ h)⟩
    exact ⟨es', hx, fun o ho => by
      obtain ⟨γ, h⟩ := hm o ho; exact ⟨γ, List.mem_cons_of_mem _ h⟩⟩

/-- A canonical output step is realized by a canonical system event. -/
theorem step_out_lrun {σ τ : State sp} {o : O} (hs : Step σ (.output o) τ) :
    ∃ γ, (γ = [] ∨ γ = [kc o]) ∧ LRun (D := D) (n := n) σ [LEv.out γ o] τ := by
  obtain ⟨ho, hcur, hR⟩ := step_output_inv hs
  obtain ⟨γ, σc, hγ, ha, hco, hexp⟩ := kc_legal ho
  have hcc := (applySeq_spec γ σ σc ha).1
  have hs' : Step σc (.output o) τ := by
    refine Step.output σc τ o hco (hcur.trans hcc.symm) ?_
    rw [hR]
    rcases hγ with rfl | rfl
    · simp [applySeq] at ha; subst ha; rfl
    · obtain ⟨hu, rfl⟩ := kc_apply_some ha
      funext k x; apply propext
      simp only [outputTable, kcState]
      exact ⟨fun h => ⟨⟨h.1, not_rm_of_le h.1 h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  exact ⟨γ, hγ, .out ha hs' hexp (.nil τ)⟩

/-- A canonical execution is realized by canonical system events, with no
receive. -/
theorem exec_lrun_canon {σ τ : State sp} {es : List (Event I O)} (hx : Exec σ es τ) :
    ∃ l : List (LEv sp D n), LRun σ l τ ∧ CanonOut l ∧ (∀ q k j d, LEv.recv q k j d ∉ l) := by
  induction hx with
  | nil σ => exact ⟨[], .nil σ, ⟨fun _ _ h => (by cases h), fun _ h => (by cases h)⟩,
      fun _ _ _ _ h => (by cases h)⟩
  | @cons σ τ' ρ e es hs _ ih =>
    obtain ⟨l, hl, hc, hnr⟩ := ih
    cases e with
    | input j =>
      refine ⟨.inp j :: l, .inp hs hl, ⟨fun γ o h => ?_, fun γ h => ?_⟩, fun q k j' d h => ?_⟩
      · rcases List.mem_cons.1 h with h | h
        · cases h
        · exact hc.1 γ o h
      · rcases List.mem_cons.1 h with h | h
        · cases h
        · exact hc.2 γ h
      · rcases List.mem_cons.1 h with h | h
        · cases h
        · exact hnr q k j' d h
    | output o =>
      obtain ⟨γ, hγ, h1⟩ := step_out_lrun (D := D) (n := n) hs
      refine ⟨.out γ o :: l, lrun_append.2 ⟨τ', h1, hl⟩, ⟨fun γ' o' h => ?_, fun γ' h => ?_⟩,
        fun q k j' d h => ?_⟩
      · rcases List.mem_cons.1 h with h | h
        · cases h; exact hγ
        · exact hc.1 γ' o' h
      · rcases List.mem_cons.1 h with h | h
        · cases h
        · exact hc.2 γ' h
      · rcases List.mem_cons.1 h with h | h
        · cases h
        · exact hnr q k j' d h

/-- For histories whose output events (up to the cut) are canonical,
Response Partition Consistency at `j` implies confluence at `j`, with a
canonical, receive-free continuation (Lemma `lem:reconciliation` applied to
the participant runs). -/
theorem confluent_of_rpc_canonical {init : Fin n → I} {H : History sp D n} {c : Fin n → Nat}
    (hwf : WF init H) (hcut : IsCut H c) (hcan : ∀ p, CanonOut ((H p).take (c p))) {j : I}
    (hj : ∀ p σ, LRun (canon sp (init p)) ((H p).take (c p)) σ → σ.cur ≼ j)
    (hr : RPCAt H c j) : ConfluentCut init H c j := by
  classical
  obtain ⟨u, hju, hu⟩ := hr
  have hX : ∀ p, ∃ x : State sp × List O, LRun (canon sp (init p)) ((H p).take (c p)) x.1 ∧
      Residual x.1 x.2 ∧ x.1.R j u := by
    intro p
    obtain ⟨τp, hp⟩ := hwf.1 p
    obtain ⟨σ, hσ⟩ := lrun_take hp (c p)
    obtain ⟨es, hx, hm⟩ := lrun_canon_exec hσ (hcan p)
    have hres : Residual σ (outs es) := run_residual hx
    refine ⟨(σ, outs es), hσ, hres, (hres j u).2 ⟨hju, hj p σ hσ, fun o ho => ?_⟩⟩
    obtain ⟨γ, hγ⟩ := hm o ho
    exact hu p γ o hγ
  let X := fun p => Classical.choose (hX p)
  have hXs : ∀ p, _ := fun p => Classical.choose_spec (hX p)
  have hE : ∀ p, ∃ l : List (LEv sp D n), LRun (X p).1 l (meetState sp j u hju) ∧
      ∀ q k j d, LEv.recv q k j d ∉ l := by
    intro p
    obtain ⟨es, hx⟩ := reach_meet (hXs p).2.1 (hXs p).2.2
    obtain ⟨l, hl, _, hnr⟩ := exec_lrun_canon (D := D) (n := n) hx
    exact ⟨l, hl, hnr⟩
  let ext : Fin n → List (LEv sp D n) := fun p => Classical.choose (hE p)
  have hEs : ∀ p, _ := fun p => Classical.choose_spec (hE p)
  have hnr : ∀ p q k j d, LEv.recv q k j d ∉ ext p := fun p => (hEs p).2
  have hext : Extends H c (fun q => (H q).take (c q) ++ ext q) ext := fun _ => rfl
  have hrun : ∀ p, LRun (canon sp (init p)) ((H p).take (c p) ++ ext p) (meetState sp j u hju) :=
    fun p => lrun_append.2 ⟨(X p).1, (hXs p).1, (hEs p).1⟩
  exact ⟨_, ext, meetState sp j u hju, hext,
    ⟨fun p => ⟨_, hrun p⟩, recvMatched_extend hwf.2 hcut hext hnr⟩, rfl, hrun⟩

theorem canonOut_of_produced {Sys : System sp D} (hS : CanonicalSystem Sys) {init : Fin n → I}
    {H : History sp D n} (hp : Produced Sys n init H) (p : Fin n) (c : Nat) :
    CanonOut ((H p).take c) := by
  refine ⟨fun γ o hm => ?_, fun γ hm => ?_⟩
  · obtain ⟨a, b, hab⟩ := List.append_of_mem (List.mem_of_mem_take hm)
    exact hS.1 _ _ _ _ _ _ (hp p a _ b hab).2
  · obtain ⟨a, b, hab⟩ := List.append_of_mem (List.mem_of_mem_take hm)
    exact hS.2 _ _ _ _ _ (hp p a _ b hab).2

/-- Remark after Def. `def:response-partition-consistency`: for a canonical
system, at a common expansion `j` of the current inputs, Response Partition
Consistency and confluence coincide. -/
theorem canonical_rpc_iff_confluent {Sys : System sp D} (hS : CanonicalSystem Sys)
    {init : Fin n → I} {H : History sp D n} (hwf : WF init H) (hp : Produced Sys n init H)
    {c : Fin n → Nat} (hcut : IsCut H c) {j : I}
    (hj : ∀ p σ, LRun (canon sp (init p)) ((H p).take (c p)) σ → σ.cur ≼ j) :
    RPCAt H c j ↔ ConfluentCut init H c j :=
  ⟨confluent_of_rpc_canonical hwf hcut (fun p => canonOut_of_produced hS hp p (c p)) hj,
   rpc_of_confluent⟩

/-- The replicated system of Theorem `thm:complete-cap-response` (2)⇒(1) is
canonical. -/
theorem respSystem_canonical (T : Table I O) : CanonicalSystem (respSystem (sp := sp) (D := D) T) :=
  ⟨fun _ _ _ _ _ _ h => h.1, fun _ _ _ _ _ h => h⟩

/-! ## Input acceptance, Answering, forced answers -/

/-- "Input acceptance says that `p` never seals an expansion of its current
input": the Input-acceptance continuation for `j` exists iff `p`'s table at the
cut still has a row at `j`. -/
theorem input_acceptance_iff (Sys : System sp D) {init : Fin n → I} {H : History sp D n}
    {comp : Fin n → Nat} (hwf : WF init H) (hprod : Produced Sys n init H)
    (hpart : Partitioned H comp) {c : Fin n → Nat} (hcut : IsCut H c) {p : Fin n}
    {σ : State sp} (hσ : LRun (canon sp (init p)) ((H p).take (c p)) σ) (j : I) :
    (∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)),
        Extends H c H' ext ∧ WF init H' ∧ Produced Sys n init H' ∧ Partitioned H' comp ∧
        (∀ q, comp q ≠ comp p → ext q = []) ∧ LEv.inp j ∈ ext p) ↔ ∃ u, σ.R j u := by
  constructor
  · rintro ⟨H', ext, hext, hwf', _, _, _, hm⟩
    obtain ⟨a, b, hab⟩ := List.append_of_mem hm
    obtain ⟨τ, hτ⟩ := hwf'.1 p
    rw [hext p, hab] at hτ
    obtain ⟨σ1, h1, h2⟩ := lrun_append.1 hτ
    have := lrun_det h1 hσ
    subst this
    obtain ⟨ρ, h3, h4⟩ := lrun_append.1 h2
    cases h4 with
    | inp hs _ =>
      obtain ⟨⟨u, hu⟩, _, _⟩ := step_input_inv hs
      exact ⟨u, (lrun_mono h3).2 j u hu⟩
  · rintro ⟨u, hu⟩
    let τ : State sp :=
      { cur := j, R := inputTable σ j, sub := fun k x h => σ.sub k x h.1,
        hasCur := ⟨u, hu, PO.refl j⟩, above := fun k x h => h.2 }
    have hstep : Step σ (.input j) τ := Step.input σ τ j ⟨u, hu⟩ rfl rfl
    obtain ⟨H', ext, hext, hwf', hprod', hpart', hp, hq⟩ :=
      extend_single Sys hwf hprod hpart hcut hσ (e := .inp j)
        (by intro q k j d h; cases h) (.inp hstep (.nil τ)) trivial
    exact ⟨H', ext, hext, hwf', hprod', hpart', fun q hq' => hq q (fun h => hq' (h ▸ rfl)),
      by rw [hp]; simp⟩

/-- The Answering clause of Def. `def:response-availability` alone. -/
def Answering (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ c, IsCut H c →
    ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) ((H p).take (c p)) σ →
      ∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)),
        Extends H c H' ext ∧ WF init H' ∧ Produced Sys n init H' ∧ Partitioned H' comp ∧
        (∀ q, comp q ≠ comp p → ext q = []) ∧ (∀ j, LEv.inp j ∉ ext p) ∧
        ∃ γ o, Q n p σ.cur o ∧ LEv.out γ o ∈ ext p

theorem answering_of_ra {Sys : System sp D} {Q : (n : Nat) → Fin n → Table I O}
    (h : ResponseAvailability Sys Q) : Answering Sys Q :=
  fun n init H comp hwf hprod hpart c hc p σ hσ => (h n init H comp hwf hprod hpart c hc p σ hσ).1

/-- **Lemma `lem:forced-answer`** as currently stated: the continuation adds
only events of `q`, and no input event; it reaches a cut at which `j` still
expands every current input and the emitted outputs have no common refinement
in `S(j)`.  Only Answering is used. -/
theorem forced_answer (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O)
    (hAns : Answering Sys Q) {init : Fin n → I} {H : History sp D n}
    {comp : Fin n → Nat} (hwf : WF init H) (hprod : Produced Sys n init H)
    (hpart : Partitioned H comp) {c : Fin n → Nat} (hc : IsCut H c) {q : Fin n}
    (halone : ∀ p, comp p = comp q → p = q) {σq : State sp}
    (hσq : LRun (canon sp (init q)) ((H q).take (c q)) σq) {j : I}
    (hj : ∀ p σ, LRun (canon sp (init p)) ((H p).take (c p)) σ → σ.cur ≼ j)
    (hno : ∀ o, Q n q σq.cur o → ¬ ∃ u, sp.S j u ∧ o ≼ u) :
    ∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)),
      Extends H c H' ext ∧ WF init H' ∧ Produced Sys n init H' ∧ Partitioned H' comp ∧
      (∀ p, p ≠ q → ext p = []) ∧ (∀ p j, LEv.inp j ∉ ext p) ∧
      IsCut H' (fun p => (H' p).length) ∧
      (∀ p σ, LRun (canon sp (init p)) ((H' p).take (H' p).length) σ → σ.cur ≼ j) ∧
      ¬ RPCAt H' (fun p => (H' p).length) j := by
  obtain ⟨H', ext, hext, hwf', hprod', hpart', hloc, hnoinp, γ, o, hQ, hm⟩ :=
    hAns n init H comp hwf hprod hpart c hc q σq hσq
  have hoth : ∀ p, p ≠ q → ext p = [] := fun p hpq => hloc p (fun h => hpq (halone p h))
  refine ⟨H', ext, hext, hwf', hprod', hpart', hoth, ?_, full_cut' hwf', ?_, ?_⟩
  · intro p j' hj'
    by_cases hpq : p = q
    · subst hpq; exact hnoinp j' hj'
    · rw [hoth p hpq] at hj'; cases hj'
  · intro p σ h
    rw [List.take_length, hext p] at h
    obtain ⟨σ1, h1, h2⟩ := lrun_append.1 h
    by_cases hpq : p = q
    · subst hpq
      rw [lrun_noinp h2 hnoinp]; exact hj p σ1 h1
    · rw [hoth p hpq] at h2; cases h2; exact hj p _ h1
  · rintro ⟨u, hu, hall⟩
    apply hno o hQ ⟨u, hu, hall q γ o ?_⟩
    rw [List.take_length, hext q]; exact List.mem_append_right _ hm

/-- "Input acceptance … excludes specifications whose answers require such a
seal": if no answer at `i` has a refinement at some `j ⪰ i`, no system has
Response Availability (already for two participants, each alone). -/
theorem ra_excludes_forced_seal (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O)
    {i j : I} (hij : i ≼ j) (hno : ∀ o, Q 2 0 i o → ¬ ∃ u, sp.S j u ∧ o ≼ u) :
    ¬ ResponseAvailability Sys Q := by
  intro hRA
  let init : Fin 2 → I := fun _ => i
  let comp : Fin 2 → Nat := fun p => p.val
  let H0 : History sp D 2 := fun _ => []
  have hwf0 : WF init H0 :=
    ⟨fun p => ⟨_, .nil _⟩, by intro p a q k j d b h; simp [H0] at h⟩
  have hprod0 : Produced Sys 2 init H0 := fun p a e b h => by simp [H0] at h
  have hpart0 : Partitioned H0 comp :=
    ⟨⟨0, 1, by simp [comp]⟩, by intro p a q k j d b h; simp [H0] at h⟩
  have hcut0 : IsCut H0 (fun _ => 0) :=
    ⟨fun _ => Nat.zero_le _, by intro p a q k j d b h; simp at h⟩
  obtain ⟨⟨H', ext, hext, hwf', hprod', hpart', _, hnoinp, γ, o, hQ, hm⟩, _⟩ :=
    hRA 2 init H0 comp hwf0 hprod0 hpart0 (fun _ => 0) hcut0 0 (canon sp i) (.nil _)
  have hH' : H' 0 = ext 0 := by rw [hext 0]; simp [H0]
  obtain ⟨τ, hτ⟩ := hwf'.1 0
  rw [hH'] at hτ
  have hτc : τ.cur = i := lrun_noinp hτ hnoinp
  have hτ' : LRun (canon sp (init 0)) ((H' 0).take (H' 0).length) τ := by
    rw [List.take_length, hH']; exact hτ
  obtain ⟨_, hacc⟩ := hRA 2 init H' comp hwf' hprod' hpart' _ (full_cut' hwf') 0 τ hτ'
  obtain ⟨u, hu⟩ := (input_acceptance_iff Sys hwf' hprod' hpart' (full_cut' hwf') hτ' j).1
    (hacc j (hτc ▸ hij))
  exact hno o hQ ⟨u, τ.sub _ _ hu, lrun_out_mem hτ hm j u hu⟩

/-- "If an output permitted at every input answers, every specification is
available": indeed the full response form then holds. -/
theorem trivially_available (Q : Obligation sp) (o0 : O) (h0 : ∀ i, Q.Q i o0) :
    ∃ Sys : System sp D, Sys.Replicated ∧ ResponseAvailability Sys (fun _ _ => Q.Q) ∧
      ResponsePC Sys := by
  refine (complete_cap_response sp D Q).2 ⟨fun _ o => o = o0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i o h; rw [h]; exact h0 i
  · intro i; exact ⟨o0, rfl⟩
  · intro i o j h _; rw [h]; exact ⟨o0, rfl, PO.refl _⟩
  · intro rows hrows j _
    refine ⟨o0, Q.sub _ _ (h0 j), fun r hr => ?_⟩
    rw [hrows r hr]; exact PO.refl _

/-! ## Lemma `lem:locality` -/

/-- Lemma `lem:locality`, first part: receive-free local histories that the
strategies can produce, glued side by side, form a produced partitioned
history for any labelling with at least two labels. -/
theorem locality_glue (Sys : System sp D) {init : Fin n → I} (L : History sp D n)
    (comp : Fin n → Nat) (h2 : ∃ p q, comp p ≠ comp q)
    (hnr : ∀ p q k j d, LEv.recv q k j d ∉ L p)
    (hc : ∀ p, Compliant (Allowed Sys n init p) (L p))
    (hr : ∀ p, ∃ τ, LRun (canon sp (init p)) (L p) τ) :
    WF init L ∧ Produced Sys n init L ∧ Partitioned L comp ∧
    IsCut L (fun p => (L p).length) := by
  have hno : ∀ p a (q : Fin n) k j d b, L p ≠ a ++ LEv.recv q k j d :: b := by
    intro p a q k j d b h
    exact hnr p q k j d (by rw [h]; simp)
  have hwf : WF init L := ⟨hr, fun p a q k j d b h => absurd h (hno p a q k j d b)⟩
  exact ⟨hwf, hc, ⟨h2, fun p a q k j d b h => absurd h (hno p a q k j d b)⟩, full_cut' hwf⟩

/-- Lemma `lem:locality`, second part: under replication a receive-free local
history the strategy can produce for one participant, it can produce for any
participant with the same initial input, in any participant set. -/
theorem locality_transfer {Sys : System sp D} (hrep : Sys.Replicated) {m N : Nat}
    {init : Fin m → I} {init' : Fin N → I} {p : Fin m} {p' : Fin N} (hi : init' p' = init p)
    {l : List (LEv sp D m)} (hc : Compliant (Allowed Sys m init p) l)
    (hnr : ∀ q k j d, LEv.recv q k j d ∉ l) {τ : State sp}
    (hrun : LRun (canon sp (init p)) l τ) :
    Compliant (Allowed Sys N init' p') (l.map tr) ∧
    LRun (canon sp (init' p')) (l.map (tr (N := N))) τ ∧
    (∀ q k j d, LEv.recv q k j d ∉ l.map (tr (N := N))) ∧
    (l.map (tr (N := N))).map LEv.erase = l.map LEv.erase := by
  obtain ⟨F, hF⟩ := hrep
  exact ⟨compliant_tr hF hi hc hnr, hi ▸ lrun_tr hrun, fun q k j d => tr_norecv _ q k j d,
    erase_tr hnr⟩

/-! ## Response interfaces -/

/-- With `T = S`, consistency on `T` is the common-expansion condition. -/
theorem consistentOn_S : ConsistentOn sp sp.S ↔ sp.CommonExpansion := Iff.rfl

/-- The emitted rows of a canonical execution started at current input `i`. -/
def emRows : I → List (Event I O) → List (I × O)
  | _, [] => []
  | _, .input j :: es => emRows j es
  | i, .output o :: es => (i, o) :: emRows i es

theorem exec_emRows {σ τ : State sp} {es : List (Event I O)} (hx : Exec σ es τ) :
    (emRows σ.cur es).map Prod.snd = outs es ∧
    ∀ r ∈ emRows σ.cur es, sp.S r.1 r.2 ∧ r.1 ≼ τ.cur := by
  induction hx with
  | nil => exact ⟨rfl, by simp [emRows]⟩
  | @cons σ τ' ρ e es hs hr ih =>
    cases e with
    | input j =>
      obtain ⟨_, hcur, _⟩ := step_input_inv hs
      simp only [emRows, outs]
      rw [hcur] at ih; exact ih
    | output o =>
      obtain ⟨hleg, hcur, _⟩ := step_output_inv hs
      simp only [emRows, outs, List.map_cons]
      rw [hcur] at ih
      refine ⟨by rw [ih.1], fun r hm => ?_⟩
      rcases List.mem_cons.1 hm with rfl | hm
      · refine ⟨σ.sub _ _ hleg, ?_⟩
        have := exec_cur_le hr; rw [hcur] at this; exact this
      · exact ih.2 r hm

/-- The state after emitting `o` from `σ` by the canonical event. -/
def outSt (σ : State sp) (o : O) (ho : σ.R σ.cur o) : State sp where
  cur := σ.cur
  R := outputTable σ o
  sub := fun k x h => σ.sub k x h.1
  hasCur := ⟨o, ho, PO.refl o⟩
  above := fun k x h => σ.above k x h.1

/-- Remark after Def. `def:response-interface`: (for `T ⊆ S`) consistency on
`T` is confluence of the canonical runs whose emitted rows lie in `T`. -/
theorem consistentOn_iff_confluent (T : Table I O) (hTS : ∀ i o, T i o → sp.S i o) :
    ConsistentOn sp T ↔
    ∀ fam : List (I × List (Event I O) × State sp),
      (∀ x ∈ fam, Exec (canon sp x.1) x.2.1 x.2.2 ∧ ∀ r ∈ emRows x.1 x.2.1, T r.1 r.2) →
      ∀ j, (∀ x ∈ fam, x.2.2.cur ≼ j) → ConfluentAt (fam.map (fun x => x.2.2)) j := by
  constructor
  · intro hc fam hfam j hj
    let rows := fam.flatMap (fun x => emRows x.1 x.2.1)
    obtain ⟨u, hu, hall⟩ := hc rows
      (by intro r hr; simp only [rows, List.mem_flatMap] at hr
          obtain ⟨x, hx, hr⟩ := hr; exact (hfam x hx).2 r hr) j
      (by intro r hr; simp only [rows, List.mem_flatMap] at hr
          obtain ⟨x, hx, hr⟩ := hr
          exact PO.trans ((exec_emRows (hfam x hx).1).2 r hr).2 (hj x hx))
    refine ⟨meetState sp j u hu, rfl, fun σ hσ => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hσ
    have hex := (hfam x hx).1
    have hres : Residual x.2.2 (outs x.2.1) := run_residual hex
    have hin : x.2.2.R j u := by
      refine (hres j u).2 ⟨hu, hj x hx, fun o ho => ?_⟩
      have hm := (exec_emRows hex).1
      rw [← hm] at ho
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ho
      exact hall r (by simp only [rows, List.mem_flatMap]; exact ⟨x, hx, hr⟩)
    exact reach_meet hres hin
  · intro hconf rows hrows j hj
    have hR : ∀ r ∈ rows, (canon sp r.1).R (canon sp r.1).cur r.2 :=
      fun r hr => ⟨hTS _ _ (hrows r hr), PO.refl _⟩
    let fam : List (I × List (Event I O) × State sp) := rows.attach.map
      (fun r => (r.1.1, [.output r.1.2], outSt (canon sp r.1.1) r.1.2 (hR r.1 r.2)))
    obtain ⟨τ, hτ, hreach⟩ := hconf fam
      (by intro x hx
          obtain ⟨r, _, rfl⟩ := List.mem_map.1 hx
          refine ⟨.cons (Step.output (canon sp r.1.1) (outSt (canon sp r.1.1) r.1.2 (hR r.1 r.2))
            r.1.2 (hR r.1 r.2) rfl rfl) (.nil _), ?_⟩
          intro r' hr'
          simp only [emRows, List.mem_singleton] at hr'
          subst hr'; exact hrows _ r.2) j
      (by intro x hx
          obtain ⟨r, _, rfl⟩ := List.mem_map.1 hx
          exact hj _ r.2)
    obtain ⟨u, hu⟩ := τ.hasCur
    rw [hτ] at hu
    refine ⟨u, τ.sub _ _ hu, fun r hr => ?_⟩
    have hmem : outSt (canon sp r.1) r.2 (hR r hr) ∈ fam.map (fun x => x.2.2) := by
      simp only [fam, List.map_map]
      exact List.mem_map.2 ⟨⟨r, hr⟩, List.mem_attach _ _, rfl⟩
    exact (reach_sub (hreach _ hmem) j u hu).2

/-! ## Relationship to the interface form -/

/-- Consistency on `T` from a bound at each input. -/
theorem consistentOn_of_bound {T : Table I O}
    (h : ∀ j, ∃ u, sp.S j u ∧ ∀ i o, T i o → i ≼ j → o ≼ u) : ConsistentOn sp T := by
  intro rows hrows j hj
  obtain ⟨u, hu, hall⟩ := h j
  exact ⟨u, hu, fun r hr => hall r.1 r.2 (hrows r hr) (hj r hr)⟩

/-- Lifted Monotonicity implies the response form with `T = Q`. -/
theorem lm_response_interface (Q : Obligation sp) (h : sp.LiftedMono) :
    ResponseInterface Q Q.Q ∧ ConsistentOn sp Q.Q := by
  have hce := (liftedMono_iff_commonExpansion _).1 h
  refine ⟨⟨fun _ _ h => h, Q.total, ?_⟩,
    fun rows hr j hj => hce rows (fun r hr' => Q.sub _ _ (hr r hr')) j hj⟩
  intro i o j hio hij
  obtain ⟨q, hq⟩ := Q.total j
  obtain ⟨w, hw, hall⟩ := hce [(i, o), (j, q)]
    (by intro r hr; simp at hr; rcases hr with rfl | rfl
        · exact Q.sub _ _ hio
        · exact Q.sub _ _ hq) j
    (by intro r hr; simp at hr; rcases hr with rfl | rfl
        · exact hij
        · exact PO.refl j)
  exact ⟨w, Q.up j q w hq hw (hall (j, q) (by simp)), hall (i, o) (by simp)⟩

theorem lm_response_form (Q : Obligation sp) (h : sp.LiftedMono) :
    ∃ Sys : System sp D, Sys.Replicated ∧ ResponseAvailability Sys (fun _ _ => Q.Q) ∧
      ResponsePC Sys :=
  (complete_cap_response sp D Q).2 ⟨Q.Q, lm_response_interface Q h⟩

/-- A total `T ⊆ Q` that satisfies Lifted Monotonicity as a specification is a
response interface on which `S` is consistent. -/
theorem subspec_lm_interface (Q : Obligation sp) (T : Spec I O) (hTQ : ∀ i o, T.S i o → Q.Q i o)
    (h : T.LiftedMono) : ResponseInterface Q T.S ∧ ConsistentOn sp T.S := by
  have hce := (liftedMono_iff_commonExpansion _).1 h
  refine ⟨⟨hTQ, T.total, ?_⟩, ?_⟩
  · intro i o j hio hij
    obtain ⟨u, hu, hall⟩ := hce [(i, o)] (by simpa using hio) j (by simpa using hij)
    exact ⟨u, hu, hall (i, o) (by simp)⟩
  · intro rows hr j hj
    obtain ⟨u, hu, hall⟩ := hce rows hr j hj
    exact ⟨u, Q.sub _ _ (hTQ _ _ hu), hall⟩

/-- For a functional specification the response form and Lifted
Monotonicity coincide (specification level). -/
theorem functional_response_iff (hf : sp.Functional) (Q : Obligation sp) :
    (∃ T, ResponseInterface Q T ∧ ConsistentOn sp T) ↔ sp.LiftedMono := by
  constructor
  · rintro ⟨T, ⟨hTQ, hTtot, _⟩, hc⟩
    have hST : ∀ i o, sp.S i o → T i o := by
      intro i o hio
      obtain ⟨o', ho'⟩ := hTtot i
      have := hf i o o' hio (Q.sub _ _ (hTQ _ _ ho'))
      subst this; exact ho'
    exact (liftedMono_iff_commonExpansion _).2 (fun rows hr j hj => hc rows (fun r h => hST _ _ (hr r h)) j hj)
  · intro h; exact ⟨Q.Q, lm_response_interface Q h⟩

/-- For a functional specification the two forms of Complete CAP coincide
(system level). -/
theorem functional_forms_coincide (hf : sp.Functional) (Q : Obligation sp) :
    (∃ Sys : System sp D, Sys.Replicated ∧ ResponseAvailability Sys (fun _ _ => Q.Q) ∧
      ResponsePC Sys) ↔
    (∃ Sys : System sp D, Availability Sys ∧ PartitionConsistency Sys) := by
  rw [complete_cap_response, complete_cap, functional_response_iff hf]

end General

/-! ## Remark "Without replication" -/

section NonRep

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type}

theorem allowed_congr {S1 S2 : System sp D} (hb : S1.basis = S2.basis) {n : Nat}
    {init init' : Fin n → I} {p : Fin n} (hs : S1.strat n init p = S2.strat n init' p) :
    Allowed S1 n init p = Allowed S2 n init' p := by
  funext pre e
  cases e <;> simp only [Allowed, hb, hs]

theorem produced_congr {S1 S2 : System sp D} (hb : S1.basis = S2.basis) {n : Nat}
    {init : Fin n → I} (hs : S1.strat n init = S2.strat n init) :
    Produced S1 n init = Produced S2 n init := by
  funext H
  unfold Produced
  have : ∀ p, Allowed S1 n init p = Allowed S2 n init p :=
    fun p => allowed_congr hb (congrFun hs p)
  simp only [this]

/-- Response Availability is a per-configuration property: it holds as soon as,
for each participant set and choice of initial inputs, some system with the
same basis and the same strategies there has it. -/
theorem ra_pointwise {Sys : System sp D} {Q : (n : Nat) → Fin n → Table I O}
    (h : ∀ n (init : Fin n → I), ∃ S' : System sp D, S'.basis = Sys.basis ∧
      S'.strat n init = Sys.strat n init ∧ ResponseAvailability S' Q) :
    ResponseAvailability Sys Q := by
  intro n init H comp hwf hprod hpart c hc p σ hσ
  obtain ⟨S', hb, hs, hRA⟩ := h n init
  have hP : Produced Sys n init = Produced S' n init := (produced_congr hb hs).symm
  rw [hP] at hprod ⊢
  exact hRA n init H comp hwf hprod hpart c hc p σ hσ

theorem rpc_pointwise {Sys : System sp D}
    (h : ∀ n (init : Fin n → I), ∃ S' : System sp D, S'.basis = Sys.basis ∧
      S'.strat n init = Sys.strat n init ∧ ResponsePC S') :
    ResponsePC Sys := by
  intro n init H comp hwf hprod hpart c hc j hj
  obtain ⟨S', hb, hs, hR⟩ := h n init
  have hP : Produced Sys n init = Produced S' n init := (produced_congr hb hs).symm
  rw [hP] at hprod
  exact hR n init H comp hwf hprod hpart c hc j hj

/-- An isolated emission of `o` at current input `i` by participant `p` of the
participant set `Fin n`. -/
def IsoEmitAt (Sys : System sp D) (n : Nat) (p : Fin n) (i : I) (o : O) : Prop :=
  ∃ (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat) (a b : List (LEv sp D n))
    (γ : List (Commitment sp)) (σ : State sp),
    WF init H ∧ Produced Sys n init H ∧ Partitioned H comp ∧ H p = a ++ .out γ o :: b ∧
    (∀ q k j d, LEv.recv q k j d ∉ a) ∧ LRun (canon sp (init p)) a σ ∧ σ.cur = i

/-- The remark's `T_p`: rows of `Q_p` emitted by `p` in isolated emissions. -/
def Tp (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O) (n : Nat) (p : Fin n) :
    Table I O :=
  fun i o => Q n p i o ∧ IsoEmitAt Sys n p i o

structure LocAt (Sys : System sp D) (n : Nat) (p : Fin n) (i : I) (o : O) where
  init : Fin n → I
  a : List (LEv sp D n)
  γ : List (Commitment sp)
  comp : Compliant (Allowed Sys n init p) (a ++ [LEv.out γ o])
  norecv : ∀ q k j d, LEv.recv q k j d ∉ a
  run : ∃ τ, LRun (canon sp (init p)) (a ++ [LEv.out γ o]) τ
  cur : ∀ σ, LRun (canon sp (init p)) a σ → σ.cur = i

theorem IsoEmitAt.loc {Sys : System sp D} {n : Nat} {p : Fin n} {i : I} {o : O}
    (h : IsoEmitAt Sys n p i o) : Nonempty (LocAt Sys n p i o) := by
  obtain ⟨init, H, _, a, b, γ, σ, hwf, hprod, _, hH, hnr, hσ, hcur⟩ := h
  have hH' : H p = (a ++ [LEv.out γ o]) ++ b := by simp [hH]
  obtain ⟨τ, hτ⟩ := hwf.1 p
  rw [hH'] at hτ
  obtain ⟨τ1, h1, _⟩ := lrun_append.1 hτ
  have hc := hprod p; rw [hH'] at hc
  exact ⟨⟨init, a, γ, compliant_prefix hc, hnr, ⟨τ1, h1⟩,
    fun σ' h => by rw [lrun_det h hσ]; exact hcur⟩⟩

theorem two_labels {n : Nat} (h2 : 2 ≤ n) :
    ∃ p q : Fin n, (fun q : Fin n => q.val) p ≠ (fun q : Fin n => q.val) q :=
  ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩

/-- Replaying an isolated emission in its own participant set, alone in its
block, the others idle. -/
theorem LocAt.replay {Sys : System sp D} {n : Nat} (h2 : 2 ≤ n) {p : Fin n} {i : I} {o : O}
    (w : LocAt Sys n p i o) (init' : Fin n → I) (hi : init' p = w.init p)
    (hA : Allowed Sys n init' p = Allowed Sys n w.init p) :
    let L : History sp D n := fun q => if q = p then w.a ++ [LEv.out w.γ o] else []
    WF init' L ∧ Produced Sys n init' L ∧ Partitioned L (fun q => q.val) ∧
      IsCut L (fun q => (L q).length) ∧
      ∀ σ, LRun (canon sp (init' p)) ((L p).take (L p).length) σ → σ.cur = i := by
  intro L
  have hLp : L p = w.a ++ [LEv.out w.γ o] := by simp [L]
  have hLq : ∀ q, q ≠ p → L q = [] := fun q h => by simp [L, h]
  obtain ⟨g1, g2, g3, g4⟩ := locality_glue Sys (init := init') L _ (two_labels h2)
    (fun q => by
      by_cases hq : q = p
      · rw [hq, hLp]; intro q' k j d hm
        rcases List.mem_append.1 hm with hm | hm
        · exact w.norecv q' k j d hm
        · simp at hm
      · rw [hLq q hq]; simp)
    (fun q => by
      by_cases hq : q = p
      · rw [hq, hLp, hA]; exact w.comp
      · rw [hLq q hq]; intro a e b h; simp at h)
    (fun q => by
      by_cases hq : q = p
      · rw [hq, hLp, hi]; exact w.run
      · rw [hLq q hq]; exact ⟨_, .nil _⟩)
  refine ⟨g1, g2, g3, g4, fun σ hσ => ?_⟩
  rw [List.take_length, hLp, hi] at hσ
  obtain ⟨σa, ha, hb⟩ := lrun_append.1 hσ
  rw [lrun_noinp hb (by simp)]
  exact w.cur σa ha

/-- Answering at a participant of a singleton-block history yields an
isolated emission by that participant, refining its earlier outputs. -/
theorem answer_iso_at {Sys : System sp D} {Q : (n : Nat) → Fin n → Table I O}
    (hRA : ResponseAvailability Sys Q) {N : Nat} {init : Fin N → I}
    {H : History sp D N} (hwf : WF init H) (hprod : Produced Sys N init H)
    (hpart : Partitioned H (fun p => p.val)) {c : Fin N → Nat} (hcut : IsCut H c)
    {p : Fin N} {σ : State sp} (hσ : LRun (canon sp (init p)) ((H p).take (c p)) σ) :
    ∃ u, Q N p σ.cur u ∧ IsoEmitAt Sys N p σ.cur u ∧
      ∀ γ0 o, LEv.out γ0 o ∈ (H p).take (c p) → o ≼ u := by
  obtain ⟨⟨H', ext, hext, hwf', hprod', hpart', _, hnoinp, γ, u, hQ, hm⟩, _⟩ :=
    hRA N init H _ hwf hprod hpart c hcut p σ hσ
  obtain ⟨a, b, hab⟩ := List.append_of_mem hm
  have hH' : H' p = ((H p).take (c p) ++ a) ++ LEv.out γ u :: b := by rw [hext p, hab]; simp
  have hnr := norecv_singletons hwf' hpart'
  obtain ⟨τ, hτ⟩ := hwf'.1 p
  have hτ' := hτ; rw [hH'] at hτ'
  obtain ⟨σa, hσa, _⟩ := lrun_append.1 hτ'
  obtain ⟨σ1, h1, h2⟩ := lrun_append.1 hσa
  have hcur : σa.cur = σ.cur := by
    rw [lrun_noinp h2 (fun j hj => hnoinp j (by rw [hab]; simp [hj])), lrun_det h1 hσ]
  refine ⟨u, hQ, ⟨init, H', _, _, b, γ, σa, hwf', hprod', hpart', hH', ?_, hσa, hcur⟩, ?_⟩
  · intro q k j d hm'
    exact hnr p q k j d (by rw [hH']; exact List.mem_append_left _ hm')
  · intro γ0 o ho
    obtain ⟨l1, l2, hl⟩ := List.append_of_mem ho
    have : LRun (canon sp (init p)) (l1 ++ LEv.out γ0 o :: (l2 ++ ext p)) τ := by
      rw [hext p, hl] at hτ; simpa using hτ
    exact lrun_later_le this (List.mem_append_right _ hm)

/-- Remark "Without replication", first half (no extra hypothesis): for a
fixed participant set with at least two participants, each `T_p` is a response
interface contained in `Q_p` (total and self-continuing). -/
theorem without_replication_interface (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O)
    (hRA : ResponseAvailability Sys Q) {n : Nat} (h2 : 2 ≤ n) (p : Fin n) :
    (∀ i o, Tp Sys Q n p i o → Q n p i o) ∧ (∀ i, ∃ o, Tp Sys Q n p i o) ∧
    ∀ i o j, Tp Sys Q n p i o → i ≼ j → ∃ u, Tp Sys Q n p j u ∧ o ≼ u := by
  classical
  refine ⟨fun _ _ h => h.1, ?_, ?_⟩
  · intro i
    let L : History sp D n := fun _ => []
    obtain ⟨g1, g2, g3, g4⟩ := locality_glue Sys (init := fun _ => i) L _ (two_labels h2)
      (fun _ _ _ _ _ => by simp [L]) (fun _ a e b h => by simp [L] at h) (fun _ => ⟨_, .nil _⟩)
    obtain ⟨u, hQ, hiso, _⟩ := answer_iso_at hRA g1 g2 g3 g4 (p := p) (σ := canon sp i) (.nil _)
    exact ⟨u, hQ, hiso⟩
  · intro i o j hT hij
    let w := Classical.choice hT.2.loc
    obtain ⟨h1, h2', h3, h4, hcur⟩ := w.replay h2 w.init rfl rfl
    let L : History sp D n := fun q => if q = p then w.a ++ [LEv.out w.γ o] else []
    have hLp : L p = w.a ++ [LEv.out w.γ o] := by simp [L]
    obtain ⟨τ1, hτ1⟩ := h1.1 p
    have hτ1' : LRun (canon sp (w.init p)) ((L p).take (L p).length) τ1 := by
      rw [List.take_length]; exact hτ1
    have hτc := hcur τ1 hτ1'
    obtain ⟨_, hacc⟩ := hRA n w.init L _ h1 h2' h3 _ h4 p τ1 hτ1'
    obtain ⟨H2, ext2, hext2, hwf2, hprod2, hpart2, _, hinj⟩ := hacc j (hτc ▸ hij)
    obtain ⟨a2, b2, hab2⟩ := List.append_of_mem hinj
    have hnr2 := norecv_singletons hwf2 hpart2
    have hH2p : H2 p = (L p ++ a2 ++ [LEv.inp j]) ++ b2 := by
      rw [hext2 p, hab2]; simp [L, List.take_of_length_le]
    let c2 : Fin n → Nat := fun q =>
      if q = p then (L p ++ a2 ++ [LEv.inp j]).length else (H2 q).length
    have hc2 : IsCut H2 c2 := cut_of_norecv hnr2 (fun q => by
      by_cases hq : q = p
      · rw [hq]; simp only [c2, ite_true]; rw [hH2p]; simp
      · simp only [c2, hq, ite_false]; exact Nat.le_refl _)
    have htake : (H2 p).take (c2 p) = L p ++ a2 ++ [LEv.inp j] := by
      simp only [c2, ite_true]; rw [hH2p]; exact List.take_left' rfl
    obtain ⟨τ2, hτ2⟩ := hwf2.1 p
    obtain ⟨σ2, hσ2⟩ := lrun_take hτ2 (c2 p)
    have hσ2' := hσ2; rw [htake] at hσ2'
    obtain ⟨_, _, hlast⟩ := lrun_append.1 hσ2'
    have hj2 : σ2.cur = j := by
      cases hlast with
      | inp hs hr => cases hr; exact (step_input_inv hs).2.1
    obtain ⟨u, hQ, hiso, hge⟩ := answer_iso_at hRA hwf2 hprod2 hpart2 hc2 hσ2
    rw [hj2] at hQ hiso
    refine ⟨u, ⟨hQ, hiso⟩, hge w.γ o ?_⟩
    rw [htake, hLp]
    simp

/-- Strategies depend on the initial inputs only through the participant's
own initial input (they may still depend on the participant set and the
participant's identity). -/
def LocalInit (Sys : System sp D) : Prop :=
  ∀ n (init init' : Fin n → I) (p : Fin n), init p = init' p →
    Sys.strat n init p = Sys.strat n init' p

/-- Remark "Without replication", second half, corrected: for a fixed
participant set with at least two participants and strategies satisfying
`LocalInit`, consistency holds for every family that draws on each `T_p` at
most once (the participants in `A`, row `r p` from `T_p`). -/
theorem without_replication (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O)
    (hRPC : ResponsePC Sys) (hloc : LocalInit Sys) {n : Nat} (h2 : 2 ≤ n)
    (A : Fin n → Prop) (r : Fin n → I × O)
    (hr : ∀ p, A p → Tp Sys Q n p (r p).1 (r p).2) (j : I) (hj : ∀ p, A p → (r p).1 ≼ j) :
    ∃ u, sp.S j u ∧ ∀ p, A p → (r p).2 ≼ u := by
  classical
  let W : ∀ p, A p → LocAt Sys n p (r p).1 (r p).2 := fun p h => Classical.choice (hr p h).2.loc
  let init : Fin n → I := fun p => if h : A p then (W p h).init p else j
  let L : History sp D n := fun p =>
    if h : A p then (W p h).a ++ [LEv.out (W p h).γ (r p).2] else []
  have hinit : ∀ p (h : A p), init p = (W p h).init p := fun p h => by simp only [init, h, ↓reduceDIte]
  have hinitn : ∀ p, ¬ A p → init p = j := fun p h => by simp only [init, h, ↓reduceDIte]
  have hLp : ∀ p (h : A p), L p = (W p h).a ++ [LEv.out (W p h).γ (r p).2] :=
    fun p h => by simp only [L, h, ↓reduceDIte]
  have hLn : ∀ p, ¬ A p → L p = [] := fun p h => by simp only [L, h, ↓reduceDIte]
  have hAl : ∀ p (h : A p), Allowed Sys n init p = Allowed Sys n (W p h).init p :=
    fun p h => allowed_congr rfl (hloc n init (W p h).init p (hinit p h))
  obtain ⟨g1, g2, g3, g4⟩ := locality_glue Sys (init := init) L _ (two_labels h2)
    (fun p => by
      by_cases h : A p
      · rw [hLp p h]; intro q k j' d hm
        rcases List.mem_append.1 hm with hm | hm
        · exact (W p h).norecv q k j' d hm
        · simp at hm
      · rw [hLn p h]; simp)
    (fun p => by
      by_cases h : A p
      · rw [hLp p h, hAl p h]; exact (W p h).comp
      · rw [hLn p h]; intro a e b h; simp at h)
    (fun p => by
      by_cases h : A p
      · rw [hLp p h, hinit p h]; exact (W p h).run
      · rw [hLn p h]; exact ⟨_, .nil _⟩)
  have hcurs : ∀ p σ, LRun (canon sp (init p)) ((L p).take (L p).length) σ → σ.cur ≼ j := by
    intro p σ hσ
    rw [List.take_length] at hσ
    by_cases h : A p
    · rw [hLp p h, hinit p h] at hσ
      obtain ⟨σa, ha, hb⟩ := lrun_append.1 hσ
      rw [lrun_noinp hb (by simp), (W p h).cur σa ha]
      exact hj p h
    · rw [hLn p h] at hσ; cases hσ
      show init p ≼ j
      rw [hinitn p h]; exact PO.refl j
  obtain ⟨u, hu, hall⟩ := hRPC n init L _ g1 g2 g3 _ g4 j hcurs
  refine ⟨u, hu, fun p h => ?_⟩
  apply hall p (W p h).γ
  rw [List.take_length, hLp p h]
  simp

end NonRep

/-! ## Concrete examples -/

section Examples

/-- Two inputs `lo ≺ hi`. -/
inductive In2 | lo | hi
  deriving DecidableEq

def In2.leB : In2 → In2 → Bool
  | .lo, _ => true
  | .hi, .hi => true
  | .hi, .lo => false

instance : PO In2 where
  le x y := In2.leB x y = true
  refl x := by cases x <;> rfl
  trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  antisymm := by intro x y; cases x <;> cases y <;> decide

instance (x y : In2) : Decidable (x ≼ y) := inferInstanceAs (Decidable (In2.leB x y = true))

/-! ### The converse counterexample: `⊥ ≺ a`, `⊥ ≺ b`, `S(0) = {⊥, a}`, `S(1) = {b}` -/

inductive O3 | bot | a | b
  deriving DecidableEq

def O3.leB : O3 → O3 → Bool
  | .bot, _ => true
  | .a, .a => true
  | .b, .b => true
  | _, _ => false

instance : PO O3 where
  le x y := O3.leB x y = true
  refl x := by cases x <;> rfl
  trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  antisymm := by intro x y; cases x <;> cases y <;> decide

instance (x y : O3) : Decidable (x ≼ y) := inferInstanceAs (Decidable (O3.leB x y = true))

def cxB : In2 → O3 → Bool
  | .lo, .bot => true
  | .lo, .a => true
  | .hi, .b => true
  | _, _ => false

abbrev cxSpec : Spec In2 O3 :=
  ⟨fun i o => cxB i o = true, by intro i; cases i; exact ⟨.bot, rfl⟩; exact ⟨.b, rfl⟩⟩

/-- `Q = S`. -/
abbrev cxQ : Obligation cxSpec :=
  ⟨cxSpec.S, fun _ _ h => h, cxSpec.total, fun _ _ _ _ h _ => h⟩

def cxTB : In2 → O3 → Bool
  | .lo, .bot => true
  | .hi, .b => true
  | _, _ => false

/-- The response interface `{(0,⊥), (1,b)}`. -/
abbrev cxT : Table In2 O3 := fun i o => cxTB i o = true

/-- "The converse fails": Lifted Monotonicity fails (at `(0,a)`), but `S` is
consistent on the response interface `{(0,⊥),(1,b)}`. -/
theorem converse_counterexample :
    ¬ cxSpec.LiftedMono ∧ ResponseInterface cxQ cxT ∧ ConsistentOn cxSpec cxT := by
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro h
    obtain ⟨u, hu, hle⟩ := h .lo .hi rfl [.a] (by simp) (by intro x hx; simp at hx; subst hx; rfl)
    have hau := hle .a (by simp)
    cases u <;> revert hu hau <;> decide
  · intro i o h; cases i <;> cases o <;> revert h <;> decide
  · intro i; cases i
    · exact ⟨.bot, rfl⟩
    · exact ⟨.b, rfl⟩
  · intro i o j h hij
    cases i <;> cases o <;> cases j <;>
      first
        | exact absurd h (by decide)
        | exact absurd hij (by decide)
        | exact ⟨.bot, rfl, rfl⟩
        | exact ⟨.b, rfl, rfl⟩
  · apply consistentOn_of_bound
    intro j; cases j
    · exact ⟨.bot, rfl, by intro i o h hi; cases i <;> cases o <;> revert h hi <;> decide⟩
    · exact ⟨.b, rfl, by intro i o h hi; cases i <;> cases o <;> revert h hi <;> decide⟩

/-- System-level reading: the response form holds, the interface form does not. -/
theorem converse_counterexample_systems (D : Type) :
    (∃ Sys : System cxSpec D, Sys.Replicated ∧ ResponseAvailability Sys (fun _ _ => cxQ.Q) ∧
      ResponsePC Sys) ∧
    ¬ ∃ Sys : System cxSpec D, Availability Sys ∧ PartitionConsistency Sys := by
  obtain ⟨h1, h2, h3⟩ := converse_counterexample
  exact ⟨(complete_cap_response cxSpec D cxQ).2 ⟨cxT, h2, h3⟩,
    fun h => h1 ((complete_cap cxSpec D).1 h)⟩

/-! ### The sub-specification counterexample, `I = {i₁, i₂, j, k₁, k₂}` -/

inductive I5 | i1 | i2 | j | k1 | k2
  deriving DecidableEq

def I5.leB : I5 → I5 → Bool
  | .i1, .i1 | .i2, .i2 | .j, .j | .k1, .k1 | .k2, .k2 => true
  | .i1, .j | .i1, .k1 | .i1, .k2 | .i2, .j | .i2, .k1 | .i2, .k2 => true
  | .j, .k1 | .j, .k2 => true
  | _, _ => false

instance : PO I5 where
  le x y := I5.leB x y = true
  refl x := by cases x <;> rfl
  trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  antisymm := by intro x y; cases x <;> cases y <;> decide

instance (x y : I5) : Decidable (x ≼ y) := inferInstanceAs (Decidable (I5.leB x y = true))

inductive O8 | a | b | c1 | c2 | d1 | d2 | e1 | e2
  deriving DecidableEq

/-- The least order with `a ≺ c₁`, `b ≺ c₂`, `c₁,c₂ ≺ d₁,d₂`,
`c₁,c₂,d₁ ≺ e₁`, `c₁,c₂,d₂ ≺ e₂` (transitivity is checked by `trans` below). -/
def O8.leB : O8 → O8 → Bool
  | .a, .a | .b, .b | .c1, .c1 | .c2, .c2 | .d1, .d1 | .d2, .d2 | .e1, .e1 | .e2, .e2 => true
  | .a, .c1 | .a, .d1 | .a, .d2 | .a, .e1 | .a, .e2 => true
  | .b, .c2 | .b, .d1 | .b, .d2 | .b, .e1 | .b, .e2 => true
  | .c1, .d1 | .c1, .d2 | .c1, .e1 | .c1, .e2 => true
  | .c2, .d1 | .c2, .d2 | .c2, .e1 | .c2, .e2 => true
  | .d1, .e1 | .d2, .e2 => true
  | _, _ => false

instance : PO O8 where
  le x y := O8.leB x y = true
  refl x := by cases x <;> rfl
  trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  antisymm := by intro x y; cases x <;> cases y <;> decide

instance (x y : O8) : Decidable (x ≼ y) := inferInstanceAs (Decidable (O8.leB x y = true))

def s5B : I5 → O8 → Bool
  | .i1, .a => true
  | .i2, .b => true
  | .j, .c1 | .j, .c2 | .j, .d1 | .j, .d2 => true
  | .k1, .e1 => true
  | .k2, .e2 => true
  | _, _ => false

abbrev sp5 : Spec I5 O8 :=
  ⟨fun i o => s5B i o = true, by
    intro i; cases i
    · exact ⟨.a, rfl⟩
    · exact ⟨.b, rfl⟩
    · exact ⟨.c1, rfl⟩
    · exact ⟨.e1, rfl⟩
    · exact ⟨.e2, rfl⟩⟩

abbrev Q5 : Obligation sp5 := ⟨sp5.S, fun _ _ h => h, sp5.total, fun _ _ _ _ h _ => h⟩

def t5B : I5 → O8 → Bool
  | .i1, .a => true
  | .i2, .b => true
  | .j, .c1 | .j, .c2 => true
  | .k1, .e1 => true
  | .k2, .e2 => true
  | _, _ => false

abbrev T5 : Table I5 O8 := fun i o => t5B i o = true

/-- `T` is a response interface on which `S` is consistent (`d₁` reconciles
families at `j`, `e₁`/`e₂` those at `k₁`/`k₂`). -/
theorem subspec_example_interface : ResponseInterface Q5 T5 ∧ ConsistentOn sp5 T5 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro i o h; cases i <;> cases o <;> revert h <;> decide
  · intro i; cases i
    · exact ⟨.a, rfl⟩
    · exact ⟨.b, rfl⟩
    · exact ⟨.c1, rfl⟩
    · exact ⟨.e1, rfl⟩
    · exact ⟨.e2, rfl⟩
  · intro i o j' h hij
    cases i <;> cases o <;> cases j' <;>
      first
        | exact absurd h (by decide)
        | exact absurd hij (by decide)
        | exact ⟨.a, rfl, rfl⟩
        | exact ⟨.b, rfl, rfl⟩
        | exact ⟨.c1, rfl, rfl⟩
        | exact ⟨.c2, rfl, rfl⟩
        | exact ⟨.e1, rfl, rfl⟩
        | exact ⟨.e2, rfl, rfl⟩
  · apply consistentOn_of_bound
    intro j'; cases j'
    · exact ⟨.a, rfl, by intro i o h hi; cases i <;> cases o <;> revert h hi <;> decide⟩
    · exact ⟨.b, rfl, by intro i o h hi; cases i <;> cases o <;> revert h hi <;> decide⟩
    · exact ⟨.d1, rfl, by intro i o h hi; cases i <;> cases o <;> revert h hi <;> decide⟩
    · exact ⟨.e1, rfl, by intro i o h hi; cases i <;> cases o <;> revert h hi <;> decide⟩
    · exact ⟨.e2, rfl, by intro i o h hi; cases i <;> cases o <;> revert h hi <;> decide⟩

/-- No total sub-specification of `S` satisfies Lifted Monotonicity (it would
contain `(i₁,a)` and `(i₂,b)`, hence `d₁` or `d₂` at `j`, which has no
refinement at `k₂` or `k₁` respectively). -/
theorem subspec_example_noLM (T' : Spec I5 O8) (hsub : ∀ i o, T'.S i o → sp5.S i o) :
    ¬ T'.LiftedMono := by
  intro hlm
  have hce := (liftedMono_iff_commonExpansion _).1 hlm
  obtain ⟨oa, hoa⟩ := T'.total .i1
  obtain ⟨ob, hob⟩ := T'.total .i2
  have ha : oa = .a := by
    have := hsub _ _ hoa; cases oa <;> first | rfl | exact absurd this (by decide)
  have hb : ob = .b := by
    have := hsub _ _ hob; cases ob <;> first | rfl | exact absurd this (by decide)
  subst ha hb
  obtain ⟨u, hu, hall⟩ := hce [(.i1, .a), (.i2, .b)]
    (by intro r hr; simp at hr; rcases hr with rfl | rfl <;> assumption) .j
    (by intro r hr; simp at hr; rcases hr with rfl | rfl <;> rfl)
  have hau := hall (.i1, .a) (by simp)
  have hbu := hall (.i2, .b) (by simp)
  have huS := hsub _ _ hu
  cases u <;> try (revert hau hbu huS; decide)
  · obtain ⟨w, hw, hallw⟩ := hce [(.j, .d1)]
      (by intro r hr; simp at hr; subst hr; exact hu) .k2
      (by intro r hr; simp at hr; subst hr; rfl)
    have h1 := hallw (.j, .d1) (by simp)
    have h2 := hsub _ _ hw
    cases w <;> revert h1 h2 <;> decide
  · obtain ⟨w, hw, hallw⟩ := hce [(.j, .d2)]
      (by intro r hr; simp at hr; subst hr; exact hu) .k1
      (by intro r hr; simp at hr; subst hr; rfl)
    have h1 := hallw (.j, .d2) (by simp)
    have h2 := hsub _ _ hw
    cases w <;> revert h1 h2 <;> decide

/-- The relationship paragraph's example, assembled: a response interface on
which `S` is consistent, although no total `T' ⊆ Q` satisfies Lifted
Monotonicity. -/
theorem subspec_counterexample :
    (ResponseInterface Q5 T5 ∧ ConsistentOn sp5 T5) ∧
    ∀ T' : Spec I5 O8, (∀ i o, T'.S i o → Q5.Q i o) → ¬ T'.LiftedMono :=
  ⟨subspec_example_interface, fun T' h => subspec_example_noLM T' h⟩

/-- "A participant that emits `d₁` or `d₂` seals `k₂` or `k₁`" (under any
basis). -/
theorem emit_d1_seals_k2 {D : Type} {n : Nat} {σ τ : State sp5} {l : List (LEv sp5 D n)}
    (h : LRun σ l τ) {γ : List (Commitment sp5)} (hm : LEv.out γ .d1 ∈ l) (u : O8) :
    ¬ τ.R .k2 u := by
  intro hu
  have h1 := lrun_out_mem h hm .k2 u hu
  have h2 := τ.sub _ _ hu
  cases u <;> revert h1 h2 <;> decide

theorem emit_d2_seals_k1 {D : Type} {n : Nat} {σ τ : State sp5} {l : List (LEv sp5 D n)}
    (h : LRun σ l τ) {γ : List (Commitment sp5)} (hm : LEv.out γ .d2 ∈ l) (u : O8) :
    ¬ τ.R .k1 u := by
  intro hu
  have h1 := lrun_out_mem h hm .k1 u hu
  have h2 := τ.sub _ _ hu
  cases u <;> revert h1 h2 <;> decide

/-! ### With other commitments, RPC does not imply confluence -/

abbrev uSpec : Spec In2 Unit := ⟨fun _ _ => True, fun _ => ⟨(), trivial⟩⟩

def sealHiState (σ : State uSpec) (h : σ.cur = .lo) : State uSpec where
  cur := σ.cur
  R := fun k u => σ.R k u ∧ k = .lo
  sub := fun k u h => σ.sub k u h.1
  hasCur := by obtain ⟨o, ho⟩ := σ.hasCur; exact ⟨o, ho, h⟩
  above := fun k u h => σ.above k u h.1

open Classical in
/-- A seal of `hi` at current input `lo`. -/
noncomputable def sealHi : Commitment uSpec where
  f := fun σ => if h : σ.cur = .lo ∧ ∃ u, σ.R .hi u then some (sealHiState σ h.1) else none
  cur_eq := by
    intro σ τ h; split at h
    · cases h; rfl
    · cases h
  sub := by
    intro σ τ h; split at h
    · cases h; exact fun k u h => h.1
    · cases h
  strict := by
    intro σ τ h; split at h
    · rename_i hh; cases h
      obtain ⟨u, hu⟩ := hh.2
      exact ⟨.hi, u, hu, fun h => by cases h.2⟩
    · cases h
  excl := by
    intro σ τ h; split at h
    · cases h
      intro k u w hu hnu hw
      exact absurd ⟨hu, hw.2⟩ hnu
    · cases h

theorem sealHi_apply :
    applySeq (canon uSpec .lo) [sealHi] = some (sealHiState (canon uSpec .lo) rfl) := by
  have hf : sealHi.f (canon uSpec .lo) = some (sealHiState (canon uSpec .lo) rfl) := by
    simp only [sealHi]
    rw [dite_eq_left_of_eq_true (eq_true ⟨rfl, (), trivial, rfl⟩)]
  simp only [applySeq, hf]

noncomputable def rnSys : System uSpec Unit := ⟨fun c => c = sealHi, fun _ _ _ _ _ => True⟩

noncomputable def rnH : History uSpec Unit 2 :=
  fun p => if p.val = 0 then [LEv.out [sealHi] ()] else []

theorem rnH_run : ∃ τ, LRun (canon uSpec .lo) [LEv.out (D := Unit) (n := 2) [sealHi] ()] τ := by
  let σc := sealHiState (canon uSpec .lo) rfl
  have hc : σc.R σc.cur () := ⟨⟨trivial, rfl⟩, rfl⟩
  have hexp : Exposable σc () := by
    intro k x _ hn; exact absurd trivial hn
  exact ⟨outSt σc () hc, .out sealHi_apply (Step.output σc (outSt σc () hc) () hc rfl rfl) hexp
    (.nil _)⟩

/-- Remark after Def. `def:response-partition-consistency`, last sentence:
with other commitments the converse can fail.  Participant `0` emits `()` at
`lo` while sealing `hi`; the emitted outputs have a common refinement at `hi`,
but the cut is not confluent at `hi`. -/
theorem rpc_not_confluent :
    WF (fun _ => In2.lo) rnH ∧ Produced rnSys 2 (fun _ => In2.lo) rnH ∧
      Partitioned rnH (fun p => p.val) ∧ IsCut rnH (fun p => (rnH p).length) ∧
      (∀ p σ, LRun (canon uSpec ((fun _ => In2.lo) p)) ((rnH p).take (rnH p).length) σ →
        σ.cur ≼ In2.hi) ∧
      RPCAt rnH (fun p => (rnH p).length) .hi ∧
      ¬ ConfluentCut (fun _ => In2.lo) rnH (fun p => (rnH p).length) .hi := by
  have h0 : rnH 0 = [LEv.out [sealHi] ()] := rfl
  have h1 : rnH 1 = [] := rfl
  have hp : ∀ p : Fin 2, p = 0 ∨ p = 1 := by decide
  obtain ⟨g1, g2, g3, g4⟩ := locality_glue rnSys (init := fun _ => In2.lo) rnH _ (two_labels (by omega))
    (fun p => by rcases hp p with rfl | rfl <;> simp [h0, h1])
    (fun p => by
      rcases hp p with rfl | rfl
      · rw [h0]; intro a e b h
        cases a with
        | nil =>
          simp at h; obtain ⟨rfl, _⟩ := h
          exact ⟨fun c hc => by simp at hc; exact hc, trivial⟩
        | cons _ _ => simp at h
      · rw [h1]; intro a e b h; simp at h)
    (fun p => by
      rcases hp p with rfl | rfl
      · rw [h0]; exact rnH_run
      · rw [h1]; exact ⟨_, .nil _⟩)
  refine ⟨g1, g2, g3, g4, ?_, ⟨(), trivial, fun _ _ _ _ => trivial⟩, ?_⟩
  · intro p σ _
    show In2.leB σ.cur .hi = true
    generalize σ.cur = x; cases x <;> rfl
  · rintro ⟨H', ext, τ, hext, _, hτj, hτ⟩
    have hr := hτ 0
    rw [hext 0] at hr
    have ht : (rnH 0).take (rnH 0).length = [LEv.out [sealHi] ()] := by rw [h0]; rfl
    rw [ht, List.singleton_append] at hr
    cases hr with
    | out ha hs _ hr' =>
      have he := Option.some.inj (ha.symm.trans sealHi_apply)
      subst he
      obtain ⟨u, hu⟩ := τ.hasCur
      rw [hτj] at hu
      have := step_sub hs _ _ ((lrun_mono hr').2 _ _ hu)
      cases this.2

/-! ### The election under the equality order -/

inductive Cand | x | y
  deriving DecidableEq

/-- Outputs `⊥`, `x`, `y` under the equality order. -/
inductive Win | bot | x | y
  deriving DecidableEq

instance : PO Win where
  le a b := a = b
  refl _ := rfl
  trans h1 h2 := h1.trans h2
  antisymm h _ := h

/-- A ballot slot grows from "not yet received" to a fixed ballot. -/
def OExt (a b : Option Cand) : Prop := a = none ∨ a = b

theorem oext_trans {a b c : Option Cand} (h1 : OExt a b) (h2 : OExt b c) : OExt a c := by
  rcases h1 with rfl | rfl
  · exact Or.inl rfl
  · exact h2

theorem oext_antisymm {a b : Option Cand} (h1 : OExt a b) (h2 : OExt b a) : a = b := by
  rcases h1 with rfl | rfl
  · rcases h2 with h | h <;> exact h.symm
  · rfl

/-- The ballots of three voters. -/
structure Ballots where
  b1 : Option Cand
  b2 : Option Cand
  b3 : Option Cand

instance : PO Ballots where
  le u v := OExt u.b1 v.b1 ∧ OExt u.b2 v.b2 ∧ OExt u.b3 v.b3
  refl _ := ⟨Or.inr rfl, Or.inr rfl, Or.inr rfl⟩
  trans h1 h2 := ⟨oext_trans h1.1 h2.1, oext_trans h1.2.1 h2.2.1, oext_trans h1.2.2 h2.2.2⟩
  antisymm := by
    intro u v h1 h2
    cases u with
    | mk x1 x2 x3 =>
      cases v with
      | mk y1 y2 y3 =>
        have e1 : x1 = y1 := oext_antisymm h1.1 h2.1
        have e2 : x2 = y2 := oext_antisymm h1.2.1 h2.2.1
        have e3 : x3 = y3 := oext_antisymm h1.2.2 h2.2.2
        subst e1 e2 e3; rfl

def cnt (c : Cand) (v : Ballots) : Nat :=
  (if v.b1 = some c then 1 else 0) + (if v.b2 = some c then 1 else 0) +
    (if v.b3 = some c then 1 else 0)

/-- The candidate with two ballots, or `⊥`. -/
def winner (v : Ballots) : Win :=
  if 2 ≤ cnt .x v then .x else if 2 ≤ cnt .y v then .y else .bot

/-- The election of Figure `fig:nonmonotone-frame` (equality order on outputs). -/
def electionEq : Spec Ballots Win := ⟨fun v o => o = winner v, fun v => ⟨winner v, rfl⟩⟩

def bXY : Ballots := ⟨some .x, some .y, none⟩
def bXYX : Ballots := ⟨some .x, some .y, some .x⟩

/-- Input acceptance excludes the election under the equality order: at
`xy·` the only answer is `⊥`, which has no refinement at `xyx`; so no system
has Response Availability for any obligation contained in `S`. -/
theorem election_eq_no_ra {D : Type} (Sys : System electionEq D)
    (Q : (n : Nat) → Fin n → Table Ballots Win) (hQ : ∀ n p i o, Q n p i o → electionEq.S i o) :
    ¬ ResponseAvailability Sys Q := by
  apply ra_excludes_forced_seal Sys Q (i := bXY) (j := bXYX) ⟨Or.inr rfl, Or.inr rfl, Or.inl rfl⟩
  rintro o ho ⟨u, hu, hle⟩
  have h1 : o = winner bXY := hQ _ _ _ _ ho
  have h2 : u = winner bXYX := hu
  have h3 : o = u := hle
  rw [h1, h2] at h3
  exact absurd h3 (by decide)

end Examples

/-! ## Remark "Without replication": counterexample to the stated form -/

section NonRepCounter

inductive O4 | a | b | a2 | b2
  deriving DecidableEq

def O4.leB : O4 → O4 → Bool
  | .a, .a | .b, .b | .a2, .a2 | .b2, .b2 => true
  | .a, .a2 | .b, .b2 => true
  | _, _ => false

instance : PO O4 where
  le x y := O4.leB x y = true
  refl x := by cases x <;> rfl
  trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  antisymm := by intro x y; cases x <;> cases y <;> decide

instance (x y : O4) : Decidable (x ≼ y) := inferInstanceAs (Decidable (O4.leB x y = true))

def s4B : In2 → O4 → Bool
  | .lo, .a | .lo, .b | .hi, .a2 | .hi, .b2 => true
  | _, _ => false

abbrev sp4 : Spec In2 O4 :=
  ⟨fun i o => s4B i o = true, by intro i; cases i; exact ⟨.a, rfl⟩; exact ⟨.a2, rfl⟩⟩

abbrev Q4 : Obligation sp4 := ⟨sp4.S, fun _ _ h => h, sp4.total, fun _ _ _ _ h _ => h⟩

def taB : In2 → O4 → Bool
  | .lo, .a | .hi, .a2 => true
  | _, _ => false

def tbB : In2 → O4 → Bool
  | .lo, .b | .hi, .b2 => true
  | _, _ => false

abbrev Ta4 : Table In2 O4 := fun i o => taB i o = true
abbrev Tb4 : Table In2 O4 := fun i o => tbB i o = true

theorem Ta4_ok : ResponseInterface Q4 Ta4 ∧ ConsistentOn sp4 Ta4 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro i o h; cases i <;> cases o <;> revert h <;> decide
  · intro i; cases i
    · exact ⟨.a, rfl⟩
    · exact ⟨.a2, rfl⟩
  · intro i o j h hij
    cases i <;> cases o <;> cases j <;>
      first
        | exact absurd h (by decide)
        | exact absurd hij (by decide)
        | exact ⟨.a, rfl, rfl⟩
        | exact ⟨.a2, rfl, rfl⟩
  · apply consistentOn_of_bound
    intro j; cases j
    · exact ⟨.a, rfl, by intro i o h hi; cases i <;> cases o <;> revert h hi <;> decide⟩
    · exact ⟨.a2, rfl, by intro i o h hi; cases i <;> cases o <;> revert h hi <;> decide⟩

theorem Tb4_ok : ResponseInterface Q4 Tb4 ∧ ConsistentOn sp4 Tb4 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro i o h; cases i <;> cases o <;> revert h <;> decide
  · intro i; cases i
    · exact ⟨.b, rfl⟩
    · exact ⟨.b2, rfl⟩
  · intro i o j h hij
    cases i <;> cases o <;> cases j <;>
      first
        | exact absurd h (by decide)
        | exact absurd hij (by decide)
        | exact ⟨.b, rfl, rfl⟩
        | exact ⟨.b2, rfl, rfl⟩
  · apply consistentOn_of_bound
    intro j; cases j
    · exact ⟨.b, rfl, by intro i o h hi; cases i <;> cases o <;> revert h hi <;> decide⟩
    · exact ⟨.b2, rfl, by intro i o h hi; cases i <;> cases o <;> revert h hi <;> decide⟩

/-- Which interface the system follows: for two participants with different
initial inputs `Tb`, otherwise `Ta`.  (Allowed by
the system assumption after Def. `def:partitioned-history`: one strategy per participant set and choice of
initial inputs.) -/
def Tsel (n : Nat) (init : Fin n → In2) : Table In2 O4 :=
  if h : 2 ≤ n then (if init ⟨0, by omega⟩ = init ⟨1, by omega⟩ then Ta4 else Tb4) else Ta4

theorem Tsel_ok (n : Nat) (init : Fin n → In2) :
    ResponseInterface Q4 (Tsel n init) ∧ ConsistentOn sp4 (Tsel n init) := by
  unfold Tsel
  split
  · split
    · exact Ta4_ok
    · exact Tb4_ok
  · exact Ta4_ok

noncomputable def mixSys : System sp4 Unit where
  basis := fun c => ∃ u, c = kc u
  strat := fun n init p pre e => respF (Tsel n init) (init p) (pre.map LEv.erase) e.erase

theorem mixSys_ra : ResponseAvailability mixSys (fun _ _ => Q4.Q) :=
  ra_pointwise fun n init => ⟨respSystem (Tsel n init), rfl, rfl,
    (response_sufficient Q4 (Tsel n init) (Tsel_ok n init).1 (Tsel_ok n init).2).2.1⟩

theorem mixSys_rpc : ResponsePC mixSys :=
  rpc_pointwise fun n init => ⟨respSystem (Tsel n init), rfl, rfl,
    (response_sufficient Q4 (Tsel n init) (Tsel_ok n init).1 (Tsel_ok n init).2).2.2⟩

/-- A single canonical emission from the empty cut is an isolated emission. -/
theorem single_emit {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type} (Sys : System sp D)
    {n : Nat} (h2 : 2 ≤ n) (init : Fin n → I) (p : Fin n) {o : O}
    (ho : (canon sp (init p)).R (init p) o)
    (hA : ∀ γ, (γ = [] ∨ γ = [kc o]) → Allowed Sys n init p [] (.out γ o)) :
    IsoEmitAt Sys n p (init p) o := by
  classical
  obtain ⟨γ, σc, hγ, ha, hco, hexp⟩ := kc_legal ho
  have hcc : σc.cur = init p := (applySeq_spec γ _ σc ha).1
  have hrun : LRun (D := D) (n := n) (canon sp (init p)) [LEv.out γ o] (outSt σc o hco) :=
    .out ha (Step.output σc (outSt σc o hco) o hco rfl rfl) hexp (.nil _)
  let L : History sp D n := fun q => if q = p then [LEv.out γ o] else []
  have hLp : L p = [LEv.out γ o] := by simp [L]
  have hLq : ∀ q, q ≠ p → L q = [] := fun q h => by simp [L, h]
  obtain ⟨g1, g2, g3, _⟩ := locality_glue Sys (init := init) L _ (two_labels h2)
    (fun q => by
      by_cases hq : q = p
      · rw [hq, hLp]; simp
      · rw [hLq q hq]; simp)
    (fun q => by
      by_cases hq : q = p
      · rw [hq, hLp]; intro a e b h
        cases a with
        | nil => simp at h; obtain ⟨rfl, _⟩ := h; exact hA γ hγ
        | cons _ _ => simp at h
      · rw [hLq q hq]; intro a e b h; simp at h)
    (fun q => by
      by_cases hq : q = p
      · rw [hq, hLp]; exact ⟨_, hrun⟩
      · rw [hLq q hq]; exact ⟨_, .nil _⟩)
  exact ⟨init, L, _, [], [], γ, canon sp (init p), g1, g2, g3, hLp,
    fun _ _ _ _ h => (by cases h), .nil _, rfl⟩

/-- **Counterexample to Remark "Without replication" as stated.**  A
(non-replicated) system has Response Availability and Response Partition
Consistency, yet the family `(lo, b) ∈ T₀`, `(lo, a) ∈ T₁` — drawing on each
`T_p` once, with common expansion `lo` — has no common refinement at any
input.  The witnesses come from different choices of initial inputs, on which
the strategies depend. -/
theorem without_replication_counterexample :
    ResponseAvailability mixSys (fun _ _ => Q4.Q) ∧ ResponsePC mixSys ∧
    Tp mixSys (fun _ _ => Q4.Q) 2 0 .lo .b ∧ Tp mixSys (fun _ _ => Q4.Q) 2 1 .lo .a ∧
    ∀ j u, sp4.S j u → ¬ (O4.b ≼ u ∧ O4.a ≼ u) := by
  refine ⟨mixSys_ra, mixSys_rpc, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ?_⟩
  · have := single_emit mixSys (n := 2) (by omega) (fun q => if q.val = 0 then .lo else .hi) 0
      (o := .b) ⟨rfl, rfl⟩ (by
        intro γ hγ
        refine ⟨?_, ?_⟩
        · intro c hc; rcases hγ with rfl | rfl
          · cases hc
          · simp at hc; exact ⟨_, hc⟩
        · exact ⟨hγ, rfl, by simp [emittedOf]⟩)
    exact this
  · have := single_emit mixSys (n := 2) (by omega) (fun _ => .lo) 1
      (o := .a) ⟨rfl, rfl⟩ (by
        intro γ hγ
        refine ⟨?_, ?_⟩
        · intro c hc; rcases hγ with rfl | rfl
          · cases hc
          · simp at hc; exact ⟨_, hc⟩
        · exact ⟨hγ, rfl, by simp [emittedOf]⟩)
    exact this
  · intro j u hu h; cases j <;> cases u <;> revert hu h <;> decide

end NonRepCounter

/-! ## Gilbert–Lynch -/

section GLSection

open GL

variable {D : Type}

/-- "A single emitted output has no refinement in the fiber at some expansion
of its input, a failure of Relational Monotonicity." -/
theorem reg_not_relMono : ¬ regSpec.RelMono := by
  intro h
  obtain ⟨o, ho⟩ := regQ_total 1 h2
  obtain ⟨u, hu, hle⟩ := h h2 hj o h2_le ho.1
  exact hj_noread u hu (hle 1 _ (h2_answer ho))

/-- The realized-history computation of the corollary's proof: in the
two-replica history (write invoked and answered at `p`, read invoked at `q`,
then only non-input events), the full prefix of the interleaving "all of `p`,
then all of `q`" has realized history `j` (write, read, write → read), which
expands both current inputs; so atomicity gives RPC at `j` there. -/
theorem final_rpc (Sys : System regSpec D) (hRPC : RealizedRPC Sys) {init : Fin 2 → Hist}
    {H : RHist D 2} {comp : Fin 2 → Nat}
    (hwf : WF init H) (hprod : Produced Sys 2 init H) (hpart : Partitioned H comp)
    (hinj : ∀ p q, comp p = comp q → p = q)
    {A B : List (LEv regSpec D 2)} (hA : H 0 = LEv.inp h1 :: A) (hB : H 1 = LEv.inp h2 :: B)
    (hAi : ∀ j, LEv.inp j ∉ A) (hBi : ∀ j, LEv.inp j ∉ B)
    {γ : List (Commitment regSpec)} {o : RMap}
    (ho : LEv.out γ o ∈ A) (hoQ : regQ 0 h1 o) :
    RPCAt H (fun p => (H p).length) hj := by
  have hnr := norecv_of_inj hwf hpart hinj
  have inp0 : ∀ k h, (H 0)[k]? = some (LEv.inp h) → k = 0 ∧ h = h1 := by
    intro k h hk
    rw [hA] at hk
    obtain ⟨hk0, he⟩ := inp_head (P := fun x => ∃ h, x = LEv.inp h)
      (fun x ⟨h, hx⟩ => hx ▸ hAi h) hk ⟨h, rfl⟩
    cases he; exact ⟨hk0, rfl⟩
  have inp1 : ∀ k h, (H 1)[k]? = some (LEv.inp h) → k = 0 ∧ h = h2 := by
    intro k h hk
    rw [hB] at hk
    obtain ⟨hk0, he⟩ := inp_head (P := fun x => ∃ h, x = LEv.inp h)
      (fun x ⟨h, hx⟩ => hx ▸ hBi h) hk ⟨h, rfl⟩
    cases he; exact ⟨hk0, rfl⟩
  have hL0 : (H 0).length = A.length + 1 := by rw [hA]; rfl
  have hL1 : (H 1).length = B.length + 1 := by rw [hB]; rfl
  let L0 := (H 0).length
  let m := (H 0).length + (H 1).length
  have p0 : ∀ k, pos2 L0 0 k = k := fun k => by simp [pos2]
  have p1 : ∀ k, pos2 L0 1 k = L0 + k := fun k => by simp [pos2]
  have il : Interleaving H (pos2 L0) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p k p' k' hk hk' he
      rcases fin2 p with rfl | rfl <;> rcases fin2 p' with rfl | rfl <;>
        simp only [p0, p1] at he <;> refine ⟨?_, ?_⟩ <;> first | rfl | omega
    · intro p k k' hkk _
      rcases fin2 p with rfl | rfl <;> simp only [p0, p1] <;> omega
    · intro p k q k' j d h
      exact absurd h (hnr p k q k' j d)
  have pc : PrefixCut H (pos2 L0) m (fun p => (H p).length) := by
    intro p
    refine ⟨Nat.le_refl _, fun k hk => ⟨fun _ => ?_, fun _ => hk⟩⟩
    rcases fin2 p with rfl | rfl <;> simp only [p0, p1] <;> omega
  have hr : Realized H (pos2 L0) m hj := by
    constructor
    · intro a op
      constructor
      · intro h
        rcases hj_ops h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨0, 0, by rw [p0]; omega, rfl, h1, by rw [hA]; rfl, rfl⟩
        · exact ⟨1, 0, by rw [p1]; omega, rfl, h2, by rw [hB]; rfl, rfl⟩
      · rintro ⟨p, k, _, _, h, hk, hop⟩
        rcases fin2 p with rfl | rfl
        · obtain ⟨_, rfl⟩ := inp0 k h hk
          obtain ⟨rfl, rfl⟩ := h1_ops hop; rfl
        · obtain ⟨_, rfl⟩ := inp1 k h hk
          obtain ⟨rfl, rfl⟩ := h2_ops hop; rfl
    · intro a b
      constructor
      · rintro ⟨rfl, rfl⟩
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ho
        have hkA := (List.getElem?_eq_some_iff.1 hk).1
        refine ⟨wOp, rOp, rfl, rfl, 0, k + 1,
          ⟨rfl, γ, o, by rw [hA]; simpa using hk, hoQ.2 0 wOp rfl rfl⟩, ?_⟩
        rintro p' k' ⟨hrep, _⟩
        have : p' = 1 := Fin.ext hrep
        subst this
        rw [p0, p1]
        omega
      · rintro ⟨opa, opb, ha, hb, p, k, ⟨hrep, _⟩, hall⟩
        rcases hj_ops hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have := hall 0 0 ⟨rfl, h1, by rw [hA]; rfl, rfl⟩
          rw [p0] at this; omega
        · rcases hj_ops ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨rfl, rfl⟩
          · have hp : p = 1 := Fin.ext hrep
            subst hp
            have := hall 1 0 ⟨rfl, h2, by rw [hB]; rfl, rfl⟩
            rw [p1, p1] at this; omega
  have hcur : ∀ p σ, LRun (canon regSpec (init p)) ((H p).take (H p).length) σ → σ.cur ≼ hj := by
    intro p σ hσ
    rw [List.take_length] at hσ
    rcases fin2 p with rfl | rfl
    · rw [hA] at hσ
      cases hσ with
      | inp hs hr => rw [lrun_noinp hr hAi, (step_input_inv hs).2.1]; exact h1_le
    · rw [hB] at hσ
      cases hσ with
      | inp hs hr => rw [lrun_noinp hr hBi, (step_input_inv hs).2.1]; exact h2_le
  exact hRPC 2 init H comp hwf hprod hpart (pos2 L0) il m _ pc hj hr hcur

/-- **Corollary `cor:gilbert-lynch`, along the paper's proof**: from Answering
alone (no Input acceptance), via `forced_answer` (Lemma
`lem:forced-answer`). -/
theorem gilbert_lynch_answering (Sys : System regSpec D) :
    ¬ (Answering Sys regQn ∧ RealizedRPC Sys) := by
  rintro ⟨hAns, hRPC⟩
  let init : Fin 2 → Hist := fun _ => emptyH
  let comp : Fin 2 → Nat := fun p => p.val
  have hinj : ∀ p q : Fin 2, comp p = comp q → p = q := fun p q h => Fin.ext h
  have h01 : comp 1 ≠ comp 0 := by decide
  have h10 : comp 0 ≠ comp 1 := by decide
  let H0 : RHist D 2 := fun _ => []
  have wf0 : WF init H0 :=
    ⟨fun p => ⟨_, LRun.nil _⟩, fun p a q k j d b h => absurd h nil_ne_app⟩
  have prod0 : Produced Sys 2 init H0 := fun p a e b h => absurd h nil_ne_app
  have part0 : Partitioned H0 comp :=
    ⟨⟨0, 1, by decide⟩, fun p a q k j d b h => absurd h nil_ne_app⟩
  have cut0 : IsCut H0 (fun _ => 0) :=
    ⟨fun _ => Nat.zero_le _, fun p a q k j d b h => absurd h nil_ne_app⟩
  -- the environment invokes the write at `p`
  obtain ⟨u1, hu1⟩ := regSpec.total h1
  have hR1 : (canon regSpec emptyH).R h1 u1 := ⟨hu1, empty_le h1⟩
  obtain ⟨H1, ext1, hext1, wf1, prod1, part1, he10, he1q⟩ :=
    extend_single Sys wf0 prod0 part0 cut0 (p := 0) (σ := canon regSpec emptyH)
      (LRun.nil _) (e := LEv.inp h1) (by intro q k j d h; cases h) (inp_lrun hR1) trivial
  have e10 : H1 0 = [LEv.inp h1] := by rw [hext1 0, he10]; rfl
  have e11 : H1 1 = [] := by rw [hext1 1, he1q 1 (by decide)]; rfl
  -- Answering at `p`: `p` acknowledges the write
  have hτ1 : LRun (canon regSpec (init 0)) ((H1 0).take (H1 0).length)
      (inpState (canon regSpec emptyH) h1 u1 hR1) := by
    rw [List.take_length, e10]; exact inp_lrun hR1
  obtain ⟨H2, ext2, hext2, wf2, prod2, part2, hloc2, hni2, γ, o, hQo, hmo⟩ :=
    hAns 2 init H1 comp wf1 prod1 part1 _ (full_cut wf1) 0 _ hτ1
  have hQo : regQ 0 h1 o := hQo
  have e20 : H2 0 = LEv.inp h1 :: ext2 0 := by
    rw [hext2 0, List.take_length, e10]; rfl
  have e21 : H2 1 = [] := by
    rw [hext2 1, List.take_length, e11, hloc2 1 h01]; rfl
  -- the environment invokes the read at `q`, after the acknowledgment
  obtain ⟨u2, hu2⟩ := regSpec.total h2
  have hR2 : (canon regSpec emptyH).R h2 u2 := ⟨hu2, empty_le h2⟩
  obtain ⟨H3, ext3, hext3, wf3, prod3, part3, he31, he3q⟩ :=
    extend_single Sys wf2 prod2 part2 (full_cut wf2) (p := 1) (σ := canon regSpec emptyH)
      (by rw [List.take_length, e21]; exact LRun.nil _) (e := LEv.inp h2)
      (by intro q k j d h; cases h) (inp_lrun hR2) trivial
  have e30 : H3 0 = LEv.inp h1 :: ext2 0 := by
    rw [hext3 0, List.take_length, e20, he3q 0 (by decide)]; simp
  have e31 : H3 1 = [LEv.inp h2] := by
    rw [hext3 1, List.take_length, e21, he31]; rfl
  -- Lemma forced-answer at `q`, alone in its block
  have hτ2 : LRun (canon regSpec (init 1)) ((H3 1).take (H3 1).length)
      (inpState (canon regSpec emptyH) h2 u2 hR2) := by
    rw [List.take_length, e31]; exact inp_lrun hR2
  have hcur3 : ∀ p σ, LRun (canon regSpec (init p)) ((H3 p).take (H3 p).length) σ →
      σ.cur ≼ hj := by
    intro p σ hσ
    rw [List.take_length] at hσ
    rcases fin2 p with rfl | rfl
    · rw [e30] at hσ
      cases hσ with
      | inp hs hr => rw [lrun_noinp hr hni2, (step_input_inv hs).2.1]; exact h1_le
    · rw [e31] at hσ
      cases hσ with
      | inp hs hr => cases hr; rw [(step_input_inv hs).2.1]; exact h2_le
  have hno : ∀ o', regQn 2 1 (inpState (canon regSpec emptyH) h2 u2 hR2).cur o' →
      ¬ ∃ u, regSpec.S hj u ∧ o' ≼ u := by
    rintro o' ho' ⟨u, hu, hle⟩
    have ho'' : regQ 1 h2 o' := ho'
    exact hj_noread u hu (hle 1 _ (h2_answer ho''))
  obtain ⟨H4, ext4, hext4, wf4, prod4, part4, hoth4, hni4, _, _, hbad⟩ :=
    forced_answer Sys regQn hAns wf3 prod3 part3 (full_cut wf3) (q := 1)
      (fun p h => hinj p 1 h) hτ2 hcur3 hno
  have e40 : H4 0 = LEv.inp h1 :: ext2 0 := by
    rw [hext4 0, List.take_length, e30, hoth4 0 (by decide)]; simp
  have e41 : H4 1 = LEv.inp h2 :: ext4 1 := by
    rw [hext4 1, List.take_length, e31]; rfl
  exact hbad (final_rpc Sys hRPC wf4 prod4 part4 hinj e40 e41 hni2 (hni4 1) hmo hQo)

/-- Corollary `cor:gilbert-lynch` as stated (Response Availability), via the
paper's route. -/
theorem gilbert_lynch_via_forced_answer (Sys : System regSpec D) :
    ¬ (ResponseAvailability Sys regQn ∧ RealizedRPC Sys) :=
  fun ⟨hRA, hRPC⟩ => gilbert_lynch_answering Sys ⟨answering_of_ra hRA, hRPC⟩

/-- Def. `def:response-obligation` for the register: each `Q_p` is contained in
`S`, total, and upward closed within fibers. -/
theorem regQ_obligation (p : Nat) :
    (∀ h ρ, regQ p h ρ → regS h ρ) ∧ (∀ h, ∃ ρ, regQ p h ρ) ∧
    ∀ h ρ u, regQ p h ρ → regS h u → ρ ≼ u → regQ p h u :=
  ⟨fun _ _ hq => hq.1, regQ_total p, fun _ _ _ hq hu hle => regQ_upward hq hu hle⟩

end GLSection

end CAP
end CC
