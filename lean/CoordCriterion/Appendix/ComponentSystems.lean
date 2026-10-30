import CoordCriterion.Appendix.Components
import CoordCriterion.CAP.ResponseForm
import CoordCriterion.CAP.TimeoutAbort

/-!
# Systems as component implementations (§4.3–4.4, Appendix D)

Namespace `CC.Components`.  A system `CAP.System sp D` (Def. `def:system`)
implements one specification `sp`: every participant works from `sp` and the
basis is shared.  Its participant runs are output-annotated runs under that
basis, so the system is one component implementation of `sp`
(`Component.ofSystemOn`).  Restricting to one-participant histories gives the
process form (`Component.process`); a replicated system
(`CAP.System.Replicated`) gives the cluster form (`Component.cluster`).  The
form is metadata: the admitted runs and their certificates do not depend on it.

* `toSEv`, `toSEvs`, `lrun_sysExec` — a participant run of `CAP/Model.lean`,
  with its sends and receives dropped and commitments transported by
  `Dist.ofCAP`, is an execution under the basis
  (`Dist.sysStep_iff_CAP`, `Dist.sysStep_commit_iff_CAP`).
* `Component.ofSystemOn`, `Component.process`, `Component.cluster`,
  `ofSystem_emptyBasis_commitmentFree`, `cfSystem_replicated`,
  `cfSystem_cluster_commitmentFree`.
* `seal_run`, `sealSys1_process`, `sealSysRepl_replicated`,
  `sealSysRepl_cluster` — the 2PC timeout-abort seal (§4.4).  Run by the
  coordinator alone (`CAP.Timeout.sealSys1`) the decision is a process
  component that admits a run applying a commitment; that seal requires
  coordination but not distributed coordination
  (`CAP.Timeout.sealSys1_local`).  Replicated (`CAP.Timeout.sealSysRepl`) it
  is a cluster component, and the seal requires distributed coordination.
  Commitment, coordination relative to a run universe, and distributed
  coordination inside one component are different properties.

Modeling choice: a component run is one participant's run of a produced,
well-formed history, from the canonical state at that participant's initial
input.  Messages stay inside the component.
-/

namespace CC
namespace Components

open CAP (System LEv LRun History WF Produced)

section Embedding
variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type} {n : Nat}

/-- A local event as a system event: inputs, output events, and commit events
are kept, sends and receives are dropped. -/
def toSEv : LEv sp D n → Option (SEvent sp)
  | .inp j => some (.input j)
  | .out γ o => some (.output (γ.map Dist.ofCAP) o)
  | .cmt γ => some (.commit (γ.map Dist.ofCAP))
  | .send _ _ => none
  | .recv _ _ _ _ => none

/-- A participant's local event list as system events. -/
def toSEvs (l : List (LEv sp D n)) : List (SEvent sp) := l.filterMap toSEv

theorem map_toCAP_ofCAP : ∀ γ : List (CAP.Commitment sp), (γ.map Dist.ofCAP).map Dist.toCAP = γ
  | [] => rfl
  | c :: γ => by simp only [List.map_cons, Dist.toCAP_ofCAP, map_toCAP_ofCAP γ]

/-- **A participant run is an execution under the basis.**  If every
commitment its output and commit events apply satisfies `P`, the translated
run is an execution under `{c | P (toCAP c)}`. -/
theorem lrun_sysExec (P : CAP.Commitment sp → Prop) {σ τ : State sp} {l : List (LEv sp D n)}
    (h : LRun σ l τ) (hB : ∀ γ o, LEv.out γ o ∈ l → ∀ c ∈ γ, P c)
    (hC : ∀ γ, LEv.cmt γ ∈ l → ∀ c ∈ γ, P c) :
    SysExec (fun c => P (Dist.toCAP c)) σ (toSEvs l) τ := by
  induction h with
  | nil => exact .nil _
  | inp hs _ ih =>
    exact .cons (.input hs) (ih (fun γ o hm => hB γ o (List.mem_cons_of_mem _ hm))
      (fun γ hm => hC γ (List.mem_cons_of_mem _ hm)))
  | @out σ σc τ' ρ γ o es ha hs hx _ ih =>
    have hb : ∀ c ∈ γ.map Dist.ofCAP, P (Dist.toCAP c) := by
      intro c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      rw [Dist.toCAP_ofCAP]
      exact hB γ o List.mem_cons_self c' hc'
    have hst : SysStep (fun c => P (Dist.toCAP c)) σ (.output (γ.map Dist.ofCAP) o) τ' :=
      Dist.sysStep_iff_CAP.2 ⟨hb, σc, by rw [map_toCAP_ofCAP]; exact ha, hs, hx⟩
    exact .cons hst (ih (fun γ o hm => hB γ o (List.mem_cons_of_mem _ hm))
      (fun γ hm => hC γ (List.mem_cons_of_mem _ hm)))
  | @cmt σ τ' ρ γ es hne ha _ ih =>
    have hb : ∀ c ∈ γ.map Dist.ofCAP, P (Dist.toCAP c) := by
      intro c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      rw [Dist.toCAP_ofCAP]
      exact hC γ List.mem_cons_self c' hc'
    have hne' : γ.map Dist.ofCAP ≠ [] := fun h => hne (List.map_eq_nil_iff.1 h)
    have hst : SysStep (fun c => P (Dist.toCAP c)) σ (.commit (γ.map Dist.ofCAP)) τ' :=
      Dist.sysStep_commit_iff_CAP.2 ⟨hb, hne', by rw [map_toCAP_ofCAP]; exact ha⟩
    exact .cons hst (ih (fun γ o hm => hB γ o (List.mem_cons_of_mem _ hm))
      (fun γ hm => hC γ (List.mem_cons_of_mem _ hm)))
  | send _ ih =>
    exact ih (fun γ o hm => hB γ o (List.mem_cons_of_mem _ hm))
      (fun γ hm => hC γ (List.mem_cons_of_mem _ hm))
  | recv _ ih =>
    exact ih (fun γ o hm => hB γ o (List.mem_cons_of_mem _ hm))
      (fun γ hm => hC γ (List.mem_cons_of_mem _ hm))

/-- **A system as a component implementation.**  Its basis is the system's,
and it admits the runs of participants of produced, well-formed histories
with a participant count in `N`, with a named output that is a row at the
participant's initial input. -/
def Component.ofSystemOn (Sys : System sp D) (N : Nat → Prop)
    (location : Option LocationForm := none) : Component sp where
  location := location
  basis c := Sys.basis (Dist.toCAP c)
  accepts r := ∃ (n : Nat) (init : Fin n → I) (H : History sp D n) (p : Fin n),
    N n ∧ WF init H ∧ Produced Sys n init H ∧ r.input = init p ∧ r.events = toSEvs (H p) ∧
      LRun (canon sp (init p)) (H p) r.final ∧ (∃ γ, SEvent.output γ r.output ∈ r.events) ∧
      sp.S r.input r.output
  sound := by
    rintro r ⟨n, init, H, p, _, _, hp, hin, hev, hl, he, hc⟩
    refine ⟨?_, he, hc⟩
    rw [hin, hev]
    refine lrun_sysExec Sys.basis hl (fun γ o hm => ?_) (fun γ hm => ?_)
    · obtain ⟨a, b, hab⟩ := List.append_of_mem hm
      exact (hp p a _ b hab).1
    · obtain ⟨a, b, hab⟩ := List.append_of_mem hm
      exact (hp p a _ b hab).1

/-- The **process** form: the system's one-participant histories. -/
def Component.process (Sys : System sp D) : Component sp :=
  Component.ofSystemOn Sys (· = 1) (some .process)

/-- The **cluster** form of a replicated system: histories with any number of
participants sharing one strategy. -/
def Component.cluster (Sys : System sp D) (_h : Sys.Replicated) : Component sp :=
  Component.ofSystemOn Sys (fun _ => True) (some .cluster)

theorem Component.ofSystemOn_accepts (Sys : System sp D) (N : Nat → Prop)
    (location : Option LocationForm) (r : OperationalRun sp) :
    (Component.ofSystemOn Sys N location).accepts r ↔
      ∃ (n : Nat) (init : Fin n → I) (H : History sp D n) (p : Fin n),
        N n ∧ WF init H ∧ Produced Sys n init H ∧ r.input = init p ∧ r.events = toSEvs (H p) ∧
        LRun (canon sp (init p)) (H p) r.final ∧ (∃ γ, SEvent.output γ r.output ∈ r.events) ∧
        sp.S r.input r.output := Iff.rfl

/-- A system with the empty basis is a commitment-free implementation, in
every form. -/
theorem ofSystem_emptyBasis_commitmentFree (Sys : System sp D) (hB : ∀ c, ¬ Sys.basis c)
    (N : Nat → Prop) (location : Option LocationForm) :
    (Component.ofSystemOn Sys N location).CommitmentFree := by
  intro r h
  have hx := ((Component.ofSystemOn Sys N location).sound r h).legal
  have hx' : SysExec (emptyBasis sp) (canon sp r.input) r.events r.final := by
    have e : (Component.ofSystemOn Sys N location).basis = emptyBasis sp :=
      funext fun c => propext ⟨fun h => hB _ h, False.elim⟩
    rw [e] at hx; exact hx
  exact sysExec_emptyBasis_coordFree hx'

/-- The commitment-free system of Theorem `thm:complete-cap` is replicated. -/
theorem cfSystem_replicated (sp : Spec I O) (D : Type) : (CAP.cfSystem sp D).Replicated :=
  ⟨fun _ _ _ => True, fun _ _ _ _ _ => Iff.rfl⟩

/-- Its cluster form is a commitment-free implementation. -/
theorem cfSystem_cluster_commitmentFree (sp : Spec I O) (D : Type) :
    (Component.cluster (CAP.cfSystem sp D) (cfSystem_replicated sp D)).CommitmentFree :=
  ofSystem_emptyBasis_commitmentFree _ (fun _ h => h) _ _

end Embedding

/-! ## The timeout abort run by the coordinator alone -/

section Timeout
open CAP CAP.Timeout

/-- A system whose coordinator may close the polls at `yy·` when it runs
alone admits, in any form that allows one participant, a run applying a
commitment. -/
theorem seal_run (D : Type) (Sys : System (voteSpec 3) D) (hb : Sys.basis cp)
    (hs : Sys.strat 1 (fun _ => yyN) 0 [] (.out [cp] .undecided)) (N : Nat → Prop) (hN : N 1)
    (location : Option LocationForm) :
    ∃ r, (Component.ofSystemOn Sys N location).accepts r ∧ Coordinates r.events := by
  obtain ⟨happ, _, _, _⟩ := timeout_seals yyN 2 rfl
  obtain ⟨-, -, -, -, hrows⟩ := timeout_seals_yy
  let σ := canon (voteSpec 3) yyN
  let σc := Figures.closeState σ
  have ha : CAP.applySeq σ [cp] = some σc := by
    simp only [CAP.applySeq]
    rw [show cp.f σ = some σc from happ]
  have hu : σc.R σc.cur .undecided := (hrows _ _).2 ⟨rfl, rfl⟩
  have hex : Exposable σc .undecided := fun _ _ _ hn => absurd (Or.inl rfl) hn
  obtain ⟨τ0, hr0⟩ := lrun_out (D := D) (n := 1) ha hu hex
  let H : History (voteSpec 3) D 1 := fun _ => [LEv.out [cp] .undecided]
  have hw : WF (fun _ => yyN) H := by
    refine ⟨fun _ => ⟨τ0, hr0⟩, fun r a q k j d b h => ?_⟩
    have hm : LEv.recv q k j d ∈ H r := by rw [h]; simp
    simp [H] at hm
  have hp : Produced Sys 1 (fun _ => yyN) H := by
    intro r a e b h
    have hr : r = 0 := Subsingleton.elim _ _
    subst hr
    cases a with
    | nil =>
      simp [H] at h; obtain ⟨rfl, _⟩ := h
      exact ⟨fun c hc => by simp at hc; subst hc; exact hb, hs⟩
    | cons _ _ => simp [H] at h
  let r : OperationalRun (voteSpec 3) := ⟨yyN, .undecided, toSEvs (H 0), τ0⟩
  have hev : r.events = [.output [Dist.ofCAP cp] .undecided] := rfl
  refine ⟨r, (Component.ofSystemOn_accepts _ _ _ _).2 ⟨1, fun _ => yyN, H, 0, hN, hw, hp, rfl,
    rfl, hr0, ⟨_, by rw [hev]; exact List.mem_cons_self⟩, decide_yyN.symm⟩, ?_⟩
  exact Or.inl ⟨_, _, by rw [hev]; exact List.mem_cons_self, List.cons_ne_nil _ _⟩

/-- **The timeout-abort seal as a process component.**  The coordinator alone
running the decision specification (`sealSys1`) is a process component that
admits a run applying a commitment (it closes the polls at `yy·`), so it is
not commitment-free.  That seal requires coordination but not distributed
coordination (`sealSys1_local`). -/
theorem sealSys1_process (D : Type) :
    (∃ r, (Component.process (sealSys1 D)).accepts r ∧ Coordinates r.events) ∧
      ¬ (Component.process (sealSys1 D)).CommitmentFree ∧
      ¬ (sealSys1 D).CoordinationFree ∧ (sealSys1 D).CoordinationFreeH := by
  obtain ⟨r, hacc, hco⟩ := seal_run D (sealSys1 D) rfl ⟨rfl, rfl, rfl, rfl⟩ (· = 1) rfl
    (some .process)
  exact ⟨⟨r, hacc, hco⟩, fun hcf => (coordFree_iff_not _).1 (hcf r hacc) hco,
    (sealSys1_local D).1, (sealSys1_local D).2⟩

/-- The replicated decision (`sealSysRepl`) is a replicated system. -/
theorem sealSysRepl_replicated (D : Type) : (sealSysRepl D).Replicated :=
  ⟨fun i _ e => match e with
    | .out γ u => γ = [cp] ∧ u = .undecided ∧ i = yyN
    | _ => False,
   fun _ _ _ _ e => by cases e <;> exact Iff.rfl⟩

/-- **The timeout-abort seal as a cluster component.**  Replicated, the same
seal is admitted by the cluster form, and it requires distributed
coordination (`sealSysRepl_not_coordinationFreeH`). -/
theorem sealSysRepl_cluster (D : Type) :
    (∃ r, (Component.cluster (sealSysRepl D) (sealSysRepl_replicated D)).accepts r ∧
      Coordinates r.events) ∧ ¬ (sealSysRepl D).CoordinationFreeH :=
  ⟨seal_run D (sealSysRepl D) rfl ⟨rfl, rfl, rfl⟩ (fun _ => True) trivial (some .cluster),
    sealSysRepl_not_coordinationFreeH D⟩

end Timeout

end Components
end CC
