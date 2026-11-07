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
  (`Dist.sysStep_iff_CAP`, `Dist.sysStep_commitment_iff_CAP`).
* `Component.ofSystemOn`, `Component.process`, `Component.cluster`,
  `ofSystem_emptyCommitmentBasis_commitmentFree`, `cfSystem_replicated`,
  `cfSystem_cluster_commitmentFree`.
* `pollClosing_run`, `pollClosingSys1_process`, `pollClosingSysRepl_replicated`,
  `pollClosingSysRepl_cluster` — the 2PC timeout-abort commitment (§4.3).  Run by the
  coordinator alone (`CAP.Timeout.pollClosingSys1`) the decision is a process
  component that admits a run applying a commitment; that fiber-emptying commitment requires
  coordination but not distributed coordination
  (`CAP.Timeout.pollClosingSys1_local`).  Replicated (`CAP.Timeout.pollClosingSysRepl`) it
  is a cluster component, and the commitment requires distributed coordination.
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

/-- A local event as a system event: inputs, output events, and commitment events
are kept, sends and receives are dropped. -/
def toSEv : LEv sp D n → Option (SEvent sp)
  | .inp j => some (.input j)
  | .out o => some (.output o)
  | .commitment γ => some (.commitment (γ.map Dist.ofCAP))
  | .send _ _ => none
  | .recv _ _ _ _ => none

/-- A participant's local event list as system events. -/
def toSEvs (l : List (LEv sp D n)) : List (SEvent sp) := l.filterMap toSEv

theorem map_toCAP_ofCAP : ∀ γ : List (CAP.Commitment sp), (γ.map Dist.ofCAP).map Dist.toCAP = γ
  | [] => rfl
  | c :: γ => by simp only [List.map_cons, Dist.toCAP_ofCAP, map_toCAP_ofCAP γ]

/-- **A participant run is an execution under the basis.**  If every
commitment its commitment events apply satisfies `P`, and every output event
emits an output that is legal where it occurs or whose canonical commitment
`x_o` (`CAP.kcap o`) satisfies `P`, the translated run is an execution under
`{c | P (toCAP c)}`. -/
theorem lrun_sysExec (P : CAP.Commitment sp → Prop) {σ τ : State sp} {l : List (LEv sp D n)}
    (h : LRun σ l τ)
    (hB : ∀ a o b, l = a ++ LEv.out o :: b → ∀ σ', LRun σ a σ' →
      Exposable σ' o ∨ P (CAP.kcap o))
    (hC : ∀ γ, LEv.commitment γ ∈ l → ∀ c ∈ γ, P c) :
    SysExec (fun c => P (Dist.toCAP c)) σ (toSEvs l) τ := by
  induction h with
  | nil => exact .nil _
  | @inp σ τ' ρ j es hs hr ih =>
    exact .cons (.input hs) (ih (fun a o b he σ' hσ' => hB (.inp j :: a) o b (by rw [he]; rfl) σ'
        (.inp hs hσ')) (fun γ hm => hC γ (List.mem_cons_of_mem _ hm)))
  | @out σ τ' ρ o es hs hr ih =>
    have hb : Exposable σ o ∨ P (Dist.toCAP (Dist.ofCAP (CAP.kcap o))) := by
      rw [Dist.toCAP_ofCAP]; exact hB [] o es rfl σ (.nil _)
    have hst : SysStep (fun c => P (Dist.toCAP c)) σ (.output o) τ' :=
      Dist.sysStep_iff_CAP.2 ⟨hs, hb⟩
    exact .cons hst (ih (fun a o' b he σ' hσ' => hB (.out o :: a) o' b (by rw [he]; rfl) σ'
        (.out hs hσ')) (fun γ hm => hC γ (List.mem_cons_of_mem _ hm)))
  | @commitment σ τ' ρ γ es hne ha hr ih =>
    have hb : ∀ c ∈ γ.map Dist.ofCAP, P (Dist.toCAP c) := by
      intro c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      rw [Dist.toCAP_ofCAP]
      exact hC γ List.mem_cons_self c' hc'
    have hne' : γ.map Dist.ofCAP ≠ [] := fun h => hne (List.map_eq_nil_iff.1 h)
    have hst : SysStep (fun c => P (Dist.toCAP c)) σ (.commitment (γ.map Dist.ofCAP)) τ' :=
      Dist.sysStep_commitment_iff_CAP.2 ⟨hb, hne', by rw [map_toCAP_ofCAP]; exact ha⟩
    exact .cons hst (ih (fun a o b he σ' hσ' => hB (.commitment γ :: a) o b (by rw [he]; rfl) σ'
        (.commitment hne ha hσ')) (fun γ hm => hC γ (List.mem_cons_of_mem _ hm)))
  | @send σ ρ j d es hr ih =>
    exact ih (fun a o b he σ' hσ' => hB (.send j d :: a) o b (by rw [he]; rfl) σ' (.send hσ'))
      (fun γ hm => hC γ (List.mem_cons_of_mem _ hm))
  | @recv σ ρ q k j d es hr ih =>
    exact ih (fun a o b he σ' hσ' => hB (.recv q k j d :: a) o b (by rw [he]; rfl) σ' (.recv hσ'))
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
      LRun (canon sp (init p)) (H p) r.final ∧ (SEvent.output r.output ∈ r.events) ∧
      sp.P r.input r.output
  sound := by
    rintro r ⟨n, init, H, p, _, _, hp, hin, hev, hl, he, hc⟩
    refine ⟨?_, he, hc⟩
    rw [hin, hev]
    refine lrun_sysExec Sys.basis hl (fun a o b hab σ' hσ' => ?_) (fun γ hm => ?_)
    · exact (hp p a _ b hab).1 σ' hσ'
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
        LRun (canon sp (init p)) (H p) r.final ∧ (SEvent.output r.output ∈ r.events) ∧
        sp.P r.input r.output := Iff.rfl

/-- A system with the empty basis is a commitment-free implementation, in
every form. -/
theorem ofSystem_emptyCommitmentBasis_commitmentFree (Sys : System sp D) (hB : ∀ c, ¬ Sys.basis c)
    (N : Nat → Prop) (location : Option LocationForm) :
    (Component.ofSystemOn Sys N location).CommitmentFree := by
  intro r h
  have hx := ((Component.ofSystemOn Sys N location).sound r h).legal
  have hx' : SysExec (emptyCommitmentBasis sp) (canon sp r.input) r.events r.final := by
    have e : (Component.ofSystemOn Sys N location).basis = emptyCommitmentBasis sp :=
      funext fun c => propext ⟨fun h => hB _ h, False.elim⟩
    rw [e] at hx; exact hx
  exact sysExec_emptyCommitmentBasis_coordFree hx'

/-- The commitment-free system of Theorem `thm:complete-cap` is replicated. -/
theorem cfSystem_replicated (sp : Spec I O) (D : Type) : (CAP.cfSystem sp D).Replicated :=
  ⟨fun _ _ _ => True, fun _ _ _ _ _ => Iff.rfl⟩

/-- Its cluster form is a commitment-free implementation. -/
theorem cfSystem_cluster_commitmentFree (sp : Spec I O) (D : Type) :
    (Component.cluster (CAP.cfSystem sp D) (cfSystem_replicated sp D)).CommitmentFree :=
  ofSystem_emptyCommitmentBasis_commitmentFree _ (fun _ h => h) _ _

end Embedding

/-! ## The timeout abort run by the coordinator alone -/

section Timeout
open CAP CAP.Timeout

/-- A system whose coordinator may close the polls at `yy·` when it runs
alone admits, in any form that allows one participant, a run applying a
commitment: the commitment event `apply(cp)`, then `output(undecided)`. -/
theorem pollClosing_run (D : Type) (Sys : System (voteSpec 3) D) (hb : Sys.basis cp)
    (hs : Sys.strat 1 (fun _ => yyN) 0 [] (.commitment [cp]))
    (hs' : Sys.strat 1 (fun _ => yyN) 0 [.commitment [cp]] (.out .undecided))
    (N : Nat → Prop) (hN : N 1) (location : Option LocationForm) :
    ∃ r, (Component.ofSystemOn Sys N location).accepts r ∧
      Coordinates (canon (voteSpec 3) r.input) r.events := by
  obtain ⟨-, -, -, -, hrows⟩ := timeout_closes_yy
  let σ := canon (voteSpec 3) yyN
  let σc := Figures.closeState σ
  obtain ⟨_, hr1⟩ := closePolls_lrun (D := D) (n := 1)
  have hu : σc.R σc.cur .undecided := (hrows _ _).2 ⟨rfl, rfl⟩
  have hex : Exposable σc .undecided := fun _ _ _ hn => absurd (Or.inl rfl) hn
  let τ0 := outState σc .undecided hu
  have hr0 : LRun (D := D) (n := 1) σ [LEv.commitment [cp], LEv.out .undecided] τ0 :=
    CAP.lrun_append.2 ⟨σc, hr1, .out (step_output_outState hu) (.nil _)⟩
  let H : History (voteSpec 3) D 1 := fun _ => [LEv.commitment [cp], LEv.out .undecided]
  have hw : WF (fun _ => yyN) H := by
    refine ⟨fun _ => ⟨τ0, hr0⟩, fun r a q k j d b h => ?_⟩
    have hm : LEv.recv q k j d ∈ H r := by rw [h]; simp
    simp [H] at hm
  have hp : Produced Sys 1 (fun _ => yyN) H := by
    intro r a e b h
    have hr : r = 0 := Subsingleton.elim _ _
    subst hr
    match a, h with
    | [], h =>
      simp only [H, List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact ⟨fun c hc => by simp at hc; subst hc; exact hb, hs⟩
    | [x], h =>
      simp only [H, List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl, _⟩ := h
      exact ⟨fun σ' hσ' => Or.inl (CAP.lrun_det hσ' hr1 ▸ hex), hs'⟩
    | _ :: _ :: _, h => simp [H] at h
  let r : OperationalRun (voteSpec 3) := ⟨yyN, .undecided, toSEvs (H 0), τ0⟩
  have hev : r.events = [.commitment [Dist.ofCAP cp], .output .undecided] := rfl
  refine ⟨r, (Component.ofSystemOn_accepts _ _ _ _).2 ⟨1, fun _ => yyN, H, 0, hN, hw, hp, rfl,
    rfl, hr0, by rw [hev]; exact List.mem_cons_of_mem _ List.mem_cons_self, decide_yyN.symm⟩, ?_⟩
  rintro ⟨τ, hx⟩
  exact hx.noCommit_of_empty _ (by rw [hev]; exact List.mem_cons_self)

/-- **The timeout-abort commitment as a process component.**  The coordinator alone
running the decision specification (`pollClosingSys1`) is a process component that
admits a run applying a commitment (it closes the polls at `yy·`), so it is
not commitment-free.  That commitment requires coordination but not distributed
coordination (`pollClosingSys1_local`). -/
theorem pollClosingSys1_process (D : Type) :
    (∃ r, (Component.process (pollClosingSys1 D)).accepts r ∧
        Coordinates (canon (voteSpec 3) r.input) r.events) ∧
      ¬ (Component.process (pollClosingSys1 D)).CommitmentFree ∧
      ¬ (pollClosingSys1 D).CoordinationFree ∧ (pollClosingSys1 D).CoordinationFreeH := by
  obtain ⟨r, hacc, hco⟩ := pollClosing_run D (pollClosingSys1 D) rfl ⟨rfl, rfl, rfl⟩
    ⟨rfl, rfl, rfl⟩ (· = 1) rfl (some .process)
  exact ⟨⟨r, hacc, hco⟩, fun hcf => hco (hcf r hacc),
    (pollClosingSys1_local D).1, (pollClosingSys1_local D).2⟩

/-- The replicated decision (`pollClosingSysRepl`) is a replicated system. -/
theorem pollClosingSysRepl_replicated (D : Type) : (pollClosingSysRepl D).Replicated :=
  ⟨fun i _ e => match e with
    | .commitment γ => γ = [cp] ∧ i = yyN
    | .out u => u = .undecided ∧ i = yyN
    | _ => False,
   fun _ _ _ _ e => by cases e <;> exact Iff.rfl⟩

/-- **The timeout-abort commitment as a cluster component.**  Replicated, the same commitment is admitted by the cluster form, and it requires distributed
coordination (`pollClosingSysRepl_not_coordinationFreeH`). -/
theorem pollClosingSysRepl_cluster (D : Type) :
    (∃ r, (Component.cluster (pollClosingSysRepl D) (pollClosingSysRepl_replicated D)).accepts r ∧
      Coordinates (canon (voteSpec 3) r.input) r.events) ∧
      ¬ (pollClosingSysRepl D).CoordinationFreeH :=
  ⟨pollClosing_run D (pollClosingSysRepl D) rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (fun _ => True) trivial
      (some .cluster),
    pollClosingSysRepl_not_coordinationFreeH D⟩

end Timeout

end Components
end CC
