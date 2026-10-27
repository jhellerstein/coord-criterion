import CoordCriterion.Foundations.Core
import CoordCriterion.Foundations.Runs
import CoordCriterion.CompleteCALM.Theorem
import CoordCriterion.Distributed.Histories
import CoordCriterion.Distributed.Commitments
import CoordCriterion.CAP.ResponseForm

/-!
# Systems, canonical systems, and coordination (Sections 4.1–4.4, Appendix C)

Claims of `sections/distributed-histories.tex`, `sections/distributed.tex`
(through `sec:coordination`) and `appendices/commitment-bases-general.tex`
(`app:bases`) beyond the core development of `Distributed/Histories.lean`
and `Distributed/Commitments.lean`, stated in the paper's form (namespace
`CC.Dist`):

* `fig_participant_runs`        — Figure `fig:participant-runs`: the two
                                  histories differ but have equal endpoints.
* `WF0`, `consistent_iff_distConsistent0`
                                — Prop. `prop:distributed-consistency` without
                                  the extra "send identifiers are unique"
                                  assumption of `Dist.History.WF`.
* `distConsistent_iff_liftedMono` — "distributed consistency exactly when
                                  Lifted Monotonicity" (Sec. distributed consistency).
* `functional_excludes_vacuous`, `functional_kappa`, `functional_seal_eq`,
  `functional_legal_ge`         — the one-row-per-input claims.
* `canonLegal_iff`, `canonExec_unique`
                                — Def. `def:canonical-system`: canonical
                                  histories are exactly those of Sec. histories.
* `conflicting_outputs2`, `conflict_is_choice`
                                — Prop. `thm:commitments-require-coordination`
                                  with independent bases, and "the conflict is
                                  a choice, not a seal".
* `sysStep_to_composite`, `sysStep_of_composite`, `composite_functional_seals`
                                — the remark after Lemma `lem:compound-commitment`.
* `reconciliation_any_basis`    — Cor. `cor:reconciliation-any-basis`.
* `converse_fails`, `system_runs_hide_nonmonotonicity`
                                — "the converse of Lemma canonical-equivalent fails".
* `reconcile_cf`                — deterministic reconciliation under Lifted
                                  Monotonicity needs no commitment (Sec. coordination).
* `toCAP`, `ofCAP`, `sysStep_iff_CAP`
                                — the two encodings of commitments and system
                                  output events (`CC.Commitment`/`SysStep` vs `CC.CAP`)
                                  coincide.
* `choice_antichain`, `not_choice_of_two`
                                — "neither [2PL nor MVTO commitment] is the
                                  choice `c_o`" (generic form).
-/

namespace CC
namespace Dist

open Classical

variable {I O : Type} [PO I] [PO O]

/-! ### Figure `fig:participant-runs` -/

section figure

/-- `input(j)` at `σ_S(i)` reaches `σ_S(j)`. -/
theorem step_canon_input (sp : Spec I O) {i j : I} (hij : i ≼ j) (hj : ∃ u, sp.S j u) :
    Step (canon sp i) (.input j) (canon sp j) := by
  obtain ⟨u, hu⟩ := hj
  refine Step.input _ _ j ⟨u, hu, hij⟩ rfl ?_
  funext k x
  apply propext
  show (sp.S k x ∧ j ≼ k) ↔ ((sp.S k x ∧ i ≼ k) ∧ j ≼ k)
  exact ⟨fun ⟨h, hk⟩ => ⟨⟨h, PO.trans hij hk⟩, hk⟩, fun ⟨⟨h, _⟩, hk⟩ => ⟨h, hk⟩⟩

variable {D : Type}

/-- (a) Direct delivery: both participants record `input(j)` from the environment. -/
def Hd (O D : Type) (i j : I) : Dist.History I O D 2 :=
  ⟨fun _ => i, fun _ => [.io (.input j)]⟩

/-- (b) Forwarded delivery: `p = 0` records `input(j)` and sends `(j, d)`; `q = 1`
receives it and records `input(j)`. -/
def Hf (O : Type) (i j : I) (d : D) : Dist.History I O D 2 :=
  ⟨fun _ => i, fun p => if p = 0 then [.io (.input j), .send 0 (some j, d)]
    else [.recv 0 (some j, d), .io (.input j)]⟩

theorem fig_participant_runs (sp : Spec I O) {i j : I} (hij : i ≼ j) (hj : ∃ u, sp.S j u)
    (d : D) :
    (Hd O D i j).WF sp ∧ (Hf O i j d).WF sp ∧
    (Hd O D i j).Endpoint sp (Hd O D i j).InH (fun _ => canon sp j) ∧
    (Hf O i j d).Endpoint sp (Hf O i j d).InH (fun _ => canon sp j) ∧
    (Hd O D i j).ev ≠ (Hf O i j d).ev := by
  have hstep := step_canon_input sp hij hj
  have hx : Exec (canon sp i) [.input j] (canon sp j) := .cons hstep (.nil _)
  -- every participant's input/output events are `[input j]`
  have hioF : ∀ p, Dist.ioOf ((Hf O i j d).ev p) = [.input j] := by
    intro p
    show Dist.ioOf (if p = 0 then _ else _) = _
    by_cases hp : p = 0
    · simp only [hp, ↓reduceIte]; rfl
    · simp only [hp, ↓reduceIte]; rfl
  have hioD : ∀ p, Dist.ioOf ((Hd O D i j).ev p) = [.input j] := by
    intro p; simp [Hd, Dist.ioOf, Dist.LEv.toIO]
  -- the only send of `Hf` is at `(0, 1)`
  have hsend : ∀ (q : Fin 2) (s x : Nat) (m : Option I × D),
      ((Hf O i j d).ev q)[s]? = some (.send x m) → q = 0 ∧ s = 1 ∧ x = 0 ∧ m = (some j, d) := by
    intro q s x m h
    by_cases hq : q = 0
    · simp only [Hf, hq, ite_true] at h
      match s, h with
      | 0, h => simp at h
      | 1, h => simp at h; exact ⟨hq, rfl, h.1.symm, h.2.symm⟩
      | _ + 2, h => simp at h
    · simp only [Hf, hq, ite_false] at h
      match s, h with
      | 0, h => simp at h
      | 1, h => simp at h
      | _ + 2, h => simp at h
  refine ⟨⟨?_, ?_, fun p => ⟨_, (hioD p) ▸ hx⟩⟩, ⟨?_, ?_, fun p => ⟨_, (hioF p) ▸ hx⟩⟩,
    Dist.History.endpoint_full.2 (fun p => (hioD p) ▸ hx),
    Dist.History.endpoint_full.2 (fun p => (hioF p) ▸ hx), ?_⟩
  · intro p r x m h
    simp only [Hd] at h
    match r, h with
    | 0, h => simp at h
    | _ + 1, h => simp at h
  · intro q s _ _ x m _ h
    simp only [Hd] at h
    match s, h with
    | 0, h => simp at h
    | _ + 1, h => simp at h
  · intro p r x m h
    by_cases hp : p = 0
    · simp only [Hf, hp, ite_true] at h
      match r, h with
      | 0, h => simp at h
      | 1, h => simp at h
      | _ + 2, h => simp at h
    · simp only [Hf, hp, ite_false] at h
      match r, h with
      | 0, h =>
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨0, 1, fun he => hp he.symm, ?_⟩
        simp [Hf]
      | 1, h => simp at h
      | _ + 2, h => simp at h
  · intro q s q' s' x m m' h h'
    obtain ⟨hq, hs, _⟩ := hsend q s x m h
    obtain ⟨hq', hs', _⟩ := hsend q' s' x m' h'
    exact ⟨hq.trans hq'.symm, hs.trans hs'.symm⟩
  · intro he
    have := congrFun he ⟨1, by decide⟩
    simp [Hd, Hf] at this

end figure

/-! ### Prop. `prop:distributed-consistency` without unique send identifiers -/

section wf0
variable {D : Type} {n : Nat}

/-- Def. `def:distributed-history` read literally: every receive has *a*
matching send at another participant (no uniqueness of send identifiers). -/
structure WF0 (sp : Spec I O) (H : Dist.History I O D n) : Prop where
  recv_match : ∀ p (r : Nat) x m, (H.ev p)[r]? = some (Dist.LEv.recv x m) →
    ∃ q, ∃ s : Nat, q ≠ p ∧ (H.ev q)[s]? = some (Dist.LEv.send x m)
  legal : ∀ p, ∃ τ : State sp, Exec (canon sp (H.init p)) (Dist.ioOf (H.ev p)) τ

theorem wf_toWF0 {sp : Spec I O} {H : Dist.History I O D n} (h : H.WF sp) : WF0 sp H :=
  ⟨h.recv_match, h.legal⟩

def CutConfluentAt0 (sp : Spec I O) (H : Dist.History I O D n) (C : Dist.Pos n → Prop)
    (j : I) : Prop :=
  ∃ H' : Dist.History I O D n, WF0 sp H' ∧ H.Extends H' C ∧
    ∃ τ : State sp, τ.cur = j ∧ H'.Endpoint sp H'.InH (fun _ => τ)

def DistConsistent0 (sp : Spec I O) (D : Type) : Prop :=
  ∀ (n : Nat) (H : Dist.History I O D n), WF0 sp H → ∀ C, H.IsCut C →
    ∀ σs : Fin n → State sp, H.Endpoint sp C σs →
    ∀ j : I, (∀ p, (σs p).cur ≼ j) → CutConfluentAt0 sp H C j

theorem cut_confluent_iff0 {sp : Spec I O} {H : Dist.History I O D n} (hW : WF0 sp H)
    {C : Dist.Pos n → Prop} (hC : H.IsCut C) {σs : Fin n → State sp}
    (hE : H.Endpoint sp C σs) (j : I) :
    CutConfluentAt0 sp H C j ↔ ∃ τ : State sp, τ.cur = j ∧ ∀ p, Reach (σs p) τ := by
  constructor
  · rintro ⟨H', _, ⟨hinit, hext⟩, τ, hτ, hend'⟩
    rw [Dist.History.endpoint_full] at hend'
    refine ⟨τ, hτ, fun p => ?_⟩
    obtain ⟨c, hc, hx⟩ := hE p
    have htake : (H'.ev p).take c = (H.ev p).take c := by
      apply List.ext_getElem?
      intro i
      rw [List.getElem?_take, List.getElem?_take]
      split
      · exact hext p i ((hc i).2 ‹_›)
      · rfl
    have h := hend' p
    rw [← List.take_append_drop c (H'.ev p), Dist.ioOf_append, Dist.exec_append] at h
    obtain ⟨ρ, h1, h2⟩ := h
    rw [hinit, htake] at h1
    have := exec_det h1 hx
    subst this
    exact ⟨_, h2⟩
  · rintro ⟨τ, hτ, hr⟩
    obtain ⟨c, hc⟩ := Dist.History.endpoint_choose hE
    have hes : ∀ p, ∃ es, Exec (σs p) es τ := hr
    let es := fun p => Classical.choose (hes p)
    have hes' : ∀ p, Exec (σs p) (es p) τ := fun p => Classical.choose_spec (hes p)
    let H' : Dist.History I O D n :=
      ⟨H.init, fun p => (H.ev p).take (c p) ++ (es p).map Dist.LEv.io⟩
    have hlegal : ∀ p, Exec (canon sp (H'.init p)) (Dist.ioOf (H'.ev p)) τ := by
      intro p
      show Exec _ (Dist.ioOf ((H.ev p).take (c p) ++ (es p).map Dist.LEv.io)) τ
      rw [Dist.ioOf_append, Dist.ioOf_map_io]
      exact (Dist.exec_append _ _).2 ⟨σs p, (hc p).2, hes' p⟩
    have hcut : ∀ q s, C (q, s) → (H'.ev q)[s]? = (H.ev q)[s]? := fun q s hs =>
      Dist.get_ext_lt (((hc q).1 s).1 hs) (hC.sub _ hs)
    refine ⟨H', ⟨?_, fun p => ⟨τ, hlegal p⟩⟩, ⟨rfl, hcut⟩, τ, hτ,
      Dist.History.endpoint_full.2 hlegal⟩
    intro p r x m h
    rcases Dist.get_ext h with ⟨hrc, hr'⟩ | ⟨_, he⟩
    · obtain ⟨q, s, hqp, hs⟩ := hW.recv_match p r x m hr'
      have hCp : C (p, r) := ((hc p).1 r).2 hrc
      have hCq : C (q, s) := hC.closed _ _ (.single (.msg q s p r x m hs hr')) hCp
      exact ⟨q, s, hqp, by rw [hcut q s hCq]; exact hs⟩
    · cases he

/-- **Prop. `prop:distributed-consistency`**, for histories in which several
sends may carry the same identifier and message. -/
theorem consistent_iff_distConsistent0 (sp : Spec I O) (D : Type) :
    sp.Consistent ↔ DistConsistent0 sp D := by
  constructor
  · intro hc n H hW C hC σs hE j hj
    rw [cut_confluent_iff0 hW hC hE]
    obtain ⟨τ, hτ, h⟩ := hc (List.ofFn σs)
      (fun σ hσ => by obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hσ; exact hE.isRun p) j
      (fun σ hσ => by obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hσ; exact hj p)
    exact ⟨τ, hτ, fun p => h _ (List.mem_ofFn.2 ⟨p, rfl⟩)⟩
  · -- message-free histories are well formed in either sense
    intro hd
    rw [Dist.consistent_iff_distConsistent sp D]
    intro n H hW C hC σs hE j hj
    obtain ⟨H', hW', hext, τ, hτ, hend⟩ := hd n H (wf_toWF0 hW) C hC σs hE j hj
    have hr := (cut_confluent_iff0 (wf_toWF0 hW) hC hE j).1 ⟨H', hW', hext, τ, hτ, hend⟩
    exact (Dist.cut_confluent_iff hW hC hE j).2 hr

end wf0

/-! ### Distributed consistency ⇔ Lifted Monotonicity -/

/-- "By Complete CALM … a specification has distributed consistency exactly
when it satisfies Lifted Monotonicity." -/
theorem distConsistent_iff_liftedMono (sp : Spec I O) (D : Type) :
    Dist.DistConsistent sp D ↔ sp.LiftedMono :=
  (Dist.consistent_iff_distConsistent sp D).symm.trans (complete_calm sp)

/-! ### One row per input -/

section functional
variable {sp : Spec I O}

/-- "With one row per input, Eq. commitment-excludes holds vacuously." -/
theorem functional_excludes_vacuous (hf : sp.Functional) (σ τ : State sp) :
    ∀ k u w, σ.R k u → ¬ τ.R k u → τ.R k w → ¬ (u ≼ w) := by
  intro k u w hu hnu hw _
  have : u = w := hf k u w (σ.sub _ _ hu) (τ.sub _ _ hw)
  exact hnu (this ▸ hw)

theorem functional_not_rejected (hf : sp.Functional) (σ : State sp) (o : O) (k : I) (x : O) :
    ¬ Rejected σ o k x := by
  intro hr
  have : ∃ u, σ.R k u ∧ o ≼ u := Classical.byContradiction fun hn => hr.2.2.1 ⟨hr.1, hn⟩
  obtain ⟨u, hu, hou⟩ := this
  have : x = u := hf k x u (σ.sub _ _ hr.1) (σ.sub _ _ hu)
  exact hr.2.1 (this ▸ hou)

/-- With one row per input, the canonical event applies at most the seal. -/
theorem functional_kappa (hf : sp.Functional) (σ : State sp) (o : O) :
    kappa σ o = (if ∃ k x, Sealed σ o k x then [sealC o] else []) := by
  have h2 : ¬ ∃ k x, Rejected σ o k x := fun ⟨k, x, h⟩ => functional_not_rejected hf σ o k x h
  simp only [kappa, h2, ite_false, List.append_nil]

/-- With one row per input, the seal `s_o` of Def. `def:lifted-output-event` is
the seal of Def. `def:output-event`: it leaves `R[out ⪰ o]`. -/
theorem functional_seal_eq (hf : sp.Functional) (σ : State sp) (o : O) (ho : σ.R σ.cur o) :
    (cmSealState σ o ho).R = outputTable σ o := by
  funext k x
  apply propext
  show (σ.R k x ∧ ¬ Sealed σ o k x) ↔ (σ.R k x ∧ o ≼ x)
  constructor
  · rintro ⟨hx, hns⟩
    refine ⟨hx, ?_⟩
    have : ∃ u, σ.R k u ∧ o ≼ u := Classical.byContradiction fun hn => hns ⟨hx, hn⟩
    obtain ⟨u, hu, hou⟩ := this
    have : x = u := hf k x u (σ.sub _ _ hx) (σ.sub _ _ hu)
    exact this ▸ hou
  · rintro ⟨hx, hox⟩
    exact ⟨hx, fun hs => hs.2 ⟨x, hx, hox⟩⟩

/-- "With one row per input … legality says that every row the commitments
leave has an output that refines `o`." -/
theorem functional_legal_ge (hf : sp.Functional) {B : Basis sp} {σ τ : State sp}
    {γ : List (Commitment sp)} {o : O} (h : SysStep B σ (.output γ o) τ) :
    ∃ σc, ApplySeq γ σ σc ∧ (∀ k x, σc.R k x → o ≼ x) ∧ τ.R = σc.R := by
  match h with
  | .output (σc := σc) _ hγ _ hleg _ hR =>
    have hge : ∀ k x, σc.R k x → o ≼ x := fun k x hx => Classical.byContradiction fun hnx => by
      obtain ⟨u, hu, hou, _⟩ := hleg k x hx hnx
      have : x = u := hf k x u (σc.sub _ _ hx) (σc.sub _ _ hu)
      exact hnx (this ▸ hou)
    exact ⟨σc, hγ, hge, by
      rw [hR]; funext k x; apply propext
      exact ⟨fun h => h.1, fun h => ⟨h, hge k x h⟩⟩⟩

end functional

/-! ### Def. `def:canonical-system`: canonical histories are those of Sec. histories -/

section canonical_system
variable {sp : Spec I O} {D : Type} {n : Nat}

/-- Annotating each participant's input/output events of `H` with commitment
sequences gives a legal canonical run (every output event is `Out_{κ_o}(o)`
at the state where it occurs). -/
def CanonLegal (sp : Spec I O) (H : Dist.History I O D n) : Prop :=
  ∀ p, ∃ es : List (SEvent sp), es.filterMap SEvent.erase = Dist.ioOf (H.ev p) ∧
    ∃ τ, CanonExec (canon sp (H.init p)) es τ

/-- The same with legal events `Out_γ(o)` from a basis `B`. -/
def SysLegal (B : Basis sp) (H : Dist.History I O D n) : Prop :=
  ∀ p, ∃ es : List (SEvent sp), es.filterMap SEvent.erase = Dist.ioOf (H.ev p) ∧
    ∃ τ, SysExec B (canon sp (H.init p)) es τ

/-- **Def. canonical system**, last clause: a history's events can be
annotated canonically iff it satisfies item 3 of Def. distributed-history. -/
theorem canonLegal_iff (H : Dist.History I O D n) :
    CanonLegal sp H ↔ ∀ p, ∃ τ : State sp, Exec (canon sp (H.init p)) (Dist.ioOf (H.ev p)) τ := by
  constructor
  · intro h p
    obtain ⟨es, he, τ, hx⟩ := h p
    exact ⟨τ, he ▸ canonExec_exec hx⟩
  · intro h p
    obtain ⟨τ, hx⟩ := h p
    obtain ⟨es, he, hc⟩ := exec_canonExec hx
    exact ⟨es, he, τ, hc⟩

/-- Canonical runs are determined by their erasure: the canonical annotation
is unique. -/
theorem canonExec_unique {σ ρ ρ' : State sp} {es es' : List (SEvent sp)}
    (h : CanonExec σ es ρ) (h' : CanonExec σ es' ρ')
    (he : es.filterMap SEvent.erase = es'.filterMap SEvent.erase) : es = es' ∧ ρ = ρ' := by
  induction h generalizing es' with
  | nil =>
    cases h' with
    | nil => exact ⟨rfl, rfl⟩
    | cons hs' _ =>
      obtain ⟨_, he', _⟩ := canonStep_step hs'
      rw [List.filterMap_nil, List.filterMap_cons_some he'] at he; cases he
  | @cons σ τ ρ e es hs _ ih =>
    cases h' with
    | nil =>
      obtain ⟨_, he', _⟩ := canonStep_step hs
      rw [List.filterMap_nil, List.filterMap_cons_some he'] at he; cases he
    | @cons _ τ' _ e' es'' hs' hr' =>
      obtain ⟨a, ha, hst⟩ := canonStep_step hs
      obtain ⟨a', ha', hst'⟩ := canonStep_step hs'
      rw [List.filterMap_cons_some ha, List.filterMap_cons_some ha'] at he
      simp only [List.cons.injEq] at he
      obtain ⟨he1, he2⟩ := he
      subst he1
      have hee : e = e' := by
        cases e with
        | input j =>
          cases e' with
          | input j' => cases ha; cases ha'; rfl
          | output _ _ => cases ha; cases ha'
          | commit _ => cases ha'
        | output γ o =>
          cases e' with
          | input _ => cases ha; cases ha'
          | output γ' o' =>
            cases ha; cases ha'
            rw [hs.2.1 γ o rfl, hs'.2.1 γ' o rfl]
          | commit _ => cases ha'
        | commit _ => cases ha
      subst hee
      have hτ : τ = τ' := step_det hst hst'
      subst hτ
      obtain ⟨h1, h2⟩ := ih hr' he2
      exact ⟨by rw [h1], h2⟩

/-- Every canonical annotation is in particular legal under `B_S`. -/
theorem canonLegal_sysLegal {H : Dist.History I O D n} (h : CanonLegal sp H) :
    SysLegal (canonBasis sp) H := by
  intro p
  obtain ⟨es, he, τ, hx⟩ := h p
  exact ⟨es, he, τ, canonExec_sysExec hx⟩

end canonical_system

/-! ### Prop. `thm:commitments-require-coordination`, refinements -/

section conflict
variable {sp : Spec I O}

/-- The two continuations may use different bases. -/
theorem conflicting_outputs2 {B B' B1 B2 : Basis sp} {σ σ' t : State sp}
    {γ γ' : List (Commitment sp)} {o x : O}
    (_h1 : SysStep B σ (.output γ o) σ') (hno : ∀ w, σ'.R σ.cur w → ¬ x ≼ w)
    (h2 : SysStep B' σ (.output γ' x) t) :
    ¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧
        (∃ es, SysExec B1 σ' es ρ) ∧ (∃ es, SysExec B2 t es ρ) := by
  obtain ⟨_, _, ht, _⟩ := containment h2
  rintro ⟨ρ, hc, ⟨es1, hx1⟩, ⟨es2, hx2⟩⟩
  obtain ⟨w, hw⟩ := ρ.hasCur
  rw [hc] at hw
  exact hno w (hx1.sub _ _ hw) (ht _ _ (hx2.sub _ _ hw)).2

/-- Some commitment of a sequence removes any row that the sequence removes. -/
theorem applySeq_removed {γ : List (Commitment sp)} {σ σc : State sp}
    (h : ApplySeq γ σ σc) {k : I} {x : O} :
    σ.R k x → ¬ σc.R k x →
      ∃ c ∈ γ, ∃ α β : State sp, c.app α = some β ∧ α.cur = σ.cur ∧ α.R k x ∧ ¬ β.R k x := by
  induction h with
  | nil => exact fun hx hn => absurd hx hn
  | @cons c cs σ τ ρ hc hrest ih =>
    intro hx hn
    by_cases hτ : τ.R k x
    · obtain ⟨c', hc', α, β, h1, h2, h3, h4⟩ := ih hτ hn
      exact ⟨c', List.mem_cons_of_mem _ hc', α, β, h1, h2.trans (c.cur_eq σ τ hc), h3, h4⟩
    · exact ⟨c, List.mem_cons_self .., σ, τ, hc, rfl, hx, hτ⟩

/-- "The conflict is at the current input, so it is a choice, not a seal":
if `Out_γ(o)` leaves no output refining `x ∈ R(i)`, then some commitment `c`
of `γ` removes `(i, x)` while keeping a row at `i`, and no kept row at `i`
refines `x`. -/
theorem conflict_is_choice {B : Basis sp} {σ σ' : State sp} {γ : List (Commitment sp)}
    {o x : O} (h1 : SysStep B σ (.output γ o) σ') (hx : σ.R σ.cur x)
    (hno : ∀ w, σ'.R σ.cur w → ¬ x ≼ w) :
    ∃ c ∈ γ, ∃ α β : State sp, c.app α = some β ∧ α.cur = σ.cur ∧ α.R σ.cur x ∧
      ¬ β.R σ.cur x ∧ (∃ w, β.R σ.cur w) ∧ ∀ w, β.R σ.cur w → ¬ x ≼ w := by
  match h1 with
  | .output (σc := σc) _ hγ _ hleg _ hR =>
    have hnc : ¬ σc.R σ.cur x := by
      intro hcx
      by_cases hox : o ≼ x
      · exact hno x (by rw [hR]; exact ⟨hcx, hox⟩) (PO.refl x)
      · obtain ⟨u, hu, hou, hxu⟩ := hleg _ _ hcx hox
        exact hno u (by rw [hR]; exact ⟨hu, hou⟩) hxu
    obtain ⟨c, hc, α, β, hab, hαc, hαx, hβx⟩ := applySeq_removed hγ hx hnc
    have hβc : β.cur = σ.cur := (c.cur_eq α β hab).trans hαc
    refine ⟨c, hc, α, β, hab, hαc, hαx, hβx, ?_, fun w hw => c.excludes α β hab _ x w hαx hβx hw⟩
    obtain ⟨w, hw⟩ := β.hasCur
    exact ⟨w, hβc ▸ hw⟩

end conflict

/-! ### Remark after Lemma `lem:compound-commitment` -/

section compound
variable {sp : Spec I O}

theorem sysStep_to_composite {B B' : Basis sp} {σ τ : State sp} {c : Commitment sp}
    {cs : List (Commitment sp)} {o : O} (hB' : B' (composite c cs))
    (h : SysStep B σ (.output (c :: cs) o) τ) :
    SysStep B' σ (.output [composite c cs] o) τ := by
  match h with
  | .output _ hγ ho hleg hcur hR =>
    exact SysStep.output (fun c' hc' => (List.mem_singleton.1 hc') ▸ hB')
      ((applySeq_composite c cs _ _).1 hγ) ho hleg hcur hR

theorem sysStep_of_composite {B B' : Basis sp} {σ τ : State sp} {c : Commitment sp}
    {cs : List (Commitment sp)} {o : O} (hB : ∀ c' ∈ c :: cs, B c')
    (h : SysStep B' σ (.output [composite c cs] o) τ) :
    SysStep B σ (.output (c :: cs) o) τ := by
  match h with
  | .output _ hγ ho hleg hcur hR =>
    exact SysStep.output hB ((applySeq_composite c cs _ _).2 hγ) ho hleg hcur hR

/-- "In a functional specification the composite … seals." -/
theorem composite_functional_seals (hf : sp.Functional) (c : Commitment sp)
    (cs : List (Commitment sp)) {σ τ : State sp} (h : (composite c cs).app σ = some τ)
    (k : I) (hk : ∃ u, σ.R k u ∧ ¬ τ.R k u) : ∀ w, ¬ τ.R k w :=
  functional_commitment_seals hf _ h k hk

end compound

/-! ### Cor. `cor:reconciliation-any-basis` -/

/-- **Cor. reconciliation under any basis.**  Runs `r` under bases `B r`,
continued under arbitrary bases `B' r` to one state with current input `j`:
some `u ∈ S(j)` refines every output emitted on every run.  (The hypothesis
that `j` is a common expansion is not needed.) -/
theorem reconciliation_any_basis {sp : Spec I O} {m : Nat} (B B' : Fin m → Basis sp)
    (i : Fin m → I) (es : Fin m → List (SEvent sp)) (ρ : Fin m → State sp)
    (hrun : ∀ r, SysExec (B r) (canon sp (i r)) (es r) (ρ r))
    (τ : State sp) (j : I) (hτ : τ.cur = j)
    (hcont : ∀ r, ∃ es', SysExec (B' r) (ρ r) es' τ) :
    ∃ u, sp.S j u ∧ ∀ r, ∀ o ∈ outs ((es r).filterMap SEvent.erase), o ≼ u := by
  obtain ⟨u, hu⟩ := τ.hasCur
  rw [hτ] at hu
  refine ⟨u, τ.sub _ _ hu, fun r => ?_⟩
  obtain ⟨es', hx'⟩ := hcont r
  have hρ : (ρ r).R j u := hx'.sub _ _ hu
  obtain ⟨_, ρ', _, _, hx, _, hsub⟩ := canonical_equivalent (hrun r)
  exact ((run_residual hx j u).1 (hsub _ _ hρ)).2.2

/-! ### The converse of Lemma `lem:canonical-equivalent` fails -/

section converse

/-- One input. -/
def U1 := Unit

instance : PO U1 where
  le _ _ := True
  refl _ := trivial
  trans _ _ := trivial
  antisymm := fun {a b} _ _ => by cases a; cases b; rfl

theorem u1_eq (a b : U1) : a = b := by cases a; cases b; rfl

/-- Two incomparable outputs. -/
def B2 := Bool

instance : PO B2 where
  le a b := a = b
  refl _ := rfl
  trans h1 h2 := h1.trans h2
  antisymm h _ := h

/-- One input with two incomparable outputs. -/
def spU : Spec U1 B2 where
  S _ _ := True
  total _ := ⟨(true : Bool), trivial⟩

/-- The empty basis. -/
def noBasis : Basis spU := fun _ => False

theorem b2_ne {a b : B2} (h : a ≠ b) : ¬ a ≼ b := h

/-- In a state whose table is full, no output is exposable. -/
theorem spU_not_exposable (σ : State spU) (hfull : ∀ k u, σ.R k u) (o : B2) :
    ¬ Exposable σ o := by
  intro he
  have hne : o ≠ (!o : Bool) := by cases o <;> (intro h; cases h)
  obtain ⟨u, _, h1, h2⟩ := he σ.cur (!o : Bool) (hfull _ _) (b2_ne hne)
  have e1 : o = u := h1
  have e2 : (!o : Bool) = u := h2
  exact hne (e1.trans e2.symm)

/-- Runs under the empty basis never leave the canonical state. -/
theorem noBasis_full {σ ρ : State spU} {es : List (SEvent spU)} (h : SysExec noBasis σ es ρ) :
    (∀ k u, σ.R k u) → ∀ k u, ρ.R k u := by
  induction h with
  | nil => exact id
  | @cons σ τ ρ e es hs _ ih =>
    intro hσ
    apply ih
    match e, hs with
    | _, .input (.input _ _ _ _ _ hR) => intro k u; rw [hR]; exact ⟨hσ k u, trivial⟩
    | _, .output (γ := γ) hb hγ _ hleg _ _ =>
      cases γ with
      | cons c _ => exact (hb c (List.mem_cons_self ..)).elim
      | nil =>
        cases hγ
        exact (spU_not_exposable σ hσ _ hleg).elim
    | _, .commit (γ := γ) hb hne _ =>
      cases γ with
      | nil => exact absurd rfl hne
      | cons c _ => exact (hb c (List.mem_cons_self ..)).elim

theorem canonU_full (i : U1) : ∀ k u, (canon spU i).R k u := fun _ _ => ⟨trivial, trivial⟩

/-- **The converse of Lemma canonical-equivalent fails.**  The canonical run
`output(true)` from `σ_S(*)` is observably equivalent to no run under the
empty basis. -/
theorem converse_fails :
    (∃ τ, Exec (canon spU ()) [.output (true : Bool)] τ) ∧
    ¬ ∃ (es : List (SEvent spU)) (ρ : State spU),
        SysExec noBasis (canon spU ()) es ρ ∧ es.filterMap SEvent.erase = [.output (true : Bool)] := by
  refine ⟨⟨outState (canon spU ()) (true : Bool) ⟨trivial, trivial⟩,
    .cons (Step.output (canon spU ()) (outState (canon spU ()) (true : Bool) ⟨trivial, trivial⟩)
      (true : Bool) ⟨trivial, trivial⟩ rfl rfl) (.nil _)⟩, ?_⟩
  rintro ⟨es, ρ, hx, he⟩
  cases hx with
  | nil => simp at he
  | cons hs _ =>
    rename_i e _ _
    cases e with
    | input _ => simp [SEvent.erase] at he
    | output γ o =>
      cases hs with
      | output hb hγ _ hleg _ _ =>
        cases γ with
        | cons c _ => exact hb c (List.mem_cons_self ..)
        | nil =>
          cases hγ
          exact spU_not_exposable _ (canonU_full ()) _ hleg
    | commit γ =>
      cases hs with
      | commit hb hne _ =>
        cases γ with
        | nil => exact hne rfl
        | cons c _ => exact hb c (List.mem_cons_self ..)

/-- "Restricting attention to one system's runs could therefore hide
non-monotonicity": `spU` is not consistent, yet every finite family of runs
under the empty basis is confluent, within that system, at every input. -/
theorem system_runs_hide_nonmonotonicity :
    ¬ spU.Consistent ∧
    ∀ fam : List (State spU), (∀ σ ∈ fam, ∃ i es, SysExec noBasis (canon spU i) es σ) →
      ∀ j : U1, ∃ τ : State spU, τ.cur = j ∧ ∀ σ ∈ fam, ∃ es, SysExec noBasis σ es τ := by
  refine ⟨fun hc => ?_, fun fam hfam j => ?_⟩
  · have hLM := (complete_calm spU).1 hc
    obtain ⟨u, _, h⟩ := hLM () () trivial [(true : B2), (false : B2)] (List.cons_ne_nil _ _)
      (fun _ _ => trivial)
    have e1 : (true : Bool) = u := h (true : B2) (List.mem_cons_self ..)
    have e2 : (false : Bool) = u := h (false : B2) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    exact Bool.noConfusion (e1.trans e2.symm)
  · refine ⟨canon spU (), u1_eq _ _, fun σ hσ => ⟨[], ?_⟩⟩
    obtain ⟨i, es, hx⟩ := hfam σ hσ
    have hfull := noBasis_full hx (canonU_full i)
    have : σ = canon spU () := State.ext' (u1_eq _ _) (by
      funext k u; apply propext
      exact ⟨fun _ => canonU_full () k u, fun _ => hfull k u⟩)
    rw [this]; exact SysExec.nil _

end converse

/-! ### Deterministic reconciliation needs no commitment -/

/-- Under Lifted Monotonicity, runs with a common expansion `j` share a row
`(j,u)`, and from each final state the commitment-free events `input(j)`,
`Out_ε(u)` reach the same state `(j, S[in ⪰ j, out ⪰ u])`. -/
theorem reconcile_cf {sp : Spec I O} (hLM : sp.LiftedMono) (fam : List (State sp))
    (hrun : ∀ σ ∈ fam, IsRun σ) (j : I) (hj : ∀ σ ∈ fam, σ.cur ≼ j) :
    ∃ u, ∃ hu : sp.S j u, (∀ σ ∈ fam, σ.R j u) ∧
      ∀ σ ∈ fam, ExecCF σ [.input j, .output u] (meetState sp j u hu) := by
  have hC := (liftedMono_iff_commonExpansion sp).1 hLM
  have hcons := (complete_calm sp).2 hLM
  obtain ⟨u, hu, hall⟩ := (survivor_test fam hrun j hj).1 (hcons fam hrun j hj)
  refine ⟨u, hu, hall, fun σ hσ => ?_⟩
  have hju := hall σ hσ
  obtain ⟨i, es, hx⟩ := hrun σ hσ
  let τ1 : State sp :=
    { cur := j
      R := inputTable σ j
      sub := fun k x h => σ.sub k x h.1
      hasCur := ⟨u, hju, PO.refl j⟩
      above := fun _ _ h => h.2 }
  have s1 : Step σ (.input j) τ1 := Step.input σ τ1 j ⟨u, hju⟩ rfl rfl
  have hτ1 : IsRun τ1 :=
    ⟨i, es ++ [.input j], (Dist.exec_append _ _).2 ⟨σ, hx, .cons s1 (.nil _)⟩⟩
  have ho : τ1.R τ1.cur u := ⟨hju, PO.refl j⟩
  have hexp := commonExpansion_exposable hC hτ1 ho
  have hres := run_residual hx
  have hEu := ((hres j u).1 hju).2.2
  have s2 : Step τ1 (.output u) (meetState sp j u hu) := by
    refine Step.output τ1 _ u ho rfl ?_
    funext k x
    apply propext
    show (sp.S k x ∧ j ≼ k ∧ u ≼ x) ↔ ((σ.R k x ∧ j ≼ k) ∧ u ≼ x)
    constructor
    · rintro ⟨hS, hjk, hux⟩
      exact ⟨⟨(hres k x).2 ⟨hS, PO.trans (hj σ hσ) hjk,
        fun o ho => PO.trans (hEu o ho) hux⟩, hjk⟩, hux⟩
    · rintro ⟨⟨h, hjk⟩, hux⟩
      exact ⟨σ.sub _ _ h, hjk, hux⟩
  exact .input s1 (.output s2 hexp (.nil _))

/-! ### The two encodings of commitments coincide -/

section encodings
variable {sp : Spec I O}

def toCAP (c : Commitment sp) : CAP.Commitment sp :=
  ⟨c.app, c.cur_eq, c.sub, c.removes, c.excludes⟩

def ofCAP (c : CAP.Commitment sp) : Commitment sp :=
  ⟨c.f, c.cur_eq, c.sub, c.strict, c.excl⟩

theorem ofCAP_toCAP (c : Commitment sp) : ofCAP (toCAP c) = c := by cases c; rfl

theorem toCAP_ofCAP (c : CAP.Commitment sp) : toCAP (ofCAP c) = c := by cases c; rfl

theorem applySeq_iff_CAP {γ : List (Commitment sp)} {σ ρ : State sp} :
    ApplySeq γ σ ρ ↔ CAP.applySeq σ (γ.map toCAP) = some ρ := by
  induction γ generalizing σ with
  | nil =>
    simp only [List.map_nil, CAP.applySeq, Option.some.injEq]
    exact ⟨fun h => by cases h; rfl, fun h => h ▸ ApplySeq.nil _⟩
  | cons c cs ih =>
    simp only [List.map_cons, CAP.applySeq]
    cases hc : c.app σ with
    | none =>
      have : (toCAP c).f σ = none := hc
      rw [this]
      simp only [reduceCtorEq, iff_false]
      intro h; cases h with | cons hc' _ => rw [hc] at hc'; cases hc'
    | some τ =>
      have : (toCAP c).f σ = some τ := hc
      rw [this]
      simp only
      rw [← ih]
      constructor
      · intro h; cases h with | cons hc' h' => rw [hc] at hc'; cases hc'; exact h'
      · intro h; exact ApplySeq.cons hc h

/-- A legal `Out_γ(o)` of `Distributed/Commitments.lean` is exactly a legal `out γ o` of
`CAP/Model.lean` (`applySeq`, then `Step` and `Exposable` at the committed
state), with the commitments transported by `toCAP`. -/
theorem sysStep_iff_CAP {B : Basis sp} {σ τ : State sp} {γ : List (Commitment sp)} {o : O} :
    SysStep B σ (.output γ o) τ ↔
      (∀ c ∈ γ, B c) ∧ ∃ σc, CAP.applySeq σ (γ.map toCAP) = some σc ∧
        Step σc (.output o) τ ∧ Exposable σc o := by
  constructor
  · intro h
    match h with
    | .output hb hγ ho hleg hcur hR =>
      exact ⟨hb, _, applySeq_iff_CAP.1 hγ,
        Step.output _ _ o ho (hcur.trans hγ.cur_eq.symm) hR, hleg⟩
  · rintro ⟨hb, σc, hγ, hs, hleg⟩
    have hγ' := applySeq_iff_CAP.2 hγ
    cases hs with
    | output _ _ ho hcur hR =>
      exact SysStep.output hb hγ' ho hleg (hcur.trans hγ'.cur_eq) hR

end encodings

/-! ### "Neither is the choice `c_o`" (generic form) -/

section antichain
variable {sp : Spec I O}

/-- If the fiber at the current input is an antichain, `c_o` keeps only `o`
there. -/
theorem choice_antichain {σ : State sp} {o : O} (ho : σ.R σ.cur o)
    (hanti : ∀ x y, σ.R σ.cur x → σ.R σ.cur y → x ≼ y → x = y) :
    ∀ x, (cmChooseState σ o).R σ.cur x ↔ x = o := by
  intro x
  constructor
  · rintro ⟨hx, hnr⟩
    apply Classical.byContradiction
    intro hne
    have hnox : ¬ o ≼ x := fun h => hne (hanti o x ho hx h).symm
    apply hnr
    refine ⟨hx, hnox, fun hs => hs.2 ⟨o, ho, PO.refl o⟩, ?_⟩
    rintro ⟨_, _, u, hu, hou, hxu⟩
    have e1 := hanti o u ho hu hou
    have e2 := hanti x u hx hu hxu
    exact hne (e2.trans e1.symm)
  · rintro rfl
    exact ⟨ho, not_rejected_of_ge (PO.refl x)⟩

/-- A commitment that keeps two distinct rows at the current input of a state
whose current fiber is an antichain is not `c_o` for any `o`. -/
theorem not_choice_of_two {σ τ : State sp} {x y : O}
    (hanti : ∀ x y, σ.R σ.cur x → σ.R σ.cur y → x ≼ y → x = y)
    (hx : τ.R σ.cur x) (hy : τ.R σ.cur y) (hxy : x ≠ y) (o : O) :
    (choiceC o).app σ ≠ some τ := by
  intro h
  obtain ⟨ho, _, rfl⟩ := chooseApp_eq.1 h
  have e1 := (choice_antichain ho hanti x).1 hx
  have e2 := (choice_antichain ho hanti y).1 hy
  exact hxy (e1.trans e2.symm)

end antichain

end Dist
end CC
