import CoordCriterion.Appendix.Deployment
import CoordCriterion.Distributed.Systems

/-!
# Deployment remark: system runs (Appendix `app:deployment`)

The remark after Prop. `thm:complete-cap-deployment`: for the runs of a
*system* (`CC.CAP` local runs, with arbitrary commitments in output events),
if the specification is monotone across partitions then every separable,
authorized family of system runs has a common refinement in `S(j)` at every
common expansion `j` (`system_monoAcross`), in particular the participant
runs at a cut of a partitioned history (`history_monoAcross`).  Proved via
`CC.Dist.sysStep_iff_CAP` and Lemma `canonical_equivalent` (system runs are
equivalent to canonical runs, `lrun_sysExec`, `SRun.canonical`).  "It does not
follow that the deployment authorizes any participant to emit `u`"
(`unauthorized_refinement`).
-/

namespace CC
namespace Deploy

open Classical

/-! ## 4. App. `app:deployment`: the proposition applies to the runs of a system

A system participant's run is a `CC.CAP` local run (`LRun`) from a canonical
state: input events, output events `out γ o` with arbitrary commitment
sequences `γ`, sends and receives.  Its emitted rows are the pairs
`(current input, o)` of its output events. -/

open CC.CAP (LEv LRun)
open CC.Deploy

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type} {m : Nat}

/-- Emitted rows along a local event list, from current input `c`. -/
def emittedL (c : I) : List (LEv sp D m) → List (I × O)
  | [] => []
  | .inp j :: es => emittedL j es
  | .out _ o :: es => (c, o) :: emittedL c es
  | .cmt _ :: es => emittedL c es
  | .send _ _ :: es => emittedL c es
  | .recv _ _ _ _ :: es => emittedL c es

/-- The `CC.SysExec` system events of a local event list (sends and receives
dropped, commitments transported by `Dist.ofCAP`). -/
def toS : List (LEv sp D m) → List (SEvent sp)
  | [] => []
  | .inp j :: es => .input j :: toS es
  | .out γ o :: es => .output (γ.map Dist.ofCAP) o :: toS es
  | .cmt γ :: es => .commit (γ.map Dist.ofCAP) :: toS es
  | .send _ _ :: es => toS es
  | .recv _ _ _ _ :: es => toS es

theorem map_ofCAP_toCAP (γ : List (CAP.Commitment sp)) :
    (γ.map Dist.ofCAP).map Dist.toCAP = γ := by
  induction γ with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, Dist.toCAP_ofCAP]; exact congrArg _ ih

/-- A local run is an execution under the full basis (via
`Dist.sysStep_iff_CAP`). -/
theorem lrun_sysExec {σ τ : State sp} {l : List (LEv sp D m)} (h : LRun σ l τ) :
    SysExec (fun _ => True) σ (toS l) τ := by
  induction h with
  | nil => exact SysExec.nil _
  | inp hs _ ih => exact SysExec.cons (SysStep.input hs) ih
  | @out σ σc τ ρ γ o es hγ hs hexp _ ih =>
    refine SysExec.cons (Dist.sysStep_iff_CAP.2 ⟨fun _ _ => trivial, σc, ?_, hs, hexp⟩) ih
    rw [map_ofCAP_toCAP]; exact hγ
  | cmt hne hγ _ ih =>
    refine SysExec.cons (SysStep.commit (fun _ _ => trivial) ?_ ?_) ih
    · intro h; exact hne (List.map_eq_nil_iff.1 h)
    · rw [Dist.applySeq_iff_CAP, map_ofCAP_toCAP]; exact hγ
  | send _ ih => exact ih
  | recv _ ih => exact ih

theorem emitted_toS (c : I) (l : List (LEv sp D m)) :
    emitted c ((toS l).filterMap SEvent.erase) = emittedL c l := by
  induction l generalizing c with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | inp j => exact ih j
    | out γ o => simp only [toS, List.filterMap_cons, SEvent.erase, emitted, emittedL, ih]
    | cmt γ => exact ih c
    | send _ _ => exact ih c
    | recv _ _ _ _ => exact ih c

/-- A participant run of a system. -/
structure SRun (sp : Spec I O) (D : Type) (m : Nat) where
  init : I
  es : List (LEv sp D m)
  fin : State sp
  run : LRun (canon sp init) es fin

def SRun.rows (r : SRun sp D m) : List (I × O) := emittedL r.init r.es

/-- **Lemma `canonical-equivalent`, applied to a system run**: a canonical
run with the same emitted rows and the same current input. -/
theorem SRun.canonical (r : SRun sp D m) :
    ∃ q : PRun sp, q.rows = r.rows ∧ q.fin.cur = r.fin.cur := by
  obtain ⟨_, ρ', _, _, hx, hc, _⟩ := canonical_equivalent (lrun_sysExec r.run)
  exact ⟨⟨r.init, _, ρ', hx⟩, emitted_toS r.init r.es, hc⟩

noncomputable def SRun.toP (r : SRun sp D m) : PRun sp := Classical.choose r.canonical

theorem SRun.toP_rows (r : SRun sp D m) : r.toP.rows = r.rows :=
  (Classical.choose_spec r.canonical).1

theorem SRun.toP_cur (r : SRun sp D m) : r.toP.fin.cur = r.fin.cur :=
  (Classical.choose_spec r.canonical).2

variable {n : Nat}

/-- A family of system participant runs. -/
abbrev SFamily (sp : Spec I O) (D : Type) (m n : Nat) := Fin n → Option (SRun sp D m)

def SEmits (F : SFamily sp D m n) (p : Fin n) (r : I × O) : Prop :=
  ∃ s, F p = some s ∧ r ∈ s.rows

def SSilent (F : SFamily sp D m n) (q : Fin n) : Prop :=
  ∃ s, F q = some s ∧ s.rows = []

/-- Each run's emitted rows lie in its participant's `A_p`. -/
def SAuthorized (Dp : Deployment sp n) (F : SFamily sp D m n) : Prop :=
  ∀ p r, SEmits F p r → Dp.A p r.1 r.2

/-- Separable under `comp` (as Def. `def:deployment`). -/
def SSeparable (F : SFamily sp D m n) (comp : Fin n → Nat) : Prop :=
  (∃ p q r r', SEmits F p r ∧ SEmits F q r' ∧ comp p ≠ comp q) ∨
  (∃ r₀ p q, SEmits F p r₀ ∧ (∀ p' r, SEmits F p' r → r = r₀) ∧
     SSilent F q ∧ comp q ≠ comp p)

def SUB (F : SFamily sp D m n) (j : I) : Prop := ∀ p s, F p = some s → s.fin.cur ≼ j

noncomputable def SFamily.toF (F : SFamily sp D m n) : Family sp n := fun p => (F p).map SRun.toP

theorem toF_emits (F : SFamily sp D m n) (p : Fin n) (r : I × O) :
    Emits F.toF p r ↔ SEmits F p r := by
  unfold Emits SEmits SFamily.toF
  cases h : F p with
  | none => simp
  | some s =>
    simp only [Option.map_some, Option.some.injEq, exists_eq_left', SRun.toP_rows]

theorem toF_silent (F : SFamily sp D m n) (q : Fin n) : Silent F.toF q ↔ SSilent F q := by
  unfold Silent SSilent SFamily.toF
  cases h : F q with
  | none => simp
  | some s =>
    simp only [Option.map_some, Option.some.injEq, exists_eq_left', SRun.toP_rows]

/-- **The deployment remark, end to end.**  If the specification is monotone
across `comp` (under the deployment), then for every family of *system*
participant runs whose emitted rows lie in their participants' `A_p` and
which is separable under `comp`, and every common expansion `j` of the runs'
current inputs, some `u ∈ S(j)` refines every emitted output. -/
theorem system_monoAcross (Dp : Deployment sp n) {comp : Fin n → Nat}
    (hmono : MonoAcross Dp comp) (F : SFamily sp D m n) (ha : SAuthorized Dp F)
    (hs : SSeparable F comp) (j : I) (hj : SUB F j) :
    ∃ u, sp.S j u ∧ ∀ p r, SEmits F p r → r.2 ≼ u := by
  have ha' : Authorized Dp F.toF := fun p r h => ha p r ((toF_emits F p r).1 h)
  have hs' : Separable F.toF comp := by
    rcases hs with ⟨p, q, r, r', h1, h2, h3⟩ | ⟨r₀, p, q, h1, h2, h3, h4⟩
    · exact Or.inl ⟨p, q, r, r', (toF_emits F p r).2 h1, (toF_emits F q r').2 h2, h3⟩
    · exact Or.inr ⟨r₀, p, q, (toF_emits F p r₀).2 h1,
        fun p' r h => h2 p' r ((toF_emits F p' r).1 h), (toF_silent F q).2 h3, h4⟩
  have hj' : UB F.toF j := by
    intro p q hq
    unfold SFamily.toF at hq
    cases h : F p with
    | none => rw [h] at hq; cases hq
    | some s =>
      rw [h] at hq; cases hq
      rw [SRun.toP_cur]; exact hj p s h
  obtain ⟨u, hu, hall⟩ := hmono F.toF ha' hs' j hj'
  exact ⟨u, hu, fun p r h => hall p r ((toF_emits F p r).2 h)⟩

/-- The same for the participant runs at a cut of a partitioned history: the
runs of all participants to the cut, as Deployment Availability permits
(their emitted rows lie in `A_p`), separable under the history's partition. -/
theorem history_monoAcross (Dp : Deployment sp n) (hmono : MonoAcrossPartitions Dp)
    (init : Fin n → I) (H : CAP.History sp D n) (comp : Fin n → Nat)
    (hP : CAP.Partitioned H comp) (c : Fin n → Nat) (σ : Fin n → State sp)
    (hσ : ∀ p, LRun (canon sp (init p)) ((H p).take (c p)) (σ p))
    (hsep : SSeparable (fun p => some ⟨init p, (H p).take (c p), σ p, hσ p⟩) comp)
    (hauth : ∀ p r, r ∈ emittedL (init p) ((H p).take (c p)) → Dp.A p r.1 r.2)
    (j : I) (hj : ∀ p, (σ p).cur ≼ j) :
    ∃ u, sp.S j u ∧ ∀ p r, r ∈ emittedL (init p) ((H p).take (c p)) → r.2 ≼ u := by
  let F : SFamily sp D n n := fun p => some ⟨init p, (H p).take (c p), σ p, hσ p⟩
  have hF : ∀ p r, SEmits F p r ↔ r ∈ emittedL (init p) ((H p).take (c p)) := by
    intro p r
    exact ⟨fun ⟨s, hs, hr⟩ => by cases hs; exact hr, fun h => ⟨_, rfl, h⟩⟩
  obtain ⟨u, hu, hall⟩ := system_monoAcross Dp (hmono comp hP.1) F
    (fun p r h => hauth p r ((hF p r).1 h)) hsep j
    (fun p s hs => by cases hs; exact hj p)
  exact ⟨u, hu, fun p r h => hall p r ((hF p r).2 h)⟩

/-- "It does not follow that the deployment authorizes any participant to emit
`u`": with fiber `{a, b, top}` (`a, b ≤ top`), `A_0 = {a}`, `A_1 = {b}`, the
specification is monotone (hence monotone across partitions), the family
"`0` emits `a`, `1` emits `b`" is authorized and separable, and its only common
refinement `top` is authorized to no participant. -/
def triD : Deployment CAP.triSpec 2 where
  A p _ u := if p = 0 then u = .a else u = .b
  sub _ _ _ _ := trivial

theorem unauthorized_refinement :
    MonoAcrossPartitions triD ∧
    ∃ (F : Family CAP.triSpec 2) (comp : Fin 2 → Nat), IsPartition comp ∧
      Authorized triD F ∧ Separable F comp ∧ UB F () ∧
      (∀ u, (∀ p r, Emits F p r → r.2 ≼ u) → u = .top) ∧ ∀ p, ¬ triD.A p () .top := by
  let out : Fin 2 → CAP.Tri := fun p => if p = 0 then .a else .b
  let F : Family CAP.triSpec 2 := fun p => some (oneShot CAP.triSpec () (out p) trivial)
  have hE : ∀ p r, Emits F p r ↔ r = ((), out p) := by
    intro p r
    constructor
    · rintro ⟨m, hm, hr⟩
      cases hm
      exact List.mem_singleton.1 (show r ∈ [((), out p)] from hr)
    · rintro rfl; exact ⟨_, rfl, show ((), out p) ∈ [((), out p)] from List.mem_singleton_self _⟩
  refine ⟨monoAcrossPartitions_of_liftedMono CAP.triSpec_liftedMono triD, F, fun p => p.val,
    ⟨0, 1, by decide⟩, ?_, ?_, fun _ _ _ => trivial, ?_, ?_⟩
  · intro p r h
    rw [hE] at h; subst h
    show if p = 0 then out p = .a else out p = .b
    by_cases hp : p = 0 <;> simp [out, hp]
  · exact Or.inl ⟨0, 1, ((), .a), ((), .b), (hE _ _).2 rfl, (hE _ _).2 rfl, by decide⟩
  · intro u hu
    have h1 : CAP.Tri.a ≼ u := hu 0 _ ((hE _ _).2 rfl)
    have h2 : CAP.Tri.b ≼ u := hu 1 _ ((hE _ _).2 rfl)
    rcases h1 with h1 | h1
    · subst h1; rcases h2 with h2 | h2 <;> cases h2
    · exact h1
  · intro p h
    show False
    revert h
    show ¬ (if p = 0 then CAP.Tri.top = .a else CAP.Tri.top = .b)
    split <;> exact fun h => CAP.Tri.noConfusion h


end Deploy
end CC
