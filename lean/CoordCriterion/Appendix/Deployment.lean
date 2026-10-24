import CoordCriterion.CAP.Model

/-!
# Availability and Confluence under a Deployment (Appendix E, `app:deployment`)

Namespace `CC.Deploy`.  This file formalizes:

* Def. `def:deployment`: deployments, participant run families, separability
  under a partition (`Deployment`, `PRun`, `Family`, `Separable`);
* Def. `def:monotone-across-partitions` (`MonoAcross`, `MonoAcrossPartitions`);
* Def. `def:deployment-availability` (`DeploymentAvailability`);
* Prop. `thm:complete-cap-deployment` in survivor form
  (`partition_compatibility`) and in confluence form
  (`partition_compatibility_confluent`);
* the surrounding claims of the appendix:
  - monotonicity implies monotonicity across partitions
    (`monoAcrossPartitions_of_liftedMono`);
  - with at least two participants and the full
    deployment `A_p = S`, monotonicity across partitions is monotonicity
    (`full_deployment_iff`, via `CC.ce_of_pairs`);
  - with the full deployment, Deployment Availability is the Availability of
    Section `sec:complete-cap` at the deployment's participant set
    (`deploymentAvailability_full`).

Further claims of the appendix: `Appendix/DeploymentExamples.lean` (chains
of emitted outputs, the leader example, single-authority deployments),
`Appendix/DeploymentSystems.lean` (the remark on system runs) and
`Appendix/Registers.lean` (subsection `app:registers`).

## Modeling choices

1. *Participants and deployments.*  The participant set is `Fin n`; a
   deployment is `A : Fin n → Table I O` with `A p ⊆ S`.  The paper's gloss
   "`(i,o) ∈ A_p` means that `p` may hold `i` as a current input" is *not*
   imposed as a restriction on inputs: Def. `def:deployment` itself only
   constrains a family's *emitted* rows (silent participants hold arbitrary
   inputs), and we follow the definition.
2. *Partitions.*  A partition is a labelling `comp : Fin n → Nat` with at
   least two distinct labels (as in `CC.CAP.Partitioned`).
3. *Participant run families.*  A family is `Fin n → Option (PRun sp)`: each
   participant has at most one canonical run (Section 3 `Exec` from
   `canon sp init`).  The emitted rows of a run are the pairs
   `(current input at the output event, output)` (`emitted`).  Arbitrary
   runs cover "every order of input arrival within each component".
4. *Separable.*  Either two emitted rows are emitted by participants in
   different components, or the set of emitted rows is a singleton `{r₀}` and
   some participant of the family whose run emits nothing lies in a component
   different from that of a participant emitting `r₀`.
5. *Deployment Availability.*  The paper's "commitments whose authority is
   entirely within the participant's component" is not defined anywhere (the
   paper defines no authority of a commitment).  We read locality exactly as
   in `CC.CAP.Availability`: the continuation is produced, stays partitioned
   by the same components, adds events only at the participant's component,
   adds no input event, and contains an output event `Out γ o` of the
   participant (so `γ` is any sequence of basis commitments).  The only
   change is that `o` must be authorized: `A p σ.cur o`.  Since a deployment
   fixes the participant set, Deployment Availability is stated for histories
   over `Fin n` only.
-/

namespace CC
namespace Deploy

open CC.CAP (step_input_inv step_output_inv)

variable {I O : Type} [PO I] [PO O]

/-! ## Deployments and participant run families -/

/-- Def. `def:deployment`: a deployment over participants `Fin n`. -/
structure Deployment (sp : Spec I O) (n : Nat) where
  A : Fin n → Table I O
  sub : ∀ p k u, A p k u → sp.S k u

/-- A partition: two or more nonempty components. -/
def IsPartition {n : Nat} (comp : Fin n → Nat) : Prop := ∃ p q, comp p ≠ comp q

/-- Emitted rows along an event list, starting at current input `c`. -/
def emitted (c : I) : List (Event I O) → List (I × O)
  | [] => []
  | .input j :: es => emitted j es
  | .output o :: es => (c, o) :: emitted c es

/-- A canonical (Section 3) run of one participant. -/
structure PRun (sp : Spec I O) where
  init : I
  es : List (Event I O)
  fin : State sp
  exec : Exec (canon sp init) es fin

/-- Emitted rows of a participant run. -/
def PRun.rows {sp : Spec I O} (m : PRun sp) : List (I × O) := emitted m.init m.es

/-- A finite participant run family over `Fin n`. -/
abbrev Family (sp : Spec I O) (n : Nat) := Fin n → Option (PRun sp)

variable {sp : Spec I O} {n : Nat}

/-- Participant `p` of the family emits row `r`. -/
def Emits (F : Family sp n) (p : Fin n) (r : I × O) : Prop :=
  ∃ m, F p = some m ∧ r ∈ m.rows

/-- Participant `q` belongs to the family and its run emits no output. -/
def Silent (F : Family sp n) (q : Fin n) : Prop :=
  ∃ m, F q = some m ∧ m.rows = []

/-- Every emitted row lies in its participant's authorized set. -/
def Authorized (Dp : Deployment sp n) (F : Family sp n) : Prop :=
  ∀ p r, Emits F p r → Dp.A p r.1 r.2

/-- Def. `def:deployment`: separable under the partition `comp`. -/
def Separable (F : Family sp n) (comp : Fin n → Nat) : Prop :=
  (∃ p q r r', Emits F p r ∧ Emits F q r' ∧ comp p ≠ comp q) ∨
  (∃ r₀ p q, Emits F p r₀ ∧ (∀ p' r, Emits F p' r → r = r₀) ∧
     Silent F q ∧ comp q ≠ comp p)

/-- `j` is a common expansion of the family's current inputs. -/
def UB (F : Family sp n) (j : I) : Prop := ∀ p m, F p = some m → m.fin.cur ≼ j

/-- Def. `def:monotone-across-partitions`: monotone across `comp`. -/
def MonoAcross (Dp : Deployment sp n) (comp : Fin n → Nat) : Prop :=
  ∀ F : Family sp n, Authorized Dp F → Separable F comp →
    ∀ j, UB F j → ∃ u, sp.S j u ∧ ∀ p r, Emits F p r → r.2 ≼ u

/-- Def. `def:monotone-across-partitions`: monotone across every partition. -/
def MonoAcrossPartitions (Dp : Deployment sp n) : Prop :=
  ∀ comp : Fin n → Nat, IsPartition comp → MonoAcross Dp comp

/-- Item (1) of Prop. `thm:complete-cap-deployment` (survivor form): some row
at `j` survives in every remainder table of the family. -/
def PartitionSurvivor (Dp : Deployment sp n) : Prop :=
  ∀ comp : Fin n → Nat, IsPartition comp →
    ∀ F : Family sp n, Authorized Dp F → Separable F comp →
      ∀ j, UB F j → ∃ u, sp.S j u ∧ ∀ p m, F p = some m → m.fin.R j u

/-- The final states of the family's runs. -/
def famStates (F : Family sp n) : List (State sp) :=
  (List.finRange n).filterMap (fun p => (F p).map PRun.fin)

/-- Item (1) of Prop. `thm:complete-cap-deployment` (confluence form): the
family's runs are confluent at `j`. -/
def PartitionConfluent (Dp : Deployment sp n) : Prop :=
  ∀ comp : Fin n → Nat, IsPartition comp →
    ∀ F : Family sp n, Authorized Dp F → Separable F comp →
      ∀ j, UB F j → ConfluentAt (famStates F) j

/-! ## Run lemmas -/

theorem emitted_exec {σ τ : State sp} {es : List (Event I O)} (hx : Exec σ es τ) :
    (emitted σ.cur es).map Prod.snd = outs es ∧
      ∀ r ∈ emitted σ.cur es, sp.S r.1 r.2 ∧ r.1 ≼ τ.cur := by
  induction hx with
  | nil => exact ⟨rfl, by simp [emitted]⟩
  | @cons σ τ' ρ e es hs hr ih =>
    cases e with
    | input j =>
      obtain ⟨_, hcur, _⟩ := step_input_inv hs
      rw [hcur] at ih
      exact ⟨by simpa [emitted, outs] using ih.1, by simpa [emitted] using ih.2⟩
    | output o =>
      obtain ⟨hleg, hcur, _⟩ := step_output_inv hs
      rw [hcur] at ih
      refine ⟨by simp [emitted, outs, ih.1], ?_⟩
      intro r hmem
      simp only [emitted, List.mem_cons] at hmem
      rcases hmem with rfl | hr'
      · refine ⟨σ.sub _ _ hleg, ?_⟩
        have := CAP.exec_cur_le hr; rw [hcur] at this; exact this
      · exact ih.2 r hr'

theorem PRun.rows_spec (m : PRun sp) :
    m.rows.map Prod.snd = outs m.es ∧ ∀ r ∈ m.rows, sp.S r.1 r.2 ∧ r.1 ≼ m.fin.cur :=
  emitted_exec m.exec

theorem PRun.mem_outs (m : PRun sp) {o : O} : o ∈ outs m.es ↔ ∃ r ∈ m.rows, r.2 = o := by
  rw [← m.rows_spec.1, List.mem_map]

theorem PRun.residual (m : PRun sp) :
    ∀ k u, m.fin.R k u ↔ (sp.S k u ∧ m.fin.cur ≼ k ∧ ∀ r ∈ m.rows, r.2 ≼ u) := by
  intro k u
  rw [run_residual m.exec k u]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun r hr => h3 _ (m.mem_outs.2 ⟨r, hr, rfl⟩)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun o ho => ?_⟩
    obtain ⟨r, hr, rfl⟩ := m.mem_outs.1 ho
    exact h3 r hr

/-- The one-output run `output o` from `σ_S(i)`. -/
def oneShot (sp : Spec I O) (i : I) (o : O) (h : sp.S i o) : PRun sp where
  init := i
  es := [.output o]
  fin := meetState sp i o h
  exec := by
    refine Exec.cons (τ := meetState sp i o h) (Step.output _ _ o ⟨h, PO.refl i⟩ rfl ?_) (Exec.nil _)
    funext k x
    apply propext
    simp only [meetState, outputTable, canon, and_assoc]

@[simp] theorem oneShot_rows (i : I) (o : O) (h : sp.S i o) :
    (oneShot sp i o h).rows = [(i, o)] := rfl

@[simp] theorem oneShot_cur (i : I) (o : O) (h : sp.S i o) :
    (oneShot sp i o h).fin.cur = i := rfl

/-! ## Prop. `thm:complete-cap-deployment` -/

/-- The per-family core: for a family with common expansion `j`, a row at `j`
survives in every remainder table iff the emitted outputs have a common
expansion in `S(j)`. -/
theorem survivor_iff_compatible (F : Family sp n) {j : I} (hj : UB F j) :
    (∃ u, sp.S j u ∧ ∀ p m, F p = some m → m.fin.R j u) ↔
      (∃ u, sp.S j u ∧ ∀ p r, Emits F p r → r.2 ≼ u) := by
  constructor
  · rintro ⟨u, hu, hall⟩
    refine ⟨u, hu, ?_⟩
    rintro p r ⟨m, hm, hr⟩
    exact ((m.residual j u).1 (hall p m hm)).2.2 r hr
  · rintro ⟨u, hu, hall⟩
    exact ⟨u, hu, fun p m hm =>
      (m.residual j u).2 ⟨hu, hj p m hm, fun r hr => hall p r ⟨m, hm, hr⟩⟩⟩

/-- **Prop. `thm:complete-cap-deployment`** (survivor form), proved as
stated. -/
theorem partition_compatibility (Dp : Deployment sp n) :
    PartitionSurvivor Dp ↔ MonoAcrossPartitions Dp := by
  constructor
  · intro h comp hc F ha hs j hj
    exact (survivor_iff_compatible F hj).1 (h comp hc F ha hs j hj)
  · intro h comp hc F ha hs j hj
    exact (survivor_iff_compatible F hj).2 (h comp hc F ha hs j hj)

theorem mem_famStates (F : Family sp n) (σ : State sp) :
    σ ∈ famStates F ↔ ∃ p m, F p = some m ∧ m.fin = σ := by
  simp only [famStates, List.mem_filterMap, List.mem_finRange, true_and,
    Option.map_eq_some_iff]

/-- **Prop. `thm:complete-cap-deployment`**, confluence form (via the
survivor test, Prop. `prop:confluence`). -/
theorem partition_compatibility_confluent (Dp : Deployment sp n) :
    PartitionConfluent Dp ↔ MonoAcrossPartitions Dp := by
  have key : ∀ (F : Family sp n) (j : I), UB F j →
      (ConfluentAt (famStates F) j ↔ ∃ u, sp.S j u ∧ ∀ p m, F p = some m → m.fin.R j u) := by
    intro F j hj
    have hrun : ∀ σ ∈ famStates F, IsRun σ := by
      intro σ hσ
      obtain ⟨p, m, _, rfl⟩ := (mem_famStates F σ).1 hσ
      exact ⟨m.init, m.es, m.exec⟩
    have hle : ∀ σ ∈ famStates F, σ.cur ≼ j := by
      intro σ hσ
      obtain ⟨p, m, hm, rfl⟩ := (mem_famStates F σ).1 hσ
      exact hj p m hm
    rw [survivor_test _ hrun j hle]
    constructor
    · rintro ⟨u, hu, hall⟩
      exact ⟨u, hu, fun p m hm => hall _ ((mem_famStates F _).2 ⟨p, m, hm, rfl⟩)⟩
    · rintro ⟨u, hu, hall⟩
      refine ⟨u, hu, fun σ hσ => ?_⟩
      obtain ⟨p, m, hm, rfl⟩ := (mem_famStates F σ).1 hσ
      exact hall p m hm
  rw [← partition_compatibility]
  constructor
  · intro h comp hc F ha hs j hj
    exact (key F j hj).1 (h comp hc F ha hs j hj)
  · intro h comp hc F ha hs j hj
    exact (key F j hj).2 (h comp hc F ha hs j hj)

/-! ## Monotonicity implies monotonicity across partitions -/

/-- All emitted rows of a family. -/
def allRows (F : Family sp n) : List (I × O) :=
  (List.finRange n).flatMap (fun p => match F p with | some m => m.rows | none => [])

theorem mem_allRows (F : Family sp n) (r : I × O) :
    r ∈ allRows F ↔ ∃ p, Emits F p r := by
  simp only [allRows, List.mem_flatMap, List.mem_finRange, true_and, Emits]
  constructor
  · rintro ⟨p, hp⟩
    revert hp
    cases h : F p with
    | none => simp
    | some m => intro hp; exact ⟨p, m, h, hp⟩
  · rintro ⟨p, m, hm, hr⟩
    exact ⟨p, by rw [hm]; exact hr⟩

/-- Monotonicity (Lifted Monotonicity) implies monotonicity across every
partition, for every deployment. -/
theorem monoAcrossPartitions_of_liftedMono (hlm : sp.LiftedMono) (Dp : Deployment sp n) :
    MonoAcrossPartitions Dp := by
  intro comp _ F _ _ j hj
  have hce := (liftedMono_iff_commonExpansion sp).1 hlm
  obtain ⟨u, hu, hall⟩ := hce (allRows F)
    (by
      intro r hr
      obtain ⟨p, m, hm, hr⟩ := (mem_allRows F r).1 hr
      exact (m.rows_spec.2 r hr).1) j
    (by
      intro r hr
      obtain ⟨p, m, hm, hr⟩ := (mem_allRows F r).1 hr
      exact PO.trans (m.rows_spec.2 r hr).2 (hj p m hm))
  exact ⟨u, hu, fun p r he => hall r ((mem_allRows F r).2 ⟨p, he⟩)⟩

/-! ## Full deployment: pairs suffice -/

/-- The family in which participants `0` and `1` each emit one row. -/
def pairFam (m₀ m₁ : PRun sp) : Family sp n := fun p =>
  if p.val = 0 then some m₀ else if p.val = 1 then some m₁ else none

theorem pairFam_some {m₀ m₁ : PRun sp} {p : Fin n} {m : PRun sp}
    (h : pairFam m₀ m₁ p = some m) : (p.val = 0 ∧ m = m₀) ∨ (p.val = 1 ∧ m = m₁) := by
  unfold pairFam at h
  by_cases h0 : p.val = 0
  · simp [h0] at h; exact Or.inl ⟨h0, h.symm⟩
  · by_cases h1 : p.val = 1
    · simp [h1] at h; exact Or.inr ⟨h1, h.symm⟩
    · simp [h0, h1] at h

/-- With at least two participants and the deployment that lets every
participant emit every row, monotonicity across partitions is monotonicity. -/
theorem full_deployment_iff (hn : 2 ≤ n) (Dp : Deployment sp n) (hA : ∀ p, Dp.A p = sp.S) :
    MonoAcrossPartitions Dp ↔ sp.LiftedMono := by
  refine ⟨fun h => ?_, fun h => monoAcrossPartitions_of_liftedMono h Dp⟩
  apply (liftedMono_iff_commonExpansion sp).2
  apply ce_of_pairs
  intro i₁ o₁ i₂ o₂ j h₁ h₂ hj₁ hj₂
  let p₀ : Fin n := ⟨0, by omega⟩
  let p₁ : Fin n := ⟨1, by omega⟩
  let F : Family sp n := pairFam (oneShot sp i₁ o₁ h₁) (oneShot sp i₂ o₂ h₂)
  have hF0 : F p₀ = some (oneShot sp i₁ o₁ h₁) := by simp [F, pairFam, p₀]
  have hF1 : F p₁ = some (oneShot sp i₂ o₂ h₂) := by simp [F, pairFam, p₁]
  have hcomp : IsPartition (fun p : Fin n => p.val) := ⟨p₀, p₁, by simp [p₀, p₁]⟩
  have hauth : Authorized Dp F := by
    rintro p r ⟨m, hm, hr⟩
    rw [hA p]
    rcases pairFam_some hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp at hr <;> subst hr <;> assumption
  have hsep : Separable F (fun p : Fin n => p.val) :=
    Or.inl ⟨p₀, p₁, (i₁, o₁), (i₂, o₂), ⟨_, hF0, by simp⟩, ⟨_, hF1, by simp⟩, by simp [p₀, p₁]⟩
  have hub : UB F j := by
    intro p m hm
    rcases pairFam_some hm with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact hj₁
    · exact hj₂
  obtain ⟨u, hu, hall⟩ := h _ hcomp F hauth hsep j hub
  exact ⟨u, hu, hall p₀ (i₁, o₁) ⟨_, hF0, by simp⟩, hall p₁ (i₂, o₂) ⟨_, hF1, by simp⟩⟩

/-! ## Def. `def:deployment-availability` -/

section Avail
open CC.CAP
variable {D : Type}

/-- The Availability of Section `sec:complete-cap` restricted to histories
over the participant set `Fin n`; `CAP.Availability` is `∀ n, AvailabilityAt`. -/
def AvailabilityAt (Sys : System sp D) (n : Nat) : Prop :=
  ∀ (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ c, IsCut H c →
    ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) ((H p).take (c p)) σ →
    ∀ o, σ.R σ.cur o →
    ∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)),
      Extends H c H' ext ∧ WF init H' ∧ Produced Sys n init H' ∧ Partitioned H' comp ∧
      (∀ q, comp q ≠ comp p → ext q = []) ∧
      (∀ q j, LEv.inp j ∉ ext q) ∧
      ∃ γ, LEv.out γ o ∈ ext p

theorem availability_iff (Sys : System sp D) :
    Availability Sys ↔ ∀ n, AvailabilityAt Sys n := Iff.rfl

/-- Def. `def:deployment-availability` (see modeling choice 5): every
surviving *authorized* row at a participant's current input can be emitted by
that participant using only events of its own component. -/
def DeploymentAvailability (Sys : System sp D) (Dp : Deployment sp n) : Prop :=
  ∀ (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ c, IsCut H c →
    ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) ((H p).take (c p)) σ →
    ∀ o, σ.R σ.cur o → Dp.A p σ.cur o →
    ∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)),
      Extends H c H' ext ∧ WF init H' ∧ Produced Sys n init H' ∧ Partitioned H' comp ∧
      (∀ q, comp q ≠ comp p → ext q = []) ∧
      (∀ q j, LEv.inp j ∉ ext q) ∧
      ∃ γ, LEv.out γ o ∈ ext p

/-- Availability implies Deployment Availability for every deployment. -/
theorem deploymentAvailability_of_availability (Sys : System sp D) (Dp : Deployment sp n)
    (h : AvailabilityAt Sys n) : DeploymentAvailability Sys Dp :=
  fun init H comp hwf hp hpart c hc p σ hσ o ho _ =>
    h init H comp hwf hp hpart c hc p σ hσ o ho

/-- With the full deployment `A_p = S`, Deployment Availability is the
Availability of Section `sec:complete-cap` (at the deployment's participant
set). -/
theorem deploymentAvailability_full (Sys : System sp D) (Dp : Deployment sp n)
    (hA : ∀ p, Dp.A p = sp.S) : DeploymentAvailability Sys Dp ↔ AvailabilityAt Sys n := by
  refine ⟨fun h => ?_, deploymentAvailability_of_availability Sys Dp⟩
  intro init H comp hwf hp hpart c hc p σ hσ o ho
  exact h init H comp hwf hp hpart c hc p σ hσ o ho (by rw [hA p]; exact σ.sub _ _ ho)

end Avail

end Deploy
end CC
