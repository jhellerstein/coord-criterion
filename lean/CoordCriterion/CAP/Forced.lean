import CoordCriterion.CAP.Necessity
import CoordCriterion.CAP.Register

/-!
# Forced responses: Gilbert–Lynch from the Complete CAP argument

The two-row case of the proof of Theorem `thm:complete-cap` uses Availability
only to let each of two participants, starting from the empty history, emit a
given output.  When that output is the only one permitted at the
participant's input, a weaker requirement suffices: that the participant can
emit *some* output (`AnsweringAtEnd`).  `cap_two_step_forced` is that
version of the two-row case.

For the register whose outputs answer every operation of the input
(`GL.regFullSpec`), the write's acknowledgment and the isolated read's `v0`
are such forced outputs, and no output at the history where the write
precedes the read refines the read's `v0`.  So no system for it has Answering
and keeps emitted outputs reconcilable (`CommonRefinementAtEnd`, the part of
Partition Consistency the argument uses): `GL.gilbert_lynch_direct`, the
Gilbert–Lynch theorem by the Complete CAP argument.
-/

namespace CC
namespace CAP

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type}

/-- Answering, at the end of histories: each participant `p`, in state
`σ = (i,R)`, can emit *some* output of `R(i)` in a continuation local to `p`. -/
def AnsweringAtEnd (Sys : System sp D) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) (H p) σ →
    ∃ o, σ.R σ.cur o ∧ ∃ ext : Fin n → List (LEv sp D n),
      WF init (fun q => H q ++ ext q) ∧ Produced Sys n init (fun q => H q ++ ext q) ∧
      Partitioned (fun q => H q ++ ext q) comp ∧
      (∀ q, comp q ≠ comp p → ext q = []) ∧
      (∀ q j, LEv.inp j ∉ ext q) ∧
      ∃ γ, LEv.out γ o ∈ ext p

/-- Availability implies Answering: the current fiber is nonempty. -/
theorem answering_of_availability {Sys : System sp D} (hA : AvailabilityAtEnd Sys) :
    AnsweringAtEnd Sys := by
  intro n init H comp hw hp hpt p σ hσ
  obtain ⟨o, ho⟩ := σ.hasCur
  exact ⟨o, ho, hA n init H comp hw hp hpt p σ hσ o ho⟩

/-- The part of Partition Consistency the two-row case uses: at the end of
every produced partitioned history, for every common expansion `j` of the
current inputs, some `u ∈ S(j)` refines every emitted output. -/
def CommonRefinementAtEnd (Sys : System sp D) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ j : I, (∀ p σ, LRun (canon sp (init p)) (H p) σ → σ.cur ≼ j) →
    ∃ u, sp.S j u ∧ ∀ p γ o, LEv.out γ o ∈ H p → o ≼ u

/-- Partition Consistency gives a common refinement: the common state `(j,R)`
has a row `(j,u)`, and rows are never added. -/
theorem commonRefinement_of_pc {Sys : System sp D} (hP : PartitionConsistencyAtEnd Sys) :
    CommonRefinementAtEnd Sys := by
  intro n init H comp hw hp hpt j hj
  obtain ⟨τ, hτj, ext, _, hτ⟩ := hP n init H comp hw hp hpt j hj
  obtain ⟨u, hu⟩ := τ.hasCur
  rw [hτj] at hu
  refine ⟨u, τ.sub _ _ hu, fun p γ o hγ => ?_⟩
  obtain ⟨σ', h2, h3⟩ := lrun_append.1 (hτ p)
  exact lrun_out_mem h2 hγ j u ((lrun_mono h3).2 j u hu)

/-- The two-row case with a weaker hypothesis: two participants in separate
blocks, starting at `init 0` and `init 1` from the empty history, can each
emit `outs p` without messages or inputs (`hE`).  A common refinement of the
emitted outputs (`hC`, implied by Partition Consistency) then lies in `S(j)`. -/
theorem two_core (Sys : System sp D) (hC : CommonRefinementAtEnd Sys)
    (init : Fin 2 → I) (outs : Fin 2 → O) {j : I} (hj : ∀ p, init p ≼ j)
    (hE : ∀ p : Fin 2, ∃ ext : Fin 2 → List (LEv sp D 2),
      WF init (fun q => ([] : List (LEv sp D 2)) ++ ext q) ∧
      Produced Sys 2 init (fun q => ([] : List (LEv sp D 2)) ++ ext q) ∧
      Partitioned (fun q => ([] : List (LEv sp D 2)) ++ ext q) (fun q => q.val) ∧
      (∀ q j, LEv.inp j ∉ ext q) ∧ ∃ γ, LEv.out γ (outs p) ∈ ext p) :
    ∃ u, sp.S j u ∧ ∀ p, outs p ≼ u := by
  classical
  let comp : Fin 2 → Nat := fun p => p.val
  have hcomp2 : ∃ p q : Fin 2, comp p ≠ comp q := ⟨0, 1, by simp [comp]⟩
  have hL : ∀ p : Fin 2, ∃ L : List (LEv sp D 2),
      (∃ τ, LRun (canon sp (init p)) L τ) ∧ (∀ (q : Fin 2) k j d, LEv.recv q k j d ∉ L) ∧
      Compliant (Allowed Sys 2 init p) L ∧ (∀ j, LEv.inp j ∉ L) ∧
      ∃ γ, LEv.out γ (outs p) ∈ L := by
    intro p
    obtain ⟨ext, hwf', hprod', hpart', hnoinp, γ, hγ⟩ := hE p
    refine ⟨ext p, ?_, ?_, ?_, hnoinp p, ⟨γ, hγ⟩⟩
    · obtain ⟨τ, h⟩ := hwf'.1 p; exact ⟨τ, by simpa using h⟩
    · intro q k j d hm
      obtain ⟨a, b, hab⟩ := List.append_of_mem hm
      have hab' : (fun q => ([] : List (LEv sp D 2)) ++ ext q) p = a ++ LEv.recv q k j d :: b := by
        simpa using hab
      exact (hwf'.2 p a q k j d b hab').1 (Fin.ext (hpart'.2 p a q k j d b hab'))
    · have := hprod' p; simpa using this
  let Lf : History sp D 2 := fun p => Classical.choose (hL p)
  have hLs : ∀ p, _ := fun p => Classical.choose_spec (hL p)
  have hnrecv : ∀ (p : Fin 2) a (q : Fin 2) k (j' : Option I) (d : D) b,
      Lf p ≠ a ++ LEv.recv q k j' d :: b := by
    intro p a q k j' d b h
    have hm : LEv.recv q k j' d ∈ Lf p := by rw [h]; simp
    exact (hLs p).2.1 q k j' d hm
  have hwfc : WF init Lf :=
    ⟨fun p => (hLs p).1, fun p a q k j' d b h => absurd h (hnrecv p a q k j' d b)⟩
  have hprodc : Produced Sys 2 init Lf := fun p => (hLs p).2.2.1
  have hpartc : Partitioned Lf comp :=
    ⟨hcomp2, fun p a q k j' d b h => absurd h (hnrecv p a q k j' d b)⟩
  have hjall : ∀ p σ, LRun (canon sp (init p)) (Lf p) σ → σ.cur ≼ j := by
    intro p σ h
    rw [lrun_noinp h (hLs p).2.2.2.1]
    exact hj p
  obtain ⟨u, hu, hall⟩ := hC 2 init Lf comp hwfc hprodc hpartc j hjall
  refine ⟨u, hu, fun p => ?_⟩
  obtain ⟨γ, hγ⟩ := (hLs p).2.2.2.2
  exact hall p γ _ hγ

/-- The two-row case with forced outputs: if `o₁` and `o₂` are the only
outputs permitted at `i₁` and `i₂`, Answering suffices in place of
Availability, and a common refinement in place of Partition Consistency. -/
theorem cap_two_step_forced (Sys : System sp D) (hA : AnsweringAtEnd Sys)
    (hC : CommonRefinementAtEnd Sys) {i₁ i₂ j : I} {o₁ o₂ : O}
    (h₁ : ∀ o, sp.S i₁ o → o = o₁) (h₂ : ∀ o, sp.S i₂ o → o = o₂)
    (hj₁ : i₁ ≼ j) (hj₂ : i₂ ≼ j) :
    ∃ u, sp.S j u ∧ o₁ ≼ u ∧ o₂ ≼ u := by
  classical
  let init : Fin 2 → I := fun p => if p.val = 0 then i₁ else i₂
  let outs : Fin 2 → O := fun p => if p.val = 0 then o₁ else o₂
  have hforced : ∀ p o, sp.S (init p) o → o = outs p := by
    intro p o h; simp only [init, outs] at h ⊢; split
    · next hp => simp only [hp, ↓reduceIte] at h; exact h₁ o h
    · next hp => simp only [hp, ↓reduceIte] at h; exact h₂ o h
  have hj : ∀ p, init p ≼ j := by
    intro p; simp only [init]; split
    · exact hj₁
    · exact hj₂
  let H0 : History sp D 2 := fun _ => []
  have hwf0 : WF init H0 :=
    ⟨fun p => ⟨_, .nil _⟩, by intro p a q k j d b h; simp [H0] at h⟩
  have hprod0 : Produced Sys 2 init H0 := fun p a e b h => by simp [H0] at h
  have hpart0 : Partitioned H0 (fun q => q.val) :=
    ⟨⟨0, 1, by simp⟩, by intro p a q k j d b h; simp [H0] at h⟩
  obtain ⟨u, hu, hall⟩ := two_core Sys hC init outs hj (fun p => by
    obtain ⟨o, ho, ext, hw, hpr, hpt, _, hni, hout⟩ :=
      hA 2 init H0 (fun q => q.val) hwf0 hprod0 hpart0 p _ (.nil _)
    have : o = outs p := hforced p o ho.1
    subst this
    exact ⟨ext, hw, hpr, hpt, hni, hout⟩)
  exact ⟨u, hu, by simpa [outs] using hall 0, by simpa [outs] using hall 1⟩

end CAP

namespace GL

open CAP

/-- The register whose outputs answer every operation of the input: maps
explained by a linearization that respond to every operation. -/
def regFull : Table Hist RMap := fun h ρ =>
  regS h ρ ∧ ∀ a op, h.ops a = some op → ρ.f a ≠ none

theorem regFull_total (h : Hist) : ∃ ρ, regFull h ρ := by
  obtain ⟨pos, hl⟩ := lin_exists h
  have hc : ∀ a, ∃ r : Option Resp, (h.ops a = none → r = none) ∧
      ∀ op, h.ops a = some op → ∃ x, r = some x ∧ RespOk h pos a op x := by
    intro a
    cases ho : h.ops a with
    | none => exact ⟨none, fun _ => rfl, fun _ h => by cases h⟩
    | some op =>
      rcases op with ⟨r, _ | w⟩
      · obtain ⟨v, hv⟩ := readVal_exists h pos a
        refine ⟨some (.val v), (fun h => by cases h), ?_⟩
        intro op' h'
        cases h'
        exact ⟨_, rfl, v, rfl, hv⟩
      · refine ⟨some .ack, (fun h => by cases h), ?_⟩
        intro op' h'
        cases h'
        exact ⟨_, rfl, rfl⟩
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice hc
  refine ⟨⟨f⟩, ⟨pos, hl, ?_⟩, ?_⟩
  · intro a r hr
    have hr : f a = some r := hr
    cases ho : h.ops a with
    | none => rw [(hf a).1 ho] at hr; cases hr
    | some op =>
      obtain ⟨x, hx, hok⟩ := (hf a).2 op ho
      rw [hx] at hr; cases hr
      exact ⟨op, rfl, hok⟩
  · intro a op ho
    obtain ⟨x, hx, _⟩ := (hf a).2 op ho
    show f a ≠ none
    rw [hx]; simp

/-- The complete-response register specification. -/
def regFullSpec : Spec Hist RMap where
  S := regFull
  total := regFull_total

/-- The acknowledgment of the write, the only output at `h1`. -/
def ackMap : RMap := ⟨fun a => if a = 0 then some .ack else none⟩

/-- The read's `v0`, the only output at `h2`. -/
def v0Map : RMap := ⟨fun a => if a = 1 then some (.val v0) else none⟩

theorem h1_forced (o : RMap) (ho : regFull h1 o) : o = ackMap := by
  obtain ⟨⟨pos, _, hex⟩, hans⟩ := ho
  apply RMap.ext'; funext a
  show o.f a = if a = 0 then some .ack else none
  split
  · next ha =>
    subst ha
    have hne := hans 0 wOp rfl
    cases hf : o.f 0 with
    | none => exact absurd hf hne
    | some r =>
      obtain ⟨op, hop, hok⟩ := hex 0 r hf
      have : op = wOp := by cases hop; rfl
      subst this
      show some r = some .ack
      rw [show r = .ack from hok]
  · next ha =>
    cases hf : o.f a with
    | none => rfl
    | some r =>
      obtain ⟨op, hop, _⟩ := hex a r hf
      exact absurd (h1_ops hop).1 ha

theorem h2_forced (o : RMap) (ho : regFull h2 o) : o = v0Map := by
  have h1' : o.f 1 = some (.val v0) := h2_answer ⟨ho.1, fun a op h _ => ho.2 a op h⟩
  obtain ⟨⟨pos, _, hex⟩, _⟩ := ho
  apply RMap.ext'; funext a
  show o.f a = if a = 1 then some (.val v0) else none
  split
  · next ha => subst ha; exact h1'
  · next ha =>
    cases hf : o.f a with
    | none => rfl
    | some r =>
      obtain ⟨op, hop, _⟩ := hex a r hf
      exact absurd (h2_ops hop).1 ha

/-- Every output at `hj`, where the write of `1` precedes the read, answers
that same read (operation `1`) with the written value `1 ≠ v0`. -/
theorem hj_reads_write (u : RMap) (hu : regFull hj u) : u.f 1 = some (.val 1) := by
  obtain ⟨⟨pos, hl, hex⟩, hans⟩ := hu
  cases hf : u.f 1 with
  | none => exact absurd hf (hans 1 rOp rfl)
  | some r =>
    obtain ⟨op, hop, hok⟩ := hex 1 r hf
    have hop' : op = rOp := by
      rcases hj_ops hop with ⟨h', _⟩ | ⟨_, h'⟩
      · cases h'
      · exact h'
    subst hop'
    obtain ⟨v, rfl, hrv⟩ := hok
    have hp : pos 0 < pos 1 := hl.2 0 1 ⟨rfl, rfl⟩
    rcases hrv with ⟨_, hno⟩ | ⟨w, ⟨r', hw'⟩, _, _⟩
    · exact absurd hp (hno 0 1 ⟨0, rfl⟩)
    · rcases hj_ops hw' with ⟨_, he⟩ | ⟨_, he⟩
      · simp only [wOp, Op.mk.injEq, Kind.write.injEq] at he
        rw [he.2]
      · simp [rOp] at he

/-- **Gilbert–Lynch, by the Complete CAP argument.**  No system for the
complete-response register lets every participant answer and keeps the
emitted outputs reconcilable: the write's acknowledgment at `h1` and the
read's `v0` at `h2` are forced, and no output at `hj`, where the write
precedes the read, refines `v0`. -/
theorem gilbert_lynch_direct {D : Type} (Sys : System regFullSpec D) :
    ¬ (AnsweringAtEnd Sys ∧ CommonRefinementAtEnd Sys) := by
  rintro ⟨hA, hC⟩
  obtain ⟨u, hu, _, h2u⟩ := cap_two_step_forced Sys hA hC (i₁ := h1) (i₂ := h2) (j := hj)
    h1_forced h2_forced h1_le h2_le
  have : u.f 1 = some (.val v0) := h2u 1 _ (by simp [v0Map])
  exact hj_noread u hu.1 this

/-- In particular no system for it has Availability and Partition
Consistency. -/
theorem gilbert_lynch_direct_cap {D : Type} (Sys : System regFullSpec D) :
    ¬ (AvailabilityAtEnd Sys ∧ PartitionConsistencyAtEnd Sys) := fun ⟨hA, hP⟩ =>
  gilbert_lynch_direct Sys ⟨answering_of_availability hA, commonRefinement_of_pc hP⟩

/-- Consequently the complete-response register fails Lifted Monotonicity. -/
theorem regFullSpec_not_liftedMono : ¬ regFullSpec.LiftedMono := by
  intro h
  obtain ⟨hA, hP⟩ := complete_cap_cf regFullSpec Unit h
  exact gilbert_lynch_direct_cap (cfSystem regFullSpec Unit)
    ⟨(availability_iff_atEnd _).1 hA, (partitionConsistency_iff_atEnd _).1 hP⟩

end GL
end CC
