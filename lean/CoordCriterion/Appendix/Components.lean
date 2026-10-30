import CoordCriterion.Appendix.Guarded
import CoordCriterion.Appendix.JointMono

/-!
# Component implementations and typed pipelines (Appendix D)

Namespace `CC.Components`.  A thin composition layer above the system model:
a *component implementation* of one specification exposes only the
output-annotated runs it admits, each certified legal under its commitment
basis and a row of its specification.  A *typed pipeline* joins two component
implementations with different specifications through a hidden *feed
witness*: one admitted upstream run and one admitted downstream run whose
boundary values agree.  Its external observation keeps only the upstream's
initial input and the downstream's output.

Adapted from the opaque component layer of the foundation development
(`det_foundation`, `DetFoundation/Composition/Components.lean`).  Sequential
composition is the library's `Comp.seq`; the values an upstream can offer are
`Joint.Img`; restricted common expansion is `Joint.CEOn`.

* `LocationForm`, `OperationalRun`, `OperationalRun.Valid`, `Component`,
  `Component.ofBasis`, `Component.ofSys`, `emptyBasis` — the boundary.  The
  location form (process, cluster, composite) is metadata and occurs in no
  proof obligation.
* `BoundaryObservation`, `FeedWitness`, `Pipeline`, `Pipeline.compositeSpec`,
  `Pipeline.Accepts`, `Pipeline.sound` — typed pipelines and boundary safety.
* `Pipeline.ContractProper` (the downstream satisfies Lifted Monotonicity on
  the values the upstream contract can offer) with `JointMonoOn`,
  `contractProper_iff_guardProper`, `contractProper_iff_jointMonoOn`,
  `contractProper_iff_rest`, `contractProper_liftedMono`.
* `Pipeline.Proper` (implementation properness: every downstream run admitted
  in a feed uses no commitment), `proper_of_downstream_commitmentFree`,
  `proper_downstream_execCF`, `ofBasis_empty_commitmentFree`.
* Contract properness does not give implementation properness or availability:
  `Component.silent` (admits nothing; vacuously proper), `early_lock_component`
  (a contract-proper pipeline whose downstream deliberately commits),
  `threshold_component` (a contract-proper pipeline whose maximally permissive
  empty-basis downstream, typed at all of `M`, admits no run at an offered
  value).
* Bridges to `Appendix/Guarded.lean`: `Component.core` (an upstream
  implementation retyped at its offered outputs), `Pipeline.offered`,
  `offered_compositeSpec` (`Guard.seq_core`), `offered_contractProper_iff`,
  `offered_available` (on the offered interface the empty-basis downstream
  admits a commitment-free following run for every admitted upstream run),
  `Component.proper_follows`, `Component.proper_run` (Theorem
  `thm:proper-coordination`(2) for the runs a component admits),
  `ofSys_free`, `ofSys_eraseSys_commitmentFree`.

Modeling choices: an `OperationalRun` names its initial input and one emitted
output; `Valid.contract` asks that this pair be a row of the specification.
"Commitment-free" is the library's `CoordFree` (no output event applies a
commitment, no commit event).  It is a property of runs, not coordination,
which the paper judges relative to a run universe.  Receiving the feed value
is the downstream's initial input, not a commitment.
-/

namespace CC
namespace Components

open Comp Joint Guard

/-! ## The component boundary -/

/-- Optional implementation-form metadata: one process, a cluster of
participants, or a composite.  It has no role in any proof. -/
inductive LocationForm where
  | process
  | cluster
  | composite
  deriving DecidableEq

section Boundary
variable {I O : Type} [PO I] [PO O]

/-- An output-annotated run at a component boundary: the initial input, one
emitted output, the system events, and the final state. -/
structure OperationalRun (sp : Spec I O) where
  input : I
  output : O
  events : List (SEvent sp)
  final : State sp

/-- The certificate for an admitted run: it is an execution under the basis
from the canonical state at its input, it emits its named output, and the
input/output pair is a row of the specification. -/
structure OperationalRun.Valid {sp : Spec I O} (B : Basis sp) (r : OperationalRun sp) :
    Prop where
  legal : SysExec B (canon sp r.input) r.events r.final
  emits : ∃ γ, SEvent.output γ r.output ∈ r.events
  contract : sp.S r.input r.output

/-- **A component implementation** of `sp`: a commitment basis, the admitted
runs, and their soundness certificates.  `location` is metadata. -/
structure Component (sp : Spec I O) where
  location : Option LocationForm := none
  basis : Basis sp
  accepts : OperationalRun sp → Prop
  sound : ∀ r, accepts r → r.Valid basis

/-- The empty commitment basis. -/
abbrev emptyBasis (sp : Spec I O) : Basis sp := fun _ => False

/-- The maximally permissive implementation under a basis: it admits every
valid run. -/
def Component.ofBasis {sp : Spec I O} (B : Basis sp) (location : Option LocationForm := none) :
    Component sp where
  location := location
  basis := B
  accepts r := r.Valid B
  sound _ h := h

/-- The implementation that admits no run. -/
def Component.silent (sp : Spec I O) : Component sp where
  basis := emptyBasis sp
  accepts _ := False
  sound _ h := False.elim h

/-- The implementation given by a one-participant system of
`Appendix/Guarded.lean` (a basis and a strategy): the runs it produces, with a
named output that is a row at the initial input. -/
def Component.ofSys {sp : Spec I O} (K : Guard.Sys sp) (location : Option LocationForm := none) :
    Component sp where
  location := location
  basis := K.basis
  accepts r := Guard.Produces K r.input r.events r.final ∧
    (∃ γ, SEvent.output γ r.output ∈ r.events) ∧ sp.S r.input r.output
  sound _ h := ⟨h.1.1, h.2.1, h.2.2⟩

theorem Component.ofBasis_accepts {sp : Spec I O} (B : Basis sp) (location : Option LocationForm)
    (r : OperationalRun sp) : (Component.ofBasis B location).accepts r ↔ r.Valid B := Iff.rfl

theorem Component.ofSys_accepts {sp : Spec I O} (K : Guard.Sys sp) (location : Option LocationForm)
    (r : OperationalRun sp) :
    (Component.ofSys K location).accepts r ↔ Guard.Produces K r.input r.events r.final ∧
      (∃ γ, SEvent.output γ r.output ∈ r.events) ∧ sp.S r.input r.output := Iff.rfl

/-- A component implementation is **commitment-free** when no run it admits
applies a commitment. -/
def Component.CommitmentFree {sp : Spec I O} (c : Component sp) : Prop :=
  ∀ r, c.accepts r → CoordFree r.events

/-- An execution under the empty basis applies no commitment. -/
theorem sysExec_emptyBasis_coordFree {sp : Spec I O} {σ τ : State sp} {es : List (SEvent sp)}
    (h : SysExec (emptyBasis sp) σ es τ) : CoordFree es := by
  induction h with
  | nil => exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h)⟩
  | @cons σ τ ρ e es hs _ ih =>
    refine ⟨fun γ o hm => ?_, fun γ hm => ?_⟩
    · rcases List.mem_cons.1 hm with he | hm
      · subst he
        cases hs with
        | output hb _ _ _ _ _ =>
          cases γ with
          | nil => rfl
          | cons c _ => exact (hb c List.mem_cons_self).elim
      · exact ih.1 γ o hm
    · rcases List.mem_cons.1 hm with he | hm
      · subst he
        cases hs with
        | commit hb hne _ =>
          cases γ with
          | nil => exact absurd rfl hne
          | cons c _ => exact (hb c List.mem_cons_self).elim
      · exact ih.2 γ hm

/-- The maximally permissive implementation under the empty basis is
commitment-free. -/
theorem ofBasis_empty_commitmentFree {sp : Spec I O} (location : Option LocationForm := none) :
    (Component.ofBasis (emptyBasis sp) location).CommitmentFree :=
  fun r h => sysExec_emptyBasis_coordFree ((Component.ofBasis_accepts _ _ r).1 h).legal

/-- Every run of a commitment-free implementation erases to a commitment-free
execution from the canonical state at its input. -/
theorem Component.CommitmentFree.execCF {sp : Spec I O} {c : Component sp}
    (hc : c.CommitmentFree) {r : OperationalRun sp} (h : c.accepts r) :
    ExecCF (canon sp r.input) (r.events.filterMap SEvent.erase) r.final :=
  coordFree_execCF (c.sound r h).legal (hc r h)

/-- The strategy that allows every event admits exactly the valid runs. -/
theorem ofSys_free {sp : Spec I O} (B : Basis sp) (location : Option LocationForm)
    (r : OperationalRun sp) :
    (Component.ofSys (Guard.Sys.free B) location).accepts r ↔
      (Component.ofBasis B location).accepts r :=
  ⟨fun h => let h := (Component.ofSys_accepts _ _ r).1 h
      (Component.ofBasis_accepts _ _ r).2 ⟨h.1.1, h.2.1, h.2.2⟩,
    fun h => let h := (Component.ofBasis_accepts _ _ r).1 h
      (Component.ofSys_accepts _ _ r).2 ⟨produces_free.2 h.legal, h.emits, h.contract⟩⟩

/-- The commitment-erased replacement of any one-participant system
(`Guard.eraseSys`) is a commitment-free implementation. -/
theorem ofSys_eraseSys_commitmentFree {sp : Spec I O} (K : Guard.Sys sp)
    (location : Option LocationForm) : (Component.ofSys (eraseSys K) location).CommitmentFree :=
  fun r h => let h := (Component.ofSys_accepts _ _ r).1 h
    ⟨eraseSys_eps h.1, eraseSys_noCommit h.1⟩

end Boundary

/-! ## Typed pipelines -/

section Pipelines
variable {I M O : Type} [PO I] [PO M] [PO O]

/-- A pipeline's external observation: the first input and the final output.
The intermediate value and both traces are absent from this type. -/
structure BoundaryObservation (I O : Type) where
  input : I
  output : O

/-- **A hidden feed witness**: an admitted upstream run and an admitted
downstream run whose boundary values agree. -/
structure FeedWitness {upSpec : Spec I M} {downSpec : Spec M O}
    (upstream : Component upSpec) (downstream : Component downSpec) where
  upRun : OperationalRun upSpec
  downRun : OperationalRun downSpec
  upAccepted : upstream.accepts upRun
  downAccepted : downstream.accepts downRun
  feed : upRun.output = downRun.input

/-- **A binary typed pipeline**: implementations of `S₁ : I ↔ M` and
`S₂ : M ↔ O`. -/
structure Pipeline (upSpec : Spec I M) (downSpec : Spec M O) where
  upstream : Component upSpec
  downstream : Component downSpec

/-- The external contract `S₂ ∘ S₁`. -/
def Pipeline.compositeSpec {upSpec : Spec I M} {downSpec : Spec M O}
    (_p : Pipeline upSpec downSpec) : Spec I O := seq upSpec downSpec

/-- The observation a feed witness exposes. -/
def FeedWitness.boundary {upSpec : Spec I M} {downSpec : Spec M O}
    {upstream : Component upSpec} {downstream : Component downSpec}
    (w : FeedWitness upstream downstream) : BoundaryObservation I O :=
  ⟨w.upRun.input, w.downRun.output⟩

/-- A pipeline admits the observations of its feed witnesses. -/
def Pipeline.Accepts {upSpec : Spec I M} {downSpec : Spec M O}
    (p : Pipeline upSpec downSpec) (obs : BoundaryObservation I O) : Prop :=
  ∃ w : FeedWitness p.upstream p.downstream, w.boundary = obs

/-- A feed witness joins a row of `S₁` and a row of `S₂` at the fed value. -/
theorem FeedWitness.contracts {upSpec : Spec I M} {downSpec : Spec M O}
    {upstream : Component upSpec} {downstream : Component downSpec}
    (w : FeedWitness upstream downstream) :
    upSpec.S w.upRun.input w.upRun.output ∧ downSpec.S w.upRun.output w.downRun.output :=
  ⟨(upstream.sound _ w.upAccepted).contract,
    w.feed ▸ (downstream.sound _ w.downAccepted).contract⟩

/-- **Boundary safety**: every observation a pipeline admits is a row of
`S₂ ∘ S₁`. -/
theorem Pipeline.sound {upSpec : Spec I M} {downSpec : Spec M O}
    (p : Pipeline upSpec downSpec) {obs : BoundaryObservation I O} (h : p.Accepts obs) :
    p.compositeSpec.S obs.input obs.output := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨w.upRun.output, w.contracts⟩

/-! ### Contract properness -/

/-- Lifted Monotonicity of `G` between inputs in `D`, in the joint-lift form. -/
def JointMonoOn (D : M → Prop) (G : Spec M O) : Prop :=
  ∀ i j, D i → D j → i ≼ j → JointLift (G.S i) (G.S j)

/-- The joint-lift form and the common-expansion form `Joint.CEOn` agree. -/
theorem jointMonoOn_iff_ceOn (D : M → Prop) (G : Spec M O) : JointMonoOn D G ↔ CEOn G D := by
  constructor
  · intro hG rows hrows j hDj hj
    induction rows with
    | nil =>
      obtain ⟨u, hu⟩ := G.total j
      exact ⟨u, hu, by simp⟩
    | cons r rows ih =>
      obtain ⟨a, ha, hta⟩ := ih (fun q hq => hrows q (List.mem_cons_of_mem _ hq))
        (fun q hq => hj q (List.mem_cons_of_mem _ hq))
      have hr := hrows r List.mem_cons_self
      obtain ⟨b, hb, hrb⟩ := hG r.1 j hr.1 hDj (hj r List.mem_cons_self) [r.2] (by simp)
        (by simp [hr.2])
      obtain ⟨u, hu, hab⟩ := hG j j hDj hDj (PO.refl j) [a, b] (by simp) (by simp [ha, hb])
      refine ⟨u, hu, fun q hq => ?_⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · exact PO.trans (hrb _ (by simp)) (hab b (by simp))
      · exact PO.trans (hta q hq) (hab a (by simp))
  · intro hC i j hDi hDj hij X _ hX
    obtain ⟨u, hu, hall⟩ := hC (X.map fun x => (i, x))
      (by
        intro r hr
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
        exact ⟨hDi, hX x hx⟩)
      j hDj
      (by
        intro r hr
        obtain ⟨x, _, rfl⟩ := List.mem_map.1 hr
        exact hij)
    exact ⟨u, hu, fun x hx => hall (i, x) (List.mem_map.2 ⟨x, hx, rfl⟩)⟩

/-- **Contract properness**: `S₂` satisfies Lifted Monotonicity on the values
`S₁` can offer.  It mentions neither implementation. -/
def Pipeline.ContractProper {upSpec : Spec I M} {downSpec : Spec M O}
    (_p : Pipeline upSpec downSpec) : Prop :=
  CEOn downSpec (Img upSpec)

/-- Contract properness is Proper Coordination (`Guard.Proper`,
Def. `def:proper-coordination`). -/
theorem contractProper_iff_guardProper {upSpec : Spec I M} {downSpec : Spec M O}
    (p : Pipeline upSpec downSpec) : p.ContractProper ↔ Guard.Proper upSpec downSpec :=
  proper_iff.symm

theorem contractProper_iff_jointMonoOn {upSpec : Spec I M} {downSpec : Spec M O}
    (p : Pipeline upSpec downSpec) : p.ContractProper ↔ JointMonoOn (Img upSpec) downSpec :=
  (jointMonoOn_iff_ceOn _ _).symm

/-- Contract properness is Lifted Monotonicity of `𝒮₂|_{𝒮₁}`. -/
theorem contractProper_iff_rest {upSpec : Spec I M} {downSpec : Spec M O}
    (p : Pipeline upSpec downSpec) : p.ContractProper ↔ (rest upSpec downSpec).LiftedMono :=
  ceOn_iff_restrictTo _ _

/-- A monotone upstream contract and a contract-proper edge have a monotone
composite. -/
theorem contractProper_liftedMono {upSpec : Spec I M} {downSpec : Spec M O}
    (p : Pipeline upSpec downSpec) (hup : upSpec.LiftedMono) (hp : p.ContractProper) :
    p.compositeSpec.LiftedMono :=
  seq_liftedMono_img hup hp

/-! ### Implementation properness -/

/-- **Implementation properness**: every downstream run admitted in a feed
applies no commitment. -/
def Pipeline.Proper {upSpec : Spec I M} {downSpec : Spec M O}
    (p : Pipeline upSpec downSpec) : Prop :=
  ∀ w : FeedWitness p.upstream p.downstream, CoordFree w.downRun.events

theorem proper_of_downstream_commitmentFree {upSpec : Spec I M} {downSpec : Spec M O}
    (p : Pipeline upSpec downSpec) (h : p.downstream.CommitmentFree) : p.Proper :=
  fun w => h _ w.downAccepted

/-- In an implementation-proper pipeline every admitted downstream run erases
to a commitment-free execution. -/
theorem proper_downstream_execCF {upSpec : Spec I M} {downSpec : Spec M O}
    {p : Pipeline upSpec downSpec} (hp : p.Proper) (w : FeedWitness p.upstream p.downstream) :
    ExecCF (canon downSpec w.downRun.input) (w.downRun.events.filterMap SEvent.erase)
      w.downRun.final :=
  coordFree_execCF (p.downstream.sound _ w.downAccepted).legal (hp w)

/-- A silent downstream makes any pipeline implementation-proper, and the
pipeline admits no observation. -/
theorem proper_silent {upSpec : Spec I M} {downSpec : Spec M O} (up : Component upSpec) :
    (Pipeline.mk up (Component.silent downSpec)).Proper ∧
      ∀ obs, ¬ (Pipeline.mk up (Component.silent downSpec)).Accepts obs :=
  ⟨fun w => False.elim w.downAccepted, fun _ ⟨w, _⟩ => w.downAccepted⟩

end Pipelines

/-! ## Contract properness does not give implementation properness -/

section EarlyLock
open Inst (Pfx smrS1)

/-- The log at the empty proposal stream emits the empty log, under any
basis. -/
theorem smr_empty_run {Cmd : Type} (B : Basis (smrS1 (Cmd := Cmd))) :
    ∃ ρ, SysExec B (canon smrS1 ⟨[]⟩) [.output [] ⟨[]⟩] ρ := by
  have ho : (canon (smrS1 (Cmd := Cmd)) ⟨[]⟩).R ⟨[]⟩ ⟨[]⟩ := ⟨(fun _ h => nomatch h), PO.refl _⟩
  have hex : Exposable (canon (smrS1 (Cmd := Cmd)) ⟨[]⟩) ⟨[]⟩ :=
    fun _ x _ hn => absurd ⟨x.l, rfl⟩ hn
  exact ⟨outState _ _ ho, .cons (τ := outState _ _ ho) (eps_step_iff.2 ⟨ho, hex, rfl, rfl⟩) (.nil _)⟩

/-- **A contract-proper pipeline need not be implementation-proper.**  With
the log `smrS1` upstream and the table of a monotone `f` downstream, the edge
is contract-proper (`f` is monotone everywhere).  The downstream implemented
by the early-lock store (`Guard.earlyLock`) admits, in a feed from the empty
log, a run whose output event takes the lock. -/
theorem early_lock_component {Cmd O : Type} [PO O] {f : Pfx Cmd → O} (hf : Monotone f)
    (b : Cmd) :
    let p : Pipeline (smrS1 (Cmd := Cmd)) (graph f) :=
      ⟨Component.ofBasis (emptyBasis _), Component.ofSys (earlyLock b f)⟩
    p.ContractProper ∧ ¬ p.Proper := by
  intro p
  refine ⟨ceOn_of_ce (graph_commonExpansion hf) _, fun hp => ?_⟩
  obtain ⟨ρ, hρ⟩ := smr_empty_run (Cmd := Cmd) (emptyBasis _)
  let e : Pfx Cmd := ⟨[]⟩
  let kb : Pfx Cmd := ⟨[b]⟩
  let σ0 := canon (graph f) e
  have hn : ¬ bFirst b σ0.cur := fun h => by change (none : Option Cmd) = some b at h; cases h
  have hrow : ∃ k x, σ0.R k x ∧ bFirst b k := ⟨kb, f kb, ⟨rfl, ⟨[b], rfl⟩⟩, rfl⟩
  have happ : (sealIn (bFirst b) : Commitment (graph f)).app σ0 =
      some (sealInState σ0 (bFirst b) hn) := sealInApp_eq.2 ⟨hn, hrow, rfl⟩
  let σc := sealInState σ0 (bFirst b) hn
  have ho : σc.R σc.cur (f e) := ⟨⟨rfl, PO.refl _⟩, hn⟩
  have hstep : SysStep (mutexB b f) σ0 (.output [sealIn (bFirst b)] (f e)) (outState σc (f e) ho) :=
    .output (fun c hc => by simp at hc; exact hc) (.cons happ (.nil _)) ho
      (store_exposable hf σc) rfl rfl
  have hstrat : Guard.Allowed (earlyLock b f) e [] (.output [sealIn (bFirst b)] (f e)) :=
    ⟨fun δ x h => by cases h; exact ⟨fun _ => rfl, fun hn' => absurd ⟨rfl, rfl⟩ hn'⟩,
      fun _ h => by cases h⟩
  let w : FeedWitness p.upstream p.downstream :=
    { upRun := ⟨⟨[]⟩, ⟨[]⟩, [.output [] ⟨[]⟩], ρ⟩
      downRun := ⟨e, f e, [.output [sealIn (bFirst b)] (f e)], outState σc (f e) ho⟩
      upAccepted := (Component.ofBasis_accepts _ _ _).2
        ⟨hρ, ⟨[], List.mem_cons_self⟩, fun _ h => nomatch h⟩
      downAccepted := (Component.ofSys_accepts _ _ _).2
        ⟨⟨.cons hstep (.nil _), compliant_snoc (l := []) compliant_nil hstrat⟩,
          ⟨_, List.mem_cons_self⟩, rfl⟩
      feed := rfl }
  exact List.cons_ne_nil _ _ ((hp w).1 _ _ List.mem_cons_self)

end EarlyLock

section Threshold
open Dist (B2)

/-- Along an empty-basis execution of the threshold store, `(10, no)` stays
while the current count is at most `9`, and the answer yes is never emitted. -/
theorem thr_never_yes {σ τ : State thr} {es : List (SEvent thr)}
    (h : SysExec (emptyBasis thr) σ es τ) :
    (σ.cur ≤ 9 → σ.R 10 false) → ∀ γ : List (Commitment thr), SEvent.output γ (true : B2) ∉ es := by
  induction h with
  | nil => intro _ _ h; cases h
  | @cons σ τ ρ e es hs _ ih =>
    intro hinv γ hm
    cases e with
    | commit δ =>
      cases hs with
      | commit hb hne _ =>
        cases δ with
        | nil => exact hne rfl
        | cons c _ => exact (hb c List.mem_cons_self).elim
    | input j =>
      cases hs with
      | input hst =>
        obtain ⟨⟨u, hu⟩, hcur, hR⟩ := CAP.step_input_inv hst
        have hle : σ.cur ≤ j := σ.above _ _ hu
        refine ih (fun hj => ?_) γ (by simpa using hm)
        rw [hcur] at hj
        rw [hR]
        exact ⟨hinv (by omega), show j ≤ 10 by omega⟩
    | output δ o =>
      cases hs with
      | output hb hγ ho hexp hcur hR =>
        cases δ with
        | cons c _ => exact (hb c List.mem_cons_self).elim
        | nil =>
          have e : ∀ {x : State thr}, ApplySeq [] σ x → x = σ := fun h => by cases h; rfl
          rw [e hγ] at ho hexp
          have hoe : o = below σ.cur := σ.sub _ _ ho
          by_cases hc : σ.cur ≤ 9
          · have hyes : o = true := by
              rw [hoe]; show decide (σ.cur < 10) = true
              exact decide_eq_true (by omega)
            subst hyes
            obtain ⟨u, _, h1, h2⟩ := hexp 10 false (hinv hc)
              (fun h => Bool.noConfusion (h : (true : Bool) = false))
            exact Bool.noConfusion ((h1 : (true : Bool) = u).trans (h2 : (false : Bool) = u).symm)
          · rcases List.mem_cons.1 hm with he | hm
            · cases he
              have hf : below σ.cur = false := by
                show decide (σ.cur < 10) = false
                exact decide_eq_false (by omega)
              rw [hf] at hoe
              exact nomatch hoe
            · exact ih (fun hj => absurd (by rw [← hcur]; exact hj) hc) γ hm

/-- **Contract properness on `M` is not enough for the empty-basis
downstream typed at all of `M`.**  For the capped counter feeding the
threshold test: the edge is contract-proper; the empty-basis upstream admits a
run at every input; but the maximally permissive empty-basis implementation
of the threshold test admits no run at any offered value, so the pipeline
admits no observation. -/
theorem threshold_component :
    let p : Pipeline up thr := ⟨Component.ofBasis (emptyBasis _), Component.ofBasis (emptyBasis _)⟩
    p.ContractProper ∧ (∀ i, ∃ r, p.upstream.accepts r ∧ r.input = i) ∧
      (∀ r, p.downstream.accepts r → ¬ Img up r.input) ∧ ∀ obs, ¬ p.Accepts obs := by
  intro p
  have hdown : ∀ r, p.downstream.accepts r → ¬ Img up r.input := by
    intro r hr ⟨i, hi⟩
    have hr : r.Valid (emptyBasis thr) := hr
    have hm : r.input ≤ 9 := by
      have e : r.input = min i 9 := hi
      omega
    have hyes : r.output = true := by
      have e : r.output = below r.input := hr.contract
      rw [e]; show decide (r.input < 10) = true; simp; omega
    obtain ⟨γ, hγ⟩ := hr.emits
    rw [hyes] at hγ
    refine thr_never_yes hr.legal (fun _ => ⟨rfl, show r.input ≤ 10 by omega⟩) γ hγ
  refine ⟨(threshold.2.2.2 : Guard.Proper up thr) |> proper_iff.1, fun i => ?_, hdown, ?_⟩
  · have ho : (canon up i).R i (cap i) := ⟨rfl, PO.refl _⟩
    have hex : Exposable (canon up i) (cap i) :=
      store_exposable (f := cap) cap_monotone (canon up i)
    exact ⟨⟨i, cap i, [.output [] (cap i)], outState _ _ ho⟩,
      (Component.ofBasis_accepts _ _ _).2
        ⟨.cons (τ := outState _ _ ho) (eps_step_iff.2 ⟨ho, hex, rfl, rfl⟩) (.nil _),
          ⟨[], List.mem_cons_self⟩, rfl⟩, rfl⟩
  · rintro obs ⟨w, _⟩
    exact hdown _ w.downAccepted (w.feed ▸ ⟨_, w.contracts.1⟩)

end Threshold

/-! ## Bridges to Proper Coordination (`Appendix/Guarded.lean`) -/

section Bridges
variable {I M O : Type} [PO I] [PO M] [PO O]

theorem mem_emitted {sp : Spec I M} {γ : List (Commitment sp)} {m : M} :
    ∀ {es : List (SEvent sp)}, SEvent.output γ m ∈ es → m ∈ emitted es
  | [], h => by cases h
  | e :: es, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact List.mem_cons_self
    · cases e with
      | input _ => exact (mem_emitted h' : m ∈ emitted es)
      | commit _ => exact (mem_emitted h' : m ∈ emitted es)
      | output _ _ => exact List.mem_cons_of_mem _ (mem_emitted h')

theorem emitted_mem {sp : Spec I M} {m : M} :
    ∀ {es : List (SEvent sp)}, m ∈ emitted es → ∃ γ, SEvent.output γ m ∈ es
  | [], h => by cases h
  | e :: es, h => by
    cases e with
    | input _ =>
      obtain ⟨γ, hγ⟩ := emitted_mem (es := es) h
      exact ⟨γ, List.mem_cons_of_mem _ hγ⟩
    | commit _ =>
      obtain ⟨γ, hγ⟩ := emitted_mem (es := es) h
      exact ⟨γ, List.mem_cons_of_mem _ hγ⟩
    | output γ' m' =>
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨γ', List.mem_cons_self⟩
      · obtain ⟨γ, hγ⟩ := emitted_mem (es := es) h
        exact ⟨γ, List.mem_cons_of_mem _ hγ⟩

/-- **An upstream implementation retyped at its offered outputs.**  The runs
of `core 𝒮₁` (outputs typed as outputs of `𝒮₁`) under its canonical basis
that match an admitted run of `c` in input, named output, and emitted
outputs. -/
def Component.core {sp : Spec I M} (c : Component sp) : Component (Guard.core sp) where
  location := c.location
  basis := canonBasis (Guard.core sp)
  accepts r' := (∃ r, c.accepts r ∧ r'.input = r.input ∧ r'.output.1 = r.output ∧
      (emitted r'.events).map Subtype.val = emitted r.events) ∧ r'.Valid (canonBasis (Guard.core sp))
  sound _ h := h.2

theorem Component.core_accepts_iff {sp : Spec I M} (c : Component sp)
    (r' : OperationalRun (Guard.core sp)) :
    c.core.accepts r' ↔ (∃ r, c.accepts r ∧ r'.input = r.input ∧ r'.output.1 = r.output ∧
      (emitted r'.events).map Subtype.val = emitted r.events) ∧
      r'.Valid (canonBasis (Guard.core sp)) := Iff.rfl

/-- Every admitted run of `c` has a retyped counterpart (`Guard.core_lockstep`). -/
theorem Component.core_accepts {sp : Spec I M} (c : Component sp) {r : OperationalRun sp}
    (h : c.accepts r) : ∃ r', c.core.accepts r' ∧ r'.input = r.input ∧ r'.output.1 = r.output := by
  have hv := c.sound r h
  obtain ⟨es', ρ', hx, _, hem, _, _⟩ :=
    core_lockstep hv.legal (canon (Guard.core sp) r.input) rfl (fun _ _ h => h)
  obtain ⟨γ, hγ⟩ := hv.emits
  have hin : r.output ∈ (emitted es').map Subtype.val := by rw [hem]; exact mem_emitted hγ
  obtain ⟨m', hm', hmv⟩ := List.mem_map.1 hin
  obtain ⟨γ', hγ'⟩ := emitted_mem hm'
  have hc : (Guard.core sp).S r.input m' := by
    show sp.S r.input m'.1
    rw [hmv]; exact hv.contract
  exact ⟨⟨r.input, m', es', ρ'⟩,
    (c.core_accepts_iff _).2 ⟨⟨r, h, rfl, hmv, hem⟩, ⟨hx, ⟨γ', hγ'⟩, hc⟩⟩, rfl, hmv⟩

/-- The pipeline typed at the offered interface: the upstream retyped by
`Component.core`, and an implementation of `𝒮₂|_{𝒮₁}`. -/
def Pipeline.offered {sp : Spec I M} {sk : Spec M O} (c : Component sp)
    (k : Component (rest sp sk)) : Pipeline (Guard.core sp) (rest sp sk) := ⟨c.core, k⟩

/-- Its external contract is still `S₂ ∘ S₁` (`Guard.seq_core`). -/
theorem offered_compositeSpec {sp : Spec I M} {sk : Spec M O} (c : Component sp)
    (k : Component (rest sp sk)) : (Pipeline.offered c k).compositeSpec = seq sp sk :=
  seq_core sp sk

/-- On the offered interface, contract properness is Proper Coordination. -/
theorem offered_contractProper_iff {sp : Spec I M} {sk : Spec M O} (c : Component sp)
    (k : Component (rest sp sk)) : (Pipeline.offered c k).ContractProper ↔ Guard.Proper sp sk := by
  rw [proper_iff_ce]
  constructor
  · intro h rows hr j hj
    exact h rows (fun r hm => ⟨r.1.2, hr r hm⟩) j j.2 hj
  · intro h
    exact ceOn_of_ce h _

/-- **Availability on the offered interface.**  If Proper Coordination holds,
then for every run an upstream implementation admits, the maximally
permissive empty-basis implementation of `𝒮₂|_{𝒮₁}` admits a following run:
a feed witness whose upstream run has the same input and named output and
whose downstream run, from the fed value, emits one exposable answer.  The
pipeline is implementation-proper. -/
theorem offered_available {sp : Spec I M} {sk : Spec M O} (hP : Guard.Proper sp sk)
    (c : Component sp) {r : OperationalRun sp} (h : c.accepts r) :
    let p := Pipeline.offered (sk := sk) c (Component.ofBasis (emptyBasis _))
    p.Proper ∧ ∃ w : FeedWitness p.upstream p.downstream,
      w.upRun.input = r.input ∧ w.upRun.output.1 = r.output ∧ CoordFree w.downRun.events := by
  intro p
  have hC := proper_iff_ce.1 hP
  obtain ⟨r', hr', hin, hout⟩ := c.core_accepts h
  obtain ⟨o, ho⟩ := (rest sp sk).total r'.output
  let τ := canon (rest sp sk) r'.output
  have ho' : τ.R τ.cur o := ⟨ho, PO.refl _⟩
  have hex : Exposable τ o := commonExpansion_exposable hC ⟨_, [], .nil _⟩ ho'
  have hx : SysExec (emptyBasis (rest sp sk)) τ [.output [] o] (outState τ o ho') :=
    .cons (τ := outState τ o ho') (eps_step_iff.2 ⟨ho', hex, rfl, rfl⟩) (.nil _)
  let w : FeedWitness p.upstream p.downstream :=
    { upRun := r', downRun := ⟨r'.output, o, [.output [] o], outState τ o ho'⟩
      upAccepted := hr'
      downAccepted := (Component.ofBasis_accepts _ _ _).2 ⟨hx, ⟨[], List.mem_cons_self⟩, ho⟩
      feed := rfl }
  exact ⟨proper_of_downstream_commitmentFree p (ofBasis_empty_commitmentFree _),
    w, hin, hout, sysExec_emptyBasis_coordFree hx⟩

/-- **Theorem `thm:proper-coordination`(2), following, for the runs an
implementation admits.**  In a proper pipeline, for every run an upstream
implementation admits that emits `m :: ms`, the empty-basis `𝒮₂|_{𝒮₁}`
follows it, and the merged trace is a run of `S₂ ∘ S₁` (`Guard.proper_follows`). -/
theorem Component.proper_follows {sp : Spec I M} {sk : Spec M O} (hP : Guard.Proper sp sk)
    (c : Component sp) {r : OperationalRun sp} (h : c.accepts r) {m : M} {ms : List M}
    (he : emitted r.events = m :: ms) :
    ∃ (hm : Img sp m) (o : O) (ps : List ({m // Img sp m} × O))
      (esK : List (SEvent (rest sp sk))) (ρK : State (rest sp sk)),
      ps.map (fun p => p.1.1) = ms ∧ esK.filterMap SEvent.erase = .output o :: storeTr ps ∧
      Produces (noStore (rest sp sk)) ⟨m, hm⟩ esK ρK ∧
      ∃ ρ' : State (seq sp sk),
        Exec (canon (seq sp sk) r.input) (merge r.events ([o] :: ps.map fun p => [p.2])) ρ' ∧
        ρ'.cur = r.final.cur :=
  Guard.proper_follows hP (c.sound r h).legal he

/-- **Theorem `thm:proper-coordination`(2), the composite run, for the runs an
implementation admits** (`Guard.proper_run`): any empty-basis run of
`𝒮₂|_{𝒮₁}` that receives each output of an admitted upstream run and answers
it any number of times gives a run of `S₂ ∘ S₁` whose table contains the
join. -/
theorem Component.proper_run {sp : Spec I M} {sk : Spec M O} (hP : Guard.Proper sp sk)
    (c : Component sp) {r : OperationalRun sp} (h : c.accepts r) {m : {m // Img sp m}}
    {ms : List {m // Img sp m}} (he : emitted r.events = m.1 :: ms.map Subtype.val) {os : List O}
    {ps : List ({m // Img sp m} × List O)} (hps : ps.map Prod.fst = ms)
    {esK : List (SEvent (rest sp sk))} {ρK : State (rest sp sk)}
    (hK : SysExec (emptyBasis _) (canon (rest sp sk) m) esK ρK)
    (htr : esK.filterMap SEvent.erase = os.map Event.output ++ blk ps) :
    ∃ ρ' : State (seq sp sk),
      Exec (canon (seq sp sk) r.input) (merge r.events (os :: ps.map Prod.snd)) ρ' ∧
      ρ'.cur = r.final.cur ∧
      (∀ k m x (h : Img sp m), r.final.R k m → ρK.R ⟨m, h⟩ x → ρ'.R k x) ∧
      IsRun ρK ∧ ∀ k m, r.final.R k m → ρK.cur.1 ≼ m :=
  Guard.proper_run hP (c.sound r h).legal he hps hK htr

end Bridges

end Components
end CC
