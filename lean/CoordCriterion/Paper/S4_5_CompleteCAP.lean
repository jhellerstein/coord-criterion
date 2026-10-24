import CoordCriterion.CAP.ResponseAvailability
import CoordCriterion.CAP.AvailabilityAtEnd
import CoordCriterion.CAP.Necessity
import CoordCriterion.CAP.Forced
import CoordCriterion.CAP.AsyncGilbertLynch
import CoordCriterion.Appendix.DeploymentExamples
import CoordCriterion.Appendix.Registers

/-!
# Paper §4.5, "The Complete CAP Theorem" (`sections/distributed.tex`)

Statement layer for Section `sec:complete-cap`, from the subsection header to
the end of `sections/distributed.tex`: Definition `def:partition-notions`,
Theorem `thm:complete-cap` (with its "moreover" clause), the remarks after its
proof, and the claims of the paragraph "Gilbert and Lynch".

How to read this file: open it next to the `.tex` file.  The `/-! ## … -/`
headers follow the paper's (sub)sections and paragraphs, in paper order.  Each
numbered result is a declaration named by its LaTeX label in guillemets
(`CC.Paper.«thm:complete-cap»`); unlabeled claims of the text are named
`«<enclosing label>/<slug>»`.  Each docstring quotes the paper (LaTeX lightly
normalized to Unicode) and, where the Lean statement reads differently, says
how they correspond.  Every statement is written out in full in terms of the
library definitions; every proof is a one-line pointer into the library
(`CoordCriterion/CAP/…`, `CoordCriterion/Appendix/…`).

The system model and its precise readings are documented in
`CoordCriterion/CAP/Model.lean` (participants `Fin n`, histories as local event
lists, cuts as prefix lengths, nondeterministic strategies, produced
histories, partitions as labellings `comp : Fin n → Nat`).
-/

namespace CC.Paper

open CC CC.CAP

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type} {n : Nat}

/-! ## §4.5 The Complete CAP Theorem

### Definition `def:partition-notions` (Partitioned history, Availability, Partition Consistency) -/

/-- Def. `def:partition-notions`(1), *Partitioned history*: "A partitioned
history divides the participants into two or more components and contains no
receive whose matching send lies in another component; participants still
receive environment input and emit outputs."

Lean: a component labelling `comp : Fin n → Nat` with two distinct labels and
no receive from a participant with another label. -/
abbrev «def:partition-notions(1)» (H : History sp D n) (comp : Fin n → Nat) : Prop :=
  Partitioned H comp

/-- Def. `def:partition-notions`(1), unfolded. -/
theorem «def:partition-notions(1)/unfolded» (H : History sp D n) (comp : Fin n → Nat) :
    Partitioned H comp ↔
      (∃ p q, comp p ≠ comp q) ∧
      ∀ (p : Fin n) (a : List (LEv sp D n)) (q : Fin n) (k : Nat) (j : Option I) (d : D) b,
        H p = a ++ LEv.recv q k j d :: b → comp q = comp p :=
  Iff.rfl

/-- Def. `def:partition-notions`(2), *System*: "Fix a system
(Definition `def:system`); we additionally require a strategy for each
participant of every finite participant set and every choice of initial
inputs, each depending only on its participant's local history."

Lean: `System sp D` has a commitment basis and a nondeterministic strategy
`strat n init p pre e` for every `n`, `init : Fin n → I`, participant `p`.
"Depending only on the local history" is the definition of `Produced`: each
event of `p` is checked against `p`'s own local prefix only. -/
abbrev «def:partition-notions(2)» (sp : Spec I O) (D : Type) : Type := System sp D

/-- Def. `def:partition-notions`(2): a history is *produced* by the system
when each participant's events are allowed given its own local prefix. -/
theorem «def:partition-notions(2)/produced» (Sys : System sp D) (init : Fin n → I)
    (H : History sp D n) :
    Produced Sys n init H ↔
      ∀ p a e b, H p = a ++ e :: b → Allowed Sys n init p a e :=
  Iff.rfl

/-- Def. `def:partition-notions`(3), *Environment*: "The environment is
adversarial: it may supply any legal input event to any participant."

Lean: input events are always allowed (their legality is checked by the run
relation `LRun` inside well-formedness `WF`). -/
theorem «def:partition-notions(3)» (Sys : System sp D) (init : Fin n → I) (p : Fin n)
    (pre : List (LEv sp D n)) (j : I) :
    Allowed Sys n init p pre (.inp j) :=
  trivial

/-- Def. `def:partition-notions`(4), *Availability*: "A continuation of a
partitioned history is local to a participant `p` when the system produces it,
it adds only events of `p`'s component and no input events, and none of its
receives takes a message sent from another component.  The system has
Availability when, in every partitioned history it produces, each participant
`p`, ending in state `(i,R)`, can emit each output in `R(i)` in some
continuation local to `p`."  In the unfolded form below, "local to `p`" is the
conjunction `Produced … ∧ Partitioned … comp ∧ (∀ q, comp q ≠ comp p → ext q =
[]) ∧ (∀ q j, inp j ∉ ext q)`. -/
abbrev «def:partition-notions(4)» (Sys : System sp D) : Prop := AvailabilityAtEnd Sys

/-- Def. `def:partition-notions`(4), unfolded.  `WF init H` is "a history"
(legal local runs from `σ_S(init p)`, matched receives); `σ` is `p`'s final
state `(i,R)`; the continuation appends `ext q` to each `H q`. -/
theorem «def:partition-notions(4)/unfolded» (Sys : System sp D) :
    AvailabilityAtEnd Sys ↔
      ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
        WF init H → Produced Sys n init H → Partitioned H comp →
        ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) (H p) σ →
        ∀ o, σ.R σ.cur o →
        ∃ ext : Fin n → List (LEv sp D n),
          WF init (fun q => H q ++ ext q) ∧ Produced Sys n init (fun q => H q ++ ext q) ∧
          Partitioned (fun q => H q ++ ext q) comp ∧
          (∀ q, comp q ≠ comp p → ext q = []) ∧
          (∀ q j, LEv.inp j ∉ ext q) ∧
          ∃ γ, LEv.out γ o ∈ ext p :=
  Iff.rfl

/-- Def. `def:partition-notions`(4): asking at every consistent cut of every
produced partitioned history (`Availability`, the form the library proofs use)
is the same as asking at the end of every such history, because a produced
partitioned history restricted to a consistent cut is again one. -/
theorem «def:partition-notions(4)/at-cuts» (Sys : System sp D) :
    Availability Sys ↔ «def:partition-notions(4)» Sys :=
  availability_iff_atEnd Sys

/-- Def. `def:partition-notions`(5), *Partition Consistency*: "The system has
Partition Consistency when the final cut of every such history is confluent at
every common expansion of the participants' current inputs.  The continuation
that confluence asks for need not stay partitioned and need not be produced by
the system." -/
abbrev «def:partition-notions(5)» (Sys : System sp D) : Prop := PartitionConsistencyAtEnd Sys

/-- Def. `def:partition-notions`(5), unfolded: for each `j` above every
participant's final current input, a well-formed continuation (neither
partitioned nor produced) puts every participant in one state `τ` with
current input `j`. -/
theorem «def:partition-notions(5)/unfolded» (Sys : System sp D) :
    PartitionConsistencyAtEnd Sys ↔
      ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
        WF init H → Produced Sys n init H → Partitioned H comp →
        ∀ j : I, (∀ p σ, LRun (canon sp (init p)) (H p) σ → σ.cur ≼ j) →
        ∃ τ : State sp, τ.cur = j ∧ ∃ ext : Fin n → List (LEv sp D n),
          WF init (fun q => H q ++ ext q) ∧ ∀ p, LRun (canon sp (init p)) (H p ++ ext p) τ :=
  Iff.rfl

/-- Def. `def:partition-notions`(5): asking at every consistent cut of every
produced partitioned history (`PartitionConsistency`, the form the library
proofs use) is the same as asking at the final cut. -/
theorem «def:partition-notions(5)/at-cuts» (Sys : System sp D) :
    PartitionConsistency Sys ↔ «def:partition-notions(5)» Sys :=
  partitionConsistency_iff_atEnd Sys

/-! ### Theorem `thm:complete-cap` -/

/-- **Theorem `thm:complete-cap` (Complete CAP).**  "For an ordered relational
specification `S`, the following are equivalent: (1) some system has
Availability and Partition Consistency; (2) `S` satisfies Lifted
Monotonicity."

Lean: `D` is the (arbitrary) type of message payloads. -/
theorem «thm:complete-cap» (sp : Spec I O) (D : Type) :
    (∃ Sys : System sp D, «def:partition-notions(4)» Sys ∧ «def:partition-notions(5)» Sys) ↔
      sp.LiftedMono :=
  ⟨fun ⟨Sys, hA, hP⟩ => cap_necessary_two Sys hA hP,
   fun h => ⟨cfSystem sp D, (availability_iff_atEnd _).1 (cf_availability h),
     (partitionConsistency_iff_atEnd _).1 (cf_partitionConsistency h)⟩⟩

/-- Theorem `thm:complete-cap`, "moreover" clause: "when they hold, a
commitment-free system has both properties: one whose strategies may emit any
exposable output `o` by `Out_ε(o)`."

Lean: `cfSystem` has empty basis and allows every event; an output event
`Out ε o` is legal exactly when `o` is exposable.  Every history it produces
is commitment-free. -/
theorem «thm:complete-cap/moreover» (sp : Spec I O) (D : Type) (h : sp.LiftedMono) :
    («def:partition-notions(4)» (cfSystem sp D) ∧ «def:partition-notions(5)» (cfSystem sp D)) ∧
    ∀ (N : Nat) (init : Fin N → I) (H : History sp D N),
      Produced (cfSystem sp D) N init H → ∀ p γ o, LEv.out γ o ∈ H p → γ = [] :=
  ⟨⟨(availability_iff_atEnd _).1 (complete_cap_cf sp D h).1,
      (partitionConsistency_iff_atEnd _).1 (complete_cap_cf sp D h).2⟩,
    fun _ _ _ => cfSystem_coordinationFree⟩

/-- Proof of Theorem `thm:complete-cap`, (2)⇒(1), last sentence: "By
Complete CALM, `S` is consistent, so it has distributed consistency
(Proposition `prop:distributed-consistency`), which gives Partition
Consistency."  Strong reading: the confluence
continuation itself can be chosen commitment-free and receive-free
(`PartitionConsistencyCF`), i.e. a history of Section `sec:histories`. -/
theorem «thm:complete-cap/proof-cf-continuations» (sp : Spec I O) (D : Type) :
    ((∃ Sys : System sp D, Availability Sys ∧ PartitionConsistency Sys) → sp.LiftedMono) ∧
    (sp.LiftedMono → Availability (cfSystem sp D) ∧ PartitionConsistencyCF (cfSystem sp D)) :=
  complete_cap_strong sp D

/-- Proof of Theorem `thm:complete-cap`, (1)⇒(2), the two-row case: "First
take two rows `(i,o)` and `(i',o')` with a common expansion `j`; we find some
`u ∈ S(j)` that refines both `o` and `o'`.  Place two participants in separate
components, starting at inputs `i` and `i'`.  Each runs without messages.  By
Availability, they can emit `o` and `o'`.  By Partition Consistency, they then
reach one state `(j,R)`, which has some row `(j,u)`; this `u` is the one we
seek. … so `u` refines `o` and `o'`." -/
theorem «thm:complete-cap/proof-two-step» (Sys : System sp D)
    (hA : «def:partition-notions(4)» Sys) (hP : «def:partition-notions(5)» Sys)
    {i₁ i₂ j : I} {o₁ o₂ : O} (h₁ : sp.S i₁ o₁) (h₂ : sp.S i₂ o₂) (hj₁ : i₁ ≼ j) (hj₂ : i₂ ≼ j) :
    ∃ u, sp.S j u ∧ o₁ ≼ u ∧ o₂ ≼ u :=
  cap_two_step Sys hA hP h₁ h₂ hj₁ hj₂

/-- Proof of Theorem `thm:complete-cap`, (1)⇒(2): "Now let
`(i_1,o_1),…,(i_k,o_k)` be rows with a common expansion `j`; we find some
`u ∈ S(j)` that refines every `o_r`.  We show by induction on `m ≤ k` that some `u_m ∈ S(j)` refines each of `o_1,…,o_m`.  For
`m=0` there is nothing to refine; since `S` is total, `j` appears in some row
`(j,u_0)`.  For
`m>0`, `(j,u_{m-1})` and `(i_m,o_m)` are rows of `S` with common expansion
`j`, so the two-row case gives some `u_m ∈ S(j)` that refines `u_{m-1}` and
`o_m`.  Since `u_{m-1}` refines `o_1,…,o_{m-1}`, so does `u_m`, by
transitivity.  Taking `m=k`, `u=u_k` refines every `o_r`, and Proposition `prop:common-expansion-form` gives Lifted
Monotonicity."  Lean: induction on the list of rows, each step by
`«thm:complete-cap/proof-two-step»`. -/
theorem «thm:complete-cap/proof-necessity» (Sys : System sp D)
    (hA : «def:partition-notions(4)» Sys) (hP : «def:partition-notions(5)» Sys) :
    sp.LiftedMono :=
  cap_necessary_two Sys hA hP

/-! ### Remarks after the proof -/

/-- "The two-row case never assumes that the system is commitment-free, so
local commitments cannot enlarge the class of specifications that admit a
system with Availability and Partition Consistency."  Lean: necessity holds
for an arbitrary system (any basis, any nondeterministic local strategies). -/
theorem «sec:complete-cap/necessity-any-system» (Sys : System sp D)
    (hA : «def:partition-notions(4)» Sys) (hP : «def:partition-notions(5)» Sys) :
    sp.LiftedMono :=
  cap_necessary_two Sys hA hP

/-- "Nor are they needed: when Lifted Monotonicity holds, the
commitment-free system already has both properties." -/
theorem «sec:complete-cap/commitments-not-needed» (sp : Spec I O) (D : Type)
    (h : sp.LiftedMono) :
    «def:partition-notions(4)» (cfSystem sp D) ∧ «def:partition-notions(5)» (cfSystem sp D) :=
  («thm:complete-cap/moreover» sp D h).1

/-- "The two-row case also shows what Partition Consistency demands: two
outputs emitted in separate components must have a common refinement at a
common expansion of their inputs."  Lean: for any system with both
properties, two rows below `j` have a common refinement in `S(j)`. -/
theorem «sec:complete-cap/pc-demand» (Sys : System sp D)
    (hA : «def:partition-notions(4)» Sys) (hP : «def:partition-notions(5)» Sys)
    {i₁ i₂ j : I} {o₁ o₂ : O} (h₁ : sp.S i₁ o₁) (h₂ : sp.S i₂ o₂) (hj₁ : i₁ ≼ j) (hj₂ : i₂ ≼ j) :
    ∃ u, sp.S j u ∧ o₁ ≼ u ∧ o₂ ≼ u :=
  cap_two_step Sys hA hP h₁ h₂ hj₁ hj₂

/-- "When Lifted Monotonicity fails, some permitted output either waits for
another component, sacrificing Availability, or is emitted independently at
the cost of Partition Consistency." -/
theorem «sec:complete-cap/lm-fails» (hlm : ¬ sp.LiftedMono) (Sys : System sp D) :
    ¬ «def:partition-notions(4)» Sys ∨ ¬ «def:partition-notions(5)» Sys :=
  (Classical.em («def:partition-notions(4)» Sys)).elim
    (fun hA => Or.inr fun hP => hlm (cap_necessary_two Sys hA hP)) Or.inl

/-- Precise reading (not a claim of the paper): Def. `def:system` speaks of "a
rule that chooses" the next events.  Strategies must be read as
nondeterministic: with deterministic strategies (2)⇒(1) fails, since a lone
participant cannot have two incomparable outputs both available.  Witness:
`triSpec` (one input, fiber `{a, b, ⊤}`) satisfies Lifted Monotonicity, yet no
deterministic system for it has Availability. -/
theorem «sec:complete-cap/deterministic-strategies» (D : Type) :
    triSpec.LiftedMono ∧
    ∀ Sys : System triSpec D, Sys.Deterministic → ¬ Availability Sys :=
  ⟨triSpec_liftedMono, deterministic_not_available D⟩

/-! ### Paragraph "Gilbert and Lynch" -/

/-- "Model a register whose input is the set of operations a participant
knows, with their real-time precedence, and whose outputs answer every
operation of the input as some linearization does.  Let `p`'s input be a write
of `v ≠ v_0` and `q`'s a read; the only outputs they permit are the
acknowledgment and `v_0`.  Where the write precedes the read, every output
returns `v`, so `v_0` has no refinement there."  Lean: the complete-response
register `regFullSpec`; the fibers at `h1` (the write) and `h2` (the read) are
singletons; no output at `hj` (write before read) returns `v0`; hence Lifted
Monotonicity fails. -/
theorem «sec:complete-cap/gl-register» :
    (∀ o, CC.GL.regFull CC.GL.h1 o → o = CC.GL.ackMap) ∧
    (∀ o, CC.GL.regFull CC.GL.h2 o → o = CC.GL.v0Map) ∧
    (∀ u, CC.GL.regFull CC.GL.hj u → u.f 1 ≠ some (.val CC.GL.v0)) ∧
    ¬ CC.GL.regFullSpec.LiftedMono :=
  ⟨CC.GL.h1_forced, CC.GL.h2_forced, fun u hu h => CC.GL.hj_noread u hu.1 h,
    CC.GL.regFullSpec_not_liftedMono⟩

/-- "In the two-row case, Availability is needed only so that `p` can emit
the acknowledgment and `q` can emit `v_0`.  Each is the only output its input
permits, so it is enough that every request receive some response …
Partition Consistency is needed only to give a common refinement of the two
emitted outputs."  Lean: the two-row case with Answering in place of
Availability, for outputs forced at their inputs, and a common refinement of
the emitted outputs in place of Partition Consistency. -/
theorem «sec:complete-cap/gl-two-row-forced» (Sys : System sp D)
    (hA : AnsweringAtEnd Sys) (hC : CommonRefinementAtEnd Sys) {i₁ i₂ j : I} {o₁ o₂ : O}
    (h₁ : ∀ o, sp.S i₁ o → o = o₁) (h₂ : ∀ o, sp.S i₂ o → o = o₂)
    (hj₁ : i₁ ≼ j) (hj₂ : i₂ ≼ j) :
    ∃ u, sp.S j u ∧ o₁ ≼ u ∧ o₂ ≼ u :=
  cap_two_step_forced Sys hA hC h₁ h₂ hj₁ hj₂

/-- "Their theorem is a case of the two-row argument": no system for the
register lets every request receive a response and keeps the emitted
responses reconcilable (linearizable). -/
theorem «sec:complete-cap/gilbert-lynch» (Sys : System CC.GL.regFullSpec D) :
    ¬ (AnsweringAtEnd Sys ∧ CommonRefinementAtEnd Sys) :=
  CC.GL.gilbert_lynch_direct Sys

/-- "Appendix `app:cap-response` takes precedence from real time" —
Corollary `cor:gilbert-lynch`, client form (both hypotheses required only of
two-participant client histories, consistency at the realized history). -/
theorem «sec:complete-cap/gl-realized» (Sys : System CC.GL.regSpec D) :
    ¬ (CC.AsyncGL.AnsweringC Sys ∧ CC.AsyncGL.RealizedRPCC Sys) :=
  CC.AsyncGL.gilbert_lynch_client Sys

/-- "gives a response form of Complete CAP for responses that are not
forced" — Theorem `thm:complete-cap-response` (see
`Paper/AppF_ResponseAvailability.lean`). -/
theorem «sec:complete-cap/response-form» (sp : Spec I O) (D : Type) (Q : Obligation sp) :
    (∃ Sys : System sp D, Sys.Replicated ∧ ResponseAvailability Sys (fun _ _ => Q.Q) ∧
      ResponsePC Sys) ↔
    ∃ T, ResponseInterface Q T ∧ ConsistentOn sp T :=
  complete_cap_response sp D Q

/-- "and derives the theorem in Gilbert and Lynch's asynchronous model
(Proposition `prop:gl-async`)." -/
theorem «sec:complete-cap/gl-async» {N : Nat} {M : Type} (hN : 2 ≤ N)
    (A : CC.AsyncGL.Alg N M) : ¬ (CC.AsyncGL.Available A ∧ CC.AsyncGL.Atomic A) :=
  CC.AsyncGL.gilbert_lynch_async hN A

end CC.Paper
