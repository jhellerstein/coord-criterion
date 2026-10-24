import CoordCriterion.CAP.ResponseAvailability
import CoordCriterion.CAP.AvailabilityAtEnd
import CoordCriterion.CAP.Necessity
import CoordCriterion.CAP.Forced
import CoordCriterion.CAP.Coordination
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
receives takes a message sent from another component.  … *Availability* is
Availability for `S`."  In the unfolded form below, "local to `p`" is the
conjunction `Produced … ∧ Partitioned … comp ∧ (∀ q, comp q ≠ comp p → ext q =
[]) ∧ (∀ q j, inp j ∉ ext q)`.  For a general availability relation see
`«def:partition-notions(4)/for»`. -/
abbrev «def:partition-notions(4)» (Sys : System sp D) : Prop := AvailabilityAtEnd Sys

/-- Def. `def:partition-notions`(4): "Fix an availability relation `A ⊆ S`,
the rows `(i,o)` whose output `o` must stay available at input `i`, and write
`A(i)` for its fiber.  The system has Availability for `A` when, in every
partitioned history it produces, each participant `p`, ending in state
`(i,R)`, can emit each output in `R(i) ∩ A(i)` in some continuation local to
`p`." -/
abbrev «def:partition-notions(4)/for» (A : Table I O) (Sys : System sp D) : Prop :=
  AvailabilityFor A Sys

/-- Def. `def:partition-notions`(4): "Availability is Availability for `S`." -/
theorem «def:partition-notions(4)/for-S» (Sys : System sp D) :
    «def:partition-notions(4)/for» sp.S Sys ↔ «def:partition-notions(4)» Sys :=
  availabilityFor_S Sys

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

/-- Def. `def:partition-notions`(6): "`S` is consistent on `A` when every
finite set of rows of `A` with a common expansion `j` has a common refinement
in `S(j)`." -/
abbrev «def:partition-notions(6)» (sp : Spec I O) (A : Table I O) : Prop := ConsistentOn sp A

/-- "With `A = S`, consistency on `A` is the common-expansion condition." -/
theorem «sec:complete-cap/consistent-on-S» (sp : Spec I O) :
    «def:partition-notions(6)» sp sp.S ↔ sp.CommonExpansion :=
  consistentOn_S

/-! ### Theorem `thm:complete-cap` -/

/-- **Theorem `thm:complete-cap` (Complete CAP).**  "For an ordered relational
specification `S` and an availability relation `A ⊆ S`, the following are
equivalent: (1) some system has Availability for `A` and Partition
Consistency; (2) `S` is consistent on `A`."

Lean: `D` is the (arbitrary) type of message payloads. -/
theorem «thm:complete-cap» (sp : Spec I O) (D : Type) (A : Table I O)
    (hAS : ∀ i o, A i o → sp.S i o) :
    (∃ Sys : System sp D, «def:partition-notions(4)/for» A Sys ∧ «def:partition-notions(5)» Sys) ↔
      «def:partition-notions(6)» sp A :=
  complete_cap_for sp D A hAS

/-- Proof of Theorem `thm:complete-cap`, (2)⇒(1): "Take the system whose
strategies emit, by the canonical output event `output(o)` …, any output `o`
of `A` in the current fiber. … so the system has Availability for `A`. …
For a system that emits only canonical output events, that is confluence at
`j`, which gives Partition Consistency."  Lean: `respSystem A`, a canonical
system. -/
theorem «thm:complete-cap/proof-sufficiency» (A : Table I O) (h : ConsistentOn sp A) :
    AvailabilityFor A (respSystem (sp := sp) (D := D) A) ∧
    PartitionConsistencyAtEnd (respSystem (sp := sp) (D := D) A) ∧
    CanonicalSystem (respSystem (sp := sp) (D := D) A) :=
  ⟨availabilityFor_resp A, pc_resp A h, respSystem_canonical A⟩

/-- Proof of Theorem `thm:complete-cap`, (1)⇒(2): "take one participant `p_r`
per row, starting at input `i_r`, each in its own component … By
Availability for `A`, each `p_r` can emit `o_r`.  By Partition Consistency,
they then reach one state `(j,R)`, which has some row `(j,u)` … so `u`
refines every `o_r`."  Lean: only a common refinement of the emitted outputs
is used (implied by Partition Consistency). -/
theorem «thm:complete-cap/proof-necessity» (A : Table I O) (hAS : ∀ i o, A i o → sp.S i o)
    (Sys : System sp D) (hA : AvailabilityFor A Sys) (hC : CommonRefinementAtEnd Sys) :
    ConsistentOn sp A :=
  consistentOn_of_availabilityFor A hAS Sys hA hC

/-! ### Corollary `cor:complete-cap-S` -/

/-- **Corollary `cor:complete-cap-S`.**  "Some system has Availability and
Partition Consistency if and only if `S` satisfies Lifted Monotonicity." -/
theorem «cor:complete-cap-S» (sp : Spec I O) (D : Type) :
    (∃ Sys : System sp D, «def:partition-notions(4)» Sys ∧ «def:partition-notions(5)» Sys) ↔
      sp.LiftedMono :=
  ⟨fun ⟨Sys, hA, hP⟩ => cap_necessary_two Sys hA hP,
   fun h => ⟨cfSystem sp D, (availability_iff_atEnd _).1 (cf_availability h),
     (partitionConsistency_iff_atEnd _).1 (cf_partitionConsistency h)⟩⟩

/-- Corollary `cor:complete-cap-S`: "When it does, a commitment-free system has
both: one whose strategies may emit any exposable output `o` by `Out_ε(o)`."

Lean: `cfSystem` has empty basis and allows every event; an output event
`Out ε o` is legal exactly when `o` is exposable.  Every history it produces
is commitment-free. -/
theorem «cor:complete-cap-S/commitment-free» (sp : Spec I O) (D : Type) (h : sp.LiftedMono) :
    («def:partition-notions(4)» (cfSystem sp D) ∧ «def:partition-notions(5)» (cfSystem sp D)) ∧
    ∀ (N : Nat) (init : Fin N → I) (H : History sp D N),
      Produced (cfSystem sp D) N init H → ∀ p γ o, LEv.out γ o ∈ H p → γ = [] :=
  ⟨⟨(availability_iff_atEnd _).1 (complete_cap_cf sp D h).1,
      (partitionConsistency_iff_atEnd _).1 (complete_cap_cf sp D h).2⟩,
    fun _ _ _ => cfSystem_coordinationFree⟩

/-- Proof of Corollary `cor:complete-cap-S`: "by Complete CALM and
Proposition `prop:distributed-consistency` it has Partition Consistency."
Strong reading: the confluence continuation itself can be chosen
commitment-free and receive-free (`PartitionConsistencyCF`). -/
theorem «cor:complete-cap-S/proof-cf-continuations» (sp : Spec I O) (D : Type) :
    ((∃ Sys : System sp D, Availability Sys ∧ PartitionConsistency Sys) → sp.LiftedMono) ∧
    (sp.LiftedMono → Availability (cfSystem sp D) ∧ PartitionConsistencyCF (cfSystem sp D)) :=
  complete_cap_strong sp D

/-! ### Remarks after the proof -/

/-- "The converse never assumes that the system is commitment-free, so
commitments cannot enlarge the class of specifications that admit a system
with Availability for `A` and Partition Consistency."  Lean: necessity holds
for an arbitrary system (any basis, any nondeterministic local strategies). -/
theorem «sec:complete-cap/necessity-any-system» (A : Table I O) (hAS : ∀ i o, A i o → sp.S i o)
    (Sys : System sp D) (hA : «def:partition-notions(4)/for» A Sys)
    (hP : «def:partition-notions(5)» Sys) : «def:partition-notions(6)» sp A :=
  consistentOn_of_availabilityFor A hAS Sys hA (commonRefinement_of_pc hP)

/-- "Under consistency on `A`, the canonical output event for an output of `A`
seals nothing and chooses only against outputs outside `A`, which the system
never emits, so the system of the proof is coordination-free (Definition
`def:coordination`)."  Lean: the system emits only rows of `A`, and no output
event removes a row that any run of the system emits, or seals an input any
run accepts. -/
theorem «sec:complete-cap/proof-system-coordination-free» (A : Table I O)
    (hcons : ConsistentOn sp A) :
    (respSystem (sp := sp) (D := D) A).CoordinationFree ∧
    ∀ k x, SysEmits (respSystem (sp := sp) (D := D) A) k x → A k x :=
  ⟨respSystem_coordinationFree A hcons, fun _ _ h => resp_emits_A h⟩

/-- "For `A = S` it needs no commitment at all."  Lean: with Availability,
any removal of a row `(k,x)` by an output event whose local prefix is
receive-free is contradicted in some produced history by another participant
whose initial input is below `k` (distributed coordination); so such a system
avoids distributed coordination only if those events remove nothing. -/
theorem «sec:complete-cap/A-eq-S-no-commitment» (Sys : System sp D)
    (hA : «def:partition-notions(4)» Sys)
    {n : Nat} {init : Fin n → I} {H : History sp D n} (hw : WF init H)
    (hp : Produced Sys n init H) {p q : Fin n} (hqp : q ≠ p)
    {a b : List (LEv sp D n)} {γ : List (Commitment sp)} {o : O} {σ σc : State sp}
    (hH : H p = a ++ LEv.out γ o :: b) (hnr : ∀ q' k j d, LEv.recv q' k j d ∉ a)
    (hrun : LRun (canon sp (init p)) a σ) (hap : applySeq σ γ = some σc)
    {k : I} {x : O} (hx : σ.R k x) (hnx : ¬ σc.R k x) (hqk : init q ≼ k) :
    ¬ Sys.CoordinationFreeH :=
  availability_not_coordinationFreeH Sys hA hw hp hqp hH hnr hrun hap hx hnx hqk

/-- "For a smaller `A` such local choices can be necessary: if `o ∈ A(i)` and
`x ∈ S(i) ∖ A(i)` have no common refinement at `i`, emitting `o` must choose
against `x`."  Lean: one input, `S = {o, x}` incomparable, `A = {o}`: `S` is
consistent on `A`, `o` is not exposable (so its output event must commit),
and the system of the proof is coordination-free. -/
theorem «sec:complete-cap/local-choice-necessary» (D : Type) :
    ConsistentOn CAP.lcSpec CAP.lcA ∧ ¬ Exposable (canon CAP.lcSpec ()) .o ∧
    (respSystem (sp := CAP.lcSpec) (D := D) CAP.lcA).CoordinationFree :=
  ⟨lcSpec_consistentOn, lcSpec_o_not_exposable,
    respSystem_coordinationFree CAP.lcA lcSpec_consistentOn⟩

/-- "When consistency on `A` fails, some output of `A` either waits for
another component, sacrificing Availability, or is emitted independently at
the cost of Partition Consistency." -/
theorem «sec:complete-cap/consistency-fails» (A : Table I O) (hAS : ∀ i o, A i o → sp.S i o)
    (hno : ¬ ConsistentOn sp A) (Sys : System sp D) :
    ¬ «def:partition-notions(4)/for» A Sys ∨ ¬ «def:partition-notions(5)» Sys :=
  (Classical.em («def:partition-notions(4)/for» A Sys)).elim
    (fun hA => Or.inr fun hP =>
      hno (consistentOn_of_availabilityFor A hAS Sys hA (commonRefinement_of_pc hP))) Or.inl

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
returns `v`, so `v_0` has no refinement there and `S` is not consistent on
`S`."  Lean: the complete-response
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

/-- "The converse in the proof of Theorem `thm:complete-cap` needs
Availability only so that `p` can emit
the acknowledgment and `q` can emit `v_0`.  Each is the only output its input
permits, so it is enough that every request receive some response …
It needs Partition Consistency only to give a common refinement of the emitted
outputs."  Lean: the two-row case with Answering in place of
Availability, for outputs forced at their inputs, and a common refinement of
the emitted outputs in place of Partition Consistency. -/
theorem «sec:complete-cap/gl-two-row-forced» (Sys : System sp D)
    (hA : AnsweringAtEnd Sys) (hC : CommonRefinementAtEnd Sys) {i₁ i₂ j : I} {o₁ o₂ : O}
    (h₁ : ∀ o, sp.S i₁ o → o = o₁) (h₂ : ∀ o, sp.S i₂ o → o = o₂)
    (hj₁ : i₁ ≼ j) (hj₂ : i₂ ≼ j) :
    ∃ u, sp.S j u ∧ o₁ ≼ u ∧ o₂ ≼ u :=
  cap_two_step_forced Sys hA hC h₁ h₂ hj₁ hj₂

/-- "Their theorem is a case of Complete CAP": no system for the
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

/-- "extends Complete CAP to systems that choose their responses when responses
are not forced" — Theorem `thm:complete-cap-response` (see
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
