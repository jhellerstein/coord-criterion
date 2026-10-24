import CoordCriterion.CAP.ResponseAvailability
import CoordCriterion.CAP.AsyncGilbertLynch
import CoordCriterion.Appendix.DeploymentExamples
import CoordCriterion.Appendix.Registers

/-!
# Paper §4.5, "The Complete CAP Theorem" (`sections/distributed.tex`)

Statement layer for Section `sec:complete-cap`, from the subsection header to
the end of `sections/distributed.tex`: Definition `def:partition-notions`,
Theorem `thm:complete-cap` (with its "moreover" clause), the remarks after its
proof, and the claims of the paragraphs "Answering every operation" and
"Deployment".

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
receives takes a message sent from another component.  The system has Availability when, at every consistent cut of
every partitioned history it produces, each participant `p` in state `(i,R)`
can emit each output in `R(i)` in some continuation local to `p`."  In the
unfolded form below, "local to `p`" is the conjunction `Produced … ∧
Partitioned H' comp ∧ (∀ q, comp q ≠ comp p → ext q = []) ∧ (∀ q j, inp j ∉ ext q)`. -/
abbrev «def:partition-notions(4)» (Sys : System sp D) : Prop := Availability Sys

/-- Def. `def:partition-notions`(4), unfolded.  `WF init H` is "a history"
(legal local runs from `σ_S(init p)`, matched receives); the cut `c` is given
by prefix lengths; `σ` is `p`'s state `(i,R)` at the cut. -/
theorem «def:partition-notions(4)/unfolded» (Sys : System sp D) :
    Availability Sys ↔
      ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
        WF init H → Produced Sys n init H → Partitioned H comp →
        ∀ c, IsCut H c →
        ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) ((H p).take (c p)) σ →
        ∀ o, σ.R σ.cur o →
        ∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)),
          Extends H c H' ext ∧ WF init H' ∧ Produced Sys n init H' ∧ Partitioned H' comp ∧
          (∀ q, comp q ≠ comp p → ext q = []) ∧
          (∀ q j, LEv.inp j ∉ ext q) ∧
          ∃ γ, LEv.out γ o ∈ ext p :=
  Iff.rfl

/-- Def. `def:partition-notions`(5), *Partition Consistency*: "The system has
Partition Consistency when every consistent cut of every such history is
confluent at every common expansion of the participants' current inputs.  The
continuation that confluence asks for need not stay partitioned and need not
be produced by the system." -/
abbrev «def:partition-notions(5)» (Sys : System sp D) : Prop := PartitionConsistency Sys

/-- Def. `def:partition-notions`(5), unfolded; `ConfluentCut` asks for a
well-formed continuation (neither partitioned nor produced) whose final cut
puts every participant in one state with current input `j`. -/
theorem «def:partition-notions(5)/unfolded» (Sys : System sp D) :
    PartitionConsistency Sys ↔
      ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
        WF init H → Produced Sys n init H → Partitioned H comp →
        ∀ c, IsCut H c →
        ∀ j : I, (∀ p σ, LRun (canon sp (init p)) ((H p).take (c p)) σ → σ.cur ≼ j) →
        ∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)) (τ : State sp),
          Extends H c H' ext ∧ WF init H' ∧ τ.cur = j ∧
          ∀ p, LRun (canon sp (init p)) (H' p) τ :=
  Iff.rfl

/-! "This is the *interface form* of Availability: every output the
specification permits must remain available, not merely some response to each
operation."  (Terminology; the response form is in
`Paper/AppF_ResponseAvailability.lean`.) -/

/-! ### Theorem `thm:complete-cap` -/

/-- **Theorem `thm:complete-cap` (Complete CAP).**  "For an ordered relational
specification `S`, the following are equivalent: (1) some system has
Availability and Partition Consistency; (2) `S` satisfies Lifted
Monotonicity."

Lean: `D` is the (arbitrary) type of message payloads. -/
theorem «thm:complete-cap» (sp : Spec I O) (D : Type) :
    (∃ Sys : System sp D, Availability Sys ∧ PartitionConsistency Sys) ↔ sp.LiftedMono :=
  complete_cap sp D

/-- Theorem `thm:complete-cap`, "moreover" clause: "when they hold, a
commitment-free system has both properties: one whose strategies may emit any
exposable output `o` by `Out_ε(o)`."

Lean: `cfSystem` has empty basis and allows every event; an output event
`Out ε o` is legal exactly when `o` is exposable.  Every history it produces
is commitment-free. -/
theorem «thm:complete-cap/moreover» (sp : Spec I O) (D : Type) (h : sp.LiftedMono) :
    (Availability (cfSystem sp D) ∧ PartitionConsistency (cfSystem sp D)) ∧
    ∀ (N : Nat) (init : Fin N → I) (H : History sp D N),
      Produced (cfSystem sp D) N init H → ∀ p γ o, LEv.out γ o ∈ H p → γ = [] :=
  ⟨complete_cap_cf sp D h, fun _ _ _ => cfSystem_coordinationFree⟩

/-- Proof of Theorem `thm:complete-cap`, (2)⇒(1), last sentence: "The
system's histories are those of Section `sec:histories`, so distributed
consistency … gives Partition Consistency."  Strong reading: the confluence
continuation itself can be chosen commitment-free and receive-free
(`PartitionConsistencyCF`), i.e. a history of Section `sec:histories`. -/
theorem «thm:complete-cap/proof-cf-continuations» (sp : Spec I O) (D : Type) :
    ((∃ Sys : System sp D, Availability Sys ∧ PartitionConsistency Sys) → sp.LiftedMono) ∧
    (sp.LiftedMono → Availability (cfSystem sp D) ∧ PartitionConsistencyCF (cfSystem sp D)) :=
  complete_cap_strong sp D

/-! ### Remarks after the proof -/

/-- "The proof of (1)⇒(2) never assumes that the system is commitment-free, so
local commitments cannot enlarge the class of specifications with both
properties."  Lean: necessity holds for an arbitrary system (any basis, any
nondeterministic local strategies). -/
theorem «sec:complete-cap/necessity-any-system» (Sys : System sp D)
    (hA : Availability Sys) (hP : PartitionConsistency Sys) : sp.LiftedMono :=
  cap_necessary Sys hA hP

/-- "When Lifted Monotonicity fails, some permitted output either waits for
another component, sacrificing Availability, or completes independently at
the cost of Partition Consistency." -/
theorem «sec:complete-cap/lm-fails» (hlm : ¬ sp.LiftedMono) (Sys : System sp D) :
    ¬ Availability Sys ∨ ¬ PartitionConsistency Sys :=
  (Classical.em (Availability Sys)).elim
    (fun hA => Or.inr fun hP => hlm (cap_necessary Sys hA hP)) Or.inl

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

/-! ### Paragraph "Answering every operation" -/

/-- "a specification that accepts an abort or a null result at every input is
trivially available": if some output `o₀` answers at every input, some
replicated system has Response Availability and Response Partition
Consistency. -/
theorem «sec:complete-cap/trivially-available» (Q : Obligation sp) (o0 : O)
    (h0 : ∀ i, Q.Q i o0) :
    ∃ Sys : System sp D, Sys.Replicated ∧ ResponseAvailability Sys (fun _ _ => Q.Q) ∧
      ResponsePC Sys :=
  trivially_available Q o0 h0

/-- "a system can answer every operation through any partition, with
responses that have a common refinement, exactly when the specification is
consistent on some response interface" — Theorem `thm:complete-cap-response`
(see `Paper/AppF_ResponseAvailability.lean`). -/
theorem «sec:complete-cap/response-form» (sp : Spec I O) (D : Type) (Q : Obligation sp) :
    (∃ Sys : System sp D, Sys.Replicated ∧ ResponseAvailability Sys (fun _ _ => Q.Q) ∧
      ResponsePC Sys) ↔
    ∃ T, ResponseInterface Q T ∧ ConsistentOn sp T :=
  complete_cap_response sp D Q

/-- "Lifted Monotonicity implies the response form". -/
theorem «sec:complete-cap/lm-implies-response-form» (Q : Obligation sp) (h : sp.LiftedMono) :
    ∃ Sys : System sp D, Sys.Replicated ∧ ResponseAvailability Sys (fun _ _ => Q.Q) ∧
      ResponsePC Sys :=
  lm_response_form Q h

/-- "and for functional specifications the two forms coincide." -/
theorem «sec:complete-cap/functional-forms-coincide» (hf : sp.Functional) (Q : Obligation sp) :
    (∃ Sys : System sp D, Sys.Replicated ∧ ResponseAvailability Sys (fun _ _ => Q.Q) ∧
      ResponsePC Sys) ↔
    (∃ Sys : System sp D, Availability Sys ∧ PartitionConsistency Sys) :=
  functional_forms_coincide hf Q

/-- "In our terms, a single emitted output has no refinement in the fiber at
some expansion of its input, a failure of Relational Monotonicity
(Corollary `cor:gilbert-lynch`)."  Lean: the linearizable register
`CC.GL.regSpec` is not relationally monotone. -/
theorem «sec:complete-cap/register-not-relMono» : ¬ CC.GL.regSpec.RelMono :=
  reg_not_relMono

/-- "The Gilbert–Lynch theorem follows as a corollary of the same machinery"
— Corollary `cor:gilbert-lynch`, client form (both hypotheses required only of
two-participant client histories); see `Paper/AppF_ResponseAvailability.lean`. -/
theorem «sec:complete-cap/gilbert-lynch» (Sys : System CC.GL.regSpec D) :
    ¬ (CC.AsyncGL.AnsweringC Sys ∧ CC.AsyncGL.RealizedRPCC Sys) :=
  CC.AsyncGL.gilbert_lynch_client Sys

/-- "The appendix derives Gilbert and Lynch's theorem in their asynchronous
model from the corollary (Proposition `prop:gl-async`)." -/
theorem «sec:complete-cap/gl-async» {N : Nat} {M : Type} (hN : 2 ≤ N)
    (A : CC.AsyncGL.Alg N M) : ¬ (CC.AsyncGL.Available A ∧ CC.AsyncGL.Atomic A) :=
  CC.AsyncGL.gilbert_lynch_async hN A

/-! ### Paragraph "Deployment" (forward pointers to Appendix `app:deployment`) -/

/-- "Appendix `app:deployment` restricts Availability to the rows each
participant is authorized to emit": with the full deployment (`A_p = S` for
every `p`) Deployment Availability is the Availability of this section (at
the deployment's participant set). -/
theorem «sec:complete-cap/deployment-availability» (Sys : System sp D)
    (Dp : CC.Deploy.Deployment sp n) (hA : ∀ p, Dp.A p = sp.S) :
    CC.Deploy.DeploymentAvailability Sys Dp ↔ CC.Deploy.AvailabilityAt Sys n :=
  CC.Deploy.deploymentAvailability_full Sys Dp hA

/-- "notes the degenerate case in which one participant holds all relevant
authority": under a single-authority deployment (at least two participants),
monotonicity across partitions only asks that each authorized row have a
refinement at every expansion of its input. -/
theorem «sec:complete-cap/single-authority» (hn : 2 ≤ n) (Dp : CC.Deploy.Deployment sp n)
    (p₀ : Fin n) (hSA : CC.Deploy.SingleAuthority Dp p₀) :
    CC.Deploy.MonoAcrossPartitions Dp ↔
      ∀ i o, Dp.A p₀ i o → ∀ j, i ≼ j → ∃ u, sp.S j u ∧ o ≼ u :=
  CC.Deploy.single_authority_iff hn Dp p₀ hSA

/-- "and shows that a causal register … needs no cross-component coordination
when each participant answers only its own reads": the causal register is
monotone across partitions under the replica deployment. -/
theorem «sec:complete-cap/causal-register» {α : Type} (G : CC.Deploy.OpSig α n) :
    CC.Deploy.MonoAcrossPartitions (CC.Deploy.replicaD G) :=
  CC.Deploy.causal_monoAcross G

end CC.Paper
