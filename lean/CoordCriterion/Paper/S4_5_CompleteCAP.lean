import CoordCriterion.CAP.ResponseAvailability
import CoordCriterion.CAP.AvailabilityAtEnd
import CoordCriterion.CAP.Necessity
import CoordCriterion.CAP.Forced
import CoordCriterion.CAP.Coordination
import CoordCriterion.Distributed.Commitments
import CoordCriterion.CAP.AsyncGilbertLynch
import CoordCriterion.Appendix.DeploymentExamples
import CoordCriterion.Appendix.Registers

/-!
# Paper §4.5, "The Complete CAP Theorem" (`sections/distributed.tex`)

Statement layer for Section `sec:complete-cap`, from the subsection header to
the end of `sections/distributed.tex`: Definitions `def:partitioned-history`,
`def:partition-notions`, `def:partition-consistency`, and `def:lm-for-A`,
Theorem `thm:complete-cap` and Corollary `cor:complete-cap-S`, the remarks
after them, and the claims of the paragraph "Gilbert and Lynch".  The proofs
of the theorem and the corollary are in Appendix `app:proofs`; their entries
are in `Paper/AppB_ProofsDistributed.lean`.

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

/-! ## §4.5 The Complete CAP Theorem -/

/-- Section `sec:complete-cap`, opening: "Complete CAP answers that broader
question for any declared guarantee.  To state the question, we must separate
the outputs that participants must keep available from the outputs that the
spec permits.  A participant acts on its local history during a
partition, while consistency compares the participants' outputs at a common
input extension of their inputs.  Their common output extension need not be emitted by
any participant.  It may exist only as the client's combined observation.

Consider a register initialized to `v₀`.  During a partition, participant
`p` receives a write `w(v)` and emits its acknowledgment, while participant
`q` receives a concurrent read `r` and returns `v₀`.  A client that later
collects both observes the write acknowledgment together with the read answer
`v₀`.  The register spec permits this combined output at the input
containing both operations: a linearization may put the concurrent read
before the write.  The combined output extends both local outputs and
provides a proof of their consistency, although no participant need ever
emit it.

We therefore encode a guarantee as an I/O specification together with an
explicit relation `E ⊆ P`: the rows whose outputs must remain locally
available.  Outputs in `P ∖ E` need only remain permitted as possible common
output extensions.  Complete CAP says that such a guarantee can stay available and
consistent through partitions exactly when the spec satisfies
Lifted Monotonicity for `E`: outputs selected by `E` on different sides of a
partition must have a common output extension in the spec at every common
input extension of their inputs.  When `E = P`, this is Lifted Monotonicity
itself."  Lean: Theorem `thm:complete-cap` and
Corollary `cor:complete-cap-S` below (the latter via
`«sec:complete-cap/lm-for-S»` and `«prop:common-expansion-form»`).  The
closing sentences ("A partition does not change which commitments a
spec needs; …") are intuition for those results. -/
theorem «sec:complete-cap/intro» (sp : Spec I O) (D : Type) (E : Table I O)
    (hES : ∀ i o, E i o → sp.P i o) :
    ((∃ Sys : System sp D, AvailabilityFor E Sys ∧ PartitionConsistencyAtEnd Sys) ↔
      ConsistentOn sp E) ∧
    ((∃ Sys : System sp D, AvailabilityAtEnd Sys ∧ PartitionConsistencyAtEnd Sys) ↔
      sp.LiftedMono) :=
  ⟨complete_cap_for sp D E hES,
   ⟨fun ⟨Sys, hA, hP⟩ => cap_necessary_two Sys hA hP,
    fun h => ⟨cfSystem sp D, (availability_iff_atEnd _).1 (cf_availability h),
      (partitionConsistency_iff_atEnd _).1 (cf_partitionConsistency h)⟩⟩⟩

/-! ### Definition `def:partitioned-history` (Partitioned history) -/

/-- **Def. `def:partitioned-history` (Partitioned history).**  "A partitioned
history divides the participants into two or more blocks and contains no
receive whose matching send lies in another block; participants still
receive environment input and emit outputs."

Lean: a block labelling `comp : Fin n → Nat` with two distinct labels and
no receive from a participant with another label. -/
abbrev «def:partitioned-history» (H : History sp D n) (comp : Fin n → Nat) : Prop :=
  Partitioned H comp

/-- Def. `def:partitioned-history`, unfolded. -/
theorem «def:partitioned-history/unfolded» (H : History sp D n) (comp : Fin n → Nat) :
    Partitioned H comp ↔
      (∃ p q, comp p ≠ comp q) ∧
      ∀ (p : Fin n) (a : List (LEv sp D n)) (q : Fin n) (k : Nat) (j : Option I) (d : D) b,
        H p = a ++ LEv.recv q k j d :: b → comp q = comp p :=
  Iff.rfl

/-! ### The system and environment assumptions -/

/-- Paragraph after Def. `def:partitioned-history`: "We fix a system, with a
strategy for each participant of every finite participant set and every choice
of initial inputs, each depending only on its participant's local history, and
an adversarial environment that may supply any legal input event to any
participant."  This entry is the system half; the environment half is
`«sec:complete-cap/environment»`.

Lean: `System sp D` has a commitment basis and a nondeterministic strategy
`strat n init p pre e` for every `n`, `init : Fin n → I`, participant `p`.
"Depending only on the local history" is the definition of `Produced`: each
event of `p` is checked against `p`'s own local prefix only. -/
abbrev «sec:complete-cap/system» (sp : Spec I O) (D : Type) : Type := System sp D

/-- "We fix a system …": a history is *produced* by the system
when each participant's events are allowed given its own local prefix. -/
theorem «sec:complete-cap/system-produced» (Sys : System sp D) (init : Fin n → I)
    (H : History sp D n) :
    Produced Sys n init H ↔
      ∀ p a e b, H p = a ++ e :: b → Allowed Sys n init p a e :=
  Iff.rfl

/-- "… and an adversarial environment that may supply any legal input event to
any participant."

Lean: input events are always allowed (their legality is checked by the run
relation `LRun` inside well-formedness `WF`). -/
theorem «sec:complete-cap/environment» (Sys : System sp D) (init : Fin n → I) (p : Fin n)
    (pre : List (LEv sp D n)) (j : I) :
    Allowed Sys n init p pre (.inp j) :=
  trivial

/-! ### Definitions `def:local-continuation`, `def:explicit-relation`, `def:partition-notions` (Availability) -/

/-- **Def. `def:local-continuation`** (Local continuation).  "A continuation
of a partitioned history is *local to* a participant `p` when the system
produces it, it adds only history events of `p`'s block and no input events,
and none of its receives takes a message sent from another block."

Lean: "local to `p`" is unfolded as `Produced … ∧ Partitioned … comp ∧
(∀ q, comp q ≠ comp p → ext q = []) ∧ (∀ q j, inp j ∉ ext q)` in the
unfolded form of `«def:partition-notions/unfolded»`. -/
abbrev «def:local-continuation» (Sys : System sp D) : Prop :=
  AvailabilityAtEnd Sys

/-- **Def. `def:explicit-relation`** (Explicit relation).  "An *explicit
relation* `E ⊆ P` is a set of rows `(i,o)` whose output `o` must stay
available at input `i`; write `E(i)` for its fiber `{o : (i,o) ∈ E}`."

Lean: a table `E : Table I O` subset of `sp.P`. -/
abbrev «def:explicit-relation» {sp : Spec I O} (E : Table I O) : Prop :=
  ∀ i o, E i o → sp.P i o

/-- **Def. `def:partition-notions`** (Availability).  "The system has
*Availability for `E`* when, in every partitioned history it produces, each
participant `p`, ending in state `(i,R)`, can emit each output in `R(i) ∩
E(i)` in some continuation local to `p` (Definition
`def:local-continuation`).  *Availability* is Availability for `P`."

Lean: `AvailabilityAtEnd Sys` (= `AvailabilityFor sp.P Sys`); for a general
`E`, use `«def:partition-notions/for»`. -/
abbrev «def:partition-notions» (Sys : System sp D) : Prop := AvailabilityAtEnd Sys

/-- Def. `def:partition-notions`: "An explicit relation `E ⊆ P` is a set
of rows `(i,o)` whose output `o` must stay available at input `i`; write
`E(i)` for its fiber `{o : (i,o) ∈ E}`.  The system has Availability for `E` when, in every
partitioned history it produces, each participant `p`, ending in state
`(i,R)`, can emit each output in `R(i) ∩ E(i)` in some continuation local to
`p`." -/
abbrev «def:partition-notions/for» (E : Table I O) (Sys : System sp D) : Prop :=
  AvailabilityFor E Sys

/-- Def. `def:partition-notions`: "Availability is Availability for `P`." -/
theorem «def:partition-notions/for-S» (Sys : System sp D) :
    «def:partition-notions/for» sp.P Sys ↔ «def:partition-notions» Sys :=
  availabilityFor_S Sys

/-- Def. `def:partition-notions`, unfolded.  `WF init H` is "a history"
(legal local runs from `σ_P(init p)`, matched receives); `σ` is `p`'s final
state `(i,R)`; the continuation appends `ext q` to each `H q`. -/
theorem «def:partition-notions/unfolded» (Sys : System sp D) :
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

/-- Def. `def:partition-notions`: asking at every consistent cut of every
produced partitioned history (`Availability`, the form the library proofs use)
is the same as asking at the end of every such history, because a produced
partitioned history restricted to a consistent cut is again one. -/
theorem «def:partition-notions/at-cuts» (Sys : System sp D) :
    Availability Sys ↔ «def:partition-notions» Sys :=
  availability_iff_atEnd Sys

/-! ### Definition `def:partition-consistency` (Partition Consistency) -/

/-- **Def. `def:partition-consistency` (Partition Consistency).**  "The system
has Partition Consistency when the final cut of every partitioned history it
produces is confluent at every common input extension of the participants' current
inputs.  The continuation
that confluence asks for need not stay partitioned and need not be produced by
the system." -/
abbrev «def:partition-consistency» (Sys : System sp D) : Prop := PartitionConsistencyAtEnd Sys

/-- Def. `def:partition-consistency`, unfolded: for each `j` above every
participant's final current input, a well-formed continuation (neither
partitioned nor produced) puts every participant in one state `τ` with
current input `j`. -/
theorem «def:partition-consistency/unfolded» (Sys : System sp D) :
    PartitionConsistencyAtEnd Sys ↔
      ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
        WF init H → Produced Sys n init H → Partitioned H comp →
        ∀ j : I, (∀ p σ, LRun (canon sp (init p)) (H p) σ → σ.cur ≼ j) →
        ∃ τ : State sp, τ.cur = j ∧ ∃ ext : Fin n → List (LEv sp D n),
          WF init (fun q => H q ++ ext q) ∧ ∀ p, LRun (canon sp (init p)) (H p ++ ext p) τ :=
  Iff.rfl

/-- Def. `def:partition-consistency`: asking at every consistent cut of every
produced partitioned history (`PartitionConsistency`, the form the library
proofs use) is the same as asking at the final cut. -/
theorem «def:partition-consistency/at-cuts» (Sys : System sp D) :
    PartitionConsistency Sys ↔ «def:partition-consistency» Sys :=
  partitionConsistency_iff_atEnd Sys

/-! ### Definition `def:lm-for-A` (Lifted Monotonicity for `E`) -/

/-- **Def. `def:lm-for-A` (Lifted Monotonicity for `E`).**  "`P` satisfies
Lifted Monotonicity for `E` when every finite set of rows of `E` with a common
input extension `j` has a common output extension in `P(j)`."  Lean: `ConsistentOn sp E`
(the library name predates the paper's term); finite sets are lists. -/
abbrev «def:lm-for-A» (sp : Spec I O) (E : Table I O) : Prop := ConsistentOn sp E

/-- "With `E = P`, Lifted Monotonicity for `E` is the common-extension
condition." -/
theorem «sec:complete-cap/lm-for-S» (sp : Spec I O) :
    «def:lm-for-A» sp sp.P ↔ sp.CommonExpansion :=
  consistentOn_S

/-! ### Theorem `thm:complete-cap` -/

/-- **Theorem `thm:complete-cap` (Complete CAP).**  "For an I/O specification
`P` and an explicit relation `E ⊆ P`, the following are
equivalent: (1) some system has Availability for `E` and Partition
Consistency; (2) `P` satisfies Lifted Monotonicity for `E`."

Lean: `D` is the (arbitrary) type of message payloads. -/
theorem «thm:complete-cap» (sp : Spec I O) (D : Type) (E : Table I O)
    (hES : ∀ i o, E i o → sp.P i o) :
    (∃ Sys : System sp D, «def:partition-notions/for» E Sys ∧ «def:partition-consistency» Sys) ↔
      «def:lm-for-A» sp E :=
  complete_cap_for sp D E hES

/-! ### Corollary `cor:complete-cap-S` -/

/-- **Corollary `cor:complete-cap-S`.**  "Some system has Availability and
Partition Consistency if and only if `P` satisfies Lifted Monotonicity." -/
theorem «cor:complete-cap-S» (sp : Spec I O) (D : Type) :
    (∃ Sys : System sp D, «def:partition-notions» Sys ∧ «def:partition-consistency» Sys) ↔
      sp.LiftedMono :=
  ⟨fun ⟨Sys, hA, hP⟩ => cap_necessary_two Sys hA hP,
   fun h => ⟨cfSystem sp D, (availability_iff_atEnd _).1 (cf_availability h),
     (partitionConsistency_iff_atEnd _).1 (cf_partitionConsistency h)⟩⟩

/-- Corollary `cor:complete-cap-S`: "When it does, a commitment-free system has
both: one whose strategies may emit any legal output `o` with no
commitment, by `Out_ε(o)`."

Lean: `cfSystem` has empty basis and allows every event; an output event
`Out ε o` is legal exactly when `o` is a legal output.  Every history it produces
is commitment-free. -/
theorem «cor:complete-cap-S/commitment-free» (sp : Spec I O) (D : Type) (h : sp.LiftedMono) :
    («def:partition-notions» (cfSystem sp D) ∧ «def:partition-consistency» (cfSystem sp D)) ∧
    ∀ (N : Nat) (init : Fin N → I) (H : History sp D N),
      Produced (cfSystem sp D) N init H → ∀ p γ o, LEv.out γ o ∈ H p → γ = [] :=
  ⟨⟨(availability_iff_atEnd _).1 (complete_cap_cf sp D h).1,
      (partitionConsistency_iff_atEnd _).1 (complete_cap_cf sp D h).2⟩,
    fun _ _ _ => cfSystem_coordinationFree⟩

/-! ### Remarks after the corollary -/

/-- "A system might hope to keep more outputs available by issuing
commitments, coordinating within each side of a partition.  It cannot: the
impossibility direction of the proof holds for every system, commitment-free
or not."  Lean: necessity holds for an arbitrary system (any basis, any
nondeterministic local strategies, so any commitments its output and commit
events issue). -/
theorem «sec:complete-cap/necessity-any-system» (E : Table I O) (hES : ∀ i o, E i o → sp.P i o)
    (Sys : System sp D) (hA : «def:partition-notions/for» E Sys)
    (hP : «def:partition-consistency» Sys) : «def:lm-for-A» sp E :=
  consistentOn_of_availabilityFor E hES Sys hA (commonRefinement_of_pc hP)

  /-- "For `E = P` the proof system needs no commitment at all."  The theorem
  gives the commitment-free system used for full Availability.  This statement
  is specification-relative: restricting a strategy to a smaller `E` does not
  turn row-removing commitments into commitment-free steps relative to `P`. -/
theorem «sec:complete-cap/proof-system-commitment-free» (sp : Spec I O) (D : Type)
      (h : sp.LiftedMono) :
      («def:partition-notions» (cfSystem sp D) ∧
        «def:partition-consistency» (cfSystem sp D)) ∧
      ∀ (N : Nat) (init : Fin N → I) (H : History sp D N),
        Produced (cfSystem sp D) N init H → ∀ p γ o, LEv.out γ o ∈ H p → γ = [] :=
    «cor:complete-cap-S/commitment-free» sp D h

  /-- Supporting operational lemma for the full-availability case.  If an output
  event in a receive-free local prefix removes a row and another participant can
  start below that row's input, Availability realizes the contradictory choice
  at the other participant. -/
theorem «sec:complete-cap/A-eq-S-no-commitment» (Sys : System sp D)
    (hA : «def:partition-notions» Sys)
    {n : Nat} {init : Fin n → I} {H : History sp D n} (hw : WF init H)
    (hp : Produced Sys n init H) {p q : Fin n} (hqp : q ≠ p)
    {a b : List (LEv sp D n)} {γ : List (CAP.Commitment sp)} {o : O} {σ σc : State sp}
    (hH : H p = a ++ LEv.out γ o :: b) (hnr : ∀ q' k j d, LEv.recv q' k j d ∉ a)
    (hrun : LRun (canon sp (init p)) a σ) (hap : CAP.applySeq σ γ = some σc)
    {k : I} {x : O} (hx : σ.R k x) (hnx : ¬ σc.R k x) (hqk : init q ≼ k) :
    ¬ Sys.CoordinationFreeH :=
  availability_not_coordinationFreeH Sys hA hw hp hqp hH hnr hrun hap hx hnx hqk

  /-- "For a smaller `E` row-removing commitments can be necessary: if `o ∈ E(i)` and
  `x ∈ P(i) ∖ E(i)` have no common output extension at `i`, emitting `o` must choose
  against `x`."  Lean: one input, `P = {o, x}` incomparable and `E = {o}`.
  `P` satisfies Lifted Monotonicity for `E`, but `o` is not exposable.  Thus no
  empty-commitment output event for `o` is legal, while the canonical output
  event is legal and applies a nonempty commitment.  Suppressing `x` in a
  strategy does not make the specification event commitment-free. -/
theorem «sec:complete-cap/local-row-removal-necessary» :
      ConsistentOn CAP.lcSpec CAP.lcA ∧ ¬ Exposable (canon CAP.lcSpec ()) .o ∧
      ∃ τ, SysStep (canonCommitmentBasis CAP.lcSpec) (canon CAP.lcSpec ())
          (.output (kappa (canon CAP.lcSpec ()) .o) .o) τ ∧
        kappa (canon CAP.lcSpec ()) .o ≠ [] := by
    have hn := CAP.lcSpec_o_not_exposable
    have ho : (canon CAP.lcSpec ()).R (canon CAP.lcSpec ()).cur .o := ⟨trivial, trivial⟩
    refine ⟨lcSpec_consistentOn, hn, outState _ _ ho, canonical_support _ _ ho, ?_⟩
    intro he
    have hs : SysStep (canonCommitmentBasis CAP.lcSpec) (canon CAP.lcSpec ())
        (.output [] .o) (outState (canon CAP.lcSpec ()) .o ho) := by simpa [he] using canonical_support _ _ ho
    exact hn (eps_step_iff.1 hs).2.1

/-- "When Lifted Monotonicity for `E` fails, some output of `E` waits for
another block, sacrificing Availability, or is emitted anyway, sacrificing
Partition Consistency." -/
theorem «sec:complete-cap/lm-for-A-fails» (E : Table I O) (hES : ∀ i o, E i o → sp.P i o)
    (hno : ¬ ConsistentOn sp E) (Sys : System sp D) :
    ¬ «def:partition-notions/for» E Sys ∨ ¬ «def:partition-consistency» Sys :=
  (Classical.em («def:partition-notions/for» E Sys)).elim
    (fun hA => Or.inr fun hP =>
      hno (consistentOn_of_availabilityFor E hES Sys hA (commonRefinement_of_pc hP))) Or.inl

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

/-- "Consider a register spec whose inputs are sets of operations
with their real-time precedence, and whose outputs answer every operation of
the input as some linearization does.  Let `p`'s input contain only a write of
`v ≠ v_0`, and `q`'s only a read.  The fiber at `p`'s input holds only the
write's acknowledgment; the fiber at `q`'s input, which contains no write,
holds only the answer `v_0` to the read.  At the common input extension where the
write precedes the read, every output in the fiber answers that same read with
`v`.  That contradicts the answer `v_0`; it is not a later read observing a
newer value.  So no output there extends `v_0`, and `P` does not satisfy
Lifted Monotonicity."

Lean: the complete-response register `regFullSpec` (an output is a response
map, operation id ↦ response, explained by some linearization and answering
every operation); `h1` is the write of `v = 1` (operation `0`), `h2` the read
(operation `1`), `hj` both with the write before the read, a common input extension
of `h1` and `h2`; `v0 = 0`.  The fibers at `h1` and `h2` are singletons; every
output at `hj` answers the same operation `1` with `1`, so none answers it
with `v0` (an output extension keeps every answer of the map it extends); hence
Lifted Monotonicity fails. -/
theorem «sec:complete-cap/gl-register» :
    (∀ o, CC.GL.regFull CC.GL.h1 o → o = CC.GL.ackMap) ∧
    (∀ o, CC.GL.regFull CC.GL.h2 o → o = CC.GL.v0Map) ∧
    CC.GL.h1 ≼ CC.GL.hj ∧ CC.GL.h2 ≼ CC.GL.hj ∧
    (∀ u, CC.GL.regFull CC.GL.hj u → u.f 1 = some (.val 1)) ∧ (1 : Nat) ≠ CC.GL.v0 ∧
    (∀ u, CC.GL.regFull CC.GL.hj u → ¬ CC.GL.v0Map ≼ u) ∧
    ¬ CC.GL.regFullSpec.LiftedMono :=
  ⟨CC.GL.h1_forced, CC.GL.h2_forced, CC.GL.h1_le, CC.GL.h2_le, CC.GL.hj_reads_write,
    by decide, fun u hu h => CC.GL.hj_noread u hu.1 (h 1 _ (by simp [CC.GL.v0Map])),
    CC.GL.regFullSpec_not_liftedMono⟩

/-- "By Complete CAP, then, no system keeps both outputs available and
consistent across a partition, which is Gilbert and Lynch's theorem."  Lean: no system for `regFullSpec` has
Availability and Partition Consistency. -/
theorem «sec:complete-cap/gl-no-system» (Sys : System CC.GL.regFullSpec D) :
    ¬ («def:partition-notions» Sys ∧ «def:partition-consistency» Sys) :=
  CC.GL.gilbert_lynch_direct_cap Sys

/-- "The proof needs less than the full hypotheses here, which is why it
yields Gilbert and Lynch's theorem exactly.  Place `p` and `q` in separate
blocks.  Availability is used only to make `p` acknowledge the write and
`q` answer the read; each fiber holds a single output, so any response will
do, which is Gilbert and Lynch's availability.  Partition Consistency is used
only to demand a common output extension of those two answers, a single
linearization that explains both, which is Gilbert and Lynch's consistency."

Lean: the two-row case of the proof, for outputs forced at their inputs, with
Answering (each participant can emit *some* output) in place of Availability
and a common output extension of the emitted outputs (`CommonRefinementAtEnd`) in
place of Partition Consistency; the proof runs the two participants in
separate blocks.  For the register, a common output extension lies in
`regFull hj`, so it is explained by a single linearization of `hj`, by the
definition of the fiber.  That Answering and `CommonRefinementAtEnd` are
Gilbert and Lynch's availability and consistency is the reading of
Appendix `app:cap-response`; see `«prop:gl-async»`. -/
theorem «sec:complete-cap/gl-two-row-forced» (Sys : System sp D)
    (hA : AnsweringAtEnd Sys) (hC : CommonRefinementAtEnd Sys) {i₁ i₂ j : I} {o₁ o₂ : O}
    (h₁ : ∀ o, sp.P i₁ o → o = o₁) (h₂ : ∀ o, sp.P i₂ o → o = o₂)
    (hj₁ : i₁ ≼ j) (hj₂ : i₂ ≼ j) :
    ∃ u, sp.P j u ∧ o₁ ≼ u ∧ o₂ ≼ u :=
  cap_two_step_forced Sys hA hC h₁ h₂ hj₁ hj₂

/-- "Their theorem is a case of Complete CAP" … "No such output extension
exists.":  no system for the register lets every request receive a response
and keeps the emitted responses reconcilable (explained by one
linearization). -/
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

/-- "and derives the theorem in Gilbert and Lynch's asynchronous model"
(Proposition `prop:gl-async`). -/
theorem «sec:complete-cap/gl-async» {N : Nat} {M : Type} (hN : 2 ≤ N)
    (A : CC.AsyncGL.Alg N M) : ¬ (CC.AsyncGL.Available A ∧ CC.AsyncGL.Atomic A) :=
  CC.AsyncGL.gilbert_lynch_async hN A

end CC.Paper
