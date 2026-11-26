import CoordCriterion.CAP.ResponseAvailability
import CoordCriterion.CAP.AvailabilityAtEnd
import CoordCriterion.CAP.Necessity
import CoordCriterion.CAP.Forced
import CoordCriterion.CAP.Coordination
import CoordCriterion.CAP.TwoPhaseCommit
import CoordCriterion.Distributed.Commitments
import CoordCriterion.CAP.AsyncGilbertLynch
import CoordCriterion.Appendix.DeploymentExamples
import CoordCriterion.Appendix.Registers
import CoordCriterion.CALM.Examples

/-!
# Paper §4.4, "The Complete CAP theorem" (`paper/distributed.tex`)

Statement layer for Section `sec:complete-cap`, from the subsection header to
the end of `paper/distributed.tex`: Definitions `def:partitioned-history`,
`def:explicit-relation`, `def:local-continuation`, `def:partition-notions`,
`def:partition-consistency`, `def:lm-for-A`, and `def:escapes-cap`, the
canonical system for `E`, Theorem `thm:complete-cap` and Corollary
`cor:complete-cap-any-system`, the remarks after them, and the claims of the paragraph "Gilbert and Lynch".  The proofs
of the theorem and the corollary are in Appendix `app:proofs-sec4`; their entries
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

/-! ## §4.4 The Complete CAP theorem -/

/-- Section `sec:complete-cap`, opening: "Complete CAP addresses the
conjecture more broadly: which specifications are subject to the CAP
conjecture, and which are not?

To pose the question, we separate the outputs that participants emit from
the conclusions an observer, such as a client, may draw by combining them.  The spec permits such combinations, but no participant emits them, and
availability does not need them."  Lean: Theorem `thm:complete-cap`,
`«thm:complete-cap/E-eq-P»`, and Corollary `cor:complete-cap-any-system`
below, in their existential form: some system has the two properties iff the
spec satisfies Lifted Monotonicity for `E` (resp. Lifted Monotonicity). -/
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

/-- **Def. `def:partitioned-history` (Partitioned history).**  The paper
introduces it with "Both availability and consistency are judged on histories
in which a partition separates the participants."  "A partitioned
history divides the participants into two or more sides and contains no
receive whose matching send lies on another side; participants still
receive environment input and emit outputs."

Lean: a side labelling `comp : Fin n → Nat` with two distinct labels and
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

/-! ### Definition `def:explicit-relation` (Explicit possibility relation) -/

/-- **Def. `def:explicit-relation`** (Explicit possibility relation).  "An
*explicit possibility relation*, or *explicit relation*, is a set `E ⊆ P` of
rows whose outputs participants actually emit.  Write `E(i)` for its outputs at
input `i`."  The paper follows the definition with the register: "These two
outputs are in `E`.  A client that collects both responses sees the pair,
which is in `P ∖ E`."  The voters of the election, later in the subsection,
illustrate it (`«def:explicit-relation/election-voters»`).

Lean: a table `E : Table I O` subset of `sp.P`; `E(i)` is `E i`. -/
abbrev «def:explicit-relation» {sp : Spec I O} (E : Table I O) : Prop :=
  ∀ i o, E i o → sp.P i o

/-- Example after Theorem `thm:complete-cap`, introduced by "Commitments and
availability can still coexist when each commitment is made by a single
participant, as the voters in the election of Section `sec:election-story`
show" (prose-only signpost): "Return to the election of Section
`sec:election-story`, now with the spec for the voters, which the registrar
observes.  Each voter's ballot is a row
of `E`, while the sets of ballots the registrar may observe across voters are
implicit outputs in `P \ E`."

Lean (`CAP.votersSpec`, `CAP.votersE`, with `n = 3` for the election): an
output records the ballots received, voter by voter, a ballot for `a` or `b`
being a response `true` or `false`; the voters' spec does not depend on how
ballots are tallied.  First conjunct: `E ⊆ P`.  Second: the combined ballots of
two voters are permitted, not in `E`, and extend both voters' single ballots.
Third: every permitted output respects each voter's ballot, being the least
output extending the single ballots it contains, each a row of `E`. -/
theorem «def:explicit-relation/election-voters» (n : Nat) :
    (∀ i v, CAP.votersE n i v → (CAP.votersSpec n).P i v) ∧
    (∀ (p q : Fin n), p ≠ q → ∀ b c : Bool,
      let u : CAP.Votes n := fun r => if r = p then some b else if r = q then some c else none
      (CAP.votersSpec n).P () u ∧ ¬ CAP.votersE n () u ∧ CAP.single p b ≼ u ∧ CAP.single q c ≼ u) ∧
    (∀ u : CAP.Votes n, (CAP.votersSpec n).P () u ∧
      (∀ p b, u p = some b → CAP.votersE n () (CAP.single p b) ∧ CAP.single p b ≼ u) ∧
      ∀ w : CAP.Votes n, (∀ p b, u p = some b → CAP.single p b ≼ w) → u ≼ w) :=
  CAP.voters_explicit n

/-! ### Definition `def:emitted-rows` (Emitted rows) -/

/-- **Def. `def:emitted-rows`** (Emitted rows), now stated inside Def.
`def:deployment` (Appendix `app:deployment`): "The *emitted rows* of a run are
the pairs `(i,o)` such that the run emits `o` at current input `i`; the emitted
rows of a system are those of its participants' runs in the histories it
produces."  The entry stays in this file because Availability for `E` below is
stated with it.

Lean: for a canonical run the emitted rows are `emRows` (`app:cap-response`) or
`Deploy.emitted` (`app:deployment`); for a system, `SysEmits Sys k x`: some
participant of some well-formed history the system produces emits `x` at
current input `k`. -/
abbrev «def:emitted-rows» (Sys : System sp D) : Table I O := SysEmits Sys

/-- Not quoted from the paper (the body no longer defines emitted rows):
under Availability for `E`, every row of `E` at a participant's state can
become an emitted row of the system.

Lean: under Availability for `E` (`AvailabilityFor`, at the end of a
partitioned history the system produces), every output of `E` in the fiber
at participant `p`'s current input is an emitted row of the system at that
input. -/
theorem «def:emitted-rows/availability» (E : Table I O) (Sys : System sp D)
    (hA : AvailabilityFor E Sys) {init : Fin n → I} {H : History sp D n}
    {comp : Fin n → Nat} (hw : WF init H) (hp : Produced Sys n init H)
    (hpt : Partitioned H comp) (p : Fin n) (σ : State sp)
    (hσ : LRun (canon sp (init p)) (H p) σ) (o : O) (ho : σ.R σ.cur o)
    (hE : E σ.cur o) : SysEmits Sys σ.cur o := by
  obtain ⟨ext, hw', hp', _, _, hni, hm⟩ := hA n init H comp hw hp hpt p σ hσ o ho hE
  obtain ⟨a, b, hab⟩ := List.append_of_mem hm
  have h2 : (fun q => H q ++ ext q) p = (H p ++ a) ++ LEv.out o :: b := by
    show H p ++ ext p = _
    rw [hab]; simp
  obtain ⟨τ, hτ⟩ := hw'.1 p
  have hτ : LRun (canon sp (init p)) ((H p ++ a) ++ LEv.out o :: b) τ := h2 ▸ hτ
  obtain ⟨σ', h1, _⟩ := lrun_append.1 hτ
  obtain ⟨σ'', hHa, ha⟩ := lrun_append.1 h1
  have hdet : σ'' = σ := lrun_det hHa hσ
  subst hdet
  have hc : σ'.cur = σ''.cur := lrun_noinp ha (fun j hj => hni p j (by
    rw [hab]; exact List.mem_append_left _ hj))
  exact ⟨n, init, _, p, H p ++ a, b, σ', hw', hp', h2, lrun_append.2 ⟨σ'', hσ, ha⟩, hc⟩


/-! ### The system and environment assumptions -/

/-- Paragraph after Def. `def:explicit-relation`: "We consider a system whose
participants each follow a strategy that depends only on their local history,
and an environment that may send any legal input to any participant."  This entry is
the system half; the environment half is `«sec:complete-cap/environment»`.

Lean: `System sp D` has a commitment basis and a nondeterministic strategy
`strat n init p pre e` for every participant count `n`, initial inputs
`init : Fin n → I`, and participant `p`.  "Depends only on their local history"
is the definition of `Produced`: each event of `p` is checked against `p`'s
own local prefix only. -/
abbrev «sec:complete-cap/system» (sp : Spec I O) (D : Type) : Type := System sp D

/-- "We consider a system …": a history is *produced* by the system
when each participant's events are allowed given its own local prefix. -/
theorem «sec:complete-cap/system-produced» (Sys : System sp D) (init : Fin n → I)
    (H : History sp D n) :
    Produced Sys n init H ↔
      ∀ p a e b, H p = a ++ e :: b → Allowed Sys n init p a e :=
  Iff.rfl

/-- "… and an environment that may send any legal input to any participant."

Lean: input events are always allowed (their legality is checked by the run
relation `LRun` inside well-formedness `WF`). -/
theorem «sec:complete-cap/environment» (Sys : System sp D) (init : Fin n → I) (p : Fin n)
    (pre : List (LEv sp D n)) (j : I) :
    Allowed Sys n init p pre (.inp j) :=
  trivial

/-! ### Definitions `def:local-continuation` (Same-side continuation), `def:partition-notions` (Availability) -/

/-- **Def. `def:local-continuation`** (Same-side continuation).
"Availability asks that, during a partition, each participant can still emit
every explicit output its state permits."  "Consider a partitioned history
that the system produces, in which participant `p` ends in state `(i,R)`.  A
*same-side continuation* for `p` extends that history with events the system
can produce on `p`'s side alone, with no new input and no message from another
side.  Participant `p` can emit `o` when some same-side continuation for `p`
emits `o`."

Lean: a same-side continuation for `p` is unfolded as `Produced … ∧
Partitioned … comp ∧ (∀ q, comp q ≠ comp p → ext q = []) ∧
(∀ q j, inp j ∉ ext q)` in the unfolded form of
`«def:partition-notions/unfolded»`; this entry names the Availability that
quantifies over it. -/
abbrev «def:local-continuation» (Sys : System sp D) : Prop :=
  AvailabilityAtEnd Sys

/-- **Def. `def:partition-notions`** (Availability).  "The system has
*Availability for `E`* when, in every partitioned history it produces, each
participant `p` can emit every output in `R(i) ∩ E(i)`, where `(i,R)` is `p`'s
final state."

Lean: `AvailabilityAtEnd Sys` is the case `E = P` (= `AvailabilityFor sp.P Sys`);
for a general `E`, use `«def:partition-notions/for»`. -/
abbrev «def:partition-notions» (Sys : System sp D) : Prop := AvailabilityAtEnd Sys

/-- Def. `def:partition-notions`: "The system has Availability for `E` when,
in every partitioned history it produces, each participant `p` can emit every
output in `R(i) ∩ E(i)`, where `(i,R)` is `p`'s final state." -/
abbrev «def:partition-notions/for» (E : Table I O) (Sys : System sp D) : Prop :=
  AvailabilityFor E Sys

/-- Def. `def:partition-notions` at `E = P` (supporting lemma; the paper no
longer names this case): Availability for `P` is `AvailabilityAtEnd`. -/
theorem «def:partition-notions/for-S» (Sys : System sp D) :
    «def:partition-notions/for» sp.P Sys ↔ «def:partition-notions» Sys :=
  availabilityFor_S Sys

/-- Def. `def:partition-notions`, unfolded.  `WF init H` is "a history"
(legal local runs from `σ_P(init p)`, matched receives); `σ` is `p`'s final
state `(i,R)`; the same-side continuation appends `ext q` to each `H q`. -/
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
          LEv.out o ∈ ext p :=
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
produces is confluent at every common input extension of the participants'
current inputs."

Lean: confluence (Def. `def:distributed-consistency`) asks for a continuation
that need not stay partitioned and need not be produced by the system; see
`«def:partition-consistency/unfolded»`. -/
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

/-! ### The canonical system for `E` -/

/-- "The *canonical system for `E`* is the system whose participants follow
canonical runs and may emit any output of `E` their state permits."

Lean: `respSystem E`.  Its basis is the canonical basis (`kc u`, the
canonical commitment of each output), it allows no commitment event
(`«sec:complete-cap/canonical-system-canonical»`), it never sends, and its
strategies emit, by the canonical output event `output(u)`, any `u ∈ E(i)` at
the current input `i` that extends every earlier output (which every output
still in the participant's table does). -/
noncomputable abbrev «sec:complete-cap/canonical-system» (sp : Spec I O) (D : Type)
    (E : Table I O) : System sp D :=
  respSystem E

/-- The canonical system for `E` "follow[s] canonical runs": it has basis
`ℬ_P` and its strategies allow no commitment event. -/
theorem «sec:complete-cap/canonical-system-canonical» (sp : Spec I O) (D : Type)
    (E : Table I O) : CanonicalSystem («sec:complete-cap/canonical-system» sp D E) :=
  respSystem_canonical E

/-! ### Definition `def:lm-for-A` (Lifted Monotonicity for `E`) -/

/-- **Def. `def:lm-for-A` (Lifted Monotonicity for `E`).**  "`P` satisfies
Lifted Monotonicity for `E` when every finite set of rows of `E` with a common
input extension `j` has a common output extension in `P(j)`."  Lean: `ConsistentOn sp E`
(the library name predates the paper's term); finite sets are lists. -/
abbrev «def:lm-for-A» (sp : Spec I O) (E : Table I O) : Prop := ConsistentOn sp E

/-! ### Definition `def:escapes-cap` (Escaping CAP) -/

/-- **Def. `def:escapes-cap` (Escaping CAP).**  "A spec *escapes CAP* for
`E` when its canonical system for `E` has Availability for `E` and Partition
Consistency."

Lean: `D` is the (arbitrary) type of message payloads; the canonical system
never sends, so the choice does not matter. -/
abbrev «def:escapes-cap» (sp : Spec I O) (D : Type) (E : Table I O) : Prop :=
  «def:partition-notions/for» E («sec:complete-cap/canonical-system» sp D E) ∧
    «def:partition-consistency» («sec:complete-cap/canonical-system» sp D E)

/-- From the proof sketch of Theorem `thm:complete-cap`: "The canonical
system's participants never wait: each can emit any output of `E` that its
state allows, so it has Availability for `E`."  This entry checks that
sentence, for every spec and every `E`.  The connective sentence before Def.
`def:lm-for-A`, "Whether the canonical system's answers stay consistent across sides depends on one condition", is made precise by Theorem `thm:complete-cap`. -/
theorem «sec:complete-cap/canonical-never-waits» (sp : Spec I O) (D : Type) (E : Table I O) :
    «def:partition-notions/for» E («sec:complete-cap/canonical-system» sp D E) :=
  availabilityFor_resp E

/-- Supporting step for `«thm:complete-cap/E-eq-P»`: with `E = P`, Lifted
Monotonicity for `E` is the row-consistency condition
(Def. `def:common-expansion-condition`). -/
theorem «sec:complete-cap/lm-for-S» (sp : Spec I O) :
    «def:lm-for-A» sp sp.P ↔ sp.CommonExpansion :=
  consistentOn_S

/-! ### Theorem `thm:complete-cap` -/

/-- **Theorem `thm:complete-cap` (Complete CAP).**  "A spec escapes CAP for
`E` if and only if it satisfies Lifted Monotonicity for `E`."

Lean: `E ⊆ P` is the hypothesis `hES`. -/
theorem «thm:complete-cap» (sp : Spec I O) (D : Type) (E : Table I O)
    (hES : ∀ i o, E i o → sp.P i o) :
    «def:escapes-cap» sp D E ↔ «def:lm-for-A» sp E :=
  ⟨fun ⟨hA, hP⟩ => consistentOn_of_availabilityFor E hES _ hA (commonRefinement_of_pc hP),
   fun h => ⟨availabilityFor_resp E, pc_resp E h⟩⟩

/-- "For `E=P`, a spec escapes CAP exactly when Lifted Monotonicity holds"
(first half). -/
theorem «thm:complete-cap/E-eq-P» (sp : Spec I O) (D : Type) :
    «def:escapes-cap» sp D sp.P ↔ sp.LiftedMono :=
  («thm:complete-cap» sp D sp.P (fun _ _ h => h)).trans
    (consistentOn_S.trans (liftedMono_iff_commonExpansion sp).symm)

/-! ### Corollary `cor:complete-cap-any-system` -/

/-- **Corollary `cor:complete-cap-any-system`.**  "If some system for a spec
has Availability for `E` and Partition Consistency, then so does the spec's
canonical system for `E`."  (By Def. `def:escapes-cap`, the spec escapes CAP
for `E`.)

Lean: `Sys` is arbitrary (any basis, any nondeterministic local strategies). -/
theorem «cor:complete-cap-any-system» (E : Table I O) (hES : ∀ i o, E i o → sp.P i o)
    (Sys : System sp D) (hA : «def:partition-notions/for» E Sys)
    (hP : «def:partition-consistency» Sys) : «def:escapes-cap» sp D E :=
  («thm:complete-cap» sp D E hES).2
    (consistentOn_of_availabilityFor E hES Sys hA (commonRefinement_of_pc hP))

/-! ### Remarks after the corollary -/

/-- Full paper: "A system might hope to keep more outputs available, without
losing Partition Consistency, by issuing commitments that coordinate within
each side of a partition.  It cannot: Corollary `cor:complete-cap-any-system`
holds for every system, whether or not it issues commitments."  Lean: the step of the corollary, that Lifted
Monotonicity for `E` is necessary, holds for an arbitrary system (any basis,
any nondeterministic local strategies, so any commitments its output and
commit events issue). -/
theorem «sec:complete-cap/necessity-any-system» (E : Table I O) (hES : ∀ i o, E i o → sp.P i o)
    (Sys : System sp D) (hA : «def:partition-notions/for» E Sys)
    (hP : «def:partition-consistency» Sys) : «def:lm-for-A» sp E :=
  consistentOn_of_availabilityFor E hES Sys hA (commonRefinement_of_pc hP)

  /-- "For `E=P`, … the canonical system then needs no commitment"
  (second half; for the canonical system itself see
  `«sec:complete-cap/canonical-system-commitment-free»`).  Lean: with
  Lifted Monotonicity, the commitment-free system `cfSystem` (empty basis,
  every legal output emitted by `output(o)`) has Availability and Partition
  Consistency, and every history it produces is commitment-free: it has no
  commitment event, and every output event emits a legal output.  This
  statement is specification-relative: restricting a strategy to a smaller
  `E` does not turn row-removing commitments into commitment-free steps
  relative to `P`. -/
theorem «sec:complete-cap/proof-system-commitment-free» (sp : Spec I O) (D : Type)
      (h : sp.LiftedMono) :
      («def:partition-notions» (cfSystem sp D) ∧
        «def:partition-consistency» (cfSystem sp D)) ∧
      ∀ (N : Nat) (init : Fin N → I) (H : History sp D N),
        Produced (cfSystem sp D) N init H →
        (∀ p γ, LEv.commitment γ ∈ H p → γ = []) ∧
        ∀ p a o b, H p = a ++ LEv.out o :: b →
          ∀ σ, LRun (canon sp (init p)) a σ → Exposable σ o :=
  ⟨⟨(availability_iff_atEnd _).1 (complete_cap_cf sp D h).1,
      (partitionConsistency_iff_atEnd _).1 (complete_cap_cf sp D h).2⟩,
    fun _ _ _ => cfSystem_coordinationFree⟩

/-- "For `E=P`, a spec escapes CAP exactly when Lifted Monotonicity holds; the
canonical system then needs no commitment."  Lean: with
Lifted Monotonicity, the canonical system for `P` (`respSystem sp.P`, the
system of Def. `def:escapes-cap`) performs no commitment event, and every
output it emits is exposable at the emitting participant's state, so no output
event applies a commitment.  Without Lifted Monotonicity the claim fails: the
canonical system may emit an output that is not exposable. -/
theorem «sec:complete-cap/canonical-system-commitment-free» (sp : Spec I O) (D : Type)
    (h : sp.LiftedMono) {N : Nat} {init : Fin N → I} {H : History sp D N}
    (hp : Produced («sec:complete-cap/canonical-system» sp D sp.P) N init H) :
    (∀ p γ, LEv.commitment γ ∉ H p) ∧
    ∀ p a o b, H p = a ++ LEv.out o :: b →
      ∀ σ, LRun (canon sp (init p)) a σ → Exposable σ o :=
  respSystem_P_commitmentFree ((liftedMono_iff_commonExpansion sp).1 h) hp

  /-- Supporting operational lemma for the full-availability case.  If an output
  event `output(o)` in a receive-free local prefix removes a row by its canonical
  commitment `x_o` (leaving `kcState σ o`) and another participant can start
  below that row's input, Availability realizes the contradictory choice at the
  other participant.  The same holds for a commitment event
  (`availability_not_coordinationFreeH_commit`). -/
theorem «sec:complete-cap/A-eq-S-no-commitment» (Sys : System sp D)
    (hA : «def:partition-notions» Sys)
    {n : Nat} {init : Fin n → I} {H : History sp D n} (hw : WF init H)
    (hp : Produced Sys n init H) {p q : Fin n} (hqp : q ≠ p)
    {a b : List (LEv sp D n)} {o : O} {σ : State sp}
    (hH : H p = a ++ LEv.out o :: b) (hnr : ∀ q' k j d, LEv.recv q' k j d ∉ a)
    (hrun : LRun (canon sp (init p)) a σ) (ho : σ.R σ.cur o)
    {k : I} {x : O} (hx : σ.R k x) (hnx : ¬ (kcState σ o ho).R k x) (hqk : init q ≼ k) :
    ¬ Sys.CoordinationFreeH :=
  availability_not_coordinationFreeH Sys hA hw hp hqp hH hnr hrun ho hx hnx hqk

  /-- Supporting example for the voters' remark in the election-voters
  example after Theorem `thm:complete-cap` (not quoted): for a smaller `E`, an output of `E`
  can still apply a commitment under the declared spec.  Lean: one input, `P = {o, x}` incomparable and `E = {o}`.
  `P` satisfies Lifted Monotonicity for `E`, but `o` is not exposable.  Thus the
  output event for `o` is not available under the empty basis, while the
  canonical output event is available under `ℬ_P` and applies the commitment
  `x_o`.  Suppressing `x` in a strategy does not make the specification event
  commitment-free. -/
theorem «sec:complete-cap/local-row-removal-necessary» :
      ConsistentOn CAP.lcSpec CAP.lcA ∧ ¬ Exposable (canon CAP.lcSpec ()) .o ∧
      (∃ τ, SysStep (canonCommitmentBasis CAP.lcSpec) (canon CAP.lcSpec ()) (.output .o) τ) ∧
      ¬ ∃ τ, SysStep (fun _ => False) (canon CAP.lcSpec ()) (.output .o) τ := by
    have hn := CAP.lcSpec_o_not_exposable
    have ho : (canon CAP.lcSpec ()).R (canon CAP.lcSpec ()).cur .o := ⟨trivial, trivial⟩
    exact ⟨lcSpec_consistentOn, hn, ⟨outState _ _ ho, canonical_support _ _ ho⟩,
      fun ⟨_, hs⟩ => hn (eps_step_iff.1 hs).2.1⟩

/-- "When Lifted Monotonicity for `E` fails, some output of `E` waits for
another side, sacrificing Availability, or is emitted anyway, sacrificing
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

/-- "Linearizability respects real-time order: if one operation finishes
before another begins, every linearization puts the first before the second.
In the register example, suppose the write finishes before the read begins.
Every linearization then puts the write first, so the read must return `v`.
But each of `p` and `q` sees only its own request, and Availability requires
`p` to acknowledge the write and `q` to answer `v_0`.  No output for the two
requests together extends both answers, so the spec does not satisfy Lifted
Monotonicity for them."

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

/-- "By Corollary `cor:complete-cap-any-system`, no system can keep both
outputs available and stay consistent across a partition, which is Gilbert and
Lynch's theorem."  Lean: no system for `regFullSpec` has
Availability and Partition Consistency. -/
theorem «sec:complete-cap/gl-no-system» (Sys : System CC.GL.regFullSpec D) :
    ¬ («def:partition-notions» Sys ∧ «def:partition-consistency» Sys) :=
  CC.GL.gilbert_lynch_direct_cap Sys

/-- "Two differences from Gilbert and Lynch's setting do not affect the
conclusion.  In general our Availability and Partition Consistency are stronger
than their availability and consistency, but in the register example they
coincide.  Each fiber holds a single output, so emitting every permitted output
is the same as responding, and a common output extension of the two answers is
a single linearization that explains both."

Lean: the two-row case of the proof, for outputs forced at their inputs, with
Answering (each participant can emit *some* output) in place of Availability
and a common output extension of the emitted outputs (`CommonRefinementAtEnd`) in
place of Partition Consistency; the proof runs the two participants on
separate sides.  For the register, a common output extension lies in
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

/-- "Gilbert and Lynch's theorem is a case of Complete CAP in which Lifted
Monotonicity for `E` fails.  We show the failure for the register example,
then extend the conclusion from the canonical system to every system." …
"Their theorem
concerns every system, not only the canonical one, so it needs one more
step." … "By Corollary `cor:complete-cap-any-system`, no system can keep both
outputs available and stay consistent across a partition, which is Gilbert
and Lynch's theorem."  Lean: `Sys` is an arbitrary system (any basis, any
local strategies), not only the canonical one: no system for the register
lets every request receive a response and keeps the emitted responses
reconcilable (explained by one linearization). -/
theorem «sec:complete-cap/gilbert-lynch» (Sys : System CC.GL.regFullSpec D) :
    ¬ (AnsweringAtEnd Sys ∧ CommonRefinementAtEnd Sys) :=
  CC.GL.gilbert_lynch_direct Sys

/-- "We also put the real-time order of the write and the read in the input,
while their model takes it from the execution; the theorem holds in their model
as well (Appendix `app:cap-response`)." —
Corollary `cor:gilbert-lynch`, client form (both hypotheses required only of
two-participant client histories, consistency at the realized history). -/
theorem «sec:complete-cap/gl-realized» (Sys : System CC.GL.regSpec D) :
    ¬ (CC.AsyncGL.AnsweringC Sys ∧ CC.AsyncGL.RealizedRPCC Sys) :=
  CC.AsyncGL.gilbert_lynch_client Sys

/-- Appendix `app:cap-response` (pointed to from the body's "the theorem holds in
their model as well") also extends Complete CAP to systems that choose their
responses when responses are not forced: Theorem `thm:complete-cap-response` (see
`Paper/AppF_ResponseAvailability.lean`). -/
theorem «sec:complete-cap/response-form» (sp : Spec I O) (D : Type) (Q : Obligation sp) :
    (∃ Sys : System sp D, Sys.Replicated ∧ ResponseAvailability Sys (fun _ _ => Q.Q) ∧
      ResponsePC Sys) ↔
    ∃ T, ResponseInterface Q T ∧ ConsistentOn sp T :=
  complete_cap_response sp D Q

/-- "the theorem holds in their model as well (Appendix `app:cap-response`)":
Gilbert and Lynch's asynchronous model, Proposition `prop:gl-async`. -/
theorem «sec:complete-cap/gl-async» {N : Nat} {M : Type} (hN : 2 ≤ N)
    (A : CC.AsyncGL.Alg N M) : ¬ (CC.AsyncGL.Available A ∧ CC.AsyncGL.Atomic A) :=
  CC.AsyncGL.gilbert_lynch_async hN A

end CC.Paper
