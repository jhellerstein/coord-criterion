import CoordCriterion.Distributed.Systems
import CoordCriterion.CAP.ResponseAvailability
import CoordCriterion.CAP.AvailabilityAtEnd
import CoordCriterion.CAP.Necessity
import CoordCriterion.CAP.Coordination

/-!
# Paper Appendix B: deferred proofs for §4 (`appendices/proof-machinery.tex`)

Statement layer for the subsection *Proofs for Section 4* of Appendix
`app:proofs`: the proofs of Prop. `prop:distributed-consistency`, the
paragraph *Exchanging outputs* (`app:exchanging-outputs`), and the proofs of
Prop. `prop:commitment-conflict`, Theorem `thm:complete-cap`, and
Corollary `cor:complete-cap-S`.  The results themselves are stated in
`Paper/S4_Distributed.lean` and `Paper/S4_5_CompleteCAP.lean`.

How to read this file: open the appendix next to it.  Entries follow the
appendix's order.  A "Proof of …" paragraph is a declaration `«proof:<label>»`
(or, for entries carried over from §4.4, `«<label>/proof-…»`) whose statement
is the result proved or the key step of the written proof.  Conventions are
those of `Paper/S4_Distributed.lean` and `Paper/S4_5_CompleteCAP.lean`;
proofs are one-line pointers into the library.
-/

namespace CC.Paper

section Distributed

open CC Classical

variable {I O : Type} [PO I] [PO O]

/-- Proof of Prop. `prop:distributed-consistency`: "The participant runs at any
cut are a finite family of runs.  Conversely, every finite family of runs is
the family of participant runs of a message-free history, one participant per
run, at its final cut." -/
theorem «proof:prop:distributed-consistency» (sp : Spec I O) (D : Type) :
    sp.Consistent ↔ Dist.DistConsistent sp D :=
  Dist.consistent_iff_distConsistent sp D

/-! ## Exchanging outputs (`app:exchanging-outputs`) -/

/-- *Exchanging outputs* (table level).  "It can silently honor `o` by
restricting its table to `R[out ⪰ o]` … Silent honoring cannot change
confluence in either direction.  It cannot help, because it only removes rows
… It cannot hurt, because a row that survives at a common input extension already
extends every output emitted in the cut (Lemma run-residual), including `o`."

Lean: each family member is a state with the residual shape for its emitted
outputs (the shape of every run, `IsRun.residual`) and a list of honored
outputs, each emitted by some member; a row at `j` survives the honored tables
iff it survives the original ones (with the survivor test, this is
confluence). -/
theorem «app:exchanging-outputs» {sp : Spec I O}
    (fam : List (State sp × List O × List O))
    (hres : ∀ x ∈ fam, Residual x.1 x.2.1)
    (hos : ∀ x ∈ fam, ∀ o ∈ x.2.2, ∃ y ∈ fam, o ∈ y.2.1) (j : I) :
    (∃ u, sp.P j u ∧ ∀ x ∈ fam, Dist.honor x.1.R x.2.2 j u) ↔
      (∃ u, sp.P j u ∧ ∀ x ∈ fam, x.1.R j u) :=
  Dist.honor_survivor fam hres hos j

/-- *Exchanging outputs* (history level).  "The confluence of a cut therefore
depends on which outputs were emitted, not on who has heard about them."

Lean: if each participant `p` honors outputs `os p` emitted in the cut, the
cut is confluent at `j` iff some row `(j,u)` survives every honored table. -/
theorem «app:exchanging-outputs/cut» {D : Type} {n : Nat}
    {sp : Spec I O} {H : Dist.History I O D n} (hW : H.WF sp) {C : Dist.Pos n → Prop}
    (hC : H.IsCut C) {σs : Fin n → State sp} (hE : H.Endpoint sp C σs) (os : Fin n → List O)
    (hos : ∀ p, ∀ o ∈ os p, H.EmittedIn C o) (j : I) (hj : ∀ p, (σs p).cur ≼ j) :
    H.CutConfluentAt sp C j ↔ ∃ u, sp.P j u ∧ ∀ p, Dist.honor (σs p).R (os p) j u :=
  Dist.honor_cut_confluent hW hC hE os hos j hj

/-- *Exchanging outputs.*  "This restriction is a table, not a specification
state: it may have no row at the participant's current input, so silent
honoring is not a specification event."

Lean: a functional, monotone specification on `Fin 3` (`Dist.spV3`); `q` at
`σ_P(1)` may emit `1`; honoring `1` at `p`'s `σ_P(0)` leaves no row at `p`'s
current input `0`, although the row `(2,2)` survives. -/
theorem «app:exchanging-outputs/honored-table-not-state» :
    (canon Dist.spV3 (Dist.v 1)).R (Dist.v 1) (Dist.v 1) ∧
    (¬ ∃ x, Dist.honor (canon Dist.spV3 (Dist.v 0)).R [Dist.v 1] (Dist.v 0) x) ∧
    Dist.honor (canon Dist.spV3 (Dist.v 0)).R [Dist.v 1] (Dist.v 2) (Dist.v 2) ∧
    (canon Dist.spV3 (Dist.v 1)).R (Dist.v 2) (Dist.v 2) :=
  Dist.honor_counterexample

/-- Proof of Prop. `prop:commitment-conflict`.  The two
clauses of `CommitmentContradictsAt` are the proof's two cases: an accepted
input whose fiber the commitment emptied, or an emitted output whose row it
removed.  In either case, because transitions never add rows, no state with
current input `k` is reachable from both resulting states. -/
theorem «proof:prop:commitment-conflict» {sp : Spec I O}
    {c : Commitment sp} {σ σc τ : State sp} {k : I}
    (happ : c.app σ = some σc) (hcontra : Dist.CommitmentContradictsAt σ σc τ k) :
    ¬ ∃ ρ : State sp, ρ.cur = k ∧ Reach σc ρ ∧ Reach τ ρ :=
  Dist.commitment_contradiction_reach happ hcontra

end Distributed

section CAP

open CC CC.CAP

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type}

/-! ## Proof of Theorem `thm:complete-cap` -/

/-- Proof of Theorem `thm:complete-cap`, (2)⇒(1): "Take the system whose
strategies emit, by the canonical output event `output(o)` …, any output `o`
of `E` in the current fiber. … so the system has Availability for `E`. …
For a system that emits only canonical output events, that is confluence at
`j`, which gives Partition Consistency."  Lean: `respSystem E`, a canonical
system. -/
theorem «thm:complete-cap/proof-sufficiency» (E : Table I O) (h : ConsistentOn sp E) :
    AvailabilityFor E (respSystem (sp := sp) (D := D) E) ∧
    PartitionConsistencyAtEnd (respSystem (sp := sp) (D := D) E) ∧
    CanonicalSystem (respSystem (sp := sp) (D := D) E) :=
  ⟨availabilityFor_resp E, pc_resp E h, respSystem_canonical E⟩

/-- Proof of Theorem `thm:complete-cap`, (1)⇒(2): "take one participant `p_r`
per row, starting at input `i_r`, each on its own side … By
Availability for `E`, each `p_r` can emit `o_r`.  By Partition Consistency,
they then reach one state `(j,R)`, which has some row `(j,u)` … so `u`
extends every `o_r`."  Lean: only a common output extension of the emitted outputs
is used (implied by Partition Consistency). -/
theorem «thm:complete-cap/proof-necessity» (E : Table I O) (hES : ∀ i o, E i o → sp.P i o)
    (Sys : System sp D) (hA : AvailabilityFor E Sys) (hC : CommonRefinementAtEnd Sys) :
    ConsistentOn sp E :=
  consistentOn_of_availabilityFor E hES Sys hA hC

/-! ## Proof of Corollary `cor:complete-cap-S` -/

/-- Proof of Corollary `cor:complete-cap-S`: "by Complete CALM and
Proposition `prop:distributed-consistency` it has Partition Consistency."
Strong reading: the confluence continuation itself can be chosen
commitment-free and receive-free (`PartitionConsistencyCF`). -/
theorem «cor:complete-cap-S/proof-cf-continuations» (sp : Spec I O) (D : Type) :
    ((∃ Sys : System sp D, Availability Sys ∧ PartitionConsistency Sys) → sp.LiftedMono) ∧
    (sp.LiftedMono → Availability (cfSystem sp D) ∧ PartitionConsistencyCF (cfSystem sp D)) :=
  complete_cap_strong sp D

end CAP

end CC.Paper
