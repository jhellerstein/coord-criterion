import CoordCriterion.Distributed.Systems
import CoordCriterion.Distributed.SystemConfluence
import CoordCriterion.CAP.ResponseAvailability
import CoordCriterion.CAP.AvailabilityAtEnd
import CoordCriterion.CAP.Necessity
import CoordCriterion.CAP.Coordination

/-!
# Paper Appendix D: proofs for §4 (`paper/app-distributed.tex`)

Statement layer for the subsection *Proofs* of Appendix
`app:proofs-sec4`: the proofs of Prop. `prop:distributed-consistency`, the
paragraph *Exchanging outputs* (`app:exchanging-outputs`), and the proofs of
Prop. `prop:commitment-conflict`, Theorem `thm:complete-cap`, and
Corollary `cor:complete-cap-any-system`.  The results themselves are stated in
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

/-- Proof of Prop. `prop:distributed-consistency`: "A cut is confluent at `j`
exactly when its participant runs are.  First assume runs are consistent.  The
participant runs at any cut form a finite family of runs, so histories are
consistent.  Now assume histories are consistent.  Every finite family of runs
is the family of participant runs, at the final cut, of a message-free history
with one participant per run, so runs are consistent." -/
theorem «proof:prop:distributed-consistency» (sp : Spec I O) (D : Type) :
    sp.Consistent ↔ Dist.DistConsistent sp D :=
  Dist.consistent_iff_distConsistent sp D

/-! ## Exchanging outputs (`app:exchanging-outputs`) -/

/-- *Exchanging outputs* (table level).  "It can also silently honor `o`
by restricting its table to `R[out ⪰ o]`. … Silent honoring never changes
whether a cut is confluent at a common input extension `j`.  It cannot make a
cut confluent at `j`, because it only removes rows … It cannot make a cut
non-confluent at `j` either.  A row that survives at `j` already extends every output emitted in the cut
(Lemma run-residual), including `o`, so the restriction keeps the row."

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

/-- Proof of Prop. `prop:system-confluence`, part (1): "By Lemma
canonical-equivalent, `R_r ⊆ R̂_r`.  Rows are never added, so a row that a
commitment event of `ρ_r` removed is not in `R_r`; hence `R_r ⊆ R̂_r \ Δ(ρ_r)`.
Conversely, let `(k,u) ∈ R̂_r \ Δ(ρ_r)`. … By induction on the events,
`(k,u) ∈ R_r`."  Part (2): "First assume continuations bring every run to a
common state `(k,R)`. … Otherwise consider the partial
function that maps each state with current input `k` whose table contains
`(k,u)` and some other row, and whose rows at `k` all extend `u`, to
`(k,{(k,u)})`. … So the function is a commitment (Definition commitment), and a
commitment event that applies it ends at `(k,{(k,u)})`.  Every run therefore
reaches `(k,{(k,u)})`."

Lean: (1) is `Dist.table_decomp` (by induction on the run, via
`Dist.table_decomp_gen`); (2) uses `Dist.keepOnly`, whose domain is slightly
larger (rows at `k` other than `u` need only not lie below `u`), and
`Dist.reach_single`, which reaches `Dist.single k u` from any state at an input
below `k` that contains `(k,u)`, under the full basis. -/
theorem «proof:prop:system-confluence» {sp : Spec I O} :
    (∀ {B : CommitmentBasis sp} {σ ρ ρh : State sp} {es : List (SEvent sp)},
      SysExec B σ es ρ → Exec σ (es.filterMap SEvent.erase) ρh →
        ∀ k u, ρ.R k u ↔ ρh.R k u ∧ ¬ Dist.Removed B σ es k u) ∧
    (∀ {σ : State sp} {k : I} {u : O} (hu : sp.P k u), σ.cur ≼ k → σ.R k u →
      ∃ es : List (SEvent sp), SysExec (fun _ => True) σ es (Dist.single k u hu)) :=
  ⟨fun h hc => Dist.table_decomp h hc, fun hu hk hku => Dist.reach_single hu hk hku⟩

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

/-- Proof of Theorem `thm:complete-cap`: "The canonical system for `E` has the
canonical basis and no commitment events.  Its strategies emit any output `o`
of `E` in the current fiber by the canonical output event `output(o)` … So
the system has Availability for `E` whatever the spec.  First assume `P`
satisfies Lifted Monotonicity for `E`.  Every output the canonical system
emits is the output of a row of `E` whose input lies below the current one. …
The system emits only canonical output events, so Lemma `lem:reconciliation`
makes this confluence at `j`, and Partition Consistency follows."   Lean: `respSystem E`, a canonical system; Availability for `E`
holds with no hypothesis on the spec. -/
theorem «thm:complete-cap/proof-sufficiency» (E : Table I O) (h : ConsistentOn sp E) :
    AvailabilityFor E (respSystem (sp := sp) (D := D) E) ∧
    PartitionConsistencyAtEnd (respSystem (sp := sp) (D := D) E) ∧
    CanonicalSystem (respSystem (sp := sp) (D := D) E) :=
  ⟨availabilityFor_resp E, pc_resp E h, respSystem_canonical E⟩

/-- Proof of Theorem `thm:complete-cap`, converse: "Now assume some system, such
as the canonical system for `E`, has Availability for `E` and Partition
Consistency. … take one participant `p_r` per row, starting at input `i_r`,
each on its own side and running without messages.  A partitioned history has
at least two sides, so if `n = 1` we add a second participant for that row on
another side.  By Availability for `E`, each `p_r` can emit `o_r`.  By
Partition Consistency, the participants then reach one state `(j,R)`, which
has some row `(j,u)` … so `u` extends every `o_r`, and Lifted Monotonicity for
`E` follows."  Lean: only a common output
extension of the emitted outputs is used (implied by Partition
Consistency). -/
theorem «thm:complete-cap/proof-necessity» (E : Table I O) (hES : ∀ i o, E i o → sp.P i o)
    (Sys : System sp D) (hA : AvailabilityFor E Sys) (hC : CommonRefinementAtEnd Sys) :
    ConsistentOn sp E :=
  consistentOn_of_availabilityFor E hES Sys hA hC

/-! ## Proof of Corollary `cor:complete-cap-any-system` -/

/-- Proof of Corollary `cor:complete-cap-any-system`: "The converse argument
in the proof of Theorem `thm:complete-cap` applies to any system with
Availability for `E` and Partition Consistency, so `P` satisfies Lifted
Monotonicity for `E`.  By Theorem `thm:complete-cap`, `P` escapes CAP for
`E`."  Lean: the conclusion is stated with escaping CAP unfolded (the
canonical system for `E` is `respSystem E`). -/
theorem «cor:complete-cap-any-system/proof» (E : Table I O) (hES : ∀ i o, E i o → sp.P i o)
    (Sys : System sp D) (hA : AvailabilityFor E Sys) (hP : PartitionConsistencyAtEnd Sys) :
    ConsistentOn sp E ∧
      (AvailabilityFor E (respSystem (sp := sp) (D := D) E) ∧
        PartitionConsistencyAtEnd (respSystem (sp := sp) (D := D) E)) :=
  have h := consistentOn_of_availabilityFor E hES Sys hA (commonRefinement_of_pc hP)
  ⟨h, availabilityFor_resp E, pc_resp E h⟩

end CAP

end CC.Paper
