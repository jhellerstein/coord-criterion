import CoordCriterion.CAP.ResponseAvailability
import CoordCriterion.CAP.AsyncGilbertLynch
import CoordCriterion.CAP.ChosenAvailability

/-!
# Paper Appendix F, "Choosing the Explicit Relation" (`appendices/cap-response.tex`)

Statement layer for Appendix `app:cap-response`, in paper order: the response
obligation, continuations within a block, Response Availability, Response
Partition Consistency and the remarks on them, replicated systems, Lemma
`lem:locality`, response interfaces and how a system serves one, Theorem
`thm:complete-cap-response`, the remark "Without replication", choosing versus
requiring every output, Lemma `lem:forced-answer`, the register,
interleavings and realized histories, client histories, Corollary
`cor:gilbert-lynch`, and Proposition `prop:gl-async`.

The paper states its definitions at the end of every partitioned history; the
library's cut forms are equivalent (`CAP/ChosenAvailability.lean`).

How to read this file: open it next to the `.tex` file.  The `/-! ## … -/`
headers are the appendix's subsections (and paragraphs).  Each numbered
result is a declaration named by its LaTeX label in guillemets
(`CC.Paper.«thm:complete-cap-response»`); unlabeled claims are named
`«<enclosing label>/<slug>»`.  Docstrings quote the paper (LaTeX lightly
normalized) and say how the Lean statement corresponds when it reads
differently.  Statements are written out in full; proofs are one-line
pointers into `CoordCriterion/CAP/ResponseForm.lean`,
`CAP/ResponseAvailability.lean`, `CAP/Register.lean`, and
`CAP/AsyncGilbertLynch.lean`.

General conventions: participants are `Fin n`; a (possibly non-uniform)
obligation is a family `Q : (n : Nat) → Fin n → Table I O` (`Q n p` is `Q_p`
in the participant set `Fin n`); a uniform one is an `Obligation sp`, used as
`fun _ _ => Q.Q`.  The system model is that of `CAP/Model.lean`.
-/

namespace CC.Paper

open CC CC.CAP

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type} {n : Nat}

/-! ## Appendix F preamble -/

/-- "The *emitted rows* of a run are the pairs `(i,o)` such that it emits `o`
at current input `i`."  Lean: for a canonical execution `es` started at
current input `i`, `emRows i es`. -/
abbrev «app:cap-response/emitted-rows» : I → List (Event I O) → List (I × O) := emRows

/-! ## Obligations, availability, and locality

### Definition `def:response-obligation` -/

/-- **Def. `def:response-obligation`** (Response obligation, answering).
"A response obligation assigns to each participant `p` a relation `Q_p ⊆ S`
that is total on `I` and upward closed within fibers: if `(i,o) ∈ Q_p`,
`(i,u) ∈ S`, and `o ⪯ u`, then `(i,u) ∈ Q_p`.  An output in `Q_p(i)` *answers*
at `i` for `p`."

Lean: `Obligation sp` packages a uniform `Q` with the three conditions.  A
per-participant obligation is a family `(n : Nat) → Fin n → Table I O`; the
register's (`CC.GL.regQn`) is checked to satisfy the conditions in
`«app:cap-response/register-obligation»` below. -/
abbrev «def:response-obligation» (sp : Spec I O) : Type := Obligation sp

/-- Def. `def:response-obligation`, the fields of `Obligation`. -/
theorem «def:response-obligation/fields» (Q : Obligation sp) :
    (∀ i o, Q.Q i o → sp.S i o) ∧ (∀ i, ∃ o, Q.Q i o) ∧
    ∀ i o u, Q.Q i o → sp.S i u → o ≼ u → Q.Q i u :=
  ⟨Q.sub, Q.total, Q.up⟩

/-- **Def. `def:uniform-obligation`** (Uniform obligation).  "A response
obligation is *uniform* when every `Q_p` is the same relation `Q`."

Lean: `Obligation sp` carries one `Q`; the uniform case is the identity shape
used throughout. -/
abbrev «def:uniform-obligation» (sp : Spec I O) : Type := Obligation sp

/-- "Response availability is only as strong as `Q_p`: if an output permitted
at every input answers, every specification is available."  Lean: indeed the
conditions of Theorem `thm:complete-cap-response` (Response Availability and Response Partition Consistency
for a replicated system) then holds. -/
theorem «app:cap-response/trivially-available» (Q : Obligation sp) (o0 : O)
    (h0 : ∀ i, Q.Q i o0) :
    ResponseForm sp D Q :=
  (responseForm_iff_cuts sp D Q).2 (trivially_available Q o0 h0)

/-! ### Definition `def:response-availability` -/

/-- **Def. `def:response-availability`**: "A continuation of a partitioned
history is within `p`'s block when the system produces it, it adds only history
events of `p`'s block, and none of its receives takes a message sent from
another block. … A system has Response Availability for `(Q_p)` when, in
every partitioned history it produces, each participant `p`, ending with
current input `i`, satisfies two conditions.  (1) *Answering.*  In some
continuation within `p`'s block that adds no input event at `p`, `p`
emits some output in `Q_p(i)`.  (2) *Input acceptance.*  For every `j ⪰ i`,
in some continuation within `p`'s block, `p` records `input(j)`."

Lean: "within `p`'s block" is `Produced … ∧ Partitioned … comp ∧
(∀ q, comp q ≠ comp p → ext q = [])`; a continuation local to `p` adds,
besides, no input event. -/
abbrev «def:response-availability» (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O) :
    Prop :=
  ResponseAvailabilityEnd Sys Q

/-- Def. `def:response-availability`, unfolded; `σ` is `p`'s final state, so
`σ.cur` is its current input `i`. -/
theorem «def:response-availability/unfolded» (Sys : System sp D)
    (Q : (n : Nat) → Fin n → Table I O) :
    ResponseAvailabilityEnd Sys Q ↔
      ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
        WF init H → Produced Sys n init H → Partitioned H comp →
        ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) (H p) σ →
          (∃ ext : Fin n → List (LEv sp D n),
            WF init (fun q => H q ++ ext q) ∧ Produced Sys n init (fun q => H q ++ ext q) ∧
            Partitioned (fun q => H q ++ ext q) comp ∧
            (∀ q, comp q ≠ comp p → ext q = []) ∧ (∀ j, LEv.inp j ∉ ext p) ∧
            ∃ γ o, Q n p σ.cur o ∧ LEv.out γ o ∈ ext p) ∧
          (∀ j, σ.cur ≼ j → ∃ ext : Fin n → List (LEv sp D n),
            WF init (fun q => H q ++ ext q) ∧ Produced Sys n init (fun q => H q ++ ext q) ∧
            Partitioned (fun q => H q ++ ext q) comp ∧
            (∀ q, comp q ≠ comp p → ext q = []) ∧ LEv.inp j ∈ ext p) :=
  Iff.rfl

/-- Def. `def:response-availability`: the library's form, at every consistent
cut, is equivalent. -/
theorem «def:response-availability/at-cuts» (Sys : System sp D)
    (Q : (n : Nat) → Fin n → Table I O) :
    ResponseAvailability Sys Q ↔ ResponseAvailabilityEnd Sys Q :=
  responseAvailability_iff_end Sys Q

/-- Def. `def:response-availability`(1), *Answering*, on its own (used by
Lemma `lem:forced-answer`), implied by Response Availability, and equivalent
to its cut form. -/
theorem «def:response-availability(1)» (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O) :
    (AnsweringEnd Sys Q ↔
      ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
        WF init H → Produced Sys n init H → Partitioned H comp →
        ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) (H p) σ →
          ∃ ext : Fin n → List (LEv sp D n),
            WF init (fun q => H q ++ ext q) ∧ Produced Sys n init (fun q => H q ++ ext q) ∧
            Partitioned (fun q => H q ++ ext q) comp ∧
            (∀ q, comp q ≠ comp p → ext q = []) ∧ (∀ j, LEv.inp j ∉ ext p) ∧
            ∃ γ o, Q n p σ.cur o ∧ LEv.out γ o ∈ ext p) ∧
    (ResponseAvailabilityEnd Sys Q → AnsweringEnd Sys Q) ∧
    (Answering Sys Q ↔ AnsweringEnd Sys Q) :=
  ⟨Iff.rfl, fun h n init H comp hw hp hpt p σ hσ => (h n init H comp hw hp hpt p σ hσ).1,
    answering_iff_end Sys Q⟩

/-- "Input acceptance says that `p` never seals an expansion of its current
input."  Lean, at any cut, in particular the end of the history: where `p`
is in state `σ`, an Input-acceptance continuation for `j` exists iff `p`'s
table still has a row at `j`. -/
theorem «def:response-availability/input-acceptance-no-seal» (Sys : System sp D)
    {init : Fin n → I} {H : History sp D n} {comp : Fin n → Nat} (hwf : WF init H)
    (hprod : Produced Sys n init H) (hpart : Partitioned H comp) {c : Fin n → Nat}
    (hcut : IsCut H c) {p : Fin n} {σ : State sp}
    (hσ : LRun (canon sp (init p)) ((H p).take (c p)) σ) (j : I) :
    (∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)),
        Extends H c H' ext ∧ WF init H' ∧ Produced Sys n init H' ∧ Partitioned H' comp ∧
        (∀ q, comp q ≠ comp p → ext q = []) ∧ LEv.inp j ∈ ext p) ↔ ∃ u, σ.R j u :=
  input_acceptance_iff Sys hwf hprod hpart hcut hσ j

/-- "It excludes specifications whose answers require such a seal": if no
answer at `i` has a refinement at some `j ⪰ i`, no system has Response
Availability (already with two participants, each alone). -/
theorem «def:response-availability/excludes-forced-seal» (Sys : System sp D)
    (Q : (n : Nat) → Fin n → Table I O) {i j : I} (hij : i ≼ j)
    (hno : ∀ o, Q 2 0 i o → ¬ ∃ u, sp.S j u ∧ o ≼ u) :
    ¬ ResponseAvailabilityEnd Sys Q :=
  fun h => ra_excludes_forced_seal Sys Q hij hno ((responseAvailability_iff_end Sys Q).2 h)

/-- "… such as the election under the equality order
(Figure `fig:nonmonotone-frame`)": no system for `electionEq` has Response
Availability for any obligation contained in `S`. -/
theorem «def:response-availability/election-equality-order» (Sys : System electionEq D)
    (Q : (n : Nat) → Fin n → Table Ballots Win) (hQ : ∀ n p i o, Q n p i o → electionEq.S i o) :
    ¬ ResponseAvailabilityEnd Sys Q :=
  fun h => election_eq_no_ra Sys Q hQ ((responseAvailability_iff_end Sys Q).2 h)

/-! ### Definition `def:response-partition-consistency` -/

/-- **Def. `def:response-partition-consistency`**: "A system has Response
Partition Consistency when, in every partitioned history it produces and at
every common expansion `j` of the participants' current inputs, some
`u ∈ S(j)` refines every output emitted in the history."  Lean: this is
`CommonRefinementAtEnd`; the library's cut form `ResponsePC` is equivalent. -/
theorem «def:response-partition-consistency» (Sys : System sp D) :
    (CommonRefinementAtEnd Sys ↔
      ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
        WF init H → Produced Sys n init H → Partitioned H comp →
        ∀ j : I, (∀ p σ, LRun (canon sp (init p)) (H p) σ → σ.cur ≼ j) →
        ∃ u, sp.S j u ∧ ∀ p γ o, LEv.out γ o ∈ H p → o ≼ u) ∧
    (ResponsePC Sys ↔ CommonRefinementAtEnd Sys) :=
  ⟨Iff.rfl, responsePC_iff_commonRefinement Sys⟩

/-- "This is the part of Partition Consistency that the converse of Theorem
`thm:complete-cap` uses, so that theorem also holds with Response Partition
Consistency in place of Partition Consistency."  Lean: Partition Consistency
implies it, and Theorem `thm:complete-cap` holds with it. -/
theorem «def:response-partition-consistency/converse-part» (A : Table I O)
    (hAS : ∀ i o, A i o → sp.S i o) :
    (∀ Sys : System sp D, PartitionConsistencyAtEnd Sys → CommonRefinementAtEnd Sys) ∧
    ((∃ Sys : System sp D, AvailabilityFor A Sys ∧ CommonRefinementAtEnd Sys) ↔
      ConsistentOn sp A) :=
  ⟨fun _ h => commonRefinement_of_pc h, complete_cap_for_rpc sp D A hAS⟩

/-- "Confluence at `j` implies a common refinement at `j` (Corollary
`cor:reconciliation-any-basis`)."  Lean, at any cut, in particular the final
one. -/
theorem «def:response-partition-consistency/of-confluent» {init : Fin n → I}
    {H : History sp D n} {c : Fin n → Nat} {j : I} (h : ConfluentCut init H c j) :
    RPCAt H c j :=
  rpc_of_confluent h

/-- "for a canonical system (Definition `def:canonical-system`) the two
coincide by Lemma `lem:reconciliation`, applied to the participant runs."
Lean, at any cut, in particular the final one. -/
theorem «def:response-partition-consistency/canonical» {Sys : System sp D}
    (hS : CanonicalSystem Sys) {init : Fin n → I} {H : History sp D n} (hwf : WF init H)
    (hp : Produced Sys n init H) {c : Fin n → Nat} (hcut : IsCut H c) {j : I}
    (hj : ∀ p σ, LRun (canon sp (init p)) ((H p).take (c p)) σ → σ.cur ≼ j) :
    RPCAt H c j ↔ ConfluentCut init H c j :=
  canonical_rpc_iff_confluent hS hwf hp hcut hj

/-- "With other commitments the converse can fail: participants may prune
their states so that they cannot be reconciled while their emitted outputs
still have a common refinement."  Witness: `uSpec` (inputs `lo ≺ hi`, one output) and the
system `rnSys` whose basis is a commitment sealing `hi`; in the history `rnH`
the cut has RPC at `hi` but is not confluent there. -/
theorem «def:response-partition-consistency/converse-fails» :
    WF (fun _ => In2.lo) rnH ∧ Produced rnSys 2 (fun _ => In2.lo) rnH ∧
      Partitioned rnH (fun p => p.val) ∧ IsCut rnH (fun p => (rnH p).length) ∧
      (∀ p σ, LRun (canon uSpec ((fun _ => In2.lo) p)) ((rnH p).take (rnH p).length) σ →
        σ.cur ≼ In2.hi) ∧
      RPCAt rnH (fun p => (rnH p).length) .hi ∧
      ¬ ConfluentCut (fun _ => In2.lo) rnH (fun p => (rnH p).length) .hi :=
  rpc_not_confluent

/-! ### Replicated systems -/

/-- "A system is *replicated* (SPMD: every participant runs the same strategy)
when its obligation is uniform and every participant runs the same strategy,
which depends only on the participant's initial input and local history, and
not on its identity or the number of participants."

Lean: one relation `F` on (initial input, erased local history, erased
event), where erasing forgets the participant-set size in receives.
Uniformity of the obligation is expressed where it is used, by the obligation
`fun _ _ => Q.Q`. -/
theorem «app:cap-response/replicated» (Sys : System sp D) :
    Sys.Replicated ↔
      ∃ F : I → List (LEvN sp D) → LEvN sp D → Prop,
        ∀ n init p pre e, Sys.strat n init p pre e ↔ F (init p) (pre.map LEv.erase) e.erase :=
  Iff.rfl

/-! ### Lemma `lem:locality` -/

/-- **Lemma `lem:locality` (Locality).**  "For each of some participants `p`,
let `ℓ_p` be a local history that `p`'s strategy can produce from initial
input `i_p` and that contains no receive.  Placing each `ℓ_p` in its own
block, with at least two blocks and any further participants idle,
gives a partitioned history that the system produces.  If the system is
replicated, a receive-free local history that the strategy can produce for one
participant it can produce for any participant with the same initial input,
in any participant set."

Lean, first conjunct: any labelling with two distinct labels works (idle
participants have `L p = []`); "can produce" is compliance with `Allowed`
plus a legal run.  Second conjunct: `tr` re-indexes a receive-free local
history into participant set `Fin N`; it stays compliant, legal, receive-free,
and erases to the same participant-independent history. -/
theorem «lem:locality» :
    (∀ (Sys : System sp D) {n : Nat} {init : Fin n → I} (L : History sp D n)
        (comp : Fin n → Nat), (∃ p q, comp p ≠ comp q) →
        (∀ p q k j d, LEv.recv q k j d ∉ L p) →
        (∀ p, Compliant (Allowed Sys n init p) (L p)) →
        (∀ p, ∃ τ, LRun (canon sp (init p)) (L p) τ) →
        WF init L ∧ Produced Sys n init L ∧ Partitioned L comp ∧
          IsCut L (fun p => (L p).length)) ∧
    (∀ {Sys : System sp D}, Sys.Replicated → ∀ {m N : Nat} {init : Fin m → I}
        {init' : Fin N → I} {p : Fin m} {p' : Fin N}, init' p' = init p →
        ∀ {l : List (LEv sp D m)}, Compliant (Allowed Sys m init p) l →
        (∀ q k j d, LEv.recv q k j d ∉ l) → ∀ {τ : State sp},
        LRun (canon sp (init p)) l τ →
        Compliant (Allowed Sys N init' p') (l.map tr) ∧
          LRun (canon sp (init' p')) (l.map (tr (N := N))) τ ∧
          (∀ q k j d, LEv.recv q k j d ∉ l.map (tr (N := N))) ∧
          (l.map (tr (N := N))).map LEv.erase = l.map LEv.erase) :=
  ⟨fun Sys _ _ L comp h2 hnr hc hr => locality_glue Sys L comp h2 hnr hc hr,
   fun hrep _ _ _ _ _ _ hi _ hc hnr _ hrun => locality_transfer hrep hi hc hnr hrun⟩

/-! ## Response interfaces

### Definition `def:response-interface` -/

/-- **Def. `def:response-interface`** (Response interface,
self-continuing): "For a uniform
obligation `Q`, a response interface is an explicit relation `T ⊆ Q`
that is total on `I` and self-continuing: if `(i,o) ∈ T` and `i ⪯ j`, then
some `u ∈ T(j)` refines `o`." -/
theorem «def:response-interface» (Q : Obligation sp) (T : Table I O) :
    ResponseInterface Q T ↔
      (∀ i o, T i o → Q.Q i o) ∧ (∀ i, ∃ o, T i o) ∧
      ∀ i o j, T i o → i ≼ j → ∃ u, T j u ∧ o ≼ u :=
  Iff.rfl

/-- "Lifted Monotonicity for `T` is that of Definition `def:lm-for-A`, and
the reconciling output may lie outside `T`."  Lean: the same `ConsistentOn`
as in Theorem `thm:complete-cap`; finite families of rows are lists. -/
theorem «def:response-interface/lm-for-T» (T : Table I O) :
    ConsistentOn sp T ↔
      ∀ rows : List (I × O), (∀ r ∈ rows, T r.1 r.2) →
        ∀ j, (∀ r ∈ rows, r.1 ≼ j) → ∃ u, sp.S j u ∧ ∀ r ∈ rows, r.2 ≼ u :=
  Iff.rfl

/-- "With `T = S` it is the common-expansion condition of Proposition
`prop:common-expansion-form`." -/
theorem «def:response-interface/T-eq-S» : ConsistentOn sp sp.S ↔ sp.CommonExpansion :=
  consistentOn_S

/-- "and by Lemma `lem:reconciliation` it is confluence of the canonical runs
whose emitted rows lie in `T`."  Lean: a family of canonical executions
`x.2.1` from `σ_S(x.1)` to `x.2.2`, with emitted rows in `T`; `T` is assumed
contained in `S`. -/
theorem «def:response-interface/confluence» (T : Table I O) (hTS : ∀ i o, T i o → sp.S i o) :
    ConsistentOn sp T ↔
      ∀ fam : List (I × List (Event I O) × State sp),
        (∀ x ∈ fam, Exec (canon sp x.1) x.2.1 x.2.2 ∧ ∀ r ∈ emRows x.1 x.2.1, T r.1 r.2) →
        ∀ j, (∀ x ∈ fam, x.2.2.cur ≼ j) → ConfluentAt (fam.map (fun x => x.2.2)) j :=
  consistentOn_iff_confluent T hTS

/-- "A response interface is an explicit relation that a system can always
serve.  Consider the system of the proof of Theorem `thm:complete-cap` for
`E = T` … So every participant's fiber intersects `T`, and Availability for
`T` gives Answering.  The same argument at an input `k ⪰ i` leaves a row at `k`,
which gives Input acceptance."  Lean: `respSystem T` has Availability for
`T`; at the end of every history it produces, each participant's current
fiber intersects `T`; hence Answering; and full Response Availability. -/
theorem «app:cap-response/serve-interface» (Q : Obligation sp) (T : Table I O)
    (hT : ResponseInterface Q T) :
    AvailabilityFor T (respSystem (sp := sp) (D := D) T) ∧
    (∀ (n : Nat) (init : Fin n → I) (H : History sp D n),
      Produced (respSystem (sp := sp) (D := D) T) n init H →
      ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) (H p) σ →
      ∃ o, σ.R σ.cur o ∧ T σ.cur o) ∧
    AnsweringEnd (respSystem (sp := sp) (D := D) T) (fun _ _ => Q.Q) ∧
    ResponseAvailabilityEnd (respSystem (sp := sp) (D := D) T) (fun _ _ => Q.Q) :=
  ⟨availabilityFor_resp T,
   fun _ _ _ hp _ _ hσ => resp_fiber_meets T (fun i o h => Q.sub i o (hT.1 i o h))
     hT.2.1 hT.2.2 hp hσ,
   respSystem_answering Q T hT,
   (responseAvailability_iff_end _ _).1 (respSystem_RA Q T hT)⟩

/-! ### Theorem `thm:complete-cap-response` -/

/-- **Theorem `thm:complete-cap-response` (Complete CAP with chosen responses).**
"For an ordered relational specification `S` and a uniform obligation `Q`,
the following are equivalent: (1) some replicated system has Response
Availability for `Q` and Response Partition Consistency; (2) `S` satisfies
Lifted Monotonicity for some response interface `T ⊆ Q`; (3) for some response interface
`T ⊆ Q`, some system has Availability for `T` and Partition Consistency."

Lean: (1) is `ResponseForm sp D Q`, written out. -/
theorem «thm:complete-cap-response» (sp : Spec I O) (D : Type) (Q : Obligation sp) :
    ((∃ Sys : System sp D, Sys.Replicated ∧ ResponseAvailabilityEnd Sys (fun _ _ => Q.Q) ∧
        CommonRefinementAtEnd Sys) ↔
      ∃ T, ResponseInterface Q T ∧ ConsistentOn sp T) ∧
    ((∃ T, ResponseInterface Q T ∧ ConsistentOn sp T) ↔
      ∃ T, ResponseInterface Q T ∧
        ∃ Sys : System sp D, AvailabilityFor T Sys ∧ PartitionConsistencyAtEnd Sys) :=
  ⟨complete_cap_response_end sp D Q, response_form_iff_chosen sp D Q⟩

/-- Proof of Theorem `thm:complete-cap-response`, (2⇒1): "Take the system of
the proof of Theorem `thm:complete-cap` for `E = T`.  It is replicated, and
… has Answering and Input acceptance. … Lifted Monotonicity for `T` gives Response
Partition Consistency."  Lean: `respSystem T`. -/
theorem «thm:complete-cap-response/proof-sufficiency» (Q : Obligation sp) (T : Table I O)
    (hT : ResponseInterface Q T) (hc : ConsistentOn sp T) :
    (respSystem (sp := sp) (D := D) T).Replicated ∧
    ResponseAvailabilityEnd (respSystem (sp := sp) (D := D) T) (fun _ _ => Q.Q) ∧
    CommonRefinementAtEnd (respSystem (sp := sp) (D := D) T) :=
  let h := response_sufficient (D := D) Q T hT hc
  ⟨h.1, (responseAvailability_iff_end _ _).1 h.2.1, (responsePC_iff_commonRefinement _).1 h.2.2⟩

/-! ### Remark "Without replication" -/

/-- **Remark "Without replication"**: "For a system that is not replicated,
fix the participant set.  The same proof, with `T_p` built from `p`'s
isolated emissions, gives one response interface `T_p ⊆ Q_p` per participant.
If moreover each strategy depends on the initial inputs only through its own
participant's, then, since each participant is replayed once, consistency is
required only for families that draw on each `T_p` at most once."

Lean: participant set `Fin n` with `n ≥ 2`; `Tp Sys Q n p` is the set of rows
of `Q_p` emitted by `p` in isolated emissions.  First conjunct: each `T_p` is
contained in `Q_p`, total and self-continuing (from Response Availability).
Second conjunct (from Response Partition Consistency and `LocalInit`): a
family drawing row `r p` from `T_p` for the participants `p` in `A` has a
common refinement at every common expansion `j`. -/
theorem «app:cap-response/without-replication» (Sys : System sp D)
    (Q : (n : Nat) → Fin n → Table I O) {n : Nat} (h2 : 2 ≤ n) :
    (ResponseAvailabilityEnd Sys Q → ∀ p : Fin n,
      (∀ i o, Tp Sys Q n p i o → Q n p i o) ∧ (∀ i, ∃ o, Tp Sys Q n p i o) ∧
      ∀ i o j, Tp Sys Q n p i o → i ≼ j → ∃ u, Tp Sys Q n p j u ∧ o ≼ u) ∧
    (CommonRefinementAtEnd Sys → LocalInit Sys →
      ∀ (A : Fin n → Prop) (r : Fin n → I × O),
        (∀ p, A p → Tp Sys Q n p (r p).1 (r p).2) →
        ∀ j : I, (∀ p, A p → (r p).1 ≼ j) → ∃ u, sp.S j u ∧ ∀ p, A p → (r p).2 ≼ u) :=
  ⟨fun hRA p => without_replication_interface Sys Q ((responseAvailability_iff_end Sys Q).2 hRA) h2 p,
   fun hRPC hloc A r hr j hj => without_replication Sys Q
     ((responsePC_iff_commonRefinement Sys).2 hRPC) hloc h2 A r hr j hj⟩

/-- The `LocalInit` hypothesis ("each strategy depends on the initial inputs
only through its own participant's") is needed: the non-replicated system
`mixSys` has Response Availability and Response Partition Consistency, yet
the rows `(lo, b) ∈ T₀` and `(lo, a) ∈ T₁`, drawing on each `T_p` once, have
no common refinement at any input. -/
theorem «app:cap-response/without-replication/local-init-needed» :
    ResponseAvailabilityEnd mixSys (fun _ _ => Q4.Q) ∧ CommonRefinementAtEnd mixSys ∧
    Tp mixSys (fun _ _ => Q4.Q) 2 0 .lo .b ∧ Tp mixSys (fun _ _ => Q4.Q) 2 1 .lo .a ∧
    ∀ j u, sp4.S j u → ¬ (O4.b ≼ u ∧ O4.a ≼ u) :=
  let h := without_replication_counterexample
  ⟨(responseAvailability_iff_end _ _).1 h.1, (responsePC_iff_commonRefinement _).1 h.2.1, h.2.2⟩

/-! ## Choosing versus requiring every output -/

/-- "Theorem `thm:complete-cap` with `E = S` requires every permitted output
to stay available; Theorem `thm:complete-cap-response` lets the system choose
which outputs to serve.  Lifted Monotonicity implies the conditions of that
theorem for every uniform
obligation, with `T = Q`." -/
theorem «app:cap-response/lm-implies-response-form» (Q : Obligation sp) (h : sp.LiftedMono) :
    (ResponseInterface Q Q.Q ∧ ConsistentOn sp Q.Q) ∧ ResponseForm sp D Q :=
  ⟨lm_response_interface Q h, (responseForm_iff_cuts sp D Q).2 (lm_response_form Q h)⟩

/-- "The converse fails.  Let `I = {0,1}` with `0 ≺ 1`, `⊥ ≺ a` and `⊥ ≺ b`
with `a, b` incomparable, `S(0) = {⊥, a}`, `S(1) = {b}`, and `Q = S`.  Lifted
Monotonicity fails at `(0,a)`, but `S` satisfies Lifted Monotonicity for the response interface
`{(0,⊥),(1,b)}`: a system that answers `⊥` at `0` never emits the output that
conflicts with `b`."  Lean: `cxSpec` on `In2 = {lo ≺ hi}` and
`O3 = {bot, a, b}`, `cxQ = S`, `cxT = {(lo,bot),(hi,b)}`; second conjunct: the
system-level form (the conditions of Theorem `thm:complete-cap-response` hold; no system has Availability and
Partition Consistency). -/
theorem «app:cap-response/converse-fails» (D : Type) :
    (¬ cxSpec.LiftedMono ∧ ResponseInterface cxQ cxT ∧ ConsistentOn cxSpec cxT) ∧
    (ResponseForm cxSpec D cxQ ∧
      ¬ ∃ Sys : System cxSpec D, AvailabilityAtEnd Sys ∧ PartitionConsistencyAtEnd Sys) :=
  ⟨converse_counterexample,
   (responseForm_iff_cuts _ _ _).2 (converse_counterexample_systems D).1,
   fun ⟨Sys, hA, hP⟩ => (converse_counterexample_systems D).2
     ⟨Sys, (availability_iff_atEnd _).2 hA, (partitionConsistency_iff_atEnd _).2 hP⟩⟩

/-- "For a functional specification the two coincide: a total `T ⊆ Q ⊆ S`
equals `S`, and both self-continuation and Lifted Monotonicity for `S` are
monotonicity."  First conjunct: at the level of interfaces; second: at the
level of systems (the conditions of Theorem `thm:complete-cap-response` ⇔ Availability and Partition
Consistency). -/
theorem «app:cap-response/functional-coincide» (hf : sp.Functional) (Q : Obligation sp) :
    ((∃ T, ResponseInterface Q T ∧ ConsistentOn sp T) ↔ sp.LiftedMono) ∧
    (ResponseForm sp D Q ↔
      (∃ Sys : System sp D, AvailabilityAtEnd Sys ∧ PartitionConsistencyAtEnd Sys)) := by
  refine ⟨functional_response_iff hf Q, ?_⟩
  rw [responseForm_iff_cuts, functional_forms_coincide hf Q]
  constructor
  · rintro ⟨Sys, hA, hP⟩
    exact ⟨Sys, (availability_iff_atEnd _).1 hA, (partitionConsistency_iff_atEnd _).1 hP⟩
  · rintro ⟨Sys, hA, hP⟩
    exact ⟨Sys, (availability_iff_atEnd _).2 hA, (partitionConsistency_iff_atEnd _).2 hP⟩

/-- "A total `T ⊆ Q` that satisfies Lifted Monotonicity as a specification is
a response interface for which `S` satisfies Lifted Monotonicity". -/
theorem «app:cap-response/lm-subspec» (Q : Obligation sp) (T : Spec I O)
    (hTQ : ∀ i o, T.S i o → Q.Q i o) (h : T.LiftedMono) :
    ResponseInterface Q T.S ∧ ConsistentOn sp T.S :=
  subspec_lm_interface Q T hTQ h

/-- "… but the condition is weaker."  The five-input example: `I = {i₁, i₂,
j, k₁, k₂}` (`sp5`, `Q5 = S`), `T = {(i₁,a),(i₂,b),(j,c₁),(j,c₂),(k₁,e₁),
(k₂,e₂)}` (`T5`) is a response interface for which `S` satisfies Lifted Monotonicity, but no
sub-specification of `Q` satisfies Lifted Monotonicity. -/
theorem «app:cap-response/subspec-weaker» :
    (ResponseInterface Q5 T5 ∧ ConsistentOn sp5 T5) ∧
    ∀ T' : Spec I5 O8, (∀ i o, T'.S i o → Q5.Q i o) → ¬ T'.LiftedMono :=
  subspec_counterexample

/-- "Reconciling outputs need not lie in `T`: a participant that emits `d₁` or
`d₂` seals `k₂` or `k₁`."  Lean: after any run emitting `d₁` no row at `k₂`
remains, and symmetrically. -/
theorem «app:cap-response/subspec-seals» {D : Type} {n : Nat} {σ τ : State sp5}
    {l : List (LEv sp5 D n)} (h : LRun σ l τ) {γ : List (Commitment sp5)} :
    (LEv.out γ .d1 ∈ l → ∀ u, ¬ τ.R .k2 u) ∧ (LEv.out γ .d2 ∈ l → ∀ u, ¬ τ.R .k1 u) :=
  ⟨fun hm u => emit_d1_seals_k2 h hm u, fun hm u => emit_d2_seals_k1 h hm u⟩

/-! ## Gilbert–Lynch with real-time precedence

"Section `sec:complete-cap` derives the Gilbert–Lynch theorem from the
converse of Theorem `thm:complete-cap`, with real-time precedence supplied as
input.  Here precedence comes from real time, and consistency is required
only at the precedence an execution realizes."  (The §4.5 derivation is
`«sec:complete-cap/gilbert-lynch»` in `Paper/S4_5_CompleteCAP.lean`.)

### Lemma `lem:forced-answer` -/

/-- **Lemma `lem:forced-answer` (Forced answer).**  "Let `i ⪯ j`, and suppose
no output in `Q_q(i)` has a refinement in `S(j)`.  In a system with Answering
for `(Q_p)`, consider a partitioned history that the system produces, in which
`q` is alone in its block, `q`'s current input is `i`, and `j` expands
every participant's current input.  Then some continuation within `q`'s
block that adds only history events of `q`, and no input event, has emitted
outputs with no common refinement in `S(j)`."

Lean: `i` is `σq.cur`; "`q` alone" is `halone`; `i ⪯ j` follows from `hj`.
The continuation keeps `j` above every current input. -/
theorem «lem:forced-answer» (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O)
    (hAns : AnsweringEnd Sys Q) {init : Fin n → I} {H : History sp D n}
    {comp : Fin n → Nat} (hwf : WF init H) (hprod : Produced Sys n init H)
    (hpart : Partitioned H comp) {q : Fin n}
    (halone : ∀ p, comp p = comp q → p = q) {σq : State sp}
    (hσq : LRun (canon sp (init q)) (H q) σq) {j : I}
    (hj : ∀ p σ, LRun (canon sp (init p)) (H p) σ → σ.cur ≼ j)
    (hno : ∀ o, Q n q σq.cur o → ¬ ∃ u, sp.S j u ∧ o ≼ u) :
    ∃ ext : Fin n → List (LEv sp D n),
      WF init (fun p => H p ++ ext p) ∧ Produced Sys n init (fun p => H p ++ ext p) ∧
      Partitioned (fun p => H p ++ ext p) comp ∧
      (∀ p, p ≠ q → ext p = []) ∧ (∀ p j, LEv.inp j ∉ ext p) ∧
      (∀ p σ, LRun (canon sp (init p)) (H p ++ ext p) σ → σ.cur ≼ j) ∧
      ¬ ∃ u, sp.S j u ∧ ∀ p γ o, LEv.out γ o ∈ H p ++ ext p → o ≼ u :=
  forced_answer_end Sys Q hAns hwf hprod hpart halone hσq hj hno

/-! ### Paragraph "The register"

Lean model (`CAP/Register.lean`, namespace `CC.GL`): an input `Hist` is a
finite map from operation ids to operations (replica, read / write `v`) with a
strict partial order `prec` of real-time precedence; expansion is inclusion of
operations and edges.  An output `RMap` is a response map, ordered by
extension.  "Real-time precedence belongs to the input …" is a modeling
remark, reflected in `prec` being part of `Hist`. -/

/-- "The fiber `S(h)` contains the maps explained by some linearization of
`h`, a total order of its operations extending precedence in which each
answered read returns the last preceding write, or the initial value `v₀`."
Lean: a linearization is a position function injective on `h`'s operations
and increasing along `prec`. -/
theorem «app:cap-response/register-fiber» (h : CC.GL.Hist) (ρ : CC.GL.RMap) :
    CC.GL.regSpec.S h ρ ↔ ∃ pos, CC.GL.Lin h pos ∧ CC.GL.Explains h pos ρ :=
  Iff.rfl

/-- "The obligation `Q_p(h)` consists of the maps in `S(h)` that answer every
read and acknowledge every write invoked at `p`." -/
theorem «app:cap-response/register-obligation-def» (p : Nat) (h : CC.GL.Hist) (ρ : CC.GL.RMap) :
    CC.GL.regQ p h ρ ↔
      CC.GL.regS h ρ ∧ ∀ a op, h.ops a = some op → op.rep = p → ρ.f a ≠ none :=
  Iff.rfl

/-- "Every finite history has a linearization, so `Q_p` is total, and it is
upward closed within fibers."  Lean: linearizations exist; `Q_p ⊆ S`, total,
upward closed (Def. `def:response-obligation`). -/
theorem «app:cap-response/register-obligation» (p : Nat) :
    (∀ h : CC.GL.Hist, ∃ pos, CC.GL.Lin h pos) ∧
    (∀ h ρ, CC.GL.regQ p h ρ → CC.GL.regS h ρ) ∧ (∀ h, ∃ ρ, CC.GL.regQ p h ρ) ∧
    ∀ h ρ u, CC.GL.regQ p h ρ → CC.GL.regS h u → ρ ≼ u → CC.GL.regQ p h u :=
  ⟨CC.GL.lin_exists, regQ_obligation p⟩

/-! ### Interleavings and realized histories -/

/-- "Real time is the order of history events in an execution: an
*interleaving* `λ` of a distributed history is a linear order of its history
events consistent with happens-before".  Lean: an injective position function
on events, increasing along each local order and along send→receive edges. -/
theorem «app:cap-response/interleaving» (H : CC.GL.RHist D n) (pos : Fin n → Nat → Nat) :
    CC.GL.Interleaving H pos ↔
      (∀ p k p' k', k < (H p).length → k' < (H p').length → pos p k = pos p' k' →
        p = p' ∧ k = k') ∧
      (∀ p k k', k < k' → k' < (H p).length → pos p k < pos p k') ∧
      (∀ p k q k' j d, (H p)[k]? = some (LEv.recv q k' j d : LEv CC.GL.regSpec D n) →
        pos q k' < pos p k) :=
  Iff.rfl

/-- "For a prefix `C` of `λ` (a consistent cut), the *realized history* `h_C`
contains the operations invoked in `C`, with an edge from `a` to `b` when
`a`'s response precedes `b`'s invocation in `λ`."  Lean: the prefix is the
events of position `< m`; invocations / responses are `IsInv` / `IsResp`
(input / output events at the operation's replica containing / answering it);
"precedes `b`'s invocation" (its first one) is "precedes every invocation of
`b`". -/
theorem «app:cap-response/realized-history» (H : CC.GL.RHist D n) (pos : Fin n → Nat → Nat)
    (m : Nat) (j : CC.GL.Hist) :
    CC.GL.Realized H pos m j ↔
      (∀ a op, j.ops a = some op ↔ ∃ p k, pos p k < m ∧ CC.GL.IsInv H a op p k) ∧
      (∀ a b, j.prec a b ↔ ∃ opa opb, j.ops a = some opa ∧ j.ops b = some opb ∧
        ∃ p k, CC.GL.IsResp H a opa p k ∧ ∀ p' k', CC.GL.IsInv H b opb p' k' → pos p k < pos p' k') :=
  Iff.rfl

/-- "If `C' ⊆ C` is also a prefix, `h_C` expands `h_{C'}`." -/
theorem «app:cap-response/realized-mono» {H : CC.GL.RHist D n} {pos : Fin n → Nat → Nat}
    {m m' : Nat} {j j' : CC.GL.Hist} (hm : m' ≤ m) (h' : CC.GL.Realized H pos m' j')
    (h : CC.GL.Realized H pos m j) : j' ≼ j :=
  CC.GL.realized_mono hm h' h

/-- "The realized history need not be a common expansion of the participants'
current inputs: an input event may introduce two operations with an edge
between them before either responds." -/
theorem «app:cap-response/realized-not-expansion» (Sys : System CC.GL.regSpec D) :
    ∃ (init : Fin 2 → CC.GL.Hist) (H : CC.GL.RHist D 2) (comp : Fin 2 → Nat)
      (pos : Fin 2 → Nat → Nat) (m : Nat) (c : Fin 2 → Nat) (j : CC.GL.Hist),
      WF init H ∧ Produced Sys 2 init H ∧ Partitioned H comp ∧ CC.GL.Interleaving H pos ∧
      CC.GL.PrefixCut H pos m c ∧ CC.GL.Realized H pos m j ∧
      ∃ σ : State CC.GL.regSpec, LRun (canon CC.GL.regSpec (init 0)) ((H 0).take (c 0)) σ ∧
        ¬ σ.cur ≼ j :=
  CC.GL.realized_not_expansion Sys

/-! ### Client histories -/

/-- "A *client history* has two participants with empty initial inputs, and
each of its input events adds one operation, invoked at its participant after
all of that participant's earlier operations are answered."  Lean: histories
over `Fin 2`, used with initial inputs `init0 = fun _ => ∅`; `ClientLocal`
encodes the input discipline per participant. -/
theorem «app:cap-response/client-history» (H : CC.GL.RHist D 2) :
    CC.AsyncGL.ClientH H ↔ ∀ p : Fin 2, CC.AsyncGL.ClientLocal p.val (H p) :=
  Iff.rfl

/-! ### Corollary `cor:gilbert-lynch` -/

/-- **Corollary `cor:gilbert-lynch` (Gilbert–Lynch).**  "No system for the
linearizable register has Answering for `(Q_p)` together with the following,
both required only of client histories: for every partitioned client history
it produces, interleaving `λ`, and prefix `C` of `λ` such that `h_C` is a
common expansion of the current inputs at `C`, the outputs emitted in `C`
have a common refinement in `S(h_C)`."

Lean: `AnsweringCEnd` is Answering for `Q_p = regQ p` at the end of client
histories; `RealizedRPCC` is the second hypothesis.  Both are written out
below. -/
theorem «cor:gilbert-lynch» (Sys : System CC.GL.regSpec D) :
    ¬ (CC.AsyncGL.AnsweringCEnd Sys ∧ CC.AsyncGL.RealizedRPCC Sys) :=
  CC.AsyncGL.gilbert_lynch_client_end Sys

/-- The two hypotheses of Corollary `cor:gilbert-lynch`, unfolded; Answering
at the end of client histories is equivalent to its cut form `AnsweringC`
(cuts of client histories are client histories). -/
theorem «cor:gilbert-lynch/hypotheses» (Sys : System CC.GL.regSpec D) :
    (CC.AsyncGL.AnsweringCEnd Sys ↔
      ∀ (H : CC.GL.RHist D 2) (comp : Fin 2 → Nat), WF CC.AsyncGL.init0 H →
        Produced Sys 2 CC.AsyncGL.init0 H → Partitioned H comp → CC.AsyncGL.ClientH H →
        ∀ (p : Fin 2) (σ : State CC.GL.regSpec),
          LRun (canon CC.GL.regSpec (CC.AsyncGL.init0 p)) (H p) σ →
          ∃ ext : Fin 2 → List (LEv CC.GL.regSpec D 2),
            WF CC.AsyncGL.init0 (fun q => H q ++ ext q) ∧
            Produced Sys 2 CC.AsyncGL.init0 (fun q => H q ++ ext q) ∧
            Partitioned (fun q => H q ++ ext q) comp ∧ (∀ q, comp q ≠ comp p → ext q = []) ∧
            (∀ j, LEv.inp j ∉ ext p) ∧ ∃ γ o, CC.GL.regQ p.val σ.cur o ∧ LEv.out γ o ∈ ext p) ∧
    (CC.AsyncGL.AnsweringC Sys ↔ CC.AsyncGL.AnsweringCEnd Sys) ∧
    (CC.AsyncGL.RealizedRPCC Sys ↔
      ∀ (H : CC.GL.RHist D 2) (comp : Fin 2 → Nat), WF CC.AsyncGL.init0 H →
        Produced Sys 2 CC.AsyncGL.init0 H → Partitioned H comp → CC.AsyncGL.ClientH H →
        ∀ pos, CC.GL.Interleaving H pos → ∀ m c, CC.GL.PrefixCut H pos m c →
        ∀ j, CC.GL.Realized H pos m j →
        (∀ p σ, LRun (canon CC.GL.regSpec (CC.AsyncGL.init0 p)) ((H p).take (c p)) σ →
          σ.cur ≼ j) →
        RPCAt H c j) :=
  ⟨Iff.rfl, CC.AsyncGL.answeringC_iff_end Sys, Iff.rfl⟩

/-- Proof of Corollary `cor:gilbert-lynch`, along the paper's route through
Lemma `lem:forced-answer` (here with the hypotheses required of all
histories, not only client histories). -/
theorem «cor:gilbert-lynch/via-forced-answer» (Sys : System CC.GL.regSpec D) :
    ¬ (Answering Sys CC.GL.regQn ∧ CC.GL.RealizedRPC Sys) :=
  gilbert_lynch_answering Sys

/-- "A system with Response Availability, and with a common refinement at
`h_C` for every prefix `C` of every partitioned history, satisfies these
hypotheses, so the corollary excludes it too."  Lean: the implications, the
resulting impossibility, and the variant with full Response Partition
Consistency. -/
theorem «cor:gilbert-lynch/also-excludes» (Sys : System CC.GL.regSpec D) :
    (ResponseAvailabilityEnd Sys CC.GL.regQn → CC.AsyncGL.AnsweringCEnd Sys) ∧
    (CC.GL.RealizedRPC Sys → CC.AsyncGL.RealizedRPCC Sys) ∧
    ¬ (ResponseAvailabilityEnd Sys CC.GL.regQn ∧ CC.GL.RealizedRPC Sys) ∧
    ¬ (ResponseAvailabilityEnd Sys CC.GL.regQn ∧ CommonRefinementAtEnd Sys) :=
  ⟨CC.AsyncGL.answeringCEnd_of_RAEnd, CC.AsyncGL.realizedRPCC_of,
   fun ⟨h1, h2⟩ => CC.GL.gilbert_lynch Sys ⟨(responseAvailability_iff_end _ _).2 h1, h2⟩,
   fun ⟨h1, h2⟩ => CC.GL.gilbert_lynch_full Sys
     ⟨(responseAvailability_iff_end _ _).2 h1, (responsePC_iff_commonRefinement _).2 h2⟩⟩

/-! "The register's obligation differs by replica, so
Theorem `thm:complete-cap-response` does not apply as stated."  (Remark; in
Lean the obligation `CC.GL.regQn n p = regQ p.val` depends on `p`, while the
theorem takes `fun _ _ => Q.Q`.) -/

/-- (Section `sec:complete-cap`, repeated here for reference.)  "a single
emitted output has no refinement in the fiber at some expansion of its input,
a failure of Relational Monotonicity." -/
theorem «cor:gilbert-lynch/not-relMono» : ¬ CC.GL.regSpec.RelMono :=
  reg_not_relMono

/-! ### Proposition `prop:gl-async`

Lean model (`CAP/AsyncGilbertLynch.lean`, namespace `CC.AsyncGL`): `Alg N M`
is one input-enabled nondeterministic state machine per node `Fin N` over
invocations, responses, sends and receives (`M` the message type);
`IsGExec A E` says that the timed traces `E` form an execution of `A`
(messages may be lost); `ClientWF E` is client well-formedness. -/

/-- Prop. `prop:gl-async`, "available (a request pending at a node is answered
in some extension of the execution that adds no request and loses every
message)". -/
theorem «prop:gl-async/available» {N : Nat} {M : Type} (A : CC.AsyncGL.Alg N M) :
    CC.AsyncGL.Available A ↔
      ∀ E, CC.AsyncGL.IsGExec A E → CC.AsyncGL.ClientWF E →
        ∀ i T a kd, (T, CC.AsyncGL.Act.inv a kd) ∈ E.tr i →
        (∀ T' r, (T', CC.AsyncGL.Act.resp a r) ∉ E.tr i) →
        ∃ E', CC.AsyncGL.IsGExec A E' ∧
          (∀ j, ∃ β, E'.tr j = E.tr j ++ β ∧ ∀ y ∈ β, (∀ j' x, x ∈ E.tr j' → x.1 < y.1) ∧
            (∀ a k, y.2 ≠ CC.AsyncGL.Act.inv a k) ∧ (∀ s m, y.2 ≠ CC.AsyncGL.Act.recv s m)) ∧
          ∃ T' r, (T', CC.AsyncGL.Act.resp a r) ∈ E'.tr i :=
  Iff.rfl

/-- Prop. `prop:gl-async`, "atomic (every execution with well-formed clients
has a linearization)"; `AtomicExec` is Lynch's atomicity of one execution. -/
theorem «prop:gl-async/atomic» {N : Nat} {M : Type} (A : CC.AsyncGL.Alg N M) :
    CC.AsyncGL.Atomic A ↔
      ∀ E, CC.AsyncGL.IsGExec A E → CC.AsyncGL.ClientWF E → CC.AsyncGL.AtomicExec E :=
  Iff.rfl

/-- **Proposition `prop:gl-async` (Gilbert–Lynch, asynchronous model).**  "In
the asynchronous network model with at least two nodes, no algorithm for a
read/write register is both available … and atomic …." -/
theorem «prop:gl-async» {N : Nat} {M : Type} (hN : 2 ≤ N) (A : CC.AsyncGL.Alg N M) :
    ¬ (CC.AsyncGL.Available A ∧ CC.AsyncGL.Atomic A) :=
  CC.AsyncGL.gilbert_lynch_async hN A

/-- Proof sketch of Prop. `prop:gl-async`: "Translate the algorithm into a
system with the canonical basis.  …  Availability, applied to each unanswered
operation of the view, gives Answering.  …  atomicity gives a common
refinement in `S(h_C)`.  The corollary excludes the algorithm."  Lean: the
translation `sysOf A` satisfies both client-form hypotheses. -/
theorem «prop:gl-async/proof» {N : Nat} {M : Type} (hN : 2 ≤ N) (A : CC.AsyncGL.Alg N M) :
    (CC.AsyncGL.Atomic A → CC.AsyncGL.Available A →
      CC.AsyncGL.AnsweringCEnd (CC.AsyncGL.sysOf A)) ∧
    (CC.AsyncGL.Atomic A → CC.AsyncGL.RealizedRPCC (CC.AsyncGL.sysOf A)) :=
  ⟨fun hat hav => (CC.AsyncGL.answeringC_iff_end _).1 (CC.AsyncGL.sys_answering hN A hat hav),
   fun hat => CC.AsyncGL.sys_rpc hN A hat⟩

/-- Proof sketch of Prop. `prop:gl-async`: "atomicity of that execution puts
the map in the fiber at the view, so the output events are legal."  Lean: in
a run of node `i` alone (no receipts, fresh ids, well-formed client), its
response map lies in the register fiber at its view. -/
theorem «prop:gl-async/atomic-view» {N : Nat} {M : Type} {A : CC.AsyncGL.Alg N M}
    (hat : CC.AsyncGL.Atomic A) {i : Fin N} {t : List (Nat × CC.AsyncGL.Act N M)}
    (hrun : ∃ s, CC.AsyncGL.NRun A i (A.start i) (CC.AsyncGL.acts t) s)
    (hpw : t.Pairwise (fun x y => x.1 < y.1))
    (hnr : ∀ x ∈ t, ∀ s m, x.2 ≠ CC.AsyncGL.Act.recv s m)
    (hf : ∀ x ∈ t, ∀ y ∈ t, ∀ a k k', x.2 = CC.AsyncGL.Act.inv a k →
      y.2 = CC.AsyncGL.Act.inv a k' → x = y)
    (halt : ∀ T a k T' b k', (T, CC.AsyncGL.Act.inv a k) ∈ t →
      (T', CC.AsyncGL.Act.inv b k') ∈ t → T' < T →
      ∃ T'' r, T'' < T ∧ (T'', CC.AsyncGL.Act.resp b r) ∈ t) :
    CC.GL.regS (CC.AsyncGL.viewOf i.val (CC.AsyncGL.acts t)) (CC.AsyncGL.rmap (CC.AsyncGL.acts t)) :=
  CC.AsyncGL.atomic_view hat hrun hpw hnr hf halt

/-- Non-vacuity (not a claim of the paper): each property alone is
satisfiable — the silent algorithm is atomic, the eager one available. -/
theorem «prop:gl-async/non-vacuity» {N : Nat} {M : Type} :
    CC.AsyncGL.Atomic (CC.AsyncGL.silentAlg N M) ∧ CC.AsyncGL.Available (CC.AsyncGL.eagerAlg N M) :=
  ⟨CC.AsyncGL.silent_atomic, CC.AsyncGL.eager_available⟩

/-! ### Final paragraph (fair executions)

"Gilbert and Lynch require availability and atomicity in all fair executions,
… Both imply the forms in the proposition. … a finite execution extends to a
fair execution with no new request in which every message is lost; …
Atomicity of the fair extension gives atomicity of the finite execution, since
atomicity is a safety property …"

Prose only: infinite (fair) executions are not modeled.  The Lean
`Available` and `Atomic` are the finite forms of the proposition, so the
step from Gilbert–Lynch's fair-execution notions to these forms is argued in
the paper, not formalized. -/

end CC.Paper
