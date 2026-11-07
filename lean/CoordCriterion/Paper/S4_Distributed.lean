import CoordCriterion.Distributed.Systems
import CoordCriterion.CALM.TransientConflict
import CoordCriterion.Figures
import CoordCriterion.CAP.Coordination
import CoordCriterion.CAP.TwoPhaseCommit
import CoordCriterion.CAP.TimeoutAbort
import CoordCriterion.Appendix.TransactionBases.NoReads
import CoordCriterion.Paper.AppG_TransactionBases
import CoordCriterion.Appendix.TransactionBases.CommitmentEvent
import CoordCriterion.Appendix.ComponentSystems
import CoordCriterion.Appendix.Deployment

/-!
# Paper §4.1–4.3: Distributed Execution (statement layer)

Covers `sections/distributed-histories.tex` (§4.1 Distributed histories, §4.2
Distributed consistency, with the paragraph *Message data*) and
`sections/distributed.tex` §4.3 Systems and canonical runs (it stops before
§4.4 The Complete CAP Theorem).  The paragraph *Exchanging outputs* and the
proofs of §4 are in Appendix B
(`Paper/AppB_ProofsDistributed.lean`).

How to read this file.  Read it side by side with the paper.  Entries appear in
paper order under headers named after the paper's subsections.  Each numbered
result is named by its LaTeX label (`«def:commitment»`,
…); an unlabeled claim of the text is named `«<enclosing label>/<slug>»`.  Each
docstring quotes the paper (LaTeX lightly turned into Unicode) and, where the
Lean statement reads differently, says how the two correspond.  Statements are
written out in full; the proofs are one-line references to the library
(`CoordCriterion/Distributed/*.lean`, `CAP/Model.lean`, `Figures.lean`,
`Appendix/TransactionBases/*.lean`), where the modeling choices are
documented.

Global reading conventions: sets are predicates, finite families are `List`s
or functions on `Fin n`, the participant set `P` is `Fin n`, `≼` is the
specification's order (`a ≼ b`: `b` extends `a`), a state `(i,R)` is a
`State sp` with `cur = i` and table `R`, and `R[out ⪰ o]` is `outputTable σ o`.
-/

namespace CC.Paper

open CC Classical

variable {I O : Type} [PO I] [PO O]

/-! ## Distributed histories (§4.1, `sec:histories`) -/

/-- **Def. `def:distributed-history`** (Distributed history, history event),
the carrier.  "A distributed history `H` is a finite set of history events,
each an occurrence at one participant of a specification event, `send(m)`,
or `receive(m)` …"

Lean: participants are `Fin n`; each participant has a finite `List` of local
events (`Dist.LEv`: `io e`, `send x m`, `recv x m` with a message identifier
`x` and a message `m = (j, d) : Option I × D`, `none` playing `∅`).  The list
order *is* item 1, the total local order.  The initial inputs `i_p` are
`H.init`.  "Commitment events are a third kind of specification event, so a
distributed history may contain them" (§4.2, after Def.
`def:commitment-event`); histories a system produces are modeled with them as
`CAP.LEv.commitment γ` in `CAP/Model.lean`, whose well-formedness includes them in
item 3. -/
abbrev «def:distributed-history» (I O D : Type) (n : Nat) := Dist.History I O D n

/-- Def. `def:distributed-history`, items 2–3: "for each receive, a matching
send of the same message at another participant, each send matching at most
one receive; and for each participant `p`, its specification events, in local
order, form a defined transition sequence from `σ_P(i_p)`".

Lean: `History.WF`.  "Each send matching at most one receive" is read as
"send identifiers are unique"; `CC.Dist.WF0` drops this (see
`«prop:distributed-consistency/literal-matching»`). -/
abbrev «def:distributed-history/well-formed» {D : Type} {n : Nat} (sp : Spec I O)
    (H : Dist.History I O D n) : Prop :=
  H.WF sp

/-- **Def. `def:happens-before`** (Happens-before).  "Happens-before is the
transitive closure of the local orders of a distributed history and of each
send preceding its matching receive." -/
abbrev «def:happens-before» {D : Type} {n : Nat}
    (H : Dist.History I O D n) : Dist.Pos n → Dist.Pos n → Prop :=
  H.HB

/-- **Def. `def:consistent-cut`** (Consistent cut).  "A consistent cut `C` is
a subset of history events closed under happens-before." -/
abbrev «def:consistent-cut» {D : Type} {n : Nat}
    (H : Dist.History I O D n) (C : Dist.Pos n → Prop) : Prop :=
  H.IsCut C

/-- "A consistent cut contains a prefix of each participant's history events,
so by item 3 it determines one run per participant."

Lean: (a) the cut is a prefix of length `c ≤ |H_p|` at each `p`; (b) an
endpoint exists; (c) it is unique.  Together these say "one run per
participant". -/
theorem «sec:histories/cut-determines-runs» {D : Type} {n : Nat} (sp : Spec I O)
    (H : Dist.History I O D n) (hW : H.WF sp) (C : Dist.Pos n → Prop) (hC : H.IsCut C) :
    (∀ p, ∃ c, c ≤ (H.ev p).length ∧ ∀ k, C (p, k) ↔ k < c) ∧
    (∃ σs : Fin n → State sp, H.Endpoint sp C σs) ∧
    (∀ σs σs' : Fin n → State sp, H.Endpoint sp C σs → H.Endpoint sp C σs' → σs = σs') :=
  ⟨hC.cut_prefix, Dist.History.endpoint_exists hW hC,
    fun _ _ => Dist.History.endpoint_unique⟩

/-- **Def. `def:participant-run`** (Participant run).  "At a consistent cut
`C`, the specification events of `C` at participant `p`, in local order, form
its participant run … whose final state we write `σ_p(C)`."

Lean: relational — `σs p` is the final state of `p`'s input/output events in
the cut (existence and uniqueness: `«sec:histories/cut-determines-runs»`). -/
abbrev «def:participant-run» {D : Type} {n : Nat} (sp : Spec I O)
    (H : Dist.History I O D n) (C : Dist.Pos n → Prop) (σs : Fin n → State sp) : Prop :=
  H.Endpoint sp C σs

/-- **Def. `def:endpoint`** (Endpoint).  "The endpoint of a consistent cut
`C` is `end(H,C) = (σ_p(C))_{p∈P}`."  Lean: `σs` is the family of final states
across participants, i.e. `H.Endpoint sp C σs`. -/
abbrev «def:endpoint» {D : Type} {n : Nat} (sp : Spec I O)
    (H : Dist.History I O D n) (C : Dist.Pos n → Prop) (σs : Fin n → State sp) : Prop :=
  H.Endpoint sp C σs

/-- Def. `def:participant-run`: a participant run is "a run (Definition run)". -/
theorem «def:participant-run/is-run» {D : Type} {n : Nat} {sp : Spec I O}
    {H : Dist.History I O D n} {C : Dist.Pos n → Prop} {σs : Fin n → State sp}
    (h : H.Endpoint sp C σs) : ∀ p, IsRun (σs p) :=
  h.isRun

/-- **Fig. participant-runs** (`fig:participant-runs`).  "Two histories
from `σ_a = σ_P(a··)` to `σ_1 = (ab·, R_1)` … In Figure participant-runs, the
input `ab·` reaches `q` directly or through a message from `p`.  The histories
differ, but at either cut each participant run is `input(ab·)`, so both
endpoints are `(σ_1, σ_1)`."

Lean, for the election `elec` and any message data `d`: the direct-delivery
history `H_d` and the forwarded-delivery history `H_f` (where `p = 0` sends
`m = (ab·, d)` and `q = 1` receives it) are both well formed, the endpoint of
each final cut is `(σ_P(ab·), σ_P(ab·))`, and the histories differ.  Here
`σ_1 = σ_P(ab·)`, whose table `R_1` is panel (b) of Fig. election-frames
(`CC.Figures.Elec.panel_b`). -/
theorem «fig:participant-runs» (D : Type) (d : D) :
    (Dist.Hd CALM.Res D CALM.bad CALM.bab).WF CALM.elec ∧
    (Dist.Hf CALM.Res CALM.bad CALM.bab d).WF CALM.elec ∧
    (Dist.Hd CALM.Res D CALM.bad CALM.bab).Endpoint CALM.elec
      (Dist.Hd CALM.Res D CALM.bad CALM.bab).InH (fun _ => canon CALM.elec CALM.bab) ∧
    (Dist.Hf CALM.Res CALM.bad CALM.bab d).Endpoint CALM.elec
      (Dist.Hf CALM.Res CALM.bad CALM.bab d).InH (fun _ => canon CALM.elec CALM.bab) ∧
    (Dist.Hd CALM.Res D CALM.bad CALM.bab).ev ≠ (Dist.Hf CALM.Res CALM.bad CALM.bab d).ev :=
  Dist.fig_participant_runs CALM.elec (by decide) ⟨_, rfl⟩ d

/-- The general form of Fig. `fig:participant-runs`: for any specification and
any `i ≼ j` with a row at `j`, both histories end at `(σ_P(j), σ_P(j))`. -/
theorem «fig:participant-runs/general» {D : Type} (sp : Spec I O) {i j : I} (hij : i ≼ j)
    (hj : ∃ u, sp.P j u) (d : D) :
    (Dist.Hd O D i j).WF sp ∧ (Dist.Hf O i j d).WF sp ∧
    (Dist.Hd O D i j).Endpoint sp (Dist.Hd O D i j).InH (fun _ => canon sp j) ∧
    (Dist.Hf O i j d).Endpoint sp (Dist.Hf O i j d).InH (fun _ => canon sp j) ∧
    (Dist.Hd O D i j).ev ≠ (Dist.Hf O i j d).ev :=
  Dist.fig_participant_runs sp hij hj d

/-! ## Distributed consistency (§4.2, `sec:distributed-consistency`) -/

/-- "A continuation of a history at a consistent cut `C` is a history `H'` that
extends the history events of `C` with further history events after them."

Lean: same initial inputs and the same events at every position of `C`; since
`C` is a prefix at each participant, the new events come after. -/
abbrev «sec:distributed-consistency/continuation» {D : Type} {n : Nat}
    (H H' : Dist.History I O D n) (C : Dist.Pos n → Prop) : Prop :=
  H.Extends H' C

/-- "A consistent cut `C` is confluent at `j` … when some continuation at `C`
has a final cut with endpoint `((j,R))_{p∈P}` for some `R`." -/
abbrev «sec:distributed-consistency/cut-confluent» {D : Type} {n : Nat} (sp : Spec I O)
    (H : Dist.History I O D n) (C : Dist.Pos n → Prop) (j : I) : Prop :=
  H.CutConfluentAt sp C j

/-- "History events at different participants are independent, so this holds
exactly when the participant runs at `C` are confluent at `j`." -/
theorem «sec:distributed-consistency/cut-confluent-iff-runs» {D : Type} {n : Nat}
    {sp : Spec I O} {H : Dist.History I O D n} (hW : H.WF sp) {C : Dist.Pos n → Prop}
    (hC : H.IsCut C) {σs : Fin n → State sp} (hE : H.Endpoint sp C σs) (j : I) :
    H.CutConfluentAt sp C j ↔ ∃ τ : State sp, τ.cur = j ∧ ∀ p, Reach (σs p) τ :=
  Dist.cut_confluent_iff hW hC hE j

/-- **Def. distributed consistency** (`def:distributed-consistency`).  "An
I/O specification has distributed consistency when, for every finite
participant set, every consistent cut of every history is confluent at every
common input extension of the participants' current inputs."

Lean: for message data of type `D`; "every finite participant set" is "every
`n`" (participants `Fin n`). -/
abbrev «def:distributed-consistency» (sp : Spec I O) (D : Type) : Prop :=
  Dist.DistConsistent sp D

/-- **Prop. consistency and distributed consistency**
(`prop:distributed-consistency`).  "An I/O specification is consistent if
and only if it has distributed consistency." -/
theorem «prop:distributed-consistency» (sp : Spec I O) (D : Type) :
    sp.Consistent ↔ Dist.DistConsistent sp D :=
  Dist.consistent_iff_distConsistent sp D

/-- Prop. `prop:distributed-consistency` for the literal reading of item 2 of
Def. distributed-history ("a matching send"), without unique send
identifiers. -/
theorem «prop:distributed-consistency/literal-matching» (sp : Spec I O) (D : Type) :
    sp.Consistent ↔ Dist.DistConsistent0 sp D :=
  Dist.consistent_iff_distConsistent0 sp D

/-- "By Complete CALM, which reduces to Functional CALM with one output per
input, a spec has distributed consistency exactly when it satisfies
Lifted Monotonicity." -/
theorem «sec:distributed-consistency/lifted-monotonicity» (sp : Spec I O) (D : Type) :
    Dist.DistConsistent sp D ↔ sp.LiftedMono :=
  Dist.distConsistent_iff_liftedMono sp D

/-- **Corollary `cor:distributed-calm`** (Complete CALM at consistent cuts).
"A spec satisfies Lifted Monotonicity if and only if, in every finite
distributed history, every consistent cut is confluent at every common input
extension of the participants' current inputs."

Lean: `DistConsistent sp D` is precisely the quantified consistent-cut
property for message data `D`. -/
theorem «cor:distributed-calm» (sp : Spec I O) (D : Type) :
    sp.LiftedMono ↔ Dist.DistConsistent sp D :=
  (Dist.distConsistent_iff_liftedMono sp D).symm

/-- "The forward direction has a concrete witness.  For participant runs with common input extension `j`, the survivor test supplies a
`u ∈ P(j)` that survives in every endpoint; by Lemma run-residual, `u` extends
everything they have emitted.  At each participant, `input(j)` followed by
`output(u)` reaches the same state without commitment (Proposition
`prop:exposure-boundary`).  This is an existence
witness in the transition system; choosing `u`, communicating it, and
scheduling the transitions belong to the operational model."

Lean: `Dist.reconcile_cf` supplies `u`, proves that `(j,u)` survives in every
endpoint, and gives the commitment-free two-event continuation from each one. -/
theorem «sec:distributed-consistency/constructive-continuation» {sp : Spec I O}
    (hLM : sp.LiftedMono) (fam : List (State sp))
    (hrun : ∀ σ ∈ fam, IsRun σ) (j : I) (hj : ∀ σ ∈ fam, σ.cur ≼ j) :
    ∃ u, ∃ hu : sp.P j u, (∀ σ ∈ fam, σ.R j u) ∧
      ∀ σ ∈ fam, ExecCF σ [.input j, .output u] (meetState sp j u hu) :=
  Dist.reconcile_cf hLM fam hrun j hj

/-- **Cor. convergence** (`cor:convergence`).  "In any history of a consistent
functional specification, every participant whose current input at a
consistent cut is `j` is in state `σ_P(j)`.  Participants with the same current
input therefore agree, regardless of message paths, arrival order, or the
outputs they emitted."

Lean: `σs` is the endpoint of the cut; the first conjunct is "`σ_p(C) =
σ_P(cur)`", the second "same current input ⇒ same state". -/
theorem «cor:convergence» {D : Type} {n : Nat} {sp : Spec I O} (hc : sp.Consistent)
    (hf : sp.Functional) {H : Dist.History I O D n} {C : Dist.Pos n → Prop}
    {σs : Fin n → State sp} (hE : H.Endpoint sp C σs) :
    (∀ p, σs p = canon sp (σs p).cur) ∧
    (∀ p q, (σs p).cur = (σs q).cur → σs p = σs q) :=
  ⟨fun p => Dist.convergence hc hf hE p rfl, Dist.convergence_agree hc hf hE⟩

/-- After Cor. `cor:convergence`: "With several outputs per input this fails
even for consistent specs: in Figure `fig:ambiguity-frames`(g), a
run that emitted `{s→s1}` has subsumed the route sets that omit it, while a
run at the same input that emitted nothing keeps them.  Consistency then
guarantees that such replicas can be reconciled, not that they agree."  The
traceroute specification is consistent; the run that emitted `{s→s1}` and the
canonical run end at the same input in different states (the first has
subsumed `{s→a}`, the second keeps it); and the two are confluent at that
input. -/
theorem «cor:convergence/relational-fails» :
    Figures.Trace.spec.Consistent ∧
      (IsRun (outState (canon Figures.Trace.spec ()) Figures.Trace.rS1
          ((Figures.Trace.canonR _).2 (by decide))) ∧
        IsRun (canon Figures.Trace.spec ()) ∧
        (outState (canon Figures.Trace.spec ()) Figures.Trace.rS1
          ((Figures.Trace.canonR _).2 (by decide))).cur = (canon Figures.Trace.spec ()).cur ∧
        ¬ (outState (canon Figures.Trace.spec ()) Figures.Trace.rS1
          ((Figures.Trace.canonR _).2 (by decide))).R () Figures.Trace.rA ∧
        (canon Figures.Trace.spec ()).R () Figures.Trace.rA ∧
        outState (canon Figures.Trace.spec ()) Figures.Trace.rS1
          ((Figures.Trace.canonR _).2 (by decide)) ≠ canon Figures.Trace.spec ()) ∧
      ConfluentAt [outState (canon Figures.Trace.spec ()) Figures.Trace.rS1
          ((Figures.Trace.canonR _).2 (by decide)), canon Figures.Trace.spec ()] () := by
  have hc := Figures.Trace.directed.2.2
  have hd := Figures.Trace.state_depends_on_outputs
  refine ⟨hc, hd, hc _ ?_ () ?_⟩
  · intro σ hσ
    rcases List.mem_cons.1 hσ with rfl | hσ
    · exact hd.1
    · rcases List.mem_cons.1 hσ with rfl | hσ
      · exact hd.2.1
      · cases hσ
  · intro σ _; exact PO.refl _

/-- The same failure on a minimal example: a consistent specification with one
input and outputs `lo ≼ hi` has a run ending at a non-canonical state. -/
theorem «cor:convergence/relational-fails-minimal» :
    CALM.specTwo.Consistent ∧ ∃ τ : State CALM.specTwo, IsRun τ ∧ τ ≠ canon CALM.specTwo τ.cur :=
  CALM.state_by_input_fails_relationally

/-- *Message data.*  "Data can influence which history events occur next at the
receiver, but it never directly changes the receiver's
specification state, and nothing in the definitions above depends on it."  The
CIDR version says: "Data can influence a system's subsequent actions, but never
directly changes the state."

Lean: distributed consistency does not depend on the type `D` of message data
(sends and receives are filtered out of participant runs by `Dist.ioOf`). -/
theorem «sec:distributed-consistency/message-data» (sp : Spec I O) (D D' : Type) :
    Dist.DistConsistent sp D ↔ Dist.DistConsistent sp D' :=
  (Dist.consistent_iff_distConsistent sp D).symm.trans (Dist.consistent_iff_distConsistent sp D')

/-- *Message data*: "Participants may also share emitted outputs in `d`; this
does not change which cuts are confluent (Appendix `app:exchanging-outputs`)."
The entries are in `Paper/AppB_ProofsDistributed.lean`
(`«app:exchanging-outputs/cut»`). -/
theorem «sec:distributed-consistency/sharing-outputs» {D : Type} {n : Nat}
    {sp : Spec I O} {H : Dist.History I O D n} (hW : H.WF sp) {C : Dist.Pos n → Prop}
    (hC : H.IsCut C) {σs : Fin n → State sp} (hE : H.Endpoint sp C σs) (os : Fin n → List O)
    (hos : ∀ p, ∀ o ∈ os p, H.EmittedIn C o) (j : I) (hj : ∀ p, (σs p).cur ≼ j) :
    H.CutConfluentAt sp C j ↔ ∃ u, sp.P j u ∧ ∀ p, Dist.honor (σs p).R (os p) j u :=
  Dist.honor_cut_confluent hW hC hE os hos j hj

/-! ## Systems and canonical runs (§4.3, `sec:systems`)

A spec describes which behaviors are permitted, but not how a system chooses
among them.  The section models those choices, then shows that their commitments
can be assessed against canonical runs regardless of system implementation
choices. -/

/-- "When the registrar of Section election-story emits `⊥`, it also closes
the polls (Figure election-frames(d)), although emitting `⊥` does not require
the poll-closing commitment.  Closing the polls is the registrar's design
decision, as fixing orderings is 2PL's."

Lean: under any basis containing `closePolls`, the commitment event
`apply([closePolls])` followed by `output(⊥)` from `σ_P(ab·)` is a run ending
at panel (d); yet `⊥` is a legal output there and `Excluded_o` is empty, so
`output(⊥)` needs no commitment. -/
theorem «sec:systems/registrar» :
    (∀ B : CommitmentBasis CALM.elec, B Figures.closePolls →
      SysExec B (canon CALM.elec CALM.bab) [.commitment [Figures.closePolls], .output .bot]
        Figures.Elec.panelD) ∧
    Exposable (canon CALM.elec CALM.bab) .bot ∧
    (¬ ∃ k x, Excluded (canon CALM.elec CALM.bab) .bot k x) :=
  ⟨Figures.Elec.registrar_step, Figures.Elec.bot_alone_at_b.1,
    Figures.Elec.bot_alone_at_b.2.1⟩

  /-! The systems section generalizes the earlier construction: "Sections
  functional-calm–complete-calm used only the canonical commitment `x_o`
  required by an output. Systems may commit earlier or remove additional
  alternatives … We therefore allow bespoke system commitments."  The formal
  definition follows. -/

  /-- **Def. commitment** (`def:commitment`).  "A commitment is a partial function
  on specification states that removes a nonempty set of rows.  No row it
  removes is subsumed by a row that remains at the same input.  Thus, whenever
  `c(i,R) = (j,R')`, we have `R' ⊊ R` and
  `(k,u) ∈ R ∖ R', (k,w) ∈ R' ⟹ u ⋠ w` (Eq. commitment-unsubsumed).  It leaves
  the current input unchanged: `j=i`."

Lean: `app : State sp → Option (State sp)` with fields `cur_eq`, `sub`,
  `removes` (`R' ⊊ R`), `unsubsumed` (Eq. commitment-unsubsumed). -/
abbrev «def:commitment» (sp : Spec I O) := Commitment sp

/-- **Eq. `eq:commitment-unsubsumed`**: whenever `c(i,R) = (i,R')`,
"`(k,u) ∈ R ∖ R', (k,w) ∈ R' ⟹ u ⋠ w`" (field `Commitment.unsubsumed`). -/
theorem «eq:commitment-unsubsumed» {sp : Spec I O} (c : Commitment sp) (σ τ : State sp)
    (h : c.app σ = some τ) :
    ∀ k u w, σ.R k u → ¬ τ.R k u → τ.R k w → ¬ (u ≼ w) :=
  c.unsubsumed σ τ h

/-- The canonical commitment of Definition `def:canonical-commitment` satisfies
Definition `def:commitment`. -/
theorem «sec:systems/canonical-commitment» {sp : Spec I O} (o : O)
    (σ τ : State sp) :
    (canonicalCommitment o : Commitment sp).app σ = some τ ↔
      ∃ h : σ.R σ.cur o, (∃ k x, Excluded σ o k x) ∧ commitmentState σ o h = τ :=
  commitmentApp_eq

/-- **Def. `def:local-history`** (Local history).  "A local history of
participant `p` is a finite sequence of `p`'s history events, including the
messages it has received."

Lean: for a `CAP.History sp D n`, participant `p`'s local history is
`H p : List (CAP.LEv sp D n)`; the events are inputs, outputs, sends,
receives, and commitment events `CAP.LEv.commitment γ`. -/
abbrev «def:local-history» (sp : Spec I O) (D : Type) (n : Nat) :=
  List (CAP.LEv sp D n)

/-- **Def. `def:strategy`** (Strategy).  "A strategy for a participant `p` is
a nondeterministic transition function: it maps each local history `λ` of
`p` to a set `θ_p(λ)` of output, commitment, and send events of `p`, and `p`
next performs any one of them, or waits.  Input and receive events are not
chosen by the strategy: inputs come from the environment and receives from
matching sends."

Lean (the `CC.CAP` system model): a strategy for `p` is a relation from local
histories (`List (CAP.LEv sp D n)`) to next events; local events include
commitment events `CAP.LEv.commitment γ`.  Its value on input events
is ignored: `CAP.Allowed` always allows inputs. -/
abbrev «def:strategy» (sp : Spec I O) (D : Type) (n : Nat) :=
  List (CAP.LEv sp D n) → CAP.LEv sp D n → Prop

/-- **Def. `def:system`** (System).  "A system consists of a *commitment
basis* `ℬ`, a set of commitments shared by all participants, and a strategy
`θ_p` for each participant `p` whose output and commitment events apply only
commitments from `ℬ`."

Lean: `CAP.System` (basis + strategies `strat n init p`, one for every
participant of every finite participant set and initial inputs, as §4.4 later
requires) with `System.CommitmentBasisRespecting`.  Its commitments are
`CAP.Commitment`, equivalent to `CC.Commitment` (`CC.Dist.toCAP`,
`CC.Dist.ofCAP`).  The library's `CAP.System` does not require basis respect;
`«def:system/restrict»` shows this loses nothing. -/
abbrev «def:system» (sp : Spec I O) (D : Type) :=
  {Sys : CAP.System sp D // Sys.CommitmentBasisRespecting}

/-- **Def. `def:produced-history`** (Produced history).  "A distributed
history produced by a system consists of input events supplied by the
environment, receives of matching sends, and output, commitment, and send
events chosen by the participants' strategies."  Lean: `CAP.Produced Sys n
init H`. -/
abbrev «def:produced-history» {sp : Spec I O} {D : Type} (Sys : CAP.System sp D)
    (n : Nat) (init : Fin n → I) (H : CAP.History sp D n) : Prop :=
  CAP.Produced Sys n init H

/-- Def. `def:system`: "A distributed history produced by the system consists
of input events supplied by the environment, receives of matching sends, and
output, commitment, and send events chosen by the participants' strategies."
For a basis-respecting system this is the library's `CAP.Produced`: every
event other than an input is permitted by the strategy at the local history
before it (`CAP.allowed_iff_stratAllowed`). -/
theorem «def:system/produced» {sp : Spec I O} {D : Type} (Sys : CAP.System sp D)
    (h : Sys.CommitmentBasisRespecting) (n : Nat) (init : Fin n → I) (H : CAP.History sp D n) :
    CAP.Produced Sys n init H ↔ ∀ p, CAP.Compliant (CAP.StratAllowed Sys n init p) (H p) :=
  ⟨fun hp p a e b hab => (CAP.allowed_iff_stratAllowed h n init p a e).1 (hp p a e b hab),
   fun hp p a e b hab => (CAP.allowed_iff_stratAllowed h n init p a e).2 (hp p a e b hab)⟩

/-- Def. `def:system`, generality: requiring the strategies to respect the
basis loses nothing.  Restricting any system's strategies to basis
commitments gives a basis-respecting system that allows exactly the same
events, hence produces the same histories. -/
theorem «def:system/restrict» {sp : Spec I O} {D : Type} (Sys : CAP.System sp D) :
    Sys.restrict.CommitmentBasisRespecting ∧
      ∀ n init p pre e, CAP.Allowed Sys.restrict n init p pre e ↔ CAP.Allowed Sys n init p pre e :=
  ⟨Sys.restrict_basisRespecting, Sys.restrict_allowed⟩

/-- After Def. `def:system`: "Coordination mechanisms live in the system: its
strategies describe how participants use them, and its basis records the
commitments they can enforce.  A system's strategies select the events of an
actual execution; they need not realize every run the spec permits.  A
deployment can separately restrict which participants may emit which rows."
Lean: `CAP.System sp D` carries one specification `sp` and one basis; its
strategies `strat n init p` may differ by participant.  A deployment
`Deploy.Deployment sp n` gives participant `p` a table `A p` inside `sp.P`.
The system is the component `Components.Component.ofSystemOn Sys N` of `sp`,
with the system's basis and the participant runs of its produced histories as
admitted runs. -/
theorem «sec:systems/one-specification» {sp : Spec I O} {D : Type} (Sys : CAP.System sp D)
    (N : Nat → Prop) (location : Option Components.LocationForm) :
    (Components.Component.ofSystemOn Sys N location).basis =
        (fun c => Sys.basis (Dist.toCAP c)) ∧
      (∀ r, (Components.Component.ofSystemOn Sys N location).accepts r →
        SysExec (fun c => Sys.basis (Dist.toCAP c)) (canon sp r.input) r.events r.final) ∧
      ∀ (n : Nat) (Dp : Deploy.Deployment sp n) p k u, Dp.A p k u → sp.P k u :=
  ⟨rfl, fun r h => ((Components.Component.ofSystemOn Sys N location).sound r h).legal,
    fun _ Dp => Dp.sub⟩

/-- **Def. system output event** (`def:system-output-event`).  "Let `(i,R)`
be a state and `o ∈ R(i)`.  A system emits `o` by the output event `output(o)`
of Section lifted-output-events, which ends at `(i, R[out ⪰ o])`.  When `o` is
not a legal output, the event applies the canonical commitment `x_o`, which
must then belong to the system's basis."

Lean: `SysStep B σ e τ` (also covering input and commitment events); its
output constructor `SysStep.output` is a `Step σ (.output o) τ` of §§2–3 with
the side condition `Exposable σ o ∨ B (canonicalCommitment o)`
(`«sec:systems/system-histories»`). -/
abbrev «def:system-output-event» {sp : Spec I O} (B : CommitmentBasis sp) (σ : State sp)
    (e : SEvent sp) (τ : State sp) : Prop :=
  SysStep B σ e τ

  /-- **Def. commitment event** (`def:commitment-event`).  "A commitment event
  `apply(γ)` applies a nonempty sequence `γ = c₁⋯cₙ` of commitments, each
defined at the state its predecessors leave, and emits nothing."

Lean: `SysStep B σ (.commitment γ) τ` (constructor `SysStep.commitment`: every
`c ∈ γ` is in `B`, `γ ≠ []`, and `ApplySeq γ σ τ`).  In the `CC.CAP` history
model the local event is `CAP.LEv.commitment γ`. -/
abbrev «def:commitment-event» {sp : Spec I O} (B : CommitmentBasis sp) (σ : State sp)
    (γ : List (Commitment sp)) (τ : State sp) : Prop :=
  SysStep B σ (.commitment γ) τ

/-- After Def. `def:commitment-event`: "A system applies its own commitments
only in commitment events.  A commitment event may precede an output event,
which then has less to remove.  The environment observes nothing from a
commitment event."  Lean: a commitment event is exactly a nonempty basis sequence applied in
order; it keeps the current input and only removes rows, and its erasure is
empty (`SEvent.erase (.commitment γ) = none`). -/
theorem «sec:systems/commitment-event-unobserved» {sp : Spec I O} {B : CommitmentBasis sp}
    {σ τ : State sp} {γ : List (Commitment sp)} :
    (SysStep B σ (.commitment γ) τ ↔ (∀ c ∈ γ, B c) ∧ γ ≠ [] ∧ ApplySeq γ σ τ) ∧
    (SysStep B σ (.commitment γ) τ → τ.cur = σ.cur ∧ ∀ k u, τ.R k u → σ.R k u) ∧
    (SEvent.commitment γ : SEvent sp).erase = none :=
  ⟨⟨fun h => by cases h with | commitment hb hne ha => exact ⟨hb, hne, ha⟩,
    fun ⟨hb, hne, ha⟩ => SysStep.commitment hb hne ha⟩,
   fun h => ⟨h.commitment_cur, h.sub⟩, rfl⟩

/-- After Def. `def:commitment-event`: "A commitment event may precede an
output event, which then has less to remove."  Lean: an old-style compound
step (commitments `γ` from the basis, then a legal output at the committed
state) is the commitment event followed by the output event; and an output
event after a commitment event removes only rows of the committed table. -/
theorem «sec:systems/commitment-then-output» {sp : Spec I O} {B : CommitmentBasis sp} :
    (∀ {σ σc τ : State sp} {γ : List (Commitment sp)} {o : O},
      (∀ c ∈ γ, B c) → ApplySeq γ σ σc → σc.R σc.cur o → Exposable σc o →
      τ.cur = σ.cur → τ.R = outputTable σc o →
      SysExec B σ ((if γ = [] then [] else [.commitment γ]) ++ [.output o]) τ) ∧
    (∀ {σc τ : State sp} {o : O}, SysStep B σc (.output o) τ →
      τ.R = outputTable σc o) :=
  ⟨fun hB hγ ho hleg hcur hR => split_output hB hγ ho hleg hcur hR,
   fun h => (containment h).2.2.2⟩

/-- Every output event of a system is the canonical event: the canonical
steps `CanonStep` (under `B_P`, no commitment events) are exactly the steps
of §§2–3. -/
theorem «sec:systems/output-is-canonical-event» {sp : Spec I O} :
    (∀ (σ τ : State sp) (e : SEvent sp), CanonStep σ e τ →
      ∃ e' : Event I O, e.erase = some e' ∧ Step σ e' τ) ∧
    (∀ (σ τ : State sp) (e : Event I O), Step σ e τ →
      ∃ e' : SEvent sp, e'.erase = some e ∧ CanonStep σ e' τ) :=
  ⟨fun _ _ _ => canonStep_step, fun _ _ _ => step_canonStep⟩

/-- Def. `def:system-output-event` together with Def. `def:system`: a
system's output event is a `Step σ (.output o) τ` of §§2–3, with `x_o` in the
basis when `o` is not legal.

Lean: in the `CC.CAP` history model an output event `out o` is exactly this
step (first conjunct, `CAP.kcap o` is `x_o`); erasure keeps `o` (second
conjunct). -/
theorem «sec:systems/system-histories» {sp : Spec I O} {B : CommitmentBasis sp} {σ τ : State sp}
    {o : O} :
    (SysStep B σ (.output o) τ ↔
      Step σ (.output o) τ ∧ (Exposable σ o ∨ B (Dist.ofCAP (CAP.kcap o)))) ∧
    (SEvent.output o : SEvent sp).erase = some (Event.output o : Event I O) :=
  ⟨Dist.sysStep_iff_CAP, rfl⟩

/-- Opener of §4.2: "Two-phase locking (2PL) uses locks on operations: when
`B` waits for a lock `A` holds, `order(A,B)` fixes `A` before `B`.
Multiversion timestamp ordering (MVTO) uses timestamps: `stamp(B)` fixes
`B` before any transaction not yet stamped."  At the canonical state of
an input whose transactions `A`, `B`, `C` have each requested commit (Appendix
G's specification), no commitment of `ℬ_MVTO` has the effect of `order(A,B)`,
and no commitment of `ℬ_2PL` has the effect of `stamp(B)`. -/
theorem «sec:systems/bases-differ» {T K : Type} {A B C : T} {k : Txn.Partial.Inp T K}
    (h : Txn.Partial.Tri k A B C) :
    (∃ τ, (Txn.Partial.order A B).app (Txn.Partial.σ3 k) = some τ ∧
      ∀ c, Txn.Partial.basisMVTO c → c.app (Txn.Partial.σ3 k) ≠ some τ) ∧
    (∃ τ, (Txn.Partial.stamp B (fun _ => False)).app (Txn.Partial.σ3 k) = some τ ∧
      ∀ c, Txn.Partial.basis2PL c → c.app (Txn.Partial.σ3 k) ≠ some τ) :=
  CC.Paper.«app:cc-bases/bases-differ» h

/-- Fig. `fig:cc-commitments`: "2PL applies `order(A,B)` when `B` waits for a
lock `A` holds, leaving `C`'s position open (panel (h)); MVTO applies
`stamp(B)` when `B` receives the first timestamp, placing `B` first (panel
(i))."  The caption: only complete rows without aborts or read results are
shown.  Among those, `order(A,B)` keeps exactly the rows with `A` before `B`,
and `stamp(B)` (no earlier stamps) exactly those with `B` first. -/
theorem «fig:cc-commitments» {T K : Type}
    {σ τ τ' : State (Txn.Partial.spec (T := T) (K := K) false)} {A B : T}
    {k : Txn.Partial.Inp T K} {c : Txn.Partial.ROut T K}
    (hp : Txn.Partial.Decides false k c.o) (hX : ∀ t, ¬ c.o.X t) (hA : k.mem A)
    (hB : k.mem B) :
    ((Txn.Partial.order A B).app σ = some τ → (τ.R k c ↔ σ.R k c ∧ c.o.lt A B)) ∧
    ((Txn.Partial.stamp B (fun _ => False)).app σ = some τ' →
      (τ'.R k c ↔ σ.R k c ∧ ∀ D, k.mem D → D ≠ B → c.o.lt B D)) :=
  ⟨fun h => CC.Paper.«app:cc-bases/fig-h» h hp hX hA hB,
   fun h => CC.Paper.«app:cc-bases/fig-i» h hp hX hB⟩

/-- "Both are commitments: rows survive at the input."

Lean, for any commitment (in particular `Txn.Partial.order`, `Txn.Partial.stamp`): a
commitment keeps a row at the current input, so where it removes rows there it
chooses — some row is kept and no removed row is extended by it. -/
theorem «sec:systems/two-systems-two-commitments» {sp : Spec I O} (c : Commitment sp)
    {σ τ : State sp} (h : c.app σ = some τ) :
    (∃ w, τ.R σ.cur w) ∧
    ((∃ u, σ.R σ.cur u ∧ ¬ τ.R σ.cur u) →
      ∃ w, τ.R σ.cur w ∧ ∀ u, σ.R σ.cur u → ¬ τ.R σ.cur u → ¬ u ≼ w) := by
  obtain ⟨w, hw⟩ := commitment_preserves_current_fiber c h
  exact ⟨⟨w, hw⟩, fun _ => ⟨w, hw, fun u hu hnu => c.unsubsumed σ τ h _ u w hu hnu hw⟩⟩

/-- "… and neither is the commitment `x_o` of Definition lifted-output-event."
At the canonical state of an input whose transactions `A`, `B`, `C` have each
requested commit (Appendix G's specification), the results of
`order(A,B)` and `stamp(B)` are not the result of `x_o` for any output `o`. -/
theorem «sec:systems/neither-is-canonical-commitment» {T K : Type} {A B C : T} {k : Txn.Partial.Inp T K}
    (h : Txn.Partial.Tri k A B C) :
    (∀ τ, (Txn.Partial.order A B).app (Txn.Partial.σ3 k) = some τ →
      ∀ o, (canonicalCommitment o).app (Txn.Partial.σ3 k) ≠ some τ) ∧
    (∀ τ, (Txn.Partial.stamp B (fun _ => False)).app (Txn.Partial.σ3 k) = some τ →
      ∀ o, (canonicalCommitment o).app (Txn.Partial.σ3 k) ≠ some τ) :=
  Txn.Partial.neither_is_canonical_commitment h

/-- "We call the runs of Sections functional-calm–complete-calm canonical runs,
and a run under a basis `ℬ` is one whose output and commitment events apply
only commitments from `ℬ` (Definition run-under-basis)."  (Formal definitions:
`«def:run-under-basis»` in `Paper/AppC_CommitmentBases.lean`.) -/
abbrev «sec:systems/run-under-basis» {sp : Spec I O} (B : CommitmentBasis sp) (es : List (SEvent sp))
    (τ : State sp) : Prop :=
  RunUnder B es τ

/-- *Observable equivalence.*  "Every output event of a system is the
canonical event for its output, which preserves the containment of tables
(Lemma output-containment); commitment events are dropped on the canonical
side; the row containment extends event by event along the run."  Every run
under any basis has an observably equivalent canonical run: one that accepts
the same inputs, emits the same outputs, and keeps at least the original's
rows after each event; its commitment events erase to nothing (Lemma
canonical-equivalent, Appendix bases).

Lean: `«lem:canonical-equivalent»`; `Lockstep` records the per-event
containment (a commitment event of the original is matched by no canonical
event), and `SEvent.erase (.commitment γ) = none`, so commitment events
disappear from the erasure `es.filterMap SEvent.erase`. -/
theorem «sec:systems/canonical-equivalent» {sp : Spec I O} {B : CommitmentBasis sp} {i : I}
    {es : List (SEvent sp)} {ρ : State sp} (h : SysExec B (canon sp i) es ρ) :
    ∃ es' ρ', Lockstep B (canon sp i) es ρ (canon sp i) es' ρ' ∧
      es.filterMap SEvent.erase = es'.filterMap SEvent.erase ∧
      Exec (canon sp i) (es.filterMap SEvent.erase) ρ' ∧
      ρ'.cur = ρ.cur ∧ (∀ k u, ρ.R k u → ρ'.R k u) :=
    canonical_equivalent h

/-- **Corollary `cor:free-eager-output`** (Eager output is incidental).
"The canonical event for a legal output applies no commitment: every row it
removes is subsumed by a row that survives.  Likewise, deferring the output
avoids no commitment."

Lean: for any commitment basis, the output event of a legal output is
available (it applies no commitment, so it needs nothing from the basis);
every row that event removes is in `Subsumed_o`.  Observable
Equivalence (`«sec:systems/canonical-equivalent»`) lifts the canonical account
to arbitrary runs under a basis. -/
theorem «cor:free-eager-output» {sp : Spec I O} (B : CommitmentBasis sp)
    (σ : State sp) (o : O) (ho : σ.R σ.cur o) (hlegal : Exposable σ o) :
    SysStep B σ (.output o) (outState σ o ho) ∧
      ∀ k x, σ.R k x → ¬ outputTable σ o k x → Subsumed σ o k x := by
  refine ⟨legal_output_step (step_output_outState ho) hlegal, ?_⟩
  intro k x hx hn
  have hox : ¬ o ≼ x := fun h => hn ⟨hx, h⟩
  obtain ⟨u, hu, hou, hxu⟩ := hlegal k x hx hox
  exact ⟨hx, hox, u, hu, hou, hxu⟩

/-- *Canonical runs suffice*, example.  "Consider 2PL on an input of three
transactions `A`, `B`, `C` that have each issued their operations and requested
commit, where `B` waits for a lock that `A` holds.  When `B` begins to wait,
2PL applies `order(A,B)` in a commitment event, before any output, keeping only
rows that can be completed without placing `B` before `A`.  The canonical run
skips that event, so it keeps every row, including the one completed by
`[B,A,C]`.  Suppose 2PL later commits all three transactions and orders `A`
before `C` before `B` in a commitment event, and then emits `[A,C,B]`.  The
canonical run
can emit the same output because that row was present all along.  Every row
retained afterward extends `[A,C,B]`, so it satisfies all of 2PL's decisions,
including the earlier order of `A` before `B`.  Thus the canonical final table
is contained in 2PL's, while Observable Equivalence gives the reverse
  containment.  The tables are equal: the lock made the `A`-before-`B` decision
  earlier than the output required.  The commitments required by a spec's
  outputs therefore do not depend on their timing or representation in a
  system's commitment basis."

Lean (`CC.Txn.Partial.CommitEx.example_commitment_event_ABC`), at any input `k`
whose transactions `A`, `B`, `C` have each issued their operations and requested
commit; rows are serial orders without aborts or reads:
(a) the commitment event `apply(order(A,B))` is a legal `B_2PL` step from
the canonical state `σ₀` to `σ₁`; `σ₁` keeps exactly the rows of `σ₀` with a
complete output extension in `σ₀` that does not commit `B` before `A` (aborting `A`
or `B` counts), so it keeps `[A,B,C]` and removes `[B,A,C]`;
(b) the canonical run stays at `σ₀`, which has `[B,A,C]`;
(c) 2PL's commitment event
`apply(TxCommit(A),TxCommit(B),TxCommit(C),order(A,C),order(C,B))` is a legal
`B_2PL` step from `σ₁` to `σ₂`, after which `[A,C,B]` is a legal output and
`output([A,C,B])` is a legal `B_2PL` step (the three `TxCommit`s alone do not
make it legal); the canonical run can emit `[A,C,B]` because that row was
present at `σ₀`.  Every row it retains afterward extends
`[A,C,B]`, hence satisfies those five commitments and the earlier `order(A,B)`;
(d) the canonical final table is therefore contained in 2PL's, while Observable
Equivalence gives the reverse containment.  The two runs end at the same
state and form a `Lockstep` pair whose commitment events are matched by no
canonical event. -/
theorem «sec:systems/canonical-example» {T K : Type} {A B C : T} {k : Txn.Partial.Inp T K}
    (h : Txn.Partial.Tri k A B C) :
    let σ0 := Txn.Partial.σ3 k
    let o2 := Txn.Partial.CommitEx.o2 (K := K) A B C
    let γ2 := Txn.Partial.CommitEx.γ2 (K := K) A B C
    let row := fun (l : List T) => Txn.Partial.full (K := K) (Txn.Partial.mk l fun _ => False)
    ∃ σ1 σ2 τ2 τ2' : State (Txn.Partial.spec (T := T) (K := K) false),
      -- (a)
      SysStep Txn.Partial.basis2PL σ0 (.commitment [Txn.Partial.order A B]) σ1 ∧ σ1.cur = k ∧
      (∀ k' w, σ1.R k' w ↔ σ0.R k' w ∧
        ∃ c, σ0.R k' c ∧ Txn.Partial.Decides false k' c.o ∧ w ≼ c ∧ ¬ c.o.lt B A) ∧
      σ1.R k (row [A, B, C]) ∧ ¬ σ1.R k (row [B, A, C]) ∧
      -- (b)
      σ0.R k (row [B, A, C]) ∧
      -- (c)
      SysStep Txn.Partial.basis2PL σ1 (.commitment γ2) σ2 ∧ Exposable σ2 o2 ∧
      SysStep Txn.Partial.basis2PL σ2 (.output o2) τ2 ∧
      (¬ ∃ ρ, SysStep Txn.Partial.basis2PL σ1
        (.commitment [Txn.Partial.commit A, Txn.Partial.commit B, Txn.Partial.commit C]) ρ ∧
        Exposable ρ o2) ∧
      CanonStep σ0 (.output o2) τ2' ∧
      -- (d)
      τ2 = τ2' ∧
      Lockstep Txn.Partial.basis2PL σ0
        [.commitment [Txn.Partial.order A B], .commitment γ2, .output o2] τ2
        σ0 [.output o2] τ2' :=
  Txn.Partial.CommitEx.example_commitment_event_ABC h


/-- **Proposition `prop:commitment-conflict`** (Commitment conflict).  "Let a
run from `σ_P(i)` apply a commitment that removes the row `(k,x)`, and let
another run from `σ_P(i)` issue the canonical events `input(k)` followed by
`output(x)`.  These two runs *conflict*: they are not confluent at `k`."

Lean: the first run is a run under any basis `B` reaching `σ`, where the
commitment `c` takes `σ` to `σc` and removes `(k,x)`.  The first run's final
state `σ'` may be any state whose rows lie within `σc`'s (for instance, after
the rest of an output event or later events).  The second run exists, and the
two final states are not `ConfluentAt k`. -/
theorem «prop:commitment-conflict» {sp : Spec I O} {B : CommitmentBasis sp}
    {i k : I} {x : O} {es : List (SEvent sp)} {σ σc σ' : State sp} {c : Commitment sp}
    (hrun : SysExec B (canon sp i) es σ) (happ : c.app σ = some σc)
    (hx : σ.R k x) (hnx : ¬ σc.R k x) (hsub : ∀ k w, σ'.R k w → σc.R k w) :
    ∃ τ : State sp, Exec (canon sp i) [.input k, .output x] τ ∧ τ.cur = k ∧
      ¬ ConfluentAt [σ', τ] k := by
  have hik : i ≼ k := (hrun.sub k x hx).2
  obtain ⟨τ, hex, hcur⟩ := CAP.canonical_run_contradicts hik (σ.sub k x hx)
  have href : ∀ w, τ.R k w → x ≼ w := by
    intro w hw
    cases hex with
    | cons _ h2 =>
      cases h2 with
      | cons s2 h3 =>
        cases h3 with
        | nil =>
          cases s2 with
          | output _ _ _ _ hR =>
            rw [hR] at hw
            exact hw.2
  refine ⟨τ, hex, hcur, ?_⟩
  rintro ⟨ρ, hρ, hall⟩
  obtain ⟨w, hw⟩ := ρ.hasCur
  rw [hρ] at hw
  have h1 := reach_sub (hall σ' (by simp)) k w hw
  have h2 := reach_sub (hall τ (by simp)) k w hw
  exact (c.unsubsumed σ σc happ k x w hx hnx (hsub k w h1)) (href w h2)

/-- Supporting form of Prop. `prop:commitment-conflict`: the second run exists.
Every commitment applied in a run from `σ_P(i)` removes some row `(k,x)`, and
the canonical run `input(k) output(x)` from `σ_P(i)` reaches current input `k`. -/
theorem «prop:commitment-conflict/second-run» {sp : Spec I O} {B : CommitmentBasis sp}
    {i : I} {es : List (SEvent sp)} {σ τ : State sp} {c : Commitment sp}
    (hrun : SysExec B (canon sp i) es σ) (happ : c.app σ = some τ) :
    ∃ k x ρ, σ.R k x ∧ ¬ τ.R k x ∧
      Exec (canon sp i) [.input k, .output x] ρ ∧ ρ.cur = k := by
  obtain ⟨k, x, hx, hnx⟩ := c.removes σ τ happ
  have hik : i ≼ k := (hrun.sub k x hx).2
  obtain ⟨ρ, he, hc⟩ := CAP.canonical_run_contradicts hik (σ.sub k x hx)
  exact ⟨k, x, ρ, hx, hnx, he, hc⟩

/-- Supporting form: from `σ_P(i)` with `i ≼ k`, the canonical run
`input(k) output(x)` reaches current input `k` for any `x ∈ P(k)`. -/
theorem «prop:commitment-conflict/canonical-run» {sp : Spec I O} {i k : I} {x : O}
    (hik : i ≼ k) (hx : sp.P k x) :
    ∃ τ : State sp, Exec (canon sp i) [.input k, .output x] τ ∧ τ.cur = k :=
  CAP.canonical_run_contradicts hik hx

/-- General form of Prop. `prop:commitment-conflict`.  Let a commitment take
`σ` to `σc`, and let `τ` either have only rows at `k` extending a removed
output `x`, or have current input `k` when the commitment emptied the fiber at
`k` (`CommitmentContradictsAt σ σc τ k`).  Then no state with current input `k`
is reachable from both, even when the two continuations use arbitrary,
independent bases. -/
theorem «prop:commitment-conflict/general» {sp : Spec I O}
      {B1 B2 : CommitmentBasis sp} {c : Commitment sp} {σ σc τ : State sp} {k : I}
      (happ : c.app σ = some σc) (hcontra : Dist.CommitmentContradictsAt σ σc τ k) :
      ¬ ∃ ρ : State sp, ρ.cur = k ∧
          (∃ es, SysExec B1 σc es ρ) ∧ (∃ es, SysExec B2 τ es ρ) :=
    Dist.commitment_contradiction_sysExec happ hcontra

  /-- Prop. `prop:commitment-conflict`, with continuations in the
  transition system of Sections 2--3. -/
theorem «prop:commitment-conflict/reach-general» {sp : Spec I O}
      {c : Commitment sp} {σ σc τ : State sp} {k : I}
      (happ : c.app σ = some σc) (hcontra : Dist.CommitmentContradictsAt σ σc τ k) :
      ¬ ∃ ρ : State sp, ρ.cur = k ∧ Reach σc ρ ∧ Reach τ ρ :=
    Dist.commitment_contradiction_reach happ hcontra

  /-- Supporting output-only form of Prop. `prop:commitment-conflict`.
under different bases. -/
theorem «prop:commitment-conflict/any-bases» {sp : Spec I O}
    {B B' B1 B2 : CommitmentBasis sp} {σ σ' t : State sp} {o x : O}
    (h1 : SysStep B σ (.output o) σ') (hno : ∀ w, σ'.R σ.cur w → ¬ x ≼ w)
    (h2 : SysStep B' σ (.output x) t) :
    ¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧
        (∃ es, SysExec B1 σ' es ρ) ∧ (∃ es, SysExec B2 t es ρ) :=
  Dist.conflicting_outputs2 h1 hno h2

/-- Prop. `prop:commitment-conflict`, with continuations in the
transition system of §§2–3. -/
theorem «prop:commitment-conflict/reach» {sp : Spec I O} {B B' : CommitmentBasis sp}
    {σ σ' t : State sp} {o x : O}
    (h1 : SysStep B σ (.output o) σ') (hno : ∀ w, σ'.R σ.cur w → ¬ x ≼ w)
    (h2 : SysStep B' σ (.output x) t) :
    ¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧ Reach σ' ρ ∧ Reach t ρ :=
  conflicting_outputs_reach h1 hno h2

/-- Prop. `prop:commitment-conflict` with the first event any
event, in particular a commitment event `apply(γ)`: "let one run perform an
output or commitment event after which no output at `i` extends `x`".

Lean: for any event `e` taking `σ` to `σ'` with no output at `i` extending `x`,
and `output(x)` taking `σ` to `t`, no state with current input `i` is
reachable from both, under any bases or in the transition system of §§2–3; if
`e` is an output event `output(o)`, then `o` is not legal, so `e` applies
`x_o`; if `e` is a commitment event, its sequence is nonempty. -/
theorem «prop:commitment-conflict/any-event» {sp : Spec I O}
    {B B' B1 B2 : CommitmentBasis sp} {σ σ' t : State sp} {e : SEvent sp}
    {x : O}
    (h1 : SysStep B σ e σ') (hno : ∀ w, σ'.R σ.cur w → ¬ x ≼ w)
    (h2 : SysStep B' σ (.output x) t) :
    (∀ o, e = .output o → ¬ Exposable σ o) ∧ (∀ γ, e = .commitment γ → γ ≠ []) ∧
    (¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧
        (∃ es, SysExec B1 σ' es ρ) ∧ (∃ es, SysExec B2 t es ρ)) ∧
    ¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧ Reach σ' ρ ∧ Reach t ρ :=
  let h := Dist.conflicting_events (B1 := B1) (B2 := B2) h1 hno h2
  ⟨h.1, h.2.1, h.2.2, Dist.conflicting_events_reach h1 hno h2⟩

/-- Paragraph "Locks in a shared-nothing database": two-phase commit combines
local prepares with the coordinator's monotone decision whether all owners
prepared.

  Lean, for the decision (`CAP/TwoPhaseCommit.lean`): inputs record the votes
  of `n` fixed participants (`none` until received; a received vote does not
  change), outputs are `undecided ≼ commit, abort`, and `P` aborts on a no vote,
  commits when all voted yes, and is undecided otherwise.  This is a monotone
  function, hence consistent.  Every decision at a commitment-free reachable
  state is exposable, so its output event is available under the empty basis:
  the decision step itself applies no commitment.  The prepare half belongs to the owners'
  specifications; messages, logging, and blocking are not modeled here. -/
theorem «sec:systems/two-phase-commit» (n : Nat) :
      (CAP.voteSpec n).Functional ∧ (CAP.voteSpec n).MonotoneF ∧ (CAP.voteSpec n).Consistent ∧
        (∀ τ : State (CAP.voteSpec n), ReachableCF τ → ∀ d,
          ∀ hd : τ.R τ.cur d, Exposable τ d ∧
            SysStep (fun _ => False) τ (.output d) (outState τ d hd)) := by
    refine ⟨CAP.voteSpec_functional n, CAP.voteSpec_monotone n, CAP.voteSpec_consistent n, ?_⟩
    intro τ hr d hd
    have he := CAP.voteSpec_exposable n τ hr d hd
    exact ⟨he, eps_step_iff.2 ⟨hd, he, rfl, rfl⟩⟩

/-- Paragraph "Locks in a shared-nothing database": "The coordinator detects
whether the owners' commitments agree and aborts when they do not.  It does not
make the owners agree."  Lean, for the
decision of `CAP/TwoPhaseCommit.lean` (each vote reports whether the owner's
prepare succeeded): the decision is `abort` exactly when some received vote is
no and `commit` exactly when every vote is yes, so once every vote is in it
aborts exactly when the votes do not all say yes.  "Does not make the owners
agree" follows from the monotone decision in `«sec:systems/two-phase-commit»`;
that a yes vote reports a successful local prepare is the protocol, not
modeled. -/
theorem «sec:systems/two-phase-commit-detects» {n : Nat} (v : CAP.Votes n) :
    (CAP.decide2PC v = .abort ↔ ∃ p, v p = some false) ∧
    (CAP.decide2PC v = .commit ↔ ∀ p, v p = some true) ∧
    ((∀ p, v p ≠ none) → (CAP.decide2PC v = .abort ↔ ¬ ∀ p, v p = some true)) :=
  CAP.decide2PC_detects v

/-- Paragraph "Locks in a shared-nothing database": "If the coordinator
instead aborts on timeout before the last vote arrives, that abort applies
another commitment, like closing the polls."  (CIDR version: "A coordinator that aborts on timeout,
before the last vote arrives, issues a commitment, like closing the polls".)

Lean (`CAP/TimeoutAbort.lean`), on the decision `voteSpec` of
`«sec:systems/two-phase-commit»`: at `σ_P(v)` with vote `p` missing,
closing the polls (`Figures.closePolls`, a commitment) applies; it is a commitment;
every input `k ⪰ v` with `k p = some b`, for `b` yes or no, had the row
`(k, decide2PC k)` and keeps none; the only rows left are `(v, decide2PC v)`
(with the polls closed, `undecided` is final: abort).  At `yy·` the struck
rows include `(yyy, commit)` and `(yyn, abort)`. -/
theorem «sec:systems/2pc-timeout-abort» {m : Nat} (v : CAP.Votes m) (p : Fin m)
    (hp : v p = none) :
    CAP.Timeout.cp.f (canon (CAP.voteSpec m) v) =
        some (Figures.closeState (canon (CAP.voteSpec m) v)) ∧
    (∀ σ τ : State (CAP.voteSpec m), CAP.Timeout.cp.f σ = some τ →
      ∀ k, (∃ u, σ.R k u ∧ ¬ τ.R k u) → ∀ w, ¬ τ.R k w) ∧
    (∀ (b : Bool) (k : CAP.Votes m), v ≼ k → k p = some b →
      (canon (CAP.voteSpec m) v).R k (CAP.decide2PC k) ∧
        ∀ u, ¬ (Figures.closeState (canon (CAP.voteSpec m) v)).R k u) ∧
    (∀ k u, (Figures.closeState (canon (CAP.voteSpec m) v)).R k u ↔
      (k = v ∧ u = CAP.decide2PC v)) :=
  CAP.Timeout.timeout_closes_expansions v p hp

  /-- A timeout before the final vote applies the nonempty poll-closing
  commitment.  The commitment removes rows for canonical runs containing late
  votes. -/
theorem «sec:systems/2pc-timeout-abort-local» :
      let c : Commitment (CAP.voteSpec 3) := Dist.ofCAP CAP.Timeout.cp
      ∃ τ, c.app (canon (CAP.voteSpec 3) CAP.Timeout.yyN) = some τ ∧
        ∃ k x ρ, (canon (CAP.voteSpec 3) CAP.Timeout.yyN).R k x ∧ ¬ τ.R k x ∧
          Exec (canon (CAP.voteSpec 3) CAP.Timeout.yyN) [.input k, .output x] ρ ∧ ρ.cur = k := by
    let c : Commitment (CAP.voteSpec 3) := Dist.ofCAP CAP.Timeout.cp
    have happ0 := (CAP.Timeout.timeout_closes_expansions CAP.Timeout.yyN 2 rfl).1
    have happ : c.app (canon (CAP.voteSpec 3) CAP.Timeout.yyN) =
        some (Figures.closeState (canon (CAP.voteSpec 3) CAP.Timeout.yyN)) := happ0
    refine ⟨_, happ, ?_⟩
    exact «prop:commitment-conflict/second-run» (B := fun _ => True) (es := [])
      (σ := canon (CAP.voteSpec 3) CAP.Timeout.yyN) (τ := _) (c := c) (.nil _) happ

end CC.Paper
