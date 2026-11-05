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
# Paper §4.1–4.4: Distributed Execution (statement layer)

Covers `sections/distributed-histories.tex` (§4.1 Distributed histories, §4.2
Distributed consistency, with the paragraph *Message data*) and
`sections/distributed.tex` from §4.3 Systems through the end of §4.4
Coordination (it stops before §4.5 The Complete CAP Theorem).  The paragraph
*Exchanging outputs* and the proofs of §4 are in Appendix B
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
  and only if it has distributed consistency."

  The paper's scope caveat names the assumption explicitly: "The converse in
  Proposition `prop:distributed-consistency` assumes unrestricted placement:
  participants have no assigned roles at this level, so any spec run may occur
  at any participant."  The placement-sensitive alternative is Appendix
  `app:deployment`. -/
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

/-- "Under Lifted Monotonicity, this confluence has a concrete witness.  For participant runs with common input extension `j`, the survivor test supplies a
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

/-! ## Systems (§4.3, `sec:systems`) -/

/-- "The registrar … emits `⊥` and closes the polls in the same event
(Figure election-frames(d)); the output event for `⊥` does not require the
poll-closing commitment.  Closing the polls is the registrar's design decision,
as fixing orderings is 2PL's."

Lean: under any basis containing `closePolls`, `Out_{[closePolls]}(⊥)` from
`σ_P(ab·)` is legal and ends at panel (d); yet `⊥` is a legal output there and
  `Excluded_o` is empty, so `output(⊥)` needs no commitment. -/
theorem «sec:systems/registrar» :
    (∀ B : CommitmentBasis CALM.elec, B Figures.closePolls →
      SysStep B (canon CALM.elec CALM.bab) (.output [Figures.closePolls] .bot)
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
participant of every finite participant set and initial inputs, as §4.5 later
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

/-- After Def. `def:system`: "A system thus implements one spec.  Its
participants may behave differently, and a deployment may limit what each one
emits (Appendix `app:deployment`), but all of them work from the same table and
basis.  Systems for different specs compose as components
(Section `sec:proper-coordination`)."  Lean: `CAP.System sp D` carries one
specification `sp` and one basis; its strategies `strat n init p` may differ
by participant.  A deployment `Deploy.Deployment sp n` gives participant `p` a
table `A p` inside `sp.P`.  The system is the component
`Components.Component.ofSystemOn Sys N` of `sp`, with the system's basis and
the participant runs of its produced histories as admitted runs. -/
theorem «sec:systems/one-specification» {sp : Spec I O} {D : Type} (Sys : CAP.System sp D)
    (N : Nat → Prop) (location : Option Components.LocationForm) :
    (Components.Component.ofSystemOn Sys N location).basis =
        (fun c => Sys.basis (Dist.toCAP c)) ∧
      (∀ r, (Components.Component.ofSystemOn Sys N location).accepts r →
        SysExec (fun c => Sys.basis (Dist.toCAP c)) (canon sp r.input) r.events r.final) ∧
      ∀ (n : Nat) (Dp : Deploy.Deployment sp n) p k u, Dp.A p k u → sp.P k u :=
  ⟨rfl, fun r h => ((Components.Component.ofSystemOn Sys N location).sound r h).legal,
    fun _ Dp => Dp.sub⟩

/-- **Def. output event, commitment-sufficient output event** (`def:system-output-event`).
"An output event `Out_γ(o)` applies a sequence `γ = c₁⋯cₙ` of commitments,
each `c_m` defined at the state its predecessors leave, and then subsumes
rows and emits `o`, all atomically.  The sequence may be empty, written
`ε`.  Write `R_c` for the table after `γ` is applied.  The event is legal
when `o` is a legal output at `(i, R_c)`: Eq. lifted-validity holds.  The event
subsumes those discarded rows and ends at `(i, R_c[out ⪰ o])`."

Lean: `SysStep B σ (.output γ o) τ` (also covering input events, unchanged).
Eq. lifted-validity at the committed state is exactly `Exposable σc o`. -/
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

/-- After Def. `def:commitment-event`: "A commitment event lets a system decide
before any output needs the decision.  The environment observes nothing from
it."  Lean: a commitment event is exactly a nonempty basis sequence applied in
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

/-- **Eq. `eq:lifted-validity`**: "`(k,x) ∈ R_c ∖ R_c[out ⪰ o] ⟹
∃ u ∈ R_c[out ⪰ o](k) : x ≼ u`."  At the committed state `σc` (table `R_c`),
this condition is exactly `Exposable σc o`, the legality premise of
`SysStep.output`. -/
theorem «eq:lifted-validity» {sp : Spec I O} (σc : State sp) (o : O) :
    Exposable σc o ↔
      ∀ k x, σc.R k x → ¬ outputTable σc o k x → ∃ u, outputTable σc o k u ∧ x ≼ u :=
  ⟨fun h k x hx hn => let ⟨u, hu, hou, hxu⟩ := h k x hx (fun hox => hn ⟨hx, hox⟩)
      ⟨u, ⟨hu, hou⟩, hxu⟩,
   fun h k x hx hn => let ⟨u, ⟨hu, hou⟩, hxu⟩ := h k x hx (fun hk => hn hk.2)
      ⟨u, hu, hou, hxu⟩⟩

  /-- "A legal `Out_γ(o)` issues at least the commitments of the `output(o)` of
  Sections functional-calm–complete-calm: its commitments remove the rows in
  `Excluded_o` (Lemma canonical-commitment-normal-form)…"

Lean: Lemma containment (1) (`CC.containment`): the event keeps the current
input, `o ∈ R(i)`, the end table is inside `R[out ⪰ o]`, and the state `σc`
left by `γ` has none of the rows of `Excluded_o`. -/
theorem «sec:systems/legal-event-containment» {sp : Spec I O} {B : CommitmentBasis sp}
    {σ τ : State sp} {γ : List (Commitment sp)} {o : O} (h : SysStep B σ (.output γ o) τ) :
    τ.cur = σ.cur ∧ σ.R σ.cur o ∧ (∀ k u, τ.R k u → σ.R k u ∧ o ≼ u) ∧
    ∃ σc, ApplySeq γ σ σc ∧ ∀ k x, Excluded σ o k x → ¬ σc.R k x :=
  containment h

/-- "… and `output(o)` is the case in which they remove exactly those."

Lean: `κ_o` is `[x_o]` when `Excluded_o ≠ ∅`, and empty otherwise; the canonical steps `CanonStep` (under `B_P`, output
events `Out_{κ_o}(o)`) are exactly the steps of §§2–3 after erasing `γ`. -/
theorem «sec:systems/output-is-canonical-event» {sp : Spec I O} :
    (∀ (σ : State sp) (o : O), kappa σ o =
      (if ∃ k x, Excluded σ o k x then [canonicalCommitment o] else [])) ∧
    (∀ (σ τ : State sp) (e : SEvent sp), CanonStep σ e τ →
      ∃ e' : Event I O, e.erase = some e' ∧ Step σ e' τ) ∧
    (∀ (σ τ : State sp) (e : Event I O), Step σ e τ →
      ∃ e' : SEvent sp, e'.erase = some e ∧ CanonStep σ e' τ) :=
  ⟨fun _ _ => rfl, fun _ _ _ => canonStep_step, fun _ _ _ => step_canonStep⟩

/-- "The environment observes `o`, not `γ`."  Together with Def. `def:system`:
a system's output events are commitment-sufficient output events `Out_γ(o)` with `γ` drawn from its
basis.

Lean: in the `CC.CAP` history model an output event `out γ o` is a basis check,
`applySeq`, and a legal-output `output(o)` step at the committed state; this is
exactly `SysStep` (first conjunct).  Erasure keeps `o` and drops `γ` (second
conjunct). -/
theorem «sec:systems/system-histories» {sp : Spec I O} {B : CommitmentBasis sp} {σ τ : State sp}
    {γ : List (Commitment sp)} {o : O} :
    (SysStep B σ (.output γ o) τ ↔
      (∀ c ∈ γ, B c) ∧ ∃ σc, CAP.applySeq σ (γ.map Dist.toCAP) = some σc ∧
        Step σc (.output o) τ ∧ Exposable σc o) ∧
    (SEvent.output γ o).erase = some (Event.output o : Event I O) :=
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

/-- *Canonical runs suffice.*  "Locks, timestamps, quorums, and consensus
differ in how and when they decide.  Yet every output event of any system
removes at least the rows that the canonical event for its output removes
(Lemma canonical-commitment-normal-form), and every run under any basis has an
observably equivalent canonical run: one that accepts the same inputs, emits
the same outputs, and keeps at least the original's rows after each event; its
commitment events erase to nothing (Lemma canonical-equivalent, Appendix
bases).  In the remainder of the paper we therefore judge consistency on
canonical runs."

Lean: the first clause is `«sec:systems/legal-event-containment»` (Lemma
`lem:canonical-commitment-normal-form`); this entry is the second, as
`«lem:canonical-equivalent»`; `Lockstep` records the per-event containment
(a commitment event of the original is matched by no canonical event), and
`SEvent.erase (.commitment γ) = none`, so commitment events disappear from the
erasure `es.filterMap SEvent.erase`. -/
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

Lean: for any commitment basis, a legal output has a legal empty-commitment
output event; every row that event removes is in `Subsumed_o`.  Canonical Run
Universality (`«sec:systems/canonical-equivalent»`) lifts the canonical account
to arbitrary runs under a basis. -/
theorem «cor:free-eager-output» {sp : Spec I O} (B : CommitmentBasis sp)
    (σ : State sp) (o : O) (ho : σ.R σ.cur o) (hlegal : Exposable σ o) :
    SysStep B σ (.output [] o) (outState σ o ho) ∧
      ∀ k x, σ.R k x → ¬ outputTable σ o k x → Subsumed σ o k x := by
  refine ⟨eps_step_iff.2 ⟨ho, hlegal, rfl, rfl⟩, ?_⟩
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
`[B,A,C]`.  Suppose 2PL later emits `[A,C,B]`; its output event commits all
three transactions and orders `A` before `C` before `B`.  The canonical run
can emit the same output because that row was present all along.  Every row
retained afterward extends `[A,C,B]`, so it satisfies all of 2PL's decisions,
including the earlier order of `A` before `B`.  Thus the canonical final table
is contained in 2PL's, while Canonical Run Universality gives the reverse
containment.  The tables are equal: the lock made the `A`-before-`B` decision
earlier than the output required."

Lean (`CC.Txn.Partial.CommitEx.example_commitment_event_ABC`), at any input `k`
whose transactions `A`, `B`, `C` have each issued their operations and requested
commit; rows are serial orders without aborts or reads:
(a) the commitment event `commit([order(A,B)])` is a legal `B_2PL` step from
the canonical state `σ₀` to `σ₁`; `σ₁` keeps exactly the rows of `σ₀` with a
complete output extension in `σ₀` that does not commit `B` before `A` (aborting `A`
or `B` counts), so it keeps `[A,B,C]` and removes `[B,A,C]`;
(b) the canonical run stays at `σ₀`, which has `[B,A,C]`;
(c) 2PL's
`Out_[TxCommit(A),TxCommit(B),TxCommit(C),order(A,C),order(C,B)]([A,C,B])`
is a legal `B_2PL` step from `σ₁`; the canonical run can emit `[A,C,B]`
because that row was present at `σ₀`.  Every row it retains afterward extends
`[A,C,B]`, hence satisfies those five commitments and the earlier `order(A,B)`;
(d) the canonical final table is therefore contained in 2PL's, while Canonical
Run Universality gives the reverse containment.  The two runs end at the same
state and form a `Lockstep` pair whose commitment event is matched by no
canonical event. -/
theorem «sec:systems/canonical-example» {T K : Type} {A B C : T} {k : Txn.Partial.Inp T K}
    (h : Txn.Partial.Tri k A B C) :
    let σ0 := Txn.Partial.σ3 k
    let o2 := Txn.Partial.CommitEx.o2 (K := K) A B C
    let γ2 := Txn.Partial.CommitEx.γ2 (K := K) A B C
    let row := fun (l : List T) => Txn.Partial.full (K := K) (Txn.Partial.mk l fun _ => False)
    ∃ σ1 τ2 τ2' : State (Txn.Partial.spec (T := T) (K := K) false),
      -- (a)
      SysStep Txn.Partial.basis2PL σ0 (.commitment [Txn.Partial.order A B]) σ1 ∧ σ1.cur = k ∧
      (∀ k' w, σ1.R k' w ↔ σ0.R k' w ∧
        ∃ c, σ0.R k' c ∧ Txn.Partial.Decides false k' c.o ∧ w ≼ c ∧ ¬ c.o.lt B A) ∧
      σ1.R k (row [A, B, C]) ∧ ¬ σ1.R k (row [B, A, C]) ∧
      -- (b)
      σ0.R k (row [B, A, C]) ∧
      -- (c)
      SysStep Txn.Partial.basis2PL σ1 (.output γ2 o2) τ2 ∧
      (¬ ∃ τ, SysStep Txn.Partial.basis2PL σ1
        (.output [Txn.Partial.commit A, Txn.Partial.commit B, Txn.Partial.commit C] o2) τ) ∧
      CanonStep σ0 (.output (kappa σ0 o2) o2) τ2' ∧
      -- (d)
      τ2 = τ2' ∧
      Lockstep Txn.Partial.basis2PL σ0 [.commitment [Txn.Partial.order A B], .output γ2 o2] τ2
        σ0 [.output (kappa σ0 o2) o2] τ2' :=
  Txn.Partial.CommitEx.example_commitment_event_ABC h

/-! ## Coordination (§4.4, `sec:coordination`) -/

/-- §4.4: "Having separated a system's observable behavior from when and
how it makes commitments, we now ask which commitments require coordination.
A commitment need not. Suppose a scheduler is constrained always to order `A`
before `B`. Its `order(A,B)` action is a commitment because it removes the
permitted `B`-before-`A` rows, but no run admitted by that scheduler contradicts
the decision. Relative to all runs permitted by the spec, it does require
coordination."  "The proposition says what a coordination mechanism must
accomplish: prevent a commitment and a run that contradicts it from occurring
independently.  The definitions diagnose the requirement, not its
implementation.  Mutexes, locks, atomic instructions, agreement protocols,
ownership, and sequencers are familiar implementations.  Using one need not
apply a commitment."  At the canonical state of any full ballot, the
poll-closing commitment `closePolls` is undefined (it would remove no row). -/
theorem «sec:coordination/closing-after-voting» (i : CALM.Ballots)
    (hfull : i.b1.isSome ∧ i.b2.isSome ∧ i.b3.isSome) :
    (Figures.closePolls (sp := CALM.elec)).app (canon CALM.elec i) = none :=
  Figures.Elec.close_after_voting i hfull

/-- **Def. contradicting run** (`def:contradicts`).  "Let a specification event of a run
`r` apply a commitment.  A run `r'` contradicts that commitment if it accepts
an input whose fiber the commitment emptied, or emits an output whose row the
commitment removed."  The events that apply commitments are output events `Out_γ(o)`
and commitment events `Apply(γ)`.

Lean (`CC.CAP` model): `CAP.Contradicts emits accepts σ σc`, for commitments
taking `σ` to `σc` and runs described by the outputs they emit at each current
input (`emits k x`) and the inputs they accept (`accepts k`): some removed row
`(k,x)` is emitted at current input `k`, or some excluded input `k` (one whose
remaining rows are all removed) is accepted. -/
abbrev «def:contradicts» {sp : Spec I O} (emits : I → O → Prop) (accepts : I → Prop)
    (σ σc : State sp) : Prop :=
  CAP.Contradicts emits accepts σ σc

  /-- **Def. `def:coordination`** (Coordination-requiring commitment).
  "We distinguish the behavior permitted by a spec from the behavior
  admitted by a particular system.  Write `𝓡_P^⊤` for all canonical runs of
  `P`.  By Canonical Run Universality it is maximal at the observable
  interface: every run under any commitment basis has the same input and
  output events as some run in `𝓡_P^⊤`.  A system `A` implementing `P` may
  admit fewer such behaviors because its strategies restrict which events it
  can perform; write `𝓡_A` for the runs it produces.  A commitment requires
  coordination relative to `𝓡` when some run in `𝓡` contradicts it."

Lean, for a system: the commitments taking `σ` to `σc` are contradicted
(`«def:contradicts»`) by the runs of `Sys`: some produced history emits a
removed row (`SysEmits`) or accepts an excluded input (`SysAccepts`); produced
histories range over all inputs the adversarial environment may supply. -/
abbrev «def:coordination» {sp : Spec I O} {D : Type} (Sys : CAP.System sp D)
    (σ σc : State sp) : Prop :=
  CAP.Contradicts (CAP.SysEmits Sys) (CAP.SysAccepts Sys) σ σc

/-- **Def. `def:distributed-coordination`** (Distributed coordination).
"Suppose participant `p` applies a commitment in a history.  The commitment
requires distributed coordination relative to `𝓡` when some run in `𝓡` at
another participant `q ≠ p` of that history contradicts it."

Lean: the commitments taking `σ` to `σc`, applied by participant `p` of `H`,
are contradicted by a participant `q ≠ p` of `H` (`OtherEmits`,
`OtherAccepts`). -/
abbrev «def:distributed-coordination» {sp : Spec I O} {D : Type} {n : Nat}
    (init : Fin n → I) (H : CAP.History sp D n) (p : Fin n) (σ σc : State sp) : Prop :=
  CAP.Contradicts (CAP.OtherEmits init H p) (CAP.OtherAccepts H p) σ σc

/-- Legacy sub-label pointing at `«def:distributed-coordination»`. -/
abbrev «def:coordination/distributed» {sp : Spec I O} {D : Type} {n : Nat}
    (init : Fin n → I) (H : CAP.History sp D n) (p : Fin n) (σ σc : State sp) : Prop :=
  CAP.Contradicts (CAP.OtherEmits init H p) (CAP.OtherAccepts H p) σ σc

/-- Def. `def:coordination`, for a specification (`𝓡` the canonical runs): a
run applies a commitment that requires coordination exactly when it applies a
commitment at all (`Coordinates`: some output event has `γ ≠ ε`, or there is a
commitment event); see `«prop:canonical-contradiction»`. -/
abbrev «def:coordination/specification» {sp : Spec I O} (es : List (SEvent sp)) : Prop :=
  Coordinates es

/-- **Def. coordination-free** (`def:coordination-free`).  "A run or history is
coordination-free relative to `𝓡` when it applies no commitment that requires
coordination relative to `𝓡`."

Lean, for a system: `System.CoordinationFree` says the commitments of every
output event and every commitment event of every produced history are local
(`LocalEvent`), which is the negation of `«def:coordination»`
(`«def:coordination-free/local-iff»`). -/
abbrev «def:coordination-free» {sp : Spec I O} {D : Type} (Sys : CAP.System sp D) : Prop :=
  Sys.CoordinationFree

/-- Def. `def:coordination-free`: an event is local (`LocalEvent`) exactly when
its commitments do not require coordination relative to the system's runs
(`«def:coordination»`); within a history, `LocalInH` is the negation of
requiring distributed coordination (`«def:coordination/distributed»`). -/
theorem «def:coordination-free/local-iff» {sp : Spec I O} {D : Type} :
    (∀ (Sys : CAP.System sp D) (σ σc : State sp),
      CAP.LocalEvent Sys σ σc ↔ ¬ «def:coordination» Sys σ σc) ∧
    (∀ {n : Nat} (init : Fin n → I) (H : CAP.History sp D n) (p : Fin n) (σ σc : State sp),
      CAP.LocalInH init H p σ σc ↔ ¬ «def:coordination/distributed» init H p σ σc) :=
  ⟨CAP.localEvent_iff_not_contradicts, CAP.localInH_iff_not_contradicts⟩

/-- Def. `def:coordination-free`, distributed: no commitment of an output or
commitment event of a produced history requires distributed coordination.  Lean:
`System.CoordinationFreeH` (every such event is `LocalInH`). -/
abbrev «def:coordination-free/distributed» {sp : Spec I O} {D : Type} (Sys : CAP.System sp D) :
    Prop :=
  Sys.CoordinationFreeH

/-- Def. `def:coordination-free`: a coordination-free system has no distributed
coordination. -/
theorem «def:coordination-free/distributed-of-free» {sp : Spec I O} {D : Type}
    {Sys : CAP.System sp D} (h : «def:coordination-free» Sys) :
    «def:coordination-free/distributed» Sys :=
  CAP.coordinationFree_to_H h

/-- **Proposition `prop:canonical-contradiction`** (Canonical runs contradict
every commitment).  "Every commitment applied in a run from a canonical state
`σ_P(i)` is contradicted by a canonical run from `σ_P(i)`."

Lean states the output-row witness directly: an applied commitment removes
some `(k,x)`, and the canonical run from the same `σ_P(i)` accepts `k` and
emits `x`.  This witnesses `CAP.Contradicts` through its output clause. -/
theorem «prop:canonical-contradiction» {sp : Spec I O} {B : CommitmentBasis sp}
    {i : I} {es : List (SEvent sp)} {σ τ : State sp} {c : Commitment sp}
    (hrun : SysExec B (canon sp i) es σ) (happ : c.app σ = some τ) :
    ∃ k x ρ, σ.R k x ∧ ¬ τ.R k x ∧
      Exec (canon sp i) [.input k, .output x] ρ ∧ ρ.cur = k := by
  obtain ⟨k, x, hx, hnx⟩ := c.removes σ τ happ
  have hik : i ≼ k := (hrun.sub k x hx).2
  obtain ⟨ρ, he, hc⟩ := CAP.canonical_run_contradicts hik (σ.sub k x hx)
  exact ⟨k, x, ρ, hx, hnx, he, hc⟩

  /-- Supporting form: from `σ_P(i)` with `i ≼ k`, the canonical run
  `input(k) output(x)` accepts `k` and emits any `x ∈ P(k)` at current input
  `k`. -/
theorem «prop:canonical-contradiction/canonical-run» {sp : Spec I O} {i k : I} {x : O}
    (hik : i ≼ k) (hx : sp.P k x) :
    ∃ τ : State sp, Exec (canon sp i) [.input k, .output x] τ ∧ τ.cur = k :=
  CAP.canonical_run_contradicts hik hx

/-- **Corollary `cor:canonical-coordination`** (Canonical coordination).
"Relative to `𝓡_P^⊤`, a run is coordination-free if and only if it applies no
commitment.  Output subsumption remains permitted.  Given two distinct
participants both initialized at `i`, the run applying a commitment from
`σ_P(i)` and a canonical run that contradicts it can occupy separate
participants in a message-free history.  The commitment therefore requires
distributed coordination relative to that history's runs."

Lean: `CoordFree es ↔ ¬ Coordinates es`; `Coordinates` means that an output
event has `γ ≠ ε` or a commitment event occurs. -/
theorem «cor:canonical-coordination» {sp : Spec I O} (es : List (SEvent sp)) :
    CoordFree es ↔ ¬ Coordinates es :=
  coordFree_iff_not es

/-- Def. `def:coordination-free`: coordination-free is the negation of coordinates,
and coordination-free runs under any basis are exactly the commitment-free
executions (`ExecCF`) of §3 after erasing `γ`.  `Out_ε(o)` ends at
`R[out ⪰ o]`, so it may still subsume rows (`«lem:canonical-commitment-normal-form»`
(3) in the App. C file). -/
theorem «def:coordination-free/commitment-free-runs» {sp : Spec I O} :
    (∀ es : List (SEvent sp), CoordFree es ↔ ¬ Coordinates es) ∧
    (∀ (B : CommitmentBasis sp) (σ τ : State sp) (es : List (SEvent sp)),
      SysExec B σ es τ → CoordFree es → ExecCF σ (es.filterMap SEvent.erase) τ) ∧
    (∀ (B : CommitmentBasis sp) (σ τ : State sp) (es : List (Event I O)), ExecCF σ es τ →
      ∃ es' : List (SEvent sp), es'.filterMap SEvent.erase = es ∧ CoordFree es' ∧
        SysExec B σ es' τ) :=
  ⟨coordFree_iff_not, fun _ _ _ _ h hf => coordFree_execCF h hf,
    fun B _ _ _ h => execCF_coordFree B h⟩

  /-- **Prop. contradicting runs cannot reconcile at the conflict input**
  (`thm:commitments-require-coordination`).  "Consider a run that applies a
  commitment and another run that contradicts it at input `k`.  Their resulting
  states have no common continuation to a state `(k,R')`."

  Lean: `CommitmentContradictsAt σ σc τ k` covers both proof cases.  Its first
  clause is an emitted output `x` whose row the commitment removed; its second
  is an accepted input whose fiber the commitment emptied.  The conclusion
  permits arbitrary, independent bases for the two continuations. -/
  theorem «thm:commitments-require-coordination» {sp : Spec I O}
      {B1 B2 : CommitmentBasis sp} {c : Commitment sp} {σ σc τ : State sp} {k : I}
      (happ : c.app σ = some σc) (hcontra : Dist.CommitmentContradictsAt σ σc τ k) :
      ¬ ∃ ρ : State sp, ρ.cur = k ∧
          (∃ es, SysExec B1 σc es ρ) ∧ (∃ es, SysExec B2 τ es ρ) :=
    Dist.commitment_contradiction_sysExec happ hcontra

  /-- Prop. `thm:commitments-require-coordination`, with continuations in the
  transition system of Sections 2--3. -/
  theorem «thm:commitments-require-coordination/reach-general» {sp : Spec I O}
      {c : Commitment sp} {σ σc τ : State sp} {k : I}
      (happ : c.app σ = some σc) (hcontra : Dist.CommitmentContradictsAt σ σc τ k) :
      ¬ ∃ ρ : State sp, ρ.cur = k ∧ Reach σc ρ ∧ Reach τ ρ :=
    Dist.commitment_contradiction_reach happ hcontra

  /-- Supporting output-only form of Prop. `thm:commitments-require-coordination`.
under different bases. -/
theorem «thm:commitments-require-coordination/any-bases» {sp : Spec I O}
    {B B' B1 B2 : CommitmentBasis sp} {σ σ' t : State sp} {γ γ' : List (Commitment sp)} {o x : O}
    (h1 : SysStep B σ (.output γ o) σ') (hno : ∀ w, σ'.R σ.cur w → ¬ x ≼ w)
    (h2 : SysStep B' σ (.output γ' x) t) :
    ¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧
        (∃ es, SysExec B1 σ' es ρ) ∧ (∃ es, SysExec B2 t es ρ) :=
  Dist.conflicting_outputs2 h1 hno h2

/-- Prop. `thm:commitments-require-coordination`, with continuations in the
transition system of §§2–3. -/
theorem «thm:commitments-require-coordination/reach» {sp : Spec I O} {B B' : CommitmentBasis sp}
    {σ σ' t : State sp} {γ γ' : List (Commitment sp)} {o x : O}
    (h1 : SysStep B σ (.output γ o) σ') (hno : ∀ w, σ'.R σ.cur w → ¬ x ≼ w)
    (h2 : SysStep B' σ (.output γ' x) t) :
    ¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧ Reach σ' ρ ∧ Reach t ρ :=
  conflicting_outputs_reach h1 hno h2

/-- Prop. `thm:commitments-require-coordination` with the first event any
event, in particular a commitment event `apply(γ)`: "let one run perform an
output or commitment event after which no output at `i` extends `x`".

Lean: for any event `e` taking `σ` to `σ'` with no output at `i` extending `x`,
and `Out_{γ'}(x)` taking `σ` to `t`, no state with current input `i` is
reachable from both, under any bases or in the transition system of §§2–3; if
`e` is an output or commitment event, its commitment sequence is nonempty. -/
theorem «thm:commitments-require-coordination/any-event» {sp : Spec I O}
    {B B' B1 B2 : CommitmentBasis sp} {σ σ' t : State sp} {e : SEvent sp}
    {γ' : List (Commitment sp)} {x : O}
    (h1 : SysStep B σ e σ') (hno : ∀ w, σ'.R σ.cur w → ¬ x ≼ w)
    (h2 : SysStep B' σ (.output γ' x) t) :
    (∀ γ o, e = .output γ o → γ ≠ []) ∧ (∀ γ, e = .commitment γ → γ ≠ []) ∧
    (¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧
        (∃ es, SysExec B1 σ' es ρ) ∧ (∃ es, SysExec B2 t es ρ)) ∧
    ¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧ Reach σ' ρ ∧ Reach t ρ :=
  let h := Dist.conflicting_events (B1 := B1) (B2 := B2) h1 hno h2
  ⟨h.1, h.2.1, h.2.2, Dist.conflicting_events_reach h1 hno h2⟩

/-- "The proposition rules out reconciliation at `i`, not forever.  For
example, suppose `i ≺ j`, `P(i) = {o,x}` with `o` and `x` incomparable, and
`P(j) = {u}` with `u` extending both.  The states that emit `o` and `x` cannot
be reconciled at `i`, although accepting `j` reconciles them.  As explained
after Definition `def:consistency`, consistency nevertheless counts the
conflict at `i` as a failure."

Lean: the example of `CALM/TransientConflict.lean`: inputs `i ≺ j`, outputs
`o`, `x` incomparable below `u`, `P(i) = {o,x}`, `P(j) = {u}`.  From
`σ_P(i)`, the canonical events `output(o)` and `output(x)` are legal; after
`output(o)` no output at `i` extends `x`, so the two states have no common
state with current input `i`; both reach `σ_P(j)` by `input(j)`, so they are
confluent at `j`; and the specification is neither consistent nor directed at
`i` (so not Lifted Monotone). -/
theorem «thm:commitments-require-coordination/confined-to-current-input» :
    open CALM.Transient in
    Step σi (.output .o) tO ∧ Step σi (.output .x) tX ∧
    (∀ y, tO.R .i y → ¬ (Out.x ≼ y)) ∧
    (¬ ∃ ρ : State spec, ρ.cur = .i ∧ Reach tO ρ ∧ Reach tX ρ) ∧
    Step tO (.input .j) (canon spec .j) ∧ Step tX (.input .j) (canon spec .j) ∧
    ConfluentAt [tO, tX] .j ∧
    ¬ spec.Consistent ∧ ¬ spec.DirectedOutputs ∧ ¬ spec.LiftedMono :=
  open CALM.Transient in
  ⟨step_o, step_x, tO_no_refine_x, not_meet_at_i, step_j_o, step_j_x, confluent_at_j,
    not_consistent, not_directedOutputs, not_liftedMono⟩
/-- Paragraph "Locks in a shared-nothing database": "Consider a database
partitioned by key, with each key owned and locked by one participant.
Ownership can keep coordination local."

*Local coordination.*  "Ordering two transactions on one key requires
coordination because, in another run, `B`'s request may arrive first and the
owner may order `B` before `A`.  Only the key's owner can produce that
contradicting run, so no distributed coordination is required."  Lean: a spec with outputs `⊥ ≤ ab, ba` (`ab`,
`ba` incomparable); emitting `ab` is a commitment (not a legal output); in the
system where only participant 0 may emit an order, another run (the owner
choosing `ba`) contradicts it, but no other participant of a history does. -/
theorem «sec:coordination/shared-nothing-single-key» (D : Type) :
    ¬ Exposable (canon CAP.ordSpec ()) .ab ∧ ¬ (CAP.ownerSys D).CoordinationFree ∧
      (CAP.ownerSys D).CoordinationFreeH :=
  ⟨CAP.ordSpec_ab_not_exposable, CAP.ownerSys_not_coordinationFree D,
    CAP.ownerSys_coordinationFreeH D⟩

/-- Paragraph "Locks in a shared-nothing database": *Distributed
coordination*: "A transaction spanning two keys is different.  Each owner
orders its own part, and the two owners can order the same pair of transactions
oppositely.  Each ordering then requires distributed coordination: the owners
must agree on one order."  Lean: when two participants may
each emit an order, some history has one emit `ab` (removing `ba`) and the
other emit `ba`, so the system is not free of distributed coordination.
"The owners must agree" is the paper's reading of that (some mechanism must
exclude one of the two events), not a separate claim.  The case that follows
is `«sec:coordination/two-phase-commit»`. -/
theorem «sec:coordination/shared-nothing-cross-key» (D : Type) :
    ¬ (CAP.twoOwnerSys D).CoordinationFreeH :=
  CAP.twoOwnerSys_not_coordinationFreeH D

/-- Paragraph "Locks in a shared-nothing database": "Two-phase commit adds
no further coordination requirement.  Each owner's prepare reflects its own
commitment, with the local coordination just described.  The coordinator then
makes the monotone decision whether all owners prepared."

Lean, for the decision (`CAP/TwoPhaseCommit.lean`): inputs record the votes
of `n` fixed participants (`none` until received; a received vote does not
change), outputs are `undecided ≼ commit, abort`, and `P` aborts on a no vote,
commits when all voted yes, and is undecided otherwise.  This is a monotone
function, hence consistent; no decision at a commitment-free reachable state
needs a commitment; and the system that emits decisions by canonical output
events is coordination-free (`CoordinationFree`), so a fortiori needs no
distributed coordination (`CoordinationFreeH`).  The prepare half is the
single-owner pattern of `«sec:coordination/shared-nothing-single-key»`; the
protocol itself (messages, logging, blocking) is not modeled.  The sentence
that follows is `«sec:coordination/two-phase-commit-detects»`. -/
theorem «sec:coordination/two-phase-commit» (n : Nat) (D : Type) :
    (CAP.voteSpec n).Functional ∧ (CAP.voteSpec n).MonotoneF ∧ (CAP.voteSpec n).Consistent ∧
      (∀ τ : State (CAP.voteSpec n), ReachableCF τ → ∀ d, τ.R τ.cur d → Exposable τ d) ∧
      (CAP.respSystem (sp := CAP.voteSpec n) (D := D) (CAP.voteSpec n).P).CoordinationFree ∧
      (CAP.respSystem (sp := CAP.voteSpec n) (D := D) (CAP.voteSpec n).P).CoordinationFreeH :=
  ⟨CAP.voteSpec_functional n, CAP.voteSpec_monotone n, CAP.voteSpec_consistent n,
   CAP.voteSpec_exposable n, CAP.voteSpec_coordinationFree n D⟩

/-- Paragraph "Locks in a shared-nothing database": "The coordinator detects
whether the owners' commitments agree and aborts when they do not.  It does not
make the owners agree."  Lean, for the
decision of `CAP/TwoPhaseCommit.lean` (each vote reports whether the owner's
prepare succeeded): the decision is `abort` exactly when some received vote is
no and `commit` exactly when every vote is yes, so once every vote is in it
aborts exactly when the votes do not all say yes.  "Does not make the owners
agree" is the coordination-freedom of `«sec:coordination/two-phase-commit»`;
that a yes vote reports a successful local prepare is the protocol, not
modeled. -/
theorem «sec:coordination/two-phase-commit-detects» {n : Nat} (v : CAP.Votes n) :
    (CAP.decide2PC v = .abort ↔ ∃ p, v p = some false) ∧
    (CAP.decide2PC v = .commit ↔ ∀ p, v p = some true) ∧
    ((∀ p, v p ≠ none) → (CAP.decide2PC v = .abort ↔ ¬ ∀ p, v p = some true)) :=
  CAP.decide2PC_detects v

/-- Paragraph "Locks in a shared-nothing database": "If the coordinator
instead aborts on timeout before the last vote arrives, that abort applies
another commitment, like closing the polls."  (CIDR version: "A coordinator that aborts on timeout,
before the last vote arrives, issues a commitment, like closing the polls".)

Lean (`CAP/TimeoutAbort.lean`), on the decision `voteSpec` of
`«sec:coordination/two-phase-commit»`: at `σ_P(v)` with vote `p` missing,
closing the polls (`Figures.closePolls`, a commitment) applies; it is a commitment;
every input `k ⪰ v` with `k p = some b`, for `b` yes or no, had the row
`(k, decide2PC k)` and keeps none; the only rows left are `(v, decide2PC v)`
(with the polls closed, `undecided` is final: abort).  At `yy·` the struck
rows include `(yyy, commit)` and `(yyn, abort)`. -/
theorem «sec:coordination/2pc-timeout-abort» {m : Nat} (v : CAP.Votes m) (p : Fin m)
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

/-- Paragraph "Locks in a shared-nothing database": "The timeout decision
requires only local coordination when a single coordinator makes it.  It
requires distributed coordination when the coordinator is replicated for
fault tolerance, as in Paxos Commit."

Lean (`CAP/TimeoutAbort.lean`), for the commitment of
`«sec:coordination/2pc-timeout-abort»` (closing the polls on `voteSpec` at
`yy·`).  The decision specification is run by a system of its own, as each
stage is in the composition section; the owners' specifications are separate
systems.

*Run by the coordinator alone* (`pollClosingSys1`, whose strategies act only when
the system has one participant): the commitment requires coordination, since
another run of the coordinator from `yy·` accepts the excluded late vote `yyy`
(not `CoordinationFree`); but no history of the system applies a commitment
that another participant of the same history contradicts
(`CoordinationFreeH`): local coordination.  The general fact is
`single_coordinationFreeH`.

*Replicated* (two or more participants run `voteSpec`): any system in which
participant `0` of two, starting at `yy·`, may close the polls there is not
`CoordinationFreeH`, since the environment may deliver `yyy` to the other
participant; `pollClosingSysRepl` (every participant at `yy·` may close the polls) is
an instance.  Distributed coordination.  Paxos Commit itself is not modeled.

Library lemmas not quoted here: the abort read as a commitment (`abortSpec`,
`abort_canonicalCommitment_yy`, `coordSys_coordinationFreeH`,
`replSys_not_coordinationFreeH`). -/
theorem «sec:coordination/2pc-timeout-abort-local» (D : Type) :
    (¬ (CAP.Timeout.pollClosingSys1 D).CoordinationFree ∧
      (CAP.Timeout.pollClosingSys1 D).CoordinationFreeH) ∧
    (∀ Sys : CAP.System (CAP.voteSpec 3) D, Sys.basis CAP.Timeout.cp →
      Sys.strat 2 (fun _ => CAP.Timeout.yyN) 0 [] (.out [CAP.Timeout.cp] .undecided) →
      ¬ Sys.CoordinationFreeH) ∧
    ¬ (CAP.Timeout.pollClosingSysRepl D).CoordinationFreeH :=
  ⟨CAP.Timeout.pollClosingSys1_local D,
   fun Sys hb hs => CAP.Timeout.pollClosing_not_coordinationFreeH Sys hb hs,
   CAP.Timeout.pollClosingSysRepl_not_coordinationFreeH D⟩

end CC.Paper
