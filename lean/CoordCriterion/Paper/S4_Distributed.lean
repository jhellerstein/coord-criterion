import CoordCriterion.Distributed.Systems
import CoordCriterion.CALM.TransientConflict
import CoordCriterion.Figures
import CoordCriterion.CAP.Coordination
import CoordCriterion.CAP.TwoPhaseCommit
import CoordCriterion.CAP.TimeoutAbort
import CoordCriterion.Appendix.TransactionBases.NoReads
import CoordCriterion.Paper.AppG_TransactionBases
import CoordCriterion.Appendix.TransactionBases.CommitEvent
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
result is named by its LaTeX label (`«def:commitment»`, `«prop:seal-or-choose»`,
…); an unlabeled claim of the text is named `«<enclosing label>/<slug>»`.  Each
docstring quotes the paper (LaTeX lightly turned into Unicode) and, where the
Lean statement reads differently, says how the two correspond.  Statements are
written out in full; the proofs are one-line references to the library
(`CoordCriterion/Distributed/*.lean`, `CAP/Model.lean`, `Figures.lean`,
`Appendix/TransactionBases/*.lean`), where the modeling choices are
documented.

Global reading conventions: sets are predicates, finite families are `List`s
or functions on `Fin n`, the participant set `P` is `Fin n`, `≼` is the
specification's order (`a ≼ b`: `b` refines/expands `a`), a state `(i,R)` is a
`State sp` with `cur = i` and table `R`, and `R[out ⪰ o]` is `outputTable σ o`.
-/

namespace CC.Paper

open CC Classical

variable {I O : Type} [PO I] [PO O]

/-! ## Distributed histories (§4.1, `sec:histories`) -/

/-- **Def. distributed history, history event, happens-before, consistent
cut** (`def:distributed-history`), the carrier.
"A distributed history `H` is a finite set of history events, each an
occurrence at one participant of a specification event, `send(m)`, or
`receive(m)` …"

Lean: participants are `Fin n`; each participant has a finite `List` of local
events (`Dist.LEv`: `io e`, `send x m`, `recv x m` with a message identifier
`x` and a message `m = (j, d) : Option I × D`, `none` playing `∅`).  The list
order *is* item 1, the total local order.  The initial inputs `i_p` are
`H.init`.  "Commitment events are a third kind of specification event, so a
distributed history may contain them" (§4.2, after Def.
`def:commitment-event`); histories a system produces are modeled with them as
`CAP.LEv.cmt γ` in `CAP/Model.lean`, whose well-formedness includes them in
item 3. -/
abbrev «def:distributed-history» (I O D : Type) (n : Nat) := Dist.History I O D n

/-- Def. `def:distributed-history`, items 2–3: "for each receive, a matching
send of the same message at another participant, each send matching at most
one receive; and for each participant `p`, its specification events, in local
order, form a defined transition sequence from `σ_S(i_p)`".

Lean: `History.WF`.  "Each send matching at most one receive" is read as
"send identifiers are unique"; `CC.Dist.WF0` drops this (see
`«prop:distributed-consistency/literal-matching»`). -/
abbrev «def:distributed-history/well-formed» {D : Type} {n : Nat} (sp : Spec I O)
    (H : Dist.History I O D n) : Prop :=
  H.WF sp

/-- Def. `def:distributed-history`: "Happens-before is the transitive closure of
the local orders and of each send preceding its matching receive." -/
abbrev «def:distributed-history/happens-before» {D : Type} {n : Nat}
    (H : Dist.History I O D n) : Dist.Pos n → Dist.Pos n → Prop :=
  H.HB

/-- Def. `def:distributed-history`: "A consistent cut `C` is a subset of history
events closed under happens-before." -/
abbrev «def:distributed-history/consistent-cut» {D : Type} {n : Nat}
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

/-- **Def. participant run, endpoint** (`def:participant-run`).  "At a
consistent cut `C`, the specification events of `C` at participant `p`, in
local order, form its participant run … whose final state we write `σ_p(C)`.
The endpoint of `C` is `end(H,C) = (σ_p(C))_{p∈P}`."

Lean: relational — `σs` *is* the endpoint when each `σs p` is the final state
of `p`'s input/output events in the cut (existence and uniqueness:
`«sec:histories/cut-determines-runs»`). -/
abbrev «def:participant-run» {D : Type} {n : Nat} (sp : Spec I O)
    (H : Dist.History I O D n) (C : Dist.Pos n → Prop) (σs : Fin n → State sp) : Prop :=
  H.Endpoint sp C σs

/-- Def. `def:participant-run`: a participant run is "a run (Definition run)". -/
theorem «def:participant-run/is-run» {D : Type} {n : Nat} {sp : Spec I O}
    {H : Dist.History I O D n} {C : Dist.Pos n → Prop} {σs : Fin n → State sp}
    (h : H.Endpoint sp C σs) : ∀ p, IsRun (σs p) :=
  h.isRun

/-- **Fig. participant-runs** (`fig:participant-runs`).  "Two histories
from `σ_a = σ_S(x··)` to `σ_1 = (xy·, R_1)` … In Figure participant-runs, the
input `xy·` reaches `q` directly or through a message from `p`.  The histories
differ, but at either cut each participant run is `input(xy·)`, so both
endpoints are `(σ_1, σ_1)`."

Lean, for the election `elec` and any message data `d`: the direct-delivery
history `H_d` and the forwarded-delivery history `H_f` (where `p = 0` sends
`m = (xy·, d)` and `q = 1` receives it) are both well formed, the endpoint of
each final cut is `(σ_S(xy·), σ_S(xy·))`, and the histories differ.  Here
`σ_1 = σ_S(xy·)`, whose table `R_1` is panel (b) of Fig. election-frames
(`CC.Figures.Elec.panel_b`). -/
theorem «fig:participant-runs» (D : Type) (d : D) :
    (Dist.Hd CALM.Res D CALM.bxd CALM.bxy).WF CALM.elec ∧
    (Dist.Hf CALM.Res CALM.bxd CALM.bxy d).WF CALM.elec ∧
    (Dist.Hd CALM.Res D CALM.bxd CALM.bxy).Endpoint CALM.elec
      (Dist.Hd CALM.Res D CALM.bxd CALM.bxy).InH (fun _ => canon CALM.elec CALM.bxy) ∧
    (Dist.Hf CALM.Res CALM.bxd CALM.bxy d).Endpoint CALM.elec
      (Dist.Hf CALM.Res CALM.bxd CALM.bxy d).InH (fun _ => canon CALM.elec CALM.bxy) ∧
    (Dist.Hd CALM.Res D CALM.bxd CALM.bxy).ev ≠ (Dist.Hf CALM.Res CALM.bxd CALM.bxy d).ev :=
  Dist.fig_participant_runs CALM.elec (by decide) ⟨_, rfl⟩ d

/-- The general form of Fig. `fig:participant-runs`: for any specification and
any `i ≼ j` with a row at `j`, both histories end at `(σ_S(j), σ_S(j))`. -/
theorem «fig:participant-runs/general» {D : Type} (sp : Spec I O) {i j : I} (hij : i ≼ j)
    (hj : ∃ u, sp.S j u) (d : D) :
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
ordered specification has distributed consistency when, for every finite
participant set, every consistent cut of every history is confluent at every
common expansion of the participants' current inputs."

Lean: for message data of type `D`; "every finite participant set" is "every
`n`" (participants `Fin n`). -/
abbrev «def:distributed-consistency» (sp : Spec I O) (D : Type) : Prop :=
  Dist.DistConsistent sp D

/-- **Prop. consistency and distributed consistency**
(`prop:distributed-consistency`).  "An ordered specification is consistent if
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
input, a specification has distributed consistency exactly when it satisfies
Lifted Monotonicity." -/
theorem «sec:distributed-consistency/lifted-monotonicity» (sp : Spec I O) (D : Type) :
    Dist.DistConsistent sp D ↔ sp.LiftedMono :=
  Dist.distConsistent_iff_liftedMono sp D

/-- **Cor. convergence** (`cor:convergence`).  "In any history of a consistent
functional specification, every participant whose current input at a
consistent cut is `j` is in state `σ_S(j)`.  Participants with the same current
input therefore agree, regardless of message paths, arrival order, or the
outputs they emitted."

Lean: `σs` is the endpoint of the cut; the first conjunct is "`σ_p(C) =
σ_S(cur)`", the second "same current input ⇒ same state". -/
theorem «cor:convergence» {D : Type} {n : Nat} {sp : Spec I O} (hc : sp.Consistent)
    (hf : sp.Functional) {H : Dist.History I O D n} {C : Dist.Pos n → Prop}
    {σs : Fin n → State sp} (hE : H.Endpoint sp C σs) :
    (∀ p, σs p = canon sp (σs p).cur) ∧
    (∀ p q, (σs p).cur = (σs q).cur → σs p = σs q) :=
  ⟨fun p => Dist.convergence hc hf hE p rfl, Dist.convergence_agree hc hf hE⟩

/-- After Cor. `cor:convergence`: "With several outputs per input this fails
even for consistent specifications: in Figure `fig:ambiguity-frames`(g), a
run that emitted `{s→s1}` has retired the route sets that omit it, while a
run at the same input that emitted nothing keeps them.  Consistency then
guarantees that such replicas can be reconciled, not that they agree."  The
traceroute specification is consistent; the run that emitted `{s→s1}` and the
canonical run end at the same input in different states (the first has
retired `{s→a}`, the second keeps it); and the two are confluent at that
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

/-- *Message data.*  "Data can influence which events occur next at the
receiver, but it never directly changes the receiver's
specification state, and nothing in the definitions above depends on it."

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
    H.CutConfluentAt sp C j ↔ ∃ u, sp.S j u ∧ ∀ p, Dist.honor (σs p).R (os p) j u :=
  Dist.honor_cut_confluent hW hC hE os hos j hj

/-! ## Systems (§4.3, `sec:systems`) -/

/-- "The registrar … emits `⊥` and closes the polls in the same event
(Figure election-frames(d)); the output event for `⊥` does not require the
poll-closing seal, so closing the polls is a design decision of the system."

Lean: under any basis containing `closePolls`, `Out_{[closePolls]}(⊥)` from
`σ_S(xy·)` is legal and ends at panel (d); yet `⊥` is exposable there and
`Sealed_⊥`, `Rejected_⊥` are empty, so `output(⊥)` needs no commitment. -/
theorem «sec:systems/registrar» :
    (∀ B : Basis CALM.elec, B Figures.closePolls →
      SysStep B (canon CALM.elec CALM.bxy) (.output [Figures.closePolls] .bot)
        Figures.Elec.panelD) ∧
    Exposable (canon CALM.elec CALM.bxy) .bot ∧
    (¬ ∃ k x, Sealed (canon CALM.elec CALM.bxy) .bot k x) ∧
    (¬ ∃ k x, Rejected (canon CALM.elec CALM.bxy) .bot k x) :=
  ⟨Figures.Elec.registrar_step, Figures.Elec.bot_alone_at_b.1,
    Figures.Elec.bot_alone_at_b.2.1, Figures.Elec.bot_alone_at_b.2.2.1⟩

/-- **Def. commitment** (`def:commitment`).  "A commitment is a partial function
on specification states that leaves the current input unchanged and removes a
nonempty set of rows, each with no remaining row at the same input that refines
it: whenever `c(i,R) = (i,R')`, we have `R' ⊊ R` and
`(k,u) ∈ R ∖ R', (k,w) ∈ R' ⟹ u ⋠ w`" (Eq. commitment-excludes).

Lean: `app : State sp → Option (State sp)` with fields `cur_eq`, `sub`,
`removes` (`R' ⊊ R`), `excludes` (Eq. commitment-excludes). -/
abbrev «def:commitment» (sp : Spec I O) := Commitment sp

/-- **Eq. `eq:commitment-excludes`**: whenever `c(i,R) = (i,R')`,
"`(k,u) ∈ R ∖ R', (k,w) ∈ R' ⟹ u ⋠ w`" (field `Commitment.excludes`). -/
theorem «eq:commitment-excludes» {sp : Spec I O} (c : Commitment sp) (σ τ : State sp)
    (h : c.app σ = some τ) :
    ∀ k u w, σ.R k u → ¬ τ.R k u → τ.R k w → ¬ (u ≼ w) :=
  c.excludes σ τ h

/-- "The seals and choices of Definitions output-event and
lifted-output-event satisfy this definition: a seal removes every row at the
inputs it seals, and a choice removes the rows in `Rejected_o`."

Lean: `sealC o`, `choiceC o : Commitment sp` (being of that type is the claim
that they satisfy Def. commitment).  `s_o` is defined at `(i,R)` exactly when
`o ∈ R(i)` and `Sealed_o ≠ ∅`, and then leaves `R ∖ Sealed_o`; `c_o` is defined
exactly when `o ∈ R(i)` and `Rejected_o ≠ ∅`, and then leaves
`R ∖ Rejected_o`.  For the seals of Def. output-event (one row per input) see
`«app:bases/canonical-are-commitments»`. -/
theorem «sec:systems/seals-and-choices-are-commitments» {sp : Spec I O} (o : O)
    (σ τ : State sp) :
    ((sealC o : Commitment sp).app σ = some τ ↔
        ∃ h : σ.R σ.cur o, (∃ k x, Sealed σ o k x) ∧ cmSealState σ o h = τ) ∧
    ((choiceC o : Commitment sp).app σ = some τ ↔
        σ.R σ.cur o ∧ (∃ k x, Rejected σ o k x) ∧ cmChooseState σ o = τ) :=
  ⟨sealApp_eq, chooseApp_eq⟩

/-- **Prop. commitments seal inputs or choose outputs** (`prop:seal-or-choose`).
"At each input where a commitment removes rows of the state it is applied to,
it either removes every row there, sealing that input, or removes some outputs
and keeps others, choosing among them."

Lean: at such an input `k`, either no row remains (seal) or some row `w`
remains that refines no removed row (choice; Eq. commitment-excludes); and not
both ("the classification is unambiguous"). -/
theorem «prop:seal-or-choose» {sp : Spec I O} (c : Commitment sp) {σ τ : State sp}
    (h : c.app σ = some τ) (k : I) (hk : ∃ u, σ.R k u ∧ ¬ τ.R k u) :
    ((∀ u, ¬ τ.R k u) ∨
      (∃ w, τ.R k w ∧ ∀ u, σ.R k u → ¬ τ.R k u → ¬ (u ≼ w))) ∧
    ¬ ((∀ u, ¬ τ.R k u) ∧ ∃ w, τ.R k w) :=
  seal_or_choose c h k hk

/-- "In a functional specification each fiber has one row, so every commitment
seals." -/
theorem «prop:seal-or-choose/functional» {sp : Spec I O} (hf : sp.Functional)
    (c : Commitment sp) {σ τ : State sp} (h : c.app σ = some τ) (k : I)
    (hk : ∃ u, σ.R k u ∧ ¬ τ.R k u) : ∀ w, ¬ τ.R k w :=
  functional_commitment_seals hf c h k hk

/-- **Def. local history, strategy** (`def:strategy`).  "A local history of participant `p` is a
finite sequence of `p`'s history events … A strategy for `p` is a
nondeterministic transition function: it maps each local history `λ` of `p` to
a set `θ_p(λ)` of output, commitment, send, and receive events of `p`, and `p`
next performs any one of them, or waits.  Input events come from the
environment, not the strategy."

Lean (the `CC.CAP` system model): a strategy for `p` is a relation from local
histories (`List (CAP.LEv sp D n)`) to next events; local events include
commitment events `CAP.LEv.cmt γ`.  Its value on input events
is ignored: `CAP.Allowed` always allows inputs. -/
abbrev «def:strategy» (sp : Spec I O) (D : Type) (n : Nat) :=
  List (CAP.LEv sp D n) → CAP.LEv sp D n → Prop

/-- **Def. system, produced history** (`def:system`).  "A system consists of a
commitment basis `ℬ`, shared by all participants, and a strategy `θ_p` for each participant `p` whose output
and commitment events apply only commitments from `ℬ`."

Lean: `CAP.System` (basis + strategies `strat n init p`, one for every
participant of every finite participant set and initial inputs, as §4.5 later
requires) with `System.BasisRespecting`.  Its commitments are
`CAP.Commitment`, equivalent to `CC.Commitment` (`CC.Dist.toCAP`,
`CC.Dist.ofCAP`).  The library's `CAP.System` does not require basis respect;
`«def:system/restrict»` shows this loses nothing. -/
abbrev «def:system» (sp : Spec I O) (D : Type) :=
  {Sys : CAP.System sp D // Sys.BasisRespecting}

/-- Def. `def:system`: "A distributed history produced by the system consists
of environment inputs and events chosen by the participants' strategies."
For a basis-respecting system this is the library's `CAP.Produced`: every
event other than an input is permitted by the strategy at the local history
before it (`CAP.allowed_iff_stratAllowed`). -/
theorem «def:system/produced» {sp : Spec I O} {D : Type} (Sys : CAP.System sp D)
    (h : Sys.BasisRespecting) (n : Nat) (init : Fin n → I) (H : CAP.History sp D n) :
    CAP.Produced Sys n init H ↔ ∀ p, CAP.Compliant (CAP.StratAllowed Sys n init p) (H p) :=
  ⟨fun hp p a e b hab => (CAP.allowed_iff_stratAllowed h n init p a e).1 (hp p a e b hab),
   fun hp p a e b hab => (CAP.allowed_iff_stratAllowed h n init p a e).2 (hp p a e b hab)⟩

/-- Def. `def:system`, generality: requiring the strategies to respect the
basis loses nothing.  Restricting any system's strategies to basis
commitments gives a basis-respecting system that allows exactly the same
events, hence produces the same histories. -/
theorem «def:system/restrict» {sp : Spec I O} {D : Type} (Sys : CAP.System sp D) :
    Sys.restrict.BasisRespecting ∧
      ∀ n init p pre e, CAP.Allowed Sys.restrict n init p pre e ↔ CAP.Allowed Sys n init p pre e :=
  ⟨Sys.restrict_basisRespecting, Sys.restrict_allowed⟩

/-- After Def. `def:system`: "A system thus implements one specification.  Its
participants may behave differently, and a deployment may limit what each one
emits (Appendix `app:deployment`), but all of them work from the same table and
basis.  Systems for different specifications compose as components
(Section `sec:proper-coordination`)."  Lean: `CAP.System sp D` carries one
specification `sp` and one basis; its strategies `strat n init p` may differ
by participant.  A deployment `Deploy.Deployment sp n` gives participant `p` a
table `A p` inside `sp.S`.  The system is the component
`Components.Component.ofSystemOn Sys N` of `sp`, with the system's basis and
the participant runs of its produced histories as admitted runs. -/
theorem «sec:systems/one-specification» {sp : Spec I O} {D : Type} (Sys : CAP.System sp D)
    (N : Nat → Prop) (location : Option Components.LocationForm) :
    (Components.Component.ofSystemOn Sys N location).basis =
        (fun c => Sys.basis (Dist.toCAP c)) ∧
      (∀ r, (Components.Component.ofSystemOn Sys N location).accepts r →
        SysExec (fun c => Sys.basis (Dist.toCAP c)) (canon sp r.input) r.events r.final) ∧
      ∀ (n : Nat) (Dp : Deploy.Deployment sp n) p k u, Dp.A p k u → sp.S k u :=
  ⟨rfl, fun r h => ((Components.Component.ofSystemOn Sys N location).sound r h).legal,
    fun _ Dp => Dp.sub⟩

/-- **Def. commitment basis, output event of a system, legal output event**
(`def:system-output-event`).  "A commitment basis is a set `ℬ` of commitments.
… An output event `Out_γ(o)` under a basis `ℬ` applies a finite, possibly empty sequence
`γ = c₁⋯cₙ` of commitments from `ℬ`, each `c_m` defined at the state its
predecessors leave, leaving a table `R_c`, and then retires rows and emits `o`,
all atomically … The event is legal when `(i,o) ∈ R_c` and every row of `R_c`
ruled out by `o` is refined by a retained row that refines `o`
(Eq. lifted-validity) … The event then … ends at `(i, R_c[out ⪰ o])`."

Lean: `SysStep B σ (.output γ o) τ` (also covering input events, unchanged).
Eq. lifted-validity at the committed state is exactly `Exposable σc o`. -/
abbrev «def:system-output-event» {sp : Spec I O} (B : Basis sp) (σ : State sp)
    (e : SEvent sp) (τ : State sp) : Prop :=
  SysStep B σ e τ

/-- **Def. commitment event** (`def:commitment-event`).  "A commitment event
`commit(γ)` under a basis `ℬ` applies a nonempty sequence `γ = c₁⋯cₙ` of
commitments from `ℬ`, each defined at the state its predecessors leave, and
emits nothing."

Lean: `SysStep B σ (.commit γ) τ` (constructor `SysStep.commit`: every
`c ∈ γ` is in `B`, `γ ≠ []`, and `ApplySeq γ σ τ`).  In the `CC.CAP` history
model the local event is `CAP.LEv.cmt γ`. -/
abbrev «def:commitment-event» {sp : Spec I O} (B : Basis sp) (σ : State sp)
    (γ : List (Commitment sp)) (τ : State sp) : Prop :=
  SysStep B σ (.commit γ) τ

/-- After Def. `def:commitment-event`: "A commitment event lets a system decide
before any output needs the decision.  The environment observes nothing from
it."  Lean: a commitment event is exactly a nonempty basis sequence applied in
order; it keeps the current input and only removes rows, and its erasure is
empty (`SEvent.erase (.commit γ) = none`). -/
theorem «sec:systems/commitment-event-unobserved» {sp : Spec I O} {B : Basis sp}
    {σ τ : State sp} {γ : List (Commitment sp)} :
    (SysStep B σ (.commit γ) τ ↔ (∀ c ∈ γ, B c) ∧ γ ≠ [] ∧ ApplySeq γ σ τ) ∧
    (SysStep B σ (.commit γ) τ → τ.cur = σ.cur ∧ ∀ k u, τ.R k u → σ.R k u) ∧
    (SEvent.commit γ : SEvent sp).erase = none :=
  ⟨⟨fun h => by cases h with | commit hb hne ha => exact ⟨hb, hne, ha⟩,
    fun ⟨hb, hne, ha⟩ => SysStep.commit hb hne ha⟩,
   fun h => ⟨h.commit_cur, h.sub⟩, rfl⟩

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
`Sealed_o` and `Rejected_o` (Lemma canonical-commitment-normal-form)…"

Lean: Lemma containment (1) (`CC.containment`): the event keeps the current
input, `o ∈ R(i)`, the end table is inside `R[out ⪰ o]`, and the state `σc`
left by `γ` has none of the rows of `Sealed_o`, `Rejected_o`. -/
theorem «sec:systems/legal-event-containment» {sp : Spec I O} {B : Basis sp}
    {σ τ : State sp} {γ : List (Commitment sp)} {o : O} (h : SysStep B σ (.output γ o) τ) :
    τ.cur = σ.cur ∧ σ.R σ.cur o ∧ (∀ k u, τ.R k u → σ.R k u ∧ o ≼ u) ∧
    ∃ σc, ApplySeq γ σ σc ∧ ∀ k x, (Sealed σ o k x ∨ Rejected σ o k x) → ¬ σc.R k x :=
  containment h

/-- "… and `output(o)` is the case in which they remove exactly those."

Lean: `κ_o` is `s_o` (if `Sealed_o ≠ ∅`) followed by `c_o` (if
`Rejected_o ≠ ∅`); the canonical steps `CanonStep` (under `B_S`, output
events `Out_{κ_o}(o)`) are exactly the steps of §§2–3 after erasing `γ`. -/
theorem «sec:systems/output-is-canonical-event» {sp : Spec I O} :
    (∀ (σ : State sp) (o : O), kappa σ o =
      (if ∃ k x, Sealed σ o k x then [sealC o] else []) ++
      (if ∃ k x, Rejected σ o k x then [choiceC o] else [])) ∧
    (∀ (σ τ : State sp) (e : SEvent sp), CanonStep σ e τ →
      ∃ e' : Event I O, e.erase = some e' ∧ Step σ e' τ) ∧
    (∀ (σ τ : State sp) (e : Event I O), Step σ e τ →
      ∃ e' : SEvent sp, e'.erase = some e ∧ CanonStep σ e' τ) :=
  ⟨fun _ _ => rfl, fun _ _ _ => canonStep_step, fun _ _ _ => step_canonStep⟩

/-- "The environment observes `o`, not `γ`."  Together with Def. `def:system`:
a system's output events are legal events `Out_γ(o)` with `γ` drawn from its
basis.

Lean: in the `CC.CAP` history model an output event `out γ o` is a basis check,
`applySeq`, and an exposable `output(o)` step at the committed state; this is
exactly `SysStep` (first conjunct).  Erasure keeps `o` and drops `γ` (second
conjunct). -/
theorem «sec:systems/system-histories» {sp : Spec I O} {B : Basis sp} {σ τ : State sp}
    {γ : List (Commitment sp)} {o : O} :
    (SysStep B σ (.output γ o) τ ↔
      (∀ c ∈ γ, B c) ∧ ∃ σc, CAP.applySeq σ (γ.map Dist.toCAP) = some σc ∧
        Step σc (.output o) τ ∧ Exposable σc o) ∧
    (SEvent.output γ o).erase = some (Event.output o : Event I O) :=
  ⟨Dist.sysStep_iff_CAP, rfl⟩

/-- *A transactional example of bespoke commitments.*  "The lock manager …
is one system; multiversion timestamp ordering (MVTO) is another, and they have
different bases … The ordering commitments are where they part:
`order(A,B)` fixes `A` before `B` and nothing else, which no MVTO commitment
does, and `stamp(B)` places `B` before every other transaction, which no 2PL
commitment does."  At the canonical state of an input whose transactions `A`,
`B`, `C` have each requested commit (Appendix G's specification), no commitment
of `ℬ_MVTO` has the effect of `order(A,B)`, and no commitment of `ℬ_2PL` has the
effect of `stamp(B)`. -/
theorem «sec:systems/bases-differ» {T K : Type} {A B C : T} {k : Txn.Partial.Inp T K}
    (h : Txn.Partial.Tri k A B C) :
    (∃ τ, (Txn.Partial.order A B).app (Txn.Partial.σ3 k) = some τ ∧
      ∀ c, Txn.Partial.basisMVTO c → c.app (Txn.Partial.σ3 k) ≠ some τ) ∧
    (∃ τ, (Txn.Partial.stamp B (fun _ => False)).app (Txn.Partial.σ3 k) = some τ ∧
      ∀ c, Txn.Partial.basis2PL c → c.app (Txn.Partial.σ3 k) ≠ some τ) :=
  CC.Paper.«app:cc-bases/bases-differ» h

/-- Fig. `fig:cc-commitments`: "When `B` waits for a lock that `A` holds, 2PL
applies `order(A,B)`, leaving `C`'s position open (panel (h)).  When MVTO gives
`B` the first timestamp, it applies `stamp(B)`, placing `B` first (panel
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

/-- *A transactional example of bespoke commitments.*  "Both are choices: they remove serialization
orders while the input stays legal, but leave different alternatives open."

Lean, for any commitment (in particular `Txn.Partial.order`, `Txn.Partial.stamp`): a
commitment keeps a row at the current input, so where it removes rows there it
chooses — some row is kept and no removed row is refined by it. -/
theorem «sec:systems/two-systems-two-choices» {sp : Spec I O} (c : Commitment sp)
    {σ τ : State sp} (h : c.app σ = some τ) :
    (∃ w, τ.R σ.cur w) ∧
    ((∃ u, σ.R σ.cur u ∧ ¬ τ.R σ.cur u) →
      ∃ w, τ.R σ.cur w ∧ ∀ u, σ.R σ.cur u → ¬ τ.R σ.cur u → ¬ u ≼ w) := by
  obtain ⟨w, hw⟩ := commitment_not_seal_cur c h
  exact ⟨⟨w, hw⟩, fun _ => ⟨w, hw, fun u hu hnu => c.excludes σ τ h _ u w hu hnu hw⟩⟩

/-- "… and neither is the choice `c_o` of Definition lifted-output-event."
At the canonical state of an input whose transactions `A`, `B`, `C` have each
requested commit (Appendix G's specification), the results of
`order(A,B)` and `stamp(B)` are not the result of `c_o` for any output `o`. -/
theorem «sec:systems/neither-is-the-choice» {T K : Type} {A B C : T} {k : Txn.Partial.Inp T K}
    (h : Txn.Partial.Tri k A B C) :
    (∀ τ, (Txn.Partial.order A B).app (Txn.Partial.σ3 k) = some τ →
      ∀ o, (choiceC o).app (Txn.Partial.σ3 k) ≠ some τ) ∧
    (∀ τ, (Txn.Partial.stamp B (fun _ => False)).app (Txn.Partial.σ3 k) = some τ →
      ∀ o, (choiceC o).app (Txn.Partial.σ3 k) ≠ some τ) :=
  Txn.Partial.neither_is_choice h

/-- "We call the runs of Sections functional-calm–complete-calm canonical runs,
and a run under a basis `ℬ` is one whose output and commitment events apply
only commitments from `ℬ` (Definition run-under-basis)."  (Formal definitions:
`«def:run-under-basis»` in `Paper/AppC_CommitmentBases.lean`.) -/
abbrev «sec:systems/run-under-basis» {sp : Spec I O} (B : Basis sp) (es : List (SEvent sp))
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
`SEvent.erase (.commit γ) = none`, so commitment events disappear from the
erasure `es.filterMap SEvent.erase`. -/
theorem «sec:systems/canonical-equivalent» {sp : Spec I O} {B : Basis sp} {i : I}
    {es : List (SEvent sp)} {ρ : State sp} (h : SysExec B (canon sp i) es ρ) :
    ∃ es' ρ', Lockstep B (canon sp i) es ρ (canon sp i) es' ρ' ∧
      es.filterMap SEvent.erase = es'.filterMap SEvent.erase ∧
      Exec (canon sp i) (es.filterMap SEvent.erase) ρ' ∧
      ρ'.cur = ρ.cur ∧ (∀ k u, ρ.R k u → ρ'.R k u) :=
    canonical_equivalent h

/-- *Canonical runs suffice*, example.  "Consider 2PL on an input of three
transactions `A`, `B`, `C` that have each issued their operations and requested
commit, where `B` waits for a lock that `A` holds.  When `B` begins to wait,
2PL applies `order(A,B)` in a commitment event, before any output, keeping only
the rows that can be completed without committing `B` before `A`.  The
canonical run skips that event, so it keeps every row, including the one
completed by `[B,A,C]`.  When 2PL later emits `[A,C,B]`, it applies no further
commitment ordering `A` and `B`, and the canonical run emits the same output;
both end with the same table.  The lock issued its commitment to `A` before `B`
earlier than any output required."

Lean (`CC.Txn.Partial.CommitEx.example_commit_event_ABC`), at any input `k`
whose transactions `A`, `B`, `C` have each issued their operations and requested
commit; rows are serial orders without aborts or reads:
(a) the commitment event `commit([order(A,B)])` is a legal `B_2PL` step from
the canonical state `σ₀` to `σ₁`; `σ₁` keeps exactly the rows of `σ₀` with a
complete refinement in `σ₀` that does not commit `B` before `A` (aborting `A`
or `B` counts), so it keeps `[A,B,C]` and removes `[B,A,C]`;
(b) the canonical run stays at `σ₀`, which has `[B,A,C]`;
(c) 2PL's `Out_[TxCommit(A),TxCommit(B),TxCommit(C),order(A,C),order(C,B)]([A,C,B])`
is a legal `B_2PL` step from `σ₁`, `Out_[TxCommit(A),TxCommit(B),TxCommit(C)]([A,C,B])`
is not (the row `[A,B,C]` survives those commitments), and the canonical run
emits `[A,C,B]` with `κ`;
(d) both end at the same state, and the runs are a `Lockstep` pair whose
commitment event is matched by no canonical event. -/
theorem «sec:systems/canonical-example» {T K : Type} {A B C : T} {k : Txn.Partial.Inp T K}
    (h : Txn.Partial.Tri k A B C) :
    let σ0 := Txn.Partial.σ3 k
    let o2 := Txn.Partial.CommitEx.o2 (K := K) A B C
    let γ2 := Txn.Partial.CommitEx.γ2 (K := K) A B C
    let row := fun (l : List T) => Txn.Partial.full (K := K) (Txn.Partial.mk l fun _ => False)
    ∃ σ1 τ2 τ2' : State (Txn.Partial.spec (T := T) (K := K) false),
      -- (a)
      SysStep Txn.Partial.basis2PL σ0 (.commit [Txn.Partial.order A B]) σ1 ∧ σ1.cur = k ∧
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
      Lockstep Txn.Partial.basis2PL σ0 [.commit [Txn.Partial.order A B], .output γ2 o2] τ2
        σ0 [.output (kappa σ0 o2) o2] τ2' :=
  Txn.Partial.CommitEx.example_commit_event_ABC h

/-! ## Coordination (§4.4, `sec:coordination`) -/

/-- §4.4: "A commitment requires coordination only when another run could
contradict it … it requires distributed coordination when that run is at
another participant.  Running such a mechanism need not issue a commitment: closing the
polls after every voter has voted still runs the mechanism, but no ballot is
left to seal, so it removes nothing the specification still permits and
applies no commitment."  At the canonical
state of any full ballot, the poll-closing commitment `closePolls` is undefined
(it would remove no row). -/
theorem «sec:coordination/closing-after-voting» (i : CALM.Ballots)
    (hfull : i.b1.isSome ∧ i.b2.isSome ∧ i.b3.isSome) :
    (Figures.closePolls (sp := CALM.elec)).app (canon CALM.elec i) = none :=
  Figures.Elec.close_after_voting i hfull

/-- **Def. contradicting run** (`def:contradicts`).  "Let an event of a run
apply a commitment.  A run contradicts the commitment if it accepts an input
the commitment seals, or emits an output the commitment chooses against at the
same input."  The events that apply commitments are output events `Out_γ(o)`
and commit events `Commit(γ)`.

Lean (`CC.CAP` model): `CAP.Contradicts emits accepts σ σc`, for commitments
taking `σ` to `σc` and runs described by the outputs they emit at each current
input (`emits k x`) and the inputs they accept (`accepts k`): some removed row
`(k,x)` is emitted at current input `k`, or some sealed input `k` (one whose
remaining rows are all removed) is accepted. -/
abbrev «def:contradicts» {sp : Spec I O} (emits : I → O → Prop) (accepts : I → Prop)
    (σ σc : State sp) : Prop :=
  CAP.Contradicts emits accepts σ σc

/-- **Def. coordination-requiring commitment, distributed coordination**
(`def:coordination`).  "Let `𝓡` be a set of runs: for a specification, its
canonical runs; for a system, the runs it can perform under any inputs the
environment may supply.  A commitment requires coordination relative to `𝓡`
when some run in `𝓡` contradicts it (Definition contradicts)."

Lean, for a system: the commitments taking `σ` to `σc` are contradicted
(`«def:contradicts»`) by the runs of `Sys`: some produced history emits a
removed row (`SysEmits`) or accepts a sealed input (`SysAccepts`); produced
histories range over all inputs the adversarial environment may supply. -/
abbrev «def:coordination» {sp : Spec I O} {D : Type} (Sys : CAP.System sp D)
    (σ σc : State sp) : Prop :=
  CAP.Contradicts (CAP.SysEmits Sys) (CAP.SysAccepts Sys) σ σc

/-- Def. `def:coordination`: "It requires distributed coordination when that
run is at another participant of the same history."  Lean: the commitments
taking `σ` to `σc`, applied by participant `p` of `H`, are contradicted by a
participant `q ≠ p` of `H` (`OtherEmits`, `OtherAccepts`). -/
abbrev «def:coordination/distributed» {sp : Spec I O} {D : Type} {n : Nat}
    (init : Fin n → I) (H : CAP.History sp D n) (p : Fin n) (σ σc : State sp) : Prop :=
  CAP.Contradicts (CAP.OtherEmits init H p) (CAP.OtherAccepts H p) σ σc

/-- Def. `def:coordination`, for a specification (`𝓡` the canonical runs): a
run applies a commitment that requires coordination exactly when it applies a
commitment at all (`Coordinates`: some output event has `γ ≠ ε`, or there is a
commit event); see `«sec:coordination/specification-contradicted»`. -/
abbrev «def:coordination/specification» {sp : Spec I O} (es : List (SEvent sp)) : Prop :=
  Coordinates es

/-- **Def. coordination-free** (`def:coordination-free`).  "A run or history is
coordination-free relative to `𝓡` when it applies no commitment that requires
coordination relative to `𝓡`."

Lean, for a system: `System.CoordinationFree` says the commitments of every
output event and every commit event of every produced history are local
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
commit event of a produced history requires distributed coordination.  Lean:
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

/-- "Whether a commitment requires coordination depends on the set of runs:
those of a specification, or those of a system implementing it.  For a
specification, every commitment requires coordination: some canonical run
accepts each input that a commitment can seal and emits each permitted
output."  Lean: from `σ_S(i)` with `i ≼ k`, the
canonical run `input(k) output(x)` accepts `k` and emits any `x ∈ S(k)` at
current input `k`. -/
theorem «sec:coordination/specification-contradicted» {sp : Spec I O} {i k : I} {x : O}
    (hik : i ≼ k) (hx : sp.S k x) :
    ∃ τ : State sp, Exec (canon sp i) [.input k, .output x] τ ∧ τ.cur = k :=
  CAP.canonical_run_contradicts hik hx

/-- Def. `def:coordination-free`: "For a specification, then, coordination-free means
commitment-free: every output event is some `Out_ε(o)`, which may still
perform output retirements, and no commitment event occurs."  Lean: `CoordFree` (every output event is
`Out_ε(o)`, and there is no commit event). -/
abbrev «def:coordination-free/specification» {sp : Spec I O} (es : List (SEvent sp)) : Prop :=
  CoordFree es

/-- "Closing the polls before every voter has voted seals the remaining
ballots."  Lean: at panel (b) (`xy·`), closing the polls is defined and leaves
no row at the remaining-ballot input `xyx`, which had the row `(xyx, x)`. -/
theorem «sec:coordination/closing-before-voting-seals» :
    (Figures.closePolls (sp := CALM.elec)).app (canon CALM.elec CALM.bxy) =
      some Figures.Elec.panelD ∧
    (canon CALM.elec CALM.bxy).R CALM.bxyx (.win .x) ∧
    ∀ o, ¬ Figures.Elec.panelD.R CALM.bxyx o := by
  refine ⟨Figures.Elec.close_at_b,
    ⟨(by decide : CALM.Res.win .x = CALM.winner CALM.bxyx), by decide⟩, fun o h => ?_⟩
  have := (Figures.Elec.panelD_rows _ o).1 h
  exact absurd this.1 (by decide)

/-- "Outputs, by contrast, come only from the system's strategies, so a choice
requires coordination only when the system can perform a run that emits an
output the choice rules out, and distributed coordination when such a run is
at another participant."  Lean: `SysEmits` requires an output event in a
produced history, hence one allowed by the participant's strategy.  The rest
of the sentence is Def. `def:coordination` for the system's runs
(`«def:coordination»`, `«def:coordination/distributed»`). -/
theorem «sec:coordination/choices-by-strategies» {sp : Spec I O} {D : Type}
    (Sys : CAP.System sp D) {k : I} {x : O} (h : CAP.SysEmits Sys k x) :
    ∃ n init q pre γ, Sys.strat n init q pre (CAP.LEv.out γ x) := by
  obtain ⟨n, init, H, q, a, b, γ, σ, _, hp, hH, _, _⟩ := h
  exact ⟨n, init, q, a, γ, ((hp q) a _ b hH).2⟩

/-- Def. `def:coordination-free`: coordination-free is the negation of coordinates,
and coordination-free runs under any basis are exactly the commitment-free
executions (`ExecCF`) of §3 after erasing `γ`.  `Out_ε(o)` ends at
`R[out ⪰ o]`, so it may still retire rows (`«lem:canonical-commitment-normal-form»`
(3) in the App. C file). -/
theorem «def:coordination-free/commitment-free-runs» {sp : Spec I O} :
    (∀ es : List (SEvent sp), CoordFree es ↔ ¬ Coordinates es) ∧
    (∀ (B : Basis sp) (σ τ : State sp) (es : List (SEvent sp)),
      SysExec B σ es τ → CoordFree es → ExecCF σ (es.filterMap SEvent.erase) τ) ∧
    (∀ (B : Basis sp) (σ τ : State sp) (es : List (Event I O)), ExecCF σ es τ →
      ∃ es' : List (SEvent sp), es'.filterMap SEvent.erase = es ∧ CoordFree es' ∧
        SysExec B σ es' τ) :=
  ⟨coordFree_iff_not, fun _ _ _ _ h hf => coordFree_execCF h hf,
    fun B _ _ _ h => execCF_coordFree B h⟩

/-- **Prop. conflicting events cannot be reconciled**
(`thm:commitments-require-coordination`).  "From a state `(i,R)`, let one
run perform an output or commitment event after which no output at `i` refines `x`,
and let another run perform an output event that emits `x`.  The two resulting
states cannot be brought to a common state with current input `i`."

Lean: this entry takes the first event to be an output event; for a
commitment event (indeed any event) see `…/any-event`.  `x ∈ R(i)` follows from the legality of `Out_{γ'}(x)`.  "Brought to a
common state" is: by executions under a basis `B''` (any; for different bases
see `…/any-bases`, for the transition system of §§2–3 see `…/reach`). -/
theorem «thm:commitments-require-coordination» {sp : Spec I O} {B B' B'' : Basis sp}
    {σ σ' t : State sp} {γ γ' : List (Commitment sp)} {o x : O}
    (h1 : SysStep B σ (.output γ o) σ') (hno : ∀ w, σ'.R σ.cur w → ¬ x ≼ w)
    (h2 : SysStep B' σ (.output γ' x) t) :
    γ ≠ [] ∧
    ¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧
        (∃ es, SysExec B'' σ' es ρ) ∧ (∃ es, SysExec B'' t es ρ) :=
  conflicting_outputs h1 hno h2

/-- Prop. `thm:commitments-require-coordination`, with the two continuations
under different bases. -/
theorem «thm:commitments-require-coordination/any-bases» {sp : Spec I O}
    {B B' B1 B2 : Basis sp} {σ σ' t : State sp} {γ γ' : List (Commitment sp)} {o x : O}
    (h1 : SysStep B σ (.output γ o) σ') (hno : ∀ w, σ'.R σ.cur w → ¬ x ≼ w)
    (h2 : SysStep B' σ (.output γ' x) t) :
    ¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧
        (∃ es, SysExec B1 σ' es ρ) ∧ (∃ es, SysExec B2 t es ρ) :=
  Dist.conflicting_outputs2 h1 hno h2

/-- Prop. `thm:commitments-require-coordination`, with continuations in the
transition system of §§2–3. -/
theorem «thm:commitments-require-coordination/reach» {sp : Spec I O} {B B' : Basis sp}
    {σ σ' t : State sp} {γ γ' : List (Commitment sp)} {o x : O}
    (h1 : SysStep B σ (.output γ o) σ') (hno : ∀ w, σ'.R σ.cur w → ¬ x ≼ w)
    (h2 : SysStep B' σ (.output γ' x) t) :
    ¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧ Reach σ' ρ ∧ Reach t ρ :=
  conflicting_outputs_reach h1 hno h2

/-- Prop. `thm:commitments-require-coordination` with the first event any
event, in particular a commitment event `commit(γ)`: "let one run perform an
output or commitment event after which no output at `i` refines `x`".

Lean: for any event `e` taking `σ` to `σ'` with no output at `i` refining `x`,
and `Out_{γ'}(x)` taking `σ` to `t`, no state with current input `i` is
reachable from both, under any bases or in the transition system of §§2–3; if
`e` is an output or commitment event, its commitment sequence is nonempty. -/
theorem «thm:commitments-require-coordination/any-event» {sp : Spec I O}
    {B B' B1 B2 : Basis sp} {σ σ' t : State sp} {e : SEvent sp}
    {γ' : List (Commitment sp)} {x : O}
    (h1 : SysStep B σ e σ') (hno : ∀ w, σ'.R σ.cur w → ¬ x ≼ w)
    (h2 : SysStep B' σ (.output γ' x) t) :
    (∀ γ o, e = .output γ o → γ ≠ []) ∧ (∀ γ, e = .commit γ → γ ≠ []) ∧
    (¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧
        (∃ es, SysExec B1 σ' es ρ) ∧ (∃ es, SysExec B2 t es ρ)) ∧
    ¬ ∃ ρ : State sp, ρ.cur = σ.cur ∧ Reach σ' ρ ∧ Reach t ρ :=
  let h := Dist.conflicting_events (B1 := B1) (B2 := B2) h1 hno h2
  ⟨h.1, h.2.1, h.2.2, Dist.conflicting_events_reach h1 hno h2⟩

/-- "The conflict is confined to the current input.  If `i ≺ j`, `S(i) = {o,x}`
with `o` and `x` incomparable, and `S(j) = {u}` with `u` refining both, the two
states can be reconciled once `j` arrives.  Consistency still counts this as a failure,
since it asks for confluence at the current input too."  (The rest of the paragraph, on the
environment and transient conflicts, is the paper's modeling assumption.)

Lean: the example of `CALM/TransientConflict.lean`: inputs `i ≺ j`, outputs
`o`, `x` incomparable below `u`, `S(i) = {o,x}`, `S(j) = {u}`.  From
`σ_S(i)`, the canonical events `output(o)` and `output(x)` are legal; after
`output(o)` no output at `i` refines `x`, so the two states have no common
state with current input `i`; both reach `σ_S(j)` by `input(j)`, so they are
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
/-- Paragraph "Locks in a shared-nothing database": "Ownership changes which
runs can contradict a commitment.  The three cases of the definitions all
arise in a database partitioned by key, in which each key is owned by one
participant, which manages its locks."

*Local coordination.*  "Ordering two transactions on one key requires
coordination: in another run `B`'s request arrives first and the key's owner
orders `B` before `A`.  But only runs at the key's owner can contradict it, so
it does not require distributed coordination."  Lean: a spec with outputs `⊥ ≤ ab, ba` (`ab`,
`ba` incomparable); emitting `ab` is a commitment (not exposable); in the
system where only participant 0 may emit an order, another run (the owner
choosing `ba`) contradicts it, but no other participant of a history does. -/
theorem «sec:coordination/shared-nothing-single-key» (D : Type) :
    ¬ Exposable (canon CAP.ordSpec ()) .ab ∧ ¬ (CAP.ownerSys D).CoordinationFree ∧
      (CAP.ownerSys D).CoordinationFreeH :=
  ⟨CAP.ordSpec_ab_not_exposable, CAP.ownerSys_not_coordinationFree D,
    CAP.ownerSys_coordinationFreeH D⟩

/-- Paragraph "Locks in a shared-nothing database", *Distributed
coordination*: "A transaction that spans keys needs one order, but each key's
owner orders its part, and the owners of two keys can order the same pair of
transactions oppositely.  Each ordering then requires distributed
coordination, and the owners must agree."  Lean: when two participants may
each emit an order, some history has one emit `ab` (removing `ba`) and the
other emit `ba`, so the system is not free of distributed coordination.
"The owners must agree" is the paper's reading of that (some mechanism must
exclude one of the two events), not a separate claim.  The case that follows
is `«sec:coordination/two-phase-commit»`. -/
theorem «sec:coordination/shared-nothing-cross-key» (D : Type) :
    ¬ (CAP.twoOwnerSys D).CoordinationFreeH :=
  CAP.twoOwnerSys_not_coordinationFreeH D

/-- Paragraph "Locks in a shared-nothing database", *No coordination*:
"Two-phase commit adds no coordination beyond the owners' own.  Each owner's
prepare is its own commitment, local coordination as in the first case.  The
unanimous vote that combines them, however, requires no coordination at all:
the coordinator's unanimity decision over a fixed set of participants is
monotone, so it issues no commitment that requires coordination."

Lean, for the decision (`CAP/TwoPhaseCommit.lean`): inputs record the votes
of `n` fixed participants (`none` until received; a received vote does not
change), outputs are `undecided ≼ commit, abort`, and `S` aborts on a no vote,
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
      (CAP.respSystem (sp := CAP.voteSpec n) (D := D) (CAP.voteSpec n).S).CoordinationFree ∧
      (CAP.respSystem (sp := CAP.voteSpec n) (D := D) (CAP.voteSpec n).S).CoordinationFreeH :=
  ⟨CAP.voteSpec_functional n, CAP.voteSpec_monotone n, CAP.voteSpec_consistent n,
   CAP.voteSpec_exposable n, CAP.voteSpec_coordinationFree n D⟩

/-- Paragraph "Locks in a shared-nothing database", *No coordination*: "The
coordinator does not make the owners agree; it detects whether their local
commitments already agree, and aborts when they do not."  Lean, for the
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

/-- Paragraph "Locks in a shared-nothing database", *No coordination*: "A
coordinator that aborts on timeout, before the last vote arrives, does issue a
commitment: like closing the polls, it seals every input that adds a missing
vote, yes or no."  (CIDR version: "A coordinator that aborts on timeout,
before the last vote arrives, issues a commitment, like closing the polls".)

Lean (`CAP/TimeoutAbort.lean`), on the decision `voteSpec` of
`«sec:coordination/two-phase-commit»`: at `σ_S(v)` with vote `p` missing,
closing the polls (`Figures.closePolls`, a commitment) applies; it is a seal;
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
  CAP.Timeout.timeout_seals v p hp

/-- Paragraph "Locks in a shared-nothing database", *No coordination*: "The
decision is its own specification, run by the coordinator alone, so this is
local coordination, as in the first case; it becomes distributed coordination
when the decision is replicated for fault tolerance, as in Paxos Commit."
(CIDR version: "but the decision is a specification only the coordinator
runs: local coordination.")

Lean (`CAP/TimeoutAbort.lean`), for the seal of
`«sec:coordination/2pc-timeout-abort»` (closing the polls on `voteSpec` at
`yy·`).  The decision specification is run by a system of its own, as each
stage is in the composition section; the owners' specifications are separate
systems.

*Run by the coordinator alone* (`sealSys1`, whose strategies act only when
the system has one participant): the seal requires coordination, since
another run of the coordinator from `yy·` accepts the sealed late vote `yyy`
(not `CoordinationFree`); but no history of the system applies a commitment
that another participant of the same history contradicts
(`CoordinationFreeH`): local coordination.  The general fact is
`single_coordinationFreeH`.

*Replicated* (two or more participants run `voteSpec`): any system in which
participant `0` of two, starting at `yy·`, may close the polls there is not
`CoordinationFreeH`, since the environment may deliver `yyy` to the other
participant; `sealSysRepl` (every participant at `yy·` may close the polls) is
an instance.  Distributed coordination.  Paxos Commit itself is not modeled.

Library lemmas not quoted here: the abort read as a choice (`abortSpec`,
`abort_choice_yy`, `coordSys_coordinationFreeH`,
`replSys_not_coordinationFreeH`). -/
theorem «sec:coordination/2pc-timeout-abort-local» (D : Type) :
    (¬ (CAP.Timeout.sealSys1 D).CoordinationFree ∧
      (CAP.Timeout.sealSys1 D).CoordinationFreeH) ∧
    (∀ Sys : CAP.System (CAP.voteSpec 3) D, Sys.basis CAP.Timeout.cp →
      Sys.strat 2 (fun _ => CAP.Timeout.yyN) 0 [] (.out [CAP.Timeout.cp] .undecided) →
      ¬ Sys.CoordinationFreeH) ∧
    ¬ (CAP.Timeout.sealSysRepl D).CoordinationFreeH :=
  ⟨CAP.Timeout.sealSys1_local D,
   fun Sys hb hs => CAP.Timeout.seal_not_coordinationFreeH Sys hb hs,
   CAP.Timeout.sealSysRepl_not_coordinationFreeH D⟩

/-- Paragraph "Locks in a shared-nothing database": "All three exchange
messages, and a client cut off from an owner cannot get its answer; only the
second issues a commitment that a run at another participant could
contradict."  Lean, for the second clause: of the three systems, only the
two-owner system of the distributed case fails to be free of distributed
coordination (`CoordinationFreeH`).  The first clause (messages, clients cut
off from owners) is not modeled; see `lean/README.md`. -/
theorem «sec:coordination/shared-nothing-only-second» (n : Nat) (D : Type) :
    (CAP.ownerSys D).CoordinationFreeH ∧ ¬ (CAP.twoOwnerSys D).CoordinationFreeH ∧
      (CAP.respSystem (sp := CAP.voteSpec n) (D := D) (CAP.voteSpec n).S).CoordinationFreeH :=
  ⟨CAP.ownerSys_coordinationFreeH D, CAP.twoOwnerSys_not_coordinationFreeH D,
    (CAP.voteSpec_coordinationFree n D).2⟩

/-- "The first event's commitment is a choice against `x`."

Lean: (a) every commitment keeps a row at the current input; (b) in the
setting of the proposition, some commitment `c` of `γ` removes `(i,x)` while
keeping a row at `i`, and no kept row at `i` refines `x`. -/
theorem «sec:coordination/conflict-is-choice» {sp : Spec I O} :
    (∀ (c : Commitment sp) (σ τ : State sp), c.app σ = some τ → ∃ w, τ.R σ.cur w) ∧
    (∀ {B : Basis sp} {σ σ' : State sp} {γ : List (Commitment sp)} {o x : O},
      SysStep B σ (.output γ o) σ' → σ.R σ.cur x → (∀ w, σ'.R σ.cur w → ¬ x ≼ w) →
      ∃ c ∈ γ, ∃ α β : State sp, c.app α = some β ∧ α.cur = σ.cur ∧ α.R σ.cur x ∧
        ¬ β.R σ.cur x ∧ (∃ w, β.R σ.cur w) ∧ ∀ w, β.R σ.cur w → ¬ x ≼ w) :=
  ⟨fun c _ _ h => commitment_not_seal_cur c h, fun h1 hx hno => Dist.conflict_is_choice h1 hx hno⟩

/-- "The first event's commitment is a choice against `x`", when the first
event is a commitment event `commit(γ)`, as the proposition allows ("an output
or commitment event").

Lean: if `commit(γ)` leaves no output at `i` refining `x ∈ R(i)`, some
commitment `c` of `γ` removes `(i,x)` while keeping a row at `i`, and no kept
row at `i` refines `x`. -/
theorem «sec:coordination/conflict-is-choice-commit» {sp : Spec I O} {B : Basis sp}
    {σ σ' : State sp} {γ : List (Commitment sp)} {x : O}
    (h1 : SysStep B σ (.commit γ) σ') (hx : σ.R σ.cur x)
    (hno : ∀ w, σ'.R σ.cur w → ¬ x ≼ w) :
    ∃ c ∈ γ, ∃ α β : State sp, c.app α = some β ∧ α.cur = σ.cur ∧ α.R σ.cur x ∧
      ¬ β.R σ.cur x ∧ (∃ w, β.R σ.cur w) ∧ ∀ w, β.R σ.cur w → ¬ x ≼ w :=
  Dist.conflict_is_choice_commit h1 hx hno

/-- "Under Lifted Monotonicity, participants at a common input `j` can each emit
a `u ∈ S(j)` that refines everything emitted, without commitment; choosing `u`
by a shared deterministic rule terminates once outputs stop."

Lean: under Lifted Monotonicity, runs with common expansion `j` share a row
`(j,u)` (which, by Lemma run-residual, refines every output emitted on each
run), and from each final state the commitment-free events `input(j)`,
`output(u)` reach the same state. -/
theorem «sec:coordination/deterministic-reconciliation» {sp : Spec I O} (hLM : sp.LiftedMono)
    (fam : List (State sp)) (hrun : ∀ σ ∈ fam, IsRun σ) (j : I) (hj : ∀ σ ∈ fam, σ.cur ≼ j) :
    ∃ u, ∃ hu : sp.S j u, (∀ σ ∈ fam, σ.R j u) ∧
      ∀ σ ∈ fam, ExecCF σ [.input j, .output u] (meetState sp j u hu) :=
  Dist.reconcile_cf hLM fam hrun j hj

end CC.Paper
