import CoordCriterion.Distributed.Systems
import CoordCriterion.Figures
import CoordCriterion.Appendix.TransactionBases.NoReads
import CoordCriterion.Paper.AppG_TransactionBases
import CoordCriterion.Appendix.TransactionBases.CanonicalExample

/-!
# Paper §4.1–4.4: Distributed Execution (statement layer)

Covers `sections/distributed-histories.tex` (§4.1 Distributed histories, §4.2
Distributed consistency, with the paragraphs *Message data* and *Exchanging
outputs*) and `sections/distributed.tex` from §4.3 Systems through the end of
§4.4 Coordination (it stops before §4.5 The Complete CAP Theorem).

How to read this file.  Read it side by side with the paper.  Entries appear in
paper order under headers named after the paper's subsections.  Each numbered
result is named by its LaTeX label (`«def:commitment»`, `«prop:seal-or-choose»`,
…); an unlabeled claim of the text is named `«<enclosing label>/<slug>»`.  Each
docstring quotes the paper (LaTeX lightly turned into Unicode) and, where the
Lean statement reads differently, says how the two correspond.  Statements are
written out in full; the proofs are one-line references to the library
(`CoordCriterion/Distributed/*.lean`, `CAP/Model.lean`, `Figures.lean`,
`Appendix/TransactionBases/NoReads.lean`), where the modeling choices are
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

/-- **Def. distributed history** (`def:distributed-history`), the carrier.
"A distributed history `H` is a finite set of history events, each an
occurrence at one participant of an input event, an output event, `send(m)`, or
`receive(m)` …"

Lean: participants are `Fin n`; each participant has a finite `List` of local
events (`Dist.LEv`: `io e`, `send x m`, `recv x m` with a message identifier
`x` and a message `m = (j, d) : Option I × D`, `none` playing `∅`).  The list
order *is* item 1, the total local order.  The initial inputs `i_p` are
`H.init`. -/
abbrev «def:distributed-history» (I O D : Type) (n : Nat) := Dist.History I O D n

/-- Def. `def:distributed-history`, items 2–3: "for each receive, a matching
send of the same message at another participant, each send matching at most
one receive; and for each participant `p`, its input and output events, in
local order, form a defined transition sequence from `σ_S(i_p)`".

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
consistent cut `C`, the input and output events of `C` at participant `p`, in
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

/-- **Fig. participant-runs** (`fig:participant-runs`).  "Two distinct histories
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

/-- *Message data.*  "Data can influence which input and output events occur
next at the receiver, but it never directly changes the receiver's
specification state, and nothing in the definitions above depends on it."

Lean: distributed consistency does not depend on the type `D` of message data
(sends and receives are filtered out of participant runs by `Dist.ioOf`). -/
theorem «sec:distributed-consistency/message-data» (sp : Spec I O) (D D' : Type) :
    Dist.DistConsistent sp D ↔ Dist.DistConsistent sp D' :=
  (Dist.consistent_iff_distConsistent sp D).symm.trans (Dist.consistent_iff_distConsistent sp D')

/-- *Exchanging outputs* (table level).  "It can silently honor `o` by
restricting its table to `R[out ⪰ o]` … Silent honoring cannot change
confluence in either direction.  It cannot help, because it only removes rows
… It cannot hurt, because a row that survives at a common expansion already
refines every output emitted in the cut (Lemma run-residual), including `o`."

Lean: each family member is a state with the residual shape for its emitted
outputs (the shape of every run, `IsRun.residual`) and a list of honored
outputs, each emitted by some member; a row at `j` survives the honored tables
iff it survives the original ones (with the survivor test, this is
confluence). -/
theorem «sec:distributed-consistency/exchanging-outputs» {sp : Spec I O}
    (fam : List (State sp × List O × List O))
    (hres : ∀ x ∈ fam, Residual x.1 x.2.1)
    (hos : ∀ x ∈ fam, ∀ o ∈ x.2.2, ∃ y ∈ fam, o ∈ y.2.1) (j : I) :
    (∃ u, sp.S j u ∧ ∀ x ∈ fam, Dist.honor x.1.R x.2.2 j u) ↔
      (∃ u, sp.S j u ∧ ∀ x ∈ fam, x.1.R j u) :=
  Dist.honor_survivor fam hres hos j

/-- *Exchanging outputs* (history level).  "The confluence of a cut therefore
depends on which outputs were emitted, not on who has heard about them."

Lean: if each participant `p` honors outputs `os p` emitted in the cut, the
cut is confluent at `j` iff some row `(j,u)` survives every honored table. -/
theorem «sec:distributed-consistency/exchanging-outputs-cut» {D : Type} {n : Nat}
    {sp : Spec I O} {H : Dist.History I O D n} (hW : H.WF sp) {C : Dist.Pos n → Prop}
    (hC : H.IsCut C) {σs : Fin n → State sp} (hE : H.Endpoint sp C σs) (os : Fin n → List O)
    (hos : ∀ p, ∀ o ∈ os p, H.EmittedIn C o) (j : I) (hj : ∀ p, (σs p).cur ≼ j) :
    H.CutConfluentAt sp C j ↔ ∃ u, sp.S j u ∧ ∀ p, Dist.honor (σs p).R (os p) j u :=
  Dist.honor_cut_confluent hW hC hE os hos j hj

/-- *Exchanging outputs.*  "This restriction is a table, not a specification
state: it may have no row at the participant's current input, so silent
honoring is not an event."

Lean: a functional, monotone specification on `Fin 3` (`Dist.spV3`); `q` at
`σ_S(1)` may emit `1`; honoring `1` at `p`'s `σ_S(0)` leaves no row at `p`'s
current input `0`, although the row `(2,2)` survives. -/
theorem «sec:distributed-consistency/honored-table-not-state» :
    (canon Dist.spV3 (Dist.v 1)).R (Dist.v 1) (Dist.v 1) ∧
    (¬ ∃ x, Dist.honor (canon Dist.spV3 (Dist.v 0)).R [Dist.v 1] (Dist.v 0) x) ∧
    Dist.honor (canon Dist.spV3 (Dist.v 0)).R [Dist.v 1] (Dist.v 2) (Dist.v 2) ∧
    (canon Dist.spV3 (Dist.v 1)).R (Dist.v 2) (Dist.v 2) :=
  Dist.honor_counterexample

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

/-- "As expected, the seals and choices of Definitions output-event and
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

/-- **Def. strategy** (`def:strategy`).  "A local history of participant `p` is a
finite sequence of `p`'s history events … A strategy for `p` is a
nondeterministic transition function: it maps each local history `λ` of `p` to
a set `θ_p(λ)` of output, send, and receive events of `p`, and `p` next performs
any one of them, or waits.  Input events come from the environment, not the
strategy."

Lean (the `CC.CAP` system model): a strategy for `p` is a relation from local
histories (`List (CAP.LEv sp D n)`) to next events.  Its value on input events
is ignored: `CAP.Allowed` always allows inputs. -/
abbrev «def:strategy» (sp : Spec I O) (D : Type) (n : Nat) :=
  List (CAP.LEv sp D n) → CAP.LEv sp D n → Prop

/-- **Def. system** (`def:system`).  "A system consists of a commitment basis
`ℬ`, the set of commitments its output events may apply, shared by all
participants, and a strategy `θ_p` for each participant `p` whose output events
apply only commitments from `ℬ`."

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

/-- **Def. output event of a system** (`def:system-output-event`).  "An output
event `Out_γ(o)` under a basis `ℬ` applies a finite, possibly empty sequence
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

/-- "A legal `Out_γ(o)` commits at least as much as the `output(o)` of
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
    (∀ (σ τ : State sp) (e : SEvent sp), CanonStep σ e τ → Step σ e.erase τ) ∧
    (∀ (σ τ : State sp) (e : Event I O), Step σ e τ →
      ∃ e' : SEvent sp, e'.erase = e ∧ CanonStep σ e' τ) :=
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
    (SEvent.output γ o).erase = (Event.output o : Event I O) :=
  ⟨Dist.sysStep_iff_CAP, rfl⟩

/-- *A transactional example of bespoke commitments.*  "The lock manager …
is one system; multiversion timestamp ordering (MVTO) is another, and they have
different bases … The ordering commitments are where they part:
`order(A,B)` fixes `A` before `B` and nothing else, which no MVTO commitment
does, and `stamp(B)` places `B` before every other transaction, which no 2PL
commitment does."  At the canonical state of `{A,B,C}` (Appendix G's
specification), no commitment of `ℬ_MVTO` has the effect of `order(A,B)`, and
no commitment of `ℬ_2PL` has the effect of `stamp(B)`. -/
theorem «sec:systems/bases-differ» {T K : Type} {rd wr : T → K → Prop} {A B C : T}
    (h : Txn.Partial.Distinct3 A B C) :
    (∃ τ, (Txn.Partial.order A B).app (Txn.Partial.σABC (K := K) rd wr h) = some τ ∧
      ∀ c, Txn.Partial.basisMVTO c → c.app (Txn.Partial.σABC rd wr h) ≠ some τ) ∧
    (∃ τ, (Txn.Partial.stamp B (fun _ => False)).app (Txn.Partial.σABC (K := K) rd wr h) = some τ ∧
      ∀ c, Txn.Partial.basis2PL c → c.app (Txn.Partial.σABC rd wr h) ≠ some τ) :=
  CC.Paper.«app:cc-bases/bases-differ» h

/-- Fig. `fig:cc-commitments`: "When `B` waits for a lock that `A` holds, 2PL
applies `order(A,B)`, leaving `C`'s position open (panel (h)).  When MVTO gives
`B` the first timestamp, it applies `stamp(B)`, placing `B` first (panel
(i))."  The caption: only complete rows without aborts or read results are
shown.  Among those, `order(A,B)` keeps exactly the rows with `A` before `B`,
and `stamp(B)` (no earlier stamps) exactly those with `B` first. -/
theorem «fig:cc-commitments» {T K : Type} {sp : Spec (Txn.FinSet T) (Txn.Partial.ROut T K)}
    {σ τ τ' : State sp} {A B : T} {k : Txn.FinSet T} {c : Txn.Partial.ROut T K}
    (hp : Txn.Partitions k c.o) (hX : ∀ t, ¬ c.o.X t) (hA : k.1 A) (hB : k.1 B) :
    ((Txn.Partial.order A B).app σ = some τ → (τ.R k c ↔ σ.R k c ∧ c.o.lt A B)) ∧
    ((Txn.Partial.stamp B (fun _ => False)).app σ = some τ' →
      (τ'.R k c ↔ σ.R k c ∧ ∀ D, k.1 D → D ≠ B → c.o.lt B D)) :=
  ⟨fun h => CC.Paper.«app:cc-bases/fig-h» h hp hX hA hB,
   fun h => CC.Paper.«app:cc-bases/fig-i» h hp hX hB⟩

/-- *A transactional example of bespoke commitments.*  "Both are choices: they remove serialization
orders while the input stays legal, but leave different alternatives open."

Lean, for any commitment (in particular `Txn.orderC`, `Txn.stampC`): a
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
At the canonical state of `{A,B,C}` (Appendix G's specification), the results of
`order(A,B)` and `stamp(B)` are not the result of `c_o` for any output `o`. -/
theorem «sec:systems/neither-is-the-choice» {T K : Type} {rd wr : T → K → Prop} {A B C : T}
    (h : Txn.Partial.Distinct3 A B C) :
    (∀ τ, (Txn.Partial.order A B).app (Txn.Partial.σABC (K := K) rd wr h) = some τ →
      ∀ o, (choiceC o).app (Txn.Partial.σABC rd wr h) ≠ some τ) ∧
    (∀ τ, (Txn.Partial.stamp B (fun _ => False)).app (Txn.Partial.σABC (K := K) rd wr h) = some τ →
      ∀ o, (choiceC o).app (Txn.Partial.σABC rd wr h) ≠ some τ) :=
  Txn.Partial.neither_is_choice h

/-- "We call the runs of Sections functional-calm–complete-calm canonical runs,
and a run under a basis `ℬ` is one whose output events apply only commitments
from `ℬ` (Definition run-under-basis)."  (Formal definitions:
`«def:run-under-basis»` in `Paper/AppC_CommitmentBases.lean`.) -/
abbrev «sec:systems/run-under-basis» {sp : Spec I O} (B : Basis sp) (es : List (SEvent sp))
    (τ : State sp) : Prop :=
  RunUnder B es τ

/-- *Canonical runs suffice.*  "Although each system can define its own basis,
no basis yields behavior that canonical runs cannot.  Lemma canonical-equivalent
shows that every run under any basis has an observably equivalent canonical
run: one that accepts the same inputs, emits the same outputs, and keeps at
least the original's rows after each event.  A system's own commitments can
only remove more rows than the canonical ones would."

Lean: as `«lem:canonical-equivalent»`; `Lockstep` records the per-event
containment. -/
theorem «sec:systems/canonical-equivalent» {sp : Spec I O} {B : Basis sp} {i : I}
    {es : List (SEvent sp)} {ρ : State sp} (h : SysExec B (canon sp i) es ρ) :
    ∃ es' ρ', Lockstep B (canon sp i) es ρ (canon sp i) es' ρ' ∧
      es.map SEvent.erase = es'.map SEvent.erase ∧
      Exec (canon sp i) (es.map SEvent.erase) ρ' ∧
      ρ'.cur = ρ.cur ∧ (∀ k u, ρ.R k u → ρ'.R k u) :=
    canonical_equivalent h

/-- *Canonical runs suffice*, example.  "Consider 2PL on input `{A,B,C}`, where
`A` reads a key `x` that no transaction writes, and `B` then waits for a lock
that `A` holds on another key.  2PL's output event reports `A`'s read and
applies `order(A,B)`, keeping only the rows that can be completed without
committing `B` before `A`.  The canonical run performs the canonical event for
the same output: reporting the read requires no commitment, so it keeps every
row that reports the read, including the one completed by `[B,A,C]`.  When 2PL later emits the complete serial order
`[A,C,B]`, the canonical run emits it too, and both runs end with the same
table.  The lock committed to `A` before `B` earlier than any output required."

Lean (Appendix G's specification; `rd`, `wr` arbitrary except `rd A x` and no
transaction writes `x`; `o1` decides nothing and reports `A`'s read of `x`
returning the initial version, `o2` is `[A,C,B]` with that read):
`read(A,x,initial)` is undefined at the canonical state, `o1` is exposable
there and `κ_{o1} = ε`; 2PL's `Out_[order(A,B)](o1)` is legal under `B_2PL`,
keeps `[A,B,C]` and removes `[B,A,C]` (both with the read), and every remaining
row has a remaining completion that does not commit `B` before `A` (aborting
`A` or `B` counts); the canonical `Out_{κ}(o1)` ends at `R[out ⪰ o1]`, which
contains 2PL's table and keeps `[B,A,C]` with the read.  (It is an output
retirement: rows that do not report the read are removed.)  2PL then emits
`o2` with `commit(A), commit(B), commit(C), order(A,C), order(C,B)`; the
canonical run emits `o2` with `κ_{o2} ≠ ε`; both end at the same state, and the
two runs are a `Lockstep` pair as in `«sec:systems/canonical-equivalent»`. -/
theorem «sec:systems/canonical-example» {T K : Type} {rd wr : T → K → Prop} {A B C : T}
    {x : K} (h : Txn.Partial.Distinct3 A B C) (hr : rd A x) (hnw : ∀ t, ¬ wr t x) :
    let σ0 := Txn.Partial.σABC rd wr h
    let k3 := Txn.Partial.tri A B C h
    let o1 := Txn.Partial.CanonEx.o1 A x
    let o2 := Txn.Partial.CanonEx.o2 A B C x
    let γ2 := Txn.Partial.CanonEx.γ2 (K := K) (rd := rd) (wr := wr) A B C
    ∃ τ1 τ2 τ1' τ2' : State (Txn.Partial.spec rd wr false),
      (Txn.Partial.read A x none).app σ0 = none ∧ Exposable σ0 o1 ∧ kappa σ0 o1 = [] ∧
      SysStep Txn.Partial.basis2PL σ0 (.output [Txn.Partial.order A B] o1) τ1 ∧
      τ1.R k3 (Txn.Partial.CanonEx.row A x [A, B, C] fun _ => False) ∧
      ¬ τ1.R k3 (Txn.Partial.CanonEx.row A x [B, A, C] fun _ => False) ∧
      (∀ k w, τ1.R k w → ∃ c, τ1.R k c ∧ Txn.Partitions k c.o ∧ w ≼ c ∧ ¬ c.o.lt B A) ∧
      CanonStep σ0 (.output (kappa σ0 o1) o1) τ1' ∧ τ1'.R = outputTable σ0 o1 ∧
      τ1'.R k3 (Txn.Partial.CanonEx.row A x [B, A, C] fun _ => False) ∧
      (∀ k u, τ1.R k u → τ1'.R k u) ∧
      SysStep Txn.Partial.basis2PL τ1 (.output γ2 o2) τ2 ∧
      CanonStep τ1' (.output (kappa τ1' o2) o2) τ2' ∧
      ¬ Exposable τ1' o2 ∧ kappa τ1' o2 ≠ [] ∧ τ2 = τ2' ∧
      Lockstep Txn.Partial.basis2PL σ0 [.output [Txn.Partial.order A B] o1, .output γ2 o2] τ2
        σ0 [.output (kappa σ0 o1) o1, .output (kappa τ1' o2) o2] τ2' :=
  Txn.Partial.CanonEx.example_2PL h hr hnw

/-! ## Coordination (§4.4, `sec:coordination`) -/

/-- §4.4: "We take coordination to mean a commitment: a binding decision that
removes behavior the specification still permits. … A mechanism used without
committing is not coordination.  Closing the polls after every voter has voted
still runs the mechanism, but no ballot is left to seal, so it removes nothing
the specification still permits and applies no commitment."  At the canonical
state of any full ballot, the poll-closing commitment `closePolls` is undefined
(it would remove no row). -/
theorem «sec:coordination/closing-after-voting» (i : CALM.Ballots)
    (hfull : i.b1.isSome ∧ i.b2.isSome ∧ i.b3.isSome) :
    (Figures.closePolls (sp := CALM.elec)).app (canon CALM.elec i) = none :=
  Figures.Elec.close_after_voting i hfull

/-- **Def. coordination** (`def:coordination`).  "A run or history coordinates
when one of its output events `Out_γ(o)` has `γ ≠ ε`, that is, applies a
commitment: a seal of inputs or a choice among outputs (Proposition
seal-or-choose)."

Lean: for runs, i.e. lists of system events.  (For histories of the `CC.CAP`
model the same condition is on the `out γ o` events of each participant.) -/
abbrev «def:coordination» {sp : Spec I O} (es : List (SEvent sp)) : Prop :=
  Coordinates es

/-- Def. `def:coordination`: "It is coordination-free, equivalently
commitment-free, when every output event is some `Out_ε(o)`; such events may
still perform output retirements." -/
abbrev «def:coordination/coordination-free» {sp : Spec I O} (es : List (SEvent sp)) : Prop :=
  CoordFree es

/-- Def. `def:coordination`: coordination-free is the negation of coordinates,
and coordination-free runs under any basis are exactly the commitment-free
executions (`ExecCF`) of §3 after erasing `γ`.  `Out_ε(o)` ends at
`R[out ⪰ o]`, so it may still retire rows (`«lem:canonical-commitment-normal-form»`
(3) in the App. C file). -/
theorem «def:coordination/commitment-free-runs» {sp : Spec I O} :
    (∀ es : List (SEvent sp), CoordFree es ↔ ¬ Coordinates es) ∧
    (∀ (B : Basis sp) (σ τ : State sp) (es : List (SEvent sp)),
      SysExec B σ es τ → CoordFree es → ExecCF σ (es.map SEvent.erase) τ) ∧
    (∀ (B : Basis sp) (σ τ : State sp) (es : List (Event I O)), ExecCF σ es τ →
      ∃ es' : List (SEvent sp), es'.map SEvent.erase = es ∧ CoordFree es' ∧
        SysExec B σ es' τ) :=
  ⟨coordFree_iff_not, fun _ _ _ _ h hf => coordFree_execCF h hf,
    fun B _ _ _ h => execCF_coordFree B h⟩

/-- **Prop. conflicting output events cannot be reconciled**
(`thm:commitments-require-coordination`).  "From a state `(i,R)`, let one
participant perform an output event after which no output at `i` refines `x`,
and let another perform an output event that emits `x`.  The two resulting
states cannot be brought to a common state with current input `i`."

Lean: `x ∈ R(i)` follows from the legality of `Out_{γ'}(x)`.  "Brought to a
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

/-- "The first event must apply a commitment, and that commitment is a choice
against `x`."

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

/-- "Complete CALM and the exposure boundary tie this to the specification:
Lifted Monotonicity holds exactly when every output at every state reachable
without commitment is exposable, so emitting outputs is coordination-free." -/
theorem «sec:coordination/lm-iff-coordination-free» (sp : Spec I O) :
    sp.LiftedMono ↔
      ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  (liftedMono_iff_commonExpansion sp).trans (exposure_boundary sp)

/-- "In the functional case, finding that continuation is trivial: the state is
fixed by the input (Corollary state-by-input), so delivering the full input
suffices." -/
theorem «sec:coordination/functional-reconciliation» {sp : Spec I O} (hf : sp.Functional)
    (hc : sp.Consistent) {τ : State sp} (hτ : IsRun τ) : τ = canon sp τ.cur :=
  state_by_input hf hc hτ

/-- "Participants at a common input `j` can reconcile by emitting some
`u ∈ S(j)` that refines everything any of them has emitted, and Lifted
Monotonicity guarantees that such a `u` exists … one strategy that terminates
is deterministic reconciliation: participants … apply the same rule for
choosing `u`, and arrive at the same state without any commitment: under Lifted
Monotonicity `u` is exposable, so each emits it by `Out_ε(u)`."

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
