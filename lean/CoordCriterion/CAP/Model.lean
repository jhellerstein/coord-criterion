import CoordCriterion.CompleteCALM.Theorem

/-!
# The system model for Complete CAP (Sections 4.1–4.5, namespace `CC.CAP`)

The self-contained system model used by Theorem `thm:complete-cap` and
Appendix `app:cap-response` (on top of `Foundations` and
`CompleteCALM/Theorem.lean`):

* commitments (Def. `def:commitment`) and output events of a system
  `Out γ o` (Def. `def:system-output-event`): `Commitment`, `applySeq`;
* distributed histories with explicit send/receive matching, consistent
  cuts, participant runs and continuations (Section `sec:histories`):
  `LEv`, `LRun`, `History`, `WF`, `IsCut`, `Extends`;
* systems with a commitment basis and (nondeterministic) local strategies
  (Def. `def:system`), and the histories a system *produces* (`System`,
  `Produced`);
* partitioned histories, Availability, Partition Consistency
  (Defs. `def:partitioned-history`, `def:partition-notions`,
  `def:partition-consistency`): `Partitioned`, `Availability`,
  `PartitionConsistency`;
* run and history lemmas used by the proofs, and `ce_exposable` (under the
  common-expansion condition every output of a run state's fiber is
  exposable).

`Distributed/Systems.lean` proves that these commitments and output events
coincide with those of `Distributed/Commitments.lean` (`CC.Dist.toCAP`,
`CC.Dist.ofCAP`, `CC.Dist.sysStep_iff_CAP`).  The theorem is in
`CAP/CompleteCAP.lean`, the response form in `CAP/ResponseForm.lean`.

## Modeling choices (precise readings)

1. *Participants.*  A finite participant set is `Fin n`; initial inputs are
   `init : Fin n → I`.
2. *Histories.*  A history is a finite list of local events per participant
   (`Fin n → List (LEv …)`); the list order is the total local order.  A
   receive `recv q k j d` names the sender `q`, the position `k` of the
   matching send in `q`'s local list, and the message content `(j, d)`; it is
   matched when `q ≠ p` and `q`'s `k`-th event is `send j d`.  The receiver
   therefore also sees the sender's identity and sequence number (harmless:
   it only gives strategies *more* information).
3. *Consistent cuts.*  Since local orders are total, a happens-before–closed
   set of events is a prefix of each participant's list closed under
   send→receive edges; we represent a cut by its prefix lengths `c : Fin n → Nat`.
4. *Output and commit events of a system.*  `out γ o` applies the commitment
   sequence `γ` (each a genuine commitment: partial, input-preserving,
   strictly row-removing, satisfying Eq. `commitment-excludes`), then is legal
   exactly when `(i,o)` survives and Eq. `lifted-validity` holds, i.e.
   `Exposable` at the committed state, and ends at `R_c[out ⪰ o]`.  This is
   literally `Step σc (.output o) τ ∧ Exposable σc o`.  A commit event
   `cmt γ` (`γ` nonempty) applies `γ` and stops there: no retirement, no
   output.
5. *Strategies are nondeterministic* (relations from local history to
   allowed next events), and may depend on the participant set, the initial
   inputs and the participant's identity, but otherwise only on the
   participant's local history.  The paper's Def. `def:system` says "a rule
   that chooses"; with *deterministic* strategies the (⇐) direction is false
   (a lone participant could not have both incomparable outputs of a fiber
   available; `deterministic_not_available` in `CAP/CompleteCAP.lean`).
   Appendix `app:cap-response` makes the nondeterministic reading explicit.
6. *Produced by the system.*  A history is produced when every event of each
   participant is allowed given its own local prefix: input events are always
   allowed (adversarial environment: any *legal* input to any participant at
   any time — legality is enforced by well-formedness); every other event must
   be allowed by the strategy, and output and commit events may use only
   basis commitments.  Locality of this condition is exactly the paper's
   "strategies depend only on local history", and it is what makes the
   (⇒) construction (gluing separate local runs) sound.
7. *Partitioned history.*  A labelling `comp : Fin n → Nat` with at least two
   distinct labels (two or more nonempty components) and no receive from a
   different component.
8. *Availability continuation.*  A continuation extends the cut's prefixes;
   for Availability it must be well formed, produced, partitioned by the same
   components, add events only at participants of `p`'s component, add no
   input event, and contain an output event of `p` emitting `o`.
9. *Partition Consistency continuation.*  Any well-formed continuation (it
   need not be partitioned or produced, and its output events may use
   arbitrary commitments) whose final cut puts every participant in the same
   state with current input `j`.
-/

namespace CC
namespace CAP

variable {I O : Type} [PO I] [PO O]

/-! ## Commitments and system output events -/

/-- Def. `def:commitment`: a partial function on specification states that
keeps the current input and removes a nonempty set of rows, none of which is
dominated by a row that remains at the same input. -/
structure Commitment (sp : Spec I O) where
  f : State sp → Option (State sp)
  cur_eq : ∀ σ τ, f σ = some τ → τ.cur = σ.cur
  sub : ∀ σ τ, f σ = some τ → ∀ k u, τ.R k u → σ.R k u
  strict : ∀ σ τ, f σ = some τ → ∃ k u, σ.R k u ∧ ¬ τ.R k u
  excl : ∀ σ τ, f σ = some τ → ∀ k u w, σ.R k u → ¬ τ.R k u → τ.R k w → ¬ (u ≼ w)

/-- Apply a commitment sequence `c₁ ⋯ cₙ`, each defined at the state its
predecessors leave. -/
def applySeq {sp : Spec I O} : State sp → List (Commitment sp) → Option (State sp)
  | σ, [] => some σ
  | σ, c :: cs =>
    match c.f σ with
    | some τ => applySeq τ cs
    | none => none

theorem applySeq_spec {sp : Spec I O} :
    ∀ (γ : List (Commitment sp)) (σ τ : State sp), applySeq σ γ = some τ →
      τ.cur = σ.cur ∧ ∀ k u, τ.R k u → σ.R k u
  | [], σ, τ, h => by
    simp [applySeq] at h; subst h; exact ⟨rfl, fun _ _ h => h⟩
  | c :: cs, σ, τ, h => by
    simp only [applySeq] at h
    split at h
    · rename_i τ1 h1
      obtain ⟨h2, h3⟩ := applySeq_spec cs τ1 τ h
      exact ⟨h2.trans (c.cur_eq _ _ h1), fun k u hu => c.sub _ _ h1 k u (h3 k u hu)⟩
    · cases h

/-- A nonempty commitment sequence that applies removes some row. -/
theorem applySeq_removes {sp : Spec I O} {γ : List (Commitment sp)} {σ σc : State sp}
    (hne : γ ≠ []) (h : applySeq σ γ = some σc) : ∃ k u, σ.R k u ∧ ¬ σc.R k u := by
  cases γ with
  | nil => exact absurd rfl hne
  | cons c cs =>
    simp only [applySeq] at h
    split at h
    · rename_i τ hτ
      obtain ⟨k, u, hu, hnu⟩ := c.strict σ τ hτ
      exact ⟨k, u, hu, fun h' => hnu ((applySeq_spec cs τ σc h).2 k u h')⟩
    · cases h

/-- Local (history) events of a participant among `n` participants with
message data `D`. -/
inductive LEv (sp : Spec I O) (D : Type) (n : Nat) where
  | inp (j : I)
  | out (γ : List (Commitment sp)) (o : O)
  | cmt (γ : List (Commitment sp))
  | send (j : Option I) (d : D)
  | recv (q : Fin n) (k : Nat) (j : Option I) (d : D)

variable {sp : Spec I O} {D : Type} {n : Nat}

/-- A participant's local event list as a transition sequence (item 3 of
Def. `def:distributed-history`): input events are `Step`s, output events are
legal `Out γ o` events, commit events `Commit(γ)` (`γ` nonempty) apply `γ`
with no retirement and no output, sends and receives leave the state
unchanged. -/
inductive LRun : State sp → List (LEv sp D n) → State sp → Prop where
  | nil (σ : State sp) : LRun σ [] σ
  | inp {σ τ ρ : State sp} {j : I} {es : List (LEv sp D n)} :
      Step σ (.input j) τ → LRun τ es ρ → LRun σ (.inp j :: es) ρ
  | out {σ σc τ ρ : State sp} {γ : List (Commitment sp)} {o : O} {es : List (LEv sp D n)} :
      applySeq σ γ = some σc → Step σc (.output o) τ → Exposable σc o →
      LRun τ es ρ → LRun σ (.out γ o :: es) ρ
  | cmt {σ τ ρ : State sp} {γ : List (Commitment sp)} {es : List (LEv sp D n)} :
      γ ≠ [] → applySeq σ γ = some τ → LRun τ es ρ → LRun σ (.cmt γ :: es) ρ
  | send {σ ρ : State sp} {j : Option I} {d : D} {es : List (LEv sp D n)} :
      LRun σ es ρ → LRun σ (.send j d :: es) ρ
  | recv {σ ρ : State sp} {q : Fin n} {k : Nat} {j : Option I} {d : D}
      {es : List (LEv sp D n)} :
      LRun σ es ρ → LRun σ (.recv q k j d :: es) ρ

/-! ## Distributed histories, cuts, continuations -/

/-- A distributed history: one finite local event list per participant. -/
abbrev History (sp : Spec I O) (D : Type) (n : Nat) := Fin n → List (LEv sp D n)

/-- Every receive has a matching send at another participant. -/
def RecvMatched (H : History sp D n) : Prop :=
  ∀ (p : Fin n) (a : List (LEv sp D n)) (q : Fin n) (k : Nat) (j : Option I) (d : D) b, H p = a ++ LEv.recv q k j d :: b →
    q ≠ p ∧ (H q)[k]? = some (LEv.send j d)

/-- Def. `def:distributed-history`: matched receives, and each participant's
events form a legal transition sequence from `σ_S(i_p)`. -/
def WF (init : Fin n → I) (H : History sp D n) : Prop :=
  (∀ p, ∃ τ, LRun (canon sp (init p)) (H p) τ) ∧ RecvMatched H

/-- Consistent cut, as prefix lengths closed under send→receive. -/
def IsCut (H : History sp D n) (c : Fin n → Nat) : Prop :=
  (∀ p, c p ≤ (H p).length) ∧
  ∀ (p : Fin n) (a : List (LEv sp D n)) (q : Fin n) (k : Nat) (j : Option I) (d : D) b, (H p).take (c p) = a ++ LEv.recv q k j d :: b → k < c q

/-- `H'` is a continuation of `H` at cut `c`, adding events `ext`. -/
def Extends (H : History sp D n) (c : Fin n → Nat) (H' : History sp D n)
    (ext : Fin n → List (LEv sp D n)) : Prop :=
  ∀ p, H' p = (H p).take (c p) ++ ext p

/-- Partitioned history: at least two components, no cross-component receive. -/
def Partitioned (H : History sp D n) (comp : Fin n → Nat) : Prop :=
  (∃ p q, comp p ≠ comp q) ∧
  ∀ (p : Fin n) (a : List (LEv sp D n)) (q : Fin n) (k : Nat) (j : Option I) (d : D) b, H p = a ++ LEv.recv q k j d :: b → comp q = comp p

/-- Confluence of a cut at `j`: some continuation has a final cut at which
every participant is in the same state `(j, R)`. -/
def ConfluentCut (init : Fin n → I) (H : History sp D n) (c : Fin n → Nat) (j : I) : Prop :=
  ∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)) (τ : State sp),
    Extends H c H' ext ∧ WF init H' ∧ τ.cur = j ∧
    ∀ p, LRun (canon sp (init p)) (H' p) τ

/-! ## Systems -/

/-- Def. `def:system`, with the extra requirement of
the system assumption after Def. `def:partitioned-history` (Section `sec:complete-cap`): a strategy for each participant of every finite
participant set and every choice of initial inputs.  Strategies are
nondeterministic: `strat n init p pre e` says that `p` may perform `e` after
local history `pre`. -/
structure System (sp : Spec I O) (D : Type) where
  basis : Commitment sp → Prop
  strat : (n : Nat) → (Fin n → I) → Fin n → List (LEv sp D n) → LEv sp D n → Prop

/-- Which next event a participant may perform after local history `pre`.
Inputs come from the adversarial environment and are always allowed (their
legality is checked by `LRun`). -/
def Allowed (Sys : System sp D) (n : Nat) (init : Fin n → I) (p : Fin n)
    (pre : List (LEv sp D n)) : LEv sp D n → Prop
  | .inp _ => True
  | .out γ o => (∀ c ∈ γ, Sys.basis c) ∧ Sys.strat n init p pre (.out γ o)
  | .cmt γ => (∀ c ∈ γ, Sys.basis c) ∧ Sys.strat n init p pre (.cmt γ)
  | .send j d => Sys.strat n init p pre (.send j d)
  | .recv q k j d => Sys.strat n init p pre (.recv q k j d)

/-- Every event of `l` is allowed given its local prefix. -/
def Compliant {E : Type} (A : List E → E → Prop) (l : List E) : Prop :=
  ∀ a e b, l = a ++ e :: b → A a e

/-- The history is produced by the system. -/
def Produced (Sys : System sp D) (n : Nat) (init : Fin n → I) (H : History sp D n) : Prop :=
  ∀ p, Compliant (Allowed Sys n init p) (H p)

/-- Def. `def:system` as worded in the paper: the strategies' output events
and commit events apply only commitments from the basis. -/
def System.BasisRespecting (Sys : System sp D) : Prop :=
  (∀ n init p pre γ o, Sys.strat n init p pre (.out γ o) → ∀ c ∈ γ, Sys.basis c) ∧
  (∀ n init p pre γ, Sys.strat n init p pre (.cmt γ) → ∀ c ∈ γ, Sys.basis c)

/-- The paper's reading of "produced": inputs from the environment, every
other event chosen by the strategy. -/
def StratAllowed (Sys : System sp D) (n : Nat) (init : Fin n → I) (p : Fin n)
    (pre : List (LEv sp D n)) : LEv sp D n → Prop
  | .inp _ => True
  | e => Sys.strat n init p pre e

/-- For a system whose strategies respect the basis, "produced" in the
paper's wording (`StratAllowed`) is `Allowed`. -/
theorem allowed_iff_stratAllowed {Sys : System sp D} (h : Sys.BasisRespecting)
    (n : Nat) (init : Fin n → I) (p : Fin n) (pre : List (LEv sp D n)) (e : LEv sp D n) :
    Allowed Sys n init p pre e ↔ StratAllowed Sys n init p pre e := by
  cases e with
  | inp j => exact Iff.rfl
  | out γ o => exact ⟨fun h' => h'.2, fun h' => ⟨h.1 n init p pre γ o h', h'⟩⟩
  | cmt γ => exact ⟨fun h' => h'.2, fun h' => ⟨h.2 n init p pre γ h', h'⟩⟩
  | send j d => exact Iff.rfl
  | recv q k j d => exact Iff.rfl

/-- Restricting a system's strategies to basis commitments. -/
def System.restrict (Sys : System sp D) : System sp D where
  basis := Sys.basis
  strat n init p pre e := Sys.strat n init p pre e ∧
    (∀ γ o, e = .out γ o → ∀ c ∈ γ, Sys.basis c) ∧
    (∀ γ, e = .cmt γ → ∀ c ∈ γ, Sys.basis c)

theorem System.restrict_basisRespecting (Sys : System sp D) : Sys.restrict.BasisRespecting :=
  ⟨fun _ _ _ _ γ o h => h.2.1 γ o rfl, fun _ _ _ _ γ h => h.2.2 γ rfl⟩

/-- Restricting loses nothing: the restricted system allows exactly the same
events, so it produces the same histories. -/
theorem System.restrict_allowed (Sys : System sp D) (n : Nat) (init : Fin n → I) (p : Fin n)
    (pre : List (LEv sp D n)) (e : LEv sp D n) :
    Allowed Sys.restrict n init p pre e ↔ Allowed Sys n init p pre e := by
  cases e with
  | inp j => exact Iff.rfl
  | out γ o =>
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, (fun γ' o' he => by cases he; exact h.1),
      fun _ he => by cases he⟩⟩
  | cmt γ =>
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, (fun _ _ he => by cases he),
      fun γ' he => by cases he; exact h.1⟩⟩
  | send j d => exact ⟨fun h => h.1, fun h => ⟨h, (fun _ _ he => by cases he),
      fun _ he => by cases he⟩⟩
  | recv q k j d => exact ⟨fun h => h.1, fun h => ⟨h, (fun _ _ he => by cases he),
      fun _ he => by cases he⟩⟩

/-- Def. `def:partition-notions`: Availability (interface form). -/
def Availability (Sys : System sp D) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ c, IsCut H c →
    ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) ((H p).take (c p)) σ →
    ∀ o, σ.R σ.cur o →
    ∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)),
      Extends H c H' ext ∧ WF init H' ∧ Produced Sys n init H' ∧ Partitioned H' comp ∧
      (∀ q, comp q ≠ comp p → ext q = []) ∧
      (∀ q j, LEv.inp j ∉ ext q) ∧
      ∃ γ, LEv.out γ o ∈ ext p

/-- Def. `def:partition-consistency`: Partition Consistency. -/
def PartitionConsistency (Sys : System sp D) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ c, IsCut H c →
    ∀ j : I, (∀ p σ, LRun (canon sp (init p)) ((H p).take (c p)) σ → σ.cur ≼ j) →
    ConfluentCut init H c j

/-- The commitment-free system of Theorem `thm:complete-cap`: empty basis
(so every output event is some `Out ε o`, legal iff `o` is exposable), and a
strategy that allows every event. -/
def cfSystem (sp : Spec I O) (D : Type) : System sp D where
  basis := fun _ => False
  strat := fun _ _ _ _ _ => True


/-! ## Run lemmas -/

theorem step_input_inv {σ τ : State sp} {j : I} (h : Step σ (.input j) τ) :
    (∃ u, σ.R j u) ∧ τ.cur = j ∧ τ.R = inputTable σ j :=
  match h with
  | .input _ _ _ h1 h2 h3 => ⟨h1, h2, h3⟩

theorem step_output_inv {σ τ : State sp} {o : O} (h : Step σ (.output o) τ) :
    σ.R σ.cur o ∧ τ.cur = σ.cur ∧ τ.R = outputTable σ o :=
  match h with
  | .output _ _ _ h1 h2 h3 => ⟨h1, h2, h3⟩

theorem lrun_append {a b : List (LEv sp D n)} {σ ρ : State sp} :
    LRun σ (a ++ b) ρ ↔ ∃ τ, LRun σ a τ ∧ LRun τ b ρ := by
  induction a generalizing σ with
  | nil => exact ⟨fun h => ⟨σ, .nil σ, h⟩, fun ⟨τ, h1, h2⟩ => by cases h1; exact h2⟩
  | cons e a ih =>
    rw [List.cons_append]
    constructor
    · intro h
      cases h with
      | inp hs hr => obtain ⟨τ, h1, h2⟩ := ih.1 hr; exact ⟨τ, .inp hs h1, h2⟩
      | out ha hs hx hr => obtain ⟨τ, h1, h2⟩ := ih.1 hr; exact ⟨τ, .out ha hs hx h1, h2⟩
      | cmt hne ha hr => obtain ⟨τ, h1, h2⟩ := ih.1 hr; exact ⟨τ, .cmt hne ha h1, h2⟩
      | send hr => obtain ⟨τ, h1, h2⟩ := ih.1 hr; exact ⟨τ, .send h1, h2⟩
      | recv hr => obtain ⟨τ, h1, h2⟩ := ih.1 hr; exact ⟨τ, .recv h1, h2⟩
    · rintro ⟨τ, h1, h2⟩
      cases h1 with
      | inp hs hr => exact .inp hs (ih.2 ⟨τ, hr, h2⟩)
      | out ha hs hx hr => exact .out ha hs hx (ih.2 ⟨τ, hr, h2⟩)
      | cmt hne ha hr => exact .cmt hne ha (ih.2 ⟨τ, hr, h2⟩)
      | send hr => exact .send (ih.2 ⟨τ, hr, h2⟩)
      | recv hr => exact .recv (ih.2 ⟨τ, hr, h2⟩)

/-- Along a participant run the current input only grows and rows are only
removed ("events never add rows"). -/
theorem lrun_mono {σ τ : State sp} {l : List (LEv sp D n)} (h : LRun σ l τ) :
    σ.cur ≼ τ.cur ∧ ∀ k u, τ.R k u → σ.R k u := by
  induction h with
  | nil σ => exact ⟨PO.refl _, fun _ _ h => h⟩
  | @inp σ τ ρ j es hs _ ih =>
    refine ⟨?_, fun k u h => step_sub hs k u (ih.2 k u h)⟩
    obtain ⟨⟨u, hu⟩, hcur, _⟩ := step_input_inv hs
    have hj : σ.cur ≼ τ.cur := by rw [hcur]; exact σ.above _ _ hu
    exact PO.trans hj ih.1
  | @out σ σc τ ρ γ o es ha hs _ _ ih =>
    obtain ⟨hc1, hc2⟩ := applySeq_spec γ σ σc ha
    have hsub := step_sub hs
    refine ⟨?_, fun k u h => hc2 k u (hsub k u (ih.2 k u h))⟩
    have : τ.cur = σc.cur := (step_output_inv hs).2.1
    rw [← hc1, ← this]; exact ih.1
  | @cmt σ τ ρ γ es _ ha _ ih =>
    obtain ⟨hc1, hc2⟩ := applySeq_spec γ σ τ ha
    exact ⟨hc1 ▸ ih.1, fun k u h => hc2 k u (ih.2 k u h)⟩
  | send _ ih => exact ih
  | recv _ ih => exact ih

/-- After a run that emits `o`, every remaining row's output expands `o`
(containment, Lemma `lem:canonical-commitment-normal-form`(1)). -/
theorem lrun_out_mem {σ τ : State sp} {l : List (LEv sp D n)} (h : LRun σ l τ)
    {γ : List (Commitment sp)} {o : O} (hm : LEv.out γ o ∈ l) :
    ∀ k x, τ.R k x → o ≼ x := by
  induction h with
  | nil => cases hm
  | inp _ _ ih => exact ih (by simpa using hm)
  | @out σ σc τ' ρ γ' o' es _ hs _ hr ih =>
    rcases List.mem_cons.1 hm with he | hm'
    · cases he
      intro k x hx
      have hx' := (lrun_mono hr).2 k x hx
      rw [(step_output_inv hs).2.2] at hx'; exact hx'.2
    · exact ih hm'
  | cmt _ _ _ ih => exact ih (by simpa using hm)
  | send _ ih => exact ih (by simpa using hm)
  | recv _ ih => exact ih (by simpa using hm)

/-- Without input events the current input does not change. -/
theorem lrun_noinp {σ τ : State sp} {l : List (LEv sp D n)} (h : LRun σ l τ)
    (hn : ∀ j, LEv.inp j ∉ l) : τ.cur = σ.cur := by
  induction h with
  | nil => rfl
  | inp _ _ _ => exact absurd (List.mem_cons_self ..) (hn _)
  | @out σ σc τ' ρ γ o es ha hs _ _ ih =>
    have h1 := ih (fun j hj => hn j (List.mem_cons_of_mem _ hj))
    have hc1 := (applySeq_spec γ σ σc ha).1
    rw [h1, (step_output_inv hs).2.1, hc1]
  | @cmt σ τ ρ γ es _ ha _ ih =>
    rw [ih (fun j hj => hn j (List.mem_cons_of_mem _ hj)), (applySeq_spec γ σ τ ha).1]
  | send _ ih => exact ih (fun j hj => hn j (List.mem_cons_of_mem _ hj))
  | recv _ ih => exact ih (fun j hj => hn j (List.mem_cons_of_mem _ hj))

/-- Participant runs are deterministic, so "the state at a cut" is well defined. -/
theorem lrun_det {σ τ τ' : State sp} {l : List (LEv sp D n)} (h : LRun σ l τ)
    (h' : LRun σ l τ') : τ = τ' := by
  induction h generalizing τ' with
  | inp hs _ ih =>
    cases h' with
    | inp hs' hr' =>
      apply ih
      obtain ⟨_, hc, hR⟩ := step_input_inv hs
      obtain ⟨_, hc', hR'⟩ := step_input_inv hs'
      have := State.ext' (hc.trans hc'.symm) (hR.trans hR'.symm)
      subst this; exact hr'
  | out ha hs _ _ ih =>
    cases h' with
    | out ha' hs' _ hr' =>
      rw [ha] at ha'; cases ha'
      apply ih
      obtain ⟨_, hc, hR⟩ := step_output_inv hs
      obtain ⟨_, hc', hR'⟩ := step_output_inv hs'
      have := State.ext' (hc.trans hc'.symm) (hR.trans hR'.symm)
      subst this; exact hr'
  | cmt _ ha _ ih =>
    cases h' with
    | cmt _ ha' hr' => rw [ha] at ha'; cases ha'; exact ih hr'
  | nil => cases h'; rfl
  | send _ ih => cases h' with | send hr' => exact ih hr'
  | recv _ ih => cases h' with | recv hr' => exact ih hr'

/-- A participant run whose output and commit events apply no commitment (so,
since commit events are nonempty, it has no commit event and every output
event is `Out ε o`) is a canonical (Section 3) execution. -/
theorem lrun_cf {σ τ : State sp} {l : List (LEv sp D n)} (h : LRun σ l τ)
    (hcf : ∀ γ o, LEv.out γ o ∈ l → γ = []) (hnc : ∀ γ, LEv.cmt γ ∈ l → γ = []) :
    ∃ es, Exec σ es τ := by
  induction h with
  | nil σ => exact ⟨[], .nil σ⟩
  | inp hs _ ih =>
    obtain ⟨es, hx⟩ := ih (fun γ o hm => hcf γ o (List.mem_cons_of_mem _ hm))
      (fun γ hm => hnc γ (List.mem_cons_of_mem _ hm))
    exact ⟨_, .cons hs hx⟩
  | @out σ σc τ' ρ γ o es ha hs _ _ ih =>
    obtain ⟨es, hx⟩ := ih (fun γ o hm => hcf γ o (List.mem_cons_of_mem _ hm))
      (fun γ hm => hnc γ (List.mem_cons_of_mem _ hm))
    have hγ := hcf γ o (List.mem_cons_self ..)
    subst hγ
    simp [applySeq] at ha; subst ha
    exact ⟨_, .cons hs hx⟩
  | cmt hne _ _ _ => exact absurd (hnc _ (List.mem_cons_self ..)) hne
  | send _ ih =>
    exact ih (fun γ o hm => hcf γ o (List.mem_cons_of_mem _ hm))
      (fun γ hm => hnc γ (List.mem_cons_of_mem _ hm))
  | recv _ ih =>
    exact ih (fun γ o hm => hcf γ o (List.mem_cons_of_mem _ hm))
      (fun γ hm => hnc γ (List.mem_cons_of_mem _ hm))

/-! ## Lifted Monotonicity and the common-expansion condition -/

/-- Under the common-expansion condition every output in the current fiber of
a residual state (in particular any run state) is exposable. -/
theorem ce_exposable (hce : sp.CommonExpansion) {σ : State sp} {E : List O}
    (hσ : Residual σ E) {o : O} (ho : σ.R σ.cur o) : Exposable σ o := by
  intro k x hkx _
  obtain ⟨hSo, _, hEo⟩ := (hσ _ _).1 ho
  obtain ⟨hSx, hck, hEx⟩ := (hσ _ _).1 hkx
  obtain ⟨u, hSu, hu⟩ := hce [(σ.cur, o), (k, x)]
    (by intro r hr; simp at hr; rcases hr with rfl | rfl <;> assumption) k
    (by intro r hr; simp at hr; rcases hr with rfl | rfl
        · exact hck
        · exact PO.refl _)
  have hou : o ≼ u := hu (σ.cur, o) (by simp)
  have hxu : x ≼ u := hu (k, x) (by simp)
  exact ⟨u, (hσ _ _).2 ⟨hSu, hck, fun e he => PO.trans (hEx e he) hxu⟩, hou, hxu⟩

/-- The commitment-free event list corresponding to a canonical execution. -/
def toL : List (Event I O) → List (LEv sp D n)
  | [] => []
  | .input j :: es => .inp j :: toL es
  | .output o :: es => .out [] o :: toL es

theorem toL_norecv : ∀ (es : List (Event I O)) (q : Fin n) (k : Nat) (j : Option I) (d : D),
    LEv.recv q k j d ∉ toL (sp := sp) es
  | [], _, _, _, _ => by simp [toL]
  | .input _ :: es, q, k, j, d => by simp [toL]; exact toL_norecv es q k j d
  | .output _ :: es, q, k, j, d => by simp [toL]; exact toL_norecv es q k j d

/-- Under the common-expansion condition a canonical execution from a residual
state is realized by `Out ε` events. -/
theorem exec_to_lrun (hce : sp.CommonExpansion) {σ τ : State sp} {es : List (Event I O)}
    (hx : Exec σ es τ) {E : List O} (hσ : Residual σ E) :
    LRun (D := D) (n := n) σ (toL es) τ := by
  induction hx generalizing E with
  | nil σ => exact .nil σ
  | @cons σ τ' ρ e es hs _ ih =>
    have hres := residual_step hσ hs
    cases e with
    | input j => exact .inp hs (ih hres)
    | output o =>
      exact .out (σc := σ) rfl hs (ce_exposable hce hσ (step_output_inv hs).1) (ih hres)

theorem exec_cur_le {σ τ : State sp} {es : List (Event I O)} (hx : Exec σ es τ) :
    σ.cur ≼ τ.cur := by
  induction hx with
  | nil => exact PO.refl _
  | @cons σ τ' ρ e es hs _ ih =>
    cases e with
    | input j =>
      obtain ⟨⟨u, hu⟩, hcur, _⟩ := step_input_inv hs
      have : σ.cur ≼ τ'.cur := by rw [hcur]; exact σ.above _ _ hu
      exact PO.trans this ih
    | output o => rw [← (step_output_inv hs).2.1]; exact ih

/-- Each emitted output of a canonical execution is witnessed by a row of `S`
at an input below the final current input. -/
theorem exec_rows {σ τ : State sp} {es : List (Event I O)} (hx : Exec σ es τ) :
    ∃ rows : List (I × O), rows.map Prod.snd = outs es ∧
      ∀ r ∈ rows, sp.S r.1 r.2 ∧ r.1 ≼ τ.cur := by
  induction hx with
  | nil => exact ⟨[], rfl, by simp⟩
  | @cons σ τ' ρ e es hs hr ih =>
    obtain ⟨rows, hm, hrw⟩ := ih
    cases e with
    | input j => exact ⟨rows, by simpa [outs] using hm, hrw⟩
    | output o =>
      obtain ⟨hleg, hcur, _⟩ := step_output_inv hs
      refine ⟨(σ.cur, o) :: rows, by simp [outs, hm], ?_⟩
      intro r hmem
      rcases List.mem_cons.1 hmem with rfl | hr'
      · refine ⟨σ.sub _ _ hleg, ?_⟩
        have := exec_cur_le hr; rw [hcur] at this; exact this
      · exact hrw r hr'


/-! ## History lemmas -/

theorem split_left {α : Type} {x y a b : List α} {e : α} (h : x ++ y = a ++ e :: b)
    (he : e ∉ y) : ∃ b', x = a ++ e :: b' := by
  rcases List.append_eq_append_iff.1 h with ⟨as, _, hy⟩ | ⟨bs, hx, hb⟩
  · exact absurd (by rw [hy]; simp) he
  · cases bs with
    | nil => simp at hb; exact absurd (by rw [← hb]; simp) he
    | cons e' bs' =>
      simp only [List.cons_append, List.cons.injEq] at hb
      obtain ⟨rfl, _⟩ := hb
      exact ⟨bs', hx⟩

theorem compliant_take {E : Type} {A : List E → E → Prop} {l : List E} (hl : Compliant A l)
    (c : Nat) : Compliant A (l.take c) := by
  intro a e b h
  apply hl a e (b ++ l.drop c)
  conv => lhs; rw [← List.take_append_drop c l]
  rw [h]; simp

theorem compliant_append {E : Type} {A : List E → E → Prop} {x y : List E} (hx : Compliant A x)
    (hy : ∀ a e b, y = a ++ e :: b → A (x ++ a) e) : Compliant A (x ++ y) := by
  intro a e b h
  rcases List.append_eq_append_iff.1 h with ⟨as, ha, hys⟩ | ⟨bs, hxs, hb⟩
  · rw [ha]; exact hy as e b hys
  · cases bs with
    | nil =>
      simp at hxs; subst hxs
      have := hy [] e b (by simp [hb])
      simpa using this
    | cons e' bs' =>
      simp only [List.cons_append, List.cons.injEq] at hb
      obtain ⟨rfl, _⟩ := hb
      exact hx a e bs' hxs

theorem lrun_take {σ τ : State sp} {l : List (LEv sp D n)} (h : LRun σ l τ) (c : Nat) :
    ∃ σ', LRun σ (l.take c) σ' := by
  rw [← List.take_append_drop c l] at h
  obtain ⟨σ', h1, _⟩ := lrun_append.1 h
  exact ⟨σ', h1⟩

/-- A cut's prefix decomposes the local history. -/
theorem take_split {l a b : List (LEv sp D n)} {e : LEv sp D n} {c : Nat}
    (h : l.take c = a ++ e :: b) : l = a ++ e :: (b ++ l.drop c) := by
  conv => lhs; rw [← List.take_append_drop c l]
  rw [h]; simp

theorem recvMatched_extend {H H' : History sp D n} {c : Fin n → Nat}
    {ext : Fin n → List (LEv sp D n)} (hm : RecvMatched H) (hc : IsCut H c)
    (hext : Extends H c H' ext) (hnr : ∀ p q k j d, LEv.recv q k j d ∉ ext p) :
    RecvMatched H' := by
  intro p a q k j d b h
  rw [hext p] at h
  obtain ⟨b', hb'⟩ := split_left h (hnr p q k j d)
  have hk := hc.2 p a q k j d b' hb'
  obtain ⟨hne, hs⟩ := hm p a q k j d _ (take_split hb')
  refine ⟨hne, ?_⟩
  rw [hext q]
  have hlt : k < ((H q).take (c q)).length := by
    rw [List.length_take]; have := (List.getElem?_eq_some_iff.1 hs).1; omega
  rw [List.getElem?_append_left hlt, List.getElem?_take]; simp [hk, hs]

theorem partitioned_extend {H H' : History sp D n} {c : Fin n → Nat}
    {ext : Fin n → List (LEv sp D n)} {comp : Fin n → Nat} (hp : Partitioned H comp)
    (hext : Extends H c H' ext) (hnr : ∀ p q k j d, LEv.recv q k j d ∉ ext p) :
    Partitioned H' comp := by
  refine ⟨hp.1, ?_⟩
  intro p a q k j d b h
  rw [hext p] at h
  obtain ⟨b', hb'⟩ := split_left h (hnr p q k j d)
  exact hp.2 p a q k j d _ (take_split hb')

end CAP
end CC
