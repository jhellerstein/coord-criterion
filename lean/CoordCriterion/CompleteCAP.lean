/-
# Complete CAP (Section 4.5, Theorem `thm:complete-cap`)

This file formalizes, self-contained on top of `Core` and `Runs`:

* commitments (Def. `def:commitment`) and output events of a system
  `Out γ o` (Def. `def:system-output-event`);
* distributed histories with explicit send/receive matching, consistent
  cuts, participant runs and continuations (Section `sec:histories`);
* systems with a commitment basis and (nondeterministic) local strategies
  (Def. `def:system`), and the histories a system *produces*;
* partitioned histories, Availability, Partition Consistency
  (Def. `def:partition-notions`);
* Theorem `thm:complete-cap` in both directions, including the "moreover"
  clause (the commitment-free system has both properties): `complete_cap`,
  `complete_cap_cf`, `cap_necessary`;
* a counterexample showing that the (⇐) direction needs nondeterministic
  strategies: `deterministic_not_available`;
* Appendix `app:cap-response`: Response Availability / Response Partition
  Consistency, Lemma `lem:forced-answer` (`forced_answer`), its abstract
  impossibility consequence (`forced_answer_impossibility`), and Theorem
  `thm:complete-cap-response` in both directions (`complete_cap_response`).
  The register instance behind Corollary `cor:gilbert-lynch` is in
  `GilbertLynch.lean`.

## Modeling choices (documented deviations / precise readings)

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
4. *Output events of a system.*  `out γ o` applies the commitment sequence `γ`
   (each a genuine commitment: partial, input-preserving, strictly
   row-removing, satisfying Eq. `commitment-excludes`), then is legal exactly
   when `(i,o)` survives and Eq. `lifted-validity` holds, i.e. `Exposable` at
   the committed state, and ends at `R_c[out ⪰ o]`.  This is literally
   `Step σc (.output o) τ ∧ Exposable σc o`.
5. *Strategies are nondeterministic* (relations from local history to
   allowed next events), and may depend on the participant set, the initial
   inputs and the participant's identity, but otherwise only on the
   participant's local history.  The paper's Def. `def:system` says "a rule
   that chooses"; with *deterministic* strategies the (⇐) direction is false
   (a lone participant could not have both incomparable outputs of a fiber
   available) — see the report.  Appendix `app:cap-response` makes the
   nondeterministic reading explicit.
6. *Produced by the system.*  A history is produced when every event of each
   participant is allowed given its own local prefix: input events are always
   allowed (adversarial environment: any *legal* input to any participant at
   any time — legality is enforced by well-formedness); every other event must
   be allowed by the strategy, and output events may use only basis
   commitments.  Locality of this condition is exactly the paper's
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
import CoordCriterion.Core
import CoordCriterion.Runs

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

/-- Local (history) events of a participant among `n` participants with
message data `D`. -/
inductive LEv (sp : Spec I O) (D : Type) (n : Nat) where
  | inp (j : I)
  | out (γ : List (Commitment sp)) (o : O)
  | send (j : Option I) (d : D)
  | recv (q : Fin n) (k : Nat) (j : Option I) (d : D)

variable {sp : Spec I O} {D : Type} {n : Nat}

/-- A participant's local event list as a transition sequence (item 3 of
Def. `def:distributed-history`): input events are `Step`s, output events are
legal `Out γ o` events, sends and receives leave the state unchanged. -/
inductive LRun : State sp → List (LEv sp D n) → State sp → Prop where
  | nil (σ : State sp) : LRun σ [] σ
  | inp {σ τ ρ : State sp} {j : I} {es : List (LEv sp D n)} :
      Step σ (.input j) τ → LRun τ es ρ → LRun σ (.inp j :: es) ρ
  | out {σ σc τ ρ : State sp} {γ : List (Commitment sp)} {o : O} {es : List (LEv sp D n)} :
      applySeq σ γ = some σc → Step σc (.output o) τ → Exposable σc o →
      LRun τ es ρ → LRun σ (.out γ o :: es) ρ
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

/-- Def. `def:system`, with the extra requirement of Def.
`def:partition-notions`(2): a strategy for each participant of every finite
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
  | .send j d => Sys.strat n init p pre (.send j d)
  | .recv q k j d => Sys.strat n init p pre (.recv q k j d)

/-- Every event of `l` is allowed given its local prefix. -/
def Compliant {E : Type} (A : List E → E → Prop) (l : List E) : Prop :=
  ∀ a e b, l = a ++ e :: b → A a e

/-- The history is produced by the system. -/
def Produced (Sys : System sp D) (n : Nat) (init : Fin n → I) (H : History sp D n) : Prop :=
  ∀ p, Compliant (Allowed Sys n init p) (H p)

/-- Def. `def:partition-notions`(4): Availability (interface form). -/
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

/-- Def. `def:partition-notions`(5): Partition Consistency. -/
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
      | send hr => obtain ⟨τ, h1, h2⟩ := ih.1 hr; exact ⟨τ, .send h1, h2⟩
      | recv hr => obtain ⟨τ, h1, h2⟩ := ih.1 hr; exact ⟨τ, .recv h1, h2⟩
    · rintro ⟨τ, h1, h2⟩
      cases h1 with
      | inp hs hr => exact .inp hs (ih.2 ⟨τ, hr, h2⟩)
      | out ha hs hx hr => exact .out ha hs hx (ih.2 ⟨τ, hr, h2⟩)
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
  | nil => cases h'; rfl
  | send _ ih => cases h' with | send hr' => exact ih hr'
  | recv _ ih => cases h' with | recv hr' => exact ih hr'

/-- A participant run whose output events are all `Out ε o` is a canonical
(Section 3) execution. -/
theorem lrun_cf {σ τ : State sp} {l : List (LEv sp D n)} (h : LRun σ l τ)
    (hcf : ∀ γ o, LEv.out γ o ∈ l → γ = []) : ∃ es, Exec σ es τ := by
  induction h with
  | nil σ => exact ⟨[], .nil σ⟩
  | inp hs _ ih =>
    obtain ⟨es, hx⟩ := ih (fun γ o hm => hcf γ o (List.mem_cons_of_mem _ hm))
    exact ⟨_, .cons hs hx⟩
  | @out σ σc τ' ρ γ o es ha hs _ _ ih =>
    obtain ⟨es, hx⟩ := ih (fun γ o hm => hcf γ o (List.mem_cons_of_mem _ hm))
    have hγ := hcf γ o (List.mem_cons_self ..)
    subst hγ
    simp [applySeq] at ha; subst ha
    exact ⟨_, .cons hs hx⟩
  | send _ ih => exact ih (fun γ o hm => hcf γ o (List.mem_cons_of_mem _ hm))
  | recv _ ih => exact ih (fun γ o hm => hcf γ o (List.mem_cons_of_mem _ hm))

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

theorem liftedMono_of_ce (h : sp.CommonExpansion) : sp.LiftedMono := by
  intro i j hij X _ hX
  obtain ⟨u, hu, hall⟩ := h (X.map (fun x => (i, x)))
    (by intro r hr; simp at hr; obtain ⟨x, hx, rfl⟩ := hr; exact hX x hx) j
    (by intro r hr; simp at hr; obtain ⟨x, _, rfl⟩ := hr; exact hij)
  exact ⟨u, hu, fun x hx => hall (i, x) (by simp; exact hx)⟩

theorem ce_of_liftedMono (h : sp.LiftedMono) : sp.CommonExpansion := by
  intro rows hrows j hj
  cases rows with
  | nil => obtain ⟨u, hu⟩ := sp.total j; exact ⟨u, hu, by simp⟩
  | cons r0 rs =>
    -- each row lifts to some output at `j`
    have hlift : ∀ r ∈ r0 :: rs, ∃ w, sp.S j w ∧ r.2 ≼ w := by
      intro r hr
      obtain ⟨w, hw, hle⟩ := h r.1 j (hj r hr) [r.2] (by simp) (by simp; exact hrows r hr)
      exact ⟨w, hw, hle r.2 (by simp)⟩
    let W : List O := (r0 :: rs).attach.map (fun r => Classical.choose (hlift r.1 r.2))
    obtain ⟨u, hu, hall⟩ := h j j (PO.refl j) W (by simp [W])
      (by intro w hw; simp only [W, List.mem_map] at hw
          obtain ⟨r, _, rfl⟩ := hw; exact (Classical.choose_spec (hlift r.1 r.2)).1)
    refine ⟨u, hu, fun r hr => ?_⟩
    have hw := (Classical.choose_spec (hlift r hr)).2
    exact PO.trans hw (hall _ (by
      simp only [W, List.mem_map]; exact ⟨⟨r, hr⟩, List.mem_attach _ _, rfl⟩))

/-- Prop. `prop:common-expansion-form`. -/
theorem liftedMono_iff_ce : sp.LiftedMono ↔ sp.CommonExpansion :=
  ⟨ce_of_liftedMono, liftedMono_of_ce⟩

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

/-! ## The commitment-free system -/

theorem cf_allowed {N : Nat} {init : Fin N → I} {p : Fin N} {pre : List (LEv sp D N)}
    {e : LEv sp D N} (he : ∀ γ o, e = .out γ o → γ = []) :
    Allowed (cfSystem sp D) N init p pre e := by
  cases e with
  | inp => trivial
  | out γ o =>
    have := he γ o rfl; subst this
    exact ⟨by simp, trivial⟩
  | send => trivial
  | recv => trivial

theorem compliant_cf_out {N : Nat} {init : Fin N → I} {p : Fin N} {l : List (LEv sp D N)}
    (h : Compliant (Allowed (cfSystem sp D) N init p) l) :
    ∀ γ o, LEv.out γ o ∈ l → γ = [] := by
  intro γ o hm
  obtain ⟨a, b, hab⟩ := List.append_of_mem hm
  have := (h a _ b hab).1
  cases γ with
  | nil => rfl
  | cons c _ => exact absurd (this c (List.mem_cons_self ..)) id

/-- Every history the commitment-free system produces is coordination-free
(Def. `def:coordination`): each output event is some `Out ε o`. -/
theorem cfSystem_coordinationFree {N : Nat} {init : Fin N → I} {H : History sp D N}
    (h : Produced (cfSystem sp D) N init H) : ∀ p γ o, LEv.out γ o ∈ H p → γ = [] :=
  fun p => compliant_cf_out (h p)

theorem cf_availability (hlm : sp.LiftedMono) : Availability (cfSystem sp D) := by
  have hce := ce_of_liftedMono hlm
  intro N init H comp hwf hprod hpart c hcut p σ hσ o ho
  classical
  obtain ⟨es, hx⟩ := lrun_cf hσ (compliant_cf_out (compliant_take (hprod p) (c p)))
  have hres : Residual σ (outs es) := run_residual hx
  have hexp : Exposable σ o := ce_exposable hce hres ho
  let τ : State sp :=
    { cur := σ.cur
      R := outputTable σ o
      sub := fun k u h => σ.sub k u h.1
      hasCur := ⟨o, ho, PO.refl o⟩
      above := fun k u h => σ.above k u h.1 }
  have hstep : Step σ (.output o) τ := Step.output σ τ o ho rfl rfl
  let ext : Fin N → List (LEv sp D N) := fun q => if q = p then [.out [] o] else []
  have hnr : ∀ p' q k j d, LEv.recv q k j d ∉ ext p' := by
    intro p' q k j d; simp only [ext]; split <;> simp
  have hext : Extends H c (fun q => (H q).take (c q) ++ ext q) ext := fun _ => rfl
  refine ⟨_, ext, hext, ⟨?_, recvMatched_extend hwf.2 hcut hext hnr⟩, ?_,
    partitioned_extend hpart hext hnr, ?_, ?_, ⟨[], by simp [ext]⟩⟩
  · intro q
    obtain ⟨τq, hq⟩ := hwf.1 q
    by_cases hqp : q = p
    · subst hqp
      refine ⟨τ, lrun_append.2 ⟨σ, hσ, ?_⟩⟩
      have hq : ext q = [.out [] o] := by simp [ext]
      rw [hq]
      exact .out rfl hstep hexp (.nil τ)
    · obtain ⟨σq, hσq⟩ := lrun_take hq (c q)
      refine ⟨σq, ?_⟩
      have hq' : ext q = [] := by simp [ext, hqp]
      show LRun _ ((H q).take (c q) ++ ext q) σq
      rw [hq', List.append_nil]; exact hσq
  · intro q
    apply compliant_append (compliant_take (hprod q) (c q))
    intro a e b he
    apply cf_allowed
    intro γ o' hγ
    subst hγ
    have hm : LEv.out γ o' ∈ ext q := by rw [he]; simp
    simp only [ext] at hm; split at hm <;> simp at hm
    exact hm.1
  · intro q hq
    have : q ≠ p := fun h => hq (h ▸ rfl)
    simp [ext, this]
  · intro q j; simp only [ext]; split <;> simp

theorem cf_partitionConsistency (hlm : sp.LiftedMono) :
    PartitionConsistency (cfSystem sp D) := by
  have hce := ce_of_liftedMono hlm
  intro N init H comp hwf hprod _ c hcut j hj
  classical
  have hX : ∀ p, ∃ x : State sp × List (I × O),
      LRun (canon sp (init p)) ((H p).take (c p)) x.1 ∧ Residual x.1 (x.2.map Prod.snd) ∧
      ∀ r ∈ x.2, sp.S r.1 r.2 ∧ r.1 ≼ x.1.cur := by
    intro p
    obtain ⟨τp, hp⟩ := hwf.1 p
    obtain ⟨σ, hσ⟩ := lrun_take hp (c p)
    obtain ⟨es, hx⟩ := lrun_cf hσ (compliant_cf_out (compliant_take (hprod p) (c p)))
    obtain ⟨rows, hm, hr⟩ := exec_rows hx
    refine ⟨(σ, rows), hσ, ?_, hr⟩
    show Residual σ (rows.map Prod.snd)
    rw [hm]; exact run_residual hx
  let X := fun p => Classical.choose (hX p)
  have hXs : ∀ p, _ := fun p => Classical.choose_spec (hX p)
  let all := (List.finRange N).flatMap (fun p => (X p).2)
  obtain ⟨u, hju, hu⟩ := hce all
    (by intro r hr; simp only [all, List.mem_flatMap] at hr
        obtain ⟨p, _, hr⟩ := hr; exact ((hXs p).2.2 r hr).1) j
    (by intro r hr; simp only [all, List.mem_flatMap] at hr
        obtain ⟨p, _, hr⟩ := hr
        exact PO.trans ((hXs p).2.2 r hr).2 (hj p _ (hXs p).1))
  have hin : ∀ p, (X p).1.R j u := by
    intro p
    refine ((hXs p).2.1 j u).2 ⟨hju, hj p _ (hXs p).1, ?_⟩
    intro o ho
    simp only [List.mem_map] at ho
    obtain ⟨r, hr, rfl⟩ := ho
    exact hu r (by simp only [all, List.mem_flatMap]; exact ⟨p, List.mem_finRange p, hr⟩)
  have hE : ∀ p, ∃ es, Exec (X p).1 es (meetState sp j u hju) :=
    fun p => reach_meet (hXs p).2.1 (hin p)
  let ext : Fin N → List (LEv sp D N) := fun p => toL (Classical.choose (hE p))
  have hnr : ∀ p q k j d, LEv.recv q k j d ∉ ext p := fun p => toL_norecv _
  have hext : Extends H c (fun q => (H q).take (c q) ++ ext q) ext := fun _ => rfl
  have hrun : ∀ p, LRun (canon sp (init p)) ((H p).take (c p) ++ ext p) (meetState sp j u hju) :=
    fun p => lrun_append.2 ⟨(X p).1, (hXs p).1,
      exec_to_lrun hce (Classical.choose_spec (hE p)) (hXs p).2.1⟩
  exact ⟨_, ext, meetState sp j u hju, hext,
    ⟨fun p => ⟨_, hrun p⟩, recvMatched_extend hwf.2 hcut hext hnr⟩, rfl, hrun⟩


/-! ## Necessity: Availability ∧ Partition Consistency ⇒ Lifted Monotonicity -/

/-- (1)⇒(2) of Theorem `thm:complete-cap`, for an arbitrary system (any
basis, any local nondeterministic strategies). -/
theorem cap_necessary (Sys : System sp D) (hA : Availability Sys)
    (hP : PartitionConsistency Sys) : sp.LiftedMono := by
  apply liftedMono_of_ce
  intro rows hrows j hj
  classical
  by_cases hne : rows = []
  · subst hne; obtain ⟨u, hu⟩ := sp.total j; exact ⟨u, hu, by simp⟩
  have hlen : 0 < rows.length := by
    cases rows with
    | nil => exact absurd rfl hne
    | cons => simp
  -- one participant per row, plus one participant at `j`
  let N := rows.length + 1
  let init : Fin N → I := fun p => if h : p.val < rows.length then (rows[p.val]'h).1 else j
  let comp : Fin N → Nat := fun p => p.val
  have hcomp2 : ∃ p q : Fin N, comp p ≠ comp q :=
    ⟨⟨0, by omega⟩, ⟨rows.length, by omega⟩, by simp [comp]; omega⟩
  let H0 : History sp D N := fun _ => []
  have hwf0 : WF init H0 :=
    ⟨fun p => ⟨_, .nil _⟩, by intro p a q k j d b h; simp [H0] at h⟩
  have hprod0 : Produced Sys N init H0 := fun p a e b h => by simp [H0] at h
  have hpart0 : Partitioned H0 comp := ⟨hcomp2, by intro p a q k j d b h; simp [H0] at h⟩
  have hcut0 : IsCut H0 (fun _ => 0) :=
    ⟨fun _ => Nat.zero_le _, by intro p a q k j d b h; simp at h⟩
  -- Availability at the empty cut: each `p_r` emits `o_r` alone in its component
  have hL : ∀ p : Fin N, ∃ L : List (LEv sp D N),
      (∃ τ, LRun (canon sp (init p)) L τ) ∧ (∀ (q : Fin N) k j d, LEv.recv q k j d ∉ L) ∧
      Compliant (Allowed Sys N init p) L ∧ (∀ j, LEv.inp j ∉ L) ∧
      ∀ h : p.val < rows.length, ∃ γ, LEv.out γ (rows[p.val]'h).2 ∈ L := by
    intro p
    by_cases hp : p.val < rows.length
    · have hσ : LRun (canon sp (init p)) ((H0 p).take 0) (canon sp (init p)) := .nil _
      have hinit : init p = (rows[p.val]'hp).1 := by simp [init, hp]
      have ho : (canon sp (init p)).R (canon sp (init p)).cur (rows[p.val]'hp).2 := by
        show sp.S (init p) _ ∧ init p ≼ init p
        rw [hinit]; exact ⟨hrows _ (List.getElem_mem ..), PO.refl _⟩
      obtain ⟨H', ext, hext, hwf', hprod', hpart', _, hnoinp, γ, hγ⟩ :=
        hA N init H0 comp hwf0 hprod0 hpart0 (fun _ => 0) hcut0 p _ hσ _ ho
      have hH' : H' p = ext p := by rw [hext p]; simp [H0]
      refine ⟨ext p, ?_, ?_, ?_, hnoinp p, fun _ => ⟨γ, hγ⟩⟩
      · obtain ⟨τ, h⟩ := hwf'.1 p; exact ⟨τ, hH' ▸ h⟩
      · intro q k j d hm
        obtain ⟨a, b, hab⟩ := List.append_of_mem hm
        rw [← hH'] at hab
        exact (hwf'.2 p a q k j d b hab).1 (Fin.ext (hpart'.2 p a q k j d b hab))
      · have := hprod' p; rw [hH'] at this; exact this
    · exact ⟨[], ⟨_, .nil _⟩, by simp, fun a e b h => by simp at h, by simp,
        fun h => absurd h hp⟩
  let Lf : History sp D N := fun p => Classical.choose (hL p)
  have hLs : ∀ p, _ := fun p => Classical.choose_spec (hL p)
  have hnrecv : ∀ (p : Fin N) a (q : Fin N) k (j' : Option I) (d : D) b,
      Lf p ≠ a ++ LEv.recv q k j' d :: b := by
    intro p a q k j' d b h
    have hm : LEv.recv q k j' d ∈ Lf p := by rw [h]; simp
    exact (hLs p).2.1 q k j' d hm
  -- glue the local runs into one partitioned, produced history
  have hwfc : WF init Lf :=
    ⟨fun p => (hLs p).1, fun p a q k j' d b h => absurd h (hnrecv p a q k j' d b)⟩
  have hprodc : Produced Sys N init Lf := fun p => (hLs p).2.2.1
  have hpartc : Partitioned Lf comp :=
    ⟨hcomp2, fun p a q k j' d b h => absurd h (hnrecv p a q k j' d b)⟩
  have hcutc : IsCut Lf (fun p => (Lf p).length) :=
    ⟨fun _ => Nat.le_refl _, fun p a q k j' d b h => by
      rw [List.take_length] at h; exact absurd h (hnrecv p a q k j' d b)⟩
  have hjall : ∀ p σ, LRun (canon sp (init p)) ((Lf p).take (Lf p).length) σ → σ.cur ≼ j := by
    intro p σ h
    rw [List.take_length] at h
    rw [lrun_noinp h (hLs p).2.2.2.1]
    show init p ≼ j
    simp only [init]
    split
    · exact hj _ (List.getElem_mem ..)
    · exact PO.refl j
  -- Partition Consistency at the final cut
  obtain ⟨H'', ext'', τ, hext'', _, hτj, hτ⟩ :=
    hP N init Lf comp hwfc hprodc hpartc _ hcutc j hjall
  obtain ⟨u, hu⟩ := τ.hasCur
  rw [hτj] at hu
  refine ⟨u, τ.sub _ _ hu, fun r hr => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  let p : Fin N := ⟨i, by omega⟩
  have h1 := hτ p
  rw [hext'' p, List.take_length] at h1
  obtain ⟨σ', h2, h3⟩ := lrun_append.1 h1
  obtain ⟨γ, hγ⟩ := (hLs p).2.2.2.2 hi
  exact lrun_out_mem h2 hγ j u ((lrun_mono h3).2 j u hu)

/-! ## Theorem `thm:complete-cap` -/

/-- **Complete CAP.**  Some system has Availability and Partition Consistency
iff the specification satisfies Lifted Monotonicity; moreover the
commitment-free system then has both. -/
theorem complete_cap (sp : Spec I O) (D : Type) :
    (∃ Sys : System sp D, Availability Sys ∧ PartitionConsistency Sys) ↔ sp.LiftedMono :=
  ⟨fun ⟨Sys, hA, hP⟩ => cap_necessary Sys hA hP,
   fun h => ⟨cfSystem sp D, cf_availability h, cf_partitionConsistency h⟩⟩

/-- The "moreover" clause of Theorem `thm:complete-cap`. -/
theorem complete_cap_cf (sp : Spec I O) (D : Type) (h : sp.LiftedMono) :
    Availability (cfSystem sp D) ∧ PartitionConsistency (cfSystem sp D) :=
  ⟨cf_availability h, cf_partitionConsistency h⟩


/-! ## Discrepancy: deterministic strategies

Def. `def:system` speaks of "a rule that chooses the participant's next
events".  If that rule is a *function* of the local history, the (2)⇒(1)
direction of Theorem `thm:complete-cap` fails: a participant alone in its
component has a single possible future, so it cannot have two incomparable
outputs of its fiber both available.  We give a three-output counterexample
satisfying Lifted Monotonicity.  The formalization above (and Appendix
`app:cap-response`) therefore reads strategies as nondeterministic. -/

/-- A strategy is deterministic when it allows at most one next event after
any local history. -/
def System.Deterministic (Sys : System sp D) : Prop :=
  ∀ n init p pre e e', Sys.strat n init p pre e → Sys.strat n init p pre e' → e = e'

/-- An output emitted after `o` on a run expands `o`. -/
theorem lrun_emit_row {σ τ : State sp} {l : List (LEv sp D n)} (h : LRun σ l τ)
    {γ : List (Commitment sp)} {o : O} (hm : LEv.out γ o ∈ l) : ∃ k, σ.R k o := by
  induction h with
  | nil => cases hm
  | inp hs _ ih =>
    obtain ⟨k, hk⟩ := ih (by simpa using hm); exact ⟨k, step_sub hs k o hk⟩
  | @out σ σc τ' ρ γ' o' es ha hs _ _ ih =>
    have hsub := (applySeq_spec γ' σ σc ha).2
    rcases List.mem_cons.1 hm with he | hm'
    · cases he; exact ⟨_, hsub _ _ (step_output_inv hs).1⟩
    · obtain ⟨k, hk⟩ := ih hm'; exact ⟨k, hsub _ _ (step_sub hs k o hk)⟩
  | send _ ih => exact ih (by simpa using hm)
  | recv _ ih => exact ih (by simpa using hm)

theorem lrun_later_le {σ τ : State sp} {l1 l2 : List (LEv sp D n)}
    {γ γ' : List (Commitment sp)} {o o' : O}
    (h : LRun σ (l1 ++ LEv.out γ o :: l2) τ) (hm : LEv.out γ' o' ∈ l2) : o ≼ o' := by
  obtain ⟨σ1, _, h2⟩ := lrun_append.1 h
  cases h2 with
  | out ha hs _ hr =>
    obtain ⟨k, hk⟩ := lrun_emit_row hr hm
    rw [(step_output_inv hs).2.2] at hk; exact hk.2

/-- A participant run cannot emit two incomparable outputs. -/
theorem lrun_no_incomparable {σ τ : State sp} {l : List (LEv sp D n)} (h : LRun σ l τ)
    {γ γ' : List (Commitment sp)} {o o' : O} (hm : LEv.out γ o ∈ l) (hm' : LEv.out γ' o' ∈ l)
    (h1 : ¬ o ≼ o') (h2 : ¬ o' ≼ o) : False := by
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hm
  rcases List.mem_append.1 hm' with hin | hin
  · obtain ⟨m1, m2, rfl⟩ := List.append_of_mem hin
    have : LRun σ (m1 ++ LEv.out γ' o' :: (m2 ++ LEv.out γ o :: l2)) τ := by simpa using h
    exact h2 (lrun_later_le (γ' := γ) this (by simp))
  · rcases List.mem_cons.1 hin with he | hin'
    · cases he; exact h1 (PO.refl _)
    · exact h1 (lrun_later_le h hin')

theorem det_prefix (Sys : System sp D) (hdet : Sys.Deterministic) {N : Nat} {init : Fin N → I}
    {p : Fin N} : ∀ (L1 L2 pre : List (LEv sp D N)),
    (∀ a e b, L1 = a ++ e :: b → Sys.strat N init p (pre ++ a) e) →
    (∀ a e b, L2 = a ++ e :: b → Sys.strat N init p (pre ++ a) e) →
    (∃ t, L2 = L1 ++ t) ∨ (∃ t, L1 = L2 ++ t)
  | [], L2, _, _, _ => Or.inl ⟨L2, rfl⟩
  | _ :: _, [], _, _, _ => Or.inr ⟨_, rfl⟩
  | e1 :: L1, e2 :: L2, pre, h1, h2 => by
    have he : e1 = e2 :=
      hdet N init p _ e1 e2 (by simpa using h1 [] e1 L1 rfl) (by simpa using h2 [] e2 L2 rfl)
    subst he
    have ih := det_prefix Sys hdet L1 L2 (pre ++ [e1])
      (fun a e b hab => by simpa using h1 (e1 :: a) e b (by simp [hab]))
      (fun a e b hab => by simpa using h2 (e1 :: a) e b (by simp [hab]))
    rcases ih with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact Or.inl ⟨t, by simp [ht]⟩
    · exact Or.inr ⟨t, by simp [ht]⟩

theorem compliant_strat {Sys : System sp D} {N : Nat} {init : Fin N → I} {p : Fin N}
    {L : List (LEv sp D N)} (hc : Compliant (Allowed Sys N init p) L)
    (hn : ∀ j, LEv.inp j ∉ L) :
    ∀ a e b, L = a ++ e :: b → Sys.strat N init p ([] ++ a) e := by
  intro a e b h
  have hA := hc a e b h
  cases e with
  | inp j => exact absurd (by rw [h]; simp) (hn j)
  | out γ o => exact by simpa using hA.2
  | send => simpa [Allowed] using hA
  | recv => simpa [Allowed] using hA

/-- Three outputs `a`, `b` incomparable, both below `top`. -/
inductive Tri where
  | a | b | top
  deriving DecidableEq

def Tri.le : Tri → Tri → Prop
  | x, y => x = y ∨ y = .top

instance : PO Tri where
  le := Tri.le
  refl := fun x => Or.inl rfl
  trans := by
    intro x y z h1 h2
    unfold Tri.le at *
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp
  antisymm := by
    intro x y h1 h2
    unfold Tri.le at *
    cases x <;> cases y <;> simp_all

instance : PO Unit where
  le := fun _ _ => True
  refl := fun _ => trivial
  trans := fun _ _ => trivial
  antisymm := fun {a b} _ _ => by cases a; cases b; rfl

/-- One input, fiber `{a, b, top}`. -/
def triSpec : Spec Unit Tri where
  S := fun _ _ => True
  total := fun _ => ⟨.a, trivial⟩

theorem triSpec_liftedMono : triSpec.LiftedMono := by
  intro i j _ X _ _
  exact ⟨.top, trivial, fun x _ => Or.inr rfl⟩

/-- **Counterexample** to (2)⇒(1) of Theorem `thm:complete-cap` under a
deterministic reading of strategies: `triSpec` satisfies Lifted Monotonicity,
yet no system with deterministic strategies has Availability. -/
theorem deterministic_not_available (D : Type) (Sys : System triSpec D)
    (hdet : Sys.Deterministic) : ¬ Availability Sys := by
  intro hA
  let init : Fin 2 → Unit := fun _ => ()
  let comp : Fin 2 → Nat := fun p => p.val
  let H0 : History triSpec D 2 := fun _ => []
  have hwf0 : WF init H0 :=
    ⟨fun p => ⟨_, .nil _⟩, by intro p a q k j d b h; simp [H0] at h⟩
  have hprod0 : Produced Sys 2 init H0 := fun p a e b h => by simp [H0] at h
  have hpart0 : Partitioned H0 comp :=
    ⟨⟨0, 1, by simp [comp]⟩, by intro p a q k j d b h; simp [H0] at h⟩
  have hcut0 : IsCut H0 (fun _ => 0) :=
    ⟨fun _ => Nat.zero_le _, by intro p a q k j d b h; simp at h⟩
  have hσ : LRun (canon triSpec (init 0)) ((H0 0).take 0) (canon triSpec (init 0)) := .nil _
  have hav : ∀ o : Tri, ∃ L : List (LEv triSpec D 2),
      (∃ τ, LRun (canon triSpec (init 0)) L τ) ∧ Compliant (Allowed Sys 2 init 0) L ∧
      (∀ j, LEv.inp j ∉ L) ∧ ∃ γ, LEv.out γ o ∈ L := by
    intro o
    obtain ⟨H', ext, hext, hwf', hprod', _, _, hnoinp, γ, hγ⟩ :=
      hA 2 init H0 comp hwf0 hprod0 hpart0 (fun _ => 0) hcut0 0 _ hσ o ⟨trivial, trivial⟩
    have hH' : H' 0 = ext 0 := by rw [hext 0]; simp [H0]
    refine ⟨ext 0, ?_, ?_, hnoinp 0, γ, hγ⟩
    · obtain ⟨τ, h⟩ := hwf'.1 0; exact ⟨τ, hH' ▸ h⟩
    · have := hprod' 0; rw [hH'] at this; exact this
  obtain ⟨La, ⟨τa, hra⟩, hca, hna, γa, hγa⟩ := hav .a
  obtain ⟨Lb, ⟨τb, hrb⟩, hcb, hnb, γb, hγb⟩ := hav .b
  have hab : ¬ (Tri.a ≼ Tri.b) := by
    show ¬ Tri.le .a .b; simp [Tri.le]
  have hba : ¬ (Tri.b ≼ Tri.a) := by
    show ¬ Tri.le .b .a; simp [Tri.le]
  rcases det_prefix Sys hdet La Lb [] (compliant_strat hca hna) (compliant_strat hcb hnb) with
    ⟨t, ht⟩ | ⟨t, ht⟩
  · subst ht
    exact lrun_no_incomparable hrb (List.mem_append_left _ hγa) hγb hab hba
  · subst ht
    exact lrun_no_incomparable hra hγa (List.mem_append_left _ hγb) hab hba


/-! ## Appendix `app:cap-response`: response availability

Precise reading chosen: Def. `def:response-availability` does not say that
its continuations are *produced by the system*; without that the (1)⇒(2)
proof of Theorem `thm:complete-cap-response` cannot place the emissions it
obtains into "partitioned histories of the system".  We require it, as the
interface-form Availability does. -/

/-- Def. `def:response-availability`, for a (possibly per-participant)
obligation `Q n p`. -/
def ResponseAvailability (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ c, IsCut H c →
    ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) ((H p).take (c p)) σ →
      -- Answering
      (∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)),
        Extends H c H' ext ∧ WF init H' ∧ Produced Sys n init H' ∧ Partitioned H' comp ∧
        (∀ q, comp q ≠ comp p → ext q = []) ∧ (∀ j, LEv.inp j ∉ ext p) ∧
        ∃ γ o, Q n p σ.cur o ∧ LEv.out γ o ∈ ext p) ∧
      -- Input acceptance
      (∀ j, σ.cur ≼ j → ∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)),
        Extends H c H' ext ∧ WF init H' ∧ Produced Sys n init H' ∧ Partitioned H' comp ∧
        (∀ q, comp q ≠ comp p → ext q = []) ∧ LEv.inp j ∈ ext p)

/-- Response Partition Consistency of a cut at `j`
(Def. `def:response-partition-consistency`). -/
def RPCAt (H : History sp D n) (c : Fin n → Nat) (j : I) : Prop :=
  ∃ u, sp.S j u ∧ ∀ p γ o, LEv.out γ o ∈ (H p).take (c p) → o ≼ u

def ResponsePC (Sys : System sp D) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ c, IsCut H c →
    ∀ j : I, (∀ p σ, LRun (canon sp (init p)) ((H p).take (c p)) σ → σ.cur ≼ j) →
    RPCAt H c j

/-- **Lemma `lem:forced-answer`.**  If `q` is alone in its component, its
current input is `i`, `j` expands every current input, and no output of
`Q_q(i)` has an expansion in `S(j)`, then the history continues (within `q`'s
component, adding no input) to a cut at which `j` still expands every current
input and the emitted outputs have no common expansion in `S(j)`. -/
theorem forced_answer (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O)
    (hRA : ResponseAvailability Sys Q) {n : Nat} {init : Fin n → I} {H : History sp D n}
    {comp : Fin n → Nat} (hwf : WF init H) (hprod : Produced Sys n init H)
    (hpart : Partitioned H comp) {c : Fin n → Nat} (hc : IsCut H c) {q : Fin n}
    (halone : ∀ p, comp p = comp q → p = q) {σq : State sp}
    (hσq : LRun (canon sp (init q)) ((H q).take (c q)) σq) {j : I}
    (hj : ∀ p σ, LRun (canon sp (init p)) ((H p).take (c p)) σ → σ.cur ≼ j)
    (hno : ∀ o, Q n q σq.cur o → ¬ ∃ u, sp.S j u ∧ o ≼ u) :
    ∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)),
      Extends H c H' ext ∧ WF init H' ∧ Produced Sys n init H' ∧ Partitioned H' comp ∧
      IsCut H' (fun p => (H' p).length) ∧
      (∀ p σ, LRun (canon sp (init p)) ((H' p).take (H' p).length) σ → σ.cur ≼ j) ∧
      ¬ RPCAt H' (fun p => (H' p).length) j := by
  obtain ⟨⟨H', ext, hext, hwf', hprod', hpart', hloc, hnoinp, γ, o, hQ, hm⟩, _⟩ :=
    hRA n init H comp hwf hprod hpart c hc q σq hσq
  refine ⟨H', ext, hext, hwf', hprod', hpart', ⟨fun _ => Nat.le_refl _, ?_⟩, ?_, ?_⟩
  · intro p a q' k j' d b h
    rw [List.take_length] at h
    obtain ⟨_, hs⟩ := hwf'.2 p a q' k j' d b h
    exact (List.getElem?_eq_some_iff.1 hs).1
  · intro p σ h
    rw [List.take_length, hext p] at h
    obtain ⟨σ1, h1, h2⟩ := lrun_append.1 h
    by_cases hpq : p = q
    · subst hpq
      rw [lrun_noinp h2 hnoinp]; exact hj p σ1 h1
    · have : ext p = [] := hloc p (fun h => hpq (halone p h))
      rw [this] at h2; cases h2; exact hj p _ h1
  · rintro ⟨u, hu, hall⟩
    apply hno o hQ ⟨u, hu, hall q γ o ?_⟩
    rw [List.take_length, hext q]; exact List.mem_append_right _ hm

/-- Abstract form of Corollary `cor:gilbert-lynch`: a system with Response
Availability cannot have Response Partition Consistency as soon as one of its
partitioned histories reaches a configuration in which an isolated
participant's only permitted answers are invalidated by input it cannot see.
(The register-specific construction of that configuration is not formalized;
see the report.) -/
theorem forced_answer_impossibility (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O)
    (hRA : ResponseAvailability Sys Q) (hRPC : ResponsePC Sys)
    {n : Nat} {init : Fin n → I} {H : History sp D n} {comp : Fin n → Nat}
    (hwf : WF init H) (hprod : Produced Sys n init H) (hpart : Partitioned H comp)
    {c : Fin n → Nat} (hc : IsCut H c) {q : Fin n} (halone : ∀ p, comp p = comp q → p = q)
    {σq : State sp} (hσq : LRun (canon sp (init q)) ((H q).take (c q)) σq) {j : I}
    (hj : ∀ p σ, LRun (canon sp (init p)) ((H p).take (c p)) σ → σ.cur ≼ j)
    (hno : ∀ o, Q n q σq.cur o → ¬ ∃ u, sp.S j u ∧ o ≼ u) : False := by
  obtain ⟨H', _, _, hwf', hprod', hpart', hcut', hj', hbad⟩ :=
    forced_answer Sys Q hRA hwf hprod hpart hc halone hσq hj hno
  exact hbad (hRPC n init H' comp hwf' hprod' hpart' _ hcut' j hj')


/-! ## Response form of Complete CAP (Theorem `thm:complete-cap-response`)

### Replicated systems, obligations, response interfaces -/

/-- Participant-independent local events (receives name the sender by number). -/
inductive LEvN (sp : Spec I O) (D : Type) where
  | inp (j : I)
  | out (γ : List (Commitment sp)) (o : O)
  | send (j : Option I) (d : D)
  | recv (q : Nat) (k : Nat) (j : Option I) (d : D)

def LEv.erase : LEv sp D n → LEvN sp D
  | .inp j => .inp j
  | .out γ o => .out γ o
  | .send j d => .send j d
  | .recv q k j d => .recv q.val k j d

/-- A replicated system gives every participant the same strategy, depending
only on its own initial input and local history — not on its identity, the
number of participants, or other participants' initial inputs. -/
def System.Replicated (Sys : System sp D) : Prop :=
  ∃ F : I → List (LEvN sp D) → LEvN sp D → Prop,
    ∀ n init p pre e, Sys.strat n init p pre e ↔ F (init p) (pre.map LEv.erase) e.erase

/-- Def. `def:response-obligation` (uniform case). -/
structure Obligation (sp : Spec I O) where
  Q : Table I O
  sub : ∀ i o, Q i o → sp.S i o
  total : ∀ i, ∃ o, Q i o
  up : ∀ i o u, Q i o → sp.S i u → o ≼ u → Q i u

/-- Def. `def:response-interface`. -/
def ResponseInterface (Q : Obligation sp) (T : Table I O) : Prop :=
  (∀ i o, T i o → Q.Q i o) ∧ (∀ i, ∃ o, T i o) ∧
  ∀ i o j, T i o → i ≼ j → ∃ u, T j u ∧ o ≼ u

/-- `S` is consistent on `T`. -/
def ConsistentOn (sp : Spec I O) (T : Table I O) : Prop :=
  ∀ rows : List (I × O), (∀ r ∈ rows, T r.1 r.2) →
    ∀ j, (∀ r ∈ rows, r.1 ≼ j) → ∃ u, sp.S j u ∧ ∀ r ∈ rows, r.2 ≼ u

theorem consistentOn_outs {T : Table I O} (hc : ConsistentOn sp T) {j : I} (L : List O)
    (hL : ∀ o ∈ L, ∃ i, T i o ∧ i ≼ j) : ∃ u, sp.S j u ∧ ∀ o ∈ L, o ≼ u := by
  let rows : List (I × O) := L.attach.map (fun o => (Classical.choose (hL o.1 o.2), o.1))
  obtain ⟨u, hu, hall⟩ := hc rows
    (by intro r hr; simp only [rows, List.mem_map] at hr
        obtain ⟨o, _, rfl⟩ := hr; exact (Classical.choose_spec (hL o.1 o.2)).1) j
    (by intro r hr; simp only [rows, List.mem_map] at hr
        obtain ⟨o, _, rfl⟩ := hr; exact (Classical.choose_spec (hL o.1 o.2)).2)
  exact ⟨u, hu, fun o ho => hall _ (by
    simp only [rows, List.mem_map]; exact ⟨⟨o, ho⟩, List.mem_attach _ _, rfl⟩)⟩

/-! ### The canonical commitment `κ_u` (seal and choice applied together) -/

/-- Rows the canonical event for `u` removes by commitment. -/
def Rm (σ : State sp) (u : O) (k : I) (x : O) : Prop := Sealed σ u k x ∨ Rejected σ u k x

theorem not_rm_of_le {σ : State sp} {u : O} {k : I} {x : O} (hx : σ.R k x) (h : u ≼ x) :
    ¬ Rm σ u k x := by
  rintro (⟨_, hs⟩ | ⟨_, hn, _⟩)
  · exact hs ⟨x, hx, h⟩
  · exact hn h

/-- A kept row that does not expand `u` is retired. -/
theorem retired_of_not_rm {σ : State sp} {u : O} {k : I} {x : O} (hx : σ.R k x)
    (hrm : ¬ Rm σ u k x) (hn : ¬ u ≼ x) : ∃ v, σ.R k v ∧ u ≼ v ∧ x ≼ v := by
  apply Classical.byContradiction
  intro hv
  apply hrm
  by_cases hs : ∃ v, σ.R k v ∧ u ≼ v
  · exact Or.inr ⟨hx, hn, fun ⟨_, h⟩ => h hs, fun ⟨_, _, h⟩ => hv h⟩
  · exact Or.inl ⟨hx, hs⟩

def kcState (σ : State sp) (u : O) (hu : σ.R σ.cur u) : State sp where
  cur := σ.cur
  R := fun k x => σ.R k x ∧ ¬ Rm σ u k x
  sub := fun k x h => σ.sub k x h.1
  hasCur := ⟨u, hu, not_rm_of_le hu (PO.refl u)⟩
  above := fun k x h => σ.above k x h.1

open Classical in
/-- The canonical commitment for `u`: defined when `u` is in the current fiber
and some row must be removed by commitment; it removes `Sealed_u ∪ Rejected_u`.
That this is a commitment (Eq. `commitment-excludes`) is checked here. -/
noncomputable def kc (u : O) : Commitment sp where
  f := fun σ => if h : σ.R σ.cur u ∧ ∃ k x, Rm σ u k x then some (kcState σ u h.1) else none
  cur_eq := by
    intro σ τ h; split at h
    · cases h; rfl
    · cases h
  sub := by
    intro σ τ h; split at h
    · cases h; exact fun k x h => h.1
    · cases h
  strict := by
    intro σ τ h; split at h
    · rename_i hh; cases h
      obtain ⟨k, x, hr⟩ := hh.2
      have hx : σ.R k x := by rcases hr with h | h; exact h.1; exact h.1
      exact ⟨k, x, hx, fun h => h.2 hr⟩
    · cases h
  excl := by
    intro σ τ h; split at h
    · cases h
      intro k x w hx hnx hw hxw
      have hrx : Rm σ u k x := Classical.byContradiction fun h => hnx ⟨hx, h⟩
      obtain ⟨hw1, hw2⟩ := hw
      -- some row at `k` expands both `u` and `w`
      have hv : ∃ v, σ.R k v ∧ u ≼ v ∧ w ≼ v := by
        by_cases huw : u ≼ w
        · exact ⟨w, hw1, huw, PO.refl w⟩
        · exact retired_of_not_rm hw1 hw2 huw
      obtain ⟨v, hv1, hv2, hv3⟩ := hv
      rcases hrx with ⟨_, hs⟩ | ⟨_, hn, _, hret⟩
      · exact hs ⟨v, hv1, hv2⟩
      · exact hret ⟨hx, hn, v, hv1, hv2, PO.trans hxw hv3⟩
    · cases h

theorem kc_apply_some {σ : State sp} {u : O} {σc : State sp}
    (h : applySeq σ [kc u] = some σc) :
    ∃ hu : σ.R σ.cur u, σc = kcState σ u hu := by
  simp only [applySeq] at h
  split at h
  · rename_i τ1 h1
    cases h
    simp only [kc] at h1
    split at h1
    · rename_i hh; cases h1; exact ⟨hh.1, rfl⟩
    · cases h1
  · cases h

/-- The canonical event for `u` is legal at any state with `u` in the current
fiber (Lemma `lem:canonical-commitment-normal-form`(2)). -/
theorem kc_legal {σ : State sp} {u : O} (hu : σ.R σ.cur u) :
    ∃ γ σc, (γ = [] ∨ γ = [kc u]) ∧ applySeq σ γ = some σc ∧ σc.R σc.cur u ∧
      Exposable σc u := by
  by_cases hrm : ∃ k x, Rm σ u k x
  · refine ⟨[kc u], kcState σ u hu, Or.inr rfl, ?_, ⟨hu, not_rm_of_le hu (PO.refl u)⟩, ?_⟩
    · simp only [applySeq, kc]; rw [dite_eq_left_of_eq_true (eq_true ⟨hu, hrm⟩)]
    · intro k x hx hn
      obtain ⟨v, hv1, hv2, hv3⟩ := retired_of_not_rm hx.1 hx.2 hn
      exact ⟨v, ⟨hv1, not_rm_of_le hv1 hv2⟩, hv2, hv3⟩
  · refine ⟨[], σ, Or.inl rfl, rfl, hu, ?_⟩
    intro k x hx hn
    exact retired_of_not_rm hx (fun h => hrm ⟨k, x, h⟩) hn

/-- Effect of a canonical event: it ends at `R[out ⪰ u]`. -/
theorem kc_effect {σ σc τ : State sp} {u : O} {γ : List (Commitment sp)}
    (hγ : γ = [] ∨ γ = [kc u]) (ha : applySeq σ γ = some σc) (hs : Step σc (.output u) τ) :
    Step σ (.output u) τ := by
  rcases hγ with rfl | rfl
  · simp [applySeq] at ha; subst ha; exact hs
  · obtain ⟨hu, rfl⟩ := kc_apply_some ha
    obtain ⟨_, hc, hR⟩ := step_output_inv hs
    refine Step.output σ τ u hu hc ?_
    rw [hR]; funext k x; apply propext
    simp only [outputTable, kcState]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, not_rm_of_le h.1 h.2⟩, h.2⟩⟩

/-! ### The replicated system of (2)⇒(1) -/

def curOf (i0 : I) : List (LEvN sp D) → I
  | [] => i0
  | .inp j :: l => curOf j l
  | .out _ _ :: l => curOf i0 l
  | .send _ _ :: l => curOf i0 l
  | .recv _ _ _ _ :: l => curOf i0 l

def emittedOf : List (LEvN sp D) → List O
  | [] => []
  | .out _ o :: l => o :: emittedOf l
  | .inp _ :: l => emittedOf l
  | .send _ _ :: l => emittedOf l
  | .recv _ _ _ _ :: l => emittedOf l

theorem curOf_append (a b : List (LEvN sp D)) (i0 : I) :
    curOf i0 (a ++ b) = curOf (curOf i0 a) b := by
  induction a generalizing i0 with
  | nil => rfl
  | cons e a ih => cases e <;> simp [curOf, ih]

theorem emittedOf_append (a b : List (LEvN sp D)) :
    emittedOf (a ++ b) = emittedOf a ++ emittedOf b := by
  induction a with
  | nil => rfl
  | cons e a ih => cases e <;> simp [emittedOf, ih]

theorem mem_emittedOf {L : List (LEv sp D n)} {γ : List (Commitment sp)} {o : O}
    (h : LEv.out γ o ∈ L) : o ∈ emittedOf (L.map LEv.erase) := by
  induction L with
  | nil => cases h
  | cons e L ih =>
    rcases List.mem_cons.1 h with rfl | h'
    · simp [LEv.erase, emittedOf]
    · cases e <;> simp [LEv.erase, emittedOf, ih h']

/-- The strategy: ignore messages, never send; emit, by the canonical event,
some `u ∈ T(i)` at the current input `i` that expands every earlier output. -/
noncomputable def respF (T : Table I O) (i0 : I) (pre : List (LEvN sp D)) : LEvN sp D → Prop
  | .out γ u => (γ = [] ∨ γ = [kc u]) ∧ T (curOf i0 pre) u ∧ ∀ o ∈ emittedOf pre, o ≼ u
  | _ => False

noncomputable def respSystem (T : Table I O) : System sp D where
  basis := fun c => ∃ u, c = kc u
  strat := fun _ init p pre e => respF T (init p) (pre.map LEv.erase) e.erase

/-- Invariant of participant runs of `respSystem T`. -/
def RInv (T : Table I O) (i0 : I) (pre : List (LEvN sp D)) (σ : State sp) : Prop :=
  σ.cur = curOf i0 pre ∧ Residual σ (emittedOf pre) ∧
  (∀ o ∈ emittedOf pre, ∃ i, T i o ∧ i ≼ σ.cur) ∧
  (emittedOf pre = [] ∨ ∃ i om, T i om ∧ i ≼ σ.cur ∧ ∀ o ∈ emittedOf pre, o ≼ om)

theorem rinv_run (T : Table I O) {N : Nat} {init : Fin N → I} {p : Fin N} :
    ∀ {σ τ : State sp} {L : List (LEv sp D N)}, LRun σ L τ →
    ∀ pre : List (LEv sp D N),
    (∀ a e b, L = a ++ e :: b → Allowed (respSystem T) N init p (pre ++ a) e) →
    RInv T (init p) (pre.map LEv.erase) σ → RInv T (init p) ((pre ++ L).map LEv.erase) τ := by
  intro σ τ L h
  induction h with
  | nil => intro pre _ hi; simpa using hi
  | @inp σ τ' ρ j es hs _ ih =>
    intro pre hc hi
    have := ih (pre ++ [.inp j]) (fun a e b hab => by
      have := hc (.inp j :: a) e b (by simp [hab]); simpa using this)
    simp only [List.append_assoc, List.singleton_append] at this
    apply this
    obtain ⟨⟨w, hw⟩, hcur, _⟩ := step_input_inv hs
    have hle : σ.cur ≼ τ'.cur := by rw [hcur]; exact σ.above _ _ hw
    obtain ⟨h1, h2, h3, h4⟩ := hi
    have hE : emittedOf ((pre ++ [LEv.inp j]).map LEv.erase) = emittedOf (pre.map LEv.erase) := by
      simp [emittedOf_append, LEv.erase, emittedOf]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [curOf_append, LEv.erase, curOf, hcur]
    · rw [hE]; have := residual_step h2 hs; simpa [outs] using this
    · rw [hE]; intro o ho; obtain ⟨i, hi1, hi2⟩ := h3 o ho; exact ⟨i, hi1, PO.trans hi2 hle⟩
    · rw [hE]; rcases h4 with h4 | ⟨i, om, hom, hi, hall⟩
      · exact Or.inl h4
      · exact Or.inr ⟨i, om, hom, PO.trans hi hle, hall⟩
  | @out σ σc τ' ρ γ u es ha hs _ _ ih =>
    intro pre hc hi
    have hA := hc [] (.out γ u) es (by simp)
    simp only [List.append_nil] at hA
    obtain ⟨_, hγ, hT, hge⟩ := hA
    have hstep := kc_effect hγ ha hs
    have := ih (pre ++ [.out γ u]) (fun a e b hab => by
      have := hc (.out γ u :: a) e b (by simp [hab]); simpa using this)
    simp only [List.append_assoc, List.singleton_append] at this
    apply this
    obtain ⟨hu, hcur, _⟩ := step_output_inv hstep
    obtain ⟨h1, h2, h3, h4⟩ := hi
    have hE : emittedOf ((pre ++ [LEv.out γ u]).map LEv.erase) =
        emittedOf (pre.map LEv.erase) ++ [u] := by
      simp [emittedOf_append, LEv.erase, emittedOf]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [curOf_append, LEv.erase, curOf, hcur, h1]
    · rw [hE]; have := residual_step h2 hstep; simpa [outs] using this
    · rw [hE]; intro o ho
      rcases List.mem_append.1 ho with ho | ho
      · obtain ⟨i, hi1, hi2⟩ := h3 o ho; exact ⟨i, hi1, hcur ▸ hi2⟩
      · simp at ho; subst ho; exact ⟨σ.cur, h1 ▸ hT, hcur ▸ PO.refl _⟩
    · rw [hE]; refine Or.inr ⟨σ.cur, u, h1 ▸ hT, hcur ▸ PO.refl _, ?_⟩
      intro o ho
      rcases List.mem_append.1 ho with ho | ho
      · exact hge o ho
      · simp at ho; subst ho; exact PO.refl _
  | @send σ ρ j d es _ _ =>
    intro pre hc _
    have := hc [] (.send j d) es rfl
    simp [Allowed, respSystem, respF, LEv.erase] at this
  | @recv σ ρ q k j d es _ _ =>
    intro pre hc _
    have := hc [] (.recv q k j d) es rfl
    simp [Allowed, respSystem, respF, LEv.erase] at this

theorem rinv_of_produced (T : Table I O) {N : Nat} {init : Fin N → I} {p : Fin N}
    {L : List (LEv sp D N)} {σ : State sp} (hc : Compliant (Allowed (respSystem T) N init p) L)
    (h : LRun (canon sp (init p)) L σ) : RInv T (init p) (L.map LEv.erase) σ := by
  have := rinv_run T h [] (fun a e b hab => by simpa using hc a e b hab)
    ⟨rfl, residual_canon sp _, by simp [emittedOf], Or.inl rfl⟩
  simpa using this

/-- Extend a history at a cut by one event at one participant. -/
theorem extend_single (Sys : System sp D) {init : Fin n → I} {H : History sp D n}
    {comp : Fin n → Nat} {c : Fin n → Nat} (hwf : WF init H) (hprod : Produced Sys n init H)
    (hpart : Partitioned H comp) (hcut : IsCut H c) {p : Fin n} {σ τ : State sp}
    (hσ : LRun (canon sp (init p)) ((H p).take (c p)) σ) {e : LEv sp D n}
    (hnr : ∀ q k j d, e ≠ .recv q k j d) (he : LRun σ [e] τ)
    (hA : Allowed Sys n init p ((H p).take (c p)) e) :
    ∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)),
      Extends H c H' ext ∧ WF init H' ∧ Produced Sys n init H' ∧ Partitioned H' comp ∧
      ext p = [e] ∧ (∀ q, q ≠ p → ext q = []) := by
  classical
  let ext : Fin n → List (LEv sp D n) := fun q => if q = p then [e] else []
  have hnr' : ∀ p' q k j d, LEv.recv q k j d ∉ ext p' := by
    intro p' q k j d; simp only [ext]; split
    · simp only [List.mem_singleton]; exact fun h => hnr q k j d h.symm
    · simp
  have hext : Extends H c (fun q => (H q).take (c q) ++ ext q) ext := fun _ => rfl
  have hp : ext p = [e] := by simp [ext]
  have hq : ∀ q, q ≠ p → ext q = [] := fun q h => by simp [ext, h]
  refine ⟨_, ext, hext, ⟨?_, recvMatched_extend hwf.2 hcut hext hnr'⟩, ?_,
    partitioned_extend hpart hext hnr', hp, hq⟩
  · intro q
    by_cases hqp : q = p
    · subst hqp; exact ⟨τ, lrun_append.2 ⟨σ, hσ, by rw [hp]; exact he⟩⟩
    · obtain ⟨τq, hq'⟩ := hwf.1 q
      obtain ⟨σq, hσq⟩ := lrun_take hq' (c q)
      refine ⟨σq, ?_⟩
      show LRun _ ((H q).take (c q) ++ ext q) σq
      rw [hq q hqp, List.append_nil]; exact hσq
  · intro q
    apply compliant_append (compliant_take (hprod q) (c q))
    intro a e' b hab
    by_cases hqp : q = p
    · subst hqp
      rw [hp] at hab
      cases a with
      | nil => simp at hab; obtain ⟨rfl, _⟩ := hab; simpa using hA
      | cons _ _ => simp at hab
    · rw [hq q hqp] at hab; simp at hab

/-- (2)⇒(1) of Theorem `thm:complete-cap-response`. -/
theorem response_sufficient (Q : Obligation sp) (T : Table I O)
    (hT : ResponseInterface Q T) (hcons : ConsistentOn sp T) :
    (respSystem (sp := sp) (D := D) T).Replicated ∧
    ResponseAvailability (respSystem (sp := sp) (D := D) T) (fun _ _ => Q.Q) ∧
    ResponsePC (respSystem (sp := sp) (D := D) T) := by
  obtain ⟨hTQ, hTtot, hTcont⟩ := hT
  refine ⟨⟨respF T, fun _ _ _ _ _ => Iff.rfl⟩, ?_, ?_⟩
  · intro N init H comp hwf hprod hpart c hcut p σ hσ
    obtain ⟨h1, h2, _, h4⟩ := rinv_of_produced T (compliant_take (hprod p) (c p)) hσ
    -- rows available at any `k ⪰ σ.cur` in `T`, expanding every emitted output
    have havail : ∀ k, σ.cur ≼ k → ∃ u, T k u ∧ ∀ o ∈ emittedOf (((H p).take (c p)).map LEv.erase), o ≼ u := by
      intro k hk
      rcases h4 with h4 | ⟨i, om, hom, hi, hall⟩
      · obtain ⟨u, hu⟩ := hTtot k; exact ⟨u, hu, by rw [h4]; simp⟩
      · obtain ⟨u, hu, hle⟩ := hTcont i om k hom (PO.trans hi hk)
        exact ⟨u, hu, fun o ho => PO.trans (hall o ho) hle⟩
    constructor
    · -- Answering
      obtain ⟨u, hu, hge⟩ := havail σ.cur (PO.refl _)
      have hRu : σ.R σ.cur u :=
        (h2 _ _).2 ⟨Q.sub _ _ (hTQ _ _ hu), PO.refl _, hge⟩
      obtain ⟨γ, σc, hγ, ha, hcu, hexp⟩ := kc_legal hRu
      have hcc : σc.cur = σ.cur := (applySeq_spec γ σ σc ha).1
      let τ : State sp :=
        { cur := σc.cur, R := outputTable σc u, sub := fun k x h => σc.sub k x h.1,
          hasCur := ⟨u, hcu, PO.refl u⟩, above := fun k x h => σc.above k x h.1 }
      have hstep : Step σc (.output u) τ := Step.output σc τ u hcu rfl rfl
      obtain ⟨H', ext, hext, hwf', hprod', hpart', hp, hq⟩ :=
        extend_single (respSystem T) hwf hprod hpart hcut hσ (e := .out γ u)
          (by intro q k j d h; cases h) (.out ha hstep hexp (.nil τ))
          ⟨by intro c' hc'; rcases hγ with rfl | rfl
              · cases hc'
              · simp at hc'; exact ⟨u, hc'⟩,
           hγ, by rw [← h1]; exact hu, hge⟩
      refine ⟨H', ext, hext, hwf', hprod', hpart', fun q hq' => hq q (fun h => hq' (h ▸ rfl)),
        by rw [hp]; simp, γ, u, hTQ _ _ hu, by rw [hp]; simp⟩
    · -- Input acceptance
      intro j hj
      obtain ⟨w, hw, hge⟩ := havail j hj
      have hRw : σ.R j w := (h2 _ _).2 ⟨Q.sub _ _ (hTQ _ _ hw), hj, hge⟩
      let τ : State sp :=
        { cur := j, R := inputTable σ j, sub := fun k x h => σ.sub k x h.1,
          hasCur := ⟨w, hRw, PO.refl j⟩, above := fun k x h => h.2 }
      have hstep : Step σ (.input j) τ := Step.input σ τ j ⟨w, hRw⟩ rfl rfl
      obtain ⟨H', ext, hext, hwf', hprod', hpart', hp, hq⟩ :=
        extend_single (respSystem T) hwf hprod hpart hcut hσ (e := .inp j)
          (by intro q k j d h; cases h) (.inp hstep (.nil τ)) trivial
      exact ⟨H', ext, hext, hwf', hprod', hpart', fun q hq' => hq q (fun h => hq' (h ▸ rfl)),
        by rw [hp]; simp⟩
  · intro N init H comp hwf hprod _ c _ j hj
    let L : List O := (List.finRange N).flatMap
      (fun p => emittedOf (((H p).take (c p)).map LEv.erase))
    obtain ⟨u, hu, hall⟩ := consistentOn_outs hcons (j := j) L (by
      intro o ho
      simp only [L, List.mem_flatMap] at ho
      obtain ⟨p, _, ho⟩ := ho
      obtain ⟨τp, hp⟩ := hwf.1 p
      obtain ⟨σ, hσ⟩ := lrun_take hp (c p)
      obtain ⟨_, _, h3, _⟩ := rinv_of_produced T (compliant_take (hprod p) (c p)) hσ
      obtain ⟨i, hi, hle⟩ := h3 o ho
      exact ⟨i, hi, PO.trans hle (hj p σ hσ)⟩)
    refine ⟨u, hu, fun p γ o hm => hall o ?_⟩
    simp only [L, List.mem_flatMap]
    exact ⟨p, List.mem_finRange p, mem_emittedOf hm⟩


/-! ### (1)⇒(2) of Theorem `thm:complete-cap-response` -/

/-- Transport a local event to a history with another number of participants
(only ever applied to receive-free lists; receives become sends, which, like
receives, leave the state unchanged). -/
def tr {m N : Nat} : LEv sp D m → LEv sp D N
  | .inp j => .inp j
  | .out γ o => .out γ o
  | .send j d => .send j d
  | .recv _ _ j d => .send j d

theorem lrun_tr {m N : Nat} {σ τ : State sp} {l : List (LEv sp D m)} (h : LRun σ l τ) :
    LRun σ (l.map (tr (N := N))) τ := by
  induction h with
  | nil => exact .nil _
  | inp hs _ ih => exact .inp hs ih
  | out ha hs hx _ ih => exact .out ha hs hx ih
  | send _ ih => exact .send ih
  | recv _ ih => exact .send ih

theorem lrun_tr_inv {m N : Nat} {l : List (LEv sp D m)} :
    ∀ {σ τ : State sp}, LRun σ (l.map (tr (N := N))) τ → LRun σ l τ := by
  induction l with
  | nil => intro σ τ h; cases h; exact .nil _
  | cons e l ih =>
    intro σ τ h
    cases e with
    | inp j => cases h with | inp hs hr => exact .inp hs (ih hr)
    | out γ o => cases h with | out ha hs hx hr => exact .out ha hs hx (ih hr)
    | send j d => cases h with | send hr => exact .send (ih hr)
    | recv q k j d => cases h with | send hr => exact .recv (ih hr)

theorem tr_norecv {m N : Nat} (l : List (LEv sp D m)) (q : Fin N) (k : Nat) (j : Option I)
    (d : D) : LEv.recv q k j d ∉ l.map (tr (N := N)) := by
  intro h
  obtain ⟨e, _, he⟩ := List.mem_map.1 h
  cases e <;> simp [tr] at he

theorem erase_tr {m N : Nat} {l : List (LEv sp D m)}
    (hnr : ∀ q k j d, LEv.recv q k j d ∉ l) :
    (l.map (tr (N := N))).map LEv.erase = l.map LEv.erase := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    have ih' := ih (fun q k j d h => hnr q k j d (List.mem_cons_of_mem _ h))
    cases e with
    | recv q k j d => exact absurd (List.mem_cons_self ..) (hnr q k j d)
    | _ => simp only [List.map_cons, ih']; rfl

theorem compliant_tr {Sys : System sp D} {F : I → List (LEvN sp D) → LEvN sp D → Prop}
    (hF : ∀ n init p pre e, Sys.strat n init p pre e ↔ F (init p) (pre.map LEv.erase) e.erase)
    {m N : Nat} {init : Fin m → I} {init' : Fin N → I} {p : Fin m} {p' : Fin N}
    (hi : init' p' = init p) {l : List (LEv sp D m)} (hc : Compliant (Allowed Sys m init p) l)
    (hnr : ∀ q k j d, LEv.recv q k j d ∉ l) :
    Compliant (Allowed Sys N init' p') (l.map tr) := by
  intro a' e' b' h
  obtain ⟨l1, l2, rfl, h1, h2⟩ := List.map_eq_append_iff.1 h
  obtain ⟨e, l3, rfl, he, _⟩ := List.map_eq_cons_iff.1 h2
  subst h1 he
  have hA := hc l1 e l3 rfl
  have hnr1 : ∀ q k j d, LEv.recv q k j d ∉ l1 :=
    fun q k j d hm => hnr q k j d (List.mem_append_left _ hm)
  have hpre : (l1.map (tr (N := N))).map LEv.erase = l1.map LEv.erase := erase_tr hnr1
  cases e with
  | inp j => trivial
  | out γ o =>
    refine ⟨hA.1, (hF _ _ _ _ _).2 ?_⟩
    rw [hi, hpre]; exact (hF _ _ _ _ _).1 hA.2
  | send j d =>
    show Sys.strat _ _ _ _ _
    rw [hF, hi, hpre]; exact (hF _ _ _ _ _).1 hA
  | recv q k j d => exact absurd (by simp) (hnr q k j d)

theorem compliant_prefix {E : Type} {A : List E → E → Prop} {x y : List E}
    (h : Compliant A (x ++ y)) : Compliant A x := by
  have := compliant_take h x.length
  simpa using this

/-- In a partitioned history whose components are singletons, nobody receives. -/
theorem norecv_singletons {N : Nat} {init : Fin N → I} {H : History sp D N}
    (hwf : WF init H) (hpart : Partitioned H (fun p => p.val)) :
    ∀ p q k j d, LEv.recv q k j d ∉ H p := by
  intro p q k j d hm
  obtain ⟨a, b, hab⟩ := List.append_of_mem hm
  exact (hwf.2 p a q k j d b hab).1 (Fin.ext (hpart.2 p a q k j d b hab))

/-- Gluing receive-free, compliant local runs into a produced partitioned
history with singleton components. -/
theorem glue {Sys : System sp D} {N : Nat} (hN : 2 ≤ N) {init : Fin N → I}
    (L : History sp D N) (hnr : ∀ p q k j d, LEv.recv q k j d ∉ L p)
    (hc : ∀ p, Compliant (Allowed Sys N init p) (L p))
    (hr : ∀ p, ∃ τ, LRun (canon sp (init p)) (L p) τ) :
    WF init L ∧ Produced Sys N init L ∧ Partitioned L (fun p => p.val) ∧
    IsCut L (fun p => (L p).length) := by
  have hno : ∀ p a (q : Fin N) k j d b, L p ≠ a ++ LEv.recv q k j d :: b := by
    intro p a q k j d b h
    exact hnr p q k j d (by rw [h]; simp)
  refine ⟨⟨hr, fun p a q k j d b h => absurd h (hno p a q k j d b)⟩, hc,
    ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩, fun p a q k j d b h => absurd h (hno p a q k j d b)⟩,
    ⟨fun _ => Nat.le_refl _, fun p a q k j d b h => ?_⟩⟩
  rw [List.take_length] at h; exact absurd h (hno p a q k j d b)

/-- An isolated emission of `o` at current input `i` in some partitioned
history produced by the system. -/
def IsoEmit (Sys : System sp D) (i : I) (o : O) : Prop :=
  ∃ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat) (p : Fin n)
    (a b : List (LEv sp D n)) (γ : List (Commitment sp)) (σ : State sp),
    WF init H ∧ Produced Sys n init H ∧ Partitioned H comp ∧ H p = a ++ .out γ o :: b ∧
    (∀ q k j d, LEv.recv q k j d ∉ a) ∧ LRun (canon sp (init p)) a σ ∧ σ.cur = i

/-- Local data of an isolated emission. -/
structure LocW (Sys : System sp D) (i : I) (o : O) where
  n : Nat
  init : Fin n → I
  p : Fin n
  a : List (LEv sp D n)
  γ : List (Commitment sp)
  comp : Compliant (Allowed Sys n init p) (a ++ [LEv.out γ o])
  norecv : ∀ q k j d, LEv.recv q k j d ∉ a
  run : ∃ τ, LRun (canon sp (init p)) (a ++ [LEv.out γ o]) τ
  cur : ∀ σ, LRun (canon sp (init p)) a σ → σ.cur = i

theorem IsoEmit.loc {Sys : System sp D} {i : I} {o : O} (h : IsoEmit Sys i o) :
    Nonempty (LocW Sys i o) := by
  obtain ⟨n, init, H, _, p, a, b, γ, σ, hwf, hprod, _, hH, hnr, hσ, hcur⟩ := h
  have hH' : H p = (a ++ [LEv.out γ o]) ++ b := by simp [hH]
  obtain ⟨τ, hτ⟩ := hwf.1 p
  rw [hH'] at hτ
  obtain ⟨τ1, h1, _⟩ := lrun_append.1 hτ
  have hc := hprod p; rw [hH'] at hc
  exact ⟨⟨n, init, p, a, γ, compliant_prefix hc, hnr, ⟨τ1, h1⟩,
    fun σ' h => by rw [lrun_det h hσ]; exact hcur⟩⟩

/-- Replaying an isolated emission at a participant with the same initial input. -/
theorem LocW.replay {Sys : System sp D} {F : I → List (LEvN sp D) → LEvN sp D → Prop}
    (hF : ∀ n init p pre e, Sys.strat n init p pre e ↔ F (init p) (pre.map LEv.erase) e.erase)
    {i : I} {o : O} (w : LocW Sys i o) {N : Nat} {init' : Fin N → I} {p' : Fin N}
    (hi : init' p' = w.init w.p) :
    Compliant (Allowed Sys N init' p') ((w.a ++ [LEv.out w.γ o]).map tr) ∧
    (∀ q k j d, LEv.recv q k j d ∉ (w.a ++ [LEv.out w.γ o]).map (tr (N := N))) ∧
    (∃ τ, LRun (canon sp (init' p')) ((w.a ++ [LEv.out w.γ o]).map (tr (N := N))) τ) ∧
    (∀ σ, LRun (canon sp (init' p')) (w.a.map (tr (N := N))) σ → σ.cur = i) := by
  refine ⟨compliant_tr hF hi w.comp ?_, fun q k j d => tr_norecv _ q k j d, ?_, ?_⟩
  · intro q k j d hm
    rcases List.mem_append.1 hm with hm | hm
    · exact w.norecv q k j d hm
    · simp at hm
  · obtain ⟨τ, hτ⟩ := w.run; rw [hi]; exact ⟨τ, lrun_tr hτ⟩
  · intro σ h; rw [hi] at h; exact w.cur σ (lrun_tr_inv h)

theorem cut_of_norecv {N : Nat} {H : History sp D N} (hnr : ∀ p q k j d, LEv.recv q k j d ∉ H p)
    {c : Fin N → Nat} (hc : ∀ p, c p ≤ (H p).length) : IsCut H c := by
  refine ⟨hc, fun p a q k j d b h => absurd ?_ (hnr p q k j d)⟩
  have := take_split h; rw [this]; simp

/-- Answering, applied at a participant of a singleton-component history,
yields an isolated emission that expands every output the participant has
already emitted. -/
theorem answer_iso {Sys : System sp D} {Q : Obligation sp}
    (hRA : ResponseAvailability Sys (fun _ _ => Q.Q)) {N : Nat} {init : Fin N → I}
    {H : History sp D N} (hwf : WF init H) (hprod : Produced Sys N init H)
    (hpart : Partitioned H (fun p => p.val)) {c : Fin N → Nat} (hcut : IsCut H c)
    {p : Fin N} {σ : State sp} (hσ : LRun (canon sp (init p)) ((H p).take (c p)) σ) :
    ∃ u, Q.Q σ.cur u ∧ IsoEmit Sys σ.cur u ∧
      ∀ γ0 o, LEv.out γ0 o ∈ (H p).take (c p) → o ≼ u := by
  obtain ⟨⟨H', ext, hext, hwf', hprod', hpart', _, hnoinp, γ, u, hQ, hm⟩, _⟩ :=
    hRA N init H _ hwf hprod hpart c hcut p σ hσ
  obtain ⟨a, b, hab⟩ := List.append_of_mem hm
  have hH' : H' p = ((H p).take (c p) ++ a) ++ LEv.out γ u :: b := by rw [hext p, hab]; simp
  have hnr := norecv_singletons hwf' hpart'
  obtain ⟨τ, hτ⟩ := hwf'.1 p
  have hτ' := hτ; rw [hH'] at hτ'
  obtain ⟨σa, hσa, _⟩ := lrun_append.1 hτ'
  obtain ⟨σ1, h1, h2⟩ := lrun_append.1 hσa
  have hcur : σa.cur = σ.cur := by
    rw [lrun_noinp h2 (fun j hj => hnoinp j (by rw [hab]; simp [hj])), lrun_det h1 hσ]
  refine ⟨u, hQ, ⟨N, init, H', _, p, _, b, γ, σa, hwf', hprod', hpart', hH', ?_, hσa, hcur⟩, ?_⟩
  · intro q k j d hm'
    exact hnr p q k j d (by rw [hH']; exact List.mem_append_left _ hm')
  · intro γ0 o ho
    obtain ⟨l1, l2, hl⟩ := List.append_of_mem ho
    have : LRun (canon sp (init p)) (l1 ++ LEv.out γ0 o :: (l2 ++ ext p)) τ := by
      rw [hext p, hl] at hτ; simpa using hτ
    exact lrun_later_le this (List.mem_append_right _ hm)

/-- (1)⇒(2) of Theorem `thm:complete-cap-response`: `T` is the set of rows
of `Q` emitted in isolated emissions. -/
theorem response_necessary (Q : Obligation sp) (Sys : System sp D) (hrep : Sys.Replicated)
    (hRA : ResponseAvailability Sys (fun _ _ => Q.Q)) (hRPC : ResponsePC Sys) :
    ∃ T, ResponseInterface Q T ∧ ConsistentOn sp T := by
  classical
  obtain ⟨F, hF⟩ := hrep
  let T : Table I O := fun i o => Q.Q i o ∧ IsoEmit Sys i o
  -- replaying one isolated emission at participant `0` of two
  have replay2 : ∀ {i o} (w : LocW Sys i o),
      let L : History sp D 2 := fun q => if q.val = 0 then (w.a ++ [LEv.out w.γ o]).map tr else []
      let init : Fin 2 → I := fun _ => w.init w.p
      WF init L ∧ Produced Sys 2 init L ∧ Partitioned L (fun p => p.val) ∧
      IsCut L (fun p => (L p).length) ∧
      ∀ σ, LRun (canon sp (init 0)) ((L 0).take (L 0).length) σ → σ.cur = i := by
    intro i o w L init
    have hr := w.replay hF (N := 2) (init' := init) (p' := 0) rfl
    have hL0 : L 0 = (w.a ++ [LEv.out w.γ o]).map tr := rfl
    obtain ⟨h1, h2, h3, h4⟩ := glue (Sys := Sys) (by omega) (init := init) L
      (fun p => by
        by_cases hp : p.val = 0
        · simp only [L, hp, ↓reduceIte]; exact hr.2.1
        · simp only [L, hp, ↓reduceIte]; simp)
      (fun p => by
        by_cases hp : p.val = 0
        · have : p = 0 := Fin.ext hp
          subst this; exact hr.1
        · simp only [L, hp]; intro a e b h; simp at h)
      (fun p => by
        by_cases hp : p.val = 0
        · have : p = 0 := Fin.ext hp
          subst this; exact hr.2.2.1
        · simp only [L, hp]; exact ⟨_, .nil _⟩)
    refine ⟨h1, h2, h3, h4, fun σ hσ => ?_⟩
    rw [List.take_length, hL0, List.map_append] at hσ
    obtain ⟨σa, ha, hb⟩ := lrun_append.1 hσ
    rw [lrun_noinp hb (by simp [tr])]
    exact hr.2.2.2 σa ha
  refine ⟨T, ⟨fun _ _ h => h.1, ?_, ?_⟩, ?_⟩
  · -- totality
    intro i
    let L : History sp D 2 := fun _ => []
    obtain ⟨h1, h2, h3, h4⟩ := glue (Sys := Sys) (by omega) (init := fun _ => i) L
      (fun _ _ _ _ _ => by simp [L]) (fun _ a e b h => by simp [L] at h)
      (fun _ => ⟨_, .nil _⟩)
    obtain ⟨u, hQ, hiso, _⟩ := answer_iso hRA h1 h2 h3 h4 (p := 0) (σ := canon sp i) (.nil _)
    exact ⟨u, hQ, hiso⟩
  · -- self-continuation
    intro i o j hT hij
    let w := Classical.choice hT.2.loc
    obtain ⟨h1, h2, h3, h4, hcur⟩ := replay2 w
    let L : History sp D 2 := fun q => if q.val = 0 then (w.a ++ [LEv.out w.γ o]).map tr else []
    let init : Fin 2 → I := fun _ => w.init w.p
    obtain ⟨τ1, hτ1⟩ := h1.1 0
    have hτ1' : LRun (canon sp (init 0)) ((L 0).take (L 0).length) τ1 := by
      rw [List.take_length]; exact hτ1
    have hτc := hcur τ1 hτ1'
    obtain ⟨_, hacc⟩ := hRA 2 init L _ h1 h2 h3 _ h4 0 τ1 hτ1'
    obtain ⟨H2, ext2, hext2, hwf2, hprod2, hpart2, _, hinj⟩ := hacc j (hτc ▸ hij)
    obtain ⟨a2, b2, hab2⟩ := List.append_of_mem hinj
    have hnr2 := norecv_singletons hwf2 hpart2
    have hH20 : H2 0 = (L 0 ++ a2 ++ [LEv.inp j]) ++ b2 := by
      rw [hext2 0, List.take_length, hab2]; simp only [List.append_assoc, List.singleton_append]
      rfl
    let c2 : Fin 2 → Nat := fun q => if q.val = 0 then (L 0 ++ a2 ++ [LEv.inp j]).length
      else (H2 q).length
    have hc2 : IsCut H2 c2 := cut_of_norecv hnr2 (fun q => by
      by_cases hq : q.val = 0
      · have : q = 0 := Fin.ext hq
        subst this; simp only [c2, hq, ↓reduceIte]; rw [hH20]; simp
      · simp only [c2, hq, ↓reduceIte]; exact Nat.le_refl _)
    have htake : (H2 0).take (c2 0) = L 0 ++ a2 ++ [LEv.inp j] := by
      show List.take (if (0 : Fin 2).val = 0 then _ else _) _ = _
      simp only [Fin.val_zero, ↓reduceIte]; rw [hH20]; exact List.take_left' rfl
    obtain ⟨τ2, hτ2⟩ := hwf2.1 0
    obtain ⟨σ2, hσ2⟩ := lrun_take hτ2 (c2 0)
    have hσ2' := hσ2; rw [htake] at hσ2'
    obtain ⟨_, _, hlast⟩ := lrun_append.1 hσ2'
    have hj2 : σ2.cur = j := by
      cases hlast with
      | inp hs hr => cases hr; exact (step_input_inv hs).2.1
    obtain ⟨u, hQ, hiso, hge⟩ := answer_iso hRA hwf2 hprod2 hpart2 hc2 hσ2
    rw [hj2] at hQ hiso
    refine ⟨u, ⟨hQ, hiso⟩, hge w.γ o ?_⟩
    rw [htake]
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.2 ⟨LEv.out w.γ o, by simp, rfl⟩))
  · -- consistency on `T`
    intro rows hrows j hj
    by_cases hne : rows = []
    · subst hne; obtain ⟨u, hu⟩ := sp.total j; exact ⟨u, hu, by simp⟩
    have hlen : 0 < rows.length := by
      cases rows with
      | nil => exact absurd rfl hne
      | cons => simp
    let N := rows.length + 1
    have hT : ∀ r : Fin rows.length, T rows[r].1 rows[r].2 :=
      fun r => hrows _ (List.getElem_mem ..)
    let W : ∀ r : Fin rows.length, LocW Sys rows[r].1 rows[r].2 :=
      fun r => Classical.choice (hT r).2.loc
    let init : Fin N → I := fun p =>
      if h : p.val < rows.length then (W ⟨p.val, h⟩).init (W ⟨p.val, h⟩).p else j
    let L : History sp D N := fun p =>
      if h : p.val < rows.length then
        ((W ⟨p.val, h⟩).a ++ [LEv.out (W ⟨p.val, h⟩).γ rows[p.val].2]).map tr
      else []
    have hrep : ∀ (p : Fin N) (h : p.val < rows.length), _ := fun p h =>
      (W ⟨p.val, h⟩).replay hF (N := N) (init' := init) (p' := p)
        (by simp only [init, h, ↓reduceDIte])
    have hLp : ∀ (p : Fin N) (h : p.val < rows.length), L p =
        ((W ⟨p.val, h⟩).a ++ [LEv.out (W ⟨p.val, h⟩).γ rows[p.val].2]).map tr :=
      fun p h => by simp only [L, h, ↓reduceDIte]
    have hLn : ∀ (p : Fin N), ¬ p.val < rows.length → L p = [] :=
      fun p h => by simp only [L, h, ↓reduceDIte]
    obtain ⟨h1, h2, h3, h4⟩ := glue (Sys := Sys) (by omega) (init := init) L
      (fun p => by
        by_cases h : p.val < rows.length
        · rw [hLp p h]; exact (hrep p h).2.1
        · rw [hLn p h]; simp)
      (fun p => by
        by_cases h : p.val < rows.length
        · rw [hLp p h]; exact (hrep p h).1
        · rw [hLn p h]; intro a e b h; simp at h)
      (fun p => by
        by_cases h : p.val < rows.length
        · rw [hLp p h]; exact (hrep p h).2.2.1
        · rw [hLn p h]; exact ⟨_, .nil _⟩)
    have hcurs : ∀ p σ, LRun (canon sp (init p)) ((L p).take (L p).length) σ → σ.cur ≼ j := by
      intro p σ hσ
      rw [List.take_length] at hσ
      by_cases h : p.val < rows.length
      · rw [hLp p h, List.map_append] at hσ
        obtain ⟨σa, ha, hb⟩ := lrun_append.1 hσ
        rw [lrun_noinp hb (by simp [tr]), (hrep p h).2.2.2 σa ha]
        exact hj _ (List.getElem_mem ..)
      · rw [hLn p h] at hσ; cases hσ
        show init p ≼ j
        simp only [init, h, ↓reduceDIte]; exact PO.refl j
    obtain ⟨u, hu, hall⟩ := hRPC N init L _ h1 h2 h3 _ h4 j hcurs
    refine ⟨u, hu, fun r hr => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
    let p : Fin N := ⟨i, by omega⟩
    apply hall p (W ⟨i, hi⟩).γ
    rw [List.take_length, hLp p hi]
    exact List.mem_map.2 ⟨LEv.out _ _, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩

/-- **Theorem `thm:complete-cap-response`** (response form of Complete CAP),
for a uniform obligation `Q`. -/
theorem complete_cap_response (sp : Spec I O) (D : Type) (Q : Obligation sp) :
    (∃ Sys : System sp D, Sys.Replicated ∧ ResponseAvailability Sys (fun _ _ => Q.Q) ∧
      ResponsePC Sys) ↔
    ∃ T, ResponseInterface Q T ∧ ConsistentOn sp T :=
  ⟨fun ⟨Sys, hrep, hRA, hRPC⟩ => response_necessary Q Sys hrep hRA hRPC,
   fun ⟨T, hT, hc⟩ => ⟨respSystem T, response_sufficient Q T hT hc⟩⟩

end CAP
end CC
