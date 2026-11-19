import CoordCriterion.CAP.Coordination
import CoordCriterion.CALM.Lemmas

/-!
# Two-phase commit: counting votes over a fixed membership (§4.3)

Supports the paragraph "Locks in a shared-nothing database" of
`sections/distributed.tex`, case "No coordination": "the coordinator's
unanimity decision over a fixed set of participants is monotone, so it issues
no commitment that requires coordination."  `decide2PC_detects` checks the
sentence after it: the decision aborts exactly when the votes do not all say
yes.

The decision specification `voteSpec n`: an input records, for each of the
`n` fixed participants, its vote if received (`some true` = yes, `some false`
= no, `none` = not yet received), ordered pointwise by "a vote, once received,
does not change"; the output is the decision `undecided ≼ commit, abort`;
`P(v)` is `abort` if some received vote is no, `commit` if every participant
voted yes, and `undecided` otherwise.

* `voteSpec_functional`, `voteSpec_monotone`: it is a monotone function;
* `voteSpec_consistent`, `voteSpec_liftedMono`: hence consistent;
* `voteSpec_exposable`: every decision at every state reachable without
  commitment is exposable (no output event of the decision needs a
  commitment);
* `voteSpec_coordinationFree`: the system that emits decisions by
  output events (`respSystem S`) is coordination-free, so in particular
  needs no distributed coordination.

Modeling choice: the protocol steps of 2PC (prepare messages, the
coordinator's log, timeouts) are not modeled; only the decision rule is.  That
each owner's prepare is its own commitment, coordination at that owner only,
is the single-owner pattern of `ownerSys` (`CAP/Coordination.lean`).
-/

namespace CC
namespace CAP

open Classical

/-- Votes of `n` fixed participants; `none` = not yet received. -/
def Votes (n : Nat) : Type := Fin n → Option Bool

/-- A received vote does not change: `v ≼ w` iff every received vote of `v`
is the same in `w`. -/
instance (n : Nat) : PO (Votes n) where
  le v w := ∀ p, v p = none ∨ v p = w p
  refl _ _ := Or.inr rfl
  trans h₁ h₂ p := by
    rcases h₁ p with h | h
    · exact Or.inl h
    · rcases h₂ p with h' | h'
      · exact Or.inl (h.trans h')
      · exact Or.inr (h.trans h')
  antisymm {v w} h₁ h₂ := funext fun p => by
    rcases h₁ p with h | h
    · rcases h₂ p with h' | h'
      · exact h.trans h'.symm
      · exact h'.symm
    · exact h

/-- The coordinator's decision. -/
inductive Decision where
  | undecided | commit | abort
  deriving DecidableEq

instance : PO Decision where
  le a b := a = .undecided ∨ a = b
  refl _ := Or.inr rfl
  trans {a b c} h₁ h₂ := by
    rcases h₁ with rfl | rfl
    · exact Or.inl rfl
    · exact h₂
  antisymm {a b} h₁ h₂ := by
    rcases h₁ with rfl | h
    · rcases h₂ with h | h <;> exact h.symm
    · exact h

/-- Abort on a no vote; commit when every participant voted yes. -/
noncomputable def decide2PC {n : Nat} (v : Votes n) : Decision :=
  if ∃ p, v p = some false then .abort
  else if ∀ p, v p = some true then .commit
  else .undecided

/-- The decision specification. -/
noncomputable def voteSpec (n : Nat) : Spec (Votes n) Decision where
  P v d := d = decide2PC v
  total _ := ⟨_, rfl⟩

/-- The decision detects whether the votes agree: it is `abort` exactly when
some received vote is no, and `commit` exactly when every vote is yes; so once
every vote is in, it aborts exactly when the votes do not all agree on yes. -/
theorem decide2PC_detects {n : Nat} (v : Votes n) :
    (decide2PC v = .abort ↔ ∃ p, v p = some false) ∧
    (decide2PC v = .commit ↔ ∀ p, v p = some true) ∧
    ((∀ p, v p ≠ none) → (decide2PC v = .abort ↔ ¬ ∀ p, v p = some true)) := by
  have hab : decide2PC v = .abort ↔ ∃ p, v p = some false := by
    unfold decide2PC
    split
    · next h1 => exact ⟨fun _ => h1, fun _ => rfl⟩
    · next h1 => split <;> exact ⟨fun h => (by cases h), fun h => (h1 h).elim⟩
  have hco : decide2PC v = .commit ↔ ∀ p, v p = some true := by
    unfold decide2PC
    split
    · next h1 =>
      obtain ⟨p, hp⟩ := h1
      exact ⟨fun h => (by cases h), fun h => (by rw [h p] at hp; cases hp)⟩
    · split
      · next h2 => exact ⟨fun _ => h2, fun _ => rfl⟩
      · next h2 => exact ⟨fun h => (by cases h), fun h => (h2 h).elim⟩
  refine ⟨hab, hco, fun hall => hab.trans ⟨fun ⟨p, hp⟩ h => (by rw [h p] at hp; cases hp),
    fun h => ?_⟩⟩
  apply Classical.byContradiction
  intro hne
  apply h
  intro p
  cases hp : v p with
  | none => exact (hall p hp).elim
  | some b =>
    cases b with
    | true => rfl
    | false => exact (hne ⟨p, hp⟩).elim

theorem voteSpec_functional (n : Nat) : (voteSpec n).Functional :=
  fun _ _ _ h h' => h.trans h'.symm

/-- Counting votes over a fixed membership is monotone. -/
theorem decide2PC_mono {n : Nat} {v w : Votes n} (h : v ≼ w) :
    decide2PC v ≼ decide2PC w := by
  by_cases hno : ∃ p, v p = some false
  · obtain ⟨p, hp⟩ := hno
    have hw : ∃ p, w p = some false := ⟨p, by
      rcases h p with h' | h'
      · rw [hp] at h'; cases h'
      · rw [← h', hp]⟩
    have hv : ∃ p, v p = some false := ⟨p, hp⟩
    simp only [decide2PC, hv, hw, ite_true]; exact Or.inr rfl
  · by_cases hyes : ∀ p, v p = some true
    · have hvw : v = w := funext fun p => by
        rcases h p with h' | h'
        · rw [hyes p] at h'; cases h'
        · exact h'
      rw [hvw]; exact PO.refl _
    · simp only [decide2PC, hno, hyes, ite_false]; exact Or.inl rfl

theorem voteSpec_monotone (n : Nat) : (voteSpec n).MonotoneF := by
  intro v w d e hvw hd he
  show d ≼ e
  rw [hd, he]; exact decide2PC_mono hvw

theorem voteSpec_consistent (n : Nat) : (voteSpec n).Consistent :=
  (functional_calm (voteSpec_functional n)).2 (voteSpec_monotone n)

theorem voteSpec_liftedMono (n : Nat) : (voteSpec n).LiftedMono :=
  (CALM.liftedMono_iff_monoF (voteSpec_functional n)).2 (voteSpec_monotone n)

/-- No decision ever needs a commitment. -/
theorem voteSpec_exposable (n : Nat) :
    ∀ τ : State (voteSpec n), ReachableCF τ → ∀ d, τ.R τ.cur d → Exposable τ d :=
  (functional_exposure_boundary (voteSpec_functional n)).1 (voteSpec_monotone n)

/-- The system that emits decisions by output events is
coordination-free, and so needs no distributed coordination. -/
theorem voteSpec_coordinationFree (n : Nat) (D : Type) :
    (respSystem (sp := voteSpec n) (D := D) (voteSpec n).P).CoordinationFree ∧
      (respSystem (sp := voteSpec n) (D := D) (voteSpec n).P).CoordinationFreeH := by
  have hce : ConsistentOn (voteSpec n) (voteSpec n).P :=
    (CALM.commonExpansion_iff_monoF (voteSpec_functional n)).2 (voteSpec_monotone n)
  exact ⟨respSystem_coordinationFree _ hce, respSystem_coordinationFreeH _ hce⟩

/-! ## Prepares report the owners' commitments (§4.3)

"Each owner's prepare reports the commitment it has already made.  The
coordinator then makes the monotone decision whether all owners prepared; it
detects whether their commitments agree and aborts when they do not.  It does
not make the owners agree."

Owner `p` works from its own spec `sp p` and is at state `σ p`; `C p u` says
that output `u` of owner `p` commits the transaction.  The owner's prepare
reports whether the commitments it has made still allow commit: some remaining
row at its current input commits.  Its vote is that report.  The coordinator's
decision `decide2PC` commits exactly when every owner's commitments allow
commit, aborts exactly when some owner's rule it out, reads only the votes,
and changes no owner's state. -/

/-- Owner `p`'s prepare: yes exactly when its commitments still allow commit. -/
noncomputable def prepareVote {n : Nat} {I : Fin n → Type} {O : Fin n → Type}
    [∀ p, PO (I p)] [∀ p, PO (O p)] {sp : ∀ p, Spec (I p) (O p)}
    (C : ∀ p, O p → Prop) (σ : ∀ p, State (sp p)) : Votes n :=
  fun p => some (decide (∃ u, (σ p).R (σ p).cur u ∧ C p u))

/-- **The coordinator detects agreement.**  With every prepare in, the
decision commits exactly when every owner's commitments still allow commit,
and aborts exactly when some owner's commitments rule commit out. -/
theorem prepare_decide {n : Nat} {I : Fin n → Type} {O : Fin n → Type}
    [∀ p, PO (I p)] [∀ p, PO (O p)] {sp : ∀ p, Spec (I p) (O p)}
    (C : ∀ p, O p → Prop) (σ : ∀ p, State (sp p)) :
    (decide2PC (prepareVote C σ) = .commit ↔
      ∀ p, ∃ u, (σ p).R (σ p).cur u ∧ C p u) ∧
    (decide2PC (prepareVote C σ) = .abort ↔
      ∃ p, ¬ ∃ u, (σ p).R (σ p).cur u ∧ C p u) := by
  obtain ⟨hab, hco, _⟩ := decide2PC_detects (prepareVote C σ)
  refine ⟨hco.trans ?_, hab.trans ?_⟩
  · refine forall_congr' fun p => ?_
    simp [prepareVote]
  · refine exists_congr fun p => ?_
    simp [prepareVote]

/-! ## The voters' spec and its explicit relation (§4.4)

Supports the two-phase-commit example of the Complete CAP subsection:
"consider two-phase commit.  We focus on the spec for the voters; the
coordinator is an observer of that spec.  The fiber of interest is at the input
`prepare(tx)`: how each voter responds to that prepare message.  Each voter's
response is a row of `E`, while the sets of responses the coordinator may
observe across voters are implicit outputs in `P \ E`."

The single input is `prepare(tx)` (`Unit`); an output records the responses
received so far, voter by voter (`Votes n`, ordered as above).  Every
combination is permitted.  `E` contains the outputs in which exactly one
voter has responded. -/

/-- The voters' spec at the input `prepare(tx)`: every combination of
responses is permitted. -/
def votersSpec (n : Nat) : Spec Unit (Votes n) where
  P _ _ := True
  total _ := ⟨fun _ => none, trivial⟩

/-- Voter `p`'s response `b`, and no other. -/
def single {n : Nat} (p : Fin n) (b : Bool) : Votes n := fun q => if q = p then some b else none

/-- The explicit relation: one voter's response. -/
def votersE (n : Nat) : Table Unit (Votes n) := fun _ v => ∃ p b, v = single p b

theorem single_le_iff {n : Nat} {p : Fin n} {b : Bool} {u : Votes n} :
    single p b ≼ u ↔ u p = some b := by
  constructor
  · intro h
    rcases h p with h | h
    · simp [single] at h
    · simpa [single] using h.symm
  · intro h q
    by_cases hq : q = p
    · subst hq; exact Or.inr (by simp [single, h])
    · exact Or.inl (by simp [single, hq])

/-- **The voters' example.**  (1) `E ⊆ P`.  (2) With two voters or more, the
combined responses of two voters are permitted but not in `E`.  (3) Every
permitted output respects each voter's response: it is the least output that
extends all the single responses it contains. -/
theorem voters_explicit (n : Nat) :
    (∀ i v, votersE n i v → (votersSpec n).P i v) ∧
    (∀ (p q : Fin n), p ≠ q → ∀ b c : Bool,
      let u : Votes n := fun r => if r = p then some b else if r = q then some c else none
      (votersSpec n).P () u ∧ ¬ votersE n () u ∧ single p b ≼ u ∧ single q c ≼ u) ∧
    (∀ u : Votes n, (votersSpec n).P () u ∧
      (∀ p b, u p = some b → votersE n () (single p b) ∧ single p b ≼ u) ∧
      ∀ w : Votes n, (∀ p b, u p = some b → single p b ≼ w) → u ≼ w) := by
  refine ⟨fun _ _ _ => trivial, ?_, ?_⟩
  · intro p q hpq b c
    refine ⟨trivial, ?_, ?_, ?_⟩
    · rintro ⟨r, d, h⟩
      have hp := congrFun h p
      have hq := congrFun h q
      simp only [single, if_pos rfl, if_neg (Ne.symm hpq)] at hp hq
      by_cases hrp : p = r
      · subst hrp; simp [hpq.symm] at hq
      · simp [hrp] at hp
    · exact single_le_iff.2 (by simp)
    · exact single_le_iff.2 (by simp [hpq.symm])
  · intro u
    refine ⟨trivial, fun p b h => ⟨⟨p, b, rfl⟩, single_le_iff.2 h⟩, fun w hw p => ?_⟩
    cases hu : u p with
    | none => exact Or.inl rfl
    | some b => exact Or.inr ((single_le_iff.1 (hw p b hu)).symm ▸ rfl)

end CAP
end CC
