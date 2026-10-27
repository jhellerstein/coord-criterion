import CoordCriterion.FunctionalCALM.Theorem
import CoordCriterion.CALM.Examples

/-!
# Specifications induced by state machines (§6, `sec:operational-models`)

Supports the paragraph "Compiling a state machine" of
`sections/instances.tex`: Definition `def:induced-specification`,
Proposition `prop:induced-specification`, and the remarks after it.

* `Machine` — states `Q`, initial state `q0`, environment events `E`, a
  transition relation `step` that accepts every event in every state, and
  `obs : Q → O`;
* `Runs M q w q'` — `M` can reach `q'` from `q` by consuming `w` (head first);
* `Abs E I` — a map `α : E* → I` onto `I`, monotone for the prefix order
  (stated as `α w ≼ α (w ++ v)`);
* `induced M A` — the table `{(α w, obs q) : q₀ →w q}` (part (1): it is total);
* `Seq E` — event sequences ordered by prefix, `prefixAbs` the identity
  abstraction; `induced_prefix` is part (2);
* `RState M` — reachable states ordered by reachability (antisymmetry is the
  class `ReachAntisymm M`), `stateAbs` maps `w` to the state reached on it;
  `induced_state` is part (3);
* `prefix_common_expansion`, `functional_iff_order_independent` — the remarks
  after the proposition;
* `voteMachine`, `firstAbs`, `election_induced` — the election of §2.1 is the
  specification induced by a vote-counting machine under the first-ballot map.

Modeling choice: event sequences are `List E`; the prefix order lives on the
wrapper `Seq E` so that no global order is put on `List`.
-/

namespace CC
namespace SM

/-- A state machine with input-enabled transitions and an observation map. -/
structure Machine (Q E O : Type) where
  q0 : Q
  step : Q → E → Q → Prop
  enabled : ∀ q e, ∃ q', step q e q'
  obs : Q → O

variable {Q E O : Type}

/-- `Runs M q w q'`: `M` can reach `q'` from `q` by consuming `w`. -/
inductive Runs (M : Machine Q E O) : Q → List E → Q → Prop where
  | nil (q : Q) : Runs M q [] q
  | cons {q q' q'' : Q} {e : E} {w : List E} :
      M.step q e q' → Runs M q' w q'' → Runs M q (e :: w) q''

/-- `q` is reachable from the initial state. -/
def Reachable (M : Machine Q E O) (q : Q) : Prop := ∃ w, Runs M M.q0 w q

/-- `M` is deterministic: each event has at most one successor. -/
def Deterministic (M : Machine Q E O) : Prop :=
  ∀ q e q1 q2, M.step q e q1 → M.step q e q2 → q1 = q2

/-- Observations grow along every transition from a reachable state. -/
def TransMono [PO O] (M : Machine Q E O) : Prop :=
  ∀ q, Reachable M q → ∀ e q', M.step q e q' → M.obs q ≼ M.obs q'

theorem runs_exists (M : Machine Q E O) (q : Q) (w : List E) : ∃ q', Runs M q w q' := by
  induction w generalizing q with
  | nil => exact ⟨q, .nil q⟩
  | cons e w ih =>
    obtain ⟨q1, h1⟩ := M.enabled q e
    obtain ⟨q2, h2⟩ := ih q1
    exact ⟨q2, .cons h1 h2⟩

theorem runs_append {M : Machine Q E O} {q q1 q2 : Q} {w v : List E}
    (h1 : Runs M q w q1) (h2 : Runs M q1 v q2) : Runs M q (w ++ v) q2 := by
  revert h2
  induction h1 with
  | nil => exact id
  | cons hs _ ih => exact fun h2 => .cons hs (ih h2)

theorem runs_split {M : Machine Q E O} :
    ∀ {q q2 : Q} (w v : List E), Runs M q (w ++ v) q2 → ∃ q1, Runs M q w q1 ∧ Runs M q1 v q2
  | q, _, [], _, h => ⟨q, .nil q, h⟩
  | _, _, e :: w, v, h => by
    rw [List.cons_append] at h
    cases h with
    | cons hs hr =>
      obtain ⟨q1, h1, h2⟩ := runs_split w v hr
      exact ⟨q1, .cons hs h1, h2⟩

theorem runs_det {M : Machine Q E O} (hd : Deterministic M) {q q1 q2 : Q} {w : List E}
    (h1 : Runs M q w q1) (h2 : Runs M q w q2) : q1 = q2 := by
  revert q2
  induction h1 with
  | nil => intro _ h2; cases h2; rfl
  | cons hs _ ih =>
    intro _ h2
    cases h2 with
    | cons hs' hr' => exact ih (hd _ _ _ _ hs' hs ▸ hr')

/-- Along a run from a reachable state, observations grow when they grow
along single transitions. -/
theorem obs_le_of_runs [PO O] {M : Machine Q E O} (ht : TransMono M) {q q' : Q} {v : List E}
    (hq : Reachable M q) (h : Runs M q v q') : M.obs q ≼ M.obs q' := by
  induction h with
  | nil => exact PO.refl _
  | @cons q q1 _ e _ hs _ ih =>
    obtain ⟨w, hw⟩ := hq
    have hq1 : Reachable M q1 := ⟨w ++ [e], runs_append hw (.cons hs (.nil _))⟩
    exact PO.trans (ht q ⟨w, hw⟩ e q1 hs) (ih hq1)

/-! ## Definition `def:induced-specification` and part (1) -/

/-- A map from `E*` onto `I`, monotone for the prefix order. -/
structure Abs (E I : Type) [PO I] where
  α : List E → I
  onto : ∀ i, ∃ w, α w = i
  mono : ∀ w v, α w ≼ α (w ++ v)

/-- The specification induced by `M` and `α`: rows `(α w, obs q)` with
`q₀ →w q`.  Totality is part (1) of Proposition `prop:induced-specification`. -/
def induced {I : Type} [PO I] [PO O] (M : Machine Q E O) (A : Abs E I) : Spec I O where
  S i o := ∃ w q, A.α w = i ∧ Runs M M.q0 w q ∧ M.obs q = o
  total i := by
    obtain ⟨w, rfl⟩ := A.onto i
    obtain ⟨q, h⟩ := runs_exists M M.q0 w
    exact ⟨_, w, q, rfl, h, rfl⟩

/-- Remark: the fiber at `i` collects the observations of every run on every
sequence mapped to `i`, so the induced specification is functional exactly
when the observation after a run depends only on `α` of the sequence. -/
theorem functional_iff_order_independent {I : Type} [PO I] [PO O]
    (M : Machine Q E O) (A : Abs E I) :
    (induced M A).Functional ↔
      ∀ w w' q q', A.α w = A.α w' → Runs M M.q0 w q → Runs M M.q0 w' q' → M.obs q = M.obs q' := by
  constructor
  · intro hf w w' q q' ha h h'
    exact hf _ _ _ ⟨w, q, rfl, h, rfl⟩ ⟨w', q', ha.symm, h', rfl⟩
  · rintro hi i o o' ⟨w, q, rfl, h, rfl⟩ ⟨w', q', ha, h', rfl⟩
    exact hi w w' q q' ha.symm h h'

/-! ## Part (2): the prefix order -/

/-- Event sequences ordered by prefix. -/
structure Seq (E : Type) where
  ev : List E

instance : PO (Seq E) where
  le a b := ∃ v, b.ev = a.ev ++ v
  refl a := ⟨[], (List.append_nil _).symm⟩
  trans := fun ⟨v, hv⟩ ⟨u, hu⟩ => ⟨v ++ u, by rw [hu, hv, List.append_assoc]⟩
  antisymm := by
    intro ⟨a⟩ ⟨b⟩ ⟨v, hv⟩ ⟨u, hu⟩
    simp only at hv hu
    have h := congrArg List.length (hu.trans (congrArg (· ++ u) hv))
    simp only [List.length_append] at h
    have hv0 : v.length = 0 := by omega
    rw [List.length_eq_zero_iff] at hv0
    subst hv0
    rw [List.append_nil] at hv
    rw [hv]

/-- The identity abstraction on `E*` ordered by prefix. -/
def prefixAbs (E : Type) : Abs E (Seq E) where
  α := Seq.mk
  onto := fun ⟨w⟩ => ⟨w, rfl⟩
  mono := fun _ v => ⟨v, rfl⟩

/-- Monotonicity in the prefix order is monotonicity of `obs` along single
transitions from reachable states. -/
theorem prefix_mono_iff [PO O] (M : Machine Q E O) (hd : Deterministic M) :
    (induced M (prefixAbs E)).MonotoneF ↔ TransMono M := by
  constructor
  · intro hm q ⟨w, hw⟩ e q' hs
    exact hm ⟨w⟩ ⟨w ++ [e]⟩ _ _ ⟨[e], rfl⟩ ⟨w, q, rfl, hw, rfl⟩
      ⟨w ++ [e], q', rfl, runs_append hw (.cons hs (.nil _)), rfl⟩
  · rintro ht _ _ _ _ ⟨v, hv⟩ ⟨w, q, rfl, hw, rfl⟩ ⟨w', q', rfl, hw', rfl⟩
    simp only [prefixAbs] at hv
    subst hv
    obtain ⟨q1, h1, h2⟩ := runs_split w v hw'
    have := runs_det hd hw h1
    subst this
    exact obs_le_of_runs ht ⟨w, hw⟩ h2

/-- **Part (2).**  For deterministic `M` and the identity abstraction, the
induced specification is functional, and it is consistent iff observations
grow along every transition from a reachable state. -/
theorem induced_prefix [PO O] (M : Machine Q E O) (hd : Deterministic M) :
    (induced M (prefixAbs E)).Functional ∧
      ((induced M (prefixAbs E)).Consistent ↔ TransMono M) := by
  have hf : (induced M (prefixAbs E)).Functional := by
    rintro _ _ _ ⟨w, q, rfl, h, rfl⟩ ⟨w', q', hw, h', rfl⟩
    cases hw
    rw [runs_det hd h h']
  exact ⟨hf, (functional_calm hf).trans (prefix_mono_iff M hd)⟩

/-- Remark: under the prefix order two sequences have a common expansion only
when one extends the other. -/
theorem prefix_common_expansion (a b c : Seq E) (ha : a ≼ c) (hb : b ≼ c) : a ≼ b ∨ b ≼ a := by
  obtain ⟨v, hv⟩ := ha
  obtain ⟨u, hu⟩ := hb
  rcases List.append_eq_append_iff.1 (hv.symm.trans hu) with ⟨a', h1, _⟩ | ⟨c', h1, _⟩
  · exact Or.inl ⟨a', h1⟩
  · exact Or.inr ⟨c', h1⟩

/-- Remark: a deterministic machine whose observations only grow induces a
consistent specification under the prefix order. -/
theorem consistent_of_growing [PO O] (M : Machine Q E O) (hd : Deterministic M)
    (hg : ∀ q e q', M.step q e q' → M.obs q ≼ M.obs q') :
    (induced M (prefixAbs E)).Consistent :=
  ((induced_prefix M hd).2).2 fun q _ e q' hs => hg q e q' hs

/-! ## Part (3): states ordered by reachability -/

/-- Reachable states of `M`. -/
structure RState (M : Machine Q E O) where
  q : Q
  reach : Reachable M q

/-- Reachability between reachable states (the order of part (3)). -/
def RLe {M : Machine Q E O} (a b : RState M) : Prop := ∃ v, Runs M a.q v b.q

/-- Hypothesis of part (3): reachability is antisymmetric on reachable states. -/
class ReachAntisymm (M : Machine Q E O) : Prop where
  antisymm : ∀ a b : RState M, RLe a b → RLe b a → a.q = b.q

instance (M : Machine Q E O) [ReachAntisymm M] : PO (RState M) where
  le := RLe
  refl a := ⟨[], .nil _⟩
  trans := fun ⟨v, hv⟩ ⟨u, hu⟩ => ⟨_, runs_append hv hu⟩
  antisymm {a b} h1 h2 := by
    have := ReachAntisymm.antisymm a b h1 h2
    cases a; cases b
    simp only at this
    subst this
    rfl

/-- The state reached on `w` (unique when `M` is deterministic). -/
noncomputable def reached (M : Machine Q E O) (w : List E) : Q :=
  Classical.choose (runs_exists M M.q0 w)

theorem reached_spec (M : Machine Q E O) (w : List E) : Runs M M.q0 w (reached M w) :=
  Classical.choose_spec (runs_exists M M.q0 w)

/-- `α(w)` is the state reached on `w`. -/
noncomputable def stateAbs (M : Machine Q E O) [ReachAntisymm M] (hd : Deterministic M) :
    Abs E (RState M) where
  α w := ⟨reached M w, w, reached_spec M w⟩
  onto := fun ⟨q, w, hw⟩ => ⟨w, by
    have := runs_det hd (reached_spec M w) hw
    cases this; rfl⟩
  mono w v := by
    obtain ⟨q1, h1, h2⟩ := runs_split w v (reached_spec M (w ++ v))
    have := runs_det hd (reached_spec M w) h1
    exact ⟨v, this ▸ h2⟩

/-- The table of part (3) is `{(q, obs q)}` over reachable states. -/
theorem stateAbs_table (M : Machine Q E O) [ReachAntisymm M] [PO O] (hd : Deterministic M)
    (i : RState M) (o : O) : (induced M (stateAbs M hd)).S i o ↔ o = M.obs i.q := by
  constructor
  · rintro ⟨w, q, rfl, h, rfl⟩
    exact congrArg M.obs (runs_det hd h (reached_spec M w))
  · rintro rfl
    obtain ⟨w, rfl⟩ := (stateAbs M hd).onto i
    exact ⟨w, _, rfl, reached_spec M w, rfl⟩

/-- **Part (3).**  For deterministic `M` with reachability antisymmetric, the
specification over reachable states is consistent exactly when the one of
part (2) is (both mean `TransMono M`). -/
theorem induced_state (M : Machine Q E O) [ReachAntisymm M] [PO O] (hd : Deterministic M) :
    (induced M (stateAbs M hd)).Consistent ↔ (induced M (prefixAbs E)).Consistent := by
  have hf : (induced M (stateAbs M hd)).Functional := by
    intro i o o' h h'
    rw [(stateAbs_table M hd i o).1 h, (stateAbs_table M hd i o').1 h']
  refine (functional_calm hf).trans (Iff.trans ?_ ((induced_prefix M hd).2).symm)
  constructor
  · intro hm q hq e q' hs
    obtain ⟨w, hw⟩ := hq
    have hq' : Reachable M q' := ⟨w ++ [e], runs_append hw (.cons hs (.nil _))⟩
    exact hm ⟨q, w, hw⟩ ⟨q', hq'⟩ _ _ ⟨[e], .cons hs (.nil _)⟩
      ((stateAbs_table M hd _ _).2 rfl) ((stateAbs_table M hd _ _).2 rfl)
  · intro ht i j o u ⟨v, hv⟩ hio hju
    rw [(stateAbs_table M hd i o).1 hio, (stateAbs_table M hd j u).1 hju]
    exact obs_le_of_runs ht i.reach hv

/-! ## The election as an induced specification -/

open CALM (Ballots Cand Res winner elec)

/-- The three voters. -/
inductive Voter | v1 | v2 | v3

/-- Keep the first ballot. -/
def first : Option Cand → Cand → Option Cand
  | none, c => some c
  | some a, _ => some a

/-- Record a ballot unless the voter has already voted. -/
def record (b : Ballots) : Voter × Cand → Ballots
  | (.v1, c) => ⟨first b.b1 c, b.b2, b.b3⟩
  | (.v2, c) => ⟨b.b1, first b.b2 c, b.b3⟩
  | (.v3, c) => ⟨b.b1, b.b2, first b.b3 c⟩

/-- No ballot yet. -/
def noBallots : Ballots := ⟨none, none, none⟩

/-- The vote-counting machine: its state is the first ballot of each voter
received so far; it observes the candidate with two ballots, or `⊥`. -/
def voteMachine : Machine Ballots (Voter × Cand) Res where
  q0 := noBallots
  step q e q' := q' = record q e
  enabled _ _ := ⟨_, rfl⟩
  obs := winner

/-- The map recording each voter's first ballot. -/
def firstBallots (w : List (Voter × Cand)) : Ballots := w.foldl record noBallots

theorem record_ext (b : Ballots) (e : Voter × Cand) : b ≼ record b e := by
  have hf : ∀ (a : Option Cand) c, CALM.oleq a (first a c) := by
    intro a c; cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨v, c⟩ := e
  cases v
  · exact ⟨hf _ _, Or.inr rfl, Or.inr rfl⟩
  · exact ⟨Or.inr rfl, hf _ _, Or.inr rfl⟩
  · exact ⟨Or.inr rfl, Or.inr rfl, hf _ _⟩

theorem foldl_ext (b : Ballots) (v : List (Voter × Cand)) : b ≼ v.foldl record b := by
  induction v generalizing b with
  | nil => exact PO.refl _
  | cons e v ih => exact PO.trans (record_ext b e) (ih _)

/-- Events that cast the ballots of `b`. -/
def castAll (b : Ballots) : List (Voter × Cand) :=
  (b.b1.map (Voter.v1, ·)).toList ++ (b.b2.map (Voter.v2, ·)).toList ++
    (b.b3.map (Voter.v3, ·)).toList

/-- The first-ballot map as an abstraction (onto, monotone for prefix). -/
def firstAbs : Abs (Voter × Cand) Ballots where
  α := firstBallots
  onto := fun ⟨a1, a2, a3⟩ => ⟨castAll ⟨a1, a2, a3⟩, by
    rcases a1 with _ | _ | _ <;> rcases a2 with _ | _ | _ <;> rcases a3 with _ | _ | _ <;> rfl⟩
  mono w v := by
    simp only [firstBallots, List.foldl_append]
    exact foldl_ext _ v

theorem voteMachine_runs (q q' : Ballots) (w : List (Voter × Cand)) :
    Runs voteMachine q w q' ↔ q' = w.foldl record q := by
  induction w generalizing q with
  | nil =>
    constructor
    · intro h; cases h; rfl
    · rintro rfl; exact .nil _
  | cons e w ih =>
    constructor
    · intro h
      cases h with
      | cons hs hr => cases hs; exact (ih _).1 hr
    · intro h
      exact .cons rfl ((ih _).2 h)

/-- **The election is an induced specification.**  The specification induced
by the vote-counting machine under the first-ballot map has exactly the rows
of the election of §2.1; in particular its fibers are singletons
`{winner i}`. -/
theorem election_induced :
    (∀ i o, (induced voteMachine firstAbs).S i o ↔ elec.S i o) ∧
      (∀ i o, (induced voteMachine firstAbs).S i o ↔ o = winner i) ∧
      (∀ w w', firstBallots w = firstBallots w' →
        voteMachine.obs (reached voteMachine w) = voteMachine.obs (reached voteMachine w')) := by
  have key : ∀ i o, (induced voteMachine firstAbs).S i o ↔ o = winner i := by
    intro i o
    constructor
    · rintro ⟨w, q, rfl, h, rfl⟩
      rw [(voteMachine_runs _ _ _).1 h]
      rfl
    · rintro rfl
      obtain ⟨w, rfl⟩ := firstAbs.onto i
      exact ⟨w, _, rfl, (voteMachine_runs _ _ _).2 rfl, rfl⟩
  refine ⟨key, key, fun w w' h => ?_⟩
  rw [(voteMachine_runs _ _ _).1 (reached_spec voteMachine w),
    (voteMachine_runs _ _ _).1 (reached_spec voteMachine w')]
  exact congrArg winner h

end SM
end CC
