import CoordCriterion.CALM.Examples
import CoordCriterion.Distributed.Systems

/-!
# Figure tables of Sections 2–3 and the discussion

* Fig. `fig:election-frames`, panel (d) "(b), then polls closed", with the
  registrar's commitment (`closePolls`, a commitment in the sense of
  Def. `def:commitment`), the claims of Sec. `sec:election-story` and
  Sec. `sec:functional-events` about it, and the printed rows and upper
  fibers of panels (a)–(d) (`Elec.*`).  The figure prints exactly the rows
  whose input ⪰ `a··`, as its caption says (`Elec.printed_complete`).
* Fig. `fig:ambiguity-frames`(f), transaction ordering (`Txn.*`), and
  (g)–(h), traceroute from several sources (`Trace.*`), as printed, with the
  claims of Sec. `sec:ambiguity-story`, Sec. `sec:lifted-monotonicity`,
  Sec. `sec:lifted-output-events` and the remark after
  Prop. `prop:exposure-boundary`.

The election specification itself (`elec`, `elecEq`) is in
`CALM/Examples.lean`.
-/

namespace CC
namespace Figures

open Classical

/-! ## 0. Generic: closing the polls -/

section Close
variable {I O : Type} [PO I] [PO O] {sp : Spec I O}

theorem canon_R (sp : Spec I O) (i k : I) (u : O) :
    (canon sp i).R k u ↔ (sp.P k u ∧ i ≼ k) := Iff.rfl

/-- The state after closing the polls: only the rows at the current input. -/
def closeState (σ : State sp) : State sp where
  cur := σ.cur
  R k u := σ.R k u ∧ k = σ.cur
  sub k u h := σ.sub k u h.1
  hasCur := let ⟨o, h⟩ := σ.hasCur; ⟨o, h, rfl⟩
  above k u h := σ.above k u h.1

noncomputable def closeApp (σ : State sp) : Option (State sp) :=
  if ∃ k u, σ.R k u ∧ k ≠ σ.cur then some (closeState σ) else none

theorem closeApp_eq {σ τ : State sp} :
    closeApp σ = some τ ↔ (∃ k u, σ.R k u ∧ k ≠ σ.cur) ∧ closeState σ = τ := by
  unfold closeApp
  split
  · rename_i h; simp only [Option.some.injEq]; exact ⟨fun e => ⟨h, e⟩, fun ⟨_, e⟩ => e⟩
  · rename_i h; simp only [reduceCtorEq, false_iff]; exact fun ⟨h', _⟩ => h h'

/-- Closing the polls is a commitment (Def. `def:commitment`): it keeps the
current input, only removes rows, removes one, and every input where it
removes a row keeps none, so Eq. `commitment-unsubsumed` holds vacuously. -/
noncomputable def closePolls : Commitment sp where
  app := closeApp
  cur_eq σ τ h := by obtain ⟨_, rfl⟩ := closeApp_eq.1 h; rfl
  sub σ τ h k u hu := by obtain ⟨_, rfl⟩ := closeApp_eq.1 h; exact hu.1
  removes σ τ h := by
    obtain ⟨⟨k, u, hu, hk⟩, rfl⟩ := closeApp_eq.1 h
    exact ⟨k, u, hu, fun h' => hk h'.2⟩
  unsubsumed σ τ h k u w hu hnu hw := by
    obtain ⟨_, rfl⟩ := closeApp_eq.1 h
    exact absurd ⟨hu, hw.2⟩ hnu

/-- It is a commitment: at every input where it removes a row, it removes all rows. -/
theorem closePolls_excludes_input {σ τ : State sp} (h : (closePolls (sp := sp)).app σ = some τ)
    (k : I) (hk : ∃ u, σ.R k u ∧ ¬ τ.R k u) : ∀ w, ¬ τ.R k w := by
  obtain ⟨_, rfl⟩ := closeApp_eq.1 h
  obtain ⟨u, hu, hnu⟩ := hk
  intro w hw
  exact hnu ⟨hu, hw.2⟩

end Close

/-! ## 1. Fig. `fig:election-frames` -/

namespace Elec
open CC.CALM

def babb : Ballots := ⟨some .a, some .b, some .b⟩   -- abb
def baaa : Ballots := ⟨some .a, some .a, some .a⟩   -- aaa
def baab : Ballots := ⟨some .a, some .a, some .b⟩   -- aab
def ba_a : Ballots := ⟨some .a, none, some .a⟩      -- a·a
def ba_b : Ballots := ⟨some .a, none, some .b⟩      -- a·b

/-- The nine inputs printed in each panel, in order, with their outputs. -/
def printed : List (Ballots × Res) :=
  [(bad, .bot), (bab, .bot), (baba, .win .a), (babb, .win .b),
   (baa, .win .a), (baaa, .win .a), (baab, .win .a),
   (ba_a, .win .a), (ba_b, .bot)]

/-- The printed outputs are the election's: every printed pair is a row. -/
theorem printed_rows : ∀ r ∈ printed, elec.P r.1 r.2 := by
  intro r hr
  simp only [printed, List.mem_cons, List.mem_nil_iff, or_false] at hr
  show r.2 = winner r.1
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Tactic helper: split a ballot into its 27 values. -/
macro "ballot_cases" k:ident : tactic =>
  `(tactic| (obtain ⟨b1, b2, b3⟩ := $k:ident;
             rcases b1 with _ | _ | _ <;> rcases b2 with _ | _ | _ <;>
             rcases b3 with _ | _ | _))

/-- The inputs `⪰ a··` are nine: the seven printed ones and `a·a`, `a·b`. -/
theorem shown_inputs (k : Ballots) :
    bad ≼ k ↔ (k = bad ∨ k = bab ∨ k = baba ∨ k = babb ∨ k = baa ∨ k = baaa ∨ k = baab ∨
      k = ba_a ∨ k = ba_b) := by
  ballot_cases k <;> decide

/-- The figure prints exactly the rows whose input `⪰ a··`: a pair is printed
iff it is a row of the election at such an input. -/
theorem printed_complete (k : Ballots) (o : Res) :
    (k, o) ∈ printed ↔ (bad ≼ k ∧ elec.P k o) := by
  constructor
  · intro hr
    refine ⟨?_, printed_rows _ hr⟩
    simp only [printed, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with h | h | h | h | h | h | h | h | h <;>
      (obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; decide)
  · rintro ⟨hk, hS⟩
    have hS' : o = winner k := hS
    subst hS'
    rcases (shown_inputs k).1 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [printed] <;> decide

/-- Future-output sets of panels (a) and (b): `{⊥, x, y}`. -/
theorem upper_ab (o : Res) :
    (∃ k, (canon elec bad).R k o) ∧ (∃ k, (canon elec bab).R k o) := by
  rcases o with _ | ⟨_ | _⟩
  · exact ⟨⟨bad, (by decide : Res.bot = winner bad), PO.refl _⟩,
      ⟨bab, (by decide : Res.bot = winner bab), PO.refl _⟩⟩
  · exact ⟨⟨baa, (by decide : Res.win .a = winner baa), by decide⟩,
      ⟨baba, (by decide : Res.win .a = winner baba), by decide⟩⟩
  · exact ⟨⟨babb, (by decide : Res.win .b = winner babb), by decide⟩,
      ⟨babb, (by decide : Res.win .b = winner babb), by decide⟩⟩

/-- Future-output set of panel (c): `{x}`. -/
theorem upper_c (o : Res) : (∃ k, (canon elec baa).R k o) ↔ o = .win .a := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨o', ho'⟩ := elec_panel_c_determined
    exact (ho' k o hk).trans ((ho' baa (.win .a) ⟨(by decide : Res.win .a = winner baa),
      PO.refl _⟩).symm)
  · rintro rfl; exact ⟨baa, (by decide : Res.win .a = winner baa), PO.refl _⟩

/-- Panel (b): the rows at printed inputs that remain are exactly
`(ab·,⊥)`, `(aba,a)`, `(abb,b)`; the other printed rows are subsumed by
`input(ab·)` (their input does not extend `ab·`). -/
theorem panel_b (k : Ballots) (o : Res) (hk : bad ≼ k) :
    ((canon elec bab).R k o ↔
      ((k = bab ∧ o = .bot) ∨ (k = baba ∧ o = .win .a) ∨ (k = babb ∧ o = .win .b))) ∧
    (elec.P k o → ¬ (canon elec bab).R k o → ¬ bab ≼ k) := by
  rw [canon_R]
  show ((o = winner k ∧ bab ≼ k) ↔ _) ∧ (o = winner k → ¬ (o = winner k ∧ bab ≼ k) → _)
  revert hk
  ballot_cases k <;> rcases o with _ | ⟨_ | _⟩ <;> decide

/-! ### Panel (d): (b), then polls closed -/

/-- The state of panel (d). -/
noncomputable def panelD : State elec := closeState (canon elec bab)

/-- Closing the polls is defined at panel (b) (the row `(aba, a)` is at
another input) and yields panel (d). -/
theorem close_at_b : (closePolls (sp := elec)).app (canon elec bab) = some panelD :=
  closeApp_eq.2 ⟨⟨baba, .win .a, ⟨(by decide : Res.win .a = winner baba), by decide⟩,
    by decide⟩, rfl⟩

/-- Closing the polls after every voter has voted applies no commitment: at the
canonical state of a full ballot (all three cast) there is no row at another
input, so `closePolls` is undefined there. -/
theorem close_after_voting (i : Ballots) (hfull : i.b1.isSome ∧ i.b2.isSome ∧ i.b3.isSome) :
    (closePolls (sp := elec)).app (canon elec i) = none := by
  show closeApp (canon elec i) = none
  unfold closeApp
  split
  · rename_i h
    exfalso
    obtain ⟨k, u, ⟨_, hik⟩, hne⟩ := h
    apply hne
    revert hfull hik
    show _ → _ → k = i
    ballot_cases i <;> ballot_cases k <;> decide
  · rfl

/-- Panel (d)'s remainder table is the single row `(ab·, ⊥)`. -/
theorem panelD_rows (k : Ballots) (o : Res) : panelD.R k o ↔ (k = bab ∧ o = .bot) := by
  constructor
  · rintro ⟨⟨hS, _⟩, rfl⟩
    exact ⟨rfl, hS.trans (by decide)⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨(by decide : Res.bot = winner bab), PO.refl _⟩, rfl⟩

theorem panelD_cur : panelD.cur = bab := rfl

/-- "Future-output set `{⊥}`; determined; `⊥` is the result." -/
theorem panelD_determined : Determined panelD ∧ ∀ k x, panelD.R k x → x = .bot :=
  ⟨⟨.bot, fun k x h => ((panelD_rows k x).1 h).2⟩, fun k x h => ((panelD_rows k x).1 h).2⟩

/-- The commitment removes exactly the still-possible rows `(aba, a)` and `(abb, b)`
(struck through), and these inputs are legal at (b) and extend the current
input: input alone would not have removed them. -/
theorem panelD_struck (k : Ballots) (o : Res) :
    ((canon elec bab).R k o ∧ ¬ panelD.R k o) ↔
      ((k = baba ∧ o = .win .a) ∨ (k = babb ∧ o = .win .b)) := by
  rw [canon_R, panelD_rows]
  show ((o = winner k ∧ bab ≼ k) ∧ ¬ (k = bab ∧ o = .bot)) ↔ _
  ballot_cases k <;> rcases o with _ | ⟨_ | _⟩ <;> decide

/-- The printed gray-only rows of (d) are those lost after `input(ab·)`;
the current input is unchanged by the commitment. -/
theorem panelD_gray (k : Ballots) (o : Res) (hk : bad ≼ k) (hS : elec.P k o) :
    ¬ panelD.R k o ↔ (¬ bab ≼ k ∨ (k = baba ∧ o = .win .a) ∨ (k = babb ∧ o = .win .b)) := by
  rw [panelD_rows]
  have hS' : o = winner k := hS
  subst hS'
  revert hk
  ballot_cases k <;> decide

/-- The registrar closes the polls when it emits `⊥`: at (b), the commitment
event `apply([closePolls])` followed by `output(⊥)` is a run under any basis
containing `closePolls`; `⊥` is legal after the commitment, and the run ends
at panel (d). -/
theorem registrar_step (B : CommitmentBasis elec) (hB : B closePolls) :
    SysExec B (canon elec bab) [.commitment [closePolls], .output .bot] panelD := by
  refine .cons (SysStep.commitment (fun c hc => by simp at hc; subst hc; exact hB)
    (List.cons_ne_nil _ _) (ApplySeq.cons close_at_b (ApplySeq.nil _))) (.cons ?_ (.nil _))
  refine legal_output_step (Step.output _ _ _ ((panelD_rows _ _).2 ⟨rfl, rfl⟩) rfl ?_) ?_
  · funext k x; apply propext
    exact ⟨fun h => ⟨h, Or.inl rfl⟩, fun h => h.1⟩
  · intro k x _ hx; exact absurd (Or.inl rfl) hx

/-- "Emitting `⊥` by itself would need no commitment": at (b), `⊥` is
exposable, `Excluded_⊥` is empty, and `output(⊥)` removes no
row; so the commitment is not required by the output. -/
theorem bot_alone_at_b :
    Exposable (canon elec bab) .bot ∧
      (¬ ∃ k x, Excluded (canon elec bab) .bot k x) ∧
      outputTable (canon elec bab) .bot = (canon elec bab).R := by
  have he := elec_panels_exposable.2.1
  refine ⟨he, (exposable_iff_empty _ _).1 he, ?_⟩
  funext k x
  apply propext
  exact ⟨fun h => h.1, fun h => ⟨h, Or.inl rfl⟩⟩

/-- Fig. `fig:nonmonotone-frame`: "the table matches Fig. (d)": panel (d)'s
remainder table is that of `output(⊥)` at (b) under the equality order. -/
theorem panelD_matches_e (k : Ballots) (r : Res) :
    panelD.R k r ↔ outputTable (canon elecEq bab) ⟨.bot⟩ k ⟨r⟩ := by
  rw [panelD_rows, elecEq_bot_single_row]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by rw [h2]⟩, fun ⟨h1, h2⟩ => ⟨h1, by cases h2; rfl⟩⟩

/-- "Extra commitments are a system's choice, not the spec's": the
registrar's run has an observably equivalent run of the transition system
(`input`/`output` events), whose table contains panel (d)'s. -/
theorem registrar_canonical (B : CommitmentBasis elec) (hB : B closePolls) :
    ∃ ρ', Exec (canon elec bab) [.output .bot] ρ' ∧ ρ'.cur = bab ∧
      ∀ k u, panelD.R k u → ρ'.R k u := by
  obtain ⟨_, ρ', _, _, hx, hc, hsub⟩ :=
    canonical_equivalent (registrar_step B hB)
  exact ⟨ρ', hx, hc, hsub⟩

/-! ### Sec. `sec:discussion`: decisive ballot vs. closing the polls -/

/-- Fill missing ballots with `x`. -/
def fillA (i : Ballots) : Ballots :=
  ⟨some (i.b1.getD .a), some (i.b2.getD .a), some (i.b3.getD .a)⟩

theorem fillA_spec (i : Ballots) : i ≼ fillA i ∧ (winner i = .bot → winner (fillA i) = .win .a) := by
  ballot_cases i <;> decide

/-- A determined canonical state of the election has a winner. -/
theorem determined_has_winner (i : Ballots) (h : Determined (canon elec i)) : winner i ≠ .bot := by
  intro hb
  obtain ⟨o, ho⟩ := h
  have h1 := ho i (winner i) ⟨rfl, PO.refl _⟩
  have h2 := ho (fillA i) (winner (fillA i)) ⟨rfl, (fillA_spec i).1⟩
  rw [(fillA_spec i).2 hb] at h2; rw [hb] at h1
  rw [← h1] at h2; cases h2

/-- A canonical state whose current input has a winner is determined. -/
theorem winner_determined (i : Ballots) (c : Cand) (h : winner i = .win c) :
    Determined (canon elec i) := by
  refine ⟨.win c, fun k x hk => ?_⟩
  obtain ⟨hS, hle⟩ := hk
  have hm := winner_mono_raw i k hle
  rw [h] at hm
  rcases hm with hm | hm
  · cases hm
  · exact hS.trans hm.symm

/-- **Decisive ballot vs. closing the polls.**  (1) A decisive ballot
(`input(aa·)` at panel (a)) reaches a determined state and every row it
removes is lost after input (its input no longer extends the current input).
(2) Closing the polls at (b) reaches a determined state and every row it
removes is at a legal input extending the current one (a commitment).
(3) The results differ: in the election, closing the polls at any
undetermined canonical state leaves the single result `⊥`, while every
determined canonical state has a winner. -/
theorem decisive_vs_close :
    (Step (canon elec bad) (.input baa) (canon elec baa) ∧ Determined (canon elec baa) ∧
      ∀ k u, (canon elec bad).R k u → ¬ (canon elec baa).R k u → ¬ baa ≼ k) ∧
    (Determined panelD ∧ ∀ k u, (canon elec bab).R k u → ¬ panelD.R k u →
      bab ≼ k ∧ k ≠ bab) ∧
    (∀ i, ¬ Determined (canon elec i) →
      (closePolls (sp := elec)).app (canon elec i) = some (closeState (canon elec i)) ∧
      ∀ k x, (closeState (canon elec i)).R k x → x = .bot) ∧
    (∀ i, Determined (canon elec i) → ∃ c, winner i = .win c) := by
  refine ⟨⟨Dist.step_canon_input elec (by decide) ⟨_, rfl⟩, elec_panel_c_determined, ?_⟩,
    ⟨panelD_determined.1, ?_⟩, ?_, ?_⟩
  · intro k u hu hn hk; exact hn ⟨hu.1, hk⟩
  · intro k u hu hn
    exact ⟨hu.2, fun hk => hn ⟨hu, hk⟩⟩
  · intro i hnd
    have hb : winner i = .bot := by
      cases hw : winner i with
      | bot => rfl
      | win c => exact absurd (winner_determined i c hw) hnd
    refine ⟨closeApp_eq.2 ⟨?_, rfl⟩, ?_⟩
    · refine ⟨fillA i, winner (fillA i), ⟨rfl, (fillA_spec i).1⟩, fun he => ?_⟩
      show False
      have : winner i = .win .a := by
        have e : fillA i = i := he
        rw [← e]; exact (fillA_spec i).2 hb
      rw [hb] at this; cases this
    · rintro k x ⟨⟨hS, _⟩, rfl⟩
      exact hS.trans hb
  · intro i hd
    cases hw : winner i with
    | bot => exact absurd hw (determined_has_winner i hd)
    | win c => exact ⟨c, rfl⟩

end Elec

/-! ## 2. Fig. `fig:ambiguity-frames`(f): transaction ordering

The printed table: the input `{A,B}` (one input, modeled by `Unit`) with the
two serial orders `[A,B]` and `[B,A]`, under the equality order. -/

namespace Txn

inductive TOut | ab | ba
  deriving DecidableEq

instance : PO TOut where
  le a b := a = b
  refl _ := rfl
  trans h1 h2 := h1.trans h2

instance : PO.Antisymm TOut where
  antisymm h _ := h

def spec : Spec Unit TOut where
  P _ _ := True
  total _ := ⟨.ab, trivial⟩

theorem le_iff (a b : TOut) : a ≼ b ↔ a = b := Iff.rfl

theorem sR (o : TOut) : (canon spec ()).R () o := ⟨trivial, trivial⟩

/-- After `output([A,B])` only the row `({A,B}, [A,B])` remains. -/
theorem after_ab (k : Unit) (o : TOut) : outputTable (canon spec ()) .ab k o ↔ o = .ab :=
  ⟨fun h => h.2.symm, fun h => ⟨sR o, h.symm⟩⟩

/-- "No remaining row extends the removed one": the row `[B,A]` is in
`Excluded_o` (a commitment), not excluded (the input keeps `[A,B]`) and not subsumed
(no row extends both). -/
theorem ba_excluded :
    Excluded (canon spec ()) .ab () .ba ∧
      ¬ Subsumed (canon spec ()) .ab () .ba ∧
      ¬ ∃ u, spec.P () u ∧ TOut.ab ≼ u ∧ TOut.ba ≼ u := by
  have hnr : ¬ Subsumed (canon spec ()) .ab () .ba := by
    rintro ⟨_, _, u, _, h1, h2⟩
    exact TOut.noConfusion (h1.trans h2.symm)
  refine ⟨⟨sR _, fun h => TOut.noConfusion h, hnr⟩, hnr, ?_⟩
  rintro ⟨u, _, h1, h2⟩
  exact TOut.noConfusion (h1.trans h2.symm)

/-- Emitting `[A,B]` is not exposable: it requires a commitment, and every
system output event emitting it applies `x_[A,B]`, which must belong to the
system's basis. -/
theorem ab_not_exposable : ¬ Exposable (canon spec ()) .ab ∧
    ∀ (B : CommitmentBasis spec) τ,
      SysStep B (canon spec ()) (.output .ab) τ → B (canonicalCommitment .ab) := by
  have hn : ¬ Exposable (canon spec ()) .ab :=
    fun h => (exposable_iff_empty _ _).1 h ⟨(), .ba, ba_excluded.1⟩
  refine ⟨hn, ?_⟩
  intro B τ h
  cases h with
  | output _ hb => exact hb.resolve_left hn

/-- The commitment `x_[A,B]` applies at `{A,B}`; it removes `[B,A]` while the
input stays legal (the row `[A,B]` remains). -/
theorem commitment_applies :
    (canonicalCommitment (sp := spec) .ab).app (canon spec ()) =
      some (commitmentState (canon spec ()) .ab (sR .ab)) ∧
      (commitmentState (canon spec ()) .ab (sR .ab)).R () .ab ∧
      ¬ (commitmentState (canon spec ()) .ab (sR .ab)).R () .ba :=
  ⟨commitmentApp_eq.2 ⟨sR _, ⟨(), .ba, ba_excluded.1⟩, rfl⟩,
   ⟨sR _, fun h => h.2.1 (PO.refl _)⟩, fun h => h.2 ba_excluded.1⟩

/-- The two orders are incompatible: not directed, not monotone, not
consistent. -/
theorem not_monotone :
    ¬ CompatibleIn (spec.P ()) [.ab, .ba] ∧ ¬ spec.DirectedOutputs ∧ ¬ spec.LiftedMono ∧
      ¬ spec.Consistent := by
  have hc : ¬ CompatibleIn (spec.P ()) [.ab, .ba] := by
    rintro ⟨u, hu, hall⟩
    exact ba_excluded.2.2 ⟨u, hu, hall _ (by simp), hall _ (by simp)⟩
  have hd : ¬ spec.DirectedOutputs := fun h => hc (h () [.ab, .ba] (by simp) (fun _ _ => trivial))
  have hl : ¬ spec.LiftedMono := fun h => hc (h () () trivial [.ab, .ba] (by simp)
    (fun _ _ => trivial))
  exact ⟨hc, hd, hl, fun h => hl ((complete_calm spec).1 h)⟩

/-- "Two transaction scheduling runs that emit `[A,B]` and `[B,A]`" cannot be
reconciled at `{A,B}`. -/
theorem runs_not_confluent :
    ¬ ConfluentAt [outState (canon spec ()) .ab (sR _), outState (canon spec ()) .ba (sR _)] () := by
  intro h
  have hrun : ∀ σ ∈ [outState (canon spec ()) .ab (sR _), outState (canon spec ()) .ba (sR _)],
      IsRun σ := by
    intro σ hσ
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hσ
    rcases hσ with rfl | rfl
    · exact ⟨(), _, Exec.cons (Step.output _ (outState _ _ _) _ (sR _) rfl rfl) (Exec.nil _)⟩
    · exact ⟨(), _, Exec.cons (Step.output _ (outState _ _ _) _ (sR _) rfl rfl) (Exec.nil _)⟩
  obtain ⟨u, hu, hall⟩ := (survivor_test _ hrun () (fun _ _ => trivial)).1 h
  exact ba_excluded.2.2 ⟨u, hu, (hall (outState (canon spec ()) .ab (sR _)) (by simp)).2,
    (hall (outState (canon spec ()) .ba (sR _)) (by simp)).2⟩

end Txn

/-! ## 3. Fig. `fig:ambiguity-frames`(g)–(h): traceroute from several sources

Inputs are the nonempty sets of traced sources among `s` and `t` (`Src`),
ordered by inclusion.  Outputs are sets of the four routes `s→s1`, `s→h`,
`s→h→s2`, `t→s2` (a `Bool` per route), ordered by inclusion.  The fiber at a
set of sources contains every nonempty set of routes from those sources that
contains each prefix of its routes (`s→h` whenever `s→h→s2`); at `{s}` these
are the five route sets the figure prints, and at `{s,t}` the eleven it
prints. -/

namespace Trace

/-- The nonempty sets of traced sources: `{s}`, `{t}`, `{s,t}`. -/
inductive Src where
  | s | t | st
  deriving DecidableEq

def Src.leb : Src → Src → Bool
  | .s, .s => true
  | .s, .st => true
  | .t, .t => true
  | .t, .st => true
  | .st, .st => true
  | _, _ => false

instance : PO Src where
  le a b := a.leb b = true
  refl a := by cases a <;> rfl
  trans {a b c} h1 h2 := by
    cases a <;> cases b <;> cases c <;> simp_all [Src.leb]

instance : PO.Antisymm Src where
  antisymm {a b} h1 h2 := by
    dsimp only [PO.le] at *
    cases a <;> cases b <;> simp_all [Src.leb]

instance (a b : Src) : Decidable (a ≼ b) := inferInstanceAs (Decidable (a.leb b = true))

def Src.hasS : Src → Bool
  | .t => false
  | _ => true

def Src.hasT : Src → Bool
  | .s => false
  | _ => true

/-- A set of observed routes: `s→s1`, `s→h`, `s→h→s2`, `t→s2`. -/
structure RS where
  s1 : Bool
  h : Bool
  h2 : Bool
  t2 : Bool
  deriving DecidableEq

abbrev RS.sub (x y : RS) : Prop :=
  (x.s1 = true → y.s1 = true) ∧ (x.h = true → y.h = true) ∧
    (x.h2 = true → y.h2 = true) ∧ (x.t2 = true → y.t2 = true)

instance : PO RS where
  le := RS.sub
  refl _ := ⟨id, id, id, id⟩
  trans h1 h2 := ⟨h2.1 ∘ h1.1, h2.2.1 ∘ h1.2.1, h2.2.2.1 ∘ h1.2.2.1, h2.2.2.2 ∘ h1.2.2.2⟩

instance : PO.Antisymm RS where
  antisymm {x y} h1 h2 := by
    dsimp only [PO.le] at *
    obtain ⟨a, b, c, d⟩ := x; obtain ⟨e, f, g, k⟩ := y
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;>
      cases k <;> simp_all [RS.sub]

instance (x y : RS) : Decidable (x ≼ y) := inferInstanceAs (Decidable (RS.sub x y))

def rS1 : RS := ⟨true, false, false, false⟩     -- {s→s1}
def rH : RS := ⟨false, true, false, false⟩      -- {s→h}
def rH2 : RS := ⟨false, true, true, false⟩      -- {s→h, s→h→s2}
def rS1H : RS := ⟨true, true, false, false⟩     -- {s→s1, s→h}
def rAll : RS := ⟨true, true, true, false⟩      -- {s→s1, s→h, s→h→s2}
def rT : RS := ⟨false, false, false, true⟩      -- {t→s2}
def rS1T : RS := ⟨true, false, false, true⟩     -- {s→s1, t→s2}
def rHT : RS := ⟨false, true, false, true⟩      -- {s→h, t→s2}
def rH2T : RS := ⟨false, true, true, true⟩      -- {s→h, s→h→s2, t→s2}
def rS1HT : RS := ⟨true, true, false, true⟩     -- {s→s1, s→h, t→s2}
def rAllT : RS := ⟨true, true, true, true⟩      -- {s→s1, s→h, s→h→s2, t→s2}

/-- Membership in the fiber at `X`: nonempty, prefix-closed, and only routes
from the traced sources. -/
def fibB (X : Src) (x : RS) : Bool :=
  (x.s1 || x.h || x.h2 || x.t2) && (!x.h2 || x.h) &&
    (X.hasS || !(x.s1 || x.h || x.h2)) && (X.hasT || !x.t2)

def inFib (X : Src) (x : RS) : Prop := fibB X x = true

instance (X : Src) (x : RS) : Decidable (inFib X x) :=
  inferInstanceAs (Decidable (fibB X x = true))

def spec : Spec Src RS where
  P := inFib
  total X := by cases X <;> first | exact ⟨rS1, rfl⟩ | exact ⟨rT, rfl⟩

def RS.union (x y : RS) : RS := ⟨x.s1 || y.s1, x.h || y.h, x.h2 || y.h2, x.t2 || y.t2⟩

macro "rs_cases" x:ident : tactic =>
  `(tactic| (obtain ⟨b1, b2, b3, b4⟩ := $x:ident;
             cases b1 <;> cases b2 <;> cases b3 <;> cases b4))

/-- The fiber at `{s}` is the five route sets printed in panel (g). -/
theorem fiber_s (x : RS) :
    inFib .s x ↔ (x = rS1 ∨ x = rH ∨ x = rH2 ∨ x = rS1H ∨ x = rAll) := by
  rs_cases x <;> decide

/-- The fiber at `{s,t}` is the eleven route sets printed in panel (g). -/
theorem fiber_st (x : RS) :
    inFib .st x ↔ (x = rS1 ∨ x = rH ∨ x = rH2 ∨ x = rS1H ∨ x = rAll ∨ x = rT ∨
      x = rS1T ∨ x = rHT ∨ x = rH2T ∨ x = rS1HT ∨ x = rAllT) := by
  rs_cases x <;> decide

/-- The fibers grow with the input: a route set permitted at `X` is permitted
at every `Y ⪰ X`. -/
theorem fib_mono {X Y : Src} (x : RS) (hXY : X ≼ Y) (hx : inFib X x) : inFib Y x := by
  revert hXY hx; cases X <;> cases Y <;> rs_cases x <;> decide

/-- The union of two route sets of a fiber is in the fiber and extends both. -/
theorem union_mem (X : Src) (x y : RS) (hx : inFib X x) (hy : inFib X y) :
    inFib X (x.union y) ∧ x ≼ x.union y ∧ y ≼ x.union y := by
  revert hx hy; cases X <;> (rs_cases x) <;> (rs_cases y) <;> decide

theorem canonR (i k : Src) (x : RS) : (canon spec i).R k x ↔ (inFib k x ∧ i ≼ k) :=
  Iff.rfl

theorem sR1 : (canon spec .s).R .s rS1 := ⟨rfl, rfl⟩

/-- Panel (g): after `output({s→s1})` at `{s}` the rows that remain (shaded)
are, at both `{s}` and `{s,t}`, the route sets containing `s→s1`. -/
theorem after_s1 (k : Src) (x : RS) :
    outputTable (canon spec .s) rS1 k x ↔
      ((k = .s ∨ k = .st) ∧ (x = rS1 ∨ x = rS1H ∨ x = rAll)) ∨
        (k = .st ∧ (x = rS1T ∨ x = rS1HT ∨ x = rAllT)) := by
  show (inFib k x ∧ Src.s ≼ k) ∧ rS1 ≼ x ↔ _
  cases k <;> rs_cases x <;> decide

/-- Panel (g): the removed rows (gray) are `{s→h}` and `{s→h,s→h→s2}` at both
inputs, and, at `{s,t}`, the three route sets that add `t→s2` to `∅`, `{s→h}`
or `{s→h,s→h→s2}`. -/
theorem removed (k : Src) (x : RS) :
    ((canon spec .s).R k x ∧ ¬ outputTable (canon spec .s) rS1 k x) ↔
      ((k = .s ∨ k = .st) ∧ (x = rH ∨ x = rH2)) ∨
        (k = .st ∧ (x = rT ∨ x = rHT ∨ x = rH2T)) := by
  show (inFib k x ∧ Src.s ≼ k) ∧ ¬ ((inFib k x ∧ Src.s ≼ k) ∧ rS1 ≼ x) ↔ _
  cases k <;> rs_cases x <;> decide

/-- `{s→s1}` is a legal output at `{s}`: every removed row, at either input,
is extended by a remaining one at its input (`{s→s1,s→h,s→h→s2}` at `{s}`,
`{s→s1,s→h,s→h→s2,t→s2}` at `{s,t}`). -/
theorem exposable : Exposable (canon spec .s) rS1 := by
  intro k x hx _
  cases k with
  | s =>
    refine ⟨rAll, ⟨rfl, hx.2⟩, by decide, ?_⟩
    have h1 : inFib .s x := hx.1; revert h1; rs_cases x <;> decide
  | t => exact absurd hx.2 (fun h => nomatch h)
  | st =>
    refine ⟨rAllT, ⟨rfl, hx.2⟩, by decide, ?_⟩
    rs_cases x <;> decide

/-- Panel (g)'s footnote: every removed row is an output subsumption, and
nothing is excluded, so `{s→s1}` is a legal output. -/
theorem removed_subsumed :
    (∀ k x, (canon spec .s).R k x → ¬ rS1 ≼ x → Subsumed (canon spec .s) rS1 k x) ∧
      (¬ ∃ k x, Excluded (canon spec .s) rS1 k x) ∧ Exposable (canon spec .s) rS1 :=
  ⟨fun k x hx hn => ⟨hx, hn, exposable k x hx hn⟩,
    (exposable_iff_empty _ _).1 exposable, exposable⟩

/-- The state of panel (g). -/
def stateG : State spec := outState (canon spec .s) rS1 sR1

theorem stG_st : stateG.R .st rS1 := ⟨⟨rfl, rfl⟩, PO.refl _⟩

/-- The state of panel (h): after `input({s,t})` from panel (g). -/
def stateH : State spec := CALM.inputState stateG .st rS1 stG_st

/-- Panel (h): `input({s,t})` is a legal input event from panel (g); the rows
that remain are the six route sets at `{s,t}` that contain `s→s1`, so the
emitted `{s→s1}` keeps output extensions at the new input. -/
theorem after_input :
    Step stateG (.input .st) stateH ∧
      ∀ k x, stateH.R k x ↔
        (k = .st ∧ (x = rS1 ∨ x = rS1H ∨ x = rAll ∨ x = rS1T ∨ x = rS1HT ∨ x = rAllT)) := by
  refine ⟨Step.input _ _ _ ⟨rS1, stG_st⟩ rfl rfl, fun k x => ?_⟩
  show ((inFib k x ∧ Src.s ≼ k) ∧ rS1 ≼ x) ∧ Src.st ≼ k ↔ _
  cases k <;> rs_cases x <;> decide

/-- Directedness inside one fiber, with a seed: a finite list of route sets of
the fiber at `X` and one more have a common extension there. -/
theorem key (X : Src) : ∀ L : List RS, (∀ x ∈ L, inFib X x) → ∀ x0, inFib X x0 →
    ∃ u, inFib X u ∧ x0 ≼ u ∧ ∀ x ∈ L, x ≼ u := by
  intro L
  induction L with
  | nil => exact fun _ x0 h0 => ⟨x0, h0, PO.refl _, by simp⟩
  | cons y ys ih =>
    intro hL x0 h0
    obtain ⟨u, hu, h0u, hys⟩ := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) x0 h0
    obtain ⟨hm, h1, h2⟩ := union_mem X u y hu (hL y List.mem_cons_self)
    refine ⟨u.union y, hm, PO.trans h0u h1, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h2
    · exact PO.trans (hys x hx) h1

/-- The traceroute spec satisfies Lifted Monotonicity: route sets permitted at
`X` stay permitted at every `Y ⪰ X`, and finitely many of them have their
union as a common extension there. -/
theorem liftedMono : spec.LiftedMono := by
  intro i j hij L hne hL
  cases L with
  | nil => exact absurd rfl hne
  | cons y ys =>
    obtain ⟨u, hu, hyu, hys⟩ := key j ys
      (fun x hx => fib_mono x hij (hL x (List.mem_cons_of_mem _ hx))) y
      (fib_mono y hij (hL y List.mem_cons_self))
    refine ⟨u, hu, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hyu
    · exact hys x hx

/-- "The traceroute fibers are directed", Relational Monotonicity ("every
route set permitted at `{s}` is still permitted at `{s,t}`"), Lifted
Monotonicity and consistency. -/
theorem directed :
    spec.DirectedOutputs ∧ spec.RelMono ∧ spec.LiftedMono ∧ spec.Consistent :=
  ⟨fun i => liftedMono i i (PO.refl i),
    fun _ _ o hij ho => ⟨o, fib_mono o hij ho, PO.refl o⟩,
    liftedMono, (complete_calm spec).2 liftedMono⟩

/-- Common extension: a route set traced from `s` and one traced from `t`
have their union as a common output extension at `{s,t}`. -/
theorem common_extension (x y : RS) (hx : inFib .s x) (hy : inFib .t y) :
    inFib .st (x.union y) ∧ x ≼ x.union y ∧ y ≼ x.union y :=
  union_mem .st x y (fib_mono x (by decide) hx) (fib_mono y (by decide) hy)

/-- The concrete instance in the text: `{s→s1}` is permitted at `{s}`,
`{t→s2}` at `{t}`, and `{s→s1, t→s2}` is permitted at `{s,t}` and extends
both. -/
theorem common_extension_example :
    inFib .s rS1 ∧ inFib .t rT ∧ inFib .st rS1T ∧ rS1 ≼ rS1T ∧ rT ≼ rS1T ∧
      rS1.union rT = rS1T := by
  decide

/-- After Cor. `cor:convergence`: a run at `{s}` that emitted `{s→s1}` and a
run at `{s}` that emitted nothing reach the same input in different states;
the first has subsumed `{s→h}`, the second keeps it. -/
theorem state_depends_on_outputs :
    IsRun stateG ∧ IsRun (canon spec .s) ∧ stateG.cur = (canon spec .s).cur ∧
      ¬ stateG.R .s rH ∧ (canon spec .s).R .s rH ∧ stateG ≠ canon spec .s := by
  have hn : ¬ stateG.R .s rH := fun h => absurd (h.2 : rS1 ≼ rH) (by decide)
  have hc : (canon spec .s).R .s rH := ⟨rfl, rfl⟩
  refine ⟨⟨.s, _, Exec.cons (Step.output _ stateG _ sR1 rfl rfl) (Exec.nil _)⟩,
    ⟨.s, [], Exec.nil _⟩, rfl, hn, hc, fun he => hn (by rw [he]; exact hc)⟩

end Trace

end Figures
end CC
