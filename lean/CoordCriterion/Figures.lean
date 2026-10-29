import CoordCriterion.CALM.Examples
import CoordCriterion.Distributed.Systems

/-!
# Figure tables of Sections 2–3 and the discussion

* Fig. `fig:election-frames`, panel (d) "(b), then polls closed", with the
  registrar's seal (`closePolls`, a commitment in the sense of
  Def. `def:commitment`), the claims of Sec. `sec:election-story` and
  Sec. `sec:functional-events` about it, and the printed rows and upper
  fibers of panels (a)–(d) (`Elec.*`).  The figure prints exactly the rows
  whose input ⪰ `x··`, as its caption says (`Elec.printed_complete`).
* Fig. `fig:ambiguity-frames`(f), transaction ordering (`Txn.*`), and (g),
  traceroute (`Trace.*`), as printed (one input; the rows at it), with the
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
    (canon sp i).R k u ↔ (sp.S k u ∧ i ≼ k) := Iff.rfl

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
removes a row keeps none, so Eq. `commitment-excludes` holds vacuously. -/
noncomputable def closePolls : Commitment sp where
  app := closeApp
  cur_eq σ τ h := by obtain ⟨_, rfl⟩ := closeApp_eq.1 h; rfl
  sub σ τ h k u hu := by obtain ⟨_, rfl⟩ := closeApp_eq.1 h; exact hu.1
  removes σ τ h := by
    obtain ⟨⟨k, u, hu, hk⟩, rfl⟩ := closeApp_eq.1 h
    exact ⟨k, u, hu, fun h' => hk h'.2⟩
  excludes σ τ h k u w hu hnu hw := by
    obtain ⟨_, rfl⟩ := closeApp_eq.1 h
    exact absurd ⟨hu, hw.2⟩ hnu

/-- It is a seal: at every input where it removes a row, it removes all rows. -/
theorem closePolls_seals {σ τ : State sp} (h : (closePolls (sp := sp)).app σ = some τ)
    (k : I) (hk : ∃ u, σ.R k u ∧ ¬ τ.R k u) : ∀ w, ¬ τ.R k w := by
  obtain ⟨_, rfl⟩ := closeApp_eq.1 h
  obtain ⟨u, hu, hnu⟩ := hk
  intro w hw
  exact hnu ⟨hu, hw.2⟩

end Close

/-! ## 1. Fig. `fig:election-frames` -/

namespace Elec
open CC.CALM

def bxyy : Ballots := ⟨some .x, some .y, some .y⟩   -- xyy
def bxxx : Ballots := ⟨some .x, some .x, some .x⟩   -- xxx
def bxxy : Ballots := ⟨some .x, some .x, some .y⟩   -- xxy
def bx_x : Ballots := ⟨some .x, none, some .x⟩      -- x·x
def bx_y : Ballots := ⟨some .x, none, some .y⟩      -- x·y

/-- The nine inputs printed in each panel, in order, with their outputs. -/
def printed : List (Ballots × Res) :=
  [(bxd, .bot), (bxy, .bot), (bxyx, .win .x), (bxyy, .win .y),
   (bxx, .win .x), (bxxx, .win .x), (bxxy, .win .x),
   (bx_x, .win .x), (bx_y, .bot)]

/-- The printed outputs are the election's: every printed pair is a row. -/
theorem printed_rows : ∀ r ∈ printed, elec.S r.1 r.2 := by
  intro r hr
  simp only [printed, List.mem_cons, List.mem_nil_iff, or_false] at hr
  show r.2 = winner r.1
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Tactic helper: split a ballot into its 27 values. -/
macro "ballot_cases" k:ident : tactic =>
  `(tactic| (obtain ⟨b1, b2, b3⟩ := $k:ident;
             rcases b1 with _ | _ | _ <;> rcases b2 with _ | _ | _ <;>
             rcases b3 with _ | _ | _))

/-- The inputs `⪰ x··` are nine: the seven printed ones and `x·x`, `x·y`. -/
theorem shown_inputs (k : Ballots) :
    bxd ≼ k ↔ (k = bxd ∨ k = bxy ∨ k = bxyx ∨ k = bxyy ∨ k = bxx ∨ k = bxxx ∨ k = bxxy ∨
      k = bx_x ∨ k = bx_y) := by
  ballot_cases k <;> decide

/-- The figure prints exactly the rows whose input `⪰ x··`: a pair is printed
iff it is a row of the election at such an input. -/
theorem printed_complete (k : Ballots) (o : Res) :
    (k, o) ∈ printed ↔ (bxd ≼ k ∧ elec.S k o) := by
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

/-- Upper fibers of panels (a) and (b): `{⊥, x, y}`. -/
theorem upper_ab (o : Res) :
    (∃ k, (canon elec bxd).R k o) ∧ (∃ k, (canon elec bxy).R k o) := by
  rcases o with _ | ⟨_ | _⟩
  · exact ⟨⟨bxd, (by decide : Res.bot = winner bxd), PO.refl _⟩,
      ⟨bxy, (by decide : Res.bot = winner bxy), PO.refl _⟩⟩
  · exact ⟨⟨bxx, (by decide : Res.win .x = winner bxx), by decide⟩,
      ⟨bxyx, (by decide : Res.win .x = winner bxyx), by decide⟩⟩
  · exact ⟨⟨bxyy, (by decide : Res.win .y = winner bxyy), by decide⟩,
      ⟨bxyy, (by decide : Res.win .y = winner bxyy), by decide⟩⟩

/-- Upper fiber of panel (c): `{x}`. -/
theorem upper_c (o : Res) : (∃ k, (canon elec bxx).R k o) ↔ o = .win .x := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨o', ho'⟩ := elec_panel_c_determined
    exact (ho' k o hk).trans ((ho' bxx (.win .x) ⟨(by decide : Res.win .x = winner bxx),
      PO.refl _⟩).symm)
  · rintro rfl; exact ⟨bxx, (by decide : Res.win .x = winner bxx), PO.refl _⟩

/-- Panel (b): the rows at printed inputs that remain are exactly
`(xy·,⊥)`, `(xyx,x)`, `(xyy,y)`; the other printed rows are retired by
`input(xy·)` (their input does not expand `xy·`). -/
theorem panel_b (k : Ballots) (o : Res) (hk : bxd ≼ k) :
    ((canon elec bxy).R k o ↔
      ((k = bxy ∧ o = .bot) ∨ (k = bxyx ∧ o = .win .x) ∨ (k = bxyy ∧ o = .win .y))) ∧
    (elec.S k o → ¬ (canon elec bxy).R k o → ¬ bxy ≼ k) := by
  rw [canon_R]
  show ((o = winner k ∧ bxy ≼ k) ↔ _) ∧ (o = winner k → ¬ (o = winner k ∧ bxy ≼ k) → _)
  revert hk
  ballot_cases k <;> rcases o with _ | ⟨_ | _⟩ <;> decide

/-! ### Panel (d): (b), then polls closed -/

/-- The state of panel (d). -/
noncomputable def panelD : State elec := closeState (canon elec bxy)

/-- Closing the polls is defined at panel (b) (the row `(xyx, x)` is at
another input) and yields panel (d). -/
theorem close_at_b : (closePolls (sp := elec)).app (canon elec bxy) = some panelD :=
  closeApp_eq.2 ⟨⟨bxyx, .win .x, ⟨(by decide : Res.win .x = winner bxyx), by decide⟩,
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

/-- Panel (d)'s remainder table is the single row `(xy·, ⊥)`. -/
theorem panelD_rows (k : Ballots) (o : Res) : panelD.R k o ↔ (k = bxy ∧ o = .bot) := by
  constructor
  · rintro ⟨⟨hS, _⟩, rfl⟩
    exact ⟨rfl, hS.trans (by decide)⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨(by decide : Res.bot = winner bxy), PO.refl _⟩, rfl⟩

theorem panelD_cur : panelD.cur = bxy := rfl

/-- "Upper fiber `{⊥}`; determined; `⊥` is the result." -/
theorem panelD_determined : Determined panelD ∧ ∀ k x, panelD.R k x → x = .bot :=
  ⟨⟨.bot, fun k x h => ((panelD_rows k x).1 h).2⟩, fun k x h => ((panelD_rows k x).1 h).2⟩

/-- The seal removes exactly the still-possible rows `(xyx, x)` and `(xyy, y)`
(struck through), and these inputs are legal at (b) and expand the current
input: input alone would not have removed them. -/
theorem panelD_struck (k : Ballots) (o : Res) :
    ((canon elec bxy).R k o ∧ ¬ panelD.R k o) ↔
      ((k = bxyx ∧ o = .win .x) ∨ (k = bxyy ∧ o = .win .y)) := by
  rw [canon_R, panelD_rows]
  show ((o = winner k ∧ bxy ≼ k) ∧ ¬ (k = bxy ∧ o = .bot)) ↔ _
  ballot_cases k <;> rcases o with _ | ⟨_ | _⟩ <;> decide

/-- The printed gray-only rows of (d) are those retired by `input(xy·)`;
the current input is unchanged by the seal. -/
theorem panelD_gray (k : Ballots) (o : Res) (hk : bxd ≼ k) (hS : elec.S k o) :
    ¬ panelD.R k o ↔ (¬ bxy ≼ k ∨ (k = bxyx ∧ o = .win .x) ∨ (k = bxyy ∧ o = .win .y)) := by
  rw [panelD_rows]
  have hS' : o = winner k := hS
  subst hS'
  revert hk
  ballot_cases k <;> decide

/-- The registrar's output event: `Out_{[closePolls]}(⊥)` at (b) is legal (under
any basis containing `closePolls`) and ends at panel (d). -/
theorem registrar_step (B : Basis elec) (hB : B closePolls) :
    SysStep B (canon elec bxy) (.output [closePolls] .bot) panelD := by
  refine SysStep.output (fun c hc => by simp at hc; subst hc; exact hB)
    (ApplySeq.cons close_at_b (ApplySeq.nil _)) ((panelD_rows _ _).2 ⟨rfl, rfl⟩) ?_ rfl ?_
  · intro k x _ hx; exact absurd (Or.inl rfl) hx
  · funext k x; apply propext
    exact ⟨fun h => ⟨h, Or.inl rfl⟩, fun h => h.1⟩

/-- "Emitting `⊥` by itself would need no commitment": at (b), `⊥` is
exposable, `Sealed_⊥` and `Rejected_⊥` are empty, and `output(⊥)` removes no
row; so the seal is not required by the output. -/
theorem bot_alone_at_b :
    Exposable (canon elec bxy) .bot ∧ (¬ ∃ k x, Sealed (canon elec bxy) .bot k x) ∧
      (¬ ∃ k x, Rejected (canon elec bxy) .bot k x) ∧
      outputTable (canon elec bxy) .bot = (canon elec bxy).R := by
  have he := elec_panels_exposable.2.1
  refine ⟨he, (exposable_iff_empty _ _).1 he |>.1, (exposable_iff_empty _ _).1 he |>.2, ?_⟩
  funext k x; apply propext
  exact ⟨fun h => h.1, fun h => ⟨h, Or.inl rfl⟩⟩

/-- Fig. `fig:nonmonotone-frame`: "the table matches Fig. (d)": panel (d)'s
remainder table is that of `output(⊥)` at (b) under the equality order. -/
theorem panelD_matches_e (k : Ballots) (r : Res) :
    panelD.R k r ↔ outputTable (canon elecEq bxy) ⟨.bot⟩ k ⟨r⟩ := by
  rw [panelD_rows, elecEq_bot_single_row]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by rw [h2]⟩, fun ⟨h1, h2⟩ => ⟨h1, by cases h2; rfl⟩⟩

/-- "Extra commitments only restrict behavior": the registrar's run has an
observably equivalent run of the transition system (`input`/`output` events),
whose table contains panel (d)'s. -/
theorem registrar_canonical (B : Basis elec) (hB : B closePolls) :
    ∃ ρ', Exec (canon elec bxy) [.output .bot] ρ' ∧ ρ'.cur = bxy ∧
      ∀ k u, panelD.R k u → ρ'.R k u := by
  obtain ⟨_, ρ', _, _, hx, hc, hsub⟩ :=
    canonical_equivalent (SysExec.cons (registrar_step B hB) (SysExec.nil _))
  exact ⟨ρ', hx, hc, hsub⟩

/-! ### Sec. `sec:discussion`: decisive ballot vs. closing the polls -/

/-- Fill missing ballots with `x`. -/
def fillX (i : Ballots) : Ballots :=
  ⟨some (i.b1.getD .x), some (i.b2.getD .x), some (i.b3.getD .x)⟩

theorem fillX_spec (i : Ballots) : i ≼ fillX i ∧ (winner i = .bot → winner (fillX i) = .win .x) := by
  ballot_cases i <;> decide

/-- A determined canonical state of the election has a winner. -/
theorem determined_has_winner (i : Ballots) (h : Determined (canon elec i)) : winner i ≠ .bot := by
  intro hb
  obtain ⟨o, ho⟩ := h
  have h1 := ho i (winner i) ⟨rfl, PO.refl _⟩
  have h2 := ho (fillX i) (winner (fillX i)) ⟨rfl, (fillX_spec i).1⟩
  rw [(fillX_spec i).2 hb] at h2; rw [hb] at h1
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
(`input(xx·)` at panel (a)) reaches a determined state and every row it
removes is retired by input (its input no longer expands the current input).
(2) Closing the polls at (b) reaches a determined state and every row it
removes is at a legal input expanding the current one (a commitment).
(3) The results differ: in the election, closing the polls at any
undetermined canonical state leaves the single result `⊥`, while every
determined canonical state has a winner. -/
theorem decisive_vs_close :
    (Step (canon elec bxd) (.input bxx) (canon elec bxx) ∧ Determined (canon elec bxx) ∧
      ∀ k u, (canon elec bxd).R k u → ¬ (canon elec bxx).R k u → ¬ bxx ≼ k) ∧
    (Determined panelD ∧ ∀ k u, (canon elec bxy).R k u → ¬ panelD.R k u →
      bxy ≼ k ∧ k ≠ bxy) ∧
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
    · refine ⟨fillX i, winner (fillX i), ⟨rfl, (fillX_spec i).1⟩, fun he => ?_⟩
      show False
      have : winner i = .win .x := by
        have e : fillX i = i := he
        rw [← e]; exact (fillX_spec i).2 hb
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
  antisymm h _ := h

def spec : Spec Unit TOut where
  S _ _ := True
  total _ := ⟨.ab, trivial⟩

theorem le_iff (a b : TOut) : a ≼ b ↔ a = b := Iff.rfl

theorem sR (o : TOut) : (canon spec ()).R () o := ⟨trivial, trivial⟩

/-- After `output([A,B])` only the row `({A,B}, [A,B])` remains. -/
theorem after_ab (k : Unit) (o : TOut) : outputTable (canon spec ()) .ab k o ↔ o = .ab :=
  ⟨fun h => h.2.symm, fun h => ⟨sR o, h.symm⟩⟩

/-- "No remaining row refines the removed one": the row `[B,A]` is in
`Rejected_o` (a choice), not sealed (the input keeps `[A,B]`) and not retired
(no row refines both). -/
theorem ba_rejected :
    Rejected (canon spec ()) .ab () .ba ∧ ¬ Sealed (canon spec ()) .ab () .ba ∧
      ¬ Retired (canon spec ()) .ab () .ba ∧
      ¬ ∃ u, spec.S () u ∧ TOut.ab ≼ u ∧ TOut.ba ≼ u := by
  have hns : ¬ Sealed (canon spec ()) .ab () .ba := fun h => h.2 ⟨.ab, sR _, rfl⟩
  have hnr : ¬ Retired (canon spec ()) .ab () .ba := by
    rintro ⟨_, _, u, _, h1, h2⟩
    exact TOut.noConfusion (h1.trans h2.symm)
  refine ⟨⟨sR _, fun h => TOut.noConfusion h, hns, hnr⟩, hns, hnr, ?_⟩
  rintro ⟨u, _, h1, h2⟩
  exact TOut.noConfusion (h1.trans h2.symm)

/-- Emitting `[A,B]` is not exposable: it requires a commitment, and every
legal system output event emitting it carries one. -/
theorem ab_not_exposable : ¬ Exposable (canon spec ()) .ab ∧
    ∀ (B : Basis spec) (γ : List (Commitment spec)) τ,
      SysStep B (canon spec ()) (.output γ .ab) τ → γ ≠ [] := by
  refine ⟨fun h => ((exposable_iff_empty _ _).1 h).2 ⟨(), .ba, ba_rejected.1⟩, ?_⟩
  intro B γ τ h
  exact containment_nonempty h ⟨(), .ba, Or.inr ba_rejected.1⟩

/-- The choice `c_[A,B]` applies at `{A,B}`; it removes `[B,A]` while the
input stays legal (the row `[A,B]` remains). -/
theorem choice_applies :
    (choiceC (sp := spec) .ab).app (canon spec ()) = some (cmChooseState (canon spec ()) .ab) ∧
      (cmChooseState (canon spec ()) .ab).R () .ab ∧
      ¬ (cmChooseState (canon spec ()) .ab).R () .ba :=
  ⟨chooseApp_eq.2 ⟨sR _, ⟨(), .ba, ba_rejected.1⟩, rfl⟩,
   ⟨sR _, not_rejected_of_ge (PO.refl _)⟩, fun h => h.2 ba_rejected.1⟩

/-- The two orders are incompatible: not directed, not monotone, not
consistent. -/
theorem not_monotone :
    ¬ CompatibleIn (spec.S ()) [.ab, .ba] ∧ ¬ spec.DirectedOutputs ∧ ¬ spec.LiftedMono ∧
      ¬ spec.Consistent := by
  have hc : ¬ CompatibleIn (spec.S ()) [.ab, .ba] := by
    rintro ⟨u, hu, hall⟩
    exact ba_rejected.2.2.2 ⟨u, hu, hall _ (by simp), hall _ (by simp)⟩
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
  exact ba_rejected.2.2.2 ⟨u, hu, (hall (outState (canon spec ()) .ab (sR _)) (by simp)).2,
    (hall (outState (canon spec ()) .ba (sR _)) (by simp)).2⟩

end Txn

/-! ## 3. Fig. `fig:ambiguity-frames`(g): traceroute

One input `i` (`Unit`); outputs are sets of the three routes
`s→s1`, `s→a`, `s→a→s2` (a `Bool` per route), ordered by inclusion; the fiber
is the five printed route sets. -/

namespace Trace

structure RS where
  s1 : Bool
  a : Bool
  a2 : Bool
  deriving DecidableEq

abbrev RS.sub (x y : RS) : Prop :=
  (x.s1 = true → y.s1 = true) ∧ (x.a = true → y.a = true) ∧ (x.a2 = true → y.a2 = true)

instance : PO RS where
  le := RS.sub
  refl _ := ⟨id, id, id⟩
  trans h1 h2 := ⟨h2.1 ∘ h1.1, h2.2.1 ∘ h1.2.1, h2.2.2 ∘ h1.2.2⟩
  antisymm {x y} h1 h2 := by
    obtain ⟨a, b, c⟩ := x; obtain ⟨d, e, f⟩ := y
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
      simp_all [RS.sub]

instance (x y : RS) : Decidable (x ≼ y) := inferInstanceAs (Decidable (RS.sub x y))

def rS1 : RS := ⟨true, false, false⟩      -- {s→s1}
def rA : RS := ⟨false, true, false⟩       -- {s→a}
def rA2 : RS := ⟨false, true, true⟩       -- {s→a, s→a→s2}
def rS1A : RS := ⟨true, true, false⟩      -- {s→s1, s→a}
def rAll : RS := ⟨true, true, true⟩       -- {s→s1, s→a, s→a→s2}

def inFib (x : RS) : Prop := x = rS1 ∨ x = rA ∨ x = rA2 ∨ x = rS1A ∨ x = rAll

instance (x : RS) : Decidable (inFib x) := inferInstanceAs (Decidable (_ ∨ _))

def spec : Spec Unit RS where
  S _ x := inFib x
  total _ := ⟨rS1, Or.inl rfl⟩

def RS.union (x y : RS) : RS := ⟨x.s1 || y.s1, x.a || y.a, x.a2 || y.a2⟩

macro "rs_cases" x:ident : tactic =>
  `(tactic| (obtain ⟨b1, b2, b3⟩ := $x:ident; cases b1 <;> cases b2 <;> cases b3))

/-- The union of two route sets of the fiber is in the fiber and refines both. -/
theorem union_mem (x y : RS) (hx : inFib x) (hy : inFib y) :
    inFib (x.union y) ∧ x ≼ x.union y ∧ y ≼ x.union y := by
  revert hx hy; rs_cases x <;> (rs_cases y) <;> decide

theorem canonR (x : RS) : (canon spec ()).R () x ↔ inFib x :=
  ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- After `output({s→s1})` the rows `{s→s1}`, `{s→s1,s→a}`,
`{s→s1,s→a,s→a→s2}` remain (shaded). -/
theorem after_s1 (x : RS) :
    outputTable (canon spec ()) rS1 () x ↔ (x = rS1 ∨ x = rS1A ∨ x = rAll) := by
  show (inFib x ∧ True) ∧ rS1 ≼ x ↔ _
  rs_cases x <;> decide

/-- The two removed rows `{s→a}` and `{s→a, s→a→s2}` are output retirements,
each refined by the remaining `{s→s1,s→a,s→a→s2}`; nothing is sealed or
rejected, so `{s→s1}` is exposable. -/
theorem removed_retired :
    (∀ x, (canon spec ()).R () x → (¬ outputTable (canon spec ()) rS1 () x ↔ (x = rA ∨ x = rA2))) ∧
    Retired (canon spec ()) rS1 () rA ∧ Retired (canon spec ()) rS1 () rA2 ∧
    (¬ ∃ k x, Sealed (canon spec ()) rS1 k x) ∧ (¬ ∃ k x, Rejected (canon spec ()) rS1 k x) ∧
    Exposable (canon spec ()) rS1 := by
  have hall : (canon spec ()).R () rAll := (canonR _).2 (by decide)
  have hexp : Exposable (canon spec ()) rS1 := by
    intro k x hx _
    cases k
    exact ⟨rAll, hall, by decide, by have := (canonR x).1 hx; revert this; rs_cases x <;> decide⟩
  obtain ⟨hS, hJ⟩ := (exposable_iff_empty _ _).1 hexp
  refine ⟨?_, ⟨(canonR _).2 (by decide), by decide, rAll, hall, by decide, by decide⟩,
    ⟨(canonR _).2 (by decide), by decide, rAll, hall, by decide, by decide⟩, hS, hJ, hexp⟩
  intro x hx
  rw [after_s1]
  have := (canonR x).1 hx
  revert this; rs_cases x <;> decide

/-- "The traceroute fiber is directed": every nonempty finite set of route
sets in it has a common refinement in it (its union). -/
theorem directed : spec.DirectedOutputs ∧ spec.LiftedMono ∧ spec.Consistent := by
  have key : ∀ X : List RS, (∀ x ∈ X, inFib x) → ∀ x0, inFib x0 →
      ∃ u, inFib u ∧ x0 ≼ u ∧ ∀ x ∈ X, x ≼ u := by
    intro X
    induction X with
    | nil => exact fun _ x0 h0 => ⟨x0, h0, PO.refl _, by simp⟩
    | cons y ys ih =>
      intro hX x0 h0
      obtain ⟨u, hu, h0u, hys⟩ := ih (fun x hx => hX x (List.mem_cons_of_mem _ hx)) x0 h0
      obtain ⟨hm, h1, h2⟩ := union_mem u y hu (hX y List.mem_cons_self)
      refine ⟨u.union y, hm, PO.trans h0u h1, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h2
      · exact PO.trans (hys x hx) h1
  have hd : spec.DirectedOutputs := by
    intro i X hne hX
    cases X with
    | nil => exact absurd rfl hne
    | cons y ys =>
      obtain ⟨u, hu, hyu, hys⟩ := key ys (fun x hx => hX x (List.mem_cons_of_mem _ hx)) y
        (hX y List.mem_cons_self)
      refine ⟨u, hu, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hyu
      · exact hys x hx
  have hl : spec.LiftedMono := fun i j _ => by cases i; cases j; exact hd ()
  exact ⟨hd, hl, (complete_calm spec).2 hl⟩

/-- "Two traceroute runs that emit different route sets pass it, since their
union survives in both." -/
theorem union_survives (x y : RS) (hx : inFib x) (hy : inFib y) :
    (outState (canon spec ()) x ((canonR x).2 hx)).R () (x.union y) ∧
    (outState (canon spec ()) y ((canonR y).2 hy)).R () (x.union y) := by
  obtain ⟨hm, h1, h2⟩ := union_mem x y hx hy
  exact ⟨⟨(canonR _).2 hm, h1⟩, ⟨(canonR _).2 hm, h2⟩⟩

/-- Remark after Prop. `prop:exposure-boundary`: a run that emitted
`{s→s1}` and a run that emitted nothing reach the same input in different
states; the first has retired `{s→a}`, the second keeps it. -/
theorem state_depends_on_outputs :
    IsRun (outState (canon spec ()) rS1 ((canonR _).2 (by decide))) ∧ IsRun (canon spec ()) ∧
    (outState (canon spec ()) rS1 ((canonR _).2 (by decide))).cur = (canon spec ()).cur ∧
    ¬ (outState (canon spec ()) rS1 ((canonR _).2 (by decide))).R () rA ∧
    (canon spec ()).R () rA ∧
    outState (canon spec ()) rS1 ((canonR _).2 (by decide)) ≠ canon spec () := by
  have hn : ¬ (outState (canon spec ()) rS1 ((canonR _).2 (by decide))).R () rA :=
    fun h => absurd h.2 (by decide)
  have hc : (canon spec ()).R () rA := (canonR _).2 (by decide)
  refine ⟨⟨(), _, Exec.cons (Step.output _ (outState _ _ _) _ ((canonR _).2 (by decide)) rfl rfl)
    (Exec.nil _)⟩, ⟨(), [], Exec.nil _⟩, rfl, hn, hc, fun he => hn (by rw [he]; exact hc)⟩

end Trace

end Figures
end CC
