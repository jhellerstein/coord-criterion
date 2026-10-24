/-
# Audit R: remaining checkable claims

1. **Figure tables.**
   * Fig. `fig:election-frames`, panel (d) "(b), then polls closed", with the
     registrar's seal (`closePolls`, a commitment in the sense of
     Def. `def:commitment`), the claims of Sec. `sec:election-story` and
     Sec. `sec:functional-events` about it, and the printed rows and upper
     fibers of panels (a)–(d) (`Elec.*`).  The figure caption says "only rows
     whose input ⪰ `x··` are shown", but `x·x` and `x·y` are such inputs and
     are not printed (`Elec.shown_inputs`, `Elec.unprinted_rows`).
   * Sec. `sec:discussion`, "Receiving a decisive ballot and closing the polls
     can leave the same result": both leave a determined state, the first by
     input retirement, the second by a commitment; in the election the two
     never leave the *same* result, since closing the polls at an undetermined
     state always leaves `⊥` and every determined canonical state has a winner
     (`Elec.decisive_vs_close`).
   * Fig. `fig:ambiguity-frames`(f), transaction ordering (`Txn.*`), and (g),
     traceroute (`Trace.*`), as printed (one input; the rows at it), with the
     claims of Sec. `sec:ambiguity-story`, Sec. `sec:lifted-monotonicity`,
     Sec. `sec:lifted-output-events` and the remark after
     Prop. `prop:exposure-boundary`.
2. **Deployment remark** (App. `app:deployment`, after
   Prop. `thm:complete-cap-deployment`): for the runs of a *system*
   (`CC.CAP` local runs, with arbitrary commitments in output events), if the
   specification is monotone across partitions then every separable,
   authorized family of system runs has a common refinement in `S(j)` at every
   common expansion `j` (`system_monoAcross`), in particular the participant
   runs at a cut of a partitioned history (`history_monoAcross`).  Proved via
   `AuditB.sysStep_iff_CAP` and Lemma `canonical_equivalent`.  "It does not
   follow that the deployment authorizes any participant to emit `u`"
   (`unauthorized_refinement`).
3. **Invariant confluence** (Sec. `sec:iconfluence-instance`): Bailis et al.'s
   Def. 6 (I-T-reachability from a common ancestor state) is equivalent to
   `CC.IConf.Model.IConfluent` (`bailis_iff`, `bailisAnc_iff`,
   `reachPlus_iff`).
-/
import CoordCriterion.Core
import CoordCriterion.Runs
import CoordCriterion.CompleteCALM
import CoordCriterion.Commitments
import CoordCriterion.CompleteCAP
import CoordCriterion.Deployment
import CoordCriterion.IConfluence
import CoordCriterion.Audit.CALM
import CoordCriterion.Audit.Distributed

namespace CC
namespace AuditR

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
open CC.AuditA

def bxyy : Ballots := ⟨some .x, some .y, some .y⟩   -- xyy
def bxxx : Ballots := ⟨some .x, some .x, some .x⟩   -- xxx
def bxxy : Ballots := ⟨some .x, some .x, some .y⟩   -- xxy
def bx_x : Ballots := ⟨some .x, none, some .x⟩      -- x·x
def bx_y : Ballots := ⟨some .x, none, some .y⟩      -- x·y

/-- The seven inputs printed in each panel, in order, with their outputs. -/
def printed : List (Ballots × Res) :=
  [(bxd, .bot), (bxy, .bot), (bxyx, .win .x), (bxyy, .win .y),
   (bxx, .win .x), (bxxx, .win .x), (bxxy, .win .x)]

/-- The printed outputs are the election's: every printed pair is a row. -/
theorem printed_rows : ∀ r ∈ printed, elec.S r.1 r.2 := by
  intro r hr
  simp only [printed, List.mem_cons, List.mem_nil_iff, or_false] at hr
  show r.2 = winner r.1
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

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

/-- The rows `(x·x, x)` and `(x·y, ⊥)` are rows at inputs `⪰ x··` that the
figure does not print (not among the printed inputs). -/
theorem unprinted_rows :
    bxd ≼ bx_x ∧ bxd ≼ bx_y ∧ elec.S bx_x (.win .x) ∧ elec.S bx_y .bot ∧
      (∀ r ∈ printed, r.1 ≠ bx_x ∧ r.1 ≠ bx_y) := by
  refine ⟨by decide, by decide, (by decide : Res.win .x = winner bx_x),
    (by decide : Res.bot = winner bx_y), ?_⟩
  intro r hr
  simp only [printed, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

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
  refine ⟨⟨AuditB.step_canon_input elec (by decide) ⟨_, rfl⟩, elec_panel_c_determined, ?_⟩,
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

/-! ## 4. App. `app:deployment`: the proposition applies to the runs of a system

A system participant's run is a `CC.CAP` local run (`LRun`) from a canonical
state: input events, output events `out γ o` with arbitrary commitment
sequences `γ`, sends and receives.  Its emitted rows are the pairs
`(current input, o)` of its output events. -/

namespace DeployR
open CC.CAP (LEv LRun)
open CC.Deploy

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type} {m : Nat}

/-- Emitted rows along a local event list, from current input `c`. -/
def emittedL (c : I) : List (LEv sp D m) → List (I × O)
  | [] => []
  | .inp j :: es => emittedL j es
  | .out _ o :: es => (c, o) :: emittedL c es
  | .send _ _ :: es => emittedL c es
  | .recv _ _ _ _ :: es => emittedL c es

/-- The `Commitments` system events of a local event list (sends and receives
dropped, commitments transported by `AuditB.ofCAP`). -/
def toS : List (LEv sp D m) → List (SEvent sp)
  | [] => []
  | .inp j :: es => .input j :: toS es
  | .out γ o :: es => .output (γ.map AuditB.ofCAP) o :: toS es
  | .send _ _ :: es => toS es
  | .recv _ _ _ _ :: es => toS es

theorem map_ofCAP_toCAP (γ : List (CAP.Commitment sp)) :
    (γ.map AuditB.ofCAP).map AuditB.toCAP = γ := by
  induction γ with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, AuditB.toCAP_ofCAP]; exact congrArg _ ih

/-- A local run is an execution under the full basis (via
`AuditB.sysStep_iff_CAP`). -/
theorem lrun_sysExec {σ τ : State sp} {l : List (LEv sp D m)} (h : LRun σ l τ) :
    SysExec (fun _ => True) σ (toS l) τ := by
  induction h with
  | nil => exact SysExec.nil _
  | inp hs _ ih => exact SysExec.cons (SysStep.input hs) ih
  | @out σ σc τ ρ γ o es hγ hs hexp _ ih =>
    refine SysExec.cons (AuditB.sysStep_iff_CAP.2 ⟨fun _ _ => trivial, σc, ?_, hs, hexp⟩) ih
    rw [map_ofCAP_toCAP]; exact hγ
  | send _ ih => exact ih
  | recv _ ih => exact ih

theorem emitted_toS (c : I) (l : List (LEv sp D m)) :
    emitted c ((toS l).map SEvent.erase) = emittedL c l := by
  induction l generalizing c with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | inp j => exact ih j
    | out γ o => simp only [toS, List.map_cons, SEvent.erase, emitted, emittedL, ih]
    | send _ _ => exact ih c
    | recv _ _ _ _ => exact ih c

/-- A participant run of a system. -/
structure SRun (sp : Spec I O) (D : Type) (m : Nat) where
  init : I
  es : List (LEv sp D m)
  fin : State sp
  run : LRun (canon sp init) es fin

def SRun.rows (r : SRun sp D m) : List (I × O) := emittedL r.init r.es

/-- **Lemma `canonical-equivalent`, applied to a system run**: a canonical
run with the same emitted rows and the same current input. -/
theorem SRun.canonical (r : SRun sp D m) :
    ∃ q : PRun sp, q.rows = r.rows ∧ q.fin.cur = r.fin.cur := by
  obtain ⟨_, ρ', _, _, hx, hc, _⟩ := canonical_equivalent (lrun_sysExec r.run)
  exact ⟨⟨r.init, _, ρ', hx⟩, emitted_toS r.init r.es, hc⟩

noncomputable def SRun.toP (r : SRun sp D m) : PRun sp := Classical.choose r.canonical

theorem SRun.toP_rows (r : SRun sp D m) : r.toP.rows = r.rows :=
  (Classical.choose_spec r.canonical).1

theorem SRun.toP_cur (r : SRun sp D m) : r.toP.fin.cur = r.fin.cur :=
  (Classical.choose_spec r.canonical).2

variable {n : Nat}

/-- A family of system participant runs. -/
abbrev SFamily (sp : Spec I O) (D : Type) (m n : Nat) := Fin n → Option (SRun sp D m)

def SEmits (F : SFamily sp D m n) (p : Fin n) (r : I × O) : Prop :=
  ∃ s, F p = some s ∧ r ∈ s.rows

def SSilent (F : SFamily sp D m n) (q : Fin n) : Prop :=
  ∃ s, F q = some s ∧ s.rows = []

/-- Each run's emitted rows lie in its participant's `A_p`. -/
def SAuthorized (Dp : Deployment sp n) (F : SFamily sp D m n) : Prop :=
  ∀ p r, SEmits F p r → Dp.A p r.1 r.2

/-- Separable under `comp` (as Def. `def:deployment`). -/
def SSeparable (F : SFamily sp D m n) (comp : Fin n → Nat) : Prop :=
  (∃ p q r r', SEmits F p r ∧ SEmits F q r' ∧ comp p ≠ comp q) ∨
  (∃ r₀ p q, SEmits F p r₀ ∧ (∀ p' r, SEmits F p' r → r = r₀) ∧
     SSilent F q ∧ comp q ≠ comp p)

def SUB (F : SFamily sp D m n) (j : I) : Prop := ∀ p s, F p = some s → s.fin.cur ≼ j

noncomputable def SFamily.toF (F : SFamily sp D m n) : Family sp n := fun p => (F p).map SRun.toP

theorem toF_emits (F : SFamily sp D m n) (p : Fin n) (r : I × O) :
    Emits F.toF p r ↔ SEmits F p r := by
  unfold Emits SEmits SFamily.toF
  cases h : F p with
  | none => simp
  | some s =>
    simp only [Option.map_some, Option.some.injEq, exists_eq_left', SRun.toP_rows]

theorem toF_silent (F : SFamily sp D m n) (q : Fin n) : Silent F.toF q ↔ SSilent F q := by
  unfold Silent SSilent SFamily.toF
  cases h : F q with
  | none => simp
  | some s =>
    simp only [Option.map_some, Option.some.injEq, exists_eq_left', SRun.toP_rows]

/-- **The deployment remark, end to end.**  If the specification is monotone
across `comp` (under the deployment), then for every family of *system*
participant runs whose emitted rows lie in their participants' `A_p` and
which is separable under `comp`, and every common expansion `j` of the runs'
current inputs, some `u ∈ S(j)` refines every emitted output. -/
theorem system_monoAcross (Dp : Deployment sp n) {comp : Fin n → Nat}
    (hmono : MonoAcross Dp comp) (F : SFamily sp D m n) (ha : SAuthorized Dp F)
    (hs : SSeparable F comp) (j : I) (hj : SUB F j) :
    ∃ u, sp.S j u ∧ ∀ p r, SEmits F p r → r.2 ≼ u := by
  have ha' : Authorized Dp F.toF := fun p r h => ha p r ((toF_emits F p r).1 h)
  have hs' : Separable F.toF comp := by
    rcases hs with ⟨p, q, r, r', h1, h2, h3⟩ | ⟨r₀, p, q, h1, h2, h3, h4⟩
    · exact Or.inl ⟨p, q, r, r', (toF_emits F p r).2 h1, (toF_emits F q r').2 h2, h3⟩
    · exact Or.inr ⟨r₀, p, q, (toF_emits F p r₀).2 h1,
        fun p' r h => h2 p' r ((toF_emits F p' r).1 h), (toF_silent F q).2 h3, h4⟩
  have hj' : UB F.toF j := by
    intro p q hq
    unfold SFamily.toF at hq
    cases h : F p with
    | none => rw [h] at hq; cases hq
    | some s =>
      rw [h] at hq; cases hq
      rw [SRun.toP_cur]; exact hj p s h
  obtain ⟨u, hu, hall⟩ := hmono F.toF ha' hs' j hj'
  exact ⟨u, hu, fun p r h => hall p r ((toF_emits F p r).2 h)⟩

/-- The same for the participant runs at a cut of a partitioned history: the
runs of all participants to the cut, as Deployment Availability permits
(their emitted rows lie in `A_p`), separable under the history's partition. -/
theorem history_monoAcross (Dp : Deployment sp n) (hmono : MonoAcrossPartitions Dp)
    (init : Fin n → I) (H : CAP.History sp D n) (comp : Fin n → Nat)
    (hP : CAP.Partitioned H comp) (c : Fin n → Nat) (σ : Fin n → State sp)
    (hσ : ∀ p, LRun (canon sp (init p)) ((H p).take (c p)) (σ p))
    (hsep : SSeparable (fun p => some ⟨init p, (H p).take (c p), σ p, hσ p⟩) comp)
    (hauth : ∀ p r, r ∈ emittedL (init p) ((H p).take (c p)) → Dp.A p r.1 r.2)
    (j : I) (hj : ∀ p, (σ p).cur ≼ j) :
    ∃ u, sp.S j u ∧ ∀ p r, r ∈ emittedL (init p) ((H p).take (c p)) → r.2 ≼ u := by
  let F : SFamily sp D n n := fun p => some ⟨init p, (H p).take (c p), σ p, hσ p⟩
  have hF : ∀ p r, SEmits F p r ↔ r ∈ emittedL (init p) ((H p).take (c p)) := by
    intro p r
    exact ⟨fun ⟨s, hs, hr⟩ => by cases hs; exact hr, fun h => ⟨_, rfl, h⟩⟩
  obtain ⟨u, hu, hall⟩ := system_monoAcross Dp (hmono comp hP.1) F
    (fun p r h => hauth p r ((hF p r).1 h)) hsep j
    (fun p s hs => by cases hs; exact hj p)
  exact ⟨u, hu, fun p r h => hall p r ((hF p r).2 h)⟩

/-- "It does not follow that the deployment authorizes any participant to emit
`u`": with fiber `{a, b, top}` (`a, b ≤ top`), `A_0 = {a}`, `A_1 = {b}`, the
specification is monotone (hence monotone across partitions), the family
"`0` emits `a`, `1` emits `b`" is authorized and separable, and its only common
refinement `top` is authorized to no participant. -/
def triD : Deployment CAP.triSpec 2 where
  A p _ u := if p = 0 then u = .a else u = .b
  sub _ _ _ _ := trivial

theorem unauthorized_refinement :
    MonoAcrossPartitions triD ∧
    ∃ (F : Family CAP.triSpec 2) (comp : Fin 2 → Nat), IsPartition comp ∧
      Authorized triD F ∧ Separable F comp ∧ UB F () ∧
      (∀ u, (∀ p r, Emits F p r → r.2 ≼ u) → u = .top) ∧ ∀ p, ¬ triD.A p () .top := by
  let out : Fin 2 → CAP.Tri := fun p => if p = 0 then .a else .b
  let F : Family CAP.triSpec 2 := fun p => some (oneShot CAP.triSpec () (out p) trivial)
  have hE : ∀ p r, Emits F p r ↔ r = ((), out p) := by
    intro p r
    constructor
    · rintro ⟨m, hm, hr⟩
      cases hm
      exact List.mem_singleton.1 (show r ∈ [((), out p)] from hr)
    · rintro rfl; exact ⟨_, rfl, show ((), out p) ∈ [((), out p)] from List.mem_singleton_self _⟩
  refine ⟨monoAcrossPartitions_of_liftedMono CAP.triSpec_liftedMono triD, F, fun p => p.val,
    ⟨0, 1, by decide⟩, ?_, ?_, fun _ _ _ => trivial, ?_, ?_⟩
  · intro p r h
    rw [hE] at h; subst h
    show if p = 0 then out p = .a else out p = .b
    by_cases hp : p = 0 <;> simp [out, hp]
  · exact Or.inl ⟨0, 1, ((), .a), ((), .b), (hE _ _).2 rfl, (hE _ _).2 rfl, by decide⟩
  · intro u hu
    have h1 : CAP.Tri.a ≼ u := hu 0 _ ((hE _ _).2 rfl)
    have h2 : CAP.Tri.b ≼ u := hu 1 _ ((hE _ _).2 rfl)
    rcases h1 with h1 | h1
    · subst h1; rcases h2 with h2 | h2 <;> cases h2
    · exact h1
  · intro p h
    show False
    revert h
    show ¬ (if p = 0 then CAP.Tri.top = .a else CAP.Tri.top = .b)
    split <;> exact fun h => CAP.Tri.noConfusion h

end DeployR

/-! ## 5. Sec. `sec:iconfluence-instance`: Bailis et al.'s definition

Bailis et al. (VLDB 2015), Def. 5: a state is *I-T-reachable* from a state
`a` when some partially ordered sequence of transaction and merge invocations
starting from `a` yields it, every intermediate state being I-valid; Def. 6:
`T` is *I-confluent* when `Dᵢ ⊔ Dⱼ` is I-valid for all I-T-reachable states
`Dᵢ, Dⱼ` with a common ancestor state.  We formalize two readings of
"common ancestor" and show that both are `CC.IConf.Model.IConfluent`
("every reachable state descends from `s0`"). -/

namespace IConfR
open CC.IConf

variable {V Tx : Type} {M : Model V Tx}

/-- Bailis et al., Def. 5: I-T-reachability from `a`. -/
inductive ReachFrom (M : Model V Tx) (a : St V) : St V → Prop where
  | base : ReachFrom M a a
  | tx {s : St V} (t : Tx) : ReachFrom M a s → M.Inv (M.app t s) → ReachFrom M a (M.app t s)
  | merge {s₁ s₂ : St V} : ReachFrom M a s₁ → ReachFrom M a s₂ → M.Inv (s₁.union s₂) →
      ReachFrom M a (s₁.union s₂)

theorem reach_iff_from (s : St V) : IConf.Reach M s ↔ ReachFrom M M.s0 s := by
  constructor
  · intro h
    induction h with
    | init => exact .base
    | tx t _ hi ih => exact .tx t ih hi
    | merge _ _ hi ih1 ih2 => exact .merge ih1 ih2 hi
  · intro h
    induction h with
    | base => exact .init
    | tx t _ hi ih => exact .tx t ih hi
    | merge _ _ hi ih1 ih2 => exact .merge ih1 ih2 hi

/-- States reachable from a reachable state are reachable. -/
theorem reach_of_from {a s : St V} (ha : IConf.Reach M a) (h : ReachFrom M a s) : IConf.Reach M s := by
  induction h with
  | base => exact ha
  | tx t _ hi ih => exact .tx t ih hi
  | merge _ _ hi ih1 ih2 => exact .merge ih1 ih2 hi

/-- Def. 6, read with an explicit common ancestor state `a` (itself reachable
or initial): the merge of any two states I-T-reachable from `a` is I-valid. -/
def BailisIC (M : Model V Tx) : Prop :=
  ∀ a, IConf.Reach M a → ∀ s₁ s₂, ReachFrom M a s₁ → ReachFrom M a s₂ → M.Inv (s₁.union s₂)

theorem bailis_iff : BailisIC M ↔ M.IConfluent := by
  constructor
  · intro h s₁ s₂ h₁ h₂
    exact h M.s0 .init s₁ s₂ ((reach_iff_from _).1 h₁) ((reach_iff_from _).1 h₂)
  · intro h a ha s₁ s₂ h₁ h₂
    exact h s₁ s₂ (reach_of_from ha h₁) (reach_of_from ha h₂)

/-- `Anc a s`: `a` is an ancestor state of `s`, i.e. a state preceding `s` in
some derivation of `s` from `s0` by at least one invocation. -/
inductive Anc (M : Model V Tx) : St V → St V → Prop where
  | txParent {s : St V} (t : Tx) : IConf.Reach M s → M.Inv (M.app t s) → Anc M s (M.app t s)
  | tx {a s : St V} (t : Tx) : Anc M a s → M.Inv (M.app t s) → Anc M a (M.app t s)
  | mergeParentL {s₁ s₂ : St V} : IConf.Reach M s₁ → IConf.Reach M s₂ → M.Inv (s₁.union s₂) →
      Anc M s₁ (s₁.union s₂)
  | mergeParentR {s₁ s₂ : St V} : IConf.Reach M s₁ → IConf.Reach M s₂ → M.Inv (s₁.union s₂) →
      Anc M s₂ (s₁.union s₂)
  | mergeL {a s₁ s₂ : St V} : Anc M a s₁ → IConf.Reach M s₂ → M.Inv (s₁.union s₂) →
      Anc M a (s₁.union s₂)
  | mergeR {a s₁ s₂ : St V} : IConf.Reach M s₁ → Anc M a s₂ → M.Inv (s₁.union s₂) →
      Anc M a (s₁.union s₂)

theorem Anc.reach {a s : St V} (h : Anc M a s) : IConf.Reach M s ∧ IConf.Reach M a := by
  induction h with
  | txParent t hs hi => exact ⟨.tx t hs hi, hs⟩
  | tx t _ hi ih => exact ⟨.tx t ih.1 hi, ih.2⟩
  | mergeParentL h1 h2 hi => exact ⟨.merge h1 h2 hi, h1⟩
  | mergeParentR h1 h2 hi => exact ⟨.merge h1 h2 hi, h2⟩
  | mergeL _ h2 hi ih => exact ⟨.merge ih.1 h2 hi, ih.2⟩
  | mergeR h1 _ hi ih => exact ⟨.merge h1 ih.1 hi, ih.2⟩

theorem union_self (s : St V) : s.union s = s :=
  funext fun _ => propext ⟨fun h => h.elim id id, Or.inl⟩

/-- Every reachable state descends from `s0` (also `s0` itself, as
`s0 ⊔ s0`): `s0` is an ancestor of every reachable state. -/
theorem s0_anc {s : St V} (h : IConf.Reach M s) : Anc M M.s0 s := by
  induction h with
  | init =>
    have := Anc.mergeParentL (M := M) IConf.Reach.init IConf.Reach.init (by rw [union_self]; exact M.init)
    rwa [union_self] at this
  | tx t _ hi ih => exact .tx t ih hi
  | merge _ h2 hi ih1 _ => exact .mergeL ih1 h2 hi

/-- Def. 6, read literally: I-T-reachable states (by at least one invocation)
with a common ancestor state.  The reachability of `Dᵢ, Dⱼ` is implied by
`Anc`. -/
def BailisAnc (M : Model V Tx) : Prop :=
  ∀ a s₁ s₂, Anc M a s₁ → Anc M a s₂ → M.Inv (s₁.union s₂)

theorem bailisAnc_iff : BailisAnc M ↔ M.IConfluent := by
  constructor
  · intro h s₁ s₂ h₁ h₂
    exact h M.s0 s₁ s₂ (s0_anc h₁) (s0_anc h₂)
  · intro h a s₁ s₂ h₁ h₂
    exact h s₁ s₂ h₁.reach.1 h₂.reach.1

/-- The states I-T-reachable from `s0` by at least one invocation are exactly
the reachable states. -/
theorem reachPlus_iff (s : St V) : (∃ a, Anc M a s) ↔ IConf.Reach M s :=
  ⟨fun ⟨_, h⟩ => h.reach.1, fun h => ⟨_, s0_anc h⟩⟩

end IConfR

end AuditR
end CC
