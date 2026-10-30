import CoordCriterion.CAP.TwoPhaseCommit
import CoordCriterion.Figures

/-!
# Two-phase commit: aborting on timeout (§4.3)

Supports the sentences of the paragraph "Locks in a shared-nothing database"
of `sections/distributed.tex` on a coordinator that aborts on timeout, before
the last vote arrives.  Two readings of that abort are checked.

*As a seal* (closing the polls on the decision specification `voteSpec`):

* `timeout_seals`: at an input with a missing vote, closing the polls
  (`Figures.closePolls`) applies, is a seal, and seals every input that adds a
  missing vote, yes or no; at `yy·` it removes `(yyy, commit)` and
  `(yyn, abort)` (`timeout_seals_yy`).
* `seal_not_coordinationFreeH`: any system in which the coordinator
  (participant `0`) may close the polls at `yy·` requires *distributed*
  coordination, whatever the other participants' strategies: the environment
  may deliver the late vote `yyy` to another participant
  (inputs are always allowed, `Allowed`).  In particular `sealSys`, where only
  the coordinator emits a decision, is not `CoordinationFreeH`.

*As a choice* (`abortSpec`: the coordinator may abort until it decides, so
`S(v) = {decide2PC v, abort}`):

* `abort_choice_yy`: at `yy·`, aborting is not exposable; its canonical
  commitment removes `(yyy, commit)` and keeps `(yyy, abort)`, so it chooses
  against commit and seals nothing.
* `coordSys_not_coordinationFree`, `coordSys_coordinationFreeH`: when only the
  coordinator decides, aborting requires coordination (another run of the
  coordinator commits at `yyy`) but not distributed coordination: no
  canonical output event of the coordinator seals an input.
* `replSys_not_coordinationFreeH`: when two participants may each decide
  (the decision replicated), one aborts at `yy·` while the other, after the
  late vote `yyy`, commits: distributed coordination.

Modeling choices: three owners' votes (`Votes 3`) for the examples; the
coordinator's timeout is an output event of the system, its clock is not
modeled; histories have two participants (or one).
-/

namespace CC
namespace CAP
namespace Timeout

open Classical

/-! ## Votes -/

/-- Three owners' votes. -/
def mk (a b c : Option Bool) : Fin 3 → Option Bool := fun p =>
  if p.val = 0 then a else if p.val = 1 then b else c

/-- `yy·`: two yes votes, the third missing. -/
abbrev yyN : Votes 3 := mk (some true) (some true) none
/-- `yyy`: the missing vote arrives, yes. -/
abbrev yyy : Votes 3 := mk (some true) (some true) (some true)
/-- `yyn`: the missing vote arrives, no. -/
abbrev yyn : Votes 3 := mk (some true) (some true) (some false)

theorem yyN_le_yyy : yyN ≼ yyy := by
  show ∀ p : Fin 3, (yyN p = none ∨ yyN p = yyy p); decide

theorem yyN_le_yyn : yyN ≼ yyn := by
  show ∀ p : Fin 3, (yyN p = none ∨ yyN p = yyn p); decide

theorem decide_yyy : decide2PC yyy = .commit :=
  (decide2PC_detects yyy).2.1.2 (by show ∀ p : Fin 3, yyy p = some true; decide)

theorem decide_yyn : decide2PC yyn = .abort :=
  (decide2PC_detects yyn).1.2 ⟨2, rfl⟩

theorem decide_yyN : decide2PC yyN = .undecided := by
  have h := decide2PC_detects yyN
  cases hd : decide2PC yyN with
  | undecided => rfl
  | commit => have := (h.2.1.1 hd) 2; cases this
  | abort =>
    obtain ⟨p, hp⟩ := h.1.1 hd
    revert hp; revert p; show ∀ p : Fin 3, yyN p = some false → _; decide

/-- A complete vote vector has no strict expansion. -/
theorem complete_max {m : Nat} {v w : Votes m} (hv : ∀ p, v p ≠ none) (h : v ≼ w) : v = w :=
  funext fun p => (h p).resolve_left (hv p)

/-! ## The timeout abort as a seal: closing the polls on `voteSpec` -/

/-- Closing the polls (Fig. `fig:election-frames`(d)) on the decision
specification. -/
noncomputable def cp {m : Nat} : Commitment (voteSpec m) :=
  Dist.toCAP (Figures.closePolls (sp := voteSpec m))

/-- **The timeout abort seals every input that adds a missing vote.**  At
`σ_S(v)` with a missing vote, closing the polls applies (it is a commitment);
it is a seal (wherever it removes a row it removes all); and every input that
adds a missing vote `p`, yes (`b = true`) or no (`b = false`), had a row and
keeps none.  Only the current input keeps rows, its row `(v, undecided)` when
no vote is no: with the polls closed, `undecided` is final, i.e. abort. -/
theorem timeout_seals {m : Nat} (v : Votes m) (p : Fin m) (hp : v p = none) :
    cp.f (canon (voteSpec m) v) = some (Figures.closeState (canon (voteSpec m) v)) ∧
    (∀ σ τ : State (voteSpec m), cp.f σ = some τ →
      ∀ k, (∃ u, σ.R k u ∧ ¬ τ.R k u) → ∀ w, ¬ τ.R k w) ∧
    (∀ (b : Bool) (k : Votes m), v ≼ k → k p = some b →
      (canon (voteSpec m) v).R k (decide2PC k) ∧
        ∀ u, ¬ (Figures.closeState (canon (voteSpec m) v)).R k u) ∧
    (∀ k u, (Figures.closeState (canon (voteSpec m) v)).R k u ↔ (k = v ∧ u = decide2PC v)) := by
  refine ⟨?_, fun σ τ h k hk => Figures.closePolls_seals h k hk, ?_, ?_⟩
  · let w : Votes m := fun q => if q = p then some true else v q
    have hvw : v ≼ w := fun q => by
      by_cases hq : q = p
      · subst hq; exact Or.inl hp
      · exact Or.inr (by simp [w, hq])
    have hne : w ≠ v := fun h => by
      have := congrFun h p; simp [w, hp] at this
    exact Figures.closeApp_eq.2 ⟨⟨w, decide2PC w, ⟨rfl, hvw⟩, hne⟩, rfl⟩
  · intro b k hvk hkp
    have hne : k ≠ v := fun h => by rw [h, hp] at hkp; cases hkp
    exact ⟨⟨rfl, hvk⟩, fun u hu => hne hu.2⟩
  · intro k u
    constructor
    · rintro ⟨⟨hS, _⟩, rfl⟩; exact ⟨rfl, hS⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨⟨rfl, PO.refl _⟩, rfl⟩

/-- At `yy·` the timeout abort removes `(yyy, commit)` and `(yyn, abort)`,
and seals both inputs; the remaining row is `(yy·, undecided)`. -/
theorem timeout_seals_yy :
    (canon (voteSpec 3) yyN).R yyy .commit ∧ (canon (voteSpec 3) yyN).R yyn .abort ∧
    (∀ u, ¬ (Figures.closeState (canon (voteSpec 3) yyN)).R yyy u) ∧
    (∀ u, ¬ (Figures.closeState (canon (voteSpec 3) yyN)).R yyn u) ∧
    (∀ k u, (Figures.closeState (canon (voteSpec 3) yyN)).R k u ↔
      (k = yyN ∧ u = .undecided)) := by
  obtain ⟨_, _, h3, h4⟩ := timeout_seals yyN 2 rfl
  obtain ⟨hy1, hy2⟩ := h3 true yyy yyN_le_yyy rfl
  obtain ⟨hn1, hn2⟩ := h3 false yyn yyN_le_yyn rfl
  rw [decide_yyy] at hy1; rw [decide_yyn] at hn1
  refine ⟨hy1, hn1, hy2, hn2, fun k u => ?_⟩
  rw [h4, decide_yyN]

/-- A participant's one-event run `Out_γ(u)`, given the committed state. -/
theorem lrun_out {I O : Type} [PO I] [PO O] {sp' : Spec I O} {D : Type} {n : Nat} {σ σc : State sp'}
    {γ : List (Commitment sp')} {u : O} (ha : applySeq σ γ = some σc)
    (hu : σc.R σc.cur u) (hex : Exposable σc u) :
    ∃ τ, LRun (D := D) (n := n) σ [LEv.out γ u] τ := by
  let τ : State sp' :=
    { cur := σc.cur, R := outputTable σc u, sub := fun k x h => σc.sub k x h.1,
      hasCur := ⟨u, hu, PO.refl u⟩, above := fun k x h => σc.above k x h.1 }
  exact ⟨τ, .out ha (Step.output σc τ u hu rfl rfl) hex (.nil τ)⟩

/-- **A seal requires distributed coordination, even if only the coordinator
decides.**  In any system whose coordinator (participant `0` of two, both
starting at `yy·`) may close the polls at `yy·`, some history has the other
participant accept the sealed input `yyy` (the environment may deliver the
late vote to any participant). -/
theorem seal_not_coordinationFreeH {D : Type} (Sys : System (voteSpec 3) D)
    (hb : Sys.basis cp) (hs : Sys.strat 2 (fun _ => yyN) 0 [] (.out [cp] .undecided)) :
    ¬ Sys.CoordinationFreeH := by
  intro hcf
  obtain ⟨happ, _, _, _⟩ := timeout_seals yyN 2 rfl
  obtain ⟨hcy, -, hsy, -, hrows⟩ := timeout_seals_yy
  let σ := canon (voteSpec 3) yyN
  let σc := Figures.closeState σ
  have ha : applySeq σ [cp] = some σc := by
    simp only [applySeq]
    rw [show cp.f σ = some σc from happ]
  have hu : σc.R σc.cur .undecided := (hrows _ _).2 ⟨rfl, rfl⟩
  have hex : Exposable σc .undecided := fun _ _ _ hn => absurd (Or.inl rfl) hn
  obtain ⟨τ0, hr0⟩ := lrun_out (D := D) (n := 2) ha hu hex
  have hr1 : LRun (D := D) (n := 2) σ [LEv.inp yyy] (canon _ yyy) :=
    .inp (Dist.step_canon_input _ yyN_le_yyy ⟨_, rfl⟩) (.nil _)
  let H : History (voteSpec 3) D 2 := fun r =>
    if r.val = 0 then [LEv.out [cp] .undecided] else [LEv.inp yyy]
  have hH0 : H 0 = [] ++ LEv.out [cp] .undecided :: [] := rfl
  have hH1 : H 1 = [] ++ LEv.inp yyy :: [] := rfl
  have hfin : ∀ r : Fin 2, r = 0 ∨ r = 1 := by decide
  have hnr : ∀ r a q k j d b, H r ≠ a ++ LEv.recv q k j d :: b := by
    intro r a q k j d b h
    have hm : LEv.recv q k j d ∈ H r := by rw [h]; simp
    rcases hfin r with rfl | rfl
    · rw [hH0] at hm; simp at hm
    · rw [hH1] at hm; simp at hm
  have hw : WF (fun _ => yyN) H := by
    refine ⟨fun r => ?_, fun r a q k j d b h => absurd h (hnr r a q k j d b)⟩
    rcases hfin r with rfl | rfl
    · exact ⟨τ0, hr0⟩
    · exact ⟨_, hr1⟩
  have hp : Produced Sys 2 (fun _ => yyN) H := by
    intro r a e b h
    rcases hfin r with rfl | rfl
    · rw [hH0] at h
      cases a with
      | nil =>
        simp at h; obtain ⟨rfl, _⟩ := h
        exact ⟨fun c hc => by simp at hc; subst hc; exact hb, hs⟩
      | cons _ _ => simp at h
    · rw [hH1] at h
      cases a with
      | nil => simp at h; obtain ⟨rfl, _⟩ := h; trivial
      | cons _ _ => simp at h
  exact (hcf.1 2 _ H hw hp 0 [] [] [cp] .undecided σ σc hH0 (.nil _) ha).2 yyy
    ⟨_, hcy⟩ hsy ⟨1, [], [], by decide, hH1⟩

/-- Only the coordinator (participant `0`) decides, by closing the polls at
`yy·`; the owners' strategies never decide. -/
noncomputable def sealSys (D : Type) : System (voteSpec 3) D where
  basis := fun c => c = cp
  strat := fun _ init p _ e =>
    match e with
    | .out γ u => γ = [cp] ∧ u = .undecided ∧ p.val = 0 ∧ init p = yyN
    | _ => False

theorem sealSys_only_coordinator (D : Type) :
    ∀ n init p pre γ u, (sealSys D).strat n init p pre (.out γ u) → p.val = 0 :=
  fun _ _ _ _ _ _ h => h.2.2.1

/-- The seal requires coordination, and distributed coordination. -/
theorem sealSys_not_coordinationFreeH (D : Type) :
    ¬ (sealSys D).CoordinationFree ∧ ¬ (sealSys D).CoordinationFreeH := by
  have h := seal_not_coordinationFreeH (sealSys D) rfl ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨fun hcf => h (coordinationFree_to_H hcf), h⟩

/-! ## The timeout abort as a choice: `abortSpec` -/

/-- The coordinator may abort until it decides: `S(v) = {decide2PC v, abort}`
(so `{abort}` after a no vote, `{undecided, abort}` while votes are missing,
`{commit, abort}` when all are yes). -/
noncomputable def abortSpec (m : Nat) : Spec (Votes m) Decision where
  S v d := d = decide2PC v ∨ d = .abort
  total _ := ⟨_, Or.inr rfl⟩

theorem le_abort_or_commit (u : Decision) : u ≼ .abort ∨ u = .commit := by
  cases u
  · exact Or.inl (Or.inl rfl)
  · exact Or.inr rfl
  · exact Or.inl (Or.inr rfl)

theorem abort_le_iff (x : Decision) : (Decision.abort ≼ x) ↔ x = .abort := by
  constructor
  · intro h
    rcases h with h | h
    · cases h
    · exact h.symm
  · rintro rfl; exact PO.refl _

/-- A state whose current fiber holds `commit` has all votes in, so no row
at another input. -/
theorem rows_at_cur_of_commit {m : Nat} {σ : State (abortSpec m)} (hc : σ.R σ.cur .commit)
    {k : Votes m} {x : Decision} (hk : σ.R k x) : k = σ.cur := by
  have hall : ∀ p, σ.cur p = some true := by
    rcases σ.sub _ _ hc with h | h
    · exact (decide2PC_detects σ.cur).2.1.1 h.symm
    · cases h
  exact (complete_max (fun p h => by rw [hall p] at h; cases h) (σ.above _ _ hk)).symm

/-- Every row at another input has `abort` beside it. -/
def Inv {m : Nat} (σ : State (abortSpec m)) : Prop :=
  ∀ k x, σ.R k x → k ≠ σ.cur → σ.R k .abort

theorem inv_canon {m : Nat} (i : Votes m) : Inv (canon (abortSpec m) i) :=
  fun _ _ h _ => ⟨Or.inr rfl, h.2⟩

/-- The canonical commitment for `u` keeps the `abort` rows at other
inputs. -/
theorem kc_keeps_abort {m : Nat} {σ : State (abortSpec m)} {u : Decision} (hu : σ.R σ.cur u)
    (hI : Inv σ) {k : Votes m} {x : Decision} (hx : σ.R k x) (hk : k ≠ σ.cur) :
    (kcState σ u hu).R k .abort := by
  have ha := hI k x hx hk
  refine ⟨ha, ?_⟩
  rcases le_abort_or_commit u with h | rfl
  · exact not_rm_of_le ha h
  · exact absurd (rows_at_cur_of_commit hu hx) hk

/-- A canonical commitment seals no input. -/
theorem kc_seals_nothing {m : Nat} {σ σc : State (abortSpec m)} {u : Decision}
    {γ : List (Commitment (abortSpec m))} (hγ : γ = [] ∨ γ = [kc u])
    (hI : Inv σ) (ha : applySeq σ γ = some σc) (k : Votes m) (hk : ∃ x, σ.R k x) :
    ∃ x, σc.R k x := by
  obtain ⟨x, hx⟩ := hk
  rcases hγ with rfl | rfl
  · simp [applySeq] at ha; subst ha; exact ⟨x, hx⟩
  · obtain ⟨hu, rfl⟩ := kc_apply_some ha
    by_cases hkc : k = σ.cur
    · subst hkc; exact (kcState σ u hu).hasCur
    · exact ⟨_, kc_keeps_abort hu hI hx hkc⟩

/-- Events whose strategies are the canonical output events. -/
def OkEv {m : Nat} {D : Type} {n : Nat} : LEv (abortSpec m) D n → Prop
  | .inp _ => True
  | .out γ u => γ = [] ∨ γ = [kc u]
  | _ => False

theorem inv_lrun {m : Nat} {D : Type} {n : Nat} {σ ρ : State (abortSpec m)}
    {es : List (LEv (abortSpec m) D n)} (h : LRun σ es ρ) (hok : ∀ e ∈ es, OkEv e)
    (hI : Inv σ) : Inv ρ := by
  induction h with
  | nil => exact hI
  | @inp σ τ ρ j es hs _ ih =>
    apply ih (fun e he => hok e (List.mem_cons_of_mem _ he))
    cases hs with
    | input _ _ hj hcur hR =>
      intro k x hk hne
      rw [hR] at hk ⊢
      rw [hcur] at hne
      refine ⟨hI k x hk.1 fun h => hne ?_, hk.2⟩
      obtain ⟨u, hu⟩ := hj
      subst h
      exact PO.antisymm (σ.above _ _ hu) hk.2
  | @out σ σc τ ρ γ o es ha hs _ _ ih =>
    apply ih (fun e he => hok e (List.mem_cons_of_mem _ he))
    have hγ : γ = [] ∨ γ = [kc o] := hok _ List.mem_cons_self
    have hIc : Inv σc := by
      rcases hγ with rfl | rfl
      · simp [applySeq] at ha; subst ha; exact hI
      · obtain ⟨hu, rfl⟩ := kc_apply_some ha
        intro k x hk hne
        exact kc_keeps_abort hu hI hk.1 hne
    cases hs with
    | output _ _ ho hcur hR =>
      intro k x hk hne
      rw [hR] at hk ⊢
      rw [hcur] at hne
      refine ⟨hIc k x hk.1 hne, ?_⟩
      rcases le_abort_or_commit o with h | rfl
      · exact h
      · exact absurd (rows_at_cur_of_commit ho hk.1) hne
  | cmt _ _ _ _ => exact absurd (hok _ List.mem_cons_self) id
  | send _ ih => exact ih (fun e he => hok e (List.mem_cons_of_mem _ he)) hI
  | recv _ ih => exact ih (fun e he => hok e (List.mem_cons_of_mem _ he)) hI

/-- **At `yy·`, aborting is a choice.**  `abort` is not exposable at
`σ_S(yy·)`; its canonical output event `Out_{[κ_abort]}(abort)` is legal,
removes `(yyy, commit)`, keeps `(yyy, abort)`, and seals no input. -/
theorem abort_choice_yy :
    ¬ Exposable (canon (abortSpec 3) yyN) .abort ∧
    ∃ σc, applySeq (canon (abortSpec 3) yyN) [kc .abort] = some σc ∧
      σc.R σc.cur .abort ∧ Exposable σc .abort ∧
      (canon (abortSpec 3) yyN).R yyy .commit ∧ ¬ σc.R yyy .commit ∧ σc.R yyy .abort ∧
      ∀ k, (∃ x, (canon (abortSpec 3) yyN).R k x) → ∃ x, σc.R k x := by
  let σ := canon (abortSpec 3) yyN
  have hcy : σ.R yyy .commit := ⟨Or.inl decide_yyy.symm, yyN_le_yyy⟩
  have hay : σ.R yyy .abort := ⟨Or.inr rfl, yyN_le_yyy⟩
  have hnot : ¬ Exposable σ .abort := by
    intro h
    obtain ⟨u, hu, h1, h2⟩ := h yyy .commit hcy (fun h => by cases (abort_le_iff _).1 h)
    rw [abort_le_iff] at h1; subst h1
    rcases h2 with h | h <;> cases h
  have hu : σ.R σ.cur .abort := ⟨Or.inr rfl, PO.refl _⟩
  obtain ⟨γ, σc, hγ, ha, hcu, hex⟩ := kc_legal hu
  have hγ' : γ = [kc .abort] := by
    rcases hγ with rfl | h
    · simp [applySeq] at ha; subst ha; exact absurd hex hnot
    · exact h
  subst hγ'
  obtain ⟨hu', rfl⟩ := kc_apply_some ha
  refine ⟨hnot, _, ha, hcu, hex, hcy, ?_, kc_keeps_abort hu' (inv_canon _) hcy ?_,
    kc_seals_nothing (Or.inr rfl) (inv_canon _) ha⟩
  · intro hc
    obtain ⟨u, hu, h1, h2⟩ := hex yyy .commit hc (fun h => by cases (abort_le_iff _).1 h)
    rw [abort_le_iff] at h1; subst h1
    rcases h2 with h | h <;> cases h
  · intro h; have := congrFun h 2; cases this

/-- Only the coordinator (participant `0`) decides, by canonical output
events. -/
noncomputable def coordSys (m : Nat) (D : Type) : System (abortSpec m) D where
  basis := fun c => ∃ u, c = kc u
  strat := fun _ _ p _ e =>
    match e with
    | .out γ u => (γ = [] ∨ γ = [kc u]) ∧ p.val = 0
    | _ => False

/-- Every participant may decide, by canonical output events (the decision
replicated). -/
noncomputable def replSys (m : Nat) (D : Type) : System (abortSpec m) D where
  basis := fun c => ∃ u, c = kc u
  strat := fun _ _ _ _ e =>
    match e with
    | .out γ u => γ = [] ∨ γ = [kc u]
    | _ => False

theorem prefix_ok {m : Nat} {D : Type} {n : Nat} {Sys : System (abortSpec m) D}
    (hS : ∀ n init p pre e, Allowed Sys n init p pre e → OkEv e)
    {init : Fin n → Votes m} {H : History (abortSpec m) D n} (hp : Produced Sys n init H)
    {p : Fin n} {a b : List (LEv (abortSpec m) D n)} {e : LEv (abortSpec m) D n}
    (hH : H p = a ++ e :: b) : ∀ e' ∈ a, OkEv e' := by
  intro e' he'
  obtain ⟨a1, a2, rfl⟩ := List.append_of_mem he'
  exact hS _ _ _ _ _ (hp p a1 e' (a2 ++ e :: b) (by rw [hH]; simp))

theorem coordSys_ok {m : Nat} {D : Type} :
    ∀ n init p pre e, Allowed (coordSys m D) n init p pre e → OkEv e := by
  intro n init p pre e h
  cases e with
  | inp _ => trivial
  | out γ u => exact h.2.1
  | cmt _ => exact h.2.elim
  | send _ _ => exact h.elim
  | recv _ _ _ _ => exact h.elim

theorem replSys_ok {m : Nat} {D : Type} :
    ∀ n init p pre e, Allowed (replSys m D) n init p pre e → OkEv e := by
  intro n init p pre e h
  cases e with
  | inp _ => trivial
  | out γ u => exact h.2
  | cmt _ => exact h.2.elim
  | send _ _ => exact h.elim
  | recv _ _ _ _ => exact h.elim

/-- **Only the coordinator decides: no distributed coordination.**  No other
participant emits a decision, and no canonical output event of the
coordinator seals an input, so no other participant can contradict it. -/
theorem coordSys_coordinationFreeH (m : Nat) (D : Type) : (coordSys m D).CoordinationFreeH := by
  refine ⟨?_, fun n init H _ hp p a b γ σ σc hH _ _ => (hp p a (.cmt γ) b hH).2.elim⟩
  intro n init H _ hp p a b γ o σ σc hH hrun hap
  obtain ⟨_, hγ, hp0⟩ := hp p a (.out γ o) b hH
  have hI : Inv σ := inv_lrun hrun (prefix_ok coordSys_ok hp hH) (inv_canon _)
  refine ⟨fun k x _ _ => ?_, fun k hk hall => ?_⟩
  · rintro ⟨q, a', b', γ', σ', hqp, hq, _, _⟩
    have hq0 : q.val = 0 := (hp q a' (.out γ' x) b' hq).2.2
    exact hqp (Fin.ext (hq0.trans hp0.symm))
  · obtain ⟨x, hx⟩ := kc_seals_nothing hγ hI hap k hk
    exact absurd hx (hall x)

/-- A one-participant history in which the coordinator, starting at `i`,
emits `u ∈ R(i)` by its canonical output event. -/
theorem one_emit {m : Nat} (D : Type) (Sys : System (abortSpec m) D) (i : Votes m)
    (hS : ∀ γ u, (γ = [] ∨ γ = [kc u]) → Sys.strat 1 (fun _ => i) 0 [] (.out γ u))
    (hb : ∀ u, Sys.basis (kc u)) (u : Decision)
    (hu : (canon (abortSpec m) i).R i u) :
    ∃ (γ : List (Commitment (abortSpec m))) (σc : State (abortSpec m)) (H : History (abortSpec m) D 1), (γ = [] ∨ γ = [kc u]) ∧
      applySeq (canon (abortSpec m) i) γ = some σc ∧ Exposable σc u ∧
      WF (fun _ => i) H ∧ Produced Sys 1 (fun _ => i) H ∧ H 0 = [] ++ LEv.out γ u :: [] := by
  obtain ⟨γ, σc, hγ, ha, hcu, hex⟩ := kc_legal hu
  obtain ⟨τ, hr⟩ := lrun_out (D := D) (n := 1) ha hcu hex
  let H : History (abortSpec m) D 1 := fun _ => [LEv.out γ u]
  refine ⟨γ, σc, H, hγ, ha, hex, ⟨fun r => ⟨τ, hr⟩, fun r a q k j d b h => ?_⟩, ?_, rfl⟩
  · have hm : LEv.recv q k j d ∈ H r := by rw [h]; simp
    simp [H] at hm
  · intro r a e b h
    have hr0 : r = 0 := Fin.ext (by omega)
    subst hr0
    cases a with
    | nil =>
      simp [H] at h; obtain ⟨rfl, _⟩ := h
      refine ⟨fun c hc => ?_, hS γ u hγ⟩
      rcases hγ with rfl | rfl
      · cases hc
      · simp at hc; subst hc; exact hb u
    | cons _ _ => simp [H] at h

/-- **Only the coordinator decides: coordination.**  The coordinator's abort
at `yy·` chooses against `(yyy, commit)`, which another run of the same
coordinator emits after all yes votes arrive. -/
theorem coordSys_not_coordinationFree (D : Type) : ¬ (coordSys 3 D).CoordinationFree := by
  intro hcf
  have hS : ∀ (i : Votes 3) γ u, (γ = [] ∨ γ = [kc u]) →
      (coordSys 3 D).strat 1 (fun _ => i) 0 [] (.out γ u) := fun _ _ _ h => ⟨h, rfl⟩
  have hb : ∀ u, (coordSys 3 D).basis (kc u) := fun u => ⟨u, rfl⟩
  obtain ⟨γ0, σc, H, hγ0, ha0, hex0, hw, hp, hH0⟩ :=
    one_emit D (coordSys 3 D) yyN (hS yyN) hb .abort ⟨Or.inr rfl, PO.refl _⟩
  obtain ⟨γ1, _, H', _, _, _, hw', hp', hH1⟩ :=
    one_emit D (coordSys 3 D) yyy (hS yyy) hb .commit ⟨Or.inl decide_yyy.symm, PO.refl _⟩
  have hcy : (canon (abortSpec 3) yyN).R yyy .commit := ⟨Or.inl decide_yyy.symm, yyN_le_yyy⟩
  -- the abort's commitments remove `(yyy, commit)`
  have hnc : ¬ σc.R yyy .commit := by
    intro hc
    obtain ⟨u, _, h1, h2⟩ := hex0 yyy .commit hc (fun h => by cases (abort_le_iff _).1 h)
    rw [abort_le_iff] at h1; subst h1
    rcases h2 with h | h <;> cases h
  exact (hcf.1 1 _ H hw hp 0 [] [] γ0 .abort _ σc hH0 (.nil _) ha0).1 yyy .commit hcy hnc
    ⟨1, _, H', 0, [], [], γ1, canon _ yyy, hw', hp', hH1, .nil _, rfl⟩

/-- **A replicated decision: distributed coordination.**  Two participants
start at `yy·`; one aborts, the other receives the late yes vote and commits,
in the same history. -/
theorem replSys_not_coordinationFreeH (D : Type) : ¬ (replSys 3 D).CoordinationFreeH := by
  intro hcf
  let σ := canon (abortSpec 3) yyN
  have hu : σ.R σ.cur .abort := ⟨Or.inr rfl, PO.refl _⟩
  obtain ⟨γ0, σc0, hγ0, ha0, hcu0, hex0⟩ := kc_legal hu
  obtain ⟨τ0, hr0⟩ := lrun_out (D := D) (n := 2) ha0 hcu0 hex0
  have hc1 : (canon (abortSpec 3) yyy).R yyy .commit := ⟨Or.inl decide_yyy.symm, PO.refl _⟩
  obtain ⟨γ1, σc1, hγ1, ha1, hcu1, hex1⟩ := kc_legal hc1
  obtain ⟨τ1, hr1⟩ := lrun_out (D := D) (n := 2) ha1 hcu1 hex1
  have hs : Step σ (.input yyy) (canon _ yyy) := Dist.step_canon_input _ yyN_le_yyy ⟨_, Or.inr rfl⟩
  have hin : LRun (D := D) (n := 2) σ [LEv.inp yyy] (canon _ yyy) := .inp hs (.nil _)
  let H : History (abortSpec 3) D 2 := fun r =>
    if r.val = 0 then [LEv.out γ0 .abort] else [LEv.inp yyy, LEv.out γ1 .commit]
  have hH0 : H 0 = [] ++ LEv.out γ0 .abort :: [] := rfl
  have hH1 : H 1 = [LEv.inp yyy] ++ LEv.out γ1 .commit :: [] := rfl
  have hfin : ∀ r : Fin 2, r = 0 ∨ r = 1 := by decide
  have hnr : ∀ r a q k j d b, H r ≠ a ++ LEv.recv q k j d :: b := by
    intro r a q k j d b h
    have hm : LEv.recv q k j d ∈ H r := by rw [h]; simp
    rcases hfin r with rfl | rfl
    · rw [hH0] at hm; simp at hm
    · rw [hH1] at hm; simp at hm
  have hw : WF (fun _ => yyN) H := by
    refine ⟨fun r => ?_, fun r a q k j d b h => absurd h (hnr r a q k j d b)⟩
    rcases hfin r with rfl | rfl
    · exact ⟨τ0, hr0⟩
    · exact ⟨τ1, by rw [hH1]; exact lrun_append.2 ⟨_, hin, hr1⟩⟩
  have hbasis : ∀ (u : Decision) (γ : List (Commitment (abortSpec 3))),
      (γ = [] ∨ γ = [kc u]) → ∀ c ∈ γ, (replSys 3 D).basis c := by
    intro u γ hγ c hc
    rcases hγ with rfl | rfl
    · cases hc
    · simp at hc; exact ⟨u, hc⟩
  have hp : Produced (replSys 3 D) 2 (fun _ => yyN) H := by
    intro r a e b h
    rcases hfin r with rfl | rfl
    · rw [hH0] at h
      cases a with
      | nil => simp at h; obtain ⟨rfl, _⟩ := h; exact ⟨hbasis _ _ hγ0, hγ0⟩
      | cons _ _ => simp at h
    · rw [hH1] at h
      match a, h with
      | [], h => simp at h; obtain ⟨rfl, _⟩ := h; trivial
      | [_], h => simp at h; obtain ⟨_, rfl, _⟩ := h; exact ⟨hbasis _ _ hγ1, hγ1⟩
      | _ :: _ :: _, h => simp at h
  have hcy : σ.R yyy .commit := ⟨Or.inl decide_yyy.symm, yyN_le_yyy⟩
  have hnc : ¬ σc0.R yyy .commit := by
    intro hc
    obtain ⟨u, _, h1, h2⟩ := hex0 yyy .commit hc (fun h => by cases (abort_le_iff _).1 h)
    rw [abort_le_iff] at h1; subst h1
    rcases h2 with h | h <;> cases h
  exact (hcf.1 2 _ H hw hp 0 [] [] γ0 .abort σ σc0 hH0 (.nil _) ha0).1 yyy .commit hcy hnc
    ⟨1, [LEv.inp yyy], [], γ1, canon _ yyy, by decide, hH1, hin, rfl⟩

end Timeout
end CAP
end CC
