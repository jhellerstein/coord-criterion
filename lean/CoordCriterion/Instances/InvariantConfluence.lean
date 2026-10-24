import CoordCriterion.Foundations.Core

/-!
# Invariant confluence (Section `sec:iconfluence-instance`, Appendix B `app:iconfluence`)

Proposition `prop:iconfluence-lm`.  We formalize the Bailis et al. model as presented in the paper
(Section `sec:iconfluence-instance`, Appendix `app:iconfluence`) and prove

* `CC.IConf.ic_iff_liftedMono`       : `T` invariant confluent ↔ `S_I` has Lifted Monotonicity;
* `CC.IConf.ic_iff_commonExpansion`  : the same with the common-expansion form.

The equivalence with Bailis et al.'s own Def. 6 is in
`Instances/BailisDefinition.lean`; the worked examples are in
`Instances/Examples.lean`.

## Representation choices

* **States** are sets of versions, `St V := V → Prop`; merge is union and the
  output order is inclusion (`s ≼ u ↔ s ⊆ u`).  Antisymmetry is by
  `funext`/`propext`.
* **Transactions** are given by an index type `Tx` and an interpretation
  `app : Tx → St V → St V`, with the inflationarity hypothesis `s ⊆ app t s`.
  (`T` is the range of `app`.)
* **Histories** (`Hist Tx`): events are natural-number ids.  A history is a
  partial labeling `lab : Nat → Option Tx` (events are the ids with a label,
  finitely many) and a strict partial order `lt` (visibility) on its events.
  We require ids to be numbered along a linear extension (`lt a b → a < b`).
  Every finite partial order admits such a numbering, so this loses no
  generality; it makes the event-by-event recursion for `pre`/`post` a plain
  recursion on `Nat`.  Since only events carry data, structural equality of
  histories is extensional, and the expansion order is antisymmetric.
* **Expansion order** on histories: `a ≼ b` iff `a` is a downward-closed
  sub-order of `b` in which every event keeps its label and exactly its
  predecessors: labels of `a` are labels of `b`, and
  `a.lt x y ↔ b.lt x y ∧ y ∈ a`.  (Paper: "`b` \inrel `a`".)
* Disjoint union of two histories is realised by interleaving ids
  (even ids for the left part, odd ids for the right part), so histories
  "up to isomorphism" are not needed.
-/

namespace CC
namespace IConf

open Classical

/-! ## States -/

/-- Database states: sets of versions. -/
def St (V : Type) := V → Prop

/-- Merge of states: union. -/
def St.union {V : Type} (s₁ s₂ : St V) : St V := fun v => s₁ v ∨ s₂ v

instance (V : Type) : PO (St V) where
  le s u := ∀ v, s v → u v
  refl _ _ h := h
  trans h₁ h₂ v h := h₂ v (h₁ v h)
  antisymm h₁ h₂ := funext fun v => propext ⟨h₁ v, h₂ v⟩

theorem St.le_def {V : Type} (s u : St V) : (s ≼ u) = (∀ v, s v → u v) := rfl

/-! ## The model -/

/-- The Bailis et al. model: an initial state `s0`, inflationary transactions
`app t`, and an invariant `Inv` holding at `s0`. -/
structure Model (V Tx : Type) where
  app : Tx → St V → St V
  infl : ∀ t (s : St V) v, s v → app t s v
  s0 : St V
  Inv : St V → Prop
  init : Inv s0

variable {V Tx : Type}

/-- Reachable states: derived from `s0` by transactions and merges, every state
along the way satisfying the invariant. -/
inductive Reach (M : Model V Tx) : St V → Prop where
  | init : Reach M M.s0
  | tx {s : St V} (t : Tx) : Reach M s → M.Inv (M.app t s) → Reach M (M.app t s)
  | merge {s₁ s₂ : St V} : Reach M s₁ → Reach M s₂ → M.Inv (s₁.union s₂) →
      Reach M (s₁.union s₂)

/-- Invariant confluence. -/
def Model.IConfluent (M : Model V Tx) : Prop :=
  ∀ s₁ s₂, Reach M s₁ → Reach M s₂ → M.Inv (s₁.union s₂)

theorem Reach.inv {M : Model V Tx} {s : St V} (h : Reach M s) : M.Inv s := by
  cases h with
  | init => exact M.init
  | tx _ _ h => exact h
  | merge _ _ h => exact h

/-! ## Histories -/

/-- A finite transaction history, with ids numbered along a linear extension. -/
structure Hist (Tx : Type) where
  lab : Nat → Option Tx
  lt : Nat → Nat → Prop
  lt_ev : ∀ {a b}, lt a b → lab a ≠ none ∧ lab b ≠ none
  lt_num : ∀ {a b}, lt a b → a < b
  lt_trans : ∀ {a b c}, lt a b → lt b c → lt a c
  fin : ∃ n, ∀ e, n ≤ e → lab e = none

namespace Hist

/-- `e` is an event of `h`. -/
def ev (h : Hist Tx) (e : Nat) : Prop := h.lab e ≠ none

theorem ext' {a b : Hist Tx} (h₁ : a.lab = b.lab) (h₂ : a.lt = b.lt) : a = b := by
  cases a; cases b; cases h₁; cases h₂; rfl

/-- `a` is a downward-closed sub-history of `b` (`b` expands `a`). -/
def le (a b : Hist Tx) : Prop :=
  (∀ e t, a.lab e = some t → b.lab e = some t) ∧ (∀ x y, a.lt x y ↔ (b.lt x y ∧ a.ev y))

theorem ev_of_lt_left {h : Hist Tx} {x y : Nat} (hl : h.lt x y) : h.ev x := (h.lt_ev hl).1
theorem ev_of_lt_right {h : Hist Tx} {x y : Nat} (hl : h.lt x y) : h.ev y := (h.lt_ev hl).2

theorem le_ev {a b : Hist Tx} (hab : a.le b) {e : Nat} (he : a.ev e) : b.ev e := by
  unfold ev at *
  cases h : a.lab e with
  | none => exact absurd h he
  | some t => rw [hab.1 e t h]; simp

theorem le_lab {a b : Hist Tx} (hab : a.le b) {e : Nat} (he : a.ev e) : a.lab e = b.lab e := by
  unfold ev at he
  cases h : a.lab e with
  | none => exact absurd h he
  | some t => rw [hab.1 e t h]

/-- Sub-histories are downward closed. -/
theorem le_down {a b : Hist Tx} (hab : a.le b) {x y : Nat} (hl : b.lt x y) (hy : a.ev y) :
    a.ev x :=
  ev_of_lt_left ((hab.2 x y).2 ⟨hl, hy⟩)

theorem le_refl (a : Hist Tx) : a.le a :=
  ⟨fun _ _ h => h, fun _ _ => ⟨fun h => ⟨h, ev_of_lt_right h⟩, fun h => h.1⟩⟩

theorem le_trans {a b c : Hist Tx} (hab : a.le b) (hbc : b.le c) : a.le c := by
  refine ⟨fun e t h => hbc.1 e t (hab.1 e t h), fun x y => ?_⟩
  rw [hab.2, hbc.2]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, le_ev hab h.2⟩, h.2⟩⟩

theorem le_antisymm {a b : Hist Tx} (hab : a.le b) (hba : b.le a) : a = b := by
  apply ext'
  · funext e
    by_cases he : a.ev e
    · exact le_lab hab he
    · by_cases hb : b.ev e
      · exact absurd (le_ev hba hb) he
      · unfold ev at he hb; simp at he hb; rw [he, hb]
  · funext x y
    apply propext
    rw [hab.2]
    exact ⟨fun h => h.1, fun h => ⟨h, le_ev hba (ev_of_lt_right h)⟩⟩

/-- Two sub-histories of a common history are ordered by event inclusion. -/
theorem le_of_sub {a b j : Hist Tx} (ha : a.le j) (hb : b.le j)
    (hs : ∀ e, a.ev e → b.ev e) : a.le b := by
  refine ⟨fun e t h => ?_, fun x y => ?_⟩
  · have hae : a.ev e := by unfold ev; rw [h]; simp
    rw [le_lab hb (hs e hae), ← le_lab ha hae, h]
  · rw [ha.2, hb.2]
    exact ⟨fun h => ⟨⟨h.1, hs y h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩

end Hist

instance : PO (Hist Tx) where
  le := Hist.le
  refl := Hist.le_refl
  trans := Hist.le_trans
  antisymm := Hist.le_antisymm

theorem Hist.po_le {a b : Hist Tx} : (a ≼ b) = a.le b := rfl

/-! ## Evaluation: `pre`, `post`, `eval` -/

section Eval
variable (M : Model V Tx)

/-- Apply the label of an event (if any). -/
def step : Option Tx → St V → St V
  | some t, s => M.app t s
  | none, s => s

/-- `post(e) = t_e(pre(e))`, where `pre(e) = s0 ∪ ⋃_{e' < e} post(e')`. -/
def post (h : Hist Tx) (e : Nat) : St V :=
  step M (h.lab e) (fun v => M.s0 v ∨ ∃ x, ∃ _ : x < e, h.lt x e ∧ post h x v)
termination_by e

/-- `pre(e) = s0 ∪ ⋃_{e' < e} post(e')`. -/
def pre (h : Hist Tx) (e : Nat) : St V := fun v => M.s0 v ∨ ∃ x, h.lt x e ∧ post M h x v

/-- `eval(h) = s0 ∪ ⋃_{e ∈ h} post(e)`. -/
def eval (h : Hist Tx) : St V := fun v => M.s0 v ∨ ∃ e, h.ev e ∧ post M h e v

theorem post_eq (h : Hist Tx) (e : Nat) : post M h e = step M (h.lab e) (pre M h e) := by
  rw [post]; congr 1; funext v; unfold pre
  apply propext
  exact ⟨fun h' => h'.elim Or.inl fun ⟨x, _, hl, hp⟩ => Or.inr ⟨x, hl, hp⟩,
    fun h' => h'.elim Or.inl fun ⟨x, hl, hp⟩ => Or.inr ⟨x, h.lt_num hl, hl, hp⟩⟩

theorem step_infl (o : Option Tx) (s : St V) (v : V) (hv : s v) : step M o s v := by
  cases o with
  | none => exact hv
  | some t => exact M.infl t s v hv

theorem pre_sub_post (h : Hist Tx) (e : Nat) (v : V) (hv : pre M h e v) : post M h e v := by
  rw [post_eq]; exact step_infl M _ _ v hv

theorem s0_sub_eval (h : Hist Tx) (v : V) (hv : M.s0 v) : eval M h v := Or.inl hv

/-- Transport of `pre`/`post` along an id map `f` that is an isomorphism of
`a` onto a downward-closed part of `b`. -/
theorem pre_post_map (a b : Hist Tx) (f : Nat → Nat)
    (hlab : ∀ e, a.ev e → b.lab (f e) = a.lab e)
    (hlt : ∀ x y, a.ev y → (a.lt x y ↔ b.lt (f x) (f y)))
    (hpred : ∀ n y, a.ev y → b.lt n (f y) → ∃ x, n = f x) :
    ∀ e, a.ev e → pre M a e = pre M b (f e) ∧ post M a e = post M b (f e) := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro he
    have hpre : pre M a e = pre M b (f e) := by
      funext v; unfold pre; apply propext
      constructor
      · rintro (h0 | ⟨x, hl, hp⟩)
        · exact Or.inl h0
        · have hx := Hist.ev_of_lt_left hl
          refine Or.inr ⟨f x, (hlt x e he).1 hl, ?_⟩
          rw [← (ih x (a.lt_num hl) hx).2]; exact hp
      · rintro (h0 | ⟨n, hl, hp⟩)
        · exact Or.inl h0
        · obtain ⟨x, rfl⟩ := hpred n e he hl
          have hl' := (hlt x e he).2 hl
          refine Or.inr ⟨x, hl', ?_⟩
          rw [(ih x (a.lt_num hl') (Hist.ev_of_lt_left hl')).2]; exact hp
    refine ⟨hpre, ?_⟩
    rw [post_eq, post_eq, hpre, hlab e he]

/-- `post` of a sub-history agrees with `post` in the larger history. -/
theorem post_sub {c j : Hist Tx} (hc : c ≼ j) {e : Nat} (he : c.ev e) :
    post M c e = post M j e :=
  (pre_post_map M c j id (fun e he => (Hist.le_lab hc he).symm)
    (fun x y hy => by rw [hc.2]; exact ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩)
    (fun n _ _ _ => ⟨n, rfl⟩) e he).2

theorem eval_sub {c j : Hist Tx} (hc : c ≼ j) (v : V) :
    eval M c v ↔ M.s0 v ∨ ∃ e, c.ev e ∧ post M j e v := by
  unfold eval
  exact ⟨fun h => h.elim Or.inl fun ⟨e, he, hp⟩ => Or.inr ⟨e, he, by rwa [← post_sub M hc he]⟩,
    fun h => h.elim Or.inl fun ⟨e, he, hp⟩ => Or.inr ⟨e, he, by rwa [post_sub M hc he]⟩⟩

/-- The state of a union of downward-closed sub-histories is the union of
their states (paper, App. `app:iconfluence`).  No inflationarity is needed. -/
theorem eval_union {a b c j : Hist Tx} (ha : a ≼ j) (hb : b ≼ j) (hc : c ≼ j)
    (hev : ∀ e, c.ev e ↔ a.ev e ∨ b.ev e) : eval M c = (eval M a).union (eval M b) := by
  funext v; apply propext
  unfold St.union
  rw [eval_sub M ha, eval_sub M hb, eval_sub M hc]
  constructor
  · rintro (h0 | ⟨e, he, hp⟩)
    · exact Or.inl (Or.inl h0)
    · rcases (hev e).1 he with h | h
      · exact Or.inl (Or.inr ⟨e, h, hp⟩)
      · exact Or.inr (Or.inr ⟨e, h, hp⟩)
  · rintro ((h0 | ⟨e, he, hp⟩) | (h0 | ⟨e, he, hp⟩))
    · exact Or.inl h0
    · exact Or.inr ⟨e, (hev e).2 (Or.inl he), hp⟩
    · exact Or.inl h0
    · exact Or.inr ⟨e, (hev e).2 (Or.inr he), hp⟩

theorem eval_mono {a b : Hist Tx} (hab : a ≼ b) : eval M a ≼ eval M b := by
  intro v hv
  rw [eval_sub M hab] at hv
  exact hv.elim Or.inl fun ⟨e, he, hp⟩ => Or.inr ⟨e, Hist.le_ev hab he, hp⟩

theorem eval_noev {c : Hist Tx} (hc : ∀ e, ¬ c.ev e) : eval M c = M.s0 := by
  funext v; apply propext; unfold eval
  exact ⟨fun h => h.elim id fun ⟨e, he, _⟩ => absurd he (hc e), Or.inl⟩

end Eval

/-! ## Constructions on histories -/

namespace Hist

/-- Restriction of `j` to a downward-closed set of ids `P`. -/
noncomputable def restrict (j : Hist Tx) (P : Nat → Prop)
    (hP : ∀ x y, j.lt x y → P y → P x) : Hist Tx where
  lab e := if P e then j.lab e else none
  lt x y := j.lt x y ∧ P y
  lt_ev := by
    intro a b ⟨hl, hb⟩
    have ha := hP a b hl hb
    simp only [ha, hb, ite_true]
    exact j.lt_ev hl
  lt_num := fun h => j.lt_num h.1
  lt_trans := fun h₁ h₂ => ⟨j.lt_trans h₁.1 h₂.1, h₂.2⟩
  fin := by
    obtain ⟨n, hn⟩ := j.fin
    exact ⟨n, fun e he => by by_cases h : P e <;> simp [h, hn e he]⟩

theorem restrict_ev {j : Hist Tx} {P : Nat → Prop} {hP} {e : Nat} :
    (j.restrict P hP).ev e ↔ P e ∧ j.ev e := by
  unfold ev restrict
  by_cases h : P e <;> simp [h]

theorem restrict_le (j : Hist Tx) (P : Nat → Prop) (hP) : j.restrict P hP ≼ j := by
  refine ⟨fun e t h => ?_, fun x y => ?_⟩
  · simp only [restrict] at h
    by_cases hp : P e
    · simp [hp] at h; exact h
    · simp [hp] at h
  · show j.lt x y ∧ P y ↔ j.lt x y ∧ (j.restrict P hP).ev y
    rw [restrict_ev]
    exact ⟨fun h => ⟨h.1, h.2, ev_of_lt_right h.1⟩, fun h => ⟨h.1, h.2.1⟩⟩

/-- Every sub-history of `j` is a restriction of `j` to a downward-closed set. -/
theorem down_of_le {c j : Hist Tx} (hc : c ≼ j) : ∀ x y, j.lt x y → c.ev y → c.ev x :=
  fun _ _ hl hy => le_down hc hl hy

/-- The empty history. -/
def empty : Hist Tx where
  lab _ := none
  lt _ _ := False
  lt_ev h := h.elim
  lt_num h := h.elim
  lt_trans h := h.elim
  fin := ⟨0, fun _ _ => rfl⟩

theorem empty_noev (e : Nat) : ¬ (empty : Hist Tx).ev e := by simp [ev, empty]

theorem empty_le (j : Hist Tx) : (empty : Hist Tx) ≼ j :=
  ⟨fun _ _ h => by simp [empty] at h, fun _ _ => ⟨fun h => h.elim, fun h => (empty_noev _ h.2).elim⟩⟩

end Hist

/-! ## Validity and the specification `S_I` -/

section Valid
variable (M : Model V Tx)

/-- Valid: every downward-closed sub-history evaluates to a valid state. -/
def Valid (g : Hist Tx) : Prop := ∀ c, c ≼ g → M.Inv (eval M c)

/-- Locally valid: every transaction step preserves the invariant. -/
def LocValid (h : Hist Tx) : Prop :=
  ∀ e, h.ev e → M.Inv (pre M h e) ∧ M.Inv (post M h e)

theorem valid_sub {g c : Hist Tx} (hg : Valid M g) (hc : c ≼ g) : Valid M c :=
  fun d hd => hg d (PO.trans hd hc)

theorem eval_restrict (j : Hist Tx) (P : Nat → Prop) (hP) (v : V) :
    eval M (j.restrict P hP) v ↔ M.s0 v ∨ ∃ e, (P e ∧ j.ev e) ∧ post M j e v := by
  rw [eval_sub M (Hist.restrict_le j P hP)]
  simp only [Hist.restrict_ev]

theorem downset_closed (h : Hist Tx) (e : Nat) :
    ∀ x y, h.lt x y → h.lt y e → h.lt x e := fun _ _ h₁ h₂ => h.lt_trans h₁ h₂

theorem downset'_closed (h : Hist Tx) (e : Nat) :
    ∀ x y, h.lt x y → (h.lt y e ∨ y = e) → (h.lt x e ∨ x = e) := by
  rintro x y hl (h' | rfl)
  · exact Or.inl (h.lt_trans hl h')
  · exact Or.inl hl

/-- `pre(e)` is the state of the strict down-set of `e` (uses transitivity). -/
theorem pre_eq_eval (h : Hist Tx) (e : Nat) :
    pre M h e = eval M (h.restrict (fun x => h.lt x e) (downset_closed h e)) := by
  funext v; apply propext
  rw [eval_restrict]; unfold pre
  exact ⟨fun h' => h'.elim Or.inl fun ⟨x, hl, hp⟩ => Or.inr ⟨x, ⟨hl, Hist.ev_of_lt_left hl⟩, hp⟩,
    fun h' => h'.elim Or.inl fun ⟨x, hl, hp⟩ => Or.inr ⟨x, hl.1, hp⟩⟩

/-- `post(e)` is the state of the down-set of `e` (uses inflationarity). -/
theorem post_eq_eval (h : Hist Tx) (e : Nat) (he : h.ev e) :
    post M h e = eval M (h.restrict (fun x => h.lt x e ∨ x = e) (downset'_closed h e)) := by
  funext v; apply propext
  rw [eval_restrict]
  constructor
  · intro hp; exact Or.inr ⟨e, ⟨Or.inr rfl, he⟩, hp⟩
  · rintro (h0 | ⟨x, ⟨hx | rfl, _⟩, hp⟩)
    · exact pre_sub_post M h e v (Or.inl h0)
    · exact pre_sub_post M h e v (Or.inr ⟨x, hx, hp⟩)
    · exact hp

theorem valid_locValid {h : Hist Tx} (hv : Valid M h) : LocValid M h := by
  intro e he
  refine ⟨?_, ?_⟩
  · rw [pre_eq_eval]; exact hv _ (Hist.restrict_le _ _ _)
  · rw [post_eq_eval M h e he]; exact hv _ (Hist.restrict_le _ _ _)

theorem valid_empty : Valid M (Hist.empty : Hist Tx) := by
  intro c hc
  have : ∀ e, ¬ c.ev e := fun e he => Hist.empty_noev e (Hist.le_ev hc he)
  rw [eval_noev M this]; exact M.init

/-- The state of a valid history is reachable (paper, first step of the proof). -/
theorem valid_reach {g : Hist Tx} (hg : Valid M g) : Reach M (eval M g) := by
  have key : ∀ k, ∀ c, c ≼ g → (∀ e, c.ev e → e < k) → Reach M (eval M c) := by
    intro k
    induction k with
    | zero =>
      intro c _ hb
      rw [eval_noev M (fun e he => absurd (hb e he) (Nat.not_lt_zero e))]
      exact Reach.init
    | succ k ih =>
      intro c hc hb
      by_cases hk : c.ev k
      · -- `k` is maximal in `c`
        have hcl : ∀ x y, c.lt x y → y < k → x < k := fun _ _ hl hy =>
          Nat.lt_trans (c.lt_num hl) hy
        let c' := c.restrict (fun x => x < k) hcl
        have hc' : c' ≼ g := PO.trans (Hist.restrict_le _ _ _) hc
        have r' : Reach M (eval M c') :=
          ih c' hc' fun e he => (Hist.restrict_ev.1 he).1
        let p := c.restrict (fun x => c.lt x k) (downset_closed c k)
        have rp : Reach M (eval M p) :=
          ih p (PO.trans (Hist.restrict_le _ _ _) hc)
            fun e he => c.lt_num (Hist.restrict_ev.1 he).1
        have hpre : pre M c k = eval M p := pre_eq_eval M c k
        have ipost : M.Inv (post M c k) := by
          rw [post_eq_eval M c k hk]; exact hg _ (PO.trans (Hist.restrict_le _ _ _) hc)
        obtain ⟨t, ht⟩ : ∃ t, c.lab k = some t := by
          unfold Hist.ev at hk; cases h : c.lab k with
          | none => exact absurd h hk
          | some t => exact ⟨t, rfl⟩
        have hpost : post M c k = M.app t (eval M p) := by
          rw [post_eq, ht, hpre]; rfl
        have rpost : Reach M (post M c k) := by
          rw [hpost]; refine Reach.tx t rp ?_; rw [← hpost]; exact ipost
        have hsplit : eval M c = (eval M c').union (post M c k) := by
          funext v; apply propext; unfold St.union
          rw [eval_restrict]; unfold eval
          constructor
          · rintro (h0 | ⟨e, he, hp⟩)
            · exact Or.inl (Or.inl h0)
            · by_cases hek : e < k
              · exact Or.inl (Or.inr ⟨e, ⟨hek, he⟩, hp⟩)
              · have : e = k := by have := hb e he; omega
                subst this; exact Or.inr hp
          · rintro ((h0 | ⟨e, ⟨_, he⟩, hp⟩) | hp)
            · exact Or.inl h0
            · exact Or.inr ⟨e, he, hp⟩
            · exact Or.inr ⟨k, hk, hp⟩
        rw [hsplit]
        refine Reach.merge r' rpost ?_
        rw [← hsplit]; exact hg c hc
      · exact ih c hc fun e he => by
          have := hb e he
          have : e ≠ k := fun h => hk (h ▸ he)
          omega
  obtain ⟨n, hn⟩ := g.fin
  exact key n g (PO.refl g) fun e he => by
    false_or_by_contra
    exact he (hn e (by omega))

end Valid

/-- Inputs of `S_I`: locally valid histories, ordered by expansion. -/
def Inp (M : Model V Tx) := {h : Hist Tx // LocValid M h}

instance (M : Model V Tx) : PO (Inp M) where
  le a b := a.1 ≼ b.1
  refl a := PO.refl a.1
  trans h₁ h₂ := PO.trans h₁ h₂
  antisymm h₁ h₂ := Subtype.ext (PO.antisymm h₁ h₂)

theorem Inp.le_def {M : Model V Tx} (a b : Inp M) : (a ≼ b) = (a.1 ≼ b.1) := rfl

/-- The specification `S_I`: at input `h`, expose the state of any
downward-closed valid sub-history of `h`. -/
def SI (M : Model V Tx) : Spec (Inp M) (St V) where
  S h s := ∃ g, g ≼ h.1 ∧ Valid M g ∧ eval M g = s
  total _ := ⟨_, Hist.empty, Hist.empty_le _, valid_empty M, rfl⟩

/-! ## (⇒) Invariant confluence gives the common-expansion condition -/

section Forward
variable (M : Model V Tx)

/-- Under invariant confluence, the union of two valid sub-histories of `j`
is valid. -/
theorem union_valid (hic : M.IConfluent) {j g₁ g₂ : Hist Tx} (h₁ : g₁ ≼ j) (h₂ : g₂ ≼ j)
    (v₁ : Valid M g₁) (v₂ : Valid M g₂) :
    Valid M (j.restrict (fun e => g₁.ev e ∨ g₂.ev e) (fun _ _ hl hy =>
      hy.elim (fun h => Or.inl (Hist.le_down h₁ hl h)) (fun h => Or.inr (Hist.le_down h₂ hl h)))) := by
  intro c hc
  have hcj : c ≼ j := PO.trans hc (Hist.restrict_le _ _ _)
  let a := j.restrict (fun e => c.ev e ∧ g₁.ev e)
    (fun x y hl hy => ⟨Hist.le_down hcj hl hy.1, Hist.le_down h₁ hl hy.2⟩)
  let b := j.restrict (fun e => c.ev e ∧ g₂.ev e)
    (fun x y hl hy => ⟨Hist.le_down hcj hl hy.1, Hist.le_down h₂ hl hy.2⟩)
  have ha : a ≼ g₁ := Hist.le_of_sub (Hist.restrict_le _ _ _) h₁
    fun e he => (Hist.restrict_ev.1 he).1.2
  have hb : b ≼ g₂ := Hist.le_of_sub (Hist.restrict_le _ _ _) h₂
    fun e he => (Hist.restrict_ev.1 he).1.2
  have hsplit : eval M c = (eval M a).union (eval M b) := by
    refine eval_union M (Hist.restrict_le _ _ _) (Hist.restrict_le _ _ _) hcj fun e => ?_
    simp only [a, b, Hist.restrict_ev]
    constructor
    · intro he
      have hu := Hist.le_ev hc he
      rw [Hist.restrict_ev] at hu
      rcases hu.1 with h | h
      · exact Or.inl ⟨⟨he, h⟩, hu.2⟩
      · exact Or.inr ⟨⟨he, h⟩, hu.2⟩
    · rintro (⟨⟨h, _⟩, _⟩ | ⟨⟨h, _⟩, _⟩) <;> exact h
  rw [hsplit]
  exact hic _ _ (valid_reach M (valid_sub M v₁ ha)) (valid_reach M (valid_sub M v₂ hb))

theorem ic_commonExpansion (hic : M.IConfluent) : (SI M).CommonExpansion := by
  intro rows hrows j hj
  have key : ∃ g, g ≼ j.1 ∧ Valid M g ∧ ∀ r ∈ rows, r.2 ≼ eval M g := by
    induction rows with
    | nil => exact ⟨Hist.empty, Hist.empty_le _, valid_empty M, fun _ h => nomatch h⟩
    | cons r rest ih =>
      obtain ⟨g, hg, vg, hgr⟩ :=
        ih (fun r h => hrows r (List.mem_cons_of_mem _ h)) (fun r h => hj r (List.mem_cons_of_mem _ h))
      obtain ⟨g', hg', vg', hev⟩ := hrows r (List.mem_cons_self ..)
      have hg'j : g' ≼ j.1 := PO.trans hg' (hj r (List.mem_cons_self ..))
      refine ⟨_, Hist.restrict_le _ _ _, union_valid M hic hg hg'j vg vg', ?_⟩
      intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · rw [← hev]
        exact eval_mono M (Hist.le_of_sub hg'j (Hist.restrict_le _ _ _)
          fun e he => Hist.restrict_ev.2 ⟨Or.inr he, Hist.le_ev hg'j he⟩)
      · exact PO.trans (hgr r' hr') (eval_mono M (Hist.le_of_sub hg (Hist.restrict_le _ _ _)
          fun e he => Hist.restrict_ev.2 ⟨Or.inl he, Hist.le_ev hg he⟩))
  obtain ⟨g, hg, vg, hgr⟩ := key
  exact ⟨eval M g, ⟨g, hg, vg, rfl⟩, hgr⟩

end Forward

/-! ## Disjoint union and adding a top event -/

namespace Hist

/-- The part of a disjoint union holding id `n`: even ids come from `g₁`,
odd ids from `g₂`. -/
def side (g₁ g₂ : Hist Tx) (n : Nat) : Hist Tx := if n % 2 = 0 then g₁ else g₂

theorem side_mod (g₁ g₂ : Hist Tx) (n : Nat) : side g₁ g₂ (n % 2) = side g₁ g₂ n := by
  unfold side; simp

theorem side_congr (g₁ g₂ : Hist Tx) {x y : Nat} (h : x % 2 = y % 2) :
    side g₁ g₂ x = side g₁ g₂ y := by
  rw [← side_mod, h, side_mod]

theorem side_cases (g₁ g₂ : Hist Tx) (P : Hist Tx → Prop) (h₁ : P g₁) (h₂ : P g₂) (n : Nat) :
    P (side g₁ g₂ n) := by
  unfold side; split <;> assumption

theorem side_lin (g₁ g₂ : Hist Tx) {k : Nat} (_hk : k < 2) (e : Nat) :
    side g₁ g₂ (2 * e + k) = side g₁ g₂ k :=
  side_congr g₁ g₂ (by omega)

/-- Disjoint union, with no order between the two parts. -/
def dunion (g₁ g₂ : Hist Tx) : Hist Tx where
  lab n := (side g₁ g₂ n).lab (n / 2)
  lt x y := x % 2 = y % 2 ∧ (side g₁ g₂ y).lt (x / 2) (y / 2)
  lt_ev := by
    intro a b ⟨hp, hl⟩
    rw [side_congr g₁ g₂ hp]
    exact (side g₁ g₂ b).lt_ev hl
  lt_num := by
    intro a b ⟨hp, hl⟩
    have := (side g₁ g₂ b).lt_num hl
    omega
  lt_trans := by
    intro a b c ⟨hp₁, hl₁⟩ ⟨hp₂, hl₂⟩
    rw [side_congr g₁ g₂ hp₂] at hl₁
    exact ⟨hp₁.trans hp₂, (side g₁ g₂ c).lt_trans hl₁ hl₂⟩
  fin := by
    obtain ⟨n₁, h₁⟩ := g₁.fin
    obtain ⟨n₂, h₂⟩ := g₂.fin
    refine ⟨2 * (n₁ + n₂), fun e he => ?_⟩
    unfold side; split
    · exact h₁ _ (by omega)
    · exact h₂ _ (by omega)

theorem dunion_lab (g₁ g₂ : Hist Tx) {k : Nat} (hk : k < 2) (e : Nat) :
    (dunion g₁ g₂).lab (2 * e + k) = (side g₁ g₂ k).lab e := by
  show (side g₁ g₂ (2 * e + k)).lab ((2 * e + k) / 2) = _
  rw [side_lin g₁ g₂ hk]; congr 1; omega

theorem dunion_lt (g₁ g₂ : Hist Tx) {k : Nat} (hk : k < 2) (x y : Nat) :
    (dunion g₁ g₂).lt (2 * x + k) (2 * y + k) ↔ (side g₁ g₂ k).lt x y := by
  show (_ ∧ (side g₁ g₂ (2 * y + k)).lt ((2 * x + k) / 2) ((2 * y + k) / 2)) ↔ _
  rw [side_lin g₁ g₂ hk]
  have h1 : (2 * x + k) / 2 = x := by omega
  have h2 : (2 * y + k) / 2 = y := by omega
  rw [h1, h2]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

theorem dunion_par {g₁ g₂ : Hist Tx} {n m : Nat} (h : (dunion g₁ g₂).lt n m) : n % 2 = m % 2 :=
  h.1

/-- The `k`-th part (`k < 2`) of a history whose order respects parity. -/
def half (c : Hist Tx) (k : Nat) : Hist Tx where
  lab e := c.lab (2 * e + k)
  lt x y := c.lt (2 * x + k) (2 * y + k)
  lt_ev h := c.lt_ev h
  lt_num h := by have := c.lt_num h; omega
  lt_trans h₁ h₂ := c.lt_trans h₁ h₂
  fin := by
    obtain ⟨n, hn⟩ := c.fin
    exact ⟨n, fun e he => hn _ (by omega)⟩

theorem half_ev {c : Hist Tx} {k e : Nat} : (half c k).ev e ↔ c.ev (2 * e + k) := Iff.rfl

theorem half_le {g₁ g₂ c : Hist Tx} (hc : c ≼ dunion g₁ g₂) {k : Nat} (hk : k < 2) :
    half c k ≼ side g₁ g₂ k := by
  refine ⟨fun e t h => ?_, fun x y => ?_⟩
  · rw [← dunion_lab g₁ g₂ hk]; exact hc.1 _ t h
  · show c.lt (2 * x + k) (2 * y + k) ↔ _
    rw [hc.2, dunion_lt g₁ g₂ hk]; rfl

theorem half_dunion (g₁ g₂ : Hist Tx) {k : Nat} (hk : k < 2) :
    half (dunion g₁ g₂) k = side g₁ g₂ k := by
  apply ext'
  · funext e; exact dunion_lab g₁ g₂ hk e
  · funext x y; exact propext (dunion_lt g₁ g₂ hk x y)

/-- Adding an event labeled `t` above all events of `g`. -/
noncomputable def addTop (g : Hist Tx) (t : Tx) : Hist Tx where
  lab e := if e = Classical.choose g.fin then some t else g.lab e
  lt x y := g.lt x y ∨ (y = Classical.choose g.fin ∧ g.ev x)
  lt_ev := by
    have hb := Classical.choose_spec g.fin
    have hn : ∀ e, g.ev e → e ≠ Classical.choose g.fin := fun e he h =>
      he (hb e (by omega))
    rintro a b (hl | ⟨rfl, ha⟩)
    · have ⟨h₁, h₂⟩ := g.lt_ev hl
      simp only [hn a h₁, hn b h₂, ite_false]; exact ⟨h₁, h₂⟩
    · simp only [hn a ha, ite_false, ite_true]; exact ⟨ha, by simp⟩
  lt_num := by
    have hb := Classical.choose_spec g.fin
    rintro a b (hl | ⟨rfl, ha⟩)
    · exact g.lt_num hl
    · false_or_by_contra; exact ha (hb a (by omega))
  lt_trans := by
    have hb := Classical.choose_spec g.fin
    rintro a b c (h₁ | ⟨rfl, _⟩) (h₂ | ⟨rfl, h₂⟩)
    · exact Or.inl (g.lt_trans h₁ h₂)
    · exact Or.inr ⟨rfl, ev_of_lt_left h₁⟩
    · exact absurd (hb _ (Nat.le_refl _)) (ev_of_lt_left h₂)
    · exact absurd (hb _ (Nat.le_refl _)) h₂
  fin := by
    obtain hb := Classical.choose_spec g.fin
    refine ⟨Classical.choose g.fin + 1, fun e he => ?_⟩
    have : e ≠ Classical.choose g.fin := by omega
    simp only [this, ite_false]; exact hb e (by omega)

theorem top_bound (g : Hist Tx) {e : Nat} (he : g.ev e) : e < Classical.choose g.fin := by
  false_or_by_contra; exact he (Classical.choose_spec g.fin e (by omega))

theorem addTop_ev (g : Hist Tx) (t : Tx) (e : Nat) :
    (addTop g t).ev e ↔ g.ev e ∨ e = Classical.choose g.fin := by
  unfold ev addTop
  by_cases h : e = Classical.choose g.fin
  · simp [h]
  · simp [h]

theorem le_addTop (g : Hist Tx) (t : Tx) : g ≼ addTop g t := by
  refine ⟨fun e t' h => ?_, fun x y => ?_⟩
  · have : e ≠ Classical.choose g.fin := Nat.ne_of_lt (top_bound g (by unfold ev; rw [h]; simp))
    show (if _ then _ else _) = _
    simp only [this, ite_false]; exact h
  · show g.lt x y ↔ (g.lt x y ∨ (y = _ ∧ g.ev x)) ∧ g.ev y
    constructor
    · intro h; exact ⟨Or.inl h, ev_of_lt_right h⟩
    · rintro ⟨h | ⟨rfl, _⟩, hy⟩
      · exact h
      · exact absurd (top_bound g hy) (Nat.lt_irrefl _)

end Hist

/-! ## (⇐) Lifted Monotonicity gives invariant confluence -/

section Backward
variable (M : Model V Tx)
open Hist

theorem post_half {g₁ g₂ c : Hist Tx} (hc : c ≼ dunion g₁ g₂) {k : Nat} (hk : k < 2)
    {e : Nat} (he : (half c k).ev e) : post M (half c k) e = post M c (2 * e + k) :=
  (pre_post_map M (half c k) c (fun e => 2 * e + k) (fun _ _ => rfl) (fun _ _ _ => Iff.rfl)
    (fun n y _ hl => by
      have := dunion_par ((hc.2 n _).1 hl).1
      exact ⟨n / 2, by omega⟩) e he).2

/-- A sub-history of a disjoint union all of whose events lie in part `k`
has the state of its `k`-th half. -/
theorem eval_half_k {g₁ g₂ c : Hist Tx} (hc : c ≼ dunion g₁ g₂) {k : Nat} (hk : k < 2)
    (hpar : ∀ n, c.ev n → n % 2 = k) : eval M c = eval M (half c k) := by
  funext v; apply propext; unfold eval
  constructor
  · rintro (h0 | ⟨n, hn, hp⟩)
    · exact Or.inl h0
    · have hn' : n = 2 * (n / 2) + k := by have := hpar n hn; omega
      rw [hn'] at hn hp
      exact Or.inr ⟨n / 2, hn, by rw [post_half M hc hk hn]; exact hp⟩
  · rintro (h0 | ⟨e, he, hp⟩)
    · exact Or.inl h0
    · exact Or.inr ⟨_, he, by rw [← post_half M hc hk he]; exact hp⟩

/-- The state of a sub-history of a disjoint union is the union of the states
of its two halves. -/
theorem eval_half {g₁ g₂ c : Hist Tx} (hc : c ≼ dunion g₁ g₂) :
    eval M c = (eval M (half c 0)).union (eval M (half c 1)) := by
  funext v; apply propext; unfold St.union eval
  constructor
  · rintro (h0 | ⟨n, hn, hp⟩)
    · exact Or.inl (Or.inl h0)
    · rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have hn' : n = 2 * (n / 2) + 0 := by omega
        rw [hn'] at hn hp
        exact Or.inl (Or.inr ⟨n / 2, hn, by rw [post_half M hc (by omega) hn]; exact hp⟩)
      · have hn' : n = 2 * (n / 2) + 1 := by omega
        rw [hn'] at hn hp
        exact Or.inr (Or.inr ⟨n / 2, hn, by rw [post_half M hc (by omega) hn]; exact hp⟩)
  · rintro ((h0 | ⟨e, he, hp⟩) | (h0 | ⟨e, he, hp⟩))
    · exact Or.inl h0
    · exact Or.inr ⟨_, he, by rw [← post_half M hc (by omega) he]; exact hp⟩
    · exact Or.inl h0
    · exact Or.inr ⟨_, he, by rw [← post_half M hc (by omega) he]; exact hp⟩

theorem eval_dunion (g₁ g₂ : Hist Tx) :
    eval M (dunion g₁ g₂) = (eval M g₁).union (eval M g₂) := by
  rw [eval_half M (PO.refl _), half_dunion g₁ g₂ (by omega : 0 < 2),
    half_dunion g₁ g₂ (by omega : 1 < 2)]
  rfl

theorem locValid_dunion {g₁ g₂ : Hist Tx} (h₁ : LocValid M g₁) (h₂ : LocValid M g₂) :
    LocValid M (dunion g₁ g₂) := by
  intro n hn
  have hk : n % 2 < 2 := Nat.mod_lt _ (by omega)
  have hn' : n = 2 * (n / 2) + n % 2 := by omega
  have hl : LocValid M (side g₁ g₂ (n % 2)) := side_cases g₁ g₂ _ h₁ h₂ _
  have hev : (side g₁ g₂ (n % 2)).ev (n / 2) := by
    rw [hn'] at hn; unfold ev at hn ⊢; rwa [dunion_lab g₁ g₂ hk] at hn
  have hm := pre_post_map M (side g₁ g₂ (n % 2)) (dunion g₁ g₂) (fun e => 2 * e + n % 2)
    (fun e _ => dunion_lab g₁ g₂ hk e) (fun x y _ => (dunion_lt g₁ g₂ hk x y).symm)
    (fun m y _ hl => by have := dunion_par hl; exact ⟨m / 2, by omega⟩) (n / 2) hev
  rw [hn', ← hm.1, ← hm.2]
  exact hl _ hev

/-- Part `k` of a disjoint union, as a sub-history: it is valid, with the
state of the `k`-th component. -/
theorem part_row {g₁ g₂ : Hist Tx} {k : Nat} (hk : k < 2) (hv : Valid M (side g₁ g₂ k)) :
    ∃ L, L ≼ dunion g₁ g₂ ∧ Valid M L ∧ eval M L = eval M (side g₁ g₂ k) := by
  let L := (dunion g₁ g₂).restrict (fun n => n % 2 = k)
    (fun x y hl hy => (dunion_par hl).trans hy)
  have hL : L ≼ dunion g₁ g₂ := restrict_le _ _ _
  have hpar : ∀ c, c ≼ L → ∀ n, c.ev n → n % 2 = k := fun c hc n hn =>
    (restrict_ev.1 (le_ev hc hn)).1
  have hhalf : half L k = side g₁ g₂ k := by
    apply PO.antisymm (half_le hL hk)
    refine le_of_sub (Hist.le_refl _) (half_le hL hk) fun e he => ?_
    rw [half_ev, restrict_ev]
    refine ⟨by omega, ?_⟩
    unfold ev; rw [dunion_lab g₁ g₂ hk]; exact he
  refine ⟨L, hL, fun c hc => ?_, ?_⟩
  · have hcj : c ≼ dunion g₁ g₂ := PO.trans hc hL
    rw [eval_half_k M hcj hk (hpar c hc)]
    exact hv _ (half_le hcj hk)
  · rw [eval_half_k M hL hk (hpar L (PO.refl _)), hhalf]

theorem side_zero (g₁ g₂ : Hist Tx) : side g₁ g₂ 0 = g₁ := rfl
theorem side_one (g₁ g₂ : Hist Tx) : side g₁ g₂ 1 = g₂ := rfl

/-- The pairwise argument: under Lifted Monotonicity (in fact, Directed
Outputs suffices), the union of the states of two valid histories is valid. -/
theorem pair_inv (hlm : (SI M).LiftedMono) {g₁ g₂ : Hist Tx} (v₁ : Valid M g₁)
    (v₂ : Valid M g₂) : M.Inv ((eval M g₁).union (eval M g₂)) := by
  let J : Inp M := ⟨dunion g₁ g₂,
    locValid_dunion M (valid_locValid M v₁) (valid_locValid M v₂)⟩
  obtain ⟨L₁, hL₁, vL₁, eL₁⟩ := part_row M (g₁ := g₁) (g₂ := g₂) (k := 0) (by omega) v₁
  obtain ⟨L₂, hL₂, vL₂, eL₂⟩ := part_row M (g₁ := g₁) (g₂ := g₂) (k := 1) (by omega) v₂
  rw [side_zero] at eL₁; rw [side_one] at eL₂
  obtain ⟨u, ⟨g, hg, vg, rfl⟩, hu⟩ := hlm J J (PO.refl J) [eval M g₁, eval M g₂]
    (by simp) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨L₁, hL₁, vL₁, eL₁⟩
      · exact ⟨L₂, hL₂, vL₂, eL₂⟩)
  have h₁ := hu _ (List.mem_cons_self ..)
  have h₂ := hu _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have heq : eval M g = (eval M g₁).union (eval M g₂) := by
    apply PO.antisymm
    · rw [← eval_dunion]; exact eval_mono M hg
    · intro v hv; exact hv.elim (h₁ v) (h₂ v)
  rw [← heq]; exact vg _ (PO.refl _)

/-- Under Lifted Monotonicity, valid histories are closed under disjoint union. -/
theorem valid_dunion (hlm : (SI M).LiftedMono) {g₁ g₂ : Hist Tx} (v₁ : Valid M g₁)
    (v₂ : Valid M g₂) : Valid M (dunion g₁ g₂) := by
  intro c hc
  rw [eval_half M hc]
  exact pair_inv M hlm (valid_sub M v₁ (half_le hc (by omega : 0 < 2)))
    (valid_sub M v₂ (half_le hc (by omega : 1 < 2)))

theorem pre_addTop (g : Hist Tx) (t : Tx) :
    pre M (addTop g t) (Classical.choose g.fin) = eval M g := by
  funext v; apply propext; unfold pre eval
  have hsub := le_addTop g t
  constructor
  · rintro (h0 | ⟨x, hl | ⟨_, hx⟩, hp⟩)
    · exact Or.inl h0
    · exact absurd (top_bound g (ev_of_lt_right hl)) (Nat.lt_irrefl _)
    · exact Or.inr ⟨x, hx, by rw [post_sub M hsub hx]; exact hp⟩
  · rintro (h0 | ⟨x, hx, hp⟩)
    · exact Or.inl h0
    · exact Or.inr ⟨x, Or.inr ⟨rfl, hx⟩, by rw [← post_sub M hsub hx]; exact hp⟩

theorem post_addTop (g : Hist Tx) (t : Tx) :
    post M (addTop g t) (Classical.choose g.fin) = M.app t (eval M g) := by
  rw [post_eq, pre_addTop]
  show step M (if _ then _ else _) _ = _
  simp only [ite_true]; rfl

theorem eval_addTop (g : Hist Tx) (t : Tx) : eval M (addTop g t) = M.app t (eval M g) := by
  funext v; apply propext
  have hsub := le_addTop g t
  constructor
  · rintro (h0 | ⟨e, he, hp⟩)
    · exact M.infl t _ v (Or.inl h0)
    · rcases (addTop_ev g t e).1 he with he' | rfl
      · rw [← post_sub M hsub he'] at hp
        exact M.infl t _ v (Or.inr ⟨e, he', hp⟩)
      · rwa [post_addTop] at hp
  · intro hv
    exact Or.inr ⟨_, (addTop_ev g t _).2 (Or.inr rfl), by rw [post_addTop]; exact hv⟩

theorem valid_addTop {g : Hist Tx} (hg : Valid M g) (t : Tx) (hi : M.Inv (M.app t (eval M g))) :
    Valid M (addTop g t) := by
  intro c hc
  have hsub := le_addTop g t
  by_cases hn : c.ev (Classical.choose g.fin)
  · have : addTop g t = c := by
      refine PO.antisymm (le_of_sub (Hist.le_refl _) hc fun e he => ?_) hc
      rcases (addTop_ev g t e).1 he with he' | rfl
      · exact ev_of_lt_left ((hc.2 e _).2 ⟨Or.inr ⟨rfl, he'⟩, hn⟩)
      · exact hn
    rw [← this, eval_addTop]; exact hi
  · refine hg c (le_of_sub hc hsub fun e he => ?_)
    rcases (addTop_ev g t e).1 (le_ev hc he) with he' | rfl
    · exact he'
    · exact absurd he hn

/-- Under Lifted Monotonicity, every reachable state is the state of a valid
history. -/
theorem reach_valid (hlm : (SI M).LiftedMono) {s : St V} (hs : Reach M s) :
    ∃ g, Valid M g ∧ eval M g = s := by
  induction hs with
  | init => exact ⟨empty, valid_empty M, eval_noev M empty_noev⟩
  | tx t _ hi ih =>
    obtain ⟨g, vg, rfl⟩ := ih
    exact ⟨addTop g t, valid_addTop M vg t hi, eval_addTop M g t⟩
  | merge _ _ _ ih₁ ih₂ =>
    obtain ⟨g₁, v₁, rfl⟩ := ih₁
    obtain ⟨g₂, v₂, rfl⟩ := ih₂
    exact ⟨dunion g₁ g₂, valid_dunion M hlm v₁ v₂, eval_dunion M g₁ g₂⟩

theorem lm_ic (hlm : (SI M).LiftedMono) : M.IConfluent := by
  intro s₁ s₂ h₁ h₂
  obtain ⟨g₁, v₁, rfl⟩ := reach_valid M hlm h₁
  obtain ⟨g₂, v₂, rfl⟩ := reach_valid M hlm h₂
  exact pair_inv M hlm v₁ v₂

end Backward

/-! ## Proposition `prop:iconfluence-lm` -/

/-- The common-expansion condition implies Lifted Monotonicity (the easy
direction of Prop. `common-expansion-form`, proved here for any spec). -/
theorem commonExpansion_liftedMono {I O : Type} [PO I] [PO O] (sp : Spec I O)
    (h : sp.CommonExpansion) : sp.LiftedMono := by
  intro i j hij X _ hX
  obtain ⟨u, hu, hX'⟩ := h (X.map fun x => (i, x))
    (fun r hr => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
      exact hX x hx)
    j (fun r hr => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.1 hr
      exact hij)
  exact ⟨u, hu, fun x hx => hX' (i, x) (List.mem_map.2 ⟨x, hx, rfl⟩)⟩

/-- **Proposition `prop:iconfluence-lm`.** `T` is invariant confluent iff
`S_I` satisfies Lifted Monotonicity. -/
theorem ic_iff_liftedMono (M : Model V Tx) : M.IConfluent ↔ (SI M).LiftedMono :=
  ⟨fun h => commonExpansion_liftedMono _ (ic_commonExpansion M h), lm_ic M⟩

/-- The same with the common-expansion form of Lifted Monotonicity. -/
theorem ic_iff_commonExpansion (M : Model V Tx) : M.IConfluent ↔ (SI M).CommonExpansion :=
  ⟨ic_commonExpansion M, fun h => lm_ic M (commonExpansion_liftedMono _ h)⟩

/-- In fact Directed Outputs (the `i = j` case of Lifted Monotonicity) already
implies invariant confluence for `S_I`; we record that `pair_inv` only uses it. -/
theorem directed_ic (M : Model V Tx) (h : (SI M).DirectedOutputs) : M.IConfluent := by
  apply lm_ic M
  intro i j hij X hne hX
  exact h j X hne fun x hx => by
    obtain ⟨g, hg, vg, rfl⟩ := hX x hx
    exact ⟨g, PO.trans hg hij, vg, rfl⟩

end IConf
end CC
