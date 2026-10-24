/-
# Audit F (part 1): Appendix `app:cc-bases`

Commitment bases for two-phase locking (2PL) and multiversion timestamp
ordering (MVTO).

* `FinSet`, `Outcome`, `txnSpec`, `abortFreeSpec` — the specification
  (inputs: finite sets of transactions under inclusion; outputs `(L,X)` under
  `X ⊆ X'`, `dom L ⊆ dom L'`, `L'|dom L = L`; rows: `X`, `dom L` partition the
  input).  `abortFreeSpec` is "the same rows with `X = ∅`".
* `ab_ba_no_common_refinement`, `txnSpec_not_liftedMono`,
  `abortFreeSpec_not_liftedMono` — "the rows `([A,B],∅)` and `([B,A],∅)` have no
  common refinement, so the specification is not monotone".
* `partitions_antichain` — the appendix's argument: at a fixed input a
  permitted output that refines another equals it.
* `filterC` — any row filter, defined when some row at the current input
  satisfies it and some row of `R` fails it, is a commitment
  (Def. `def:commitment`, Eq. `commitment-excludes`) in a specification whose
  fibers are antichains; `filterC_app_iff` is the definedness/effect statement.
* `orderC`, `commitC`, `abortC`, `stampC`, `basis2PL`, `basisMVTO` — the
  commitments and bases, for either specification.
* `deadlock_rows`, `deadlock_state`, `deadlock_forces_abort` — 2PL deadlock.
* `abortFree_order_blocks`, `abortFree_order_blocks_forever` — under the
  abort-free specification `order(B,A)` is undefined once `order(A,B)` is
  applied, at every later state.
* `orderP_abortFree`, `stampP_first_abortFree` — Fig. `fig:cc-commitments`
  (h) is `order(A,B)`, (i) is `stamp(B)` with `Z = ∅`.
* `stamp_order_row` — MVTO: the abort-free row ordered by the stamps satisfies
  every `stamp` and `commit` condition, so the specification does not itself
  force an abort.
* `exposable_iff_refines` — in an antichain-fiber specification, `o` is
  exposable at `σ` iff every remaining row refines `o` (what
  Prop. `prop:exposability` decides here).

Modeling choices: outputs `(L,X)` are arbitrary (not necessarily finite)
pairs of an abort set and a strict total order on `dom L`; finiteness of
inputs is witnessed by a duplicate-free list.  The guards "distinct
`A,B ∈ i`" (order) and "`Z ⊆ i`" (stamp) are part of definedness.
-/
import CoordCriterion.Commitments
import CoordCriterion.CompleteCALM

namespace CC
namespace AuditF

/-! ### Finite sets ordered by inclusion -/

/-- A finite set, presented by a duplicate-free list of its elements. -/
def FinSet (α : Type) : Type := {s : α → Prop // ∃ l : List α, l.Nodup ∧ ∀ x, s x ↔ x ∈ l}

instance instPOFinSet (α : Type) : PO (FinSet α) where
  le a b := ∀ x, a.1 x → b.1 x
  refl _ _ h := h
  trans h1 h2 x hx := h2 x (h1 x hx)
  antisymm h1 h2 := Subtype.ext (funext fun x => propext ⟨h1 x, h2 x⟩)

/-- The finite set of the elements of a duplicate-free list. -/
def FinSet.ofList {α : Type} (l : List α) (hl : l.Nodup) : FinSet α :=
  ⟨fun x => x ∈ l, l, hl, fun _ => Iff.rfl⟩

/-! ### Outcomes `(L, X)` -/

variable {T : Type}

/-- An outcome `(L,X)`: an abort set `X` and a strict total order `lt` (the
serialization order `L`) on its domain `dom`. -/
structure Outcome (T : Type) where
  X : T → Prop
  dom : T → Prop
  lt : T → T → Prop
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ a b c, lt a b → lt b c → lt a c
  total : ∀ a b, dom a → dom b → a ≠ b → lt a b ∨ lt b a
  supp : ∀ a b, lt a b → dom a ∧ dom b

theorem Outcome.ext' {o o' : Outcome T} (hX : o.X = o'.X) (hd : o.dom = o'.dom)
    (hl : o.lt = o'.lt) : o = o' := by
  cases o; cases o'; cases hX; cases hd; cases hl; rfl

/-- `(L,X) ≼ (L',X')` iff `X ⊆ X'`, `dom L ⊆ dom L'`, `L'|dom L = L`. -/
def Outcome.le (o o' : Outcome T) : Prop :=
  (∀ t, o.X t → o'.X t) ∧ (∀ t, o.dom t → o'.dom t) ∧
    ∀ a b, o.dom a → o.dom b → (o'.lt a b ↔ o.lt a b)

instance instPOOutcome (T : Type) : PO (Outcome T) where
  le := Outcome.le
  refl _ := ⟨fun _ h => h, fun _ h => h, fun _ _ _ _ => Iff.rfl⟩
  trans h1 h2 :=
    ⟨fun t h => h2.1 t (h1.1 t h), fun t h => h2.2.1 t (h1.2.1 t h),
     fun a b da db => (h2.2.2 a b (h1.2.1 a da) (h1.2.1 b db)).trans (h1.2.2 a b da db)⟩
  antisymm {o o'} h1 h2 := by
    apply Outcome.ext'
    · funext t; exact propext ⟨h1.1 t, h2.1 t⟩
    · funext t; exact propext ⟨h1.2.1 t, h2.2.1 t⟩
    · funext a b
      apply propext
      constructor
      · intro h
        have hs := o.supp a b h
        exact (h1.2.2 a b hs.1 hs.2).2 h
      · intro h
        have hs := o'.supp a b h
        exact (h2.2.2 a b hs.1 hs.2).2 h

/-- A row `(k,(L,X))` is permitted when `X` and `dom L` partition `k`. -/
def Partitions (k : FinSet T) (o : Outcome T) : Prop :=
  ∀ t, (k.1 t ↔ (o.X t ∨ o.dom t)) ∧ ¬ (o.X t ∧ o.dom t)

/-- Abort everything. -/
def allAbort (k : FinSet T) : Outcome T where
  X := k.1
  dom _ := False
  lt _ _ := False
  irrefl _ h := h
  trans _ _ _ h _ := h
  total _ _ h _ _ := h.elim
  supp _ _ h := h.elim

/-- The serialization order given by first-occurrence positions in a list. -/
def listOrder [DecidableEq T] (l : List T) : Outcome T where
  X _ := False
  dom t := t ∈ l
  lt a b := a ∈ l ∧ b ∈ l ∧ l.idxOf a < l.idxOf b
  irrefl _ h := Nat.lt_irrefl _ h.2.2
  trans _ _ _ h1 h2 := ⟨h1.1, h2.2.1, Nat.lt_trans h1.2.2 h2.2.2⟩
  total a b ha hb hne := by
    rcases Nat.lt_trichotomy (l.idxOf a) (l.idxOf b) with h | h | h
    · exact Or.inl ⟨ha, hb, h⟩
    · exfalso; apply hne
      have e1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem ha)
      have e2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hb)
      rw [← e1, ← e2]
      simp only [h]
    · exact Or.inr ⟨hb, ha, h⟩
  supp _ _ h := ⟨h.1, h.2.1⟩

/-- **The specification** of Appendix `app:cc-bases`. -/
def txnSpec (T : Type) : Spec (FinSet T) (Outcome T) where
  S k o := Partitions k o
  total k := ⟨allAbort k, fun _ => ⟨⟨Or.inl, fun h => h.elim id False.elim⟩, fun h => h.2⟩⟩

/-- **The abort-free specification**: the same rows with `X = ∅`. -/
def abortFreeSpec (T : Type) : Spec (FinSet T) (Outcome T) where
  S k o := Partitions k o ∧ ∀ t, ¬ o.X t
  total k := by
    classical
    obtain ⟨l, _, hl⟩ := k.2
    refine ⟨listOrder l, fun t => ⟨?_, fun h => h.1⟩, fun _ h => h⟩
    rw [hl t]
    exact ⟨Or.inr, fun h => h.elim False.elim id⟩

/-! ### Not monotone -/

/-- The outcome `([A,B], ∅)`. -/
def ordPair (A B : T) (h : A ≠ B) : Outcome T where
  X _ := False
  dom t := t = A ∨ t = B
  lt a b := a = A ∧ b = B
  irrefl a hab := h (hab.1.symm.trans hab.2)
  trans _ _ _ h1 h2 := absurd (h2.1.symm.trans h1.2) h
  total a b da db hne := by
    rcases da with rfl | rfl <;> rcases db with rfl | rfl
    · exact absurd rfl hne
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hne
  supp _ _ hab := ⟨Or.inl hab.1, Or.inr hab.2⟩

/-- The input `{A,B}`. -/
def pairSet (A B : T) (h : A ≠ B) : FinSet T :=
  FinSet.ofList [A, B] (by simp [h])

theorem pairSet_mem {A B : T} {h : A ≠ B} (t : T) : (pairSet A B h).1 t ↔ t = A ∨ t = B := by
  show t ∈ [A, B] ↔ _
  simp

theorem ordPair_row {A B : T} (h : A ≠ B) : (abortFreeSpec T).S (pairSet A B h) (ordPair A B h) :=
  ⟨fun t => ⟨by rw [pairSet_mem]; exact ⟨Or.inr, fun h => h.elim False.elim id⟩,
    fun h => h.1⟩, fun _ h => h⟩

theorem ordPair_row' {A B : T} (h : A ≠ B) :
    (abortFreeSpec T).S (pairSet A B h) (ordPair B A (Ne.symm h)) :=
  ⟨fun t => ⟨by
      rw [pairSet_mem]
      show _ ↔ False ∨ (t = B ∨ t = A)
      exact ⟨fun h => Or.inr h.symm, fun h => h.elim False.elim Or.symm⟩,
    fun h => h.1⟩, fun _ h => h⟩

/-- `([A,B],∅)` and `([B,A],∅)` have no common refinement in `O` at all. -/
theorem ab_ba_no_common_refinement {A B : T} (h : A ≠ B) :
    ¬ ∃ u : Outcome T, ordPair A B h ≼ u ∧ ordPair B A (Ne.symm h) ≼ u := by
  rintro ⟨u, h1, h2⟩
  have hab : u.lt A B := (h1.2.2 A B (Or.inl rfl) (Or.inr rfl)).2 ⟨rfl, rfl⟩
  have hba : u.lt B A := (h2.2.2 B A (Or.inl rfl) (Or.inr rfl)).2 ⟨rfl, rfl⟩
  exact u.irrefl A (u.trans _ _ _ hab hba)

theorem not_directed_of {I O : Type} [PO I] [PO O] {sp : Spec I O} {i : I} {o1 o2 : O}
    (h1 : sp.S i o1) (h2 : sp.S i o2) (hn : ¬ ∃ u, o1 ≼ u ∧ o2 ≼ u) :
    ¬ sp.DirectedOutputs ∧ ¬ sp.LiftedMono := by
  have hd : ¬ sp.DirectedOutputs := by
    intro hD
    obtain ⟨u, _, hu⟩ := hD i [o1, o2] (by simp) (by simp [h1, h2])
    exact hn ⟨u, hu o1 (by simp), hu o2 (by simp)⟩
  exact ⟨hd, fun hL => hd ((liftedMono_iff_relMono_directed sp).1 hL).2⟩

/-- **The specification is not monotone** (nor are its fibers directed). -/
theorem txnSpec_not_liftedMono {A B : T} (h : A ≠ B) :
    ¬ (txnSpec T).DirectedOutputs ∧ ¬ (txnSpec T).LiftedMono :=
  not_directed_of (sp := txnSpec T) (ordPair_row h).1 (ordPair_row' h).1
    (ab_ba_no_common_refinement h)

/-- The abort-free specification is not monotone either. -/
theorem abortFreeSpec_not_liftedMono {A B : T} (h : A ≠ B) :
    ¬ (abortFreeSpec T).DirectedOutputs ∧ ¬ (abortFreeSpec T).LiftedMono :=
  not_directed_of (sp := abortFreeSpec T) (ordPair_row h) (ordPair_row' h)
    (ab_ba_no_common_refinement h)

/-! ### Fibers are antichains -/

/-- **The appendix's argument.**  At a fixed input, a permitted output that
refines another equals it, because both pairs partition the input. -/
theorem partitions_antichain {k : FinSet T} {o o' : Outcome T}
    (h : Partitions k o) (h' : Partitions k o') (hle : o ≼ o') : o = o' := by
  have hX : ∀ t, o.X t ↔ o'.X t := by
    intro t
    refine ⟨hle.1 t, fun hx => ?_⟩
    rcases (h t).1.1 ((h' t).1.2 (Or.inl hx)) with hx' | hd
    · exact hx'
    · exact absurd ⟨hx, hle.2.1 t hd⟩ (h' t).2
  have hD : ∀ t, o.dom t ↔ o'.dom t := by
    intro t
    refine ⟨hle.2.1 t, fun hd => ?_⟩
    rcases (h t).1.1 ((h' t).1.2 (Or.inr hd)) with hx | hd'
    · exact absurd ⟨hle.1 t hx, hd⟩ (h' t).2
    · exact hd'
  apply PO.antisymm hle
  refine ⟨fun t => (hX t).2, fun t => (hD t).2, fun a b da db => ?_⟩
  exact (hle.2.2 a b ((hD a).2 da) ((hD b).2 db)).symm

section Generic
variable {I O : Type} [PO I] [PO O]

/-- Fibers are antichains. -/
def Antichain (sp : Spec I O) : Prop := ∀ k u w, sp.S k u → sp.S k w → u ≼ w → u = w

theorem txn_antichain : Antichain (txnSpec T) :=
  fun _ _ _ hu hw hle => partitions_antichain hu hw hle

theorem abortFree_antichain : Antichain (abortFreeSpec T) :=
  fun _ _ _ hu hw hle => partitions_antichain hu.1 hw.1 hle

variable {sp : Spec I O}

/-- `(i, R ∩ P)`. -/
def filterState (σ : State sp) (P : I → O → Prop) (h : ∃ o, σ.R σ.cur o ∧ P σ.cur o) :
    State sp where
  cur := σ.cur
  R k u := σ.R k u ∧ P k u
  sub k u h := σ.sub k u h.1
  hasCur := let ⟨o, ho, hp⟩ := h; ⟨o, ho, hp⟩
  above k u h := σ.above k u h.1

/-- Definedness of the filter: the guard holds, some row of `R` at the current
input satisfies `P`, and some row of `R` fails it. -/
def FilterDefined (G : State sp → Prop) (P : I → O → Prop) (σ : State sp) : Prop :=
  G σ ∧ (∃ o, σ.R σ.cur o ∧ P σ.cur o) ∧ ∃ k u, σ.R k u ∧ ¬ P k u

open Classical in
noncomputable def filterApp (G : State sp → Prop) (P : I → O → Prop) (σ : State sp) :
    Option (State sp) :=
  if h : FilterDefined G P σ then some (filterState σ P h.2.1) else none

theorem filterApp_eq {G : State sp → Prop} {P : I → O → Prop} {σ τ : State sp} :
    filterApp G P σ = some τ ↔ ∃ h : FilterDefined G P σ, filterState σ P h.2.1 = τ := by
  unfold filterApp
  split
  · rename_i h
    simp only [Option.some.injEq]
    exact ⟨fun e => ⟨h, e⟩, fun ⟨_, e⟩ => e⟩
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    rintro ⟨h', _⟩
    exact h h'

theorem filterApp_none {G : State sp → Prop} {P : I → O → Prop} {σ : State sp} :
    filterApp G P σ = none ↔ ¬ FilterDefined G P σ := by
  unfold filterApp
  split
  · rename_i h; simp only [reduceCtorEq, false_iff]; exact fun hn => hn h
  · rename_i h; simp only [true_iff]; exact h

/-- **Each row filter is a commitment** (Def. `def:commitment`) when fibers are
antichains: a removed row and a kept row at the same input differ, and
permitted outputs at one input are comparable only when equal. -/
noncomputable def filterC (hA : Antichain sp) (G : State sp → Prop) (P : I → O → Prop) :
    Commitment sp where
  app := filterApp G P
  cur_eq := by
    intro σ τ h; obtain ⟨_, rfl⟩ := filterApp_eq.1 h; rfl
  sub := by
    intro σ τ h k u hu; obtain ⟨_, rfl⟩ := filterApp_eq.1 h; exact hu.1
  removes := by
    intro σ τ h
    obtain ⟨hd, rfl⟩ := filterApp_eq.1 h
    obtain ⟨k, u, hu, hnp⟩ := hd.2.2
    exact ⟨k, u, hu, fun h' => hnp h'.2⟩
  excludes := by
    intro σ τ h k u w hu hnu hw huw
    obtain ⟨_, rfl⟩ := filterApp_eq.1 h
    have e : u = w := hA k u w (σ.sub _ _ hu) (σ.sub _ _ hw.1) huw
    subst e
    exact hnu ⟨hu, hw.2⟩

/-- Definedness and effect of a filter commitment: defined exactly when the
guard holds, some row of `R` at `i` satisfies `P`, and some row of `R` fails
it; it then retains the rows of `R` satisfying `P`. -/
theorem filterC_app_iff (hA : Antichain sp) {G : State sp → Prop} {P : I → O → Prop}
    {σ τ : State sp} :
    (filterC hA G P).app σ = some τ ↔
      FilterDefined G P σ ∧ τ.cur = σ.cur ∧ ∀ k u, τ.R k u ↔ σ.R k u ∧ P k u := by
  show filterApp G P σ = some τ ↔ _
  rw [filterApp_eq]
  constructor
  · rintro ⟨hd, rfl⟩; exact ⟨hd, rfl, fun _ _ => Iff.rfl⟩
  · rintro ⟨hd, hc, hR⟩
    refine ⟨hd, State.ext' hc.symm ?_⟩
    funext k u; exact (propext (hR k u)).symm

/-- In an antichain-fiber specification, `o` is exposable at `σ` exactly when
every remaining row (at every input) refines `o`. -/
theorem exposable_iff_refines (hA : Antichain sp) (σ : State sp) (o : O) :
    Exposable σ o ↔ ∀ k x, σ.R k x → o ≼ x := by
  constructor
  · intro he k x hx
    apply Classical.byContradiction
    intro hn
    obtain ⟨u, hu, hou, hxu⟩ := he k x hx hn
    have e : x = u := hA k x u (σ.sub _ _ hx) (σ.sub _ _ hu) hxu
    exact hn (e ▸ hou)
  · intro h k x hx hn; exact absurd (h k x hx) hn

end Generic

/-! ### The commitments and bases -/

/-- `order(A,B)`: `A ∈ X`, or `B ∈ X`, or `A <_L B`. -/
def orderP (A B : T) : FinSet T → Outcome T → Prop := fun _ o => o.X A ∨ o.X B ∨ o.lt A B
/-- `commit(A)`: `A ∉ X`. -/
def commitP (A : T) : FinSet T → Outcome T → Prop := fun _ o => ¬ o.X A
/-- `abort(A)`: `A ∈ X`. -/
def abortP (A : T) : FinSet T → Outcome T → Prop := fun _ o => o.X A
/-- `stamp(A)` given `Z`: at row `(k,(L,X))`, every `z ∈ Z` has `z <_L A` or one
of `z, A` aborted, and every `D ∈ k ∖ (Z ∪ {A})` has `A <_L D` or one of `A, D`
aborted. -/
def stampP (A : T) (Z : T → Prop) : FinSet T → Outcome T → Prop := fun k o =>
  (∀ z, Z z → o.lt z A ∨ o.X z ∨ o.X A) ∧
  (∀ D, k.1 D → ¬ Z D → D ≠ A → o.lt A D ∨ o.X A ∨ o.X D)

section Bases
variable (sp : Spec (FinSet T) (Outcome T)) (hA : Antichain sp)

/-- `order(A,B)`, for distinct `A, B` in the current input. -/
noncomputable def orderC (A B : T) : Commitment sp :=
  filterC hA (fun σ => A ≠ B ∧ σ.cur.1 A ∧ σ.cur.1 B) (orderP A B)
noncomputable def commitC (A : T) : Commitment sp := filterC hA (fun _ => True) (commitP A)
noncomputable def abortC (A : T) : Commitment sp := filterC hA (fun _ => True) (abortP A)
/-- `stamp(A)`, given `Z ⊆ i`. -/
noncomputable def stampC (A : T) (Z : T → Prop) : Commitment sp :=
  filterC hA (fun σ => ∀ z, Z z → σ.cur.1 z) (stampP A Z)

/-- `B_2PL = {order, commit, abort}`, over all transactions. -/
def basis2PL : Basis sp := fun c =>
  (∃ A B, c = orderC sp hA A B) ∨ (∃ A, c = commitC sp hA A) ∨ (∃ A, c = abortC sp hA A)

/-- `B_MVTO = {stamp, commit, abort}`, over all transactions. -/
def basisMVTO : Basis sp := fun c =>
  (∃ A Z, c = stampC sp hA A Z) ∨ (∃ A, c = commitC sp hA A) ∨ (∃ A, c = abortC sp hA A)

end Bases

/-- The commitments for the specification and the abort-free one. -/
noncomputable abbrev orderT (A B : T) := orderC (txnSpec T) txn_antichain A B
noncomputable abbrev orderAF (A B : T) := orderC (abortFreeSpec T) abortFree_antichain A B

/-! ### 2PL deadlock -/

/-- Rows satisfying both `order(A,B)` and `order(B,A)` are exactly those with
`A ∈ X` or `B ∈ X`. -/
theorem deadlock_rows (k : FinSet T) (o : Outcome T) (A B : T) :
    (orderP A B k o ∧ orderP B A k o) ↔ (o.X A ∨ o.X B) := by
  constructor
  · rintro ⟨h1 | h1 | h1, h2 | h2 | h2⟩ <;> first
      | exact Or.inl ‹_› | exact Or.inr ‹_›
      | exact absurd (o.trans _ _ _ h1 h2) (o.irrefl _)
  · rintro (h | h)
    · exact ⟨Or.inl h, Or.inr (Or.inl h)⟩
    · exact ⟨Or.inr (Or.inl h), Or.inl h⟩

/-- **Deadlock.**  After `order(A,B)` and then `order(B,A)`, the rows left (at
every input, in particular at `i`) are exactly the rows of `R` with `A ∈ X` or
`B ∈ X`. -/
theorem deadlock_state {sp : Spec (FinSet T) (Outcome T)} (hA : Antichain sp) {A B : T}
    {σ σ1 σ2 : State sp} (h1 : (orderC sp hA A B).app σ = some σ1)
    (h2 : (orderC sp hA B A).app σ1 = some σ2) :
    σ2.cur = σ.cur ∧ ∀ k u, σ2.R k u ↔ σ.R k u ∧ (u.X A ∨ u.X B) := by
  obtain ⟨_, c1, r1⟩ := (filterC_app_iff hA).1 h1
  obtain ⟨_, c2, r2⟩ := (filterC_app_iff hA).1 h2
  refine ⟨c2.trans c1, fun k u => ?_⟩
  rw [r2, r1, ← deadlock_rows k u A B, and_assoc]

/-- After the deadlock, every output still available at any later state (whose
table is contained in the deadlock table) aborts `A` or `B`: resolving it
means fixing `A` or `B` as aborted. -/
theorem deadlock_forces_abort {sp : Spec (FinSet T) (Outcome T)} (hA : Antichain sp) {A B : T}
    {σ σ1 σ2 : State sp} (h1 : (orderC sp hA A B).app σ = some σ1)
    (h2 : (orderC sp hA B A).app σ1 = some σ2) (τ : State sp)
    (hτ : ∀ k u, τ.R k u → σ2.R k u) : ∀ k u, τ.R k u → u.X A ∨ u.X B :=
  fun k u h => (((deadlock_state hA h1 h2).2 k u).1 (hτ k u h)).2

/-- **Abort-free deadlock.**  Under the abort-free specification, once
`order(A,B)` has been applied, `order(B,A)` is undefined at every state whose
table is contained in the result (whatever its current input). -/
theorem abortFree_order_blocks {A B : T} {σ σ1 : State (abortFreeSpec T)}
    (h : (orderAF A B).app σ = some σ1) (τ : State (abortFreeSpec T))
    (hτ : ∀ k u, τ.R k u → σ1.R k u) : (orderAF B A).app τ = none := by
  obtain ⟨_, _, r1⟩ := (filterC_app_iff abortFree_antichain).1 h
  show filterApp _ _ τ = none
  rw [filterApp_none]
  rintro ⟨_, ⟨o, ho, hp⟩, _⟩
  have hab := ((r1 _ _).1 (hτ _ _ ho)).2
  have hX := (τ.sub _ _ ho).2
  rcases hab with h | h | hab
  · exact hX _ h
  · exact hX _ h
  rcases hp with h | h | hba
  · exact hX _ h
  · exact hX _ h
  · exact o.irrefl _ (o.trans _ _ _ hab hba)

/-- ... in particular at every state any later execution, under any basis,
reaches: `order(B,A)` is never defined again. -/
theorem abortFree_order_blocks_forever {A B : T} {σ σ1 : State (abortFreeSpec T)}
    (h : (orderAF A B).app σ = some σ1) (Bs : Basis (abortFreeSpec T))
    {es : List (SEvent (abortFreeSpec T))} {τ : State (abortFreeSpec T)}
    (hx : SysExec Bs σ1 es τ) : (orderAF B A).app τ = none :=
  abortFree_order_blocks h τ hx.sub

/-! ### Figure `fig:cc-commitments` and MVTO -/

/-- Fig. (h): under the abort-free specification, `order(A,B)` keeps exactly
the rows with `A` before `B`. -/
theorem orderP_abortFree {k : FinSet T} {o : Outcome T} (h : (abortFreeSpec T).S k o) (A B : T) :
    orderP A B k o ↔ o.lt A B := by
  constructor
  · rintro (h' | h' | h')
    · exact absurd h' (h.2 _)
    · exact absurd h' (h.2 _)
    · exact h'
  · exact fun h' => Or.inr (Or.inr h')

/-- Fig. (i): under the abort-free specification, `stamp(B)` with `Z = ∅`
keeps exactly the rows with `B` first. -/
theorem stampP_first_abortFree {k : FinSet T} {o : Outcome T} (h : (abortFreeSpec T).S k o)
    (B : T) : stampP B (fun _ => False) k o ↔ ∀ D, k.1 D → D ≠ B → o.lt B D := by
  constructor
  · intro hs D hD hne
    rcases hs.2 D hD id hne with h' | h' | h'
    · exact h'
    · exact absurd h' (h.2 _)
    · exact absurd h' (h.2 _)
  · intro hf
    exact ⟨fun _ h => h.elim, fun D hD _ hne => Or.inl (hf D hD hne)⟩

/-- **MVTO: no abort is forced by this specification.**  An abort-free row whose
order is the stamp order (`Z` = transactions of `k` before `A`) satisfies
`stamp(A)` and `commit(A)` for every `A ∈ k`. -/
theorem stamp_order_row {k : FinSet T} {o : Outcome T} (h : (abortFreeSpec T).S k o)
    {A : T} (hA : k.1 A) :
    stampP A (fun z => k.1 z ∧ o.lt z A) k o ∧ commitP A k o := by
  have dom_of : ∀ t, k.1 t → o.dom t := fun t ht =>
    ((h.1 t).1.1 ht).elim (fun hx => absurd hx (h.2 t)) id
  refine ⟨⟨fun z hz => Or.inl hz.2, fun D hD hnZ hne => ?_⟩, h.2 A⟩
  rcases o.total A D (dom_of A hA) (dom_of D hD) (Ne.symm hne) with h' | h'
  · exact Or.inl h'
  · exact absurd ⟨hD, h'⟩ hnZ

end AuditF
end CC
