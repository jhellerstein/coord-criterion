import CoordCriterion.Appendix.TransactionBases.NoReads

/-!
# Transactions with partial outputs (Appendix G, `app:cc-bases`)

Namespace `CC.Txn.Partial`.  The transaction specification of the appendix:
outputs `(L,X,ρ)` may leave transactions undecided and may report read results
of undecided transactions, as 2PL and MVTO schedulers do.

* `ROut`, `Valid`, `LastWrite`, `Complete`, `Permitted`, `spec` — the
  specification (`af = true`: the abort-free variant).  A *complete* output
  decides every transaction of the input; a row is permitted when some
  permitted complete output at the same input refines it.
* `ab_ba_rows`, `ab_ba_no_common`, `spec_not_liftedMono` — not monotone.
* `Keep`, `closeC`, `closeC_app_iff`, `keep_complete` — a *closure commitment*
  for a condition `Q` on complete outputs keeps a row when some remaining
  complete row at the same input refines it and satisfies `Q`; it is a
  commitment (Def. `def:commitment`) for every `Q`.  (Removing exactly the
  rows that fail an up-closed condition would leave rows with no remaining
  completion, e.g. a row committing `A` and `B` whose read forces a third
  transaction between them against the stamps; the closure form removes them.)
* `order`, `commit`, `abort`, `stamp`, `read`, `basis2PL`, `basisMVTO`.
* `Good`, `good_run` — every state reached under either basis is convex and
  completable; `read_emit` — after `read(B,x,v)`, emitting the read is
  exposable.
* `fig_h`, `fig_i`, `order_at`, `stamp_at`, `order_not_MVTO`, `stamp_not_2PL`,
  `not_read`, `not_choice`, `neither_is_choice` — Fig. `fig:cc-commitments`
  and the bases differ, at the canonical state of `{A,B,C}`.
* `deadlock`, `deadlock_complete`, `deadlock_commit`, `abortFree_blocks` —
  2PL deadlock.
* `stamps_row`, `TwoStamps.no_both`, `TwoStamps.read_no_both`,
  `TwoStamps.abort_entailed`, `Ex.mvto_instance`, `writer_after_A` — MVTO:
  what a reported read commits to, when `A`'s abort is entailed, and an
  instance where it is a choice.

Modeling choices: as in `NoReads.lean`, inputs are `FinSet T`, `(L,X)` is an
`Outcome T`; `ρ a x = some v` reports that `a`'s read of `x` returned `v`
(`none`: the initial version; `some W`: the write by `W`).  The guards
("`A ∈ i`" etc.) are part of definedness.
-/

namespace CC
namespace Txn
namespace Partial

open Classical

set_option linter.unusedSimpArgs false

variable {T K : Type}

/-! ### Outputs `(L, X, ρ)` -/

/-- An output `(L,X,ρ)`. -/
structure ROut (T K : Type) where
  o : Outcome T
  ρ : T → K → Option (Option T)

/-- `(L,X,ρ) ≼ (L',X',ρ')` iff `(L,X) ≼ (L',X')` and `ρ ⊆ ρ'`. -/
def ROut.le (r r' : ROut T K) : Prop :=
  r.o ≼ r'.o ∧ ∀ a x v, r.ρ a x = some v → r'.ρ a x = some v

theorem ROut.ext' {r r' : ROut T K} (h1 : r.o = r'.o) (h2 : r.ρ = r'.ρ) : r = r' := by
  cases r; cases r'; cases h1; cases h2; rfl

instance instPOROut (T K : Type) : PO (ROut T K) where
  le := ROut.le
  refl r := ⟨PO.refl r.o, fun _ _ _ h => h⟩
  trans h1 h2 := ⟨PO.trans h1.1 h2.1, fun a x v h => h2.2 a x v (h1.2 a x v h)⟩
  antisymm {r r'} h1 h2 := by
    apply ROut.ext' (PO.antisymm h1.1 h2.1)
    funext a x
    cases e : r.ρ a x with
    | none =>
      cases e' : r'.ρ a x with
      | none => rfl
      | some v =>
        have h := h2.2 a x v e'
        rw [e] at h; cases h
    | some v => exact (h1.2 a x v e).symm

theorem le_ρ {r r' : ROut T K} (h : r ≼ r') {a : T} {x : K} {v : Option T}
    (e : r.ρ a x = some v) : r'.ρ a x = some v := h.2 a x v e

/-! ### The specification -/

section Spec
variable (rd wr : T → K → Prop)

/-- `v` is a version of `x` present at input `k`: the initial version, or the
write of `x` by a transaction of `k`. -/
def Valid (k : FinSet T) (x : K) : Option T → Prop
  | none => True
  | some W => k.1 W ∧ wr W x

/-- `v` is the last write of `x` before `a` in `L`, or the initial version if
no earlier transaction writes `x`. -/
def LastWrite (o : Outcome T) (a : T) (x : K) : Option T → Prop
  | none => ∀ w, o.lt w a → ¬ wr w x
  | some w => o.lt w a ∧ wr w x ∧ ∀ w', o.lt w w' → o.lt w' a → ¬ wr w' x

/-- A complete output `(L,X,ρ)` is permitted at `k`: `X` and `dom L` partition
`k`, each reported read is a read of a transaction of `k` returning a version
present at `k`, and a read by a committed transaction returns the last earlier
write.  (Reads by aborted transactions are otherwise unconstrained.) -/
def Complete (k : FinSet T) (r : ROut T K) : Prop :=
  Partitions k r.o ∧
    ∀ a x v, r.ρ a x = some v →
      k.1 a ∧ rd a x ∧ Valid wr k x v ∧ (r.o.dom a → LastWrite wr r.o a x v)

/-- Permitted complete outputs; with `af = true`, also abort-free. -/
def Permitted (af : Bool) (k : FinSet T) (r : ROut T K) : Prop :=
  Complete rd wr k r ∧ (af = true → ∀ t, ¬ r.o.X t)

/-- No reads reported. -/
def full (o : Outcome T) : ROut T K := ⟨o, fun _ _ => none⟩

theorem full_complete {k : FinSet T} {o : Outcome T} (h : Partitions k o) :
    Complete (K := K) rd wr k (full o) :=
  ⟨h, fun _ _ _ e => by cases e⟩

/-- **The specification** (`af = false`) and its abort-free variant
(`af = true`): a row is permitted when some permitted complete output at the
same input refines it. -/
def spec (af : Bool) : Spec (FinSet T) (ROut T K) where
  S k u := ∃ c, Permitted rd wr af k c ∧ u ≼ c
  total k := by
    cases af with
    | false =>
      exact ⟨full (allAbort k), full (allAbort k),
        ⟨full_complete rd wr (allAbort_partitions' k), fun h => by cases h⟩, PO.refl _⟩
    | true =>
      obtain ⟨o, ho⟩ := (abortFreeSpec T).total k
      exact ⟨full o, full o, ⟨full_complete rd wr ho.1, fun _ => ho.2⟩, PO.refl _⟩
where
  allAbort_partitions' (k : FinSet T) : Partitions k (allAbort k) :=
    fun _ => ⟨⟨Or.inl, fun h => h.elim id False.elim⟩, fun h => h.2⟩

end Spec

theorem allAbort_part (k : FinSet T) : Partitions k (allAbort k) :=
  spec.allAbort_partitions' k

/-- Comparable complete outputs at one input have the same `(L,X)`. -/
theorem same_o {k : FinSet T} {a b : ROut T K} (ha : Partitions k a.o)
    (hb : Partitions k b.o) (h : a ≼ b) : a.o = b.o :=
  partitions_antichain ha hb h.1

section Rows
variable {rd wr : T → K → Prop} {af : Bool}

/-- Rows are closed downward (within the output order). -/
theorem spec_down {k : FinSet T} {u w : ROut T K} (hw : (spec rd wr af).S k w) (h : u ≼ w) :
    (spec rd wr af).S k u :=
  let ⟨c, hc, hwc⟩ := hw; ⟨c, hc, PO.trans h hwc⟩

/-- A row that decides every transaction of its input is a permitted complete
output. -/
theorem permitted_of_row {k : FinSet T} {c : ROut T K} (hc : (spec rd wr af).S k c)
    (hp : Partitions k c.o) : Permitted rd wr af k c := by
  obtain ⟨c', ⟨⟨hp', hρ'⟩, haf⟩, hle⟩ := hc
  have e := same_o hp hp' hle
  refine ⟨⟨hp, fun a x v hv => ?_⟩, fun h t => by rw [e]; exact haf h t⟩
  rw [e]
  exact hρ' a x v (le_ρ hle hv)

/-- The read facts of any row are facts about transactions and versions of its
input. -/
theorem row_read {k : FinSet T} {u : ROut T K} (hu : (spec rd wr af).S k u) {a : T} {x : K}
    {v : Option T} (e : u.ρ a x = some v) : k.1 a ∧ rd a x ∧ Valid wr k x v := by
  obtain ⟨c, ⟨⟨_, hρ⟩, _⟩, hle⟩ := hu
  obtain ⟨h1, h2, h3, _⟩ := hρ a x v (le_ρ hle e)
  exact ⟨h1, h2, h3⟩

/-- A row's committed transactions lie in its input. -/
theorem row_dom {k : FinSet T} {u : ROut T K} (hu : (spec rd wr af).S k u) {t : T}
    (h : u.o.dom t) : k.1 t := by
  obtain ⟨c, ⟨⟨hp, _⟩, _⟩, hle⟩ := hu
  exact ((hp t).1.2 (Or.inr (hle.1.2.1 t h)))

end Rows

/-! ### Closure commitments -/

section Closure
variable {sp : Spec (FinSet T) (ROut T K)}

/-- Row `(k,u)` of `σ` is kept by the condition `Q` on complete outputs: some
row of `σ` at `k` that decides every transaction of `k`, refines `u`, and
satisfies `Q`, remains. -/
def Keep (σ : State sp) (Q : ROut T K → Prop) (k : FinSet T) (u : ROut T K) : Prop :=
  σ.R k u ∧ ∃ c, σ.R k c ∧ Partitions k c.o ∧ u ≼ c ∧ Q c

/-- Definedness: the guard holds, some row at the current input is kept, and
some row is removed. -/
def Defined (G : State sp → Prop) (Q : ROut T K → Prop) (σ : State sp) : Prop :=
  G σ ∧ (∃ u, Keep σ Q σ.cur u) ∧ ∃ k u, σ.R k u ∧ ¬ Keep σ Q k u

/-- The state `(i, {kept rows})`. -/
def keepState (σ : State sp) (Q : ROut T K → Prop) (h : ∃ u, Keep σ Q σ.cur u) : State sp where
  cur := σ.cur
  R := Keep σ Q
  sub k u h := σ.sub k u h.1
  hasCur := h
  above k u h := σ.above k u h.1

noncomputable def closeApp (G : State sp → Prop) (Q : ROut T K → Prop) (σ : State sp) :
    Option (State sp) :=
  if h : Defined G Q σ then some (keepState σ Q h.2.1) else none

theorem closeApp_eq {G : State sp → Prop} {Q : ROut T K → Prop} {σ τ : State sp} :
    closeApp G Q σ = some τ ↔ ∃ h : Defined G Q σ, keepState σ Q h.2.1 = τ := by
  unfold closeApp
  split
  · rename_i h
    simp only [Option.some.injEq]
    exact ⟨fun e => ⟨h, e⟩, fun ⟨_, e⟩ => e⟩
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    rintro ⟨h', _⟩
    exact h h'

/-- **A closure commitment is a commitment** (Def. `def:commitment`), for every
condition `Q`: a removed row has no remaining complete row above it satisfying
`Q`, so no kept row refines it (a kept row's complete witness would serve). -/
noncomputable def closeC (G : State sp → Prop) (Q : ROut T K → Prop) : Commitment sp where
  app := closeApp G Q
  cur_eq := by
    intro σ τ h; obtain ⟨_, rfl⟩ := closeApp_eq.1 h; rfl
  sub := by
    intro σ τ h k u hu; obtain ⟨_, rfl⟩ := closeApp_eq.1 h; exact hu.1
  removes := by
    intro σ τ h
    obtain ⟨hd, rfl⟩ := closeApp_eq.1 h
    exact hd.2.2
  excludes := by
    intro σ τ h k u w hu hnu hw huw
    obtain ⟨_, rfl⟩ := closeApp_eq.1 h
    obtain ⟨_, c, hc, hp, hwc, hq⟩ := hw
    exact hnu ⟨hu, c, hc, hp, PO.trans huw hwc, hq⟩

theorem closeC_app_iff {G : State sp → Prop} {Q : ROut T K → Prop} {σ τ : State sp} :
    (closeC G Q).app σ = some τ ↔
      Defined G Q σ ∧ τ.cur = σ.cur ∧ ∀ k u, τ.R k u ↔ Keep σ Q k u := by
  show closeApp G Q σ = some τ ↔ _
  rw [closeApp_eq]
  constructor
  · rintro ⟨hd, rfl⟩; exact ⟨hd, rfl, fun _ _ => Iff.rfl⟩
  · rintro ⟨hd, hc, hR⟩
    refine ⟨hd, State.ext' hc.symm ?_⟩
    funext k u; exact (propext (hR k u)).symm

theorem closeC_none {G : State sp → Prop} {Q : ROut T K → Prop} {σ : State sp} :
    (closeC G Q).app σ = none ↔ ¬ Defined G Q σ := by
  show closeApp G Q σ = none ↔ _
  unfold closeApp
  split
  · rename_i h; simp only [reduceCtorEq, false_iff]; exact fun hn => hn h
  · rename_i h; simp only [true_iff]; exact h

/-- A complete row is kept exactly when it satisfies a condition on `(L,X)`. -/
theorem keep_complete {σ : State sp} {P : Outcome T → Prop} {k : FinSet T} {c : ROut T K}
    (hp : Partitions k c.o) : Keep σ (fun c => P c.o) k c ↔ σ.R k c ∧ P c.o := by
  constructor
  · rintro ⟨h, c', _, hp', hle, hq⟩
    exact ⟨h, (same_o hp hp' hle) ▸ hq⟩
  · rintro ⟨h, hq⟩
    exact ⟨h, c, h, hp, PO.refl _, hq⟩

/-- After a closure commitment, every row has a remaining complete refinement
satisfying `Q`. -/
theorem after_completion {G : State sp → Prop} {Q : ROut T K → Prop} {σ τ : State sp}
    (h : (closeC G Q).app σ = some τ) {k : FinSet T} {u : ROut T K} (hu : τ.R k u) :
    ∃ c, τ.R k c ∧ Partitions k c.o ∧ u ≼ c ∧ Q c := by
  obtain ⟨_, _, hR⟩ := closeC_app_iff.1 h
  obtain ⟨_, c, hc, hp, hle, hq⟩ := (hR k u).1 hu
  exact ⟨c, (hR k c).2 ⟨hc, c, hc, hp, PO.refl _, hq⟩, hp, hle, hq⟩

/-- After a closure commitment for a condition on `(L,X)`, every complete row
of every smaller table satisfies it. -/
theorem after_complete {G : State sp → Prop} {P : Outcome T → Prop} {σ τ : State sp}
    (h : (closeC G (fun c => P c.o)).app σ = some τ) {R : FinSet T → ROut T K → Prop}
    (hR : ∀ k u, R k u → τ.R k u) {k : FinSet T} {c : ROut T K} (hc : R k c)
    (hp : Partitions k c.o) : P c.o := by
  obtain ⟨_, _, hR'⟩ := closeC_app_iff.1 h
  exact ((keep_complete hp).1 ((hR' k c).1 (hR k c hc))).2

/-- The current input only grows: if `τ`'s table is contained in `σ`'s, then
`σ.cur ⊆ τ.cur`. -/
theorem cur_mono {σ τ : State sp} (h : ∀ k u, τ.R k u → σ.R k u) : σ.cur ≼ τ.cur :=
  let ⟨_, ho⟩ := τ.hasCur; σ.above _ _ (h _ _ ho)

end Closure

/-! ### The commitments and the bases -/

/-- `order(A,B)`: no committed `B` before a committed `A`. -/
def OrderOK (A B : T) (o : Outcome T) : Prop := ¬ o.lt B A
/-- `commit(A)`: `A ∉ X`. -/
def CommitOK (A : T) (o : Outcome T) : Prop := ¬ o.X A
/-- `abort(A)`: `A ∉ dom L`. -/
def AbortOK (A : T) (o : Outcome T) : Prop := ¬ o.dom A
/-- `stamp(A)` given `Z`: no committed `D ∉ Z ∪ {A}` before `A`, and no
committed `z ∈ Z` after `A`. -/
def StampOK (A : T) (Z : T → Prop) (o : Outcome T) : Prop :=
  (∀ D, ¬ Z D → D ≠ A → ¬ o.lt D A) ∧ ∀ z, Z z → ¬ o.lt A z

section Bases
variable {sp : Spec (FinSet T) (ROut T K)}

/-- `order(A,B)`, for distinct `A, B` of the current input. -/
noncomputable def order (A B : T) : Commitment sp :=
  closeC (fun σ => A ≠ B ∧ σ.cur.1 A ∧ σ.cur.1 B) (fun c => OrderOK A B c.o)
/-- `commit(A)`, for `A` in the current input. -/
noncomputable def commit (A : T) : Commitment sp :=
  closeC (fun σ => σ.cur.1 A) (fun c => CommitOK A c.o)
/-- `abort(A)`, for `A` in the current input. -/
noncomputable def abort (A : T) : Commitment sp :=
  closeC (fun σ => σ.cur.1 A) (fun c => AbortOK A c.o)
/-- `stamp(A)` given `Z ⊆ i` with `A ∈ i ∖ Z`. -/
noncomputable def stamp (A : T) (Z : T → Prop) : Commitment sp :=
  closeC (fun σ => σ.cur.1 A ∧ ¬ Z A ∧ ∀ z, Z z → σ.cur.1 z) (fun c => StampOK A Z c.o)
/-- `read(A,x,v)`, for `A` in the current input: `A`'s read of `x` returns `v`. -/
noncomputable def read (A : T) (x : K) (v : Option T) : Commitment sp :=
  closeC (fun σ => σ.cur.1 A) (fun c => c.ρ A x = some v)

/-- `B_2PL = {order, commit, abort, read}`. -/
def basis2PL : Basis sp := fun c =>
  (∃ A B, c = order A B) ∨ (∃ A, c = commit A) ∨ (∃ A, c = abort A) ∨
    (∃ A x v, c = read A x v)

/-- `B_MVTO = {stamp, commit, abort, read}`. -/
def basisMVTO : Basis sp := fun c =>
  (∃ A Z, c = stamp A Z) ∨ (∃ A, c = commit A) ∨ (∃ A, c = abort A) ∨
    (∃ A x v, c = read A x v)

/-- A closure commitment. -/
def IsClosure (c : Commitment sp) : Prop := ∃ G Q, c = closeC G Q

theorem basis2PL_closure {c : Commitment sp} (h : basis2PL c) : IsClosure c := by
  rcases h with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact ⟨_, _, rfl⟩

theorem basisMVTO_closure {c : Commitment sp} (h : basisMVTO c) : IsClosure c := by
  rcases h with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact ⟨_, _, rfl⟩

end Bases

/-! ### States reached under closure bases -/

section Good
variable {rd wr : T → K → Prop} {af : Bool}

/-- Rows between two rows of the table at one input are in the table. -/
def Convex (σ : State (spec rd wr af)) : Prop :=
  ∀ k x y c, σ.R k x → σ.R k c → x ≼ y → y ≼ c → σ.R k y

/-- Every row has a complete refinement in the table at the same input. -/
def Completable (σ : State (spec rd wr af)) : Prop :=
  ∀ k x, σ.R k x → ∃ c, σ.R k c ∧ Partitions k c.o ∧ x ≼ c

def Good (σ : State (spec rd wr af)) : Prop := Convex σ ∧ Completable σ

theorem good_canon (i : FinSet T) : Good (canon (spec rd wr af) i) := by
  refine ⟨fun k _ y c _ hc _ hyc => ⟨spec_down hc.1 hyc, hc.2⟩, fun k x hx => ?_⟩
  obtain ⟨c, hc, hle⟩ := hx.1
  exact ⟨c, ⟨⟨c, hc, PO.refl _⟩, hx.2⟩, hc.1.1, hle⟩

theorem good_input {σ τ : State (spec rd wr af)} {j : FinSet T} (h : Step σ (.input j) τ)
    (hg : Good σ) : Good τ := by
  have hR : ∀ k u, τ.R k u ↔ σ.R k u ∧ j ≼ k := by
    cases h with
    | input _ _ _ _ hR => intro k u; rw [hR]; exact Iff.rfl
  refine ⟨fun k x y c hx hc hxy hyc => ?_, fun k x hx => ?_⟩
  · rw [hR] at hx hc ⊢
    exact ⟨hg.1 k x y c hx.1 hc.1 hxy hyc, hx.2⟩
  · rw [hR] at hx
    obtain ⟨c, hc, hp, hle⟩ := hg.2 k x hx.1
    exact ⟨c, (hR k c).2 ⟨hc, hx.2⟩, hp, hle⟩

theorem good_outputTable {σ τ : State (spec rd wr af)} {o : ROut T K}
    (hR0 : τ.R = outputTable σ o) (hg : Good σ) : Good τ := by
  have hR : ∀ k u, τ.R k u ↔ σ.R k u ∧ o ≼ u := by intro k u; rw [hR0]; exact Iff.rfl
  refine ⟨fun k x y c hx hc hxy hyc => ?_, fun k x hx => ?_⟩
  · rw [hR] at hx hc ⊢
    exact ⟨hg.1 k x y c hx.1 hc.1 hxy hyc, PO.trans hx.2 hxy⟩
  · rw [hR] at hx
    obtain ⟨c, hc, hp, hle⟩ := hg.2 k x hx.1
    exact ⟨c, (hR k c).2 ⟨hc, PO.trans hx.2 hle⟩, hp, hle⟩

theorem good_close {G : State (spec rd wr af) → Prop} {Q : ROut T K → Prop}
    {σ τ : State (spec rd wr af)} (h : (closeC G Q).app σ = some τ) (hg : Good σ) :
    Good τ := by
  obtain ⟨_, _, hR⟩ := closeC_app_iff.1 h
  refine ⟨fun k x y c hx hc hxy hyc => ?_, fun k x hx => ?_⟩
  · obtain ⟨hx', _⟩ := (hR k x).1 hx
    obtain ⟨hc', c', hc'', hp, hcc, hq⟩ := (hR k c).1 hc
    exact (hR k y).2 ⟨hg.1 k x y c hx' hc' hxy hyc, c', hc'', hp, PO.trans hyc hcc, hq⟩
  · obtain ⟨c, hc, hp, hle, _⟩ := after_completion h hx
    exact ⟨c, hc, hp, hle⟩

theorem good_applySeq {γ : List (Commitment (spec rd wr af))} {σ ρ : State (spec rd wr af)}
    (hγ : ∀ c ∈ γ, IsClosure c) (h : ApplySeq γ σ ρ) (hg : Good σ) : Good ρ := by
  induction h with
  | nil => exact hg
  | @cons c cs σ τ ρ hc _ ih =>
    obtain ⟨G, Q, rfl⟩ := hγ c (by simp)
    exact ih (fun c' h' => hγ c' (by simp [h'])) (good_close hc hg)

theorem good_sysStep {B : Basis (spec rd wr af)} (hB : ∀ c, B c → IsClosure c)
    {σ τ : State (spec rd wr af)} {e : SEvent (spec rd wr af)} (h : SysStep B σ e τ)
    (hg : Good σ) : Good τ := by
  cases h with
  | input h => exact good_input h hg
  | output hγ happ _ _ _ hR =>
      exact good_outputTable hR (good_applySeq (fun c hc => hB c (hγ c hc)) happ hg)
  | commit hγ _ happ =>
    exact good_applySeq (fun c hc => hB c (hγ c hc)) happ hg

theorem good_sysExec {B : Basis (spec rd wr af)} (hB : ∀ c, B c → IsClosure c)
    {σ τ : State (spec rd wr af)} {es : List (SEvent (spec rd wr af))}
    (h : SysExec B σ es τ) (hg : Good σ) : Good τ := by
  induction h with
  | nil => exact hg
  | cons hs _ ih => exact ih (good_sysStep hB hs hg)

/-- **Every state reached by a run under `B_2PL` or `B_MVTO` is good.** -/
theorem good_run {i : FinSet T} {es : List (SEvent (spec rd wr af))}
    {τ : State (spec rd wr af)} :
    (SysExec basis2PL (canon _ i) es τ → Good τ) ∧
    (SysExec basisMVTO (canon _ i) es τ → Good τ) :=
  ⟨fun h => good_sysExec (fun _ => basis2PL_closure) h (good_canon i),
   fun h => good_sysExec (fun _ => basisMVTO_closure) h (good_canon i)⟩

end Good

/-! ### Not monotone -/

section Mono
variable (rd wr : T → K → Prop) (af : Bool)

theorem ab_ba_rows {A B : T} (h : A ≠ B) :
    (spec rd wr af).S (pairSet A B h) (full (ordPair A B h)) ∧
    (spec rd wr af).S (pairSet A B h) (full (ordPair B A (Ne.symm h))) :=
  ⟨⟨_, ⟨full_complete rd wr (ordPair_row h).1, fun _ => (ordPair_row h).2⟩, PO.refl _⟩,
   ⟨_, ⟨full_complete rd wr (ordPair_row' h).1, fun _ => (ordPair_row' h).2⟩, PO.refl _⟩⟩

/-- `([A,B],∅,∅)` and `([B,A],∅,∅)` have no common refinement at all. -/
theorem ab_ba_no_common {A B : T} (h : A ≠ B) :
    ¬ ∃ u : ROut T K, full (ordPair A B h) ≼ u ∧ full (ordPair B A (Ne.symm h)) ≼ u :=
  fun ⟨u, h1, h2⟩ => ab_ba_no_common_refinement h ⟨u.o, h1.1, h2.1⟩

/-- **Not monotone** (fibers not directed, no Lifted Monotonicity), for both
the specification and its abort-free variant. -/
theorem spec_not_liftedMono {A B : T} (h : A ≠ B) :
    ¬ (spec (K := K) rd wr af).DirectedOutputs ∧ ¬ (spec (K := K) rd wr af).LiftedMono :=
  not_directed_of (ab_ba_rows rd wr af h).1 (ab_ba_rows rd wr af h).2 (ab_ba_no_common h)

end Mono

/-! ### 2PL deadlock -/

section Deadlock
variable {sp : Spec (FinSet T) (ROut T K)}

theorem order_guard {A B : T} {σ τ : State sp} (h : (order A B).app σ = some τ) :
    A ≠ B ∧ σ.cur.1 A ∧ σ.cur.1 B :=
  (closeC_app_iff.1 h).1.1

/-- **Deadlock.**  After `order(A,B)` and later `order(B,A)`, no row of any
smaller table (at any input) commits both `A` and `B`. -/
theorem deadlock {A B : T} {σ σ1 σ1' σ2 : State sp}
    (h1 : (order A B).app σ = some σ1) (hs : ∀ k u, σ1'.R k u → σ1.R k u)
    (h2 : (order B A).app σ1' = some σ2) {R : FinSet T → ROut T K → Prop}
    (hR : ∀ k u, R k u → σ2.R k u) {k : FinSet T} {w : ROut T K} (hw : R k w) :
    ¬ (w.o.dom A ∧ w.o.dom B) := by
  rintro ⟨hA, hB⟩
  obtain ⟨c, hc, hp, hle, hq⟩ := after_completion h2 (hR k w hw)
  have hq1 : OrderOK A B c.o :=
    after_complete h1 (R := σ2.R) (fun k u h => hs k u ((order B A).sub _ _ h2 k u h)) hc hp
  have hne := (order_guard h1).1
  rcases c.o.total A B (hle.1.2.1 A hA) (hle.1.2.1 B hB) hne with h | h
  · exact hq h
  · exact hq1 h

/-- … so every complete row of a smaller table whose input contains `A` and `B`
aborts one of them. -/
theorem deadlock_complete {A B : T} {σ σ1 σ1' σ2 : State sp}
    (h1 : (order A B).app σ = some σ1) (hs : ∀ k u, σ1'.R k u → σ1.R k u)
    (h2 : (order B A).app σ1' = some σ2) {R : FinSet T → ROut T K → Prop}
    (hR : ∀ k u, R k u → σ2.R k u) {k : FinSet T} {c : ROut T K} (hc : R k c)
    (hp : Partitions k c.o) (hA : k.1 A) (hB : k.1 B) : c.o.X A ∨ c.o.X B := by
  have hd := deadlock h1 hs h2 hR hc
  rcases (hp A).1.1 hA with h | h
  · exact Or.inl h
  rcases (hp B).1.1 hB with h' | h'
  · exact Or.inr h'
  exact absurd ⟨h, h'⟩ hd

/-- **Resolving a deadlock.**  If after the deadlock `commit(A)` is applied, then
in every smaller table every complete row aborts `B`, and `commit(B)` is
undefined. -/
theorem deadlock_commit {A B : T} {σ σ1 σ1' σ2 σ3 σ4 : State sp}
    (h1 : (order A B).app σ = some σ1) (hs : ∀ k u, σ1'.R k u → σ1.R k u)
    (h2 : (order B A).app σ1' = some σ2) (hs' : ∀ k u, σ3.R k u → σ2.R k u)
    (h3 : (commit A).app σ3 = some σ4) (τ : State sp) (hτ : ∀ k u, τ.R k u → σ4.R k u) :
    (∀ k c, τ.R k c → Partitions k c.o → c.o.X B) ∧ (commit B).app τ = none := by
  have h43 : ∀ k u, σ4.R k u → σ3.R k u := (commit A).sub _ _ h3
  have hτ2 : ∀ k u, τ.R k u → σ2.R k u := fun k u h => hs' k u (h43 k u (hτ k u h))
  have hτσ : ∀ k u, τ.R k u → σ.R k u := fun k u h =>
    (order A B).sub _ _ h1 k u (hs k u ((order B A).sub _ _ h2 k u (hτ2 k u h)))
  have hAB := order_guard h1
  have key : ∀ k c, τ.R k c → Partitions k c.o → c.o.X B := by
    intro k c hc hp
    have hk : σ.cur ≼ k := σ.above _ _ (hτσ k c hc)
    have hnX : CommitOK A c.o := after_complete h3 hτ hc hp
    have hdA : c.o.dom A := ((hp A).1.1 (hk A hAB.2.1)).resolve_left hnX
    rcases (hp B).1.1 (hk B hAB.2.2) with h | h
    · exact h
    · exact absurd ⟨hdA, h⟩ (deadlock h1 hs h2 hτ2 hc)
  refine ⟨key, closeC_none.2 ?_⟩
  rintro ⟨_, ⟨u, _, c, hc, hp, _, hq⟩, _⟩
  exact hq (key _ c hc hp)

/-- **Abort-free deadlock.**  Under the abort-free specification, once
`order(A,B)` has been applied, `order(B,A)` is undefined at every state whose
table is contained in the result: `A`, and so `B`, waits forever. -/
theorem abortFree_blocks {rd wr : T → K → Prop} {A B : T}
    {σ σ1 : State (spec rd wr true)} (h : (order A B).app σ = some σ1)
    (τ : State (spec rd wr true)) (hτ : ∀ k u, τ.R k u → σ1.R k u) :
    (order B A).app τ = none := by
  refine closeC_none.2 ?_
  rintro ⟨⟨hne, hB, hA⟩, ⟨u, _, c, hc, hp, _, hq⟩, _⟩
  have hq1 : OrderOK A B c.o := after_complete h hτ hc hp
  have hnoX := (permitted_of_row (τ.sub _ _ hc) hp).2 rfl
  have dA := ((hp A).1.1 hA).resolve_left (hnoX A)
  have dB := ((hp B).1.1 hB).resolve_left (hnoX B)
  rcases c.o.total A B dA dB (Ne.symm hne) with h' | h'
  · exact hq h'
  · exact hq1 h'

/-- … in particular at every state that any later execution reaches. -/
theorem abortFree_blocks_forever {rd wr : T → K → Prop} {A B : T}
    {σ σ1 : State (spec rd wr true)} (h : (order A B).app σ = some σ1)
    (Bs : Basis (spec rd wr true)) {es : List (SEvent (spec rd wr true))}
    {τ : State (spec rd wr true)} (hx : SysExec Bs σ1 es τ) : (order B A).app τ = none :=
  abortFree_blocks h τ hx.sub

end Deadlock

/-! ### MVTO: what a reported read entails -/

/-- `u` with `A` added to the aborted transactions. -/
def addAbort (u : ROut T K) (A : T) : ROut T K :=
  ⟨{ u.o with X := fun t => u.o.X t ∨ t = A }, u.ρ⟩

/-- `u` with the read fact "`B`'s read of `x` returned `v`". -/
noncomputable def addRead (u : ROut T K) (B : T) (x : K) (v : Option T) : ROut T K :=
  ⟨u.o, fun a y => if a = B ∧ y = x then some v else u.ρ a y⟩

theorem le_addAbort (u : ROut T K) (A : T) : u ≼ addAbort u A :=
  ⟨⟨fun _ h => Or.inl h, fun _ h => h, fun _ _ _ _ => Iff.rfl⟩, fun _ _ _ h => h⟩

theorem addAbort_mono {u w : ROut T K} (h : u ≼ w) (A : T) : addAbort u A ≼ addAbort w A :=
  ⟨⟨fun t h' => h'.elim (fun h'' => Or.inl (h.1.1 t h'')) Or.inr, h.1.2.1, h.1.2.2⟩, h.2⟩

theorem addAbort_le {u c : ROut T K} (h : u ≼ c) {A : T} (hA : c.o.X A) : addAbort u A ≼ c :=
  ⟨⟨fun t h' => h'.elim (h.1.1 t) (fun e => e ▸ hA), h.1.2.1, h.1.2.2⟩, h.2⟩

theorem addRead_ρ (u : ROut T K) (B : T) (x : K) (v : Option T) :
    (addRead u B x v).ρ B x = some v := by
  simp [addRead]

theorem le_addRead {u : ROut T K} {B : T} {x : K} {v : Option T}
    (h : ∀ v', u.ρ B x = some v' → v' = v) : u ≼ addRead u B x v := by
  refine ⟨PO.refl _, fun a y w e => ?_⟩
  simp only [addRead]
  split
  · rename_i hay
    obtain ⟨rfl, rfl⟩ := hay
    rw [h w e]
  · exact e

theorem addRead_mono {u w : ROut T K} (h : u ≼ w) (B : T) (x : K) (v : Option T) :
    addRead u B x v ≼ addRead w B x v := by
  refine ⟨h.1, fun a y v' e => ?_⟩
  simp only [addRead] at e ⊢
  by_cases hay : a = B ∧ y = x
  · simp only [hay, and_self, ↓reduceIte] at e ⊢; exact e
  · simp only [hay, ↓reduceIte] at e ⊢; exact h.2 a y v' e

theorem addRead_le {u c : ROut T K} (h : u ≼ c) {B : T} {x : K} {v : Option T}
    (hc : c.ρ B x = some v) : addRead u B x v ≼ c := by
  refine ⟨h.1, fun a y v' e => ?_⟩
  simp only [addRead] at e
  split at e
  · rename_i hay; obtain ⟨rfl, rfl⟩ := hay; cases e; exact hc
  · exact h.2 a y v' e

section MVTO
variable {rd wr : T → K → Prop} {af : Bool}

theorem stamp_guard {A : T} {Z : T → Prop} {σ τ : State (spec rd wr af)}
    (h : (stamp A Z).app σ = some τ) : σ.cur.1 A ∧ ¬ Z A ∧ ∀ z, Z z → σ.cur.1 z :=
  (closeC_app_iff.1 h).1.1

/-- **The row argument.**  A complete row satisfying `stamp(A)` (given `Z_A`)
and `stamp(B)` (given `Z_B ∋ A`), where `A` writes `x`, cannot commit both `A`
and `B` and report that `B` read `v`, where `v` is the initial version of `x` or
the write by a transaction of `Z_A` other than `A`: `A` lies between that
version and `B`. -/
theorem stamps_row {k : FinSet T} {c : ROut T K} (hc : Complete rd wr k c)
    {A B : T} {ZA ZB : T → Prop} {x : K} {v : Option T}
    (hsA : StampOK A ZA c.o) (hsB : StampOK B ZB c.o) (hAB : ZB A) (hBB : ¬ ZB B)
    (hwA : wr A x) (hv : ∀ W, v = some W → ZA W ∧ W ≠ A) (hρ : c.ρ B x = some v)
    (hdA : c.o.dom A) (hdB : c.o.dom B) : False := by
  have hne : A ≠ B := fun e => hBB (e ▸ hAB)
  have hlw := (hc.2 B x v hρ).2.2.2 hdB
  have hAB' : c.o.lt A B := (c.o.total A B hdA hdB hne).resolve_right (hsB.2 A hAB)
  cases v with
  | none => exact hlw A hAB' hwA
  | some W =>
    obtain ⟨hWB, _, hlast⟩ := hlw
    obtain ⟨hZW, hWA⟩ := hv W rfl
    have hWA' : c.o.lt W A :=
      (c.o.total W A (c.o.supp _ _ hWB).1 hdA hWA).resolve_right (hsA.2 W hZW)
    exact hlast A hWA' hAB' hwA

/-- The two stamps in a run: `stamp(A)` (given `Z_A`) leading to `σ1`, then,
at a state `σ1'` with a smaller table, `stamp(B)` (given `Z_B ∋ A`) leading to
`σ2`. -/
structure TwoStamps (A B : T) (ZA ZB : T → Prop) (σ σ2 : State (spec rd wr af)) where
  σ1 : State (spec rd wr af)
  σ1' : State (spec rd wr af)
  h1 : (stamp A ZA).app σ = some σ1
  hs : ∀ k u, σ1'.R k u → σ1.R k u
  h2 : (stamp B ZB).app σ1' = some σ2
  hAB : ZB A

namespace TwoStamps
variable {A B : T} {ZA ZB : T → Prop} {σ σ2 : State (spec rd wr af)}

theorem sub (H : TwoStamps A B ZA ZB σ σ2) : ∀ k u, σ2.R k u → σ.R k u :=
  fun k u h => (stamp A ZA).sub _ _ H.h1 k u (H.hs k u ((stamp B ZB).sub _ _ H.h2 k u h))

/-- **No row reporting the read commits both.**  After the two stamps, if `A`
writes `x`, then no row of any smaller table that reports `B`'s read of `x`
returning `v` (initial, or written by a transaction stamped before `A`) commits
both `A` and `B`. -/
theorem no_both (H : TwoStamps A B ZA ZB σ σ2) {x : K} {v : Option T} (hwA : wr A x)
    (hv : ∀ W, v = some W → ZA W) {R : FinSet T → ROut T K → Prop}
    (hR : ∀ k u, R k u → σ2.R k u) {k : FinSet T} {w : ROut T K} (hw : R k w)
    (hρ : w.ρ B x = some v) : ¬ (w.o.dom A ∧ w.o.dom B) := by
  rintro ⟨hdA, hdB⟩
  obtain ⟨c, hc, hp, hle, hqB⟩ := after_completion H.h2 (hR k w hw)
  have hqA : StampOK A ZA c.o :=
    after_complete H.h1 (R := σ2.R) (fun k u h => H.hs k u ((stamp B ZB).sub _ _ H.h2 k u h))
      hc hp
  have hgA := stamp_guard H.h1
  have hgB := stamp_guard H.h2
  exact stamps_row (permitted_of_row (σ2.sub _ _ hc) hp).1 hqA hqB H.hAB hgB.2.1 hwA
    (fun W e => ⟨hv W e, fun h => hgA.2.1 (h ▸ hv W e)⟩) (le_ρ hle hρ)
    (hle.1.2.1 A hdA) (hle.1.2.1 B hdB)

/-- **What reporting the read commits to.**  After the two stamps (and
anything else), `read(B,x,v)` leaves no row, in any smaller table, that commits
both `A` and `B`. -/
theorem read_no_both (H : TwoStamps A B ZA ZB σ σ2) {x : K} {v : Option T} (hwA : wr A x)
    (hv : ∀ W, v = some W → ZA W) {σ3 σ4 : State (spec rd wr af)}
    (hs3 : ∀ k u, σ3.R k u → σ2.R k u) (h : (read B x v).app σ3 = some σ4)
    {R : FinSet T → ROut T K → Prop} (hR : ∀ k u, R k u → σ4.R k u) {k : FinSet T}
    {w : ROut T K} (hw : R k w) : ¬ (w.o.dom A ∧ w.o.dom B) := by
  rintro ⟨hdA, hdB⟩
  obtain ⟨c, hc, _, hle, hq⟩ := after_completion h (hR k w hw)
  exact H.no_both hwA hv (R := σ4.R) (fun k u h' => hs3 k u ((read B x v).sub _ _ h k u h'))
    hc hq ⟨hle.1.2.1 A hdA, hle.1.2.1 B hdB⟩

/-- **Once `B` is committed, `A`'s abort is entailed.**  Let `τ` be a good state
below the two stamps whose rows all refine an output `u` reporting that `B`
read `v` (initial, or written by a transaction stamped before `A`), with `A`
writing `x`, and whose complete rows all commit `B` (for example after
`commit(B)`, or after emitting an output that commits `B`).  Then no row of `τ`
commits `A`, every complete row aborts `A`, and if `u` is a row at the current
input then so is `u` with `A` aborted, and emitting it is exposable: it applies
no commitment. -/
theorem abort_entailed (H : TwoStamps A B ZA ZB σ σ2) {x : K} {v : Option T}
    (hwA : wr A x) (hv : ∀ W, v = some W → ZA W) {τ : State (spec rd wr af)}
    (hτ : ∀ k u, τ.R k u → σ2.R k u) (hg : Good τ) {u : ROut T K}
    (hall : ∀ k w, τ.R k w → u ≼ w) (hρ : u.ρ B x = some v)
    (hB : ∀ k c, τ.R k c → Partitions k c.o → c.o.dom B) :
    (∀ k w, τ.R k w → ¬ w.o.dom A) ∧
    (∀ k c, τ.R k c → Partitions k c.o → c.o.X A) ∧
    (τ.R τ.cur u → τ.R τ.cur (addAbort u A) ∧ Exposable τ (addAbort u A)) := by
  have noA : ∀ k w, τ.R k w → ¬ w.o.dom A := by
    intro k w hw hdA
    obtain ⟨c, hc, hp, hle, _⟩ := after_completion H.h2 (hτ k w hw)
    obtain ⟨c', hc', hp', hle'⟩ := hg.2 k w hw
    exact H.no_both hwA hv hτ hc' (le_ρ (PO.trans (hall k w hw) hle') hρ)
      ⟨hle'.1.2.1 A hdA, hB k c' hc' hp'⟩
  have hAcur : σ.cur.1 A := (stamp_guard H.h1).1
  have Xc : ∀ k c, τ.R k c → Partitions k c.o → c.o.X A := by
    intro k c hc hp
    have hk : σ.cur ≼ k := σ.above _ _ (H.sub k c (hτ k c hc))
    exact ((hp A).1.1 (hk A hAcur)).resolve_right (noA k c hc)
  refine ⟨noA, Xc, fun hu => ?_⟩
  have up : ∀ k w, τ.R k w → τ.R k (addAbort w A) := by
    intro k w hw
    obtain ⟨c, hc, hp, hle⟩ := hg.2 k w hw
    exact hg.1 k w _ c hw hc (le_addAbort w A) (addAbort_le hle (Xc k c hc hp))
  refine ⟨up _ u hu, fun k w hw _ => ⟨addAbort w A, up k w hw,
    addAbort_mono (hall k w hw) A, le_addAbort w A⟩⟩

end TwoStamps

/-- **Reporting a read after `read(B,x,v)` applies no further commitment.**  At
a good state, after `read(B,x,v)`, if every row refines `u` and `u` is a row,
then `u` with the read fact added is a row at the same input, and emitting it is
exposable. -/
theorem read_emit {B : T} {x : K} {v : Option T} {σ σ' : State (spec rd wr af)}
    (hg : Good σ) (h : (read B x v).app σ = some σ') {u : ROut T K} {k : FinSet T}
    (hu : σ'.R k u) (hall : ∀ k w, σ'.R k w → u ≼ w) :
    σ'.R k (addRead u B x v) ∧ Exposable σ' (addRead u B x v) := by
  have hg' := good_close h hg
  have up : ∀ k w, σ'.R k w → σ'.R k (addRead w B x v) := by
    intro k w hw
    obtain ⟨c, hc, _, hle, hq⟩ := after_completion h hw
    refine hg'.1 k w _ c hw hc (le_addRead fun v' e => ?_) (addRead_le hle hq)
    have := le_ρ hle e; rw [hq] at this; cases this; rfl
  exact ⟨up k u hu, fun k w hw _ => ⟨addRead w B x v, up k w hw,
    addRead_mono (hall k w hw) B x v, (le_addRead fun v' e => by
      obtain ⟨c, _, _, hle, hq⟩ := after_completion h hw
      have := le_ρ hle e; rw [hq] at this; cases this; rfl)⟩⟩

end MVTO

/-! ### Rows that commit nothing; reads and canonical choices at a canonical state -/

/-- The output that decides nothing and reports nothing. -/
def emptyO : Outcome T where
  X _ := False
  dom _ := False
  lt _ _ := False
  irrefl _ h := h
  trans _ _ _ h _ := h
  total _ _ h _ _ := h.elim
  supp _ _ h := h.elim

theorem emptyO_le (o : Outcome T) : emptyO ≼ o :=
  ⟨fun _ h => h.elim, fun _ h => h.elim, fun _ _ h _ => h.elim⟩

/-- `{(A,x) ↦ v}`. -/
noncomputable def single (A : T) (x : K) (v : Option T) : T → K → Option (Option T) :=
  fun a y => if a = A ∧ y = x then some v else none

theorem single_eq {A : T} {x : K} {v : Option T} : single A x v A x = some v := by
  simp [single]

section Canon
variable {rd wr : T → K → Prop}

/-- A row of the specification that commits nothing is refined by the complete
output that aborts everything and reports the same reads. -/
theorem uncommitted_completion {k : FinSet T} {y : ROut T K}
    (hy : (spec rd wr false).S k y) (hd : ∀ t, ¬ y.o.dom t) :
    Permitted rd wr false k ⟨allAbort k, y.ρ⟩ ∧ y ≼ ⟨allAbort k, y.ρ⟩ := by
  obtain ⟨c, ⟨⟨hp, _⟩, _⟩, hle⟩ := hy
  refine ⟨⟨⟨allAbort_part k, fun a x v e => ?_⟩, fun h => by cases h⟩, ?_, fun _ _ _ h => h⟩
  · obtain ⟨h1, h2, h3⟩ := row_read hy' e
    exact ⟨h1, h2, h3, fun h => h.elim⟩
  · refine ⟨fun t hX => ?_, fun t h => absurd h (hd t), fun a _ h _ => absurd h (hd a)⟩
    exact (hp t).1.2 (Or.inl (hle.1.1 t hX))
where hy' : (spec rd wr false).S k y := hy

/-- At a canonical state, a closure commitment for a condition that holds
whenever nothing is committed keeps every row that commits nothing. -/
theorem keeps_uncommitted {k0 : FinSet T} {P : Outcome T → Prop}
    (hP : ∀ o : Outcome T, (∀ a b, ¬ o.lt a b) → P o) {k : FinSet T} {y : ROut T K}
    (hy : (canon (spec rd wr false) k0).R k y) (hd : ∀ t, ¬ y.o.dom t) :
    Keep (canon (spec rd wr false) k0) (fun c => P c.o) k y := by
  obtain ⟨hp, hle⟩ := uncommitted_completion hy.1 hd
  exact ⟨hy, _, ⟨⟨_, hp, PO.refl _⟩, hy.2⟩, allAbort_part k, hle, hP _ fun _ _ h => h⟩

/-- `y = (∅,∅,{(a,x) ↦ v})`, with `a` reading `x` at `k` and `v` present at `k`,
is a row at `k`. -/
theorem single_row {k : FinSet T} {a : T} {x : K} {v : Option T} (ha : k.1 a) (hr : rd a x)
    (hv : Valid wr k x v) :
    (spec rd wr false).S k ⟨emptyO, single a x v⟩ := by
  refine ⟨⟨allAbort k, single a x v⟩, ⟨⟨allAbort_part k, fun b y w e => ?_⟩,
    fun h => by cases h⟩, emptyO_le _, fun _ _ _ h => h⟩
  simp only [single] at e
  split at e
  · rename_i h; obtain ⟨rfl, rfl⟩ := h; cases e; exact ⟨ha, hr, hv, fun h => h.elim⟩
  · cases e

/-- A version of `x` is *forced* at `k` when `v` is the only version present at
`k`: then `v` is the initial version and no transaction of `k` writes `x`. -/
theorem forced_version {k : FinSet T} {x : K} {v : Option T}
    (h : ∀ v', Valid wr k x v' → v' = v) : v = none ∧ ∀ w, k.1 w → ¬ wr w x := by
  have e : v = none := (h none trivial).symm
  refine ⟨e, fun w hw hww => ?_⟩
  have := h (some w) ⟨hw, hww⟩
  rw [e] at this; cases this

/-- Adding forced reads to a complete row keeps it permitted. -/
theorem add_forced {k : FinSet T} {r : ROut T K} (hr : Complete rd wr k r)
    (hρ : ∀ a x, r.ρ a x = none) {ρ' : T → K → Option (Option T)}
    (h : ∀ a x v, ρ' a x = some v →
      k.1 a ∧ rd a x ∧ Valid wr k x v ∧ ∀ v', Valid wr k x v' → v' = v) :
    Complete rd wr k ⟨r.o, ρ'⟩ ∧ r ≼ ⟨r.o, ρ'⟩ := by
  refine ⟨⟨hr.1, fun a x v e => ?_⟩, PO.refl _, fun a x v e => by rw [hρ] at e; cases e⟩
  obtain ⟨h1, h2, h3, h4⟩ := h a x v e
  obtain ⟨rfl, hw⟩ := forced_version h4
  refine ⟨h1, h2, h3, fun _ w hlt hww => hw w ?_ hww⟩
  exact (hr.1 w).1.2 (Or.inr (r.o.supp _ _ hlt).1)

/-- **No read commitment has the effect `τ`** at the canonical state of `k0`,
if `τ` keeps every row at `k0` that commits nothing and removes some complete
row at `k0` that reports no reads. -/
theorem not_read {k0 : FinSet T} {τ : State (spec rd wr false)}
    (hi : ∀ y, (canon (spec rd wr false) k0).R k0 y → (∀ t, ¬ y.o.dom t) → τ.R k0 y)
    {r : ROut T K} (hr : (canon (spec rd wr false) k0).R k0 r) (hrp : Partitions k0 r.o)
    (hrρ : ∀ a x, r.ρ a x = none) (hnr : ¬ τ.R k0 r) (A : T) (x : K) (v : Option T) :
    (read A x v).app (canon (spec rd wr false) k0) ≠ some τ := by
  intro h
  obtain ⟨⟨_, ⟨u, _, c, hc, _, _, hq⟩, _⟩, _, hR⟩ := closeC_app_iff.1 h
  obtain ⟨ha, hrd, hv⟩ := row_read hc.1 hq
  by_cases halt : ∃ v', Valid wr k0 x v' ∧ v' ≠ v
  · obtain ⟨v', hv', hne⟩ := halt
    have hy := single_row (wr := wr) ha hrd hv'
    obtain ⟨_, c', _, _, hle, hq'⟩ := (hR k0 _).1 (hi _ ⟨hy, PO.refl _⟩ fun _ h => h)
    have := le_ρ hle (single_eq (A := A) (x := x) (v := v'))
    rw [hq'] at this; cases this; exact hne rfl
  · have hforced : ∀ v', Valid wr k0 x v' → v' = v := fun v' h' =>
      Classical.byContradiction fun hn => halt ⟨v', h', hn⟩
    have hrc := (permitted_of_row hr.1 hrp).1
    obtain ⟨hc', hle⟩ := add_forced hrc hrρ (ρ' := single A x v) (fun b y w e => by
      simp only [single] at e
      split at e
      · rename_i hb; obtain ⟨rfl, rfl⟩ := hb; cases e; exact ⟨ha, hrd, hv, hforced⟩
      · cases e)
    exact hnr ((hR k0 r).2 ⟨hr, _, ⟨⟨_, ⟨hc', fun h => by cases h⟩, PO.refl _⟩, PO.refl _⟩,
      hrp, hle, single_eq⟩)

/-- **No canonical choice `c_o` has the effect `τ`** at the canonical state of
`k0`, if `τ` keeps every row at `k0` that commits nothing, the complete row
aborting everything, and some complete row aborting nothing (without reads),
and removes some complete row at `k0` that reports no reads. -/
theorem not_choice {k0 : FinSet T} {τ : State (spec rd wr false)}
    (hi : ∀ y, (canon (spec rd wr false) k0).R k0 y → (∀ t, ¬ y.o.dom t) → τ.R k0 y)
    (ha : τ.R k0 (full (allAbort k0))) {c1 : Outcome T} (hc1p : Partitions k0 c1)
    (hc1X : ∀ t, ¬ c1.X t) (hc1 : τ.R k0 (full c1))
    {r : ROut T K} (hr : (canon (spec rd wr false) k0).R k0 r) (hrp : Partitions k0 r.o)
    (hrρ : ∀ a x, r.ρ a x = none) (hnr : ¬ τ.R k0 r) (o : ROut T K) :
    (choiceC o).app (canon (spec rd wr false) k0) ≠ some τ := by
  intro h
  obtain ⟨ho, _, e⟩ := chooseApp_eq.1 h
  let σ0 := canon (spec rd wr false) k0
  have hR : ∀ k u, τ.R k u ↔ σ0.R k u ∧ ¬ Rejected σ0 o k u := by
    intro k u; rw [← e]; exact Iff.rfl
  -- a kept row at `k0` has a common refinement with `o` in `R(k0)`
  have compat : ∀ y, τ.R k0 y → ∃ u, σ0.R k0 u ∧ o ≼ u ∧ y ≼ u := by
    intro y hy
    obtain ⟨hy0, hnrej⟩ := (hR k0 y).1 hy
    by_cases hoy : o ≼ y
    · exact ⟨y, hy0, hoy, PO.refl _⟩
    · have hns : ¬ Sealed σ0 o k0 y := fun hs => hs.2 ⟨o, ho, PO.refl _⟩
      exact Classical.byContradiction fun hn =>
        hnrej ⟨hy0, hoy, hns, fun ⟨_, _, u, hu, hou, hyu⟩ => hn ⟨u, hu, hou, hyu⟩⟩
  -- `o` decides nothing
  have hodom : ∀ t, ¬ o.o.dom t := by
    intro t hdt
    obtain ⟨u, hu, hou, hau⟩ := compat _ ha
    obtain ⟨c, hc, hcu⟩ := hu.1
    have e' := same_o (allAbort_part k0) hc.1.1 (PO.trans hau hcu)
    have : c.o.dom t := hcu.1.2.1 t (hou.1.2.1 t hdt)
    rw [← e'] at this; exact this
  have hoX : ∀ t, ¬ o.o.X t := by
    intro t hXt
    obtain ⟨u, hu, hou, hcu1⟩ := compat _ hc1
    obtain ⟨c, hc, hcu⟩ := hu.1
    have e' := same_o hc1p hc.1.1 (PO.trans hcu1 hcu)
    have : c.o.X t := hcu.1.1 t (hou.1.1 t hXt)
    rw [← e'] at this; exact hc1X t this
  by_cases halt : ∃ a x v v', o.ρ a x = some v ∧ Valid wr k0 x v' ∧ v' ≠ v
  · obtain ⟨a, x, v, v', hov, hv', hne⟩ := halt
    obtain ⟨hak, hrd, _⟩ := row_read ho.1 hov
    have hy := single_row (wr := wr) hak hrd hv'
    obtain ⟨u, _, hou, hyu⟩ := compat _ (hi _ ⟨hy, PO.refl _⟩ fun _ h => h)
    have e1 := le_ρ hou hov
    have e2 := le_ρ hyu (single_eq (A := a) (x := x) (v := v'))
    rw [e1] at e2; cases e2; exact hne rfl
  · have hforced : ∀ a x v, o.ρ a x = some v → ∀ v', Valid wr k0 x v' → v' = v :=
      fun a x v hov v' h' => Classical.byContradiction fun hn => halt ⟨a, x, v, v', hov, h', hn⟩
    have hrc := (permitted_of_row hr.1 hrp).1
    obtain ⟨hc', hle⟩ := add_forced hrc hrρ (ρ' := o.ρ) (fun a x v e =>
      let ⟨h1, h2, h3⟩ := row_read ho.1 e; ⟨h1, h2, h3, hforced a x v e⟩)
    have hr' : σ0.R k0 ⟨r.o, o.ρ⟩ := ⟨⟨_, ⟨hc', fun h => by cases h⟩, PO.refl _⟩, PO.refl _⟩
    have hou : o ≼ ⟨r.o, o.ρ⟩ :=
      ⟨⟨fun t h => absurd h (hoX t), fun t h => absurd h (hodom t),
        fun a _ h _ => absurd h (hodom a)⟩, fun _ _ _ h => h⟩
    refine hnr ((hR k0 r).2 ⟨hr, fun hrej => hrej.2.2.2 ?_⟩)
    exact ⟨hr, hrej.2.1, _, hr', hou, hle⟩

end Canon

/-! ### Figure `fig:cc-commitments` -/

section Figure
variable {sp : Spec (FinSet T) (ROut T K)}

/-- **Fig. (h).**  On complete rows without aborts whose input contains `A`
and `B`, `order(A,B)` keeps exactly those with `A` before `B`. -/
theorem fig_h {A B : T} {σ τ : State sp} (h : (order A B).app σ = some τ) {k : FinSet T}
    {c : ROut T K} (hp : Partitions k c.o) (hX : ∀ t, ¬ c.o.X t) (hA : k.1 A) (hB : k.1 B) :
    τ.R k c ↔ σ.R k c ∧ c.o.lt A B := by
  obtain ⟨⟨⟨hne, _, _⟩, _, _⟩, _, hR⟩ := closeC_app_iff.1 h
  rw [hR, keep_complete hp]
  have dA := ((hp A).1.1 hA).resolve_left (hX A)
  have dB := ((hp B).1.1 hB).resolve_left (hX B)
  refine and_congr_right fun _ => ⟨fun hq => ?_, fun hab hba => c.o.irrefl _ (c.o.trans _ _ _ hab hba)⟩
  exact (c.o.total A B dA dB hne).resolve_right hq

/-- **Fig. (i).**  On complete rows without aborts whose input contains `B`,
`stamp(B)` with no earlier stamps keeps exactly those with `B` first. -/
theorem fig_i {B : T} {σ τ : State sp} (h : (stamp B (fun _ => False)).app σ = some τ)
    {k : FinSet T} {c : ROut T K} (hp : Partitions k c.o) (hX : ∀ t, ¬ c.o.X t)
    (hB : k.1 B) : τ.R k c ↔ σ.R k c ∧ ∀ D, k.1 D → D ≠ B → c.o.lt B D := by
  obtain ⟨_, _, hR⟩ := closeC_app_iff.1 h
  rw [hR, keep_complete hp]
  have dB := ((hp B).1.1 hB).resolve_left (hX B)
  refine and_congr_right fun _ => ⟨fun hq D hD hne => ?_, fun hf => ⟨fun D _ hne hDB => ?_,
    fun _ h => h.elim⟩⟩
  · have dD := ((hp D).1.1 hD).resolve_left (hX D)
    exact (c.o.total B D dB dD (Ne.symm hne)).resolve_right (hq.1 D id hne)
  · have hD := (hp D).1.2 (Or.inr (c.o.supp _ _ hDB).1)
    exact c.o.irrefl _ (c.o.trans _ _ _ hDB (hf D hD hne))

end Figure

/-! ### Rows at `{A,B,C}` -/

/-- The outcome that commits `l` in list order and aborts `Xs`. -/
noncomputable def mk (l : List T) (Xs : T → Prop) : Outcome T := { listOrder l with X := Xs }

theorem mk_dom (l : List T) (Xs : T → Prop) (t : T) : (mk l Xs).dom t ↔ t ∈ l := Iff.rfl
theorem mk_X (l : List T) (Xs : T → Prop) (t : T) : (mk l Xs).X t ↔ Xs t := Iff.rfl

theorem lt3 {a b c : T} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (Xs : T → Prop) (s t : T) :
    (mk [a, b, c] Xs).lt s t ↔ (s = a ∧ (t = b ∨ t = c)) ∨ (s = b ∧ t = c) := by
  show (s ∈ [a, b, c] ∧ t ∈ [a, b, c] ∧ _) ↔ _
  have h1 : [a, b, c].idxOf a = 0 := by simp [List.idxOf_cons]
  have h2 : [a, b, c].idxOf b = 1 := by simp [List.idxOf_cons, hab]
  have h3 : [a, b, c].idxOf c = 2 := by simp [List.idxOf_cons, hac, hbc]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hs, ht, h⟩
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> simp_all
  · rintro (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩) <;> simp_all

theorem lt2 {a b : T} (hab : a ≠ b) (Xs : T → Prop) (s t : T) :
    (mk [a, b] Xs).lt s t ↔ s = a ∧ t = b := by
  show (s ∈ [a, b] ∧ t ∈ [a, b] ∧ _) ↔ _
  have h1 : [a, b].idxOf a = 0 := by simp [List.idxOf_cons]
  have h2 : [a, b].idxOf b = 1 := by simp [List.idxOf_cons, hab]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hs, ht, h⟩
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp_all
  · rintro ⟨rfl, rfl⟩; simp_all

theorem lt1 (a : T) (Xs : T → Prop) (s t : T) : ¬ (mk [a] Xs).lt s t := by
  rintro ⟨hs, ht, h⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ht
  subst hs; subst ht; exact Nat.lt_irrefl _ h

section Three
variable {A B C : T}

/-- Three distinct transactions. -/
structure Distinct3 (A B C : T) : Prop where
  ab : A ≠ B
  ac : A ≠ C
  bc : B ≠ C

/-- The input `{A,B,C}`. -/
noncomputable def tri (A B C : T) (h : Distinct3 A B C) : FinSet T :=
  FinSet.ofList [A, B, C] (by simp [h.ab, h.ac, h.bc])

theorem tri_mem (h : Distinct3 A B C) (t : T) : (tri A B C h).1 t ↔ t = A ∨ t = B ∨ t = C := by
  show t ∈ [A, B, C] ↔ _
  simp

/-- A complete row without aborts or reads at `{A,B,C}`, for each listing of
`A, B, C`. -/
theorem perm_part (h : Distinct3 A B C) {a b c : T}
    (hm : ∀ t, t = a ∨ t = b ∨ t = c ↔ t = A ∨ t = B ∨ t = C) :
    Partitions (tri A B C h) (mk [a, b, c] fun _ => False) := by
  intro t
  refine ⟨?_, fun h' => h'.1⟩
  rw [tri_mem, mk_dom, ← hm]
  constructor
  · intro h'; exact Or.inr (by simpa using h')
  · rintro (h' | h')
    · exact h'.elim
    · simpa using h'

variable {rd wr : T → K → Prop}

theorem perm_row (h : Distinct3 A B C) {a b c : T}
    (hm : ∀ t, t = a ∨ t = b ∨ t = c ↔ t = A ∨ t = B ∨ t = C) :
    (canon (spec rd wr false) (tri A B C h)).R (tri A B C h)
      (full (mk [a, b, c] fun _ => False)) :=
  ⟨⟨_, ⟨full_complete rd wr (perm_part h hm), fun h => by cases h⟩, PO.refl _⟩, PO.refl _⟩

/-- The canonical state of `{A,B,C}`. -/
noncomputable abbrev σABC (rd wr : T → K → Prop) (h : Distinct3 A B C) :
    State (spec rd wr false) := canon (spec rd wr false) (tri A B C h)

theorem allAbort_row (h : Distinct3 A B C) :
    (σABC rd wr h).R (tri A B C h) (full (allAbort (tri A B C h))) :=
  ⟨⟨_, ⟨full_complete rd wr (allAbort_part _), fun h => by cases h⟩, PO.refl _⟩, PO.refl _⟩

theorem hm_id : ∀ t : T, t = A ∨ t = B ∨ t = C ↔ t = A ∨ t = B ∨ t = C := fun _ => Iff.rfl
theorem hm_bac : ∀ t : T, t = B ∨ t = A ∨ t = C ↔ t = A ∨ t = B ∨ t = C := by
  intro t; constructor <;> rintro (h | h | h) <;> simp [h]
theorem hm_cab : ∀ t : T, t = C ∨ t = A ∨ t = B ↔ t = A ∨ t = B ∨ t = C := by
  intro t; constructor <;> rintro (h | h | h) <;> simp [h]
theorem hm_bca : ∀ t : T, t = B ∨ t = C ∨ t = A ↔ t = A ∨ t = B ∨ t = C := by
  intro t; constructor <;> rintro (h | h | h) <;> simp [h]
theorem hm_cba : ∀ t : T, t = C ∨ t = B ∨ t = A ↔ t = A ∨ t = B ∨ t = C := by
  intro t; constructor <;> rintro (h | h | h) <;> simp [h]

/-- Membership of a complete row in the result of a closure commitment for a
condition on `(L,X)`. -/
theorem res_iff {G : State (spec rd wr false) → Prop} {P : Outcome T → Prop}
    {σ τ : State (spec rd wr false)} (hτ : (closeC G (fun c => P c.o)).app σ = some τ)
    {k : FinSet T} {c : ROut T K} (hp : Partitions k c.o) : τ.R k c ↔ σ.R k c ∧ P c.o := by
  rw [(closeC_app_iff.1 hτ).2.2, keep_complete hp]

/-- `order(A,B)` at the canonical state of `{A,B,C}`: defined, it removes
`[B,A,C]` and keeps `[A,B,C]` and `[C,A,B]` (rows at the current input). -/
theorem order_at (h : Distinct3 A B C) :
    ∃ τ, (order A B).app (σABC rd wr h) = some τ ∧
      τ.R (tri A B C h) (full (mk [A, B, C] fun _ => False)) ∧
      τ.R (tri A B C h) (full (mk [C, A, B] fun _ => False)) ∧
      ¬ τ.R (tri A B C h) (full (mk [B, A, C] fun _ => False)) := by
  have hk : ∀ t, (tri A B C h).1 t ↔ _ := tri_mem h
  have d : Defined (fun σ : State (spec rd wr false) => A ≠ B ∧ σ.cur.1 A ∧ σ.cur.1 B)
      (fun c => OrderOK A B c.o) (σABC rd wr h) := by
    refine ⟨⟨h.ab, (hk A).2 (Or.inl rfl), (hk B).2 (Or.inr (Or.inl rfl))⟩,
      ⟨_, (keep_complete (perm_part h hm_id)).2 ⟨perm_row h hm_id, ?_⟩⟩,
      _, _, perm_row h hm_bac, fun hk' => ((keep_complete (perm_part h hm_bac)).1 hk').2 ?_⟩
    · show ¬ (mk [A, B, C] _).lt B A
      rw [lt3 h.ab h.ac h.bc]; simp [h.ab, h.ac, h.bc, Ne.symm h.ab, Ne.symm h.ac, Ne.symm h.bc]
    · show (mk [B, A, C] _).lt B A
      rw [lt3 (Ne.symm h.ab) h.bc h.ac]; simp
  obtain ⟨τ, hτ⟩ : ∃ τ, (order (sp := spec rd wr false) A B).app (σABC rd wr h) = some τ := by
    cases e : (order (sp := spec rd wr false) A B).app (σABC rd wr h) with
    | none => exact absurd d (closeC_none.1 e)
    | some τ => exact ⟨τ, rfl⟩
  refine ⟨τ, hτ, (res_iff hτ (perm_part h hm_id)).2 ⟨perm_row h hm_id, ?_⟩,
    (res_iff hτ (perm_part h hm_cab)).2 ⟨perm_row h hm_cab, ?_⟩,
    fun hm => ((res_iff hτ (perm_part h hm_bac)).1 hm).2 ?_⟩
  · show ¬ (mk [A, B, C] _).lt B A
    rw [lt3 h.ab h.ac h.bc]; simp [h.ab, h.ac, h.bc, Ne.symm h.ab, Ne.symm h.ac, Ne.symm h.bc]
  · show ¬ (mk [C, A, B] _).lt B A
    rw [lt3 (Ne.symm h.ac) (Ne.symm h.bc) h.ab]; simp [h.ab, h.ac, h.bc, Ne.symm h.ab, Ne.symm h.ac, Ne.symm h.bc]
  · show (mk [B, A, C] _).lt B A
    rw [lt3 (Ne.symm h.ab) h.bc h.ac]; simp

theorem lt_ABC (h : Distinct3 A B C) (Xs : T → Prop) (s t : T) :
    (mk [A, B, C] Xs).lt s t ↔ (s = A ∧ (t = B ∨ t = C)) ∨ (s = B ∧ t = C) :=
  lt3 h.ab h.ac h.bc Xs s t
theorem lt_BAC (h : Distinct3 A B C) (Xs : T → Prop) (s t : T) :
    (mk [B, A, C] Xs).lt s t ↔ (s = B ∧ (t = A ∨ t = C)) ∨ (s = A ∧ t = C) :=
  lt3 (Ne.symm h.ab) h.bc h.ac Xs s t
theorem lt_CAB (h : Distinct3 A B C) (Xs : T → Prop) (s t : T) :
    (mk [C, A, B] Xs).lt s t ↔ (s = C ∧ (t = A ∨ t = B)) ∨ (s = A ∧ t = B) :=
  lt3 (Ne.symm h.ac) (Ne.symm h.bc) h.ab Xs s t
theorem lt_BCA (h : Distinct3 A B C) (Xs : T → Prop) (s t : T) :
    (mk [B, C, A] Xs).lt s t ↔ (s = B ∧ (t = C ∨ t = A)) ∨ (s = C ∧ t = A) :=
  lt3 h.bc (Ne.symm h.ab) (Ne.symm h.ac) Xs s t
theorem lt_CBA (h : Distinct3 A B C) (Xs : T → Prop) (s t : T) :
    (mk [C, B, A] Xs).lt s t ↔ (s = C ∧ (t = B ∨ t = A)) ∨ (s = B ∧ t = A) :=
  lt3 (Ne.symm h.bc) (Ne.symm h.ac) (Ne.symm h.ab) Xs s t

/-- Evaluate order facts of the rows at `{A,B,C}`. -/
macro "d3 " h:term : tactic =>
  `(tactic| simp [full, OrderOK, StampOK, AbortOK, CommitOK, mk_dom, lt_ABC $h, lt_BAC $h, lt_CAB $h, lt_BCA $h, lt_CBA $h, ($h).ab, ($h).ac,
    ($h).bc, Ne.symm ($h).ab, Ne.symm ($h).ac, Ne.symm ($h).bc])

/-- `stamp(B)` with no earlier stamps at the canonical state of `{A,B,C}`:
defined, it keeps `[B,A,C]` and `[B,C,A]` and removes `[A,B,C]` and
`[C,B,A]`. -/
theorem stamp_at (h : Distinct3 A B C) :
    ∃ τ, (stamp B (fun _ => False)).app (σABC rd wr h) = some τ ∧
      τ.R (tri A B C h) (full (mk [B, A, C] fun _ => False)) ∧
      τ.R (tri A B C h) (full (mk [B, C, A] fun _ => False)) ∧
      ¬ τ.R (tri A B C h) (full (mk [A, B, C] fun _ => False)) ∧
      ¬ τ.R (tri A B C h) (full (mk [C, B, A] fun _ => False)) := by
  have hk : ∀ t, (tri A B C h).1 t ↔ _ := tri_mem h
  have sBAC : StampOK B (fun _ => False) (mk [B, A, C] fun _ => False) :=
    ⟨fun D _ hne => by d3 h <;> exact hne, fun _ h => h.elim⟩
  have sBCA : StampOK B (fun _ => False) (mk [B, C, A] fun _ => False) :=
    ⟨fun D _ hne => by d3 h <;> exact hne, fun _ h => h.elim⟩
  have nABC : ¬ StampOK B (fun _ => False) (mk [A, B, C] fun _ => False) :=
    fun hs => hs.1 A id h.ab (by d3 h)
  have nCBA : ¬ StampOK B (fun _ => False) (mk [C, B, A] fun _ => False) :=
    fun hs => hs.1 C id (Ne.symm h.bc) (by d3 h)
  have d : Defined (fun σ : State (spec rd wr false) =>
        σ.cur.1 B ∧ ¬ False ∧ ∀ z, False → σ.cur.1 z)
      (fun c => StampOK B (fun _ => False) c.o) (σABC rd wr h) :=
    ⟨⟨(hk B).2 (Or.inr (Or.inl rfl)), id, fun _ h => h.elim⟩,
      ⟨_, (keep_complete (perm_part h hm_bac)).2 ⟨perm_row h hm_bac, sBAC⟩⟩,
      _, _, perm_row h hm_id, fun hk' => nABC ((keep_complete (perm_part h hm_id)).1 hk').2⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, (stamp (sp := spec rd wr false) B (fun _ => False)).app
      (σABC rd wr h) = some τ := by
    cases e : (stamp (sp := spec rd wr false) B (fun _ => False)).app (σABC rd wr h) with
    | none => exact absurd d (closeC_none.1 e)
    | some τ => exact ⟨τ, rfl⟩
  exact ⟨τ, hτ, (res_iff hτ (perm_part h hm_bac)).2 ⟨perm_row h hm_bac, sBAC⟩,
    (res_iff hτ (perm_part h hm_bca)).2 ⟨perm_row h hm_bca, sBCA⟩,
    fun hm => nABC ((res_iff hτ (perm_part h hm_id)).1 hm).2,
    fun hm => nCBA ((res_iff hτ (perm_part h hm_cba)).1 hm).2⟩

/-- The result of `order(A,B)` or `stamp(B)` keeps every row that commits
nothing. -/
theorem order_keeps_uncommitted (h : Distinct3 A B C) {τ : State (spec rd wr false)}
    (hτ : (order A B).app (σABC rd wr h) = some τ) :
    ∀ y, (σABC rd wr h).R (tri A B C h) y → (∀ t, ¬ y.o.dom t) → τ.R (tri A B C h) y :=
  fun y hy hd => ((closeC_app_iff.1 hτ).2.2 _ y).2
    (keeps_uncommitted (P := OrderOK A B) (fun _ ho => ho B A) hy hd)

theorem stamp_keeps_uncommitted (h : Distinct3 A B C) {τ : State (spec rd wr false)}
    (hτ : (stamp B (fun _ => False)).app (σABC rd wr h) = some τ) :
    ∀ y, (σABC rd wr h).R (tri A B C h) y → (∀ t, ¬ y.o.dom t) → τ.R (tri A B C h) y :=
  fun y hy hd => ((closeC_app_iff.1 hτ).2.2 _ y).2
    (keeps_uncommitted (P := StampOK B (fun _ => False))
      (fun _ ho => ⟨fun D _ _ => ho D B, fun _ h => h.elim⟩) hy hd)

/-- **`order(A,B)` is no MVTO commitment**: at the canonical state of
`{A,B,C}`, no commitment of `B_MVTO` has the effect of `order(A,B)`. -/
theorem order_not_MVTO (h : Distinct3 A B C) {τ : State (spec rd wr false)}
    (hτ : (order A B).app (σABC rd wr h) = some τ) :
    ∀ c : Commitment (spec rd wr false), basisMVTO c → c.app (σABC rd wr h) ≠ some τ := by
  have rABC : τ.R (tri A B C h) (full (mk [A, B, C] fun _ => False)) :=
    (res_iff hτ (perm_part h hm_id)).2 ⟨perm_row h hm_id, by show ¬ _; d3 h⟩
  have rCAB : τ.R (tri A B C h) (full (mk [C, A, B] fun _ => False)) :=
    (res_iff hτ (perm_part h hm_cab)).2 ⟨perm_row h hm_cab, by show ¬ _; d3 h⟩
  have nBAC : ¬ τ.R (tri A B C h) (full (mk [B, A, C] fun _ => False)) :=
    fun hm => ((res_iff hτ (perm_part h hm_bac)).1 hm).2 (by show _; d3 h)
  intro c hc e
  rcases hc with ⟨A', Z, rfl⟩ | ⟨A', rfl⟩ | ⟨A', rfl⟩ | ⟨T', x, v, rfl⟩
  · have g := stamp_guard e
    have s1 : StampOK A' Z _ := ((res_iff e (perm_part h hm_id)).1 rABC).2
    have s2 : StampOK A' Z _ := ((res_iff e (perm_part h hm_cab)).1 rCAB).2
    rcases (tri_mem h A').1 g.1 with rfl | rfl | rfl
    · have hZC : ¬ Z C := fun hz => s1.2 C hz (by d3 h)
      exact s2.1 C hZC (Ne.symm h.ac) (by d3 h)
    · have hZC : ¬ Z C := fun hz => s1.2 C hz (by d3 h)
      exact s2.1 C hZC (Ne.symm h.bc) (by d3 h)
    · have hZA : Z A := Classical.byContradiction fun hz => s1.1 A hz h.ac (by d3 h)
      exact s2.2 A hZA (by d3 h)
  · exact nBAC ((res_iff e (perm_part h hm_bac)).2 ⟨perm_row h hm_bac, fun hx => hx⟩)
  · have g : (tri A B C h).1 A' := (closeC_app_iff.1 e).1.1
    have := ((res_iff e (perm_part h hm_id)).1 rABC).2
    exact this (by rw [tri_mem] at g; rcases g with rfl | rfl | rfl <;> d3 h)
  · exact not_read (order_keeps_uncommitted h hτ) (perm_row h hm_bac) (perm_part h hm_bac)
      (fun _ _ => rfl) nBAC T' x v e

/-- **`stamp(B)` (no earlier stamps) is no 2PL commitment**: at the canonical
state of `{A,B,C}`, no commitment of `B_2PL` has its effect. -/
theorem stamp_not_2PL (h : Distinct3 A B C) {τ : State (spec rd wr false)}
    (hτ : (stamp B (fun _ => False)).app (σABC rd wr h) = some τ) :
    ∀ c : Commitment (spec rd wr false), basis2PL c → c.app (σABC rd wr h) ≠ some τ := by
  have sOK : ∀ {l : List T}, StampOK B (fun _ => False) (mk l fun _ => False) ↔
      ∀ D, D ≠ B → ¬ (mk l fun _ => False).lt D B :=
    ⟨fun hs D hne => hs.1 D id hne, fun hf => ⟨fun D _ hne => hf D hne, fun _ h => h.elim⟩⟩
  have iff_of : ∀ {a b c : T} (hm : ∀ t, t = a ∨ t = b ∨ t = c ↔ t = A ∨ t = B ∨ t = C),
      τ.R (tri A B C h) (full (mk [a, b, c] fun _ => False)) ↔
        ∀ D, D ≠ B → ¬ (mk [a, b, c] fun _ => False).lt D B := by
    intro a b c hm
    rw [res_iff hτ (perm_part h hm)]
    exact ⟨fun h' => sOK.1 h'.2, fun h' => ⟨perm_row h hm, sOK.2 h'⟩⟩
  have rBAC := (iff_of hm_bac).2 (fun D hne => by d3 h <;> exact hne)
  have rBCA := (iff_of hm_bca).2 (fun D hne => by d3 h <;> exact hne)
  have nABC : ¬ τ.R _ (full (mk [A, B, C] fun _ => False)) :=
    fun hm => (iff_of hm_id).1 hm A h.ab (by d3 h)
  have nCBA : ¬ τ.R _ (full (mk [C, B, A] fun _ => False)) :=
    fun hm => (iff_of hm_cba).1 hm C (Ne.symm h.bc) (by d3 h)
  intro c hc e
  rcases hc with ⟨A', B', rfl⟩ | ⟨A', rfl⟩ | ⟨A', rfl⟩ | ⟨T', x, v, rfl⟩
  · obtain ⟨hne, hA', hB'⟩ := order_guard e
    have o1 := fun {a b c : T} (hm : ∀ t, t = a ∨ t = b ∨ t = c ↔ t = A ∨ t = B ∨ t = C) =>
      (res_iff e (perm_part h hm) (c := full (mk [a, b, c] fun _ => False)))
    have hA'' : (tri A B C h).1 A' := hA'
    have hB'' : (tri A B C h).1 B' := hB'
    rw [tri_mem] at hA'' hB''
    rcases hA'' with rfl | rfl | rfl <;> rcases hB'' with rfl | rfl | rfl
    · exact hne rfl
    · exact ((o1 hm_bac).1 rBAC).2 (by d3 h)
    · exact ((o1 hm_bca).1 rBCA).2 (by d3 h)
    · exact nCBA ((o1 hm_cba).2 ⟨perm_row h hm_cba, by show ¬ _; d3 h⟩)
    · exact hne rfl
    · exact nABC ((o1 hm_id).2 ⟨perm_row h hm_id, by show ¬ _; d3 h⟩)
    · exact ((o1 hm_bac).1 rBAC).2 (by d3 h)
    · exact ((o1 hm_bac).1 rBAC).2 (by d3 h)
    · exact hne rfl
  · exact nABC ((res_iff e (perm_part h hm_id)).2 ⟨perm_row h hm_id, fun hx => hx⟩)
  · have g : (tri A B C h).1 A' := (closeC_app_iff.1 e).1.1
    have := ((res_iff e (perm_part h hm_bac)).1 rBAC).2
    exact this (by rw [tri_mem] at g; rcases g with rfl | rfl | rfl <;> d3 h)
  · exact not_read (stamp_keeps_uncommitted h hτ) (perm_row h hm_id) (perm_part h hm_id)
      (fun _ _ => rfl) nABC T' x v e

/-- **Neither figure commitment is a canonical choice `c_o`**, for any output
`o`, at the canonical state of `{A,B,C}`. -/
theorem neither_is_choice (h : Distinct3 A B C) :
    (∀ τ, (order A B).app (σABC rd wr h) = some τ →
      ∀ o, (choiceC o).app (σABC rd wr h) ≠ some τ) ∧
    (∀ τ, (stamp B (fun _ => False)).app (σABC rd wr h) = some τ →
      ∀ o, (choiceC o).app (σABC rd wr h) ≠ some τ) := by
  have hX : ∀ {l : List T} t, ¬ (mk l fun _ => False).X t := fun _ h => h
  refine ⟨fun τ hτ o => ?_, fun τ hτ o => ?_⟩
  · have hA : τ.R _ (full (allAbort (tri A B C h))) :=
      order_keeps_uncommitted h hτ _ (allAbort_row h) (fun _ h => h)
    have rABC : τ.R (tri A B C h) (full (mk [A, B, C] fun _ => False)) :=
      (res_iff hτ (perm_part h hm_id)).2 ⟨perm_row h hm_id, by show ¬ _; d3 h⟩
    have nBAC : ¬ τ.R (tri A B C h) (full (mk [B, A, C] fun _ => False)) :=
      fun hm => ((res_iff hτ (perm_part h hm_bac)).1 hm).2 (by show _; d3 h)
    exact not_choice (order_keeps_uncommitted h hτ) hA (perm_part h hm_id) hX rABC
      (perm_row h hm_bac) (perm_part h hm_bac) (fun _ _ => rfl) nBAC o
  · obtain ⟨τ', hτ', rBAC, _, nABC, _⟩ := stamp_at (rd := rd) (wr := wr) h
    rw [hτ] at hτ'; cases hτ'
    have hA : τ.R _ (full (allAbort (tri A B C h))) :=
      stamp_keeps_uncommitted h hτ _ (allAbort_row h) (fun _ h => h)
    exact not_choice (stamp_keeps_uncommitted h hτ) hA (perm_part h hm_bac) hX rBAC
      (perm_row h hm_id) (perm_part h hm_id) (fun _ _ => rfl) nABC o

end Three

/-! ### Membership helpers -/

section Helpers
variable {sp : Spec (FinSet T) (ROut T K)}

theorem exists_of_defined {G : State sp → Prop} {Q : ROut T K → Prop} {σ : State sp}
    (d : Defined G Q σ) : ∃ τ, (closeC G Q).app σ = some τ := by
  cases e : (closeC G Q).app σ with
  | none => exact absurd d (closeC_none.1 e)
  | some τ => exact ⟨τ, rfl⟩

theorem mem_close {G : State sp → Prop} {Q : ROut T K → Prop} {σ τ : State sp}
    (h : (closeC G Q).app σ = some τ) {k : FinSet T} {u c : ROut T K} (hu : σ.R k u)
    (hc : σ.R k c) (hp : Partitions k c.o) (hle : u ≼ c) (hq : Q c) : τ.R k u :=
  ((closeC_app_iff.1 h).2.2 k u).2 ⟨hu, c, hc, hp, hle, hq⟩

theorem not_mem_close {G : State sp → Prop} {P : Outcome T → Prop} {σ τ : State sp}
    (h : (closeC G (fun c => P c.o)).app σ = some τ) {k : FinSet T} {c : ROut T K}
    (hp : Partitions k c.o) (hn : ¬ P c.o) : ¬ τ.R k c :=
  fun hm => hn (after_complete h (R := τ.R) (fun _ _ h => h) hm hp)

end Helpers

/-- Rows below a row are rows (the table is closed downward). -/
def DownClosed {rd wr : T → K → Prop} {af : Bool} (σ : State (spec rd wr af)) : Prop :=
  ∀ k u w, σ.R k w → (spec rd wr af).S k u → u ≼ w → σ.R k u

theorem downClosed_canon {rd wr : T → K → Prop} {af : Bool} (i : FinSet T) :
    DownClosed (canon (spec rd wr af) i) :=
  fun _ _ _ hw hu _ => ⟨hu, hw.2⟩

theorem downClosed_close {rd wr : T → K → Prop} {af : Bool} {G : State (spec rd wr af) → Prop}
    {Q : ROut T K → Prop} {σ τ : State (spec rd wr af)} (h : (closeC G Q).app σ = some τ)
    (hd : DownClosed σ) : DownClosed τ := by
  intro k u w hw hu hle
  obtain ⟨_, _, hR⟩ := closeC_app_iff.1 h
  obtain ⟨hw', c, hc, hp, hwc, hq⟩ := (hR k w).1 hw
  exact (hR k u).2 ⟨hd k u w hw' hu hle, c, hc, hp, PO.trans hle hwc, hq⟩

/-! ### MVTO at `{A,B}`: when aborting `A` is a choice and when it is entailed -/

namespace Ex
variable {rd wr : T → K → Prop} {A B C : T}

/-- The output that decides nothing and reports that `B`'s read of `x`
returned the initial version. -/
noncomputable def u (B : T) (x : K) : ROut T K := addRead (full emptyO) B x none
/-- `B` commits, `A` aborts, with the read. -/
noncomputable def r1 (A B : T) (x : K) : ROut T K := ⟨mk [B] (· = A), (u B x).ρ⟩
/-- `A` commits, `B` aborts, with the read. -/
noncomputable def r2 (A B : T) (x : K) : ROut T K := ⟨mk [A] (· = B), (u B x).ρ⟩
/-- `[A,B]`, no reads. -/
noncomputable def rAB (A B : T) : ROut T K := full (mk [A, B] fun _ => False)

theorem u_ρ (B : T) (x : K) (a : T) (y : K) :
    (u B x).ρ a y = if a = B ∧ y = x then some none else none := rfl

theorem u_le (B : T) (x : K) (o : Outcome T) : u B x ≼ (⟨o, (u B x).ρ⟩ : ROut T K) :=
  ⟨emptyO_le o, fun _ _ _ h => h⟩

theorem part_AB (h : Distinct3 A B C) :
    Partitions (pairSet A B h.ab) (mk [A, B] fun _ => False) := by
  intro t; rw [pairSet_mem, mk_X, mk_dom]; simp
theorem part_BA (h : Distinct3 A B C) :
    Partitions (pairSet A B h.ab) (mk [B, A] fun _ => False) := by
  intro t; rw [pairSet_mem, mk_X, mk_dom]; simp [or_comm]
theorem part_r1 (h : Distinct3 A B C) : Partitions (pairSet A B h.ab) (mk [B] (· = A)) := by
  intro t; rw [pairSet_mem, mk_X, mk_dom]; simp
  rintro rfl; first | exact h.ab | exact fun e => h.ab e.symm | exact Ne.symm h.ab
theorem part_r2 (h : Distinct3 A B C) : Partitions (pairSet A B h.ab) (mk [A] (· = B)) := by
  intro t; rw [pairSet_mem, mk_X, mk_dom]; simp [or_comm]
  rintro rfl; first | exact h.ab | exact fun e => h.ab e.symm | exact Ne.symm h.ab

theorem complete_read {k : FinSet T} {o : Outcome T} {x : K} (hp : Partitions k o)
    (hB : k.1 B) (hr : rd B x) (hlw : o.dom B → ∀ w, o.lt w B → ¬ wr w x) :
    Complete rd wr k ⟨o, (u B x).ρ⟩ := by
  refine ⟨hp, fun a y v e => ?_⟩
  rw [u_ρ] at e
  split at e
  · rename_i hay; obtain ⟨rfl, rfl⟩ := hay; cases e; exact ⟨hB, hr, trivial, hlw⟩
  · cases e

theorem canon_row {k0 k : FinSet T} {c : ROut T K} (hc : Complete rd wr k c) (hk : k0 ≼ k) :
    (canon (spec rd wr false) k0).R k c :=
  ⟨⟨c, ⟨hc, fun h => by cases h⟩, PO.refl _⟩, hk⟩

/-- **MVTO at `{A,B}`** (with a third transaction `C` that may arrive later).
`A` writes `x` and `B` reads `x`.  From the canonical state of `{A,B}`:
`stamp(A)` (first), then `stamp(B)` (after `A`).

1. Reporting that `B` read the initial version of `x` is not exposable: the row
   `[A,B]` (both committed, `A` first) cannot be completed with that read.
   `read(B,x,initial)` removes it, and the output event
   `Out_{read(B,x,initial)}(u)` reporting the read is legal under `B_MVTO`.
2. After it, both completions remain: `r1` (`B` commits, `A` aborts) and `r2`
   (`A` commits, `B` aborts).  Aborting `A` is a choice: emitting `A`'s abort
   is not exposable, and `abort(A)` and `abort(B)` are both defined and keep
   different completions.
3. Once `commit(B)` is applied, `A`'s abort is entailed: `u` with `A` aborted
   is a row and emitting it is exposable. -/
theorem mvto_instance (h : Distinct3 A B C) {x : K} (hwA : wr A x) (hrB : rd B x) :
    ∃ σ1 σ2 σ3 τ : State (spec rd wr false),
      (stamp A (fun _ => False)).app (canon _ (pairSet A B h.ab)) = some σ1 ∧
      (stamp B (· = A)).app σ1 = some σ2 ∧
      σ2.R (pairSet A B h.ab) (rAB A B) ∧ ¬ Exposable σ2 (u B x) ∧
      (read B x none).app σ2 = some σ3 ∧ ¬ σ3.R (pairSet A B h.ab) (rAB A B) ∧
      SysStep basisMVTO σ2 (.output [read B x none] (u B x)) τ ∧
      τ.R (pairSet A B h.ab) (r1 A B x) ∧ τ.R (pairSet A B h.ab) (r2 A B x) ∧
      ¬ Exposable τ (addAbort (u B x) A) ∧
      (∃ τA, (abort A).app τ = some τA ∧
        τA.R (pairSet A B h.ab) (r1 A B x) ∧ ¬ τA.R (pairSet A B h.ab) (r2 A B x)) ∧
      (∃ τB, (abort B).app τ = some τB ∧
        τB.R (pairSet A B h.ab) (r2 A B x) ∧ ¬ τB.R (pairSet A B h.ab) (r1 A B x)) ∧
      (∃ τC, (commit B).app τ = some τC ∧
        τC.R (pairSet A B h.ab) (addAbort (u B x) A) ∧ Exposable τC (addAbort (u B x) A)) := by
  let k2 := pairSet A B h.ab
  let k3 := tri A B C h
  let σ0 := canon (spec rd wr false) k2
  have hk2 : ∀ t, k2.1 t ↔ t = A ∨ t = B := pairSet_mem
  have hA2 : k2.1 A := (hk2 A).2 (Or.inl rfl)
  have hB2 : k2.1 B := (hk2 B).2 (Or.inr rfl)
  have k23 : k2 ≼ k3 := fun t ht => by
    rw [tri_mem]; rcases (hk2 t).1 ht with rfl | rfl <;> simp
  have l2 : ∀ s t, (mk [A, B] fun _ => False).lt s t ↔ s = A ∧ t = B := lt2 h.ab _
  have l2' : ∀ s t, (mk [B, A] fun _ => False).lt s t ↔ s = B ∧ t = A := lt2 (Ne.symm h.ab) _
  have lACB : ∀ s t, (mk [A, C, B] fun _ => False).lt s t ↔
      (s = A ∧ (t = C ∨ t = B)) ∨ (s = C ∧ t = B) := lt3 h.ac h.ab (Ne.symm h.bc) _
  have hm_acb : ∀ t : T, t = A ∨ t = C ∨ t = B ↔ t = A ∨ t = B ∨ t = C := by
    intro t; constructor <;> rintro (h | h | h) <;> simp [h]
  have pACB := perm_part h hm_acb
  -- complete rows
  have cAB : Complete rd wr k2 (rAB A B) := full_complete rd wr (part_AB h)
  have cBA : Complete rd wr k2 (full (K := K) (mk [B, A] fun _ => False)) :=
    full_complete rd wr (part_BA h)
  have c1 : Complete rd wr k2 (r1 A B x) :=
    complete_read (part_r1 h) hB2 hrB (fun _ w hw => absurd hw (lt1 _ _ _ _))
  have c2 : Complete rd wr k2 (r2 A B x) :=
    complete_read (part_r2 h) hB2 hrB (fun hd => by
      have : B ∈ [A] := hd
      simp at this; exact absurd this.symm h.ab)
  have cACB : Complete rd wr k3 (full (K := K) (mk [A, C, B] fun _ => False)) :=
    full_complete rd wr pACB
  -- stamp conditions
  have sA_AB : StampOK A (fun _ => False) (mk [A, B] fun _ => False) :=
    ⟨fun D _ hne hD => by rw [l2] at hD; exact hne hD.1, fun _ h => h.elim⟩
  have sB_AB : StampOK B (· = A) (mk [A, B] fun _ => False) :=
    ⟨fun D hD _ hl => by rw [l2] at hl; exact hD hl.1,
     fun _ _ hl => by rw [l2] at hl; exact h.ab hl.1.symm⟩
  have sA_1 : StampOK A (fun _ => False) (r1 A B x).o :=
    ⟨fun _ _ _ hl => lt1 _ _ _ _ hl, fun _ h => h.elim⟩
  have sB_1 : StampOK B (· = A) (r1 A B x).o :=
    ⟨fun _ _ _ hl => lt1 _ _ _ _ hl, fun _ _ hl => lt1 _ _ _ _ hl⟩
  have sA_2 : StampOK A (fun _ => False) (r2 A B x).o :=
    ⟨fun _ _ _ hl => lt1 _ _ _ _ hl, fun _ h => h.elim⟩
  have sB_2 : StampOK B (· = A) (r2 A B x).o :=
    ⟨fun _ _ _ hl => lt1 _ _ _ _ hl, fun _ _ hl => lt1 _ _ _ _ hl⟩
  have sA_ACB : StampOK A (fun _ => False) (mk [A, C, B] fun _ => False) :=
    ⟨fun D _ _ hl => by
      rw [lACB] at hl
      rcases hl with ⟨_, e | e⟩ | ⟨_, e⟩
      · exact h.ac e
      · exact h.ab e
      · exact h.ab e, fun _ h => h.elim⟩
  have nB_ACB : ¬ StampOK B (· = A) (mk [A, C, B] fun _ => False) :=
    fun hs => hs.1 C (fun e => h.ac e.symm) (Ne.symm h.bc) ((lACB C B).2 (Or.inr ⟨rfl, rfl⟩))
  -- σ1
  obtain ⟨σ1, h1⟩ := exists_of_defined (sp := spec rd wr false)
    (G := fun σ => σ.cur.1 A ∧ ¬ False ∧ ∀ z, False → σ.cur.1 z)
    (Q := fun c => StampOK A (fun _ => False) c.o) (σ := σ0)
    ⟨⟨hA2, id, fun _ h => h.elim⟩,
     ⟨_, (keep_complete (part_AB h)).2 ⟨canon_row cAB (PO.refl _), sA_AB⟩⟩,
     _, _, canon_row cBA (PO.refl _), fun hk => ((keep_complete (part_BA h)).1 hk).2.1 B id
       (Ne.symm h.ab) ((l2' B A).2 ⟨rfl, rfl⟩)⟩
  have m1 : ∀ {k} {c : ROut T K}, Complete rd wr k c → k2 ≼ k →
      StampOK A (fun _ => False) c.o → σ1.R k c :=
    fun hc hk hs => mem_close h1 (canon_row hc hk) (canon_row hc hk) hc.1 (PO.refl _) hs
  -- σ2
  obtain ⟨σ2, h2⟩ := exists_of_defined (sp := spec rd wr false)
    (G := fun σ => σ.cur.1 B ∧ ¬ (B = A) ∧ ∀ z, z = A → σ.cur.1 z)
    (Q := fun c => StampOK B (· = A) c.o) (σ := σ1)
    ⟨⟨by rw [(closeC_app_iff.1 h1).2.1]; exact hB2, fun e => h.ab e.symm,
      fun z hz => by rw [(closeC_app_iff.1 h1).2.1, hz]; exact hA2⟩,
     ⟨rAB A B, by
        rw [(closeC_app_iff.1 h1).2.1]
        exact (keep_complete (part_AB h)).2 ⟨m1 cAB (PO.refl _) sA_AB, sB_AB⟩⟩,
     _, _, m1 cACB k23 sA_ACB, fun hk => nB_ACB ((keep_complete pACB).1 hk).2⟩
  have m2 : ∀ {k} {c : ROut T K}, Complete rd wr k c → k2 ≼ k →
      StampOK A (fun _ => False) c.o → StampOK B (· = A) c.o → σ2.R k c :=
    fun hc hk hs hs' => mem_close h2 (m1 hc hk hs) (m1 hc hk hs) hc.1 (PO.refl _) hs'
  have cur2 : σ2.cur = k2 := by
    rw [(closeC_app_iff.1 h2).2.1, (closeC_app_iff.1 h1).2.1]; rfl
  -- the row `[A,B]` cannot report the read
  have noAB : ∀ {w : ROut T K}, (spec rd wr false).S k2 w → rAB A B ≼ w →
      w.ρ B x = some none → False := by
    intro w hw hle e
    obtain ⟨c, hc, hwc⟩ := hw
    have eo := same_o (part_AB h) hc.1.1 (PO.trans hle hwc)
    have hdB : c.o.dom B := by rw [← eo]; show B ∈ [A, B]; simp
    have hlw := (hc.1.2 B x none (le_ρ hwc e)).2.2.2 hdB
    exact hlw A (by rw [← eo]; exact (l2 A B).2 ⟨rfl, rfl⟩) hwA
  have rAB2 : σ2.R k2 (rAB A B) := m2 cAB (PO.refl _) sA_AB sB_AB
  -- σ3
  have r1_2 : σ2.R k2 (r1 A B x) := m2 c1 (PO.refl _) sA_1 sB_1
  have r2_2 : σ2.R k2 (r2 A B x) := m2 c2 (PO.refl _) sA_2 sB_2
  obtain ⟨σ3, h3⟩ := exists_of_defined (sp := spec rd wr false)
    (G := fun σ => σ.cur.1 B) (Q := fun c => c.ρ B x = some none) (σ := σ2)
    ⟨by show σ2.cur.1 B; rw [cur2]; exact hB2, ⟨r1 A B x, by rw [cur2]; exact
        ⟨r1_2, _, r1_2, part_r1 h, PO.refl _, addRead_ρ (full emptyO) B x none⟩⟩,
     _, _, rAB2, fun ⟨_, c, hc, _, hle, hq⟩ => noAB (σ2.sub _ _ hc) hle hq⟩
  have cur3 : σ3.cur = k2 := by rw [(closeC_app_iff.1 h3).2.1, cur2]
  have m3 : ∀ {c : ROut T K}, σ2.R k2 c → Partitions k2 c.o → c.ρ B x = some none →
      σ3.R k2 c :=
    fun hc hp hq => mem_close h3 hc hc hp (PO.refl _) hq
  have r1_3 := m3 r1_2 (part_r1 h) (addRead_ρ (full emptyO) B x none)
  have r2_3 := m3 r2_2 (part_r2 h) (addRead_ρ (full emptyO) B x none)
  have good3 : Good σ3 := good_close h3 (good_close h2 (good_close h1 (good_canon k2)))
  have dc3 : DownClosed σ3 :=
    downClosed_close h3 (downClosed_close h2 (downClosed_close h1 (downClosed_canon k2)))
  have e0_3 : σ3.R k2 (full emptyO) :=
    dc3 _ _ _ r1_3 (spec_down (σ3.sub _ _ r1_3) ⟨emptyO_le _, fun _ _ _ h => by cases h⟩)
      ⟨emptyO_le _, fun _ _ _ h => by cases h⟩
  have hall0 : ∀ k w, σ3.R k w → (full emptyO : ROut T K) ≼ w :=
    fun _ w _ => ⟨emptyO_le _, fun _ _ _ h => by cases h⟩
  obtain ⟨u3, uexp⟩ := read_emit (good_close h2 (good_close h1 (good_canon k2))) h3 e0_3 hall0
  have u3' : σ3.R σ3.cur (u B x) := by rw [cur3]; exact u3
  let τ := outState σ3 (u B x) u3'
  have hτ : ∀ k w, τ.R k w ↔ σ3.R k w ∧ u B x ≼ w := fun _ _ => Iff.rfl
  have step : SysStep basisMVTO σ2 (.output [read B x none] (u B x)) τ :=
    SysStep.output (fun c hc => by
        simp only [List.mem_singleton] at hc; subst hc
        exact Or.inr (Or.inr (Or.inr ⟨B, x, none, rfl⟩)))
      (ApplySeq.cons h3 (ApplySeq.nil _)) u3' uexp ((closeC_app_iff.1 h3).2.1) rfl
  have curτ : τ.cur = k2 := cur3
  have r1τ : τ.R k2 (r1 A B x) := (hτ _ _).2 ⟨r1_3, u_le B x _⟩
  have r2τ : τ.R k2 (r2 A B x) := (hτ _ _).2 ⟨r2_3, u_le B x _⟩
  have goodτ : Good τ := good_outputTable rfl good3
  -- claims
  refine ⟨σ1, σ2, σ3, τ, h1, h2, rAB2, ?_, h3, ?_, step, r1τ, r2τ, ?_, ?_, ?_, ?_⟩
  · -- reporting the read is not exposable before `read(B,x,initial)`
    intro hex
    obtain ⟨w, hw, hu, hle⟩ := hex k2 (rAB A B) rAB2 (fun hle => by
      have := le_ρ hle (addRead_ρ (full emptyO) B x none); cases this)
    exact noAB (σ2.sub _ _ hw) hle (le_ρ hu (addRead_ρ _ B x none))
  · exact fun hm => let ⟨_, c, hc, _, hle, hq⟩ := ((closeC_app_iff.1 h3).2.2 _ _).1 hm
      noAB (σ2.sub _ _ hc) hle hq
  · -- aborting `A` is not exposable
    intro hex
    obtain ⟨w, hw, hle1, hle2⟩ := hex k2 (r2 A B x) r2τ (fun hle => by
      have : (mk [A] (· = B)).X A := hle.1.1 A (Or.inr rfl)
      exact h.ab this)
    obtain ⟨c, hc, hwc⟩ := (τ.sub _ _ hw)
    exact (hc.1.1 A).2 ⟨hwc.1.1 A (hle1.1.1 A (Or.inr rfl)),
      hwc.1.2.1 A (hle2.1.2.1 A (show A ∈ [A] by simp))⟩
  · obtain ⟨τA, hA⟩ := exists_of_defined (sp := spec rd wr false) (G := fun σ => σ.cur.1 A)
      (Q := fun c => AbortOK A c.o) (σ := τ)
      ⟨by show τ.cur.1 A; rw [curτ]; exact hA2, ⟨r1 A B x, by rw [curτ]; exact
          ⟨r1τ, _, r1τ, part_r1 h, PO.refl _, fun hd => by
            have : A ∈ [B] := hd; simp at this; exact h.ab this⟩⟩,
       _, _, r2τ, fun hk => ((keep_complete (part_r2 h)).1 hk).2 (show A ∈ [A] by simp)⟩
    exact ⟨τA, hA, mem_close hA r1τ r1τ (part_r1 h) (PO.refl _) (fun hd => by
        have : A ∈ [B] := hd; simp at this; exact h.ab this),
      not_mem_close hA (part_r2 h) (fun hn => hn (show A ∈ [A] by simp))⟩
  · obtain ⟨τB, hB⟩ := exists_of_defined (sp := spec rd wr false) (G := fun σ => σ.cur.1 B)
      (Q := fun c => AbortOK B c.o) (σ := τ)
      ⟨by show τ.cur.1 B; rw [curτ]; exact hB2, ⟨r2 A B x, by rw [curτ]; exact
          ⟨r2τ, _, r2τ, part_r2 h, PO.refl _, fun hd => by
            have : B ∈ [A] := hd; simp at this; exact h.ab this.symm⟩⟩,
       _, _, r1τ, fun hk => ((keep_complete (part_r1 h)).1 hk).2 (show B ∈ [B] by simp)⟩
    exact ⟨τB, hB, mem_close hB r2τ r2τ (part_r2 h) (PO.refl _) (fun hd => by
        have : B ∈ [A] := hd; simp at this; exact h.ab this.symm),
      not_mem_close hB (part_r1 h) (fun hn => hn (show B ∈ [B] by simp))⟩
  · have ok1 : CommitOK B (r1 A B x).o := fun hX => h.ab (show B = A from hX).symm
    obtain ⟨τC, hC⟩ := exists_of_defined (sp := spec rd wr false) (G := fun σ => σ.cur.1 B)
      (Q := fun c => CommitOK B c.o) (σ := τ)
      ⟨by show τ.cur.1 B; rw [curτ]; exact hB2, ⟨r1 A B x, by rw [curτ]; exact
          ⟨r1τ, _, r1τ, part_r1 h, PO.refl _, ok1⟩⟩,
       _, _, r2τ, fun hk => ((keep_complete (part_r2 h)).1 hk).2 (show B = B from rfl)⟩
    have curC : τC.cur = k2 := by rw [(closeC_app_iff.1 hC).2.1, curτ]
    have H : TwoStamps A B (fun _ => False) (· = A) σ0 σ2 := ⟨σ1, σ1, h1, fun _ _ h => h, h2, rfl⟩
    have hsubC : ∀ k w, τC.R k w → τ.R k w := (commit B).sub _ _ hC
    have hτ2 : ∀ k w, τC.R k w → σ2.R k w := fun k w hw =>
      (read B x none).sub _ _ h3 k w ((hτ k w).1 (hsubC k w hw)).1
    have hBdom : ∀ k c, τC.R k c → Partitions k c.o → c.o.dom B := by
      intro k c hc hp
      have hk : k2 ≼ k := σ0.above _ _ (H.sub k c (hτ2 k c hc))
      exact ((hp B).1.1 (hk B hB2)).resolve_left (after_complete hC (fun _ _ h => h) hc hp)
    have uC : τC.R τC.cur (u B x) := by
      rw [curC]
      exact mem_close hC ((hτ _ _).2 ⟨u3, PO.refl _⟩) r1τ (part_r1 h) (u_le B x _) ok1
    obtain ⟨_, _, hent⟩ := H.abort_entailed hwA (fun _ e => by cases e) hτ2
      (good_close hC goodτ) (fun k w hw => ((hτ k w).1 (hsubC k w hw)).2)
      (addRead_ρ _ B x none) hBdom
    obtain ⟨hm, hex⟩ := hent uC
    rw [curC] at hm
    exact ⟨τC, hC, hm, hex⟩

end Ex

/-! ### The writer must be stamped before `A` -/

/-- **The hypothesis on the version cannot be dropped.**  At `{A,W,B}`, stamped
`A`, `W`, `B` in that order, with `A` and `W` writing `x` and `B` reading it,
the complete row that commits all three in stamp order and reports that `B`
read `W`'s write is permitted, satisfies every stamp, and commits `A`. -/
theorem writer_after_A {rd wr : T → K → Prop} {A W B : T} (h : Distinct3 A W B) {x : K}
    (hwA : wr A x) (hwW : wr W x) (hrB : rd B x) :
    let r : ROut T K := ⟨mk [A, W, B] fun _ => False, single B x (some W)⟩
    Complete rd wr (tri A W B h) r ∧ StampOK A (fun _ => False) r.o ∧
      StampOK W (· = A) r.o ∧ StampOK B (fun z => z = A ∨ z = W) r.o ∧
      wr A x ∧ r.ρ B x = some (some W) ∧ r.o.dom A := by
  intro r
  have l : ∀ s t, r.o.lt s t ↔ (s = A ∧ (t = W ∨ t = B)) ∨ (s = W ∧ t = B) :=
    lt3 h.ab h.ac h.bc _
  have hk := tri_mem h
  refine ⟨⟨perm_part h hm_id, fun a y v e => ?_⟩, ⟨fun D _ hne hl => ?_, fun _ h => h.elim⟩,
    ⟨fun D hD hne hl => ?_, fun z hz hl => ?_⟩, ⟨fun D hD hne hl => ?_, fun z hz hl => ?_⟩,
    hwA, single_eq, show A ∈ [A, W, B] by simp⟩
  · simp only [r, single] at e
    split at e
    · rename_i hay; obtain ⟨rfl, rfl⟩ := hay; cases e
      refine ⟨(hk _).2 (by simp), hrB, ⟨(hk _).2 (by simp), hwW⟩, fun _ => ?_⟩
      refine ⟨(l W a).2 (Or.inr ⟨rfl, rfl⟩), hwW, fun w' h1 h2 => ?_⟩
      rw [l] at h1 h2
      rcases h1 with ⟨e1, _⟩ | ⟨_, rfl⟩
      · exact absurd e1.symm h.ab
      · rcases h2 with ⟨e2, _⟩ | ⟨e2, _⟩
        · exact absurd e2 (Ne.symm h.ac)
        · exact absurd e2 (Ne.symm h.bc)
    · cases e
  all_goals
    revert hl; rw [l]
    have := h.ab; have := h.ac; have := h.bc
    have := Ne.symm h.ab; have := Ne.symm h.ac; have := Ne.symm h.bc
    simp_all

end Partial
end Txn
end CC
