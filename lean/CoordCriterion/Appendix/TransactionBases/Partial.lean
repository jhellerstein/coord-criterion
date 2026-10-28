import CoordCriterion.Appendix.TransactionBases.Spec

/-!
# Commitment bases for 2PL and MVTO (Appendix G, `app:cc-bases`)

Namespace `CC.Txn.Partial`.  The specification is in `Spec.lean`.

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
  completable; `read_emit`, `abort_emit` — after `read(B,n,v)` (resp.
  `abort(A)`), emitting the read (resp. the abort) is exposable.
* `fig_h`, `fig_i`, `order_at`, `stamp_at`, `order_not_MVTO`, `stamp_not_2PL`,
  `not_read`, `not_choice`, `neither_is_choice` — Fig. `fig:cc-commitments`
  and the bases differ, at the canonical state of three transactions that have
  requested commit.
* `deadlock`, `deadlock_complete`, `deadlock_commit`, `abortFree_deadlock`,
  `abortFree_never_both` — 2PL deadlock.
* `stamps_row`, `TwoStamps.no_both`, `TwoStamps.read_no_both`,
  `TwoStamps.abort_entailed` — MVTO: what a reported read commits to, and when
  `A`'s abort is entailed.  The run in which it is a choice is in `MVTO.lean`.

Modeling choices: the guards ("`A ∈ i`", "`A` has requested commit", "the
`n`-th operation of `A` is a read", etc.) are part of definedness.
-/

namespace CC
namespace Txn
namespace Partial

open Classical

set_option linter.unusedSimpArgs false

variable {T K : Type}

/-! ### Closure commitments -/

section Closure
variable {af : Bool}

/-- Row `(k,u)` of `σ` is kept by the condition `Q` on complete outputs: some
row of `σ` at `k` that is complete at `k`, refines `u`, and satisfies `Q`,
remains. -/
def Keep (σ : State (spec (T := T) (K := K) af)) (Q : ROut T K → Prop) (k : Inp T K)
    (u : ROut T K) : Prop :=
  σ.R k u ∧ ∃ c, σ.R k c ∧ Decides af k c.o ∧ u ≼ c ∧ Q c

/-- Definedness: the guard holds, some row at the current input is kept, and
some row is removed. -/
def Defined (G : State (spec (T := T) (K := K) af) → Prop) (Q : ROut T K → Prop)
    (σ : State (spec (T := T) (K := K) af)) : Prop :=
  G σ ∧ (∃ u, Keep σ Q σ.cur u) ∧ ∃ k u, σ.R k u ∧ ¬ Keep σ Q k u

/-- The state `(i, {kept rows})`. -/
def keepState (σ : State (spec (T := T) (K := K) af)) (Q : ROut T K → Prop)
    (h : ∃ u, Keep σ Q σ.cur u) : State (spec (T := T) (K := K) af) where
  cur := σ.cur
  R := Keep σ Q
  sub k u h := σ.sub k u h.1
  hasCur := h
  above k u h := σ.above k u h.1

noncomputable def closeApp (G : State (spec (T := T) (K := K) af) → Prop) (Q : ROut T K → Prop)
    (σ : State (spec (T := T) (K := K) af)) : Option (State (spec (T := T) (K := K) af)) :=
  if h : Defined G Q σ then some (keepState σ Q h.2.1) else none

theorem closeApp_eq {G : State (spec (T := T) (K := K) af) → Prop} {Q : ROut T K → Prop}
    {σ τ : State (spec (T := T) (K := K) af)} :
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
noncomputable def closeC (G : State (spec (T := T) (K := K) af) → Prop) (Q : ROut T K → Prop) :
    Commitment (spec (T := T) (K := K) af) where
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

theorem closeC_app_iff {G : State (spec (T := T) (K := K) af) → Prop} {Q : ROut T K → Prop}
    {σ τ : State (spec (T := T) (K := K) af)} :
    (closeC G Q).app σ = some τ ↔
      Defined G Q σ ∧ τ.cur = σ.cur ∧ ∀ k u, τ.R k u ↔ Keep σ Q k u := by
  show closeApp G Q σ = some τ ↔ _
  rw [closeApp_eq]
  constructor
  · rintro ⟨hd, rfl⟩; exact ⟨hd, rfl, fun _ _ => Iff.rfl⟩
  · rintro ⟨hd, hc, hR⟩
    refine ⟨hd, State.ext' hc.symm ?_⟩
    funext k u; exact (propext (hR k u)).symm

theorem closeC_none {G : State (spec (T := T) (K := K) af) → Prop} {Q : ROut T K → Prop}
    {σ : State (spec (T := T) (K := K) af)} : (closeC G Q).app σ = none ↔ ¬ Defined G Q σ := by
  show closeApp G Q σ = none ↔ _
  unfold closeApp
  split
  · rename_i h; simp only [reduceCtorEq, false_iff]; exact fun hn => hn h
  · rename_i h; simp only [true_iff]; exact h

/-- A complete row is kept exactly when it satisfies a condition on `(L,X)`. -/
theorem keep_complete {σ : State (spec (T := T) (K := K) af)} {P : Outcome T → Prop}
    {k : Inp T K} {c : ROut T K} (hp : Decides af k c.o) :
    Keep σ (fun c => P c.o) k c ↔ σ.R k c ∧ P c.o := by
  constructor
  · rintro ⟨h, c', _, hp', hle, hq⟩
    exact ⟨h, (same_o hp hp' hle) ▸ hq⟩
  · rintro ⟨h, hq⟩
    exact ⟨h, c, h, hp, PO.refl _, hq⟩

/-- After a closure commitment, every row has a remaining complete refinement
satisfying `Q`. -/
theorem after_completion {G : State (spec (T := T) (K := K) af) → Prop} {Q : ROut T K → Prop}
    {σ τ : State (spec (T := T) (K := K) af)} (h : (closeC G Q).app σ = some τ) {k : Inp T K} {u : ROut T K}
    (hu : τ.R k u) : ∃ c, τ.R k c ∧ Decides af k c.o ∧ u ≼ c ∧ Q c := by
  obtain ⟨_, _, hR⟩ := closeC_app_iff.1 h
  obtain ⟨_, c, hc, hp, hle, hq⟩ := (hR k u).1 hu
  exact ⟨c, (hR k c).2 ⟨hc, c, hc, hp, PO.refl _, hq⟩, hp, hle, hq⟩

/-- After a closure commitment for a condition on `(L,X)`, every complete row
of every smaller table satisfies it. -/
theorem after_complete {G : State (spec (T := T) (K := K) af) → Prop} {P : Outcome T → Prop}
    {σ τ : State (spec (T := T) (K := K) af)} (h : (closeC G (fun c => P c.o)).app σ = some τ)
    {R : Inp T K → ROut T K → Prop} (hR : ∀ k u, R k u → τ.R k u) {k : Inp T K}
    {c : ROut T K} (hc : R k c) (hp : Decides af k c.o) : P c.o := by
  obtain ⟨_, _, hR'⟩ := closeC_app_iff.1 h
  exact ((keep_complete hp).1 ((hR' k c).1 (hR k c hc))).2

/-- The current input only grows: if `τ`'s table is contained in `σ`'s, then
`σ.cur ≼ τ.cur`. -/
theorem cur_mono {sp : Spec (Inp T K) (ROut T K)} {σ τ : State sp}
    (h : ∀ k u, τ.R k u → σ.R k u) : σ.cur ≼ τ.cur :=
  let ⟨_, ho⟩ := τ.hasCur; σ.above _ _ (h _ _ ho)

theorem exists_of_defined {G : State (spec (T := T) (K := K) af) → Prop} {Q : ROut T K → Prop}
    {σ : State (spec (T := T) (K := K) af)} (d : Defined G Q σ) : ∃ τ, (closeC G Q).app σ = some τ := by
  cases e : (closeC G Q).app σ with
  | none => exact absurd d (closeC_none.1 e)
  | some τ => exact ⟨τ, rfl⟩

theorem mem_close {G : State (spec (T := T) (K := K) af) → Prop} {Q : ROut T K → Prop}
    {σ τ : State (spec (T := T) (K := K) af)} (h : (closeC G Q).app σ = some τ) {k : Inp T K} {u c : ROut T K}
    (hu : σ.R k u) (hc : σ.R k c) (hp : Decides af k c.o) (hle : u ≼ c) (hq : Q c) : τ.R k u :=
  ((closeC_app_iff.1 h).2.2 k u).2 ⟨hu, c, hc, hp, hle, hq⟩

theorem not_mem_close {G : State (spec (T := T) (K := K) af) → Prop} {P : Outcome T → Prop}
    {σ τ : State (spec (T := T) (K := K) af)} (h : (closeC G (fun c => P c.o)).app σ = some τ) {k : Inp T K}
    {c : ROut T K} (hp : Decides af k c.o) (hn : ¬ P c.o) : ¬ τ.R k c :=
  fun hm => hn (after_complete h (R := τ.R) (fun _ _ h => h) hm hp)

/-- Membership of a complete row in the result of a closure commitment for a
condition on `(L,X)`. -/
theorem res_iff {G : State (spec (T := T) (K := K) af) → Prop} {P : Outcome T → Prop}
    {σ τ : State (spec (T := T) (K := K) af)} (hτ : (closeC G (fun c => P c.o)).app σ = some τ)
    {k : Inp T K} {c : ROut T K} (hp : Decides af k c.o) : τ.R k c ↔ σ.R k c ∧ P c.o := by
  rw [(closeC_app_iff.1 hτ).2.2, keep_complete hp]

end Closure

/-! ### The commitments and the bases -/

/-- `order(A,B)`: no committed `B` before a committed `A`. -/
def OrderOK (A B : T) (o : Outcome T) : Prop := ¬ o.lt B A
/-- `TxCommit(A)`: `A ∉ X`. -/
def CommitOK (A : T) (o : Outcome T) : Prop := ¬ o.X A
/-- `abort(A)`: `A ∉ dom L`. -/
def AbortOK (A : T) (o : Outcome T) : Prop := ¬ o.dom A
/-- `stamp(A)` given `Z`: no committed `D ∉ Z ∪ {A}` before `A`, and no
committed `z ∈ Z` after `A`. -/
def StampOK (A : T) (Z : T → Prop) (o : Outcome T) : Prop :=
  (∀ D, ¬ Z D → D ≠ A → ¬ o.lt D A) ∧ ∀ z, Z z → ¬ o.lt A z

section Bases
variable {af : Bool}

/-- `order(A,B)`, for distinct `A, B` of the current input. -/
noncomputable def order (A B : T) : Commitment (spec (T := T) (K := K) af) :=
  closeC (fun σ => A ≠ B ∧ σ.cur.mem A ∧ σ.cur.mem B) (fun c => OrderOK A B c.o)
/-- `TxCommit(A)`, for `A` whose commit request is in the current input. -/
noncomputable def commit (A : T) : Commitment (spec (T := T) (K := K) af) :=
  closeC (fun σ => σ.cur.fin A) (fun c => CommitOK A c.o)
/-- `abort(A)`, for `A` in the current input. -/
noncomputable def abort (A : T) : Commitment (spec (T := T) (K := K) af) :=
  closeC (fun σ => σ.cur.mem A) (fun c => AbortOK A c.o)
/-- `stamp(A)` given `Z ⊆ i` with `A ∈ i ∖ Z`. -/
noncomputable def stamp (A : T) (Z : T → Prop) : Commitment (spec (T := T) (K := K) af) :=
  closeC (fun σ => σ.cur.mem A ∧ ¬ Z A ∧ ∀ z, Z z → σ.cur.mem z) (fun c => StampOK A Z c.o)
/-- `read(A,n,v)`, for `A` whose `n`-th operation in the current input is a
read: that read returns `v`. -/
noncomputable def read (A : T) (n : Nat) (v : Option T) : Commitment (spec (T := T) (K := K) af) :=
  closeC (fun σ => ∃ x, σ.cur.op A n = some (.rd x)) (fun c => c.ρ A n = some v)

/-- `B_2PL = {order, TxCommit, abort, read}`. -/
def basis2PL : Basis (spec (T := T) (K := K) af) := fun c =>
  (∃ A B, c = order A B) ∨ (∃ A, c = commit A) ∨ (∃ A, c = abort A) ∨
    (∃ A n v, c = read A n v)

/-- `B_MVTO = {stamp, TxCommit, abort, read}`. -/
def basisMVTO : Basis (spec (T := T) (K := K) af) := fun c =>
  (∃ A Z, c = stamp A Z) ∨ (∃ A, c = commit A) ∨ (∃ A, c = abort A) ∨
    (∃ A n v, c = read A n v)

/-- A closure commitment. -/
def IsClosure (c : Commitment (spec (T := T) (K := K) af)) : Prop := ∃ G Q, c = closeC G Q

theorem basis2PL_closure {c : Commitment (spec (T := T) (K := K) af)} (h : basis2PL c) :
    IsClosure c := by
  rcases h with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact ⟨_, _, rfl⟩

theorem basisMVTO_closure {c : Commitment (spec (T := T) (K := K) af)} (h : basisMVTO c) :
    IsClosure c := by
  rcases h with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact ⟨_, _, rfl⟩

theorem order_guard {A B : T} {σ τ : State (spec (T := T) (K := K) af)}
    (h : (order A B).app σ = some τ) : A ≠ B ∧ σ.cur.mem A ∧ σ.cur.mem B :=
  (closeC_app_iff.1 h).1.1

theorem commit_guard {A : T} {σ τ : State (spec (T := T) (K := K) af)}
    (h : (commit A).app σ = some τ) : σ.cur.fin A :=
  (closeC_app_iff.1 h).1.1

theorem abort_guard {A : T} {σ τ : State (spec (T := T) (K := K) af)}
    (h : (abort A).app σ = some τ) : σ.cur.mem A :=
  (closeC_app_iff.1 h).1.1

theorem stamp_guard {A : T} {Z : T → Prop} {σ τ : State (spec (T := T) (K := K) af)}
    (h : (stamp A Z).app σ = some τ) : σ.cur.mem A ∧ ¬ Z A ∧ ∀ z, Z z → σ.cur.mem z :=
  (closeC_app_iff.1 h).1.1

end Bases

/-! ### States reached under closure bases -/

section Good
variable {af : Bool}

/-- Rows between two rows of the table at one input are in the table. -/
def Convex (σ : State (spec (T := T) (K := K) af)) : Prop :=
  ∀ k x y c, σ.R k x → σ.R k c → x ≼ y → y ≼ c → σ.R k y

/-- Every row has a complete refinement in the table at the same input. -/
def Completable (σ : State (spec (T := T) (K := K) af)) : Prop :=
  ∀ k x, σ.R k x → ∃ c, σ.R k c ∧ Decides af k c.o ∧ x ≼ c

def Good (σ : State (spec (T := T) (K := K) af)) : Prop := Convex σ ∧ Completable σ

theorem good_canon (i : Inp T K) : Good (canon (spec (T := T) (K := K) af) i) := by
  refine ⟨fun k _ y c _ hc _ hyc => ⟨spec_down hc.1 hyc, hc.2⟩, fun k x hx => ?_⟩
  obtain ⟨c, hc, hle⟩ := hx.1
  exact ⟨c, ⟨⟨c, hc, PO.refl _⟩, hx.2⟩, hc.1, hle⟩

theorem good_input {σ τ : State (spec (T := T) (K := K) af)} {j : Inp T K}
    (h : Step σ (.input j) τ) (hg : Good σ) : Good τ := by
  have hR : ∀ k u, τ.R k u ↔ σ.R k u ∧ j ≼ k := by
    cases h with
    | input _ _ _ _ hR => intro k u; rw [hR]; exact Iff.rfl
  refine ⟨fun k x y c hx hc hxy hyc => ?_, fun k x hx => ?_⟩
  · rw [hR] at hx hc ⊢
    exact ⟨hg.1 k x y c hx.1 hc.1 hxy hyc, hx.2⟩
  · rw [hR] at hx
    obtain ⟨c, hc, hp, hle⟩ := hg.2 k x hx.1
    exact ⟨c, (hR k c).2 ⟨hc, hx.2⟩, hp, hle⟩

theorem good_outputTable {σ τ : State (spec (T := T) (K := K) af)} {o : ROut T K}
    (hR0 : τ.R = outputTable σ o) (hg : Good σ) : Good τ := by
  have hR : ∀ k u, τ.R k u ↔ σ.R k u ∧ o ≼ u := by intro k u; rw [hR0]; exact Iff.rfl
  refine ⟨fun k x y c hx hc hxy hyc => ?_, fun k x hx => ?_⟩
  · rw [hR] at hx hc ⊢
    exact ⟨hg.1 k x y c hx.1 hc.1 hxy hyc, PO.trans hx.2 hxy⟩
  · rw [hR] at hx
    obtain ⟨c, hc, hp, hle⟩ := hg.2 k x hx.1
    exact ⟨c, (hR k c).2 ⟨hc, PO.trans hx.2 hle⟩, hp, hle⟩

theorem good_close {G : State (spec (T := T) (K := K) af) → Prop} {Q : ROut T K → Prop}
    {σ τ : State (spec (T := T) (K := K) af)} (h : (closeC G Q).app σ = some τ) (hg : Good σ) : Good τ := by
  obtain ⟨_, _, hR⟩ := closeC_app_iff.1 h
  refine ⟨fun k x y c hx hc hxy hyc => ?_, fun k x hx => ?_⟩
  · obtain ⟨hx', _⟩ := (hR k x).1 hx
    obtain ⟨hc', c', hc'', hp, hcc, hq⟩ := (hR k c).1 hc
    exact (hR k y).2 ⟨hg.1 k x y c hx' hc' hxy hyc, c', hc'', hp, PO.trans hyc hcc, hq⟩
  · obtain ⟨c, hc, hp, hle, _⟩ := after_completion h hx
    exact ⟨c, hc, hp, hle⟩

theorem good_applySeq {γ : List (Commitment (spec (T := T) (K := K) af))}
    {σ ρ : State (spec (T := T) (K := K) af)} (hγ : ∀ c ∈ γ, IsClosure c) (h : ApplySeq γ σ ρ) (hg : Good σ) :
    Good ρ := by
  induction h with
  | nil => exact hg
  | @cons c cs σ τ ρ hc _ ih =>
    obtain ⟨G, Q, rfl⟩ := hγ c (by simp)
    exact ih (fun c' h' => hγ c' (by simp [h'])) (good_close hc hg)

theorem good_sysStep {B : Basis (spec (T := T) (K := K) af)} (hB : ∀ c, B c → IsClosure c)
    {σ τ : State (spec (T := T) (K := K) af)} {e : SEvent (spec (T := T) (K := K) af)} (h : SysStep B σ e τ) (hg : Good σ) :
    Good τ := by
  cases h with
  | input h => exact good_input h hg
  | output hγ happ _ _ _ hR =>
      exact good_outputTable hR (good_applySeq (fun c hc => hB c (hγ c hc)) happ hg)
  | commit hγ _ happ =>
    exact good_applySeq (fun c hc => hB c (hγ c hc)) happ hg

theorem good_sysExec {B : Basis (spec (T := T) (K := K) af)} (hB : ∀ c, B c → IsClosure c)
    {σ τ : State (spec (T := T) (K := K) af)} {es : List (SEvent (spec (T := T) (K := K) af))} (h : SysExec B σ es τ)
    (hg : Good σ) : Good τ := by
  induction h with
  | nil => exact hg
  | cons hs _ ih => exact ih (good_sysStep hB hs hg)

/-- **Every state reached by a run under `B_2PL` or `B_MVTO` is good.** -/
theorem good_run {i : Inp T K} {es : List (SEvent (spec (T := T) (K := K) af))} {τ : State (spec (T := T) (K := K) af)} :
    (SysExec basis2PL (canon _ i) es τ → Good τ) ∧
    (SysExec basisMVTO (canon _ i) es τ → Good τ) :=
  ⟨fun h => good_sysExec (fun _ => basis2PL_closure) h (good_canon i),
   fun h => good_sysExec (fun _ => basisMVTO_closure) h (good_canon i)⟩

end Good

/-! ### Inputs in which every transaction has requested commit -/

/-- At an input in which every transaction has requested commit, a pair `(L,X)`
that partitions the transactions and aborts nothing is complete in both
specifications. -/
theorem decides_of_all_fin {af : Bool} {k : Inp T K} (hf : ∀ t, k.mem t → k.fin t)
    {o : Outcome T} (hp : Partitions k.txs o) (hX : ∀ t, ¬ o.X t) : Decides af k o := by
  cases af with
  | false => exact ⟨hp, fun t hd => hf t ((hp t).1.2 (Or.inr hd))⟩
  | true =>
    refine fun t => ⟨hX t, fun hd => hf t ((hp t).1.2 (Or.inr hd)), fun hfin => ?_⟩
    exact ((hp t).1.1 (Inp.fin_mem hfin)).resolve_left (hX t)

/-! ### Not monotone -/

section Mono
variable (af : Bool)

/-- The rows `([A,B],∅,∅)` and `([B,A],∅,∅)`, at an input whose transactions are
`A` and `B`, both having requested commit. -/
theorem ab_ba_rows {A B : T} (h : A ≠ B) {k : Inp T K} (hk : ∀ t, k.mem t ↔ t = A ∨ t = B)
    (hf : ∀ t, k.mem t → k.fin t) :
    (spec (T := T) (K := K) af).S k (full (ordPair A B h)) ∧ (spec (T := T) (K := K) af).S k (full (ordPair B A (Ne.symm h))) := by
  have p1 : Partitions k.txs (ordPair A B h) := fun t =>
    ⟨by rw [show k.txs.1 t ↔ _ from hk t]; exact ⟨Or.inr, fun h => h.elim False.elim id⟩,
      fun h => h.1⟩
  have p2 : Partitions k.txs (ordPair B A (Ne.symm h)) := fun t =>
    ⟨by
      rw [show k.txs.1 t ↔ _ from hk t]
      show _ ↔ False ∨ (t = B ∨ t = A)
      exact ⟨fun h => Or.inr h.symm, fun h => h.elim False.elim Or.symm⟩, fun h => h.1⟩
  exact ⟨⟨_, full_complete (decides_of_all_fin hf p1 fun _ h => h), PO.refl _⟩,
    ⟨_, full_complete (decides_of_all_fin hf p2 fun _ h => h), PO.refl _⟩⟩

/-- `([A,B],∅,∅)` and `([B,A],∅,∅)` have no common refinement at all. -/
theorem ab_ba_no_common {A B : T} (h : A ≠ B) :
    ¬ ∃ u : ROut T K, full (ordPair A B h) ≼ u ∧ full (ordPair B A (Ne.symm h)) ≼ u :=
  fun ⟨u, h1, h2⟩ => ab_ba_no_common_refinement h ⟨u.o, h1.1, h2.1⟩

/-- **Not monotone** (fibers not directed, no Lifted Monotonicity), for both
the specification and its abort-free variant. -/
theorem spec_not_liftedMono {A B : T} (h : A ≠ B) {k : Inp T K}
    (hk : ∀ t, k.mem t ↔ t = A ∨ t = B) (hf : ∀ t, k.mem t → k.fin t) :
    ¬ (spec (T := T) (K := K) af).DirectedOutputs ∧ ¬ (spec (T := T) (K := K) af).LiftedMono :=
  not_directed_of (ab_ba_rows af h hk hf).1 (ab_ba_rows af h hk hf).2 (ab_ba_no_common h)

/-- An input whose transactions are `A` and `B`, each having requested commit
(with no operations). -/
noncomputable def pairDone (A B : T) (h : A ≠ B) : Inp T K :=
  Inp.ofList [A, B] (by simp [h]) fun _ => ⟨[], true⟩

theorem pairDone_mem {A B : T} {h : A ≠ B} (t : T) :
    (pairDone (K := K) A B h).mem t ↔ t = A ∨ t = B := by
  show t ∈ [A, B] ↔ _; simp

theorem pairDone_fin {A B : T} {h : A ≠ B} (t : T) (ht : (pairDone (K := K) A B h).mem t) :
    (pairDone (K := K) A B h).fin t := by
  unfold pairDone Inp.fin
  rw [Inp.ofList_tx (show t ∈ [A, B] from ht)]

end Mono

/-! ### 2PL deadlock -/

section Deadlock
variable {af : Bool}

/-- **Deadlock.**  After `order(A,B)` and later `order(B,A)`, no row of any
smaller table (at any input) commits both `A` and `B`. -/
theorem deadlock {A B : T} {σ σ1 σ1' σ2 : State (spec (T := T) (K := K) af)}
    (h1 : (order A B).app σ = some σ1) (hs : ∀ k u, σ1'.R k u → σ1.R k u)
    (h2 : (order B A).app σ1' = some σ2) {R : Inp T K → ROut T K → Prop}
    (hR : ∀ k u, R k u → σ2.R k u) {k : Inp T K} {w : ROut T K} (hw : R k w) :
    ¬ (w.o.dom A ∧ w.o.dom B) := by
  rintro ⟨hA, hB⟩
  obtain ⟨c, hc, hp, hle, hq⟩ := after_completion h2 (hR k w hw)
  have hq1 : OrderOK A B c.o :=
    after_complete h1 (R := σ2.R) (fun k u h => hs k u ((order B A).sub _ _ h2 k u h)) hc hp
  have hne := (order_guard h1).1
  rcases c.o.total A B (hle.1.2.1 A hA) (hle.1.2.1 B hB) hne with h | h
  · exact hq h
  · exact hq1 h

/-- … so every complete row of a smaller table aborts one of them. -/
theorem deadlock_complete {A B : T} {σ σ1 σ1' σ2 : State (spec (T := T) (K := K) false)}
    (h1 : (order A B).app σ = some σ1) (hs : ∀ k u, σ1'.R k u → σ1.R k u)
    (h2 : (order B A).app σ1' = some σ2) {R : Inp T K → ROut T K → Prop}
    (hR : ∀ k u, R k u → σ2.R k u) {k : Inp T K} {c : ROut T K} (hc : R k c)
    (hp : Decides false k c.o) (hA : k.mem A) (hB : k.mem B) : c.o.X A ∨ c.o.X B := by
  have hd := deadlock h1 hs h2 hR hc
  rcases hp.decided hA with h | h
  · exact Or.inl h
  rcases hp.decided hB with h' | h'
  · exact Or.inr h'
  exact absurd ⟨h, h'⟩ hd

/-- **Resolving a deadlock by committing.**  If after the deadlock
`TxCommit(A)` is applied, then in every smaller table every complete row aborts
`B`, and `TxCommit(B)` is undefined. -/
theorem deadlock_commit {A B : T} {σ σ1 σ1' σ2 σ3 σ4 : State (spec (T := T) (K := K) false)}
    (h1 : (order A B).app σ = some σ1) (hs : ∀ k u, σ1'.R k u → σ1.R k u)
    (h2 : (order B A).app σ1' = some σ2) (hs' : ∀ k u, σ3.R k u → σ2.R k u)
    (h3 : (commit A).app σ3 = some σ4) (τ : State (spec (T := T) (K := K) false))
    (hτ : ∀ k u, τ.R k u → σ4.R k u) :
    (∀ k c, τ.R k c → Decides false k c.o → c.o.X B) ∧ (commit B).app τ = none := by
  have h43 : ∀ k u, σ4.R k u → σ3.R k u := (commit A).sub _ _ h3
  have hτ2 : ∀ k u, τ.R k u → σ2.R k u := fun k u h => hs' k u (h43 k u (hτ k u h))
  have hτσ : ∀ k u, τ.R k u → σ.R k u := fun k u h =>
    (order A B).sub _ _ h1 k u (hs k u ((order B A).sub _ _ h2 k u (hτ2 k u h)))
  have hAB := order_guard h1
  have key : ∀ k c, τ.R k c → Decides false k c.o → c.o.X B := by
    intro k c hc hp
    have hk : σ.cur ≼ k := σ.above _ _ (hτσ k c hc)
    have hnX : CommitOK A c.o := after_complete h3 hτ hc hp
    have hdA : c.o.dom A := (hp.decided (Inp.le_mem hk hAB.2.1)).resolve_left hnX
    rcases hp.decided (Inp.le_mem hk hAB.2.2) with h | h
    · exact h
    · exact absurd ⟨hdA, h⟩ (deadlock h1 hs h2 hτ2 hc)
  refine ⟨key, closeC_none.2 ?_⟩
  rintro ⟨_, ⟨u, _, c, hc, hp, _, hq⟩, _⟩
  exact hq (key _ c hc hp)

/-- **Abort-free deadlock.**  Under the abort-free specification, after
`order(A,B)` and later `order(B,A)`, no row of any smaller table is at an input
in which both `A` and `B` have requested commit. -/
theorem abortFree_deadlock {A B : T} {σ σ1 σ1' σ2 : State (spec (T := T) (K := K) true)}
    (h1 : (order A B).app σ = some σ1) (hs : ∀ k u, σ1'.R k u → σ1.R k u)
    (h2 : (order B A).app σ1' = some σ2) {R : Inp T K → ROut T K → Prop}
    (hR : ∀ k u, R k u → σ2.R k u) {k : Inp T K} {w : ROut T K} (hw : R k w) :
    ¬ (k.fin A ∧ k.fin B) := by
  rintro ⟨hA, hB⟩
  obtain ⟨c, hc, hp, _, _⟩ := after_completion h2 (hR k w hw)
  exact deadlock h1 hs h2 (R := σ2.R) (fun _ _ h => h) hc ⟨hp.dom_of_fin hA, hp.dom_of_fin hB⟩

/-- … so no later state, reached by any execution under any basis, is at an
input in which both have requested commit: the two commit requests are never
both accepted. -/
theorem abortFree_never_both {A B : T} {σ σ1 σ1' σ2 : State (spec (T := T) (K := K) true)}
    (h1 : (order A B).app σ = some σ1) (hs : ∀ k u, σ1'.R k u → σ1.R k u)
    (h2 : (order B A).app σ1' = some σ2) (Bs : Basis (spec (T := T) (K := K) true))
    {es : List (SEvent (spec (T := T) (K := K) true))} {τ : State (spec (T := T) (K := K) true)} (hx : SysExec Bs σ2 es τ) :
    ¬ (τ.cur.fin A ∧ τ.cur.fin B) :=
  let ⟨_, ho⟩ := τ.hasCur
  abortFree_deadlock h1 hs h2 hx.sub ho

end Deadlock

/-! ### Adding read results and aborts -/

/-- `u` with `A` added to the aborted transactions. -/
def addAbort (u : ROut T K) (A : T) : ROut T K :=
  ⟨{ u.o with X := fun t => u.o.X t ∨ t = A }, u.ρ⟩

/-- `u` with the read fact "the `n`-th operation of `B` returned `v`". -/
noncomputable def addRead (u : ROut T K) (B : T) (n : Nat) (v : Option T) : ROut T K :=
  ⟨u.o, fun a m => if a = B ∧ m = n then some v else u.ρ a m⟩

theorem le_addAbort (u : ROut T K) (A : T) : u ≼ addAbort u A :=
  ⟨⟨fun _ h => Or.inl h, fun _ h => h, fun _ _ _ _ => Iff.rfl⟩, fun _ _ _ h => h⟩

theorem addAbort_mono {u w : ROut T K} (h : u ≼ w) (A : T) : addAbort u A ≼ addAbort w A :=
  ⟨⟨fun t h' => h'.elim (fun h'' => Or.inl (h.1.1 t h'')) Or.inr, h.1.2.1, h.1.2.2⟩, h.2⟩

theorem addAbort_le {u c : ROut T K} (h : u ≼ c) {A : T} (hA : c.o.X A) : addAbort u A ≼ c :=
  ⟨⟨fun t h' => h'.elim (h.1.1 t) (fun e => e ▸ hA), h.1.2.1, h.1.2.2⟩, h.2⟩

theorem addRead_ρ (u : ROut T K) (B : T) (n : Nat) (v : Option T) :
    (addRead u B n v).ρ B n = some v := by
  simp [addRead]

theorem le_addRead {u : ROut T K} {B : T} {n : Nat} {v : Option T}
    (h : ∀ v', u.ρ B n = some v' → v' = v) : u ≼ addRead u B n v := by
  refine ⟨PO.refl _, fun a m w e => ?_⟩
  simp only [addRead]
  split
  · rename_i ham
    obtain ⟨rfl, rfl⟩ := ham
    rw [h w e]
  · exact e

theorem addRead_mono {u w : ROut T K} (h : u ≼ w) (B : T) (n : Nat) (v : Option T) :
    addRead u B n v ≼ addRead w B n v := by
  refine ⟨h.1, fun a m v' e => ?_⟩
  simp only [addRead] at e ⊢
  by_cases ham : a = B ∧ m = n
  · simp only [ham, and_self, ↓reduceIte] at e ⊢; exact e
  · simp only [ham, ↓reduceIte] at e ⊢; exact h.2 a m v' e

theorem addRead_le {u c : ROut T K} (h : u ≼ c) {B : T} {n : Nat} {v : Option T}
    (hc : c.ρ B n = some v) : addRead u B n v ≼ c := by
  refine ⟨h.1, fun a m v' e => ?_⟩
  simp only [addRead] at e
  split at e
  · rename_i ham; obtain ⟨rfl, rfl⟩ := ham; cases e; exact hc
  · exact h.2 a m v' e

section Emit
variable {af : Bool}

/-- **Reporting a read after `read(B,n,v)` applies no further commitment.**  At
a good state, after `read(B,n,v)`, if every row refines `u` and `u` is a row,
then `u` with the read fact added is a row at the same input, and emitting it is
exposable. -/
theorem read_emit {B : T} {n : Nat} {v : Option T} {σ σ' : State (spec (T := T) (K := K) af)}
    (hg : Good σ) (h : (read B n v).app σ = some σ') {u : ROut T K} {k : Inp T K}
    (hu : σ'.R k u) (hall : ∀ k w, σ'.R k w → u ≼ w) :
    σ'.R k (addRead u B n v) ∧ Exposable σ' (addRead u B n v) := by
  have hg' := good_close h hg
  have up : ∀ k w, σ'.R k w → σ'.R k (addRead w B n v) := by
    intro k w hw
    obtain ⟨c, hc, _, hle, hq⟩ := after_completion h hw
    refine hg'.1 k w _ c hw hc (le_addRead fun v' e => ?_) (addRead_le hle hq)
    have := le_ρ hle e; rw [hq] at this; cases this; rfl
  exact ⟨up k u hu, fun k w hw _ => ⟨addRead w B n v, up k w hw,
    addRead_mono (hall k w hw) B n v, (le_addRead fun v' e => by
      obtain ⟨c, _, _, hle, hq⟩ := after_completion h hw
      have := le_ρ hle e; rw [hq] at this; cases this; rfl)⟩⟩

/-- At a good state of the specification whose complete rows all abort `A`, if
every row refines `u` and `u` is a row at the current input, then `u` with `A`
aborted is a row there, and emitting it is exposable. -/
theorem abort_exposable {A : T} {τ : State (spec (T := T) (K := K) false)} (hg : Good τ)
    (hX : ∀ k c, τ.R k c → Decides false k c.o → c.o.X A) {u : ROut T K}
    (hall : ∀ k w, τ.R k w → u ≼ w) (hu : τ.R τ.cur u) :
    τ.R τ.cur (addAbort u A) ∧ Exposable τ (addAbort u A) := by
  have up : ∀ k w, τ.R k w → τ.R k (addAbort w A) := by
    intro k w hw
    obtain ⟨c, hc, hp, hle⟩ := hg.2 k w hw
    exact hg.1 k w _ c hw hc (le_addAbort w A) (addAbort_le hle (hX k c hc hp))
  exact ⟨up _ u hu, fun k w hw _ => ⟨addAbort w A, up k w hw,
    addAbort_mono (hall k w hw) A, le_addAbort w A⟩⟩

/-- **Reporting an abort after `abort(A)` applies no further commitment.** -/
theorem abort_emit {A : T} {σ σ' : State (spec (T := T) (K := K) false)} (hg : Good σ)
    (h : (abort A).app σ = some σ') {u : ROut T K} (hu : σ'.R σ'.cur u)
    (hall : ∀ k w, σ'.R k w → u ≼ w) :
    σ'.R σ'.cur (addAbort u A) ∧ Exposable σ' (addAbort u A) := by
  have hA := abort_guard h
  refine abort_exposable (good_close h hg) (fun k c hc hp => ?_) hall hu
  have hk : σ.cur ≼ k := σ.above _ _ ((abort A).sub _ _ h k c hc)
  exact (hp.decided (Inp.le_mem hk hA)).resolve_right (after_complete h (fun _ _ h => h) hc hp)

end Emit

/-! ### MVTO: what a reported read entails -/

section MVTO
variable {af : Bool}

/-- **The row argument.**  A complete row at `k` satisfying `stamp(A)` (given
`Z_A`) and `stamp(B)` (given `Z_B ∋ A`), where `A` writes `x` at `k`, cannot
commit both `A` and `B` and report that `B`'s `n`-th operation, a read of `x`,
returned `v`, where `v` is the initial version of `x` or the write by a
transaction of `Z_A` other than `A`: `A` lies between that version and `B`.
(If `B` itself writes `x` before the read, the read must return `B`'s own
write, which is not stamped before `A`.) -/
theorem stamps_row {k : Inp T K} {c : ROut T K} (hc : Complete af k c)
    {A B : T} {ZA ZB : T → Prop} {x : K} {n : Nat} {v : Option T}
    (hsA : StampOK A ZA c.o) (hsB : StampOK B ZB c.o) (hAB : ZB A) (hBB : ¬ ZB B)
    (hwA : k.writes A x) (hop : k.op B n = some (.rd x))
    (hv : ∀ W, v = some W → ZA W ∧ W ≠ A) (hρ : c.ρ B n = some v)
    (hdA : c.o.dom A) (hdB : c.o.dom B) : False := by
  have hne : A ≠ B := fun e => hBB (e ▸ hAB)
  obtain ⟨y, hy, _, hrok⟩ := hc.2 B n v hρ
  rw [hop] at hy; cases hy
  have hAB' : c.o.lt A B := (c.o.total A B hdA hdB hne).resolve_right (hsB.2 A hAB)
  by_cases own : OwnW k B n x
  · have e := (hrok hdB).1 own
    subst e
    exact hsA.2 B (hv B rfl).1 hAB'
  have hlw := (hrok hdB).2 own
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
structure TwoStamps (A B : T) (ZA ZB : T → Prop) (σ σ2 : State (spec (T := T) (K := K) af)) where
  σ1 : State (spec (T := T) (K := K) af)
  σ1' : State (spec (T := T) (K := K) af)
  h1 : (stamp A ZA).app σ = some σ1
  hs : ∀ k u, σ1'.R k u → σ1.R k u
  h2 : (stamp B ZB).app σ1' = some σ2
  hAB : ZB A

namespace TwoStamps
variable {A B : T} {ZA ZB : T → Prop} {σ σ2 : State (spec (T := T) (K := K) af)}

theorem sub (H : TwoStamps A B ZA ZB σ σ2) : ∀ k u, σ2.R k u → σ.R k u :=
  fun k u h => (stamp A ZA).sub _ _ H.h1 k u (H.hs k u ((stamp B ZB).sub _ _ H.h2 k u h))

/-- **No row reporting the read commits both.**  After the two stamps, no row
of any smaller table, at an input in which `A` writes `x` and the `n`-th
operation of `B` reads `x`, that reports this read returning `v` (initial, or
written by a transaction stamped before `A`) commits both `A` and `B`. -/
theorem no_both (H : TwoStamps A B ZA ZB σ σ2) {x : K} {n : Nat} {v : Option T}
    (hv : ∀ W, v = some W → ZA W) {R : Inp T K → ROut T K → Prop}
    (hR : ∀ k u, R k u → σ2.R k u) {k : Inp T K} (hwA : k.writes A x)
    (hop : k.op B n = some (.rd x)) {w : ROut T K} (hw : R k w)
    (hρ : w.ρ B n = some v) : ¬ (w.o.dom A ∧ w.o.dom B) := by
  rintro ⟨hdA, hdB⟩
  obtain ⟨c, hc, hp, hle, hqB⟩ := after_completion H.h2 (hR k w hw)
  have hqA : StampOK A ZA c.o :=
    after_complete H.h1 (R := σ2.R) (fun k u h => H.hs k u ((stamp B ZB).sub _ _ H.h2 k u h))
      hc hp
  have hgA := stamp_guard H.h1
  have hgB := stamp_guard H.h2
  exact stamps_row (permitted_of_row (σ2.sub _ _ hc) hp) hqA hqB H.hAB hgB.2.1 hwA hop
    (fun W e => ⟨hv W e, fun h => hgA.2.1 (h ▸ hv W e)⟩) (le_ρ hle hρ)
    (hle.1.2.1 A hdA) (hle.1.2.1 B hdB)

/-- **What reporting the read commits to.**  After the two stamps (and
anything else), `read(B,n,v)` leaves no row, in any smaller table, at an input
in which `A` writes `x` and the `n`-th operation of `B` reads `x`, that commits
both `A` and `B`. -/
theorem read_no_both (H : TwoStamps A B ZA ZB σ σ2) {x : K} {n : Nat} {v : Option T}
    (hv : ∀ W, v = some W → ZA W) {σ3 σ4 : State (spec (T := T) (K := K) af)}
    (hs3 : ∀ k u, σ3.R k u → σ2.R k u) (h : (read B n v).app σ3 = some σ4)
    {R : Inp T K → ROut T K → Prop} (hR : ∀ k u, R k u → σ4.R k u) {k : Inp T K}
    (hwA : k.writes A x) (hop : k.op B n = some (.rd x)) {w : ROut T K} (hw : R k w) :
    ¬ (w.o.dom A ∧ w.o.dom B) := by
  rintro ⟨hdA, hdB⟩
  obtain ⟨c, hc, _, hle, hq⟩ := after_completion h (hR k w hw)
  exact H.no_both hv (R := σ4.R) (fun k u h' => hs3 k u ((read B n v).sub _ _ h k u h'))
    hwA hop hc hq ⟨hle.1.2.1 A hdA, hle.1.2.1 B hdB⟩

end TwoStamps

/-- **Once `B` is committed, `A`'s abort is entailed.**  Let `τ` be a good
state below the two stamps, at an input in which `A` writes `x` and the `n`-th
operation of `B` reads `x`, whose rows all refine an output `u` reporting that
this read returned `v` (initial, or written by a transaction stamped before
`A`), and whose complete rows all commit `B` (for example after
`TxCommit(B)`).  Then no row of `τ` commits `A`, every complete row aborts `A`,
and if `u` is a row at the current input then so is `u` with `A` aborted, and
emitting it is exposable: it applies no commitment. -/
theorem TwoStamps.abort_entailed {A B : T} {ZA ZB : T → Prop}
    {σ σ2 : State (spec (T := T) (K := K) false)} (H : TwoStamps A B ZA ZB σ σ2) {x : K}
    {n : Nat} {v : Option T} (hv : ∀ W, v = some W → ZA W) {τ : State (spec (T := T) (K := K) false)}
    (hτ : ∀ k u, τ.R k u → σ2.R k u) (hg : Good τ) (hwA : τ.cur.writes A x)
    (hop : τ.cur.op B n = some (.rd x)) {u : ROut T K}
    (hall : ∀ k w, τ.R k w → u ≼ w) (hρ : u.ρ B n = some v)
    (hB : ∀ k c, τ.R k c → Decides false k c.o → c.o.dom B) :
    (∀ k w, τ.R k w → ¬ w.o.dom A) ∧
    (∀ k c, τ.R k c → Decides false k c.o → c.o.X A) ∧
    (τ.R τ.cur u → τ.R τ.cur (addAbort u A) ∧ Exposable τ (addAbort u A)) := by
  have noA : ∀ k w, τ.R k w → ¬ w.o.dom A := by
    intro k w hw hdA
    have hk : τ.cur ≼ k := τ.above _ _ hw
    obtain ⟨c', hc', hp', hle'⟩ := hg.2 k w hw
    exact H.no_both hv hτ (Inp.le_writes hk hwA) (Inp.le_op hk hop) hc'
      (le_ρ (PO.trans (hall k w hw) hle') hρ) ⟨hle'.1.2.1 A hdA, hB k c' hc' hp'⟩
  have hAcur : σ.cur.mem A := (stamp_guard H.h1).1
  have Xc : ∀ k c, τ.R k c → Decides false k c.o → c.o.X A := by
    intro k c hc hp
    have hk : σ.cur ≼ k := σ.above _ _ (H.sub k c (hτ k c hc))
    exact (hp.decided (Inp.le_mem hk hAcur)).resolve_right (noA k c hc)
  exact ⟨noA, Xc, fun hu => abort_exposable hg Xc hall hu⟩

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

/-- `{(A,n) ↦ v}`. -/
noncomputable def single (A : T) (n : Nat) (v : Option T) : T → Nat → Option (Option T) :=
  fun a m => if a = A ∧ m = n then some v else none

theorem single_eq {A : T} {n : Nat} {v : Option T} : single A n v A n = some v := by
  simp [single]

section Canon

/-- A row of the specification that commits nothing is refined by the complete
output that aborts everything and reports the same reads. -/
theorem uncommitted_completion {k : Inp T K} {y : ROut T K}
    (hy : (spec (T := T) (K := K) false).S k y) (hd : ∀ t, ¬ y.o.dom t) :
    Complete false k ⟨allAbort k.txs, y.ρ⟩ ∧ y ≼ ⟨allAbort k.txs, y.ρ⟩ := by
  obtain ⟨c, ⟨hp, _⟩, hle⟩ := hy
  refine ⟨⟨allAbort_decides k, fun a n v e => ?_⟩, ?_, fun _ _ _ h => h⟩
  · obtain ⟨x, h1, h2⟩ := row_read hy' e
    exact ⟨x, h1, h2, fun h => h.elim⟩
  · refine ⟨fun t hX => ?_, fun t h => absurd h (hd t), fun a _ h _ => absurd h (hd a)⟩
    exact ((hp.1 t).1).2 (Or.inl (hle.1.1 t hX))
where hy' : (spec (T := T) (K := K) false).S k y := hy

/-- At a canonical state, a closure commitment for a condition that holds
whenever nothing is committed keeps every row that commits nothing. -/
theorem keeps_uncommitted {k0 : Inp T K} {P : Outcome T → Prop}
    (hP : ∀ o : Outcome T, (∀ a b, ¬ o.lt a b) → P o) {k : Inp T K} {y : ROut T K}
    (hy : (canon (spec (T := T) (K := K) false) k0).R k y) (hd : ∀ t, ¬ y.o.dom t) :
    Keep (canon (spec (T := T) (K := K) false) k0) (fun c => P c.o) k y := by
  obtain ⟨hp, hle⟩ := uncommitted_completion hy.1 hd
  exact ⟨hy, _, ⟨⟨_, hp, PO.refl _⟩, hy.2⟩, allAbort_decides k, hle, hP _ fun _ _ h => h⟩

/-- `y = (∅,∅,{(a,n) ↦ v})`, with the `n`-th operation of `a` a read of `x` at
`k` and `v` present at `k`, is a row at `k`. -/
theorem single_row {k : Inp T K} {a : T} {n : Nat} {x : K} {v : Option T}
    (hr : k.op a n = some (.rd x)) (hv : Valid k x v) :
    (spec (T := T) (K := K) false).S k ⟨emptyO, single a n v⟩ := by
  refine ⟨⟨allAbort k.txs, single a n v⟩, ⟨allAbort_decides k, fun b m w e => ?_⟩,
    emptyO_le _, fun _ _ _ h => h⟩
  simp only [single] at e
  split at e
  · rename_i h; obtain ⟨rfl, rfl⟩ := h; cases e; exact ⟨x, hr, hv, fun h => h.elim⟩
  · cases e

/-- A version of `x` is *forced* at `k` when `v` is the only version present at
`k`: then `v` is the initial version and no transaction of `k` writes `x`. -/
theorem forced_version {k : Inp T K} {x : K} {v : Option T}
    (h : ∀ v', Valid k x v' → v' = v) : v = none ∧ ∀ w, ¬ k.writes w x := by
  have e : v = none := (h none trivial).symm
  refine ⟨e, fun w hww => ?_⟩
  have := h (some w) hww
  rw [e] at this; cases this

/-- Adding forced reads to a complete row keeps it permitted. -/
theorem add_forced {k : Inp T K} {r : ROut T K} (hr : Complete false k r)
    (hρ : ∀ a n, r.ρ a n = none) {ρ' : T → Nat → Option (Option T)}
    (h : ∀ a n v, ρ' a n = some v →
      ∃ x, k.op a n = some (.rd x) ∧ Valid k x v ∧ ∀ v', Valid k x v' → v' = v) :
    Complete false k ⟨r.o, ρ'⟩ ∧ r ≼ ⟨r.o, ρ'⟩ := by
  refine ⟨⟨hr.1, fun a n v e => ?_⟩, PO.refl _, fun a n v e => by rw [hρ] at e; cases e⟩
  obtain ⟨x, h1, h2, h4⟩ := h a n v e
  obtain ⟨rfl, hw⟩ := forced_version h4
  refine ⟨x, h1, h2, fun _ => ⟨fun ⟨m, _, hm⟩ => absurd (Inp.op_writes hm) (hw a), fun _ w _ hww => hw w hww⟩⟩

/-- **No read commitment has the effect `τ`** at the canonical state of `k0`,
if `τ` keeps every row at `k0` that commits nothing and removes some complete
row at `k0` that reports no reads. -/
theorem not_read {k0 : Inp T K} {τ : State (spec (T := T) (K := K) false)}
    (hi : ∀ y, (canon (spec (T := T) (K := K) false) k0).R k0 y → (∀ t, ¬ y.o.dom t) → τ.R k0 y)
    {r : ROut T K} (hr : (canon (spec (T := T) (K := K) false) k0).R k0 r) (hrp : Decides false k0 r.o)
    (hrρ : ∀ a n, r.ρ a n = none) (hnr : ¬ τ.R k0 r) (A : T) (n : Nat) (v : Option T) :
    (read A n v).app (canon (spec (T := T) (K := K) false) k0) ≠ some τ := by
  intro h
  obtain ⟨⟨_, ⟨u, _, c, hc, _, _, hq⟩, _⟩, _, hR⟩ := closeC_app_iff.1 h
  obtain ⟨x, hrd, hv⟩ := row_read hc.1 hq
  by_cases halt : ∃ v', Valid k0 x v' ∧ v' ≠ v
  · obtain ⟨v', hv', hne⟩ := halt
    have hy := single_row hrd hv'
    obtain ⟨_, c', _, _, hle, hq'⟩ := (hR k0 _).1 (hi _ ⟨hy, PO.refl _⟩ fun _ h => h)
    have := le_ρ hle (single_eq (A := A) (n := n) (v := v'))
    rw [hq'] at this; cases this; exact hne rfl
  · have hforced : ∀ v', Valid k0 x v' → v' = v := fun v' h' =>
      Classical.byContradiction fun hn => halt ⟨v', h', hn⟩
    have hrc := permitted_of_row hr.1 hrp
    obtain ⟨hc', hle⟩ := add_forced hrc hrρ (ρ' := single A n v) (fun b m w e => by
      simp only [single] at e
      split at e
      · rename_i hb; obtain ⟨rfl, rfl⟩ := hb; cases e; exact ⟨x, hrd, hv, hforced⟩
      · cases e)
    exact hnr ((hR k0 r).2 ⟨hr, _, ⟨⟨_, hc', PO.refl _⟩, PO.refl _⟩,
      hrp, hle, single_eq⟩)

/-- **No canonical choice `c_o` has the effect `τ`** at the canonical state of
`k0`, if `τ` keeps every row at `k0` that commits nothing, the complete row
aborting everything, and some complete row aborting nothing (without reads),
and removes some complete row at `k0` that reports no reads. -/
theorem not_choice {k0 : Inp T K} {τ : State (spec (T := T) (K := K) false)}
    (hi : ∀ y, (canon (spec (T := T) (K := K) false) k0).R k0 y → (∀ t, ¬ y.o.dom t) → τ.R k0 y)
    (ha : τ.R k0 (full (allAbort k0.txs))) {c1 : Outcome T} (hc1p : Decides false k0 c1)
    (hc1X : ∀ t, ¬ c1.X t) (hc1 : τ.R k0 (full c1))
    {r : ROut T K} (hr : (canon (spec (T := T) (K := K) false) k0).R k0 r) (hrp : Decides false k0 r.o)
    (hrρ : ∀ a n, r.ρ a n = none) (hnr : ¬ τ.R k0 r) (o : ROut T K) :
    (choiceC o).app (canon (spec (T := T) (K := K) false) k0) ≠ some τ := by
  intro h
  obtain ⟨ho, _, e⟩ := chooseApp_eq.1 h
  let σ0 := canon (spec (T := T) (K := K) false) k0
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
    have e' := same_o (allAbort_decides k0) hc.1 (PO.trans hau hcu)
    have : c.o.dom t := hcu.1.2.1 t (hou.1.2.1 t hdt)
    rw [← e'] at this; exact this
  have hoX : ∀ t, ¬ o.o.X t := by
    intro t hXt
    obtain ⟨u, hu, hou, hcu1⟩ := compat _ hc1
    obtain ⟨c, hc, hcu⟩ := hu.1
    have e' := same_o (a := full c1) hc1p hc.1 (PO.trans hcu1 hcu)
    have : c.o.X t := hcu.1.1 t (hou.1.1 t hXt)
    rw [← e'] at this; exact hc1X t this
  by_cases halt : ∃ a n x v v', o.ρ a n = some v ∧ k0.op a n = some (.rd x) ∧
      Valid k0 x v' ∧ v' ≠ v
  · obtain ⟨a, n, x, v, v', hov, hop, hv', hne⟩ := halt
    have hy := single_row hop hv'
    obtain ⟨u, _, hou, hyu⟩ := compat _ (hi _ ⟨hy, PO.refl _⟩ fun _ h => h)
    have e1 := le_ρ hou hov
    have e2 := le_ρ hyu (single_eq (A := a) (n := n) (v := v'))
    rw [e1] at e2; cases e2; exact hne rfl
  · have hforced : ∀ a n v, o.ρ a n = some v →
        ∃ x, k0.op a n = some (.rd x) ∧ Valid k0 x v ∧ ∀ v', Valid k0 x v' → v' = v := by
      intro a n v hov
      obtain ⟨x, hop, hv⟩ := row_read ho.1 hov
      exact ⟨x, hop, hv, fun v' h' =>
        Classical.byContradiction fun hn => halt ⟨a, n, x, v, v', hov, hop, h', hn⟩⟩
    have hrc := permitted_of_row hr.1 hrp
    obtain ⟨hc', hle⟩ := add_forced hrc hrρ (ρ' := o.ρ) hforced
    have hr' : σ0.R k0 ⟨r.o, o.ρ⟩ := ⟨⟨_, hc', PO.refl _⟩, PO.refl _⟩
    have hou : o ≼ ⟨r.o, o.ρ⟩ :=
      ⟨⟨fun t h => absurd h (hoX t), fun t h => absurd h (hodom t),
        fun a _ h _ => absurd h (hodom a)⟩, fun _ _ _ h => h⟩
    refine hnr ((hR k0 r).2 ⟨hr, fun hrej => hrej.2.2.2 ?_⟩)
    exact ⟨hr, hrej.2.1, _, hr', hou, hle⟩

end Canon

/-! ### Figure `fig:cc-commitments` -/

section Figure
variable {af : Bool}

/-- **Fig. (h).**  On complete rows without aborts whose input contains `A`
and `B`, `order(A,B)` keeps exactly those with `A` before `B`. -/
theorem fig_h {A B : T} {σ τ : State (spec (T := T) (K := K) false)}
    (h : (order A B).app σ = some τ) {k : Inp T K} {c : ROut T K} (hp : Decides false k c.o)
    (hX : ∀ t, ¬ c.o.X t) (hA : k.mem A) (hB : k.mem B) :
    τ.R k c ↔ σ.R k c ∧ c.o.lt A B := by
  obtain ⟨⟨⟨hne, _, _⟩, _, _⟩, _, hR⟩ := closeC_app_iff.1 h
  rw [hR, keep_complete hp]
  have dA := (hp.decided hA).resolve_left (hX A)
  have dB := (hp.decided hB).resolve_left (hX B)
  refine and_congr_right fun _ => ⟨fun hq => ?_, fun hab hba => c.o.irrefl _ (c.o.trans _ _ _ hab hba)⟩
  exact (c.o.total A B dA dB hne).resolve_right hq

/-- **Fig. (i).**  On complete rows without aborts whose input contains `B`,
`stamp(B)` with no earlier stamps keeps exactly those with `B` first. -/
theorem fig_i {B : T} {σ τ : State (spec (T := T) (K := K) false)}
    (h : (stamp B (fun _ => False)).app σ = some τ) {k : Inp T K} {c : ROut T K}
    (hp : Decides false k c.o) (hX : ∀ t, ¬ c.o.X t) (hB : k.mem B) :
    τ.R k c ↔ σ.R k c ∧ ∀ D, k.mem D → D ≠ B → c.o.lt B D := by
  obtain ⟨_, _, hR⟩ := closeC_app_iff.1 h
  rw [hR, keep_complete hp]
  have dB := (hp.decided hB).resolve_left (hX B)
  refine and_congr_right fun _ => ⟨fun hq D hD hne => ?_, fun hf => ⟨fun D _ hne hDB => ?_,
    fun _ h => h.elim⟩⟩
  · have dD := (hp.decided hD).resolve_left (hX D)
    exact (c.o.total B D dB dD (Ne.symm hne)).resolve_right (hq.1 D id hne)
  · have hD := hp.dom_mem (c.o.supp _ _ hDB).1
    exact c.o.irrefl _ (c.o.trans _ _ _ hDB (hf D hD hne))

end Figure

/-! ### Rows at three transactions that have requested commit -/

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

/-- Three distinct transactions. -/
structure Distinct3 (A B C : T) : Prop where
  ab : A ≠ B
  ac : A ≠ C
  bc : B ≠ C

/-- An input whose transactions are `A`, `B`, `C`, each having requested
commit (with any operations). -/
structure Tri (k : Inp T K) (A B C : T) : Prop where
  d : Distinct3 A B C
  mem : ∀ t, k.mem t ↔ t = A ∨ t = B ∨ t = C
  fin : ∀ t, k.mem t → k.fin t

/-- Such an input exists for any three distinct transactions: each has
requested commit and issued no operations. -/
noncomputable def triDone (A B C : T) (h : Distinct3 A B C) : Inp T K :=
  Inp.ofList [A, B, C] (by simp [h.ab, h.ac, h.bc]) fun _ => ⟨[], true⟩

theorem triDone_tri {A B C : T} (h : Distinct3 A B C) : Tri (triDone (K := K) A B C h) A B C :=
  ⟨h, fun t => by show t ∈ [A, B, C] ↔ _; simp,
    fun t ht => by unfold triDone Inp.fin; rw [Inp.ofList_tx (show t ∈ [A, B, C] from ht)]⟩

section Three
variable {A B C : T} {k : Inp T K}

/-- A complete row without aborts or reads at `k`, for each listing of
`A, B, C`. -/
theorem perm_part {af : Bool} (h : Tri k A B C) {a b c : T}
    (hm : ∀ t, t = a ∨ t = b ∨ t = c ↔ t = A ∨ t = B ∨ t = C) :
    Decides af k (mk [a, b, c] fun _ => False) := by
  refine decides_of_all_fin h.fin (fun t => ⟨?_, fun h' => h'.1⟩) (fun _ h => h)
  show k.mem t ↔ _
  rw [h.mem, mk_dom, ← hm]
  constructor
  · intro h'; exact Or.inr (by simpa using h')
  · rintro (h' | h')
    · exact h'.elim
    · simpa using h'

/-- The canonical state of `k`. -/
noncomputable abbrev σ3 (k : Inp T K) : State (spec (T := T) (K := K) false) :=
  canon (spec (T := T) (K := K) false) k

theorem perm_row (h : Tri k A B C) {a b c : T}
    (hm : ∀ t, t = a ∨ t = b ∨ t = c ↔ t = A ∨ t = B ∨ t = C) :
    (σ3 k).R k (full (mk [a, b, c] fun _ => False)) :=
  ⟨⟨_, full_complete (perm_part h hm), PO.refl _⟩, PO.refl _⟩

theorem allAbort_row : (σ3 k).R k (full (allAbort k.txs)) :=
  ⟨⟨_, full_complete (allAbort_decides k), PO.refl _⟩, PO.refl _⟩

theorem hm_id : ∀ t : T, t = A ∨ t = B ∨ t = C ↔ t = A ∨ t = B ∨ t = C := fun _ => Iff.rfl
theorem hm_bac : ∀ t : T, t = B ∨ t = A ∨ t = C ↔ t = A ∨ t = B ∨ t = C := by
  intro t; constructor <;> rintro (h | h | h) <;> simp [h]
theorem hm_cab : ∀ t : T, t = C ∨ t = A ∨ t = B ↔ t = A ∨ t = B ∨ t = C := by
  intro t; constructor <;> rintro (h | h | h) <;> simp [h]
theorem hm_bca : ∀ t : T, t = B ∨ t = C ∨ t = A ↔ t = A ∨ t = B ∨ t = C := by
  intro t; constructor <;> rintro (h | h | h) <;> simp [h]
theorem hm_cba : ∀ t : T, t = C ∨ t = B ∨ t = A ↔ t = A ∨ t = B ∨ t = C := by
  intro t; constructor <;> rintro (h | h | h) <;> simp [h]
theorem hm_acb : ∀ t : T, t = A ∨ t = C ∨ t = B ↔ t = A ∨ t = B ∨ t = C := by
  intro t; constructor <;> rintro (h | h | h) <;> simp [h]

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
theorem lt_ACB (h : Distinct3 A B C) (Xs : T → Prop) (s t : T) :
    (mk [A, C, B] Xs).lt s t ↔ (s = A ∧ (t = C ∨ t = B)) ∨ (s = C ∧ t = B) :=
  lt3 h.ac h.ab (Ne.symm h.bc) Xs s t

/-- Evaluate order facts of the rows at `{A,B,C}`. -/
macro "d3 " h:term : tactic =>
  `(tactic| simp [full, OrderOK, StampOK, AbortOK, CommitOK, mk_dom, lt_ABC $h, lt_BAC $h,
    lt_CAB $h, lt_BCA $h, lt_CBA $h, ($h).ab, ($h).ac,
    ($h).bc, Ne.symm ($h).ab, Ne.symm ($h).ac, Ne.symm ($h).bc])

/-- `order(A,B)` at the canonical state of `k`: defined, it removes
`[B,A,C]` and keeps `[A,B,C]` and `[C,A,B]` (rows at the current input). -/
theorem order_at (h : Tri k A B C) :
    ∃ τ, (order A B).app (σ3 k) = some τ ∧
      τ.R k (full (mk [A, B, C] fun _ => False)) ∧
      τ.R k (full (mk [C, A, B] fun _ => False)) ∧
      ¬ τ.R k (full (mk [B, A, C] fun _ => False)) := by
  have hd := h.d
  have d : Defined (fun σ : State (spec (T := T) (K := K) false) =>
        A ≠ B ∧ σ.cur.mem A ∧ σ.cur.mem B) (fun c => OrderOK A B c.o) (σ3 k) := by
    refine ⟨⟨hd.ab, (h.mem A).2 (Or.inl rfl), (h.mem B).2 (Or.inr (Or.inl rfl))⟩,
      ⟨_, (keep_complete (perm_part h hm_id)).2 ⟨perm_row h hm_id, ?_⟩⟩,
      _, _, perm_row h hm_bac, fun hk' => ((keep_complete (perm_part h hm_bac)).1 hk').2 ?_⟩
    · d3 hd
    · d3 hd
  obtain ⟨τ, hτ⟩ := exists_of_defined d
  refine ⟨τ, hτ, (res_iff hτ (perm_part h hm_id)).2 ⟨perm_row h hm_id, ?_⟩,
    (res_iff hτ (perm_part h hm_cab)).2 ⟨perm_row h hm_cab, ?_⟩,
    fun hm => ((res_iff hτ (perm_part h hm_bac)).1 hm).2 ?_⟩
  · d3 hd
  · d3 hd
  · d3 hd

/-- `stamp(B)` with no earlier stamps at the canonical state of `k`: defined,
it keeps `[B,A,C]` and `[B,C,A]` and removes `[A,B,C]` and `[C,B,A]`. -/
theorem stamp_at (h : Tri k A B C) :
    ∃ τ, (stamp B (fun _ => False)).app (σ3 k) = some τ ∧
      τ.R k (full (mk [B, A, C] fun _ => False)) ∧
      τ.R k (full (mk [B, C, A] fun _ => False)) ∧
      ¬ τ.R k (full (mk [A, B, C] fun _ => False)) ∧
      ¬ τ.R k (full (mk [C, B, A] fun _ => False)) := by
  have hd := h.d
  have sBAC : StampOK B (fun _ => False) (mk [B, A, C] fun _ => False) :=
    ⟨fun D _ hne => by d3 hd <;> exact hne, fun _ h => h.elim⟩
  have sBCA : StampOK B (fun _ => False) (mk [B, C, A] fun _ => False) :=
    ⟨fun D _ hne => by d3 hd <;> exact hne, fun _ h => h.elim⟩
  have nABC : ¬ StampOK B (fun _ => False) (mk [A, B, C] fun _ => False) :=
    fun hs => hs.1 A id hd.ab (by d3 hd)
  have nCBA : ¬ StampOK B (fun _ => False) (mk [C, B, A] fun _ => False) :=
    fun hs => hs.1 C id (Ne.symm hd.bc) (by d3 hd)
  have d : Defined (fun σ : State (spec (T := T) (K := K) false) =>
        σ.cur.mem B ∧ ¬ False ∧ ∀ z, False → σ.cur.mem z)
      (fun c => StampOK B (fun _ => False) c.o) (σ3 k) :=
    ⟨⟨(h.mem B).2 (Or.inr (Or.inl rfl)), id, fun _ h => h.elim⟩,
      ⟨_, (keep_complete (perm_part h hm_bac)).2 ⟨perm_row h hm_bac, sBAC⟩⟩,
      _, _, perm_row h hm_id, fun hk' => nABC ((keep_complete (perm_part h hm_id)).1 hk').2⟩
  obtain ⟨τ, hτ⟩ := exists_of_defined d
  exact ⟨τ, hτ, (res_iff hτ (perm_part h hm_bac)).2 ⟨perm_row h hm_bac, sBAC⟩,
    (res_iff hτ (perm_part h hm_bca)).2 ⟨perm_row h hm_bca, sBCA⟩,
    fun hm => nABC ((res_iff hτ (perm_part h hm_id)).1 hm).2,
    fun hm => nCBA ((res_iff hτ (perm_part h hm_cba)).1 hm).2⟩

/-- The result of `order(A,B)` or `stamp(B)` keeps every row that commits
nothing. -/
theorem order_keeps_uncommitted {τ : State (spec (T := T) (K := K) false)}
    (hτ : (order A B).app (σ3 k) = some τ) :
    ∀ y, (σ3 k).R k y → (∀ t, ¬ y.o.dom t) → τ.R k y :=
  fun y hy hd => ((closeC_app_iff.1 hτ).2.2 _ y).2
    (keeps_uncommitted (P := OrderOK A B) (fun _ ho => ho B A) hy hd)

theorem stamp_keeps_uncommitted {τ : State (spec (T := T) (K := K) false)}
    (hτ : (stamp B (fun _ => False)).app (σ3 k) = some τ) :
    ∀ y, (σ3 k).R k y → (∀ t, ¬ y.o.dom t) → τ.R k y :=
  fun y hy hd => ((closeC_app_iff.1 hτ).2.2 _ y).2
    (keeps_uncommitted (P := StampOK B (fun _ => False))
      (fun _ ho => ⟨fun D _ _ => ho D B, fun _ h => h.elim⟩) hy hd)

/-- **`order(A,B)` is no MVTO commitment**: at the canonical state of `k`, no
commitment of `B_MVTO` has the effect of `order(A,B)`. -/
theorem order_not_MVTO (h : Tri k A B C) {τ : State (spec (T := T) (K := K) false)}
    (hτ : (order A B).app (σ3 k) = some τ) :
    ∀ c : Commitment (spec (T := T) (K := K) false), basisMVTO c → c.app (σ3 k) ≠ some τ := by
  have hd := h.d
  have rABC : τ.R k (full (mk [A, B, C] fun _ => False)) :=
    (res_iff hτ (perm_part h hm_id)).2 ⟨perm_row h hm_id, by show ¬ _; d3 hd⟩
  have rCAB : τ.R k (full (mk [C, A, B] fun _ => False)) :=
    (res_iff hτ (perm_part h hm_cab)).2 ⟨perm_row h hm_cab, by show ¬ _; d3 hd⟩
  have nBAC : ¬ τ.R k (full (mk [B, A, C] fun _ => False)) :=
    fun hm => ((res_iff hτ (perm_part h hm_bac)).1 hm).2 (by show _; d3 hd)
  intro c hc e
  rcases hc with ⟨A', Z, rfl⟩ | ⟨A', rfl⟩ | ⟨A', rfl⟩ | ⟨T', n, v, rfl⟩
  · have g := stamp_guard e
    have s1 : StampOK A' Z _ := ((res_iff e (perm_part h hm_id)).1 rABC).2
    have s2 : StampOK A' Z _ := ((res_iff e (perm_part h hm_cab)).1 rCAB).2
    rcases (h.mem A').1 g.1 with rfl | rfl | rfl
    · have hZC : ¬ Z C := fun hz => s1.2 C hz (by d3 hd)
      exact s2.1 C hZC (Ne.symm hd.ac) (by d3 hd)
    · have hZC : ¬ Z C := fun hz => s1.2 C hz (by d3 hd)
      exact s2.1 C hZC (Ne.symm hd.bc) (by d3 hd)
    · have hZA : Z A := Classical.byContradiction fun hz => s1.1 A hz hd.ac (by d3 hd)
      exact s2.2 A hZA (by d3 hd)
  · exact nBAC ((res_iff e (perm_part h hm_bac)).2 ⟨perm_row h hm_bac, fun hx => hx⟩)
  · have g : k.mem A' := abort_guard e
    have := ((res_iff e (perm_part h hm_id)).1 rABC).2
    exact this (by rw [h.mem] at g; rcases g with rfl | rfl | rfl <;> d3 hd)
  · exact not_read (order_keeps_uncommitted hτ) (perm_row h hm_bac) (perm_part h hm_bac)
      (fun _ _ => rfl) nBAC T' n v e

/-- **`stamp(B)` (no earlier stamps) is no 2PL commitment**: at the canonical
state of `k`, no commitment of `B_2PL` has its effect. -/
theorem stamp_not_2PL (h : Tri k A B C) {τ : State (spec (T := T) (K := K) false)}
    (hτ : (stamp B (fun _ => False)).app (σ3 k) = some τ) :
    ∀ c : Commitment (spec (T := T) (K := K) false), basis2PL c → c.app (σ3 k) ≠ some τ := by
  have hd := h.d
  have sOK : ∀ {l : List T}, StampOK B (fun _ => False) (mk l fun _ => False) ↔
      ∀ D, D ≠ B → ¬ (mk l fun _ => False).lt D B :=
    ⟨fun hs D hne => hs.1 D id hne, fun hf => ⟨fun D _ hne => hf D hne, fun _ h => h.elim⟩⟩
  have iff_of : ∀ {a b c : T} (hm : ∀ t, t = a ∨ t = b ∨ t = c ↔ t = A ∨ t = B ∨ t = C),
      τ.R k (full (mk [a, b, c] fun _ => False)) ↔
        ∀ D, D ≠ B → ¬ (mk [a, b, c] fun _ => False).lt D B := by
    intro a b c hm
    rw [res_iff hτ (perm_part h hm)]
    exact ⟨fun h' => sOK.1 h'.2, fun h' => ⟨perm_row h hm, sOK.2 h'⟩⟩
  have rBAC := (iff_of hm_bac).2 (fun D hne => by d3 hd <;> exact hne)
  have rBCA := (iff_of hm_bca).2 (fun D hne => by d3 hd <;> exact hne)
  have nABC : ¬ τ.R k (full (mk [A, B, C] fun _ => False)) :=
    fun hm => (iff_of hm_id).1 hm A hd.ab (by d3 hd)
  have nCBA : ¬ τ.R k (full (mk [C, B, A] fun _ => False)) :=
    fun hm => (iff_of hm_cba).1 hm C (Ne.symm hd.bc) (by d3 hd)
  intro c hc e
  rcases hc with ⟨A', B', rfl⟩ | ⟨A', rfl⟩ | ⟨A', rfl⟩ | ⟨T', n, v, rfl⟩
  · obtain ⟨hne, hA', hB'⟩ := order_guard e
    have o1 := fun {a b c : T} (hm : ∀ t, t = a ∨ t = b ∨ t = c ↔ t = A ∨ t = B ∨ t = C) =>
      (res_iff e (perm_part h hm) (c := full (mk [a, b, c] fun _ => False)))
    have hA'' : k.mem A' := hA'
    have hB'' : k.mem B' := hB'
    rw [h.mem] at hA'' hB''
    rcases hA'' with rfl | rfl | rfl <;> rcases hB'' with rfl | rfl | rfl
    · exact hne rfl
    · exact ((o1 hm_bac).1 rBAC).2 (by d3 hd)
    · exact ((o1 hm_bca).1 rBCA).2 (by d3 hd)
    · exact nCBA ((o1 hm_cba).2 ⟨perm_row h hm_cba, by show ¬ _; d3 hd⟩)
    · exact hne rfl
    · exact nABC ((o1 hm_id).2 ⟨perm_row h hm_id, by show ¬ _; d3 hd⟩)
    · exact ((o1 hm_bac).1 rBAC).2 (by d3 hd)
    · exact ((o1 hm_bac).1 rBAC).2 (by d3 hd)
    · exact hne rfl
  · exact nABC ((res_iff e (perm_part h hm_id)).2 ⟨perm_row h hm_id, fun hx => hx⟩)
  · have g : k.mem A' := abort_guard e
    have := ((res_iff e (perm_part h hm_bac)).1 rBAC).2
    exact this (by rw [h.mem] at g; rcases g with rfl | rfl | rfl <;> d3 hd)
  · exact not_read (stamp_keeps_uncommitted hτ) (perm_row h hm_id) (perm_part h hm_id)
      (fun _ _ => rfl) nABC T' n v e

/-- **Neither figure commitment is a canonical choice `c_o`**, for any output
`o`, at the canonical state of `k`. -/
theorem neither_is_choice (h : Tri k A B C) :
    (∀ τ, (order A B).app (σ3 k) = some τ → ∀ o, (choiceC o).app (σ3 k) ≠ some τ) ∧
    (∀ τ, (stamp B (fun _ => False)).app (σ3 k) = some τ →
      ∀ o, (choiceC o).app (σ3 k) ≠ some τ) := by
  have hd := h.d
  have hX : ∀ {l : List T} t, ¬ (mk l fun _ => False).X t := fun _ h => h
  refine ⟨fun τ hτ o => ?_, fun τ hτ o => ?_⟩
  · have hA : τ.R _ (full (allAbort k.txs)) :=
      order_keeps_uncommitted hτ _ allAbort_row (fun _ h => h)
    have rABC : τ.R k (full (mk [A, B, C] fun _ => False)) :=
      (res_iff hτ (perm_part h hm_id)).2 ⟨perm_row h hm_id, by show ¬ _; d3 hd⟩
    have nBAC : ¬ τ.R k (full (mk [B, A, C] fun _ => False)) :=
      fun hm => ((res_iff hτ (perm_part h hm_bac)).1 hm).2 (by show _; d3 hd)
    exact not_choice (order_keeps_uncommitted hτ) hA (perm_part h hm_id) hX rABC
      (perm_row h hm_bac) (perm_part h hm_bac) (fun _ _ => rfl) nBAC o
  · obtain ⟨τ', hτ', rBAC, _, nABC, _⟩ := stamp_at h
    rw [hτ] at hτ'; cases hτ'
    have hA : τ.R _ (full (allAbort k.txs)) :=
      stamp_keeps_uncommitted hτ _ allAbort_row (fun _ h => h)
    exact not_choice (stamp_keeps_uncommitted hτ) hA (perm_part h hm_bac) hX rBAC
      (perm_row h hm_id) (perm_part h hm_id) (fun _ _ => rfl) nABC o

end Three

/-! ### Downward closure -/

/-- Rows below a row are rows (the table is closed downward). -/
def DownClosed {af : Bool} (σ : State (spec (T := T) (K := K) af)) : Prop :=
  ∀ k u w, σ.R k w → (spec (T := T) (K := K) af).S k u → u ≼ w → σ.R k u

theorem downClosed_canon {af : Bool} (i : Inp T K) :
    DownClosed (canon (spec (T := T) (K := K) af) i) :=
  fun _ _ _ hw hu _ => ⟨hu, hw.2⟩

theorem downClosed_close {af : Bool} {G : State (spec (T := T) (K := K) af) → Prop}
    {Q : ROut T K → Prop} {σ τ : State (spec (T := T) (K := K) af)} (h : (closeC G Q).app σ = some τ)
    (hd : DownClosed σ) : DownClosed τ := by
  intro k u w hw hu hle
  obtain ⟨_, _, hR⟩ := closeC_app_iff.1 h
  obtain ⟨hw', c, hc, hp, hwc, hq⟩ := (hR k w).1 hw
  exact (hR k u).2 ⟨hd k u w hw' hu hle, c, hc, hp, PO.trans hle hwc, hq⟩

end Partial
end Txn
end CC
