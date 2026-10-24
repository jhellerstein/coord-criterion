import CoordCriterion.Appendix.TransactionBases.NoReads

/-!
# The transaction specification with read results (Appendix G, `app:cc-bases`)

Namespace `CC.Txn.Reads`.  The specification with outputs `(L,X,ρ)` used by
the current appendix, and the MVTO abort claim: transactions carry the keys
they read (`rd`) and write (`wr`); outputs are `(L,X,ρ)` with `ρ` a partial map
from reads `(a,x)` of committed transactions to versions (`some W` = the write
of `x` by `W`, `none` = the initial version), ordered by `(L,X) ≼ (L',X')` and
extension of `ρ`.

* `ROut`, `Permitted`, `readSpec` — the specification; `readSpec` is total.
* `not_antichain` — fibers are no longer antichains (`ρ ⊂ ρ'`).
* `comparable_same_LX`, `Stable`, `filterCS`, `filterCS_app_iff` — a row
  filter that is constant on comparable permitted rows at one input is a
  commitment; conditions on `(L,X)` alone are (`stable_lift`).
* `orderR`, `commitR`, `abortR`, `stampR`, `basisMVTO_R` — the unchanged
  commitments, lifted.
* `forced_abort_row`, `forced_abort` — the abort claim: after `stamp(A)` and
  then `stamp(B)` (`A ∈ Z_B`), any output event emitting `ρ(B,x) = v`, with
  `A` writing `x` and `v` the initial version or written by some `W ∈ Z_A`,
  emits `A ∈ X`, and every remaining row has `A ∈ X`.
* `Ex.*` — concrete instance (`W=0`, `A=1`, `B=2`, one key): the base
  specification keeps a row with `A` committed after the three stamps
  (`Ex.base_keeps_commit`), the read specification keeps both a row with `A`
  committed and no read fact and a row with the read fact (which aborts `A`)
  (`Ex.reads_rows`), the output event emitting the read fact is legal under
  `B_MVTO` (`Ex.read_event_legal`), and the hypothesis `W ∈ Z_A` cannot be dropped
  (`Ex.writer_after_A`).
-/

namespace CC
namespace Txn
namespace Reads

variable {T K : Type}

/-! ### Outputs `(L, X, ρ)` -/

/-- An output `(L,X,ρ)`; `ρ a x = some v` says the read of `x` by `a` returns
version `v` (`none` = initial version, `some W` = the write by `W`). -/
structure ROut (T K : Type) where
  o : Outcome T
  ρ : T → K → Option (Option T)

/-- `(L,X,ρ) ≼ (L',X',ρ')` iff `(L,X) ≼ (L',X')` and `ρ'` extends `ρ`. -/
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

section Spec
variable (rd wr : T → K → Prop)

/-- `v` is the last write of `x` by a transaction before `a` in `L`, or the
initial version if there is none. -/
def LastWrite (o : Outcome T) (a : T) (x : K) : Option T → Prop
  | none => ∀ w, o.lt w a → ¬ wr w x
  | some w => o.lt w a ∧ wr w x ∧ ∀ w', o.lt w w' → o.lt w' a → ¬ wr w' x

/-- A row `(k,(L,X,ρ))` is permitted when `(L,X)` partitions `k` and each
`ρ(a,x)` is a read of a committed `a` returning the last write of `x` before
`a` in `L` (or the initial version). -/
def Permitted (k : FinSet T) (r : ROut T K) : Prop :=
  Partitions k r.o ∧
    ∀ a x v, r.ρ a x = some v → r.o.dom a ∧ rd a x ∧ LastWrite wr r.o a x v

theorem allAbort_partitions (k : FinSet T) : Partitions k (allAbort k) :=
  fun _ => ⟨⟨Or.inl, fun h => h.elim id False.elim⟩, fun h => h.2⟩

/-- **The read-fact specification** (total: abort everything, read nothing). -/
def readSpec : Spec (FinSet T) (ROut T K) where
  S := Permitted rd wr
  total k := ⟨⟨allAbort k, fun _ _ => none⟩, allAbort_partitions k,
    fun _ _ _ h => by cases h⟩

/-- Comparable permitted rows at one input have the same `(L,X)`. -/
theorem comparable_same_LX {k : FinSet T} {u w : ROut T K}
    (hu : Permitted rd wr k u) (hw : Permitted rd wr k w) (h : u ≼ w) : u.o = w.o :=
  partitions_antichain hu.1 hw.1 h.1

/-- The one-transaction committed outcome `[A]`. -/
def single (A : T) : Outcome T where
  X _ := False
  dom t := t = A
  lt _ _ := False
  irrefl _ h := h
  trans _ _ _ h _ := h
  total _ _ ha hb hne := absurd (ha.trans hb.symm) hne
  supp _ _ h := h.elim

open Classical in
/-- **Fibers are not antichains**: if `A` reads `x`, the rows `([A],∅,∅)` and
`([A],∅,{(A,x) ↦ initial})` at `{A}` are distinct and comparable. -/
theorem not_antichain {A : T} {x : K} (hr : rd A x) : ¬ Antichain (readSpec rd wr) := by
  intro hA
  let k : FinSet T := FinSet.ofList [A] (by simp)
  have hp : Partitions k (single A) := fun t => by
    show (t ∈ [A] ↔ False ∨ t = A) ∧ ¬ (False ∧ t = A)
    simp
  let u : ROut T K := ⟨single A, fun _ _ => none⟩
  let w : ROut T K := ⟨single A, fun a y => if a = A ∧ y = x then some none else none⟩
  have hu : (readSpec rd wr).S k u := ⟨hp, fun _ _ _ h => by cases h⟩
  have hw : (readSpec rd wr).S k w := by
    refine ⟨hp, fun a y v h => ?_⟩
    simp only [w] at h
    split at h
    · rename_i hay
      obtain ⟨rfl, rfl⟩ := hay
      cases h
      exact ⟨rfl, hr, fun _ h => h.elim⟩
    · cases h
  have hle : u ≼ w := ⟨PO.refl _, fun _ _ _ h => by cases h⟩
  have e := congrArg (fun r : ROut T K => r.ρ A x) (hA k u w hu hw hle)
  simp [u, w] at e

end Spec

/-! ### Filters stable on comparable rows are commitments -/

section Generic
variable {I O : Type} [PO I] [PO O] {sp : Spec I O}

/-- `P` does not separate comparable permitted rows at one input. -/
def Stable (sp : Spec I O) (P : I → O → Prop) : Prop :=
  ∀ k u w, sp.S k u → sp.S k w → u ≼ w → (P k u ↔ P k w)

/-- A row filter (defined when the guard holds, some row at the current input
satisfies `P`, and some row fails it) is a commitment whenever `P` is stable. -/
noncomputable def filterCS (G : State sp → Prop) (P : I → O → Prop) (hP : Stable sp P) :
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
    exact hnu ⟨hu, (hP k u w (σ.sub _ _ hu) (σ.sub _ _ hw.1) huw).2 hw.2⟩

theorem filterCS_app_iff {G : State sp → Prop} {P : I → O → Prop} {hP : Stable sp P}
    {σ τ : State sp} :
    (filterCS G P hP).app σ = some τ ↔
      FilterDefined G P σ ∧ τ.cur = σ.cur ∧ ∀ k u, τ.R k u ↔ σ.R k u ∧ P k u := by
  show filterApp G P σ = some τ ↔ _
  rw [filterApp_eq]
  constructor
  · rintro ⟨hd, rfl⟩; exact ⟨hd, rfl, fun _ _ => Iff.rfl⟩
  · rintro ⟨hd, hc, hR⟩
    refine ⟨hd, State.ext' hc.symm ?_⟩
    funext k u; exact (propext (hR k u)).symm

end Generic

/-! ### The commitments, unchanged -/

section Commitments
variable (rd wr : T → K → Prop)

/-- A condition on `(L,X)` read on `(L,X,ρ)`. -/
def lift (P : FinSet T → Outcome T → Prop) : FinSet T → ROut T K → Prop :=
  fun k r => P k r.o

/-- Every condition on `(L,X)` alone is stable. -/
theorem stable_lift (P : FinSet T → Outcome T → Prop) :
    Stable (readSpec rd wr) (lift (K := K) P) := by
  intro k u w hu hw h
  show P k u.o ↔ P k w.o
  rw [comparable_same_LX rd wr hu hw h]

noncomputable def orderR (A B : T) : Commitment (readSpec rd wr) :=
  filterCS (fun σ => A ≠ B ∧ σ.cur.1 A ∧ σ.cur.1 B) (lift (orderP A B)) (stable_lift rd wr _)
noncomputable def commitR (A : T) : Commitment (readSpec rd wr) :=
  filterCS (fun _ => True) (lift (commitP A)) (stable_lift rd wr _)
noncomputable def abortR (A : T) : Commitment (readSpec rd wr) :=
  filterCS (fun _ => True) (lift (abortP A)) (stable_lift rd wr _)
noncomputable def stampR (A : T) (Z : T → Prop) : Commitment (readSpec rd wr) :=
  filterCS (fun σ => ∀ z, Z z → σ.cur.1 z) (lift (stampP A Z)) (stable_lift rd wr _)

/-- `B_MVTO = {stamp, commit, abort}` for the read-fact specification. -/
def basisMVTO_R : Basis (readSpec rd wr) := fun c =>
  (∃ A Z, c = stampR rd wr A Z) ∨ (∃ A, c = commitR rd wr A) ∨ (∃ A, c = abortR rd wr A)

end Commitments

/-! ### The abort claim -/

section Abort
variable {rd wr : T → K → Prop}

theorem not_X_of_dom {k : FinSet T} {o : Outcome T} (h : Partitions k o) {t : T}
    (hd : o.dom t) : ¬ o.X t := fun hx => (h t).2 ⟨hx, hd⟩

/-- **Row form.**  At a permitted row satisfying `stamp(A)` (given `Z_A`) and
`stamp(B)` (given `Z_B ∋ A`), if `A` writes `x` and `ρ(B,x) = v` with `v` the
initial version or written by a transaction of `Z_A`, then `A ∈ X`. -/
theorem forced_abort_row {k : FinSet T} {u : ROut T K} (hu : Permitted rd wr k u)
    {A B : T} {ZA ZB : T → Prop} {x : K} {v : Option T}
    (hsA : stampP A ZA k u.o) (hsB : stampP B ZB k u.o) (hAB : ZB A) (hwA : wr A x)
    (hv : ∀ W, v = some W → ZA W) (hρ : u.ρ B x = some v) : u.o.X A := by
  obtain ⟨hdB, _, hlw⟩ := hu.2 B x v hρ
  have hXB := not_X_of_dom hu.1 hdB
  apply Classical.byContradiction
  intro hXA
  have hAB' : u.o.lt A B := by
    rcases hsB.1 A hAB with h | h | h
    · exact h
    · exact absurd h hXA
    · exact absurd h hXB
  cases v with
  | none => exact hlw A hAB' hwA
  | some W =>
    obtain ⟨hWB, _, hlast⟩ := hlw
    have hWA : u.o.lt W A := by
      rcases hsA.1 W (hv W rfl) with h | h | h
      · exact h
      · exact absurd h (not_X_of_dom hu.1 (u.o.supp _ _ hWB).1)
      · exact absurd h hXA
    exact hlast A hWA hAB' hwA

/-- **The abort claim.**  Apply `stamp(A)` (given `Z_A`), run anything, apply
`stamp(B)` (given `Z_B ∋ A`), run anything, then take a legal output event
`Out_γ(r)` with `ρ_r(B,x) = v`, where `A` writes `x` and `v` is the initial
version or written by a transaction of `Z_A`.  Then the emitted output aborts
`A`, and so does every remaining row (at every input). -/
theorem forced_abort {Bs : Basis (readSpec rd wr)} {A B : T} {ZA ZB : T → Prop}
    {x : K} {v : Option T} {σ σ1 σ1' σ2 τ0 τ : State (readSpec rd wr)}
    {es1 es2 : List (SEvent (readSpec rd wr))} {γ : List (Commitment (readSpec rd wr))}
    {r : ROut T K}
    (h1 : (stampR rd wr A ZA).app σ = some σ1) (hx1 : SysExec Bs σ1 es1 σ1')
    (h2 : (stampR rd wr B ZB).app σ1' = some σ2) (hx2 : SysExec Bs σ2 es2 τ0)
    (hout : SysStep Bs τ0 (.output γ r) τ)
    (hAB : ZB A) (hwA : wr A x) (hv : ∀ W, v = some W → ZA W) (hρ : r.ρ B x = some v) :
    r.o.X A ∧ ∀ k u, τ.R k u → u.o.X A := by
  obtain ⟨_, _, r1⟩ := filterCS_app_iff.1 h1
  obtain ⟨_, _, r2⟩ := filterCS_app_iff.1 h2
  -- every row of `τ0` is permitted and satisfies both stamps
  have rows : ∀ k u, τ0.R k u → u.ρ B x = some v → u.o.X A := by
    intro k u hu hρu
    have h2u := (r2 k u).1 (hx2.sub k u hu)
    have h1u := (r1 k u).1 (hx1.sub k u h2u.1)
    exact forced_abort_row (τ0.sub k u hu) h1u.2 h2u.2 hAB hwA hv hρu
  obtain ⟨_, hr, hsub, _⟩ := containment hout
  refine ⟨rows _ r hr hρ, fun k u hu => ?_⟩
  obtain ⟨hu0, hle⟩ := hsub k u hu
  exact rows k u hu0 (hle.2 B x v hρ)

end Abort

/-! ### Concrete instance: `W = 0`, `A = 1`, `B = 2`, one key -/

namespace Ex

/-- `0` and `1` write the key; `2` reads it. -/
def wr : Nat → Unit → Prop := fun t _ => t = 0 ∨ t = 1
def rd : Nat → Unit → Prop := fun t _ => t = 2

def k0 : FinSet Nat := FinSet.ofList [0, 1, 2] (by decide)
def k1 : FinSet Nat := FinSet.ofList [0, 1, 2, 3] (by decide)

theorem k0_mem (t : Nat) : k0.1 t ↔ t = 0 ∨ t = 1 ∨ t = 2 := by
  show t ∈ [0, 1, 2] ↔ _; simp

theorem k0_le_k1 : k0 ≼ k1 := fun t (h : t ∈ [0, 1, 2]) => by
  show t ∈ [0, 1, 2, 3]; simp at h ⊢; omega

/-- Every list order with its elements partitioning the list's finite set. -/
theorem listOrder_part (l : List Nat) (hl : l.Nodup) :
    Partitions (FinSet.ofList l hl) (listOrder l) :=
  fun _ => ⟨⟨Or.inr, fun h => h.elim False.elim id⟩, fun h => h.1⟩

theorem lo_part (k : FinSet Nat) (l : List Nat) (h : ∀ t, k.1 t ↔ t ∈ l) :
    Partitions k (listOrder l) :=
  fun t => ⟨⟨fun ht => Or.inr ((h t).1 ht), fun h' => h'.elim False.elim (h t).2⟩, fun h => h.1⟩

/-- `(L,X)` with `L = [0,2]` and `X = {1}`. -/
def o02 : Outcome Nat := { listOrder [0, 2] with X := fun t => t = 1 }

theorem o02_part : Partitions k0 o02 := fun t => by
  show (t ∈ [0, 1, 2] ↔ t = 1 ∨ t ∈ [0, 2]) ∧ ¬ (t = 1 ∧ t ∈ [0, 2])
  simp; omega

/-- Stamps `0` (`Z = ∅`), `1` (`Z = {0}`), `2` (`Z = {0,1}`). -/
abbrev Z0 : Nat → Prop := fun _ => False
abbrev Z1 : Nat → Prop := fun z => z = 0
abbrev Z2 : Nat → Prop := fun z => z = 0 ∨ z = 1

instance instDecLO (l : List Nat) (a b : Nat) : Decidable ((listOrder l).lt a b) :=
  inferInstanceAs (Decidable (a ∈ l ∧ b ∈ l ∧ l.idxOf a < l.idxOf b))

instance instDecO02 (a b : Nat) : Decidable (o02.lt a b) :=
  inferInstanceAs (Decidable ((listOrder [0, 2]).lt a b))

theorem lo_lt (l : List Nat) (a b : Nat) :
    (listOrder l).lt a b ↔ a ∈ l ∧ b ∈ l ∧ l.idxOf a < l.idxOf b := Iff.rfl

/-- The stamp order `[0,1,2]` satisfies the three stamps at `k0`. -/
theorem lo012_stamps :
    stampP 0 Z0 k0 (listOrder [0, 1, 2]) ∧ stampP 1 Z1 k0 (listOrder [0, 1, 2]) ∧
      stampP 2 Z2 k0 (listOrder [0, 1, 2]) := by
  refine ⟨⟨fun _ h => h.elim, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro D hD _ hne; rw [k0_mem] at hD
    rcases hD with rfl | rfl | rfl <;> first | exact absurd rfl hne | (left; decide)
  · intro z hz; subst hz; left; decide
  · intro D hD hZ hne; rw [k0_mem] at hD
    rcases hD with rfl | rfl | rfl <;> first | exact absurd rfl hne | exact absurd rfl hZ | (left; decide)
  · intro z hz; rcases hz with rfl | rfl <;> (left; decide)
  · intro D hD hZ hne; rw [k0_mem] at hD
    rcases hD with rfl | rfl | rfl <;> first | exact absurd rfl hne | exact absurd (Or.inl rfl) hZ | exact absurd (Or.inr rfl) hZ

/-- `([0,2], {1})` satisfies the three stamps at `k0`. -/
theorem o02_stamps : stampP 0 Z0 k0 o02 ∧ stampP 1 Z1 k0 o02 ∧ stampP 2 Z2 k0 o02 := by
  refine ⟨⟨fun _ h => h.elim, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro D hD _ hne; rw [k0_mem] at hD
    rcases hD with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact Or.inr (Or.inr rfl)
    · left; decide
  · intro z _; exact Or.inr (Or.inr rfl)
  · intro _ _ _ _; exact Or.inr (Or.inl rfl)
  · intro z hz; rcases hz with rfl | rfl
    · left; decide
    · exact Or.inr (Or.inl rfl)
  · intro D hD hZ hne; rw [k0_mem] at hD
    rcases hD with rfl | rfl | rfl <;> first | exact absurd rfl hne | exact absurd (Or.inl rfl) hZ | exact absurd (Or.inr rfl) hZ

/-- Rows failing each stamp while satisfying the earlier ones. -/
theorem fail0 : ¬ stampP 0 Z0 k0 (listOrder [1, 0, 2]) := by
  intro h
  rcases h.2 1 ((k0_mem 1).2 (by omega)) id (by omega) with h | h | h
  · exact absurd h (by decide)
  · exact h
  · exact h

theorem fail1 : stampP 0 Z0 k0 (listOrder [0, 2, 1]) ∧ ¬ stampP 1 Z1 k0 (listOrder [0, 2, 1]) := by
  refine ⟨⟨fun _ h => h.elim, ?_⟩, fun h => ?_⟩
  · intro D hD _ hne; rw [k0_mem] at hD
    rcases hD with rfl | rfl | rfl <;> first | exact absurd rfl hne | (left; decide)
  · rcases h.2 2 ((k0_mem 2).2 (by omega)) (by omega) (by omega) with h | h | h
    · exact absurd h (by decide)
    · exact h
    · exact h

theorem k1_mem (t : Nat) : k1.1 t ↔ t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by
  show t ∈ [0, 1, 2, 3] ↔ _; simp

theorem fail2 : stampP 0 Z0 k1 (listOrder [0, 1, 3, 2]) ∧ stampP 1 Z1 k1 (listOrder [0, 1, 3, 2]) ∧
    ¬ stampP 2 Z2 k1 (listOrder [0, 1, 3, 2]) := by
  refine ⟨⟨fun _ h => h.elim, ?_⟩, ⟨?_, ?_⟩, fun h => ?_⟩
  · intro D hD _ hne; rw [k1_mem] at hD
    rcases hD with rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | (left; decide)
  · intro z hz; subst hz; left; decide
  · intro D hD hZ hne; rw [k1_mem] at hD
    rcases hD with rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | exact absurd rfl hZ | (left; decide)
  · rcases h.2 3 ((k1_mem 3).2 (by omega)) (by omega) (by omega) with h | h | h
    · exact absurd h (by decide)
    · exact h
    · exact h

theorem p102 : Partitions k0 (listOrder [1, 0, 2]) :=
  lo_part _ _ fun t => by rw [k0_mem]; simp; omega
theorem p021 : Partitions k0 (listOrder [0, 2, 1]) :=
  lo_part _ _ fun t => by rw [k0_mem]; simp; omega
theorem p0132 : Partitions k1 (listOrder [0, 1, 3, 2]) :=
  lo_part _ _ fun t => by rw [k1_mem]; simp; omega

theorem k0_cur_mem (z : Nat) (h : Z2 z) : k0.1 z := (k0_mem z).2 (by omega)

/-! #### Base specification -/

section Base
open Classical

noncomputable abbrev sT (A : Nat) (Z : Nat → Prop) := stampC (txnSpec Nat) txn_antichain A Z

/-- **Claim (4), base specification.**  From the canonical state at `{0,1,2}`,
`stamp(0)`, `stamp(1)`, `stamp(2)` are all defined, and the row
`([0,1,2], ∅)`, in which `A = 1` is committed, remains. -/
theorem base_keeps_commit : ∃ σ1 σ2 σ3 : State (txnSpec Nat),
    (sT 0 Z0).app (canon _ k0) = some σ1 ∧ (sT 1 Z1).app σ1 = some σ2 ∧
    (sT 2 Z2).app σ2 = some σ3 ∧ σ3.R k0 (listOrder [0, 1, 2]) ∧
    ¬ (listOrder [0, 1, 2]).X 1 := by
  obtain ⟨s0, s1, s2⟩ := lo012_stamps
  have p012 : (txnSpec Nat).S k0 (listOrder [0, 1, 2]) := listOrder_part _ _
  let σ1 := filterState (canon (txnSpec Nat) k0) (stampP 0 Z0) ⟨_, ⟨p012, PO.refl _⟩, s0⟩
  let σ2 := filterState σ1 (stampP 1 Z1) ⟨_, ⟨⟨p012, PO.refl _⟩, s0⟩, s1⟩
  let σ3 := filterState σ2 (stampP 2 Z2) ⟨_, ⟨⟨⟨p012, PO.refl _⟩, s0⟩, s1⟩, s2⟩
  refine ⟨σ1, σ2, σ3, ?_, ?_, ?_, ⟨⟨⟨⟨p012, PO.refl _⟩, s0⟩, s1⟩, s2⟩, fun h => h⟩
  · refine (filterC_app_iff txn_antichain).2 ⟨⟨fun _ h => h.elim, ⟨_, ⟨p012, PO.refl _⟩, s0⟩,
      k0, listOrder [1, 0, 2], ⟨p102, PO.refl _⟩, fail0⟩, rfl, fun _ _ => Iff.rfl⟩
  · refine (filterC_app_iff txn_antichain).2 ⟨⟨fun z hz => (k0_mem z).2 (Or.inl hz),
      ⟨_, ⟨⟨p012, PO.refl _⟩, s0⟩, s1⟩,
      k0, listOrder [0, 2, 1], ⟨⟨p021, PO.refl _⟩, fail1.1⟩, fail1.2⟩,
      rfl, fun _ _ => Iff.rfl⟩
  · refine (filterC_app_iff txn_antichain).2 ⟨⟨k0_cur_mem, ⟨_, ⟨⟨⟨p012, PO.refl _⟩, s0⟩, s1⟩, s2⟩,
      k1, listOrder [0, 1, 3, 2], ⟨⟨⟨p0132, k0_le_k1⟩, fail2.1⟩, fail2.2.1⟩,
      fail2.2.2⟩, rfl, fun _ _ => Iff.rfl⟩

end Base

/-! #### Read-fact specification -/

section ReadsEx
open Classical

noncomputable abbrev sR (A : Nat) (Z : Nat → Prop) := stampR rd wr A Z

def none_ρ : Nat → Unit → Option (Option Nat) := fun _ _ => none

/-- `ρ(2, ·) = 0`. -/
def ρ20 : Nat → Unit → Option (Option Nat) := fun a _ => if a = 2 then some (some 0) else none

theorem lift_part (l : List Nat) (hl : l.Nodup) :
    (readSpec rd wr).S (FinSet.ofList l hl) ⟨listOrder l, none_ρ⟩ :=
  ⟨listOrder_part l hl, fun _ _ _ h => by cases h⟩

theorem r02_row : (readSpec rd wr).S k0 ⟨o02, ρ20⟩ := by
  refine ⟨o02_part, fun a x v h => ?_⟩
  simp only [ρ20] at h
  split at h
  · rename_i ha; subst ha; cases h
    refine ⟨(by decide : (2 : Nat) ∈ [0, 2]), rfl, ?_, Or.inl rfl, ?_⟩
    · show (listOrder [0, 2]).lt 0 2; decide
    · intro w' h1 h2
      have h1' : (listOrder [0, 2]).lt 0 w' := h1
      have h2' : (listOrder [0, 2]).lt w' 2 := h2
      rw [lo_lt] at h1' h2'
      obtain ⟨_, hw, hi⟩ := h1'
      simp at hw
      rcases hw with rfl | rfl
      · exact absurd hi (by decide)
      · exact absurd h2'.2.2 (by decide)
  · cases h

theorem p012R : (readSpec rd wr).S k0 ⟨listOrder [0, 1, 2], none_ρ⟩ :=
  lift_part [0, 1, 2] (by decide)

/-- The states after the lifted `stamp(0)`, `stamp(1)`, `stamp(2)` from the
canonical state at `{0,1,2}`. -/
noncomputable def S1 : State (readSpec rd wr) :=
  filterState (canon _ k0) (lift (stampP 0 Z0)) ⟨_, ⟨p012R, PO.refl _⟩, lo012_stamps.1⟩
noncomputable def S2 : State (readSpec rd wr) :=
  filterState S1 (lift (stampP 1 Z1)) ⟨_, ⟨⟨p012R, PO.refl _⟩, lo012_stamps.1⟩, lo012_stamps.2.1⟩
noncomputable def S3 : State (readSpec rd wr) :=
  filterState S2 (lift (stampP 2 Z2))
    ⟨_, ⟨⟨⟨p012R, PO.refl _⟩, lo012_stamps.1⟩, lo012_stamps.2.1⟩, lo012_stamps.2.2⟩

theorem S1_app : (sR 0 Z0).app (canon _ k0) = some S1 :=
  filterCS_app_iff.2 ⟨⟨fun _ h => h.elim, ⟨_, ⟨p012R, PO.refl _⟩, lo012_stamps.1⟩,
    k0, ⟨listOrder [1, 0, 2], none_ρ⟩, ⟨⟨p102, fun _ _ _ h => by cases h⟩, PO.refl _⟩, fail0⟩,
    rfl, fun _ _ => Iff.rfl⟩

theorem S2_app : (sR 1 Z1).app S1 = some S2 :=
  filterCS_app_iff.2 ⟨⟨fun z hz => (k0_mem z).2 (Or.inl hz),
    ⟨_, ⟨⟨p012R, PO.refl _⟩, lo012_stamps.1⟩, lo012_stamps.2.1⟩,
    k0, ⟨listOrder [0, 2, 1], none_ρ⟩,
    ⟨⟨⟨p021, fun _ _ _ h => by cases h⟩, PO.refl _⟩, fail1.1⟩, fail1.2⟩,
    rfl, fun _ _ => Iff.rfl⟩

theorem S3_app : (sR 2 Z2).app S2 = some S3 :=
  filterCS_app_iff.2 ⟨⟨k0_cur_mem,
    ⟨_, ⟨⟨⟨p012R, PO.refl _⟩, lo012_stamps.1⟩, lo012_stamps.2.1⟩, lo012_stamps.2.2⟩,
    k1, ⟨listOrder [0, 1, 3, 2], none_ρ⟩,
    ⟨⟨⟨⟨p0132, fun _ _ _ h => by cases h⟩, k0_le_k1⟩, fail2.1⟩, fail2.2.1⟩, fail2.2.2⟩,
    rfl, fun _ _ => Iff.rfl⟩

/-- The output `([0,2], {1}, ρ(2,x) = 0)`. -/
def r02 : ROut Nat Unit := ⟨o02, ρ20⟩

theorem r02_S3 : S3.R k0 r02 :=
  ⟨⟨⟨⟨r02_row, PO.refl _⟩, o02_stamps.1⟩, o02_stamps.2.1⟩, o02_stamps.2.2⟩

/-- **Claim (4), read-fact specification.**  From the canonical state at
`{0,1,2}`, the lifted `stamp(0)`, `stamp(1)`, `stamp(2)` are all defined; the
row `([0,1,2], ∅, ∅)` (A = 1 committed, no read fact) remains, as does the
row `([0,2], {1}, ρ(2,x) = 0)`; and every remaining row with `ρ(2,x) = 0`
aborts `1`. -/
theorem reads_rows :
    (sR 0 Z0).app (canon _ k0) = some S1 ∧ (sR 1 Z1).app S1 = some S2 ∧
    (sR 2 Z2).app S2 = some S3 ∧
    S3.R k0 ⟨listOrder [0, 1, 2], none_ρ⟩ ∧ ¬ (listOrder [0, 1, 2]).X 1 ∧
    S3.R k0 r02 ∧
    ∀ k u, S3.R k u → u.ρ 2 () = some (some 0) → u.o.X 1 := by
  refine ⟨S1_app, S2_app, S3_app,
    ⟨⟨⟨⟨p012R, PO.refl _⟩, lo012_stamps.1⟩, lo012_stamps.2.1⟩, lo012_stamps.2.2⟩,
    fun h => h, r02_S3, ?_⟩
  intro k u hu hρ
  obtain ⟨⟨⟨⟨hp, _⟩, _⟩, h1⟩, h2⟩ := hu
  exact forced_abort_row (A := 1) (B := 2) (ZA := Z1) (ZB := Z2) hp h1 h2 (Or.inr rfl)
    (Or.inr rfl) (fun W hW => by cases hW; rfl) hρ

/-! #### The output event emitting `ρ(2,x) = 0` is legal -/

theorem allAbort_stamp {k : FinSet Nat} {A : Nat} {Z : Nat → Prop} (hA : k.1 A) :
    stampP A Z k (allAbort k) :=
  ⟨fun _ _ => Or.inr (Or.inr hA), fun _ _ _ _ => Or.inr (Or.inl hA)⟩

/-- `([0], {1,2})`. -/
def o0 : Outcome Nat := { listOrder [0] with X := fun t => t = 1 ∨ t = 2 }

theorem o0_part : Partitions k0 o0 := fun t => by
  show (t ∈ [0, 1, 2] ↔ (t = 1 ∨ t = 2) ∨ t ∈ [0]) ∧ ¬ ((t = 1 ∨ t = 2) ∧ t ∈ [0])
  simp; omega

theorem o0_stamps : stampP 0 Z0 k0 o0 ∧ stampP 1 Z1 k0 o0 ∧ stampP 2 Z2 k0 o0 := by
  refine ⟨⟨fun _ h => h.elim, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro D hD _ hne; rw [k0_mem] at hD
    rcases hD with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · intro _ _; exact Or.inr (Or.inr (Or.inl rfl))
  · intro _ _ _ _; exact Or.inr (Or.inl (Or.inl rfl))
  · intro _ _; exact Or.inr (Or.inr (Or.inr rfl))
  · intro _ _ _ _; exact Or.inr (Or.inl (Or.inr rfl))

/-- After `abort(1)`, `commit(0)`, `commit(2)`. -/
noncomputable def S4 : State (readSpec rd wr) :=
  filterState S3 (lift (abortP 1)) ⟨r02, r02_S3, (rfl : (1 : Nat) = 1)⟩
noncomputable def S5 : State (readSpec rd wr) :=
  filterState S4 (lift (commitP 0)) ⟨r02, ⟨r02_S3, (rfl : (1 : Nat) = 1)⟩,
    (by decide : ¬ ((0 : Nat) = 1))⟩
noncomputable def S6 : State (readSpec rd wr) :=
  filterState S5 (lift (commitP 2)) ⟨r02, ⟨⟨r02_S3, (rfl : (1 : Nat) = 1)⟩,
    (by decide : ¬ ((0 : Nat) = 1))⟩, (by decide : ¬ ((2 : Nat) = 1))⟩

theorem aa_S3 : S3.R k0 ⟨allAbort k0, none_ρ⟩ :=
  ⟨⟨⟨⟨⟨allAbort_partitions k0, fun _ _ _ h => by cases h⟩, PO.refl _⟩,
    allAbort_stamp ((k0_mem 0).2 (Or.inl rfl))⟩, allAbort_stamp ((k0_mem 1).2 (by omega))⟩,
    allAbort_stamp ((k0_mem 2).2 (by omega))⟩

theorem S4_app : (abortR rd wr 1).app S3 = some S4 :=
  filterCS_app_iff.2 ⟨⟨trivial, ⟨r02, r02_S3, (rfl : (1 : Nat) = 1)⟩,
    k0, ⟨listOrder [0, 1, 2], none_ρ⟩,
    ⟨⟨⟨⟨p012R, PO.refl _⟩, lo012_stamps.1⟩, lo012_stamps.2.1⟩, lo012_stamps.2.2⟩, fun h => h⟩,
    rfl, fun _ _ => Iff.rfl⟩

theorem S5_app : (commitR rd wr 0).app S4 = some S5 :=
  filterCS_app_iff.2 ⟨⟨trivial, ⟨r02, ⟨r02_S3, (rfl : (1 : Nat) = 1)⟩,
    (by decide : ¬ ((0 : Nat) = 1))⟩,
    k0, ⟨allAbort k0, none_ρ⟩, ⟨aa_S3, (k0_mem 1).2 (by omega)⟩,
    fun h => h ((k0_mem 0).2 (Or.inl rfl))⟩, rfl, fun _ _ => Iff.rfl⟩

theorem S6_app : (commitR rd wr 2).app S5 = some S6 :=
  filterCS_app_iff.2 ⟨⟨trivial, ⟨r02, ⟨⟨r02_S3, (rfl : (1 : Nat) = 1)⟩,
    (by decide : ¬ ((0 : Nat) = 1))⟩, (by decide : ¬ ((2 : Nat) = 1))⟩,
    k0, ⟨o0, none_ρ⟩,
    ⟨⟨⟨⟨⟨⟨⟨o0_part, fun _ _ _ h => by cases h⟩, PO.refl _⟩, o0_stamps.1⟩, o0_stamps.2.1⟩,
      o0_stamps.2.2⟩, Or.inl rfl⟩, fun h => by cases h with | inl h => cases h | inr h => cases h⟩,
    fun h => h (Or.inr rfl)⟩, rfl, fun _ _ => Iff.rfl⟩

theorem r02_S6 : S6.R k0 r02 :=
  ⟨⟨⟨r02_S3, (rfl : (1 : Nat) = 1)⟩, (by decide : ¬ ((0 : Nat) = 1))⟩,
    (by decide : ¬ ((2 : Nat) = 1))⟩

/-- Add the read fact `ρ(2,x) = 0` to a row. -/
def addRead (x : ROut Nat Unit) : ROut Nat Unit :=
  ⟨x.o, fun a y => if a = 2 then some (some 0) else x.ρ a y⟩

/-- `r02` is exposable at the state after `γ = abort(1) commit(0) commit(2)`:
every remaining row extends, by adding the read fact, to a remaining row
refining `r02`. -/
theorem r02_exposable : Exposable S6 r02 := by
  intro k x hx _
  obtain ⟨⟨⟨⟨⟨⟨⟨hS, hk⟩, st0⟩, st1⟩, st2⟩, hX1⟩, hX0⟩, hX2⟩ := hx
  have hS' := hS
  obtain ⟨hp, hρ⟩ := hS'
  have dom_of : ∀ t, k.1 t → ¬ x.o.X t → x.o.dom t := fun t ht hn =>
    ((hp t).1.1 ht).elim (fun h => absurd h hn) id
  have d0 := dom_of 0 (hk 0 ((k0_mem 0).2 (Or.inl rfl))) hX0
  have d2 := dom_of 2 (hk 2 ((k0_mem 2).2 (by omega))) hX2
  have nd1 : ¬ x.o.dom 1 := fun h => (hp 1).2 ⟨hX1, h⟩
  have l02 : x.o.lt 0 2 := by
    rcases st2.1 0 (Or.inl rfl) with h | h | h
    · exact h
    · exact absurd h hX0
    · exact absurd h hX2
  have wr01 : ∀ w, wr w () → w = 0 ∨ w = 1 := fun _ h => h
  -- the read of `x` by `2`, if any, returns `0`
  have key : ∀ v, x.ρ 2 () = some v → v = some 0 := by
    intro v hv
    obtain ⟨_, _, hl⟩ := hρ 2 () v hv
    cases v with
    | none => exact absurd (Or.inl rfl) (hl 0 l02)
    | some w =>
      obtain ⟨hw2, hw, _⟩ := hl
      rcases wr01 w hw with rfl | rfl
      · rfl
      · exact absurd (x.o.supp _ _ hw2).1 nd1
  have hu : (readSpec rd wr).S k (addRead x) := by
    refine ⟨hp, fun a y v h => ?_⟩
    simp only [addRead] at h
    split at h
    · rename_i ha; subst ha; cases h
      refine ⟨d2, rfl, l02, Or.inl rfl, fun w' h1 h2 hw => ?_⟩
      rcases wr01 w' hw with rfl | rfl
      · exact x.o.irrefl _ h1
      · exact nd1 (x.o.supp _ _ h2).1
    · exact hρ a y v h
  refine ⟨addRead x, ⟨⟨⟨⟨⟨⟨⟨hu, hk⟩, st0⟩, st1⟩, st2⟩, hX1⟩, hX0⟩, hX2⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩,
    ⟨PO.refl _, ?_⟩⟩
  · intro t ht; cases ht; exact hX1
  · intro t ht
    have ht' : t = 0 ∨ t = 2 := by have h' : t ∈ [0, 2] := ht; simpa using h'
    rcases ht' with rfl | rfl
    · exact d0
    · exact d2
  · intro a b ha hb
    have ha' : a = 0 ∨ a = 2 := by have h' : a ∈ [0, 2] := ha; simpa using h'
    have hb' : b = 0 ∨ b = 2 := by have h' : b ∈ [0, 2] := hb; simpa using h'
    show x.o.lt a b ↔ o02.lt a b
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact ⟨fun h => absurd h (x.o.irrefl _), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => by decide, fun _ => l02⟩
    · exact ⟨fun h => absurd (x.o.trans _ _ _ l02 h) (x.o.irrefl _),
        fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (x.o.irrefl _), fun h => absurd h (by decide)⟩
  · intro a y v h
    show (if a = 2 then some (some 0) else x.ρ a y) = some v
    simp only [r02, ρ20] at h
    split at h
    · rename_i ha; simp only [ha, ↓reduceIte]; exact h
    · cases h
  · intro a y v h
    show (if a = 2 then some (some 0) else x.ρ a y) = some v
    split
    · rename_i ha; subst ha; cases y; rw [key v h]
    · exact h

/-- **Non-vacuity of the abort claim.**  After the three stamps, the output
event `Out_γ(([0,2], {1}, ρ(2,x) = 0))` with `γ = abort(1) commit(0) commit(2)`
is legal under `B_MVTO`; by `forced_abort`, its output and every remaining row
abort `1`. -/
theorem read_event_legal : ∃ τ : State (readSpec rd wr),
    SysStep (basisMVTO_R rd wr) S3 (.output [abortR rd wr 1, commitR rd wr 0, commitR rd wr 2] r02) τ ∧
    r02.o.X 1 ∧ ∀ k u, τ.R k u → u.o.X 1 := by
  have hstep : SysStep (basisMVTO_R rd wr) S3
      (.output [abortR rd wr 1, commitR rd wr 0, commitR rd wr 2] r02) (outState S6 r02 r02_S6) := by
    refine SysStep.output ?_ (ApplySeq.cons S4_app (ApplySeq.cons S5_app
      (ApplySeq.cons S6_app (ApplySeq.nil _)))) r02_S6 r02_exposable rfl rfl
    intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact Or.inr (Or.inr ⟨1, rfl⟩)
    · exact Or.inr (Or.inl ⟨0, rfl⟩)
    · exact Or.inr (Or.inl ⟨2, rfl⟩)
  refine ⟨_, hstep, ?_⟩
  exact forced_abort (A := 1) (B := 2) (ZA := Z1) (ZB := Z2) (x := ()) (v := some 0)
    S2_app (SysExec.nil _) S3_app (SysExec.nil _) hstep (Or.inr rfl) (Or.inr rfl)
    (fun W hW => by cases hW; rfl) rfl

/-- **`W ∈ Z_A` cannot be dropped.**  With stamps `A = 0` (`Z = ∅`), `W = 1`
(`Z = {0}`), `B = 2` (`Z = {0,1}`), the row `([0,1,2], ∅, ρ(2,x) = 1)` —
`A` writes `x`, `B` reads the write of `W`, stamped after `A` — satisfies all
three stamps and keeps `A` committed. -/
theorem writer_after_A :
    let r : ROut Nat Unit := ⟨listOrder [0, 1, 2], fun a _ => if a = 2 then some (some 1) else none⟩
    (readSpec rd wr).S k0 r ∧ lift (stampP 0 Z0) k0 r ∧ lift (stampP 1 Z1) k0 r ∧
      lift (stampP 2 Z2) k0 r ∧ wr 0 () ∧ r.ρ 2 () = some (some 1) ∧ ¬ r.o.X 0 := by
  obtain ⟨s0, s1, s2⟩ := lo012_stamps
  refine ⟨⟨listOrder_part _ _, fun a x v h => ?_⟩, s0, s1, s2, Or.inl rfl, rfl, fun h => h⟩
  simp only at h
  split at h
  · rename_i ha; subst ha; cases h
    refine ⟨(by decide : (2 : Nat) ∈ [0, 1, 2]), rfl, ?_, Or.inr rfl, ?_⟩
    · show (listOrder [0, 1, 2]).lt 1 2; decide
    · intro w' h1 h2
      have h1' : (listOrder [0, 1, 2]).lt 1 w' := h1
      have h2' : (listOrder [0, 1, 2]).lt w' 2 := h2
      rw [lo_lt] at h1' h2'
      obtain ⟨_, hw, hi⟩ := h1'
      simp at hw
      rcases hw with rfl | rfl | rfl
      · exact absurd hi (by decide)
      · exact absurd hi (by decide)
      · exact absurd h2'.2.2 (by decide)
  · cases h

end ReadsEx

end Ex

end Reads
end Txn
end CC
