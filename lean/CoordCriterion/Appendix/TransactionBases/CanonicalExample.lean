import CoordCriterion.Appendix.TransactionBases.Partial

/-!
# Canonical runs suffice: a 2PL run and its canonical run (§4.3)

Namespace `CC.Txn.Partial.CanonEx`.  A worked instance of Lemma
`lem:canonical-equivalent` for the specification of Appendix G
(`Partial.lean`), at the input `{A,B,C}`, where `A` reads a key `x` that no
transaction writes.

* `o1` — the output that decides nothing and reports that `A`'s read of `x`
  returned the initial version; `o2` — the complete serial order `[A,C,B]`
  with that read.
* `read_undefined`, `o1_exposable` — reporting the read needs no commitment:
  `read(A,x,initial)` is undefined at the canonical state (it would remove no
  row), and `o1` is exposable there and after `order(A,B)`.
* `example_2PL` — the 2PL run `Out_[order(A,B)](o1)`,
  `Out_[commit(A),commit(B),commit(C),order(A,C),order(C,B)](o2)` and the
  canonical run `Out_{κ}(o1)`, `Out_{κ}(o2)` (with `κ = ε` for `o1`): after the
  first event the canonical table strictly contains 2PL's (it keeps the row
  `[B,A,C]` with the read), both runs end at the same state, and the pair is a
  `Lockstep` pair, as in the lemma.

Modeling choices: `rd`, `wr` are arbitrary apart from `rd A x` and "no
transaction writes `x`"; only the read of `x` is reported.
-/

namespace CC
namespace Txn
namespace Partial
namespace CanonEx

open Classical

set_option linter.unusedSimpArgs false

variable {T K : Type} {rd wr : T → K → Prop} {A B C : T} {x : K}

/-- The output that decides nothing and reports that `A`'s read of `x` returned
the initial version. -/
noncomputable def o1 (A : T) (x : K) : ROut T K := addRead (full emptyO) A x none

/-- The outcome `mk l Xs` with `A`'s read of `x` reported (initial version). -/
noncomputable def row (A : T) (x : K) (l : List T) (Xs : T → Prop) : ROut T K :=
  addRead (full (mk l Xs)) A x none

/-- The complete serial order `[A,C,B]`, with the read. -/
noncomputable def o2 (A B C : T) (x : K) : ROut T K := row A x [A, C, B] fun _ => False

/-- The commitments of 2PL's second output event. -/
noncomputable def γ2 (A B C : T) : List (Commitment (spec (K := K) rd wr false)) :=
  [commit A, commit B, commit C, order A C, order C B]

/-! ### The read of `x` is forced -/

/-- No transaction writes `x`, so every reported read of `x` returns the
initial version. -/
theorem forced_v (hnw : ∀ t, ¬ wr t x) {k : FinSet T} {u : ROut T K}
    (hu : (spec rd wr false).S k u) {a : T} {v : Option T} (e : u.ρ a x = some v) : v = none := by
  obtain ⟨_, _, hv⟩ := row_read hu e
  cases v with
  | none => rfl
  | some W => exact absurd hv.2 (hnw W)

theorem le_add (hnw : ∀ t, ¬ wr t x) {k : FinSet T} {u : ROut T K}
    (hu : (spec rd wr false).S k u) : u ≼ addRead u A x none :=
  le_addRead fun _ e => forced_v hnw hu e

theorem full_le_add (o : Outcome T) (c : ROut T K) (h : o ≼ c.o) :
    addRead (full o) A x none ≼ addRead c A x none :=
  addRead_mono ⟨h, fun _ _ _ e => by cases e⟩ A x none

/-- Adding the read to a complete output keeps it complete. -/
theorem complete_add (hr : rd A x) (hnw : ∀ t, ¬ wr t x) {k : FinSet T} {c : ROut T K}
    (hc : Complete rd wr k c) (hA : k.1 A) : Complete rd wr k (addRead c A x none) := by
  refine ⟨hc.1, fun a y v e => ?_⟩
  simp only [addRead] at e
  split at e
  · rename_i hay
    obtain ⟨rfl, rfl⟩ := hay
    cases e
    exact ⟨hA, hr, trivial, fun _ w _ => hnw w⟩
  · exact hc.2 a y v e

/-- Tables closed under adding the read. -/
def FR (σ : State (spec rd wr false)) (A : T) (x : K) : Prop :=
  ∀ k u, σ.R k u → σ.R k (addRead u A x none)

theorem FR_canon (hr : rd A x) (hnw : ∀ t, ¬ wr t x) {i : FinSet T} (hA : i.1 A) :
    FR (canon (spec rd wr false) i) A x := by
  rintro k u ⟨⟨c, ⟨hc, _⟩, hle⟩, hk⟩
  exact ⟨⟨_, ⟨complete_add hr hnw hc (hk A hA), fun h => by cases h⟩,
    addRead_mono hle A x none⟩, hk⟩

theorem FR_close {G : State (spec rd wr false) → Prop} {P : Outcome T → Prop}
    {σ τ : State (spec rd wr false)} (h : (closeC G (fun c => P c.o)).app σ = some τ)
    (hF : FR σ A x) : FR τ A x := by
  intro k u hu
  obtain ⟨_, _, hR⟩ := closeC_app_iff.1 h
  obtain ⟨hu', c, hc, hp, hle, hq⟩ := (hR k u).1 hu
  exact (hR k _).2 ⟨hF k u hu', _, hF k c hc, hp, addRead_mono hle A x none, hq⟩

theorem FR_out (hnw : ∀ t, ¬ wr t x) {σ : State (spec rd wr false)} {o : ROut T K}
    (ho : σ.R σ.cur o) (hF : FR σ A x) : FR (outState σ o ho) A x := by
  intro k u hu
  exact ⟨hF k u hu.1, PO.trans hu.2 (le_add hnw (σ.sub _ _ hu.1))⟩

/-- **Reporting the read is exposable** at every state whose table is closed
under adding it. -/
theorem o1_exposable (hnw : ∀ t, ¬ wr t x) {σ : State (spec rd wr false)} (hF : FR σ A x) :
    Exposable σ (o1 A x) :=
  fun k w hw _ => ⟨addRead w A x none, hF k w hw, full_le_add _ w (emptyO_le _),
    le_add hnw (σ.sub _ _ hw)⟩

/-- **`read(A,x,initial)` is undefined** at the canonical state of `{A,B,C}`:
it would remove no row. -/
theorem read_undefined (h : Distinct3 A B C) (hr : rd A x) (hnw : ∀ t, ¬ wr t x) :
    (read A x none).app (σABC rd wr h) = none := by
  refine closeC_none.2 fun ⟨_, _, k, u, hu, hn⟩ => hn ⟨hu, ?_⟩
  obtain ⟨⟨c, ⟨hc, _⟩, hle⟩, hk⟩ := hu
  have hA : (tri A B C h).1 A := (tri_mem h A).2 (Or.inl rfl)
  have hc' := complete_add hr hnw hc (hk A hA)
  exact ⟨_, ⟨⟨_, ⟨hc', fun h => by cases h⟩, PO.refl _⟩, hk⟩, hc.1,
    PO.trans hle (le_add hnw ⟨c, ⟨hc, fun h => by cases h⟩, PO.refl _⟩), addRead_ρ _ _ _ _⟩

/-! ### Closure steps -/

/-- Every complete row of the table satisfies `P`. -/
def AllP (σ : State (spec rd wr false)) (P : Outcome T → Prop) : Prop :=
  ∀ k c, σ.R k c → Partitions k c.o → P c.o

theorem allP_close {G : State (spec rd wr false) → Prop} {P : Outcome T → Prop}
    {σ τ : State (spec rd wr false)} (h : (closeC G (fun c => P c.o)).app σ = some τ) :
    AllP τ P :=
  fun _ _ hc hp => after_complete h (fun _ _ h => h) hc hp

theorem allP_sub {σ τ : State (spec rd wr false)} {P : Outcome T → Prop}
    (hs : ∀ k u, τ.R k u → σ.R k u) (h : AllP σ P) : AllP τ P :=
  fun k c hc hp => h k c (hs k c hc) hp

/-- A closure step for a condition on `(L,X)` that keeps a complete row `r`
and removes a complete row `s` at the current input. -/
theorem step_close {G : State (spec rd wr false) → Prop} {P : Outcome T → Prop}
    {σ : State (spec rd wr false)} {k : FinSet T} (hcur : σ.cur = k) (hG : G σ)
    {r s : ROut T K} (hr : σ.R k r) (hrp : Partitions k r.o) (hPr : P r.o)
    (hs : σ.R k s) (hsp : Partitions k s.o) (hPs : ¬ P s.o) :
    ∃ τ, (closeC G (fun c => P c.o)).app σ = some τ ∧ τ.cur = k ∧ ¬ τ.R k s ∧
      ∀ {k' u c}, σ.R k' u → σ.R k' c → Partitions k' c.o → u ≼ c → P c.o →
        τ.R k' u ∧ τ.R k' c := by
  obtain ⟨τ, hτ⟩ := exists_of_defined (G := G) (Q := fun c => P c.o) (σ := σ)
    ⟨hG, ⟨r, by rw [hcur]; exact (keep_complete hrp).2 ⟨hr, hPr⟩⟩, k, s, hs,
      fun hk => hPs ((keep_complete hsp).1 hk).2⟩
  exact ⟨τ, hτ, (closeC_app_iff.1 hτ).2.1.trans hcur, not_mem_close hτ hsp hPs,
    fun hu hc hp hle hq => ⟨mem_close hτ hu hc hp hle hq, mem_close hτ hc hc hp (PO.refl _) hq⟩⟩

/-! ### Rows at `{A,B,C}` -/

section Rows
variable (h : Distinct3 A B C)
include h

theorem lt_ACB (Xs : T → Prop) (s t : T) :
    (mk [A, C, B] Xs).lt s t ↔ (s = A ∧ (t = C ∨ t = B)) ∨ (s = C ∧ t = B) :=
  lt3 h.ac h.ab (Ne.symm h.bc) Xs s t

omit h in
theorem hm_acb : ∀ t : T, t = A ∨ t = C ∨ t = B ↔ t = A ∨ t = B ∨ t = C := by
  intro t; constructor <;> rintro (h | h | h) <;> simp [h]

/-- A complete row of `mk l Xs` at `{A,B,C}` from a partition condition. -/
theorem part_mk {l : List T} {Xs : T → Prop}
    (h1 : ∀ t, (t = A ∨ t = B ∨ t = C) ↔ (Xs t ∨ t ∈ l)) (h2 : ∀ t, ¬ (Xs t ∧ t ∈ l)) :
    Partitions (tri A B C h) (mk l Xs) :=
  fun t => ⟨by rw [tri_mem, h1]; exact Iff.rfl, h2 t⟩

theorem part_AC_B : Partitions (tri A B C h) (mk [A, C] (· = B)) := by
  refine part_mk h (fun t => ?_) (fun t ⟨e, hm⟩ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor <;> rintro (e | e | e) <;> simp [e]
  · rw [e] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with e' | e'
    · exact h.ab e'.symm
    · exact h.bc e'

theorem part_AB_C : Partitions (tri A B C h) (mk [A, B] (· = C)) := by
  refine part_mk h (fun t => ?_) (fun t ⟨e, hm⟩ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor <;> rintro (e | e | e) <;> simp [e]
  · rw [e] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with e' | e'
    · exact h.ac e'.symm
    · exact h.bc e'.symm

variable (rd wr) in
theorem row_canon (hr : rd A x) (hnw : ∀ t, ¬ wr t x) {l : List T} {Xs : T → Prop}
    (hp : Partitions (tri A B C h) (mk l Xs)) :
    (σABC rd wr h).R (tri A B C h) (row A x l Xs) :=
  Ex.canon_row (complete_add hr hnw (full_complete rd wr hp) ((tri_mem h A).2 (Or.inl rfl)))
    (PO.refl _)

omit h in
theorem o1_le_row (l : List T) (Xs : T → Prop) : o1 A x ≼ row A x l Xs :=
  full_le_add _ _ (emptyO_le _)

/-- The complete rows of a table below `{A,B,C}` whose outcome refines
`[A,C,B]` are exactly those that satisfy the six commitments. -/
theorem acb_le {k : FinSet T} {o : Outcome T} (hp : Partitions k o) (hk : tri A B C h ≼ k)
    (cA : CommitOK A o) (cB : CommitOK B o) (cC : CommitOK C o) (oAC : OrderOK A C o)
    (oCB : OrderOK C B o) (oAB : OrderOK A B o) : mk [A, C, B] (fun _ => False) ≼ o := by
  have dom : ∀ t, (t = A ∨ t = B ∨ t = C) → ¬ o.X t → o.dom t := fun t ht hX =>
    ((hp t).1.1 (hk t ((tri_mem h t).2 ht))).resolve_left hX
  have dA := dom A (Or.inl rfl) cA
  have dB := dom B (Or.inr (Or.inl rfl)) cB
  have dC := dom C (Or.inr (Or.inr rfl)) cC
  have hAC : o.lt A C := (o.total A C dA dC h.ac).resolve_right oAC
  have hCB : o.lt C B := (o.total C B dC dB (Ne.symm h.bc)).resolve_right oCB
  have hAB : o.lt A B := (o.total A B dA dB h.ab).resolve_right oAB
  have nCA : ¬ o.lt C A := oAC
  have nBC : ¬ o.lt B C := oCB
  have nBA : ¬ o.lt B A := oAB
  have irr := o.irrefl
  refine ⟨fun _ h => h.elim, fun t ht => ?_, fun a b ha hb => ?_⟩
  · simp only [mk_dom, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with e | e | e <;> rw [e]
    · exact dA
    · exact dC
    · exact dB
  · rw [lt_ACB h]
    simp only [mk_dom, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with e | e | e <;> rcases hb with e' | e' | e' <;> rw [e, e'] <;>
      simp [hAC, hCB, hAB, nCA, nBC, nBA, irr, h.ab, h.ac, h.bc, Ne.symm h.ab, Ne.symm h.ac,
        Ne.symm h.bc]

theorem le_acb {k : FinSet T} {o : Outcome T} (hp : Partitions k o)
    (hle : mk [A, C, B] (fun _ => False) ≼ o) :
    CommitOK A o ∧ CommitOK B o ∧ CommitOK C o ∧ OrderOK A C o ∧ OrderOK C B o ∧
      OrderOK A B o := by
  have mA : (mk [A, C, B] fun _ => False).dom A := by simp [mk_dom]
  have mB : (mk [A, C, B] fun _ => False).dom B := by simp [mk_dom]
  have mC : (mk [A, C, B] fun _ => False).dom C := by simp [mk_dom]
  have nl : ∀ s t, (mk [A, C, B] fun _ => False).dom s → (mk [A, C, B] fun _ => False).dom t →
      ¬ (mk [A, C, B] fun _ => False).lt s t → ¬ o.lt s t :=
    fun s t hs ht hn hl => hn ((hle.2.2 s t hs ht).1 hl)
  refine ⟨fun hX => (hp A).2 ⟨hX, hle.2.1 A mA⟩, fun hX => (hp B).2 ⟨hX, hle.2.1 B mB⟩,
    fun hX => (hp C).2 ⟨hX, hle.2.1 C mC⟩, nl C A mC mA ?_, nl B C mB mC ?_, nl B A mB mA ?_⟩ <;>
    rw [lt_ACB h] <;> simp [h.ab, h.ac, h.bc, Ne.symm h.ab, Ne.symm h.ac, Ne.symm h.bc]

end Rows

/-- Evaluate order facts of the rows used below. -/
macro "d5 " h:term : tactic =>
  `(tactic| simp [row, addRead, full, allAbort, OrderOK, CommitOK, mk_X, mk_dom, lt_ABC $h,
    lt_BAC $h, lt_CAB $h, lt_ACB $h, lt2 ($h).ab, lt2 ($h).ac, ($h).ab, ($h).ac, ($h).bc,
    Ne.symm ($h).ab, Ne.symm ($h).ac, Ne.symm ($h).bc])

/-! ### The two runs -/

/-- **A 2PL run and its canonical run** at `{A,B,C}`, where `A` reads `x` and no
transaction writes `x`.

1. Reporting `A`'s read (`o1`) needs no commitment: `read(A,x,initial)` is
   undefined at the canonical state, `o1` is exposable there, and `κ_{o1} = ε`.
2. 2PL emits `o1` with `order(A,B)`: legal under `B_2PL`; afterwards the row
   `[A,B,C]` (with the read) remains, `[B,A,C]` (with the read) is gone, and
   every row has a remaining complete refinement with `A` before `B` (or one of
   them aborted).  The canonical event `Out_{κ}(o1)` ends at `R[out ⪰ o1]`,
   which contains 2PL's table and keeps `[B,A,C]`.
3. 2PL then emits the complete `o2 = [A,C,B]` with
   `commit(A), commit(B), commit(C), order(A,C), order(C,B)`: legal under
   `B_2PL`.  The canonical run emits `o2` with `κ_{o2} ≠ ε` (`o2` is not
   exposable there), and both runs end at the same state.
4. The two runs are in lockstep (Lemma `lem:canonical-equivalent`). -/
theorem example_2PL (h : Distinct3 A B C) (hr : rd A x) (hnw : ∀ t, ¬ wr t x) :
    ∃ τ1 τ2 τ1' τ2' : State (spec rd wr false),
      -- 1
      (read A x none).app (σABC rd wr h) = none ∧ Exposable (σABC rd wr h) (o1 A x) ∧
      kappa (σABC rd wr h) (o1 A x) = [] ∧
      -- 2
      SysStep basis2PL (σABC rd wr h) (.output [order A B] (o1 A x)) τ1 ∧
      τ1.R (tri A B C h) (row A x [A, B, C] fun _ => False) ∧
      ¬ τ1.R (tri A B C h) (row A x [B, A, C] fun _ => False) ∧
      (∀ k w, τ1.R k w → ∃ c, τ1.R k c ∧ Partitions k c.o ∧ w ≼ c ∧ ¬ c.o.lt B A) ∧
      CanonStep (σABC rd wr h) (.output (kappa (σABC rd wr h) (o1 A x)) (o1 A x)) τ1' ∧
      τ1'.R = outputTable (σABC rd wr h) (o1 A x) ∧
      τ1'.R (tri A B C h) (row A x [B, A, C] fun _ => False) ∧
      (∀ k u, τ1.R k u → τ1'.R k u) ∧
      -- 3
      SysStep basis2PL τ1 (.output (γ2 A B C) (o2 A B C x)) τ2 ∧
      CanonStep τ1' (.output (kappa τ1' (o2 A B C x)) (o2 A B C x)) τ2' ∧
      ¬ Exposable τ1' (o2 A B C x) ∧ kappa τ1' (o2 A B C x) ≠ [] ∧
      τ2 = τ2' ∧
      -- 4
      Lockstep basis2PL (σABC rd wr h)
        [.output [order A B] (o1 A x), .output (γ2 A B C) (o2 A B C x)] τ2
        (σABC rd wr h)
        [.output (kappa (σABC rd wr h) (o1 A x)) (o1 A x),
         .output (kappa τ1' (o2 A B C x)) (o2 A B C x)] τ2' := by
  let k3 := tri A B C h
  let σ0 := σABC rd wr h
  let Z : T → Prop := fun _ => False
  have hA3 : k3.1 A := (tri_mem h A).2 (Or.inl rfl)
  have hB3 : k3.1 B := (tri_mem h B).2 (Or.inr (Or.inl rfl))
  have hC3 : k3.1 C := (tri_mem h C).2 (Or.inr (Or.inr rfl))
  -- rows
  have pACB := perm_part h hm_acb
  have pABC := perm_part h hm_id
  have pBAC := perm_part h hm_bac
  have pCAB := perm_part h hm_cab
  have pAll : Partitions k3 (allAbort k3) := allAbort_part k3
  have pACb := part_AC_B h
  have pABc := part_AB_C h
  have r0 : ∀ {l : List T} {Xs : T → Prop}, Partitions k3 (mk l Xs) →
      σ0.R k3 (row A x l Xs) := fun hp => row_canon rd wr h hr hnw hp
  have rAll0 : σ0.R k3 (addRead (full (allAbort k3)) A x none) :=
    Ex.canon_row (complete_add hr hnw (full_complete rd wr pAll) hA3) (PO.refl _)
  -- `o1` at σ0
  have F0 : FR σ0 A x := FR_canon hr hnw hA3
  have exp0 : Exposable σ0 (o1 A x) := o1_exposable hnw F0
  have kap0 : kappa σ0 (o1 A x) = [] := by
    obtain ⟨hS, hJ⟩ := (exposable_iff_empty _ _).1 exp0
    simp [kappa, hS, hJ]
  have o1_0 : σ0.R k3 (o1 A x) :=
    ⟨spec_down (r0 pACB).1 (o1_le_row _ _), PO.refl _⟩
  -- event 1 (2PL): `order(A,B)`
  obtain ⟨σ1, h1, cur1, nBAC1, m1⟩ := step_close (G := fun σ : State (spec rd wr false) =>
      A ≠ B ∧ σ.cur.1 A ∧ σ.cur.1 B) (P := OrderOK A B) (σ := σ0) (k := k3) rfl
    ⟨h.ab, hA3, hB3⟩ (r0 pACB) pACB (by d5 h) (r0 pBAC) pBAC (by d5 h)
  have o1_1 : σ1.R σ1.cur (o1 A x) := by
    rw [cur1]; exact (m1 o1_0 (r0 pACB) pACB (o1_le_row _ _) (by d5 h)).1
  have F1 : FR σ1 A x := FR_close h1 F0
  let τ1 := outState σ1 (o1 A x) o1_1
  have step1 : SysStep basis2PL σ0 (.output [order A B] (o1 A x)) τ1 :=
    SysStep.output (fun c hc => by
        simp only [List.mem_singleton] at hc; subst hc; exact Or.inl ⟨A, B, rfl⟩)
      (ApplySeq.cons h1 (ApplySeq.nil _)) o1_1 (o1_exposable hnw F1)
      ((closeC_app_iff.1 h1).2.1) rfl
  have curτ1 : τ1.cur = k3 := cur1
  have F1' : FR τ1 A x := FR_out hnw o1_1 F1
  -- rows of τ1
  have t1 : ∀ {l : List T} {Xs : T → Prop}, Partitions k3 (mk l Xs) →
      OrderOK A B (mk l Xs) → τ1.R k3 (row A x l Xs) := fun hp hq =>
    ⟨(m1 (r0 hp) (r0 hp) hp (PO.refl _) hq).1, o1_le_row _ _⟩
  have rAll1 : τ1.R k3 (addRead (full (allAbort k3)) A x none) :=
    ⟨(m1 rAll0 rAll0 pAll (PO.refl _) (fun h => h)).1, full_le_add _ _ (emptyO_le _)⟩
  have rABC1 := t1 pABC (by d5 h)
  have nBAC1' : ¬ τ1.R k3 (row A x [B, A, C] Z) := fun hm => nBAC1 hm.1
  have AB1 : ∀ k w, τ1.R k w → ∃ c, τ1.R k c ∧ Partitions k c.o ∧ w ≼ c ∧ ¬ c.o.lt B A := by
    intro k w hw
    obtain ⟨c, hc, hp, hle, hq⟩ := after_completion h1 hw.1
    exact ⟨c, ⟨hc, PO.trans hw.2 hle⟩, hp, hle, hq⟩
  -- canonical event 1
  let τ1' := outState σ0 (o1 A x) o1_0
  have cstep1 : CanonStep σ0 (.output (kappa σ0 (o1 A x)) (o1 A x)) τ1' :=
    ⟨canonical_support σ0 (o1 A x) o1_0, ⟨(fun _ _ e => by cases e; rfl), fun _ e => by cases e⟩⟩
  have rBAC1' : τ1'.R k3 (row A x [B, A, C] Z) := ⟨r0 pBAC, o1_le_row _ _⟩
  have sub1 : ∀ k u, τ1.R k u → τ1'.R k u := fun k u hu =>
    ⟨(order A B).sub _ _ h1 k u hu.1, hu.2⟩
  -- event 2 (2PL): commit(A), commit(B), commit(C), order(A,C), order(C,B)
  have tACB := t1 pACB (by d5 h)
  obtain ⟨σa, ha, cura, _, ma⟩ := step_close (G := fun σ : State (spec rd wr false) => σ.cur.1 A)
    (P := CommitOK A) (σ := τ1) (k := k3) curτ1 (by show τ1.cur.1 A; rw [curτ1]; exact hA3)
    tACB pACB (by d5 h) rAll1 pAll (fun hn => hn hA3)
  have aACB := (ma tACB tACB pACB (PO.refl _) (by d5 h)).1
  have aACb := (ma (t1 pACb (by d5 h)) (t1 pACb (by d5 h)) pACb (PO.refl _) (by d5 h)).1
  have aABc := (ma (t1 pABc (by d5 h)) (t1 pABc (by d5 h)) pABc (PO.refl _) (by d5 h)).1
  have aCAB := (ma (t1 pCAB (by d5 h)) (t1 pCAB (by d5 h)) pCAB (PO.refl _) (by d5 h)).1
  have aABC := (ma rABC1 rABC1 pABC (PO.refl _) (by d5 h)).1
  obtain ⟨σb, hb, curb, _, mb⟩ := step_close (G := fun σ : State (spec rd wr false) => σ.cur.1 B)
    (P := CommitOK B) (σ := σa) (k := k3) cura (by show σa.cur.1 B; rw [cura]; exact hB3)
    aACB pACB (by d5 h) aACb pACb (by d5 h)
  have bACB := (mb aACB aACB pACB (PO.refl _) (by d5 h)).1
  have bABc := (mb aABc aABc pABc (PO.refl _) (by d5 h)).1
  have bCAB := (mb aCAB aCAB pCAB (PO.refl _) (by d5 h)).1
  have bABC := (mb aABC aABC pABC (PO.refl _) (by d5 h)).1
  obtain ⟨σc, hc, curc, _, mc⟩ := step_close (G := fun σ : State (spec rd wr false) => σ.cur.1 C)
    (P := CommitOK C) (σ := σb) (k := k3) curb (by show σb.cur.1 C; rw [curb]; exact hC3)
    bACB pACB (by d5 h) bABc pABc (by d5 h)
  have cACB := (mc bACB bACB pACB (PO.refl _) (by d5 h)).1
  have cCAB := (mc bCAB bCAB pCAB (PO.refl _) (by d5 h)).1
  have cABC := (mc bABC bABC pABC (PO.refl _) (by d5 h)).1
  obtain ⟨σd, hd, curd, _, md⟩ := step_close (G := fun σ : State (spec rd wr false) =>
      A ≠ C ∧ σ.cur.1 A ∧ σ.cur.1 C) (P := OrderOK A C) (σ := σc) (k := k3) curc
    ⟨h.ac, by rw [curc]; exact hA3, by rw [curc]; exact hC3⟩
    cACB pACB (by d5 h) cCAB pCAB (by d5 h)
  have dACB := (md cACB cACB pACB (PO.refl _) (by d5 h)).1
  have dABC := (md cABC cABC pABC (PO.refl _) (by d5 h)).1
  obtain ⟨σe, he, cure, _, me⟩ := step_close (G := fun σ : State (spec rd wr false) =>
      C ≠ B ∧ σ.cur.1 C ∧ σ.cur.1 B) (P := OrderOK C B) (σ := σd) (k := k3) curd
    ⟨Ne.symm h.bc, by rw [curd]; exact hC3, by rw [curd]; exact hB3⟩
    dACB pACB (by d5 h) dABC pABC (by d5 h)
  have eACB := (me dACB dACB pACB (PO.refl _) (by d5 h)).1
  have app2 : ApplySeq (γ2 (K := K) (rd := rd) (wr := wr) A B C) τ1 σe :=
    ApplySeq.cons ha (ApplySeq.cons hb (ApplySeq.cons hc (ApplySeq.cons hd
      (ApplySeq.cons he (ApplySeq.nil _)))))
  -- subsets
  have se : ∀ k u, σe.R k u → σd.R k u := (order C B).sub _ _ he
  have sd : ∀ k u, σd.R k u → σc.R k u := (order A C).sub _ _ hd
  have sc : ∀ k u, σc.R k u → σb.R k u := (commit C).sub _ _ hc
  have sb : ∀ k u, σb.R k u → σa.R k u := (commit B).sub _ _ hb
  have sa : ∀ k u, σa.R k u → τ1.R k u := (commit A).sub _ _ ha
  have sτ : ∀ k u, τ1.R k u → σ1.R k u := fun _ _ h => h.1
  -- every complete row of σe satisfies the six conditions
  have PAB : AllP σe (OrderOK A B) := allP_sub (fun k u h => sτ k u (sa k u (sb k u
    (sc k u (sd k u (se k u h)))))) (allP_close h1)
  have PcA : AllP σe (CommitOK A) := allP_sub (fun k u h => sb k u
    (sc k u (sd k u (se k u h)))) (allP_close ha)
  have PcB : AllP σe (CommitOK B) := allP_sub (fun k u h => sc k u (sd k u (se k u h)))
    (allP_close hb)
  have PcC : AllP σe (CommitOK C) := allP_sub (fun k u h => sd k u (se k u h)) (allP_close hc)
  have PAC : AllP σe (OrderOK A C) := allP_sub se (allP_close hd)
  have PCB : AllP σe (OrderOK C B) := allP_close he
  have Fe : FR σe A x :=
    FR_close he (FR_close hd (FR_close hc (FR_close hb (FR_close ha F1'))))
  have ge : Good σe := good_close he (good_close hd (good_close hc (good_close hb
    (good_close ha (good_outputTable rfl (good_close h1 (good_canon k3)))))))
  have o2e : σe.R σe.cur (o2 A B C x) := by rw [cure]; exact eACB
  have exp2 : Exposable σe (o2 A B C x) := by
    intro k w hw _
    obtain ⟨c, hc', hp, hle⟩ := ge.2 k w hw
    have hk : k3 ≼ k := cure ▸ σe.above _ _ hc'
    have hmk := acb_le h hp hk (PcA k c hc' hp) (PcB k c hc' hp) (PcC k c hc' hp)
      (PAC k c hc' hp) (PCB k c hc' hp) (PAB k c hc' hp)
    exact ⟨addRead c A x none, Fe k c hc', full_le_add _ c hmk,
      PO.trans hle (le_add hnw (σe.sub _ _ hc'))⟩
  let τ2 := outState σe (o2 A B C x) o2e
  have step2 : SysStep basis2PL τ1 (.output (γ2 A B C) (o2 A B C x)) τ2 := by
    refine SysStep.output (fun c hc => ?_) app2 o2e exp2 (cure.trans curτ1.symm) rfl
    simp only [γ2, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨A, rfl⟩)
    · exact Or.inr (Or.inl ⟨B, rfl⟩)
    · exact Or.inr (Or.inl ⟨C, rfl⟩)
    · exact Or.inl ⟨A, C, rfl⟩
    · exact Or.inl ⟨C, B, rfl⟩
  -- canonical event 2
  have o2_1' : τ1'.R τ1'.cur (o2 A B C x) := ⟨r0 pACB, o1_le_row _ _⟩
  let τ2' := outState τ1' (o2 A B C x) o2_1'
  have cstep2 : CanonStep τ1' (.output (kappa τ1' (o2 A B C x)) (o2 A B C x)) τ2' :=
    ⟨canonical_support τ1' (o2 A B C x) o2_1', ⟨(fun _ _ e => by cases e; rfl), fun _ e => by cases e⟩⟩
  have nexp : ¬ Exposable τ1' (o2 A B C x) := by
    have lAB : ∀ {o : Outcome T}, (mk [A, C, B] Z) ≼ o → o.lt A B := fun hle =>
      (hle.2.2 A B (by simp [mk_dom]) (by simp [mk_dom])).2 (by rw [lt_ACB h]; simp)
    have lBA : ∀ {o : Outcome T}, (mk [B, A, C] Z) ≼ o → o.lt B A := fun hle =>
      (hle.2.2 B A (by simp [mk_dom]) (by simp [mk_dom])).2 (by rw [lt_BAC h]; simp)
    intro hex
    obtain ⟨u, _, hou, hwu⟩ := hex k3 _ rBAC1' (fun hle => by
      have := lAB hle.1
      rw [show (row A x [B, A, C] Z).o = mk [B, A, C] Z from rfl, lt_BAC h] at this
      simp [h.ab, h.ac, h.bc, Ne.symm h.ab, Ne.symm h.ac, Ne.symm h.bc] at this)
    exact u.o.irrefl _ (u.o.trans _ _ _ (lAB hou.1) (lBA hwu.1))
  have kap2 : kappa τ1' (o2 A B C x) ≠ [] := by
    intro hk
    apply nexp
    rw [exposable_iff_empty]
    refine ⟨fun hS => ?_, fun hJ => ?_⟩
    · simp [kappa, hS] at hk
    · simp [kappa, hJ] at hk
  -- both runs end at the same state
  have eq2 : τ2 = τ2' := by
    refine State.ext' (show σe.cur = k3 from cure) ?_
    funext k u
    apply propext
    constructor
    · rintro ⟨hu, hle⟩
      exact ⟨sub1 k u (sa k u (sb k u (sc k u (sd k u (se k u hu))))), hle⟩
    · rintro ⟨⟨hu0, hu1⟩, hle⟩
      obtain ⟨⟨c, ⟨hcc, _⟩, huc⟩, hk⟩ := hu0
      have hp := hcc.1
      have hmk : mk [A, C, B] Z ≼ c.o := PO.trans hle.1 huc.1
      obtain ⟨qA, qB, qC, qAC, qCB, qAB⟩ := le_acb h hp hmk
      have c0 : σ0.R k c := Ex.canon_row hcc hk
      have u0 : σ0.R k u := ⟨spec_down ⟨c, ⟨hcc, fun h => by cases h⟩, PO.refl _⟩ huc, hk⟩
      obtain ⟨u1, c1⟩ := m1 u0 c0 hp huc qAB
      have u1' : τ1.R k u := ⟨u1, hu1⟩
      have c1' : τ1.R k c := ⟨c1, PO.trans hu1 huc⟩
      obtain ⟨ua, ca⟩ := ma u1' c1' hp huc qA
      obtain ⟨ub, cb⟩ := mb ua ca hp huc qB
      obtain ⟨uc, cc⟩ := mc ub cb hp huc qC
      obtain ⟨ud, cd⟩ := md uc cc hp huc qAC
      obtain ⟨ue, _⟩ := me ud cd hp huc qCB
      exact ⟨ue, hle⟩
  refine ⟨τ1, τ2, τ1', τ2', read_undefined h hr hnw, exp0, kap0, step1, rABC1, nBAC1', AB1,
    cstep1, rfl, rBAC1', sub1, step2, cstep2, nexp, kap2, eq2, ?_⟩
  exact Lockstep.cons step1 cstep1 rfl curτ1 sub1
    (Lockstep.cons step2 cstep2 rfl (by rw [eq2]) (fun k u hu => by rw [← eq2]; exact hu)
      (Lockstep.nil τ2 τ2'))

end CanonEx
end Partial
end Txn
end CC
