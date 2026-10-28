import CoordCriterion.Appendix.TransactionBases.Partial

/-!
# MVTO's eager abort: a run in which aborting the writer is a choice (Appendix G)

Namespace `CC.Txn.Partial`.  The specification of `Spec.lean`, the bases of
`Partial.lean`.

* `Ex.mvto_run` — a run under `B_MVTO` driven by operation arrivals.  `A`'s
  first operation (a read of `x`) arrives and `A` is stamped; `B`'s read of
  `x` arrives, `B` is stamped after `A`, and the read is reported as the
  initial version; then `A`'s write of `x` arrives.  Reporting the read is not
  exposable on its own (the row committing `A` then `B`, at an input in which
  `A` writes `x`, cannot be completed with it); after `A`'s write, aborting `A`
  is a choice (two completions remain, `abort(A)` and `abort(B)` keep
  different ones, and emitting `A`'s abort is not exposable), which MVTO's
  write rule makes with `Out_[abort(A)]`; once `B`'s commit request arrives
  and `TxCommit(B)` is applied, `A`'s abort is exposable.
* `writer_after_A` — the hypothesis on the version in
  `TwoStamps.no_both` cannot be dropped.
-/

namespace CC
namespace Txn
namespace Partial

open Classical

set_option linter.unusedSimpArgs false

variable {T K : Type}

/-! ### Inputs built from lists -/

theorem Seq.empty_le (s : Seq K) : Seq.empty ≼ s :=
  ⟨⟨s.ops, by simp [Seq.empty]⟩, fun h => by cases h⟩

theorem Inp.ofList_tx_out {l : List T} {hl : l.Nodup} {s : T → Seq K} {t : T} (h : t ∉ l) :
    (Inp.ofList l hl s).tx t = Seq.empty := by simp [Inp.ofList, h]

theorem Inp.ofList_le {l l' : List T} {hl : l.Nodup} {hl' : l'.Nodup} {s s' : T → Seq K}
    (hsub : ∀ t ∈ l, t ∈ l') (hs : ∀ t ∈ l, s t ≼ s' t) :
    Inp.ofList l hl s ≼ Inp.ofList l' hl' s' := by
  refine ⟨hsub, fun t => ?_⟩
  by_cases ht : t ∈ l
  · rw [Inp.ofList_tx ht, Inp.ofList_tx (hsub t ht)]; exact hs t ht
  · rw [Inp.ofList_tx_out ht]; exact Seq.empty_le _

/-- The state after accepting input `j`. -/
def inSt {af : Bool} (σ : State (spec (T := T) (K := K) af)) (j : Inp T K) (u : ROut T K)
    (h : σ.R j u) : State (spec (T := T) (K := K) af) where
  cur := j
  R := inputTable σ j
  sub k x h := σ.sub k x h.1
  hasCur := ⟨u, h, PO.refl j⟩
  above _ _ h := h.2

theorem inSt_step {af : Bool} {B : Basis (spec (T := T) (K := K) af)}
    (σ : State (spec (T := T) (K := K) af)) (j : Inp T K) (u : ROut T K) (h : σ.R j u) :
    SysStep B σ (.input j) (inSt σ j u h) :=
  SysStep.input (Step.input _ _ j ⟨u, h⟩ rfl rfl)

/-! ### The MVTO run -/

namespace Ex

variable {A B C : T}

/-- One read of `x`, commit not requested / requested. -/
def sR (x : K) : Seq K := ⟨[.rd x], false⟩
def sR' (x : K) : Seq K := ⟨[.rd x], true⟩
/-- A read and then a write of `x`, commit not requested / requested. -/
def sRW (x : K) : Seq K := ⟨[.rd x, .wr x], false⟩
def sRW' (x : K) : Seq K := ⟨[.rd x, .wr x], true⟩
/-- Commit requested, no operations. -/
def sDone : Seq K := ⟨[], true⟩

section Inputs
variable (h : Distinct3 A B C) (x : K)

/-- `A`'s read of `x` has arrived. -/
noncomputable def i1 : Inp T K := Inp.ofList [A] (by simp) fun _ => sR x
/-- … and `B`'s read of `x`. -/
noncomputable def i2 : Inp T K := Inp.ofList [A, B] (by simp [h.ab]) fun _ => sR x
/-- … and `A`'s write of `x`. -/
noncomputable def i3 : Inp T K :=
  Inp.ofList [A, B] (by simp [h.ab]) fun t => if t = A then sRW x else sR x
/-- … and `B`'s commit request. -/
noncomputable def i4 : Inp T K :=
  Inp.ofList [A, B] (by simp [h.ab]) fun t => if t = A then sRW x else sR' x
/-- … and `A`'s commit request. -/
noncomputable def j2 : Inp T K :=
  Inp.ofList [A, B] (by simp [h.ab]) fun t => if t = A then sRW' x else sR' x
/-- `j2` with a third transaction `C` that requested commit. -/
noncomputable def j3 : Inp T K :=
  Inp.ofList [A, B, C] (by simp [h.ab, h.ac, h.bc])
    fun t => if t = A then sRW' x else if t = B then sR' x else sDone

end Inputs

section Facts
variable {h : Distinct3 A B C} {x : K}

theorem le12 : i1 (A := A) x ≼ i2 h x :=
  Inp.ofList_le (by simp) (fun _ _ => PO.refl _)
theorem le23 : i2 h x ≼ i3 h x :=
  Inp.ofList_le (fun _ h => h) (fun t _ => by
    by_cases e : t = A <;> simp only [e, ite_true, ite_false]
    · exact ⟨⟨[.wr x], rfl⟩, fun h => by cases h⟩
    · exact PO.refl _)
theorem le34 : i3 h x ≼ i4 h x :=
  Inp.ofList_le (fun _ h => h) (fun t _ => by
    by_cases e : t = A <;> simp only [e, ite_true, ite_false]
    · exact PO.refl _
    · exact ⟨⟨[], rfl⟩, fun h => by cases h⟩)
theorem le4j : i4 h x ≼ j2 h x :=
  Inp.ofList_le (fun _ h => h) (fun t _ => by
    by_cases e : t = A <;> simp only [e, ite_true, ite_false]
    · exact ⟨⟨[], rfl⟩, fun h => by cases h⟩
    · exact PO.refl _)
theorem le2j3 : i2 h x ≼ j3 h x :=
  Inp.ofList_le (by simp) (fun t ht => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · simp only [ite_true]; exact ⟨⟨[.wr x], rfl⟩, fun h => by cases h⟩
    · simp only [Ne.symm h.ab, ite_true, ite_false]; exact ⟨⟨[], rfl⟩, fun h => by cases h⟩)

theorem le13 : i1 (A := A) x ≼ i3 h x := PO.trans le12 le23
theorem le14 : i1 (A := A) x ≼ i4 h x := PO.trans le13 le34
theorem le1j : i1 (A := A) x ≼ j2 h x := PO.trans le14 le4j
theorem le2j : i2 h x ≼ j2 h x := PO.trans (PO.trans le23 le34) le4j
theorem le3j : i3 h x ≼ j2 h x := PO.trans le34 le4j
theorem le24 : i2 h x ≼ i4 h x := PO.trans le23 le34
theorem le1j3 : i1 (A := A) x ≼ j3 h x := PO.trans le12 le2j3

theorem j2_mem (t : T) : (j2 h x).mem t ↔ t = A ∨ t = B := by
  show t ∈ [A, B] ↔ _; simp
theorem i_mem2 (t : T) : (i2 h x).mem t ↔ t = A ∨ t = B := by
  show t ∈ [A, B] ↔ _; simp
theorem i3_mem (t : T) : (i3 h x).mem t ↔ t = A ∨ t = B := by
  show t ∈ [A, B] ↔ _; simp
theorem i4_mem (t : T) : (i4 h x).mem t ↔ t = A ∨ t = B := by
  show t ∈ [A, B] ↔ _; simp
theorem j3_mem (t : T) : (j3 h x).mem t ↔ t = A ∨ t = B ∨ t = C := by
  show t ∈ [A, B, C] ↔ _; simp

theorem j2_fin (t : T) (ht : (j2 h x).mem t) : (j2 h x).fin t := by
  unfold Inp.fin j2
  rw [Inp.ofList_tx ht]
  by_cases e : t = A <;> simp [e, sRW', sR']
theorem j3_fin (t : T) (ht : (j3 h x).mem t) : (j3 h x).fin t := by
  unfold Inp.fin j3
  rw [Inp.ofList_tx ht]
  by_cases e : t = A
  · subst e; simp [sRW']
  by_cases e' : t = B
  · subst e'; simp [Ne.symm h.ab, sR']
  · simp [e, e', sDone]
theorem i4_finB : (i4 h x).fin B := by
  unfold Inp.fin i4
  rw [Inp.ofList_tx (by simp)]
  simp [Ne.symm h.ab, sR']
theorem i4_fin (t : T) : (i4 h x).fin t → t = B := by
  unfold Inp.fin i4
  intro ht
  by_cases hm : t ∈ [A, B]
  · rw [Inp.ofList_tx hm] at ht
    by_cases e : t = A
    · simp [e, sRW] at ht
    · simp at hm; exact hm.resolve_left e
  · rw [Inp.ofList_tx_out hm] at ht; cases ht

theorem i2_opB : (i2 h x).op B 0 = some (.rd x) := by
  unfold Inp.op i2; rw [Inp.ofList_tx (by simp)]; rfl
theorem i4_writesA : (i4 h x).writes A x := by
  unfold Inp.writes i4; rw [Inp.ofList_tx (by simp)]; simp [sRW]
theorem j2_writesA : (j2 h x).writes A x := Inp.le_writes le4j i4_writesA
theorem i4_opB : (i4 h x).op B 0 = some (.rd x) := Inp.le_op le24 i2_opB
theorem j2_opB : (j2 h x).op B 0 = some (.rd x) := Inp.le_op le2j i2_opB

end Facts

/-! #### Outputs -/

/-- The output that decides nothing and reports that `B`'s read (its operation
`0`) returned the initial version. -/
noncomputable def u (B : T) : ROut T K := addRead (full emptyO) B 0 none
/-- `B` committed, `A` aborted, with the read. -/
noncomputable def r1 (A B : T) : ROut T K := ⟨mk [B] (· = A), (u (K := K) B).ρ⟩
/-- `A` committed, `B` aborted, with the read. -/
noncomputable def r2 (A B : T) : ROut T K := ⟨mk [A] (· = B), (u (K := K) B).ρ⟩
/-- Everything aborted, with the read. -/
noncomputable def aR (B : T) (k : Inp T K) : ROut T K := ⟨allAbort k.txs, (u (K := K) B).ρ⟩
/-- `[A,B]`, no reads. -/
noncomputable def rAB (A B : T) : ROut T K := full (mk [A, B] fun _ => False)

theorem u_ρ (B : T) (a : T) (m : Nat) :
    (u (K := K) B).ρ a m = if a = B ∧ m = 0 then some none else none := rfl

theorem u_le (B : T) (o : Outcome T) : u (K := K) B ≼ (⟨o, (u (K := K) B).ρ⟩ : ROut T K) :=
  ⟨emptyO_le o, fun _ _ _ h => h⟩

theorem full_le (c : ROut T K) : (full emptyO : ROut T K) ≼ c :=
  ⟨emptyO_le _, fun _ _ _ h => by cases h⟩

/-- A complete `(L,X)` with `B`'s read added is complete when `B`, if
committed, is preceded by no writer of `x`. -/
theorem complete_u {k : Inp T K} {o : Outcome T} {x : K} (hp : Decides false k o)
    (hop : k.op B 0 = some (.rd x)) (hlw : o.dom B → ∀ w, o.lt w B → ¬ k.writes w x) :
    Complete false k ⟨o, (u (K := K) B).ρ⟩ := by
  refine ⟨hp, fun a m v e => ?_⟩
  rw [u_ρ] at e
  split at e
  · rename_i ham; obtain ⟨rfl, rfl⟩ := ham; cases e
    exact ⟨x, hop, trivial, fun hd => ⟨fun ⟨_, hm, _⟩ => absurd hm (Nat.not_lt_zero _),
      fun _ => hlw hd⟩⟩
  · cases e

theorem canon_row {i k : Inp T K} {c : ROut T K} (hc : Complete false k c) (hk : i ≼ k) :
    (canon (spec (T := T) (K := K) false) i).R k c :=
  ⟨⟨c, hc, PO.refl _⟩, hk⟩

/-- `[B]` with `A` aborted is complete at an input whose transactions are `A`
and `B`, if `B` has requested commit. -/
theorem decides_r1 (hab : A ≠ B) {k : Inp T K} (hk : ∀ t, k.mem t ↔ t = A ∨ t = B)
    (hf : k.fin B) : Decides false k (mk [B] (· = A)) := by
  refine ⟨fun t => ⟨?_, fun ⟨e, e'⟩ => ?_⟩, fun t ht => ?_⟩
  · show k.mem t ↔ _
    rw [hk, mk_X, mk_dom]; simp only [List.mem_cons, List.not_mem_nil, or_false]
  · have e1 : t = A := e
    have e2 : t = B := by simpa [mk_dom] using e'
    exact hab (e1.symm.trans e2)
  · have e2 : t = B := by simpa [mk_dom] using ht
    rw [e2]; exact hf

/-- `[A]` with `B` aborted is complete at an input whose transactions are `A`
and `B`, if `A` has requested commit. -/
theorem decides_r2 (hab : A ≠ B) {k : Inp T K} (hk : ∀ t, k.mem t ↔ t = A ∨ t = B)
    (hf : k.fin A) : Decides false k (mk [A] (· = B)) := by
  refine ⟨fun t => ⟨?_, fun ⟨e, e'⟩ => ?_⟩, fun t ht => ?_⟩
  · show k.mem t ↔ _
    rw [hk, mk_X, mk_dom]; simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact or_comm
  · have e1 : t = B := e
    have e2 : t = A := by simpa [mk_dom] using e'
    exact hab (e2.symm.trans e1)
  · have e2 : t = A := by simpa [mk_dom] using ht
    rw [e2]; exact hf

/-- **MVTO's eager abort**, as a run under `B_MVTO` driven by arrivals (with a
third transaction `C` that may still arrive).  Inputs: `i1` (`A` has issued a
read of `x`), `i2` (and `B` a read of `x`), `i3` (and `A` a write of `x`),
`i4` (and `B` its commit request); `j2` adds `A`'s commit request.

1. `A`'s first operation: `Commit([stamp(A)])`.  `B`'s arrives: `input(i2)`,
   `Commit([stamp(B)])` with `Z = {A}`.
2. Reporting `B`'s read as the initial version is not exposable: the row
   `[A,B]` at `j2`, where `A` writes `x`, cannot be completed with it.
   `read(B,0,initial)` removes that row, and `Out_[read(B,0,initial)](u)` is
   legal.
3. `A`'s write arrives: `input(i3)`.  At `j2` both completions remain, `r1`
   (`B` committed, `A` aborted) and `r2` (`A` committed, `B` aborted); emitting
   `A`'s abort is not exposable; `abort(A)` and `abort(B)` are both defined and
   keep different completions.  MVTO's write rule emits `A`'s abort with
   `Out_[abort(A)]`.
4. Alternatively, `B`'s commit request arrives: `input(i4)`,
   `Commit([TxCommit(B)])`; then `A`'s abort is exposable, and `Out_ε` emits
   it. -/
theorem mvto_run (h : Distinct3 A B C) (x : K) :
    ∃ σ1 σ2 σ3 σ3r σ4 σ5 σ6 σ7 σ8 : State (spec (T := T) (K := K) false),
      -- 1
      SysStep basisMVTO (canon _ (i1 (A := A) x)) (.commit [stamp A (fun _ => False)]) σ1 ∧
      SysStep basisMVTO σ1 (.input (i2 h x)) σ2 ∧
      SysStep basisMVTO σ2 (.commit [stamp B (· = A)]) σ3 ∧
      -- 2
      σ3.R (j2 h x) (rAB A B) ∧ ¬ Exposable σ3 (u B) ∧
      (read B 0 none).app σ3 = some σ3r ∧ ¬ σ3r.R (j2 h x) (rAB A B) ∧
      SysStep basisMVTO σ3 (.output [read B 0 none] (u B)) σ4 ∧
      -- 3
      SysStep basisMVTO σ4 (.input (i3 h x)) σ5 ∧
      σ5.R (j2 h x) (r1 A B) ∧ σ5.R (j2 h x) (r2 A B) ∧
      ¬ Exposable σ5 (addAbort (u B) A) ∧
      (∃ τA, (abort A).app σ5 = some τA ∧
        τA.R (j2 h x) (r1 A B) ∧ ¬ τA.R (j2 h x) (r2 A B)) ∧
      (∃ τB, (abort B).app σ5 = some τB ∧
        τB.R (j2 h x) (r2 A B) ∧ ¬ τB.R (j2 h x) (r1 A B)) ∧
      (∃ τe, SysStep basisMVTO σ5 (.output [abort A] (addAbort (u B) A)) τe) ∧
      -- 4
      SysStep basisMVTO σ5 (.input (i4 h x)) σ6 ∧
      SysStep basisMVTO σ6 (.commit [commit B]) σ7 ∧
      Exposable σ7 (addAbort (u B) A) ∧
      SysStep basisMVTO σ7 (.output [] (addAbort (u B) A)) σ8 := by
  -- names
  let I1 := i1 (K := K) (A := A) x
  let I2 := i2 h x
  let I3 := i3 h x
  let I4 := i4 h x
  let J := j2 h x
  let J3 := j3 h x
  let σ0 := canon (spec (T := T) (K := K) false) I1
  have hA1 : I1.mem A := show A ∈ [A] by simp
  have hA2 : I2.mem A := (i_mem2 A).2 (Or.inl rfl)
  have hB2 : I2.mem B := (i_mem2 B).2 (Or.inr rfl)
  have hA3 : I3.mem A := (i3_mem A).2 (Or.inl rfl)
  have hBJ : J.fin B := j2_fin B ((j2_mem B).2 (Or.inr rfl))
  have l2' : ∀ s t, (mk [B, A] fun _ => False).lt s t ↔ s = B ∧ t = A := lt2 (Ne.symm h.ab) _
  have l2 : ∀ s t, (mk [A, B] fun _ => False).lt s t ↔ s = A ∧ t = B := lt2 h.ab _
  have lACB := lt_ACB h (fun _ => False)
  -- complete rows
  have pJ : ∀ {o : Outcome T}, (∀ t, ¬ o.X t) → (∀ t, (t = A ∨ t = B) ↔ o.dom t) →
      Decides false J o := fun hX hd =>
    decides_of_all_fin j2_fin (fun t => ⟨by
      show t ∈ [A, B] ↔ _
      rw [show t ∈ [A, B] ↔ t = A ∨ t = B by simp, hd]
      exact ⟨Or.inr, fun h' => h'.elim (fun e => absurd e (hX t)) id⟩, fun h' => hX t h'.1⟩) hX
  have dAB : Decides false J (mk [A, B] fun _ => False) := pJ (fun _ h => h) (fun t => by simp [mk_dom])
  have dBA : Decides false J (mk [B, A] fun _ => False) :=
    pJ (fun _ h => h) (fun t => by simp [mk_dom]; exact or_comm)
  have dACB : Decides false J3 (mk [A, C, B] fun _ => False) :=
    decides_of_all_fin j3_fin (fun t => ⟨by
      show t ∈ [A, B, C] ↔ _
      simp [mk_X, mk_dom]
      constructor <;> rintro (e | e | e) <;> simp [e], fun h' => h'.1⟩) (fun _ h => h)
  -- complete rows
  have cAB : Complete false J (rAB (K := K) A B) := full_complete dAB
  have cBA : Complete false J (full (K := K) (mk [B, A] fun _ => False)) := full_complete dBA
  have cACB : Complete false J3 (full (K := K) (mk [A, C, B] fun _ => False)) :=
    full_complete dACB
  have dr1 : Decides false J (mk [B] (· = A)) := decides_r1 h.ab j2_mem hBJ
  have dr2 : Decides false J (mk [A] (· = B)) :=
    decides_r2 h.ab j2_mem (j2_fin A ((j2_mem A).2 (Or.inl rfl)))
  have dr1' : Decides false I4 (mk [B] (· = A)) := decides_r1 h.ab i4_mem i4_finB
  have nlt1 : ∀ {a : T} {Xs : T → Prop} {w : T}, ¬ (mk [a] Xs).lt w B := lt1 _ _ _ _
  have c1 : Complete false J (r1 (K := K) A B) :=
    complete_u dr1 j2_opB (fun _ w hw => absurd hw nlt1)
  have c2 : Complete false J (r2 (K := K) A B) :=
    complete_u dr2 j2_opB (fun hd => by
      have : B ∈ [A] := hd; simp at this; exact absurd this.symm h.ab)
  have c1' : Complete false I4 (r1 (K := K) A B) :=
    complete_u dr1' i4_opB (fun _ w hw => absurd hw nlt1)
  have i3_opB : I3.op B 0 = some (.rd x) := Inp.le_op le23 i2_opB
  have caR : ∀ {k : Inp T K}, k.op B 0 = some (.rd x) → Complete false k (aR B k) :=
    fun hop => complete_u (allAbort_decides _) hop (fun hd => hd.elim)
  -- stamp conditions
  have nolt : ∀ {a : T} {Z : T → Prop} {o : Outcome T}, (∀ s t, ¬ o.lt s t) → StampOK a Z o :=
    fun hn => ⟨fun _ _ _ hl => hn _ _ hl, fun _ _ hl => hn _ _ hl⟩
  have aAll : ∀ (k : Inp T K) s t, ¬ (allAbort k.txs).lt s t := fun _ _ _ h => h
  have sA_AB : StampOK A (fun _ => False) (mk [A, B] fun _ => False) :=
    ⟨fun D _ hne hD => by rw [l2] at hD; exact hne hD.1, fun _ h => h.elim⟩
  have sB_AB : StampOK B (· = A) (mk [A, B] fun _ => False) :=
    ⟨fun D hD _ hl => by rw [l2] at hl; exact hD hl.1,
     fun _ _ hl => by rw [l2] at hl; exact h.ab hl.1.symm⟩
  have sA_ACB : StampOK A (fun _ => False) (mk [A, C, B] fun _ => False) :=
    ⟨fun D _ _ hl => by
      rw [lACB] at hl
      rcases hl with ⟨_, e | e⟩ | ⟨_, e⟩
      · exact h.ac e
      · exact h.ab e
      · exact h.ab e, fun _ h => h.elim⟩
  have nB_ACB : ¬ StampOK B (· = A) (mk [A, C, B] fun _ => False) :=
    fun hs => hs.1 C (fun e => h.ac e.symm) (Ne.symm h.bc) ((lACB C B).2 (Or.inr ⟨rfl, rfl⟩))
  have s1 : ∀ {Z : T → Prop} {a : T}, StampOK a Z (mk [B] (· = A)) := nolt (lt1 _ _)
  have s2 : ∀ {Z : T → Prop} {a : T}, StampOK a Z (mk [A] (· = B)) := nolt (lt1 _ _)
  -- σ1: `stamp(A)` on `A`'s first operation
  have r0 : ∀ {k : Inp T K} {w c : ROut T K}, w ≼ c → Complete false k c → I1 ≼ k →
      σ0.R k w := fun hw hc hk => ⟨spec_down ⟨_, hc, PO.refl _⟩ hw, hk⟩
  have cAll1 : Complete false I1 (full (K := K) (allAbort I1.txs)) :=
    full_complete (allAbort_decides _)
  obtain ⟨σ1, h1⟩ := exists_of_defined (af := false) (σ := σ0)
    (G := fun σ => σ.cur.mem A ∧ ¬ False ∧ ∀ z, False → σ.cur.mem z)
    (Q := fun c => StampOK A (fun _ => False) c.o)
    ⟨⟨hA1, id, fun _ h => h.elim⟩,
     ⟨_, (keep_complete (P := StampOK A fun _ => False) cAll1.1).2
        ⟨r0 (PO.refl _) cAll1 (PO.refl _), nolt (aAll _)⟩⟩,
     _, _, r0 (PO.refl _) cBA le1j, fun hk =>
       ((keep_complete (P := StampOK A fun _ => False) dBA).1 hk).2.1 B id (Ne.symm h.ab)
         ((l2' B A).2 ⟨rfl, rfl⟩)⟩
  have h1' : (stamp (K := K) A (fun _ => False)).app σ0 = some σ1 := h1
  have m1 : ∀ {k : Inp T K} {w c : ROut T K}, w ≼ c → Complete false k c → I1 ≼ k →
      StampOK A (fun _ => False) c.o → σ1.R k w := fun hw hc hk hs =>
    mem_close h1 (r0 hw hc hk) (r0 (PO.refl _) hc hk) hc.1 hw hs
  have step1 : SysStep basisMVTO σ0 (.commit [stamp A (fun _ => False)]) σ1 :=
    SysStep.commit (fun c hc => by
        simp only [List.mem_singleton] at hc; subst hc; exact Or.inl ⟨A, _, rfl⟩)
      (List.cons_ne_nil _ _) (ApplySeq.cons h1' (ApplySeq.nil _))
  have cur1 : σ1.cur = I1 := (closeC_app_iff.1 h1).2.1
  -- σ2: `B`'s read arrives
  have cAll2 : Complete false I2 (full (K := K) (allAbort I2.txs)) :=
    full_complete (allAbort_decides _)
  let σ2 := inSt σ1 I2 _ (m1 (PO.refl _) cAll2 le12 (nolt (aAll _)))
  have step2 : SysStep basisMVTO σ1 (.input I2) σ2 := inSt_step _ _ _ _
  have m2 : ∀ {k : Inp T K} {w c : ROut T K}, w ≼ c → Complete false k c → I1 ≼ k →
      I2 ≼ k → StampOK A (fun _ => False) c.o → σ2.R k w := fun hw hc hk hk2 hs =>
    ⟨m1 hw hc hk hs, hk2⟩
  -- σ3: `stamp(B)` after `A`
  obtain ⟨σ3, h3⟩ := exists_of_defined (af := false) (σ := σ2)
    (G := fun σ => σ.cur.mem B ∧ ¬ (B = A) ∧ ∀ z, z = A → σ.cur.mem z)
    (Q := fun c => StampOK B (· = A) c.o)
    ⟨⟨hB2, fun e => h.ab e.symm, fun z hz => by rw [hz]; exact hA2⟩,
     ⟨_, (keep_complete (P := StampOK B (· = A)) cAll2.1).2
        ⟨m2 (PO.refl _) cAll2 le12 (PO.refl _) (nolt (aAll _)), nolt (aAll _)⟩⟩,
     _, _, m2 (PO.refl _) cACB le1j3 le2j3 sA_ACB,
     fun hk => nB_ACB ((keep_complete (P := StampOK B (· = A)) dACB).1 hk).2⟩
  have h3' : (stamp (K := K) B (· = A)).app σ2 = some σ3 := h3
  have cur3 : σ3.cur = I2 := (closeC_app_iff.1 h3).2.1
  have m3 : ∀ {k : Inp T K} {w c : ROut T K}, w ≼ c → Complete false k c → I1 ≼ k →
      I2 ≼ k → StampOK A (fun _ => False) c.o → StampOK B (· = A) c.o → σ3.R k w :=
    fun hw hc hk hk2 hs hs' =>
      mem_close h3 (m2 hw hc hk hk2 hs) (m2 (PO.refl _) hc hk hk2 hs) hc.1 hw hs'
  have step3 : SysStep basisMVTO σ2 (.commit [stamp B (· = A)]) σ3 :=
    SysStep.commit (fun c hc => by
        simp only [List.mem_singleton] at hc; subst hc; exact Or.inl ⟨B, _, rfl⟩)
      (List.cons_ne_nil _ _) (ApplySeq.cons h3' (ApplySeq.nil _))
  have good3 : Good σ3 := good_close h3 (good_input (Step.input _ _ _ ⟨_, (m1 (PO.refl _) cAll2
    le12 (nolt (aAll _)))⟩ rfl rfl) (good_close h1 (good_canon I1)))
  -- the row `[A,B]` at `j2` cannot report the read
  have noOwn : ¬ OwnW J B 0 x := fun ⟨_, hm, _⟩ => absurd hm (Nat.not_lt_zero _)
  have noAB : ∀ {w : ROut T K}, (spec (T := T) (K := K) false).S J w → rAB A B ≼ w →
      w.ρ B 0 = some none → False := by
    intro w hw hle e
    obtain ⟨c, hc, hwc⟩ := hw
    have eo := same_o dAB hc.1 (PO.trans hle hwc)
    have hdB : c.o.dom B := by rw [← eo]; show B ∈ [A, B]; simp
    obtain ⟨y, hy, _, hrok⟩ := hc.2 B 0 none (le_ρ hwc e)
    rw [j2_opB] at hy; cases hy
    exact (hrok hdB).2 noOwn A (by rw [← eo]; exact (l2 A B).2 ⟨rfl, rfl⟩) j2_writesA
  have rAB3 : σ3.R J (rAB A B) := m3 (PO.refl _) cAB le1j le2j sA_AB sB_AB
  have nexp3 : ¬ Exposable σ3 (u B) := by
    intro hex
    obtain ⟨w, hw, hu, hle⟩ := hex J (rAB A B) rAB3 (fun hle => by
      have := le_ρ hle (addRead_ρ (full emptyO) B 0 none); cases this)
    exact noAB (σ3.sub _ _ hw) hle (le_ρ hu (addRead_ρ _ B 0 none))
  -- σ3r: `read(B,0,initial)`
  have aR3 : σ3.R I2 (aR B I2) :=
    m3 (PO.refl _) (caR i2_opB) le12 (PO.refl _) (nolt (aAll _)) (nolt (aAll _))
  obtain ⟨σ3r, h3r⟩ := exists_of_defined (af := false) (σ := σ3)
    (G := fun σ => ∃ y, σ.cur.op B 0 = some (.rd y)) (Q := fun c => c.ρ B 0 = some none)
    ⟨⟨x, by rw [cur3]; exact i2_opB⟩,
     ⟨aR B I2, by rw [cur3]; exact ⟨aR3, _, aR3, allAbort_decides _, PO.refl _,
        addRead_ρ (full emptyO) B 0 none⟩⟩,
     _, _, rAB3, fun ⟨_, c, hc, _, hle, hq⟩ => noAB (σ3.sub _ _ hc) hle hq⟩
  have h3r' : (read (K := K) B 0 none).app σ3 = some σ3r := h3r
  have cur3r : σ3r.cur = I2 := (closeC_app_iff.1 h3r).2.1.trans cur3
  have nAB3r : ¬ σ3r.R J (rAB A B) := fun hm =>
    let ⟨_, c, hc, _, hle, hq⟩ := ((closeC_app_iff.1 h3r).2.2 _ _).1 hm
    noAB (σ3.sub _ _ hc) hle hq
  have m3r : ∀ {k : Inp T K} {w c : ROut T K}, w ≼ c → Complete false k c → I1 ≼ k →
      I2 ≼ k → StampOK A (fun _ => False) c.o → StampOK B (· = A) c.o →
      c.ρ B 0 = some none → σ3r.R k w :=
    fun hw hc hk hk2 hs hs' hq =>
      mem_close h3r (m3 hw hc hk hk2 hs hs') (m3 (PO.refl _) hc hk hk2 hs hs') hc.1 hw hq
  -- σ4: `Out_[read(B,0,initial)](u)`
  have e0 : σ3r.R I2 (full emptyO) :=
    m3r (full_le _) (caR i2_opB) le12 (PO.refl _) (nolt (aAll _)) (nolt (aAll _))
      (addRead_ρ _ B 0 none)
  obtain ⟨u3, uexp⟩ := read_emit good3 h3r e0 (fun _ w _ => full_le w)
  have u3' : σ3r.R σ3r.cur (u B) := by rw [cur3r]; exact u3
  let σ4 := outState σ3r (u B) u3'
  have step4 : SysStep basisMVTO σ3 (.output [read B 0 none] (u B)) σ4 :=
    SysStep.output (fun c hc => by
        simp only [List.mem_singleton] at hc; subst hc
        exact Or.inr (Or.inr (Or.inr ⟨B, 0, none, rfl⟩)))
      (ApplySeq.cons h3r' (ApplySeq.nil _)) u3' uexp ((closeC_app_iff.1 h3r).2.1) rfl
  have m4 : ∀ {k : Inp T K} {w c : ROut T K}, w ≼ c → Complete false k c → I1 ≼ k →
      I2 ≼ k → StampOK A (fun _ => False) c.o → StampOK B (· = A) c.o →
      c.ρ B 0 = some none → u B ≼ w → σ4.R k w :=
    fun hw hc hk hk2 hs hs' hq hu => ⟨m3r hw hc hk hk2 hs hs' hq, hu⟩
  -- σ5: `A`'s write arrives
  let σ5 := inSt σ4 I3 _ (m4 (PO.refl _) (caR i3_opB) le13 le23 (nolt (aAll _)) (nolt (aAll _))
    (addRead_ρ _ B 0 none) (u_le B _))
  have step5 : SysStep basisMVTO σ4 (.input I3) σ5 := inSt_step _ _ _ _
  have m5 : ∀ {k : Inp T K} {w c : ROut T K}, w ≼ c → Complete false k c → I1 ≼ k →
      I2 ≼ k → StampOK A (fun _ => False) c.o → StampOK B (· = A) c.o →
      c.ρ B 0 = some none → u B ≼ w → I3 ≼ k → σ5.R k w :=
    fun hw hc hk hk2 hs hs' hq hu hk3 => ⟨m4 hw hc hk hk2 hs hs' hq hu, hk3⟩
  have hρu : (u (K := K) B).ρ B 0 = some none := addRead_ρ _ B 0 none
  have r1_5 : σ5.R J (r1 A B) :=
    m5 (PO.refl _) c1 le1j le2j s1 s1 hρu (u_le B _) le3j
  have r2_5 : σ5.R J (r2 A B) :=
    m5 (PO.refl _) c2 le1j le2j s2 s2 hρu (u_le B _) le3j
  have aR5 : σ5.R I3 (aR B I3) :=
    m5 (PO.refl _) (caR i3_opB) le13 le23 (nolt (aAll _)) (nolt (aAll _)) hρu (u_le B _)
      (PO.refl _)
  have u5 : σ5.R I3 (u B) :=
    m5 (u_le B _) (caR i3_opB) le13 le23 (nolt (aAll _)) (nolt (aAll _)) hρu (PO.refl _)
      (PO.refl _)
  have good5 : Good σ5 :=
    good_input (Step.input _ _ _ ⟨_, aR5.1⟩ rfl rfl)
      (good_outputTable rfl (good_close h3r good3))
  have hall5 : ∀ k w, σ5.R k w → u B ≼ w := fun _ _ hw => hw.1.2
  have nexp5 : ¬ Exposable σ5 (addAbort (u B) A) := by
    intro hex
    obtain ⟨w, hw, hle1, hle2⟩ := hex J (r2 A B) r2_5 (fun hle => by
      have : (mk [A] (· = B)).X A := hle.1.1 A (Or.inr rfl)
      exact h.ab this)
    obtain ⟨c, hc, hwc⟩ := σ5.sub _ _ hw
    exact hc.1.not_both A ⟨hwc.1.1 A (hle1.1.1 A (Or.inr rfl)),
      hwc.1.2.1 A (hle2.1.2.1 A (show A ∈ [A] by simp))⟩
  have nA1 : AbortOK A (mk [B] (· = A)) := fun hd => by
    have : A ∈ [B] := hd; simp at this; exact h.ab this
  have nB2 : AbortOK B (mk [A] (· = B)) := fun hd => by
    have : B ∈ [A] := hd; simp at this; exact h.ab this.symm
  -- `abort(A)` and `abort(B)` at σ5
  obtain ⟨τA, hA⟩ := exists_of_defined (af := false) (σ := σ5) (G := fun σ => σ.cur.mem A)
    (Q := fun c => AbortOK A c.o)
    ⟨hA3, ⟨aR B I3, (keep_complete (P := AbortOK A) (allAbort_decides _)).2 ⟨aR5, fun h => h⟩⟩,
     _, _, r2_5, fun hk => ((keep_complete (P := AbortOK A) dr2).1 hk).2 (show A ∈ [A] by simp)⟩
  obtain ⟨τB, hB⟩ := exists_of_defined (af := false) (σ := σ5) (G := fun σ => σ.cur.mem B)
    (Q := fun c => AbortOK B c.o)
    ⟨(i3_mem (h := h) (x := x) B).2 (Or.inr rfl),
     ⟨aR B I3, (keep_complete (P := AbortOK B) (allAbort_decides _)).2 ⟨aR5, fun h => h⟩⟩,
     _, _, r1_5, fun hk => ((keep_complete (P := AbortOK B) dr1).1 hk).2 (show B ∈ [B] by simp)⟩
  have hA' : (abort (K := K) A).app σ5 = some τA := hA
  -- eager: MVTO's write rule
  have curA : τA.cur = I3 := (closeC_app_iff.1 hA).2.1
  have uA : τA.R τA.cur (u B) := by
    rw [curA]; exact mem_close hA u5 aR5 (allAbort_decides _) (u_le B _) (fun h => h)
  obtain ⟨uA', expA⟩ := abort_emit good5 hA' uA (fun k w hw => hall5 k w ((abort A).sub _ _ hA' k w hw))
  have stepE : SysStep basisMVTO σ5 (.output [abort A] (addAbort (u B) A))
      (outState τA (addAbort (u B) A) uA') :=
    SysStep.output (fun c hc => by
        simp only [List.mem_singleton] at hc; subst hc; exact Or.inr (Or.inr (Or.inl ⟨A, rfl⟩)))
      (ApplySeq.cons hA' (ApplySeq.nil _)) uA' expA curA rfl
  -- lazy: `B`'s commit request arrives
  have aR5' : σ5.R I4 (aR B I4) :=
    m5 (PO.refl _) (caR i4_opB) le14 le24 (nolt (aAll _)) (nolt (aAll _)) hρu (u_le B _) le34
  let σ6 := inSt σ5 I4 _ aR5'
  have step6 : SysStep basisMVTO σ5 (.input I4) σ6 := inSt_step _ _ _ _
  have r1_6 : σ6.R I4 (r1 A B) :=
    ⟨m5 (PO.refl _) c1' le14 le24 s1 s1 hρu (u_le B _) le34, PO.refl _⟩
  have u6 : σ6.R I4 (u B) :=
    ⟨m5 (u_le B _) c1' le14 le24 s1 s1 hρu (PO.refl _) le34, PO.refl _⟩
  have ok1 : CommitOK B (mk [B] (· = A)) := fun hX => h.ab (show B = A from hX).symm
  obtain ⟨σ7, hC⟩ := exists_of_defined (af := false) (σ := σ6) (G := fun σ => σ.cur.fin B)
    (Q := fun c => CommitOK B c.o)
    ⟨(i4_finB : I4.fin B), ⟨r1 A B, (keep_complete (P := CommitOK B) dr1').2 ⟨r1_6, ok1⟩⟩,
     _, _, (⟨aR5', PO.refl _⟩ : σ6.R I4 (aR B I4)),
     fun hk => ((keep_complete (P := CommitOK B) (allAbort_decides _)).1 hk).2
       ((i4_mem (h := h) (x := x) B).2 (Or.inr rfl))⟩
  have hC' : (commit (K := K) B).app σ6 = some σ7 := hC
  have cur7 : σ7.cur = I4 := (closeC_app_iff.1 hC).2.1
  have step7 : SysStep basisMVTO σ6 (.commit [commit B]) σ7 :=
    SysStep.commit (fun c hc => by
        simp only [List.mem_singleton] at hc; subst hc; exact Or.inr (Or.inl ⟨B, rfl⟩))
      (List.cons_ne_nil _ _) (ApplySeq.cons hC' (ApplySeq.nil _))
  -- `A`'s abort is entailed
  have H : TwoStamps A B (fun _ => False) (· = A) σ0 σ3 :=
    ⟨σ1, σ2, h1', fun _ _ h => h.1, h3', rfl⟩
  have sub73 : ∀ k w, σ7.R k w → σ3.R k w := fun k w hw =>
    (read B 0 none).sub _ _ h3r' k w ((((commit B).sub _ _ hC' k w hw).1).1).1
  have good7 : Good σ7 := good_close hC (good_input (Step.input _ _ _ ⟨_, aR5'⟩ rfl rfl) good5)
  have hall7 : ∀ k w, σ7.R k w → u B ≼ w := fun k w hw =>
    hall5 k w ((commit B).sub _ _ hC' k w hw).1
  have hB7 : ∀ k c, σ7.R k c → Decides false k c.o → c.o.dom B := by
    intro k c hc hp
    have hk : I4 ≼ k := cur7 ▸ σ7.above _ _ hc
    exact (hp.decided (Inp.le_mem hk ((i4_mem (h := h) (x := x) B).2 (Or.inr rfl)))).resolve_left
      (after_complete hC (fun _ _ h => h) hc hp)
  obtain ⟨_, _, hent⟩ := H.abort_entailed (fun _ e => by cases e) sub73 good7
    (by rw [cur7]; exact i4_writesA) (by rw [cur7]; exact i4_opB) hall7 hρu hB7
  have u7 : σ7.R σ7.cur (u B) := by
    rw [cur7]; exact mem_close hC u6 r1_6 dr1' (u_le B _) ok1
  obtain ⟨hm, hex⟩ := hent u7
  refine ⟨σ1, σ2, σ3, σ3r, σ4, σ5, σ6, σ7, outState σ7 _ hm, step1, step2, step3, rAB3, nexp3,
    h3r', nAB3r, step4, step5, r1_5, r2_5, nexp5, ?_, ?_, ⟨_, stepE⟩, step6, step7, hex,
    SysStep.output (fun c hc => by cases hc) (ApplySeq.nil _) hm hex rfl rfl⟩
  · exact ⟨τA, hA', mem_close hA r1_5 r1_5 dr1 (PO.refl _) nA1,
      not_mem_close hA dr2 (fun hn => hn (show A ∈ [A] by simp))⟩
  · exact ⟨τB, hB, mem_close hB r2_5 r2_5 dr2 (PO.refl _) nB2,
      not_mem_close hB dr1 (fun hn => hn (show B ∈ [B] by simp))⟩

end Ex

/-! ### The writer must be stamped before `A` -/

/-- **The hypothesis on the version cannot be dropped.**  At an input whose
transactions `A`, `W`, `B` have each requested commit, stamped in that order,
with `A` and `W` writing `x` and the `n`-th operation of `B` a read of `x` not
preceded by a write of `x` by `B`, the complete row that commits all three in
stamp order and reports that the read returned `W`'s write is permitted,
satisfies every stamp, and commits `A`. -/
theorem writer_after_A {A W B : T} {k : Inp T K} (hk : Tri k A W B) {x : K} {n : Nat}
    (hwA : k.writes A x) (hwW : k.writes W x) (hop : k.op B n = some (.rd x))
    (hown : ¬ OwnW k B n x) :
    let r : ROut T K := ⟨mk [A, W, B] fun _ => False, single B n (some W)⟩
    Complete false k r ∧ StampOK A (fun _ => False) r.o ∧
      StampOK W (· = A) r.o ∧ StampOK B (fun z => z = A ∨ z = W) r.o ∧
      k.writes A x ∧ r.ρ B n = some (some W) ∧ r.o.dom A := by
  intro r
  have h := hk.d
  have l : ∀ s t, r.o.lt s t ↔ (s = A ∧ (t = W ∨ t = B)) ∨ (s = W ∧ t = B) :=
    lt3 h.ab h.ac h.bc _
  refine ⟨⟨perm_part hk hm_id, fun a m v e => ?_⟩, ⟨fun D _ hne hl => ?_, fun _ h => h.elim⟩,
    ⟨fun D hD hne hl => ?_, fun z hz hl => ?_⟩, ⟨fun D hD hne hl => ?_, fun z hz hl => ?_⟩,
    hwA, single_eq, show A ∈ [A, W, B] by simp⟩
  · simp only [r, single] at e
    split at e
    · rename_i ham; obtain ⟨rfl, rfl⟩ := ham; cases e
      refine ⟨x, hop, hwW, fun _ => ⟨fun ho => absurd ho hown, fun _ => ?_⟩⟩
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
