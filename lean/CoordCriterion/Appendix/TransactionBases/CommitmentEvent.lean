import CoordCriterion.Appendix.TransactionBases.Partial

/-!
# A 2PL commitment event and its canonical run (§4.3, *Canonical runs suffice*)

Namespace `CC.Txn.Partial.CommitEx`.  The specification of Appendix G
(`Spec.lean`), at an input `k` whose transactions `A`, `B`, `C` have each issued
their operations (any) and requested commit.

When `B` requests a lock that `A` holds, 2PL makes `B` wait.  The wait commits
`B` to serialize after `A` before anything is reported: it is the commitment
event `Apply([order(A,B)])`, which applies `order(A,B)` and emits nothing.
Later, before emitting the serial order `[A,C,B]`, 2PL applies no further
commitment ordering `A` and `B`; the commitment event
`Apply([TxCommit(A),TxCommit(B),TxCommit(C),order(A,C),order(C,B)])` commits
each transaction and places `C`, after which the output event `output([A,C,B])`
is legal.

* `example_commitment_event_ABC` — the 2PL run `Apply([order(A,B)])`,
  `Apply([TxCommit(A),TxCommit(B),TxCommit(C),order(A,C),order(C,B)])`,
  `output([A,C,B])` under `B_2PL`, its canonical run `output([A,C,B])`, their
  `Lockstep` pair (Lemma `lem:canonical-equivalent`, the commitment events
  matched by no canonical event), and the same final state.  After the
  `TxCommit` commitments alone, `output([A,C,B])` is not legal.
-/

namespace CC
namespace Txn
namespace Partial
namespace CommitEx

open Classical

set_option linter.unusedSimpArgs false

variable {T K : Type} {A B C : T}

/-- The complete serial order `[A,C,B]`, no reads reported. -/
noncomputable def o2 (A B C : T) : ROut T K := full (mk [A, C, B] fun _ => False)

/-- The commitments 2PL applies before emitting `[A,C,B]`. -/
noncomputable def γ2 (A B C : T) : List (Commitment (spec (T := T) (K := K) false)) :=
  [commit A, commit B, commit C, order A C, order C B]

/-! ### Closure steps -/

/-- Every complete row of the table satisfies `P`. -/
def AllP (σ : State (spec (T := T) (K := K) false)) (P : Outcome T → Prop) : Prop :=
  ∀ k c, σ.R k c → Decides false k c.o → P c.o

theorem allP_close {G : State (spec (T := T) (K := K) false) → Prop} {P : Outcome T → Prop}
    {σ τ : State (spec (T := T) (K := K) false)} (h : (closeC G (fun c => P c.o)).app σ = some τ) :
    AllP τ P :=
  fun _ _ hc hp => after_complete h (fun _ _ h => h) hc hp

theorem allP_sub {σ τ : State (spec (T := T) (K := K) false)} {P : Outcome T → Prop}
    (hs : ∀ k u, τ.R k u → σ.R k u) (h : AllP σ P) : AllP τ P :=
  fun k c hc hp => h k c (hs k c hc) hp

/-- A closure step for a condition on `(L,X)` that keeps a complete row `r`
and removes a complete row `s` at the current input. -/
theorem step_close {G : State (spec (T := T) (K := K) false) → Prop} {P : Outcome T → Prop}
    {σ : State (spec (T := T) (K := K) false)} {k : Inp T K} (hcur : σ.cur = k) (hG : G σ)
    {r s : ROut T K} (hr : σ.R k r) (hrp : Decides false k r.o) (hPr : P r.o)
    (hs : σ.R k s) (hsp : Decides false k s.o) (hPs : ¬ P s.o) :
    ∃ τ, (closeC G (fun c => P c.o)).app σ = some τ ∧ τ.cur = k ∧ ¬ τ.R k s ∧
      ∀ {k' u c}, σ.R k' u → σ.R k' c → Decides false k' c.o → u ≼ c → P c.o →
        τ.R k' u ∧ τ.R k' c := by
  obtain ⟨τ, hτ⟩ := exists_of_defined (G := G) (Q := fun c => P c.o) (σ := σ)
    ⟨hG, ⟨r, by rw [hcur]; exact (keep_complete hrp).2 ⟨hr, hPr⟩⟩, k, s, hs,
      fun hk => hPs ((keep_complete hsp).1 hk).2⟩
  exact ⟨τ, hτ, (closeC_app_iff.1 hτ).2.1.trans hcur, not_mem_close hτ hsp hPs,
    fun hu hc hp hle hq => ⟨mem_close hτ hu hc hp hle hq, mem_close hτ hc hc hp (PO.refl _) hq⟩⟩

/-- A closure commitment for a condition on `(L,X)` keeps every complete row
that satisfies it. -/
theorem keep_row {G : State (spec (T := T) (K := K) false) → Prop} {P : Outcome T → Prop}
    {σ τ : State (spec (T := T) (K := K) false)} (h : (closeC G (fun c => P c.o)).app σ = some τ)
    {k : Inp T K} {r : ROut T K} (hr : σ.R k r) (hp : Decides false k r.o) (hP : P r.o) :
    τ.R k r :=
  ((closeC_app_iff.1 h).2.2 k r).2 ((keep_complete hp).2 ⟨hr, hP⟩)

/-! ### Rows extending `[A,C,B]` -/

section Rows
variable {k : Inp T K} (h : Tri k A B C)
include h

/-- A complete row at an input above `k` that commits `A`, `B`, `C` and
satisfies the three orders extends `[A,C,B]`. -/
theorem acb_le {k' : Inp T K} {o : Outcome T} (hp : Decides false k' o) (hk : k ≼ k')
    (cA : CommitOK A o) (cB : CommitOK B o) (cC : CommitOK C o) (oAC : OrderOK A C o)
    (oCB : OrderOK C B o) (oAB : OrderOK A B o) : mk [A, C, B] (fun _ => False) ≼ o := by
  have hd := h.d
  have dom : ∀ t, (t = A ∨ t = B ∨ t = C) → ¬ o.X t → o.dom t := fun t ht hX =>
    (hp.decided (Inp.le_mem hk ((h.mem t).2 ht))).resolve_left hX
  have dA := dom A (Or.inl rfl) cA
  have dB := dom B (Or.inr (Or.inl rfl)) cB
  have dC := dom C (Or.inr (Or.inr rfl)) cC
  have hAC : o.lt A C := (o.total A C dA dC hd.ac).resolve_right oAC
  have hCB : o.lt C B := (o.total C B dC dB (Ne.symm hd.bc)).resolve_right oCB
  have hAB : o.lt A B := (o.total A B dA dB hd.ab).resolve_right oAB
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
  · rw [lt_ACB hd]
    simp only [mk_dom, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with e | e | e <;> rcases hb with e' | e' | e' <;> rw [e, e'] <;>
      simp [hAC, hCB, hAB, nCA, nBC, nBA, irr, hd.ab, hd.ac, hd.bc, Ne.symm hd.ab,
        Ne.symm hd.ac, Ne.symm hd.bc]

/-- A complete row extending `[A,C,B]` satisfies the six conditions. -/
theorem le_acb {k' : Inp T K} {o : Outcome T} (hp : Decides false k' o)
    (hle : mk [A, C, B] (fun _ => False) ≼ o) :
    CommitOK A o ∧ CommitOK B o ∧ CommitOK C o ∧ OrderOK A C o ∧ OrderOK C B o ∧
      OrderOK A B o := by
  have hd := h.d
  have mA : (mk [A, C, B] fun _ => False).dom A := by simp [mk_dom]
  have mB : (mk [A, C, B] fun _ => False).dom B := by simp [mk_dom]
  have mC : (mk [A, C, B] fun _ => False).dom C := by simp [mk_dom]
  have nl : ∀ s t, (mk [A, C, B] fun _ => False).dom s → (mk [A, C, B] fun _ => False).dom t →
      ¬ (mk [A, C, B] fun _ => False).lt s t → ¬ o.lt s t :=
    fun s t hs ht hn hl => hn ((hle.2.2 s t hs ht).1 hl)
  refine ⟨fun hX => hp.not_both A ⟨hX, hle.2.1 A mA⟩, fun hX => hp.not_both B ⟨hX, hle.2.1 B mB⟩,
    fun hX => hp.not_both C ⟨hX, hle.2.1 C mC⟩, nl C A mC mA ?_, nl B C mB mC ?_,
    nl B A mB mA ?_⟩ <;>
    rw [lt_ACB hd] <;> simp [hd.ab, hd.ac, hd.bc, Ne.symm hd.ab, Ne.symm hd.ac, Ne.symm hd.bc]

end Rows

/-- Evaluate order facts of the rows used below. -/
macro "d5 " h:term : tactic =>
  `(tactic| simp [full, allAbort, OrderOK, CommitOK, mk_X, mk_dom, lt_ABC $h,
    lt_BAC $h, lt_CAB $h, lt_ACB $h, lt2 ($h).ab, lt2 ($h).ac, ($h).ab, ($h).ac, ($h).bc,
    Ne.symm ($h).ab, Ne.symm ($h).ac, Ne.symm ($h).bc])

/-! ### The two runs -/

/-- **2PL with a commitment event, and its canonical run** (§4.3, *Canonical
runs suffice*).  `k` is an input whose transactions `A`, `B`, `C` have each
issued their operations and requested commit; `B` waits for a lock `A` holds.
`σ₀` is the canonical state of `k`; rows are written as serial orders without
aborts or reads.

(a) When `B` begins to wait, the commitment event `Apply([order(A,B)])` is a
    legal `B_2PL` step from `σ₀` to `σ₁`, before any output.  It keeps the
    current input and keeps exactly the rows of `σ₀` that have a complete
    output extension in `σ₀` that does not commit `B` before `A` (aborting `A` or `B`
    counts); in particular it keeps `[A,B,C]` and removes `[B,A,C]`.
(b) The canonical run skips that event: it is still at `σ₀`, which has the row
    `[B,A,C]`.
(c) 2PL then applies the commitment event `Apply([TxCommit(A), TxCommit(B),
    TxCommit(C), order(A,C), order(C,B)])` (a `B_2PL` step from `σ₁` to `σ₂`),
    after which `output([A,C,B])` is legal and is a `B_2PL` step.  After the
    `TxCommit` commitments alone it would not be legal.  The canonical run can
    emit the same output because that row was present at `σ₀`.  Every row it
    retains afterward extends `[A,C,B]`, hence satisfies all five commitments
    of the second commitment event and the earlier `order(A,B)`.
(d) The canonical final table is therefore contained in 2PL's; Observable
    Equivalence gives the reverse containment.  The two runs end at the same
    state, and form a `Lockstep` pair in which both commitment events are
    matched by no canonical event. -/
theorem example_commitment_event_ABC {k : Inp T K} (h : Tri k A B C) :
    ∃ σ1 σ2 τ2 τ2' : State (spec (T := T) (K := K) false),
      -- (a)
      SysStep basis2PL (σ3 k) (.commitment [order A B]) σ1 ∧ σ1.cur = k ∧
      (∀ k' w, σ1.R k' w ↔ (σ3 k).R k' w ∧
        ∃ c, (σ3 k).R k' c ∧ Decides false k' c.o ∧ w ≼ c ∧ ¬ c.o.lt B A) ∧
      σ1.R k (full (mk [A, B, C] fun _ => False)) ∧
      ¬ σ1.R k (full (mk [B, A, C] fun _ => False)) ∧
      -- (b)
      (σ3 k).R k (full (mk [B, A, C] fun _ => False)) ∧
      -- (c)
      SysStep basis2PL σ1 (.commitment (γ2 A B C)) σ2 ∧
      Exposable σ2 (o2 A B C) ∧ SysStep basis2PL σ2 (.output (o2 A B C)) τ2 ∧
      (¬ ∃ ρ, SysStep basis2PL σ1 (.commitment [commit A, commit B, commit C]) ρ ∧
        Exposable ρ (o2 A B C)) ∧
      CanonStep (σ3 k) (.output (o2 A B C)) τ2' ∧
      -- (d)
      τ2 = τ2' ∧
      Lockstep basis2PL (σ3 k)
        [.commitment [order A B], .commitment (γ2 A B C), .output (o2 A B C)] τ2
        (σ3 k) [.output (o2 A B C)] τ2' := by
  have hd := h.d
  let σ0 := σ3 (T := T) (K := K) k
  let Z : T → Prop := fun _ => False
  have hA : k.mem A := (h.mem A).2 (Or.inl rfl)
  have hB : k.mem B := (h.mem B).2 (Or.inr (Or.inl rfl))
  have hC : k.mem C := (h.mem C).2 (Or.inr (Or.inr rfl))
  have fA := h.fin A hA
  have fB := h.fin B hB
  have fC := h.fin C hC
  -- rows
  have pACB := perm_part (af := false) h hm_acb
  have pABC := perm_part (af := false) h hm_id
  have pBAC := perm_part (af := false) h hm_bac
  have pCAB := perm_part (af := false) h hm_cab
  have pAll : Decides false k (allAbort k.txs) := allAbort_decides k
  have r0 : ∀ {o : Outcome T}, Decides false k o → σ0.R k (full o) := fun hp =>
    ⟨⟨_, full_complete hp, PO.refl _⟩, PO.refl _⟩
  -- the partially aborted rows `[A,C]` (B aborted) and `[A,B]` (C aborted)
  have pACb : Decides false k (mk [A, C] (· = B)) := by
    refine ⟨fun t => ⟨?_, fun ⟨e, hm⟩ => ?_⟩, fun t ht => h.fin t ?_⟩
    · show k.mem t ↔ _
      rw [h.mem, mk_X, mk_dom]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor <;> rintro (e | e | e) <;> simp [e]
    · have e' : t = B := e
      rw [e'] at hm
      simp only [mk_dom, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with e'' | e''
      · exact hd.ab e''.symm
      · exact hd.bc e''
    · simp only [mk_dom, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with e | e <;> rw [e]
      · exact hA
      · exact hC
  have pABc : Decides false k (mk [A, B] (· = C)) := by
    refine ⟨fun t => ⟨?_, fun ⟨e, hm⟩ => ?_⟩, fun t ht => h.fin t ?_⟩
    · show k.mem t ↔ _
      rw [h.mem, mk_X, mk_dom]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor <;> rintro (e | e | e) <;> simp [e]
    · have e' : t = C := e
      rw [e'] at hm
      simp only [mk_dom, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with e'' | e''
      · exact hd.ac e''.symm
      · exact hd.bc e''.symm
    · simp only [mk_dom, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with e | e <;> rw [e]
      · exact hA
      · exact hB
  -- (a) the commitment event `Apply([order(A,B)])`
  obtain ⟨σ1, h1, cur1, nBAC1, m1⟩ := step_close (G := fun σ : State (spec (T := T) (K := K) false) =>
      A ≠ B ∧ σ.cur.mem A ∧ σ.cur.mem B) (P := OrderOK A B) (σ := σ0) (k := k) rfl
    ⟨hd.ab, hA, hB⟩ (r0 pACB) pACB (by d5 hd) (r0 pBAC) pBAC (by d5 hd)
  have h1' : (order (K := K) A B).app σ0 = some σ1 := h1
  have stepC : SysStep basis2PL σ0 (.commitment [order A B]) σ1 :=
    SysStep.commitment (fun c hc => by
        simp only [List.mem_singleton] at hc; subst hc; exact Or.inl ⟨A, B, rfl⟩)
      (List.cons_ne_nil _ _) (ApplySeq.cons h1' (ApplySeq.nil _))
  have keep1 : ∀ k' w, σ1.R k' w ↔ σ0.R k' w ∧
      ∃ c, σ0.R k' c ∧ Decides false k' c.o ∧ w ≼ c ∧ ¬ c.o.lt B A :=
    (closeC_app_iff.1 h1).2.2
  have t1 : ∀ {o : Outcome T}, Decides false k o → OrderOK A B o → σ1.R k (full o) :=
    fun hp hq => (m1 (r0 hp) (r0 hp) hp (PO.refl _) hq).1
  have rABC1 := t1 pABC (by d5 hd)
  -- (c) the output event
  have tACB := t1 pACB (by d5 hd)
  have rAll1 := t1 pAll (fun h => h)
  obtain ⟨σa, ha, cura, _, ma⟩ := step_close (G := fun σ : State (spec (T := T) (K := K) false) =>
      σ.cur.fin A) (P := CommitOK A) (σ := σ1) (k := k) cur1
    (by show σ1.cur.fin A; rw [cur1]; exact fA) tACB pACB (by d5 hd) rAll1 pAll (fun hn => hn hA)
  have aACB := (ma tACB tACB pACB (PO.refl _) (by d5 hd)).1
  have aACb := (ma (t1 pACb (by d5 hd)) (t1 pACb (by d5 hd)) pACb (PO.refl _) (by d5 hd)).1
  have aABc := (ma (t1 pABc (by d5 hd)) (t1 pABc (by d5 hd)) pABc (PO.refl _) (by d5 hd)).1
  have aCAB := (ma (t1 pCAB (by d5 hd)) (t1 pCAB (by d5 hd)) pCAB (PO.refl _) (by d5 hd)).1
  have aABC := (ma rABC1 rABC1 pABC (PO.refl _) (by d5 hd)).1
  obtain ⟨σb, hb, curb, _, mb⟩ := step_close (G := fun σ : State (spec (T := T) (K := K) false) =>
      σ.cur.fin B) (P := CommitOK B) (σ := σa) (k := k) cura
    (by show σa.cur.fin B; rw [cura]; exact fB) aACB pACB (by d5 hd) aACb pACb (by d5 hd)
  have bACB := (mb aACB aACB pACB (PO.refl _) (by d5 hd)).1
  have bABc := (mb aABc aABc pABc (PO.refl _) (by d5 hd)).1
  have bCAB := (mb aCAB aCAB pCAB (PO.refl _) (by d5 hd)).1
  have bABC := (mb aABC aABC pABC (PO.refl _) (by d5 hd)).1
  obtain ⟨σc, hc, curc, _, mc⟩ := step_close (G := fun σ : State (spec (T := T) (K := K) false) =>
      σ.cur.fin C) (P := CommitOK C) (σ := σb) (k := k) curb
    (by show σb.cur.fin C; rw [curb]; exact fC) bACB pACB (by d5 hd) bABc pABc (by d5 hd)
  have cACB := (mc bACB bACB pACB (PO.refl _) (by d5 hd)).1
  have cCAB := (mc bCAB bCAB pCAB (PO.refl _) (by d5 hd)).1
  have cABC := (mc bABC bABC pABC (PO.refl _) (by d5 hd)).1
  obtain ⟨σd, hdd, curd, _, md⟩ := step_close (G := fun σ : State (spec (T := T) (K := K) false) =>
      A ≠ C ∧ σ.cur.mem A ∧ σ.cur.mem C) (P := OrderOK A C) (σ := σc) (k := k) curc
    ⟨hd.ac, by rw [curc]; exact hA, by rw [curc]; exact hC⟩
    cACB pACB (by d5 hd) cCAB pCAB (by d5 hd)
  have dACB := (md cACB cACB pACB (PO.refl _) (by d5 hd)).1
  have dABC := (md cABC cABC pABC (PO.refl _) (by d5 hd)).1
  obtain ⟨σe, he, cure, _, me⟩ := step_close (G := fun σ : State (spec (T := T) (K := K) false) =>
      C ≠ B ∧ σ.cur.mem C ∧ σ.cur.mem B) (P := OrderOK C B) (σ := σd) (k := k) curd
    ⟨Ne.symm hd.bc, by rw [curd]; exact hC, by rw [curd]; exact hB⟩
    dACB pACB (by d5 hd) dABC pABC (by d5 hd)
  have eACB := (me dACB dACB pACB (PO.refl _) (by d5 hd)).1
  have app2 : ApplySeq (γ2 (K := K) A B C) σ1 σe :=
    ApplySeq.cons ha (ApplySeq.cons hb (ApplySeq.cons hc (ApplySeq.cons hdd
      (ApplySeq.cons he (ApplySeq.nil _)))))
  -- subsets
  have se : ∀ k u, σe.R k u → σd.R k u := (order C B).sub _ _ he
  have sd : ∀ k u, σd.R k u → σc.R k u := (order A C).sub _ _ hdd
  have sc : ∀ k u, σc.R k u → σb.R k u := (commit C).sub _ _ hc
  have sb : ∀ k u, σb.R k u → σa.R k u := (commit B).sub _ _ hb
  have sa : ∀ k u, σa.R k u → σ1.R k u := (commit A).sub _ _ ha
  have s1 : ∀ k u, σ1.R k u → σ0.R k u := (order A B).sub _ _ h1'
  -- every complete row of σe satisfies the six conditions
  have PAB : AllP σe (OrderOK A B) := allP_sub (fun k u h => sa k u (sb k u
    (sc k u (sd k u (se k u h))))) (allP_close h1)
  have PcA : AllP σe (CommitOK A) := allP_sub (fun k u h => sb k u
    (sc k u (sd k u (se k u h)))) (allP_close ha)
  have PcB : AllP σe (CommitOK B) := allP_sub (fun k u h => sc k u (sd k u (se k u h)))
    (allP_close hb)
  have PcC : AllP σe (CommitOK C) := allP_sub (fun k u h => sd k u (se k u h)) (allP_close hc)
  have PAC : AllP σe (OrderOK A C) := allP_sub se (allP_close hdd)
  have PCB : AllP σe (OrderOK C B) := allP_close he
  have ge : Good σe := good_close he (good_close hdd (good_close hc (good_close hb
    (good_close ha (good_close h1 (good_canon k))))))
  have o2e : σe.R σe.cur (o2 A B C) := by rw [cure]; exact eACB
  have exp2 : Exposable σe (o2 A B C) := by
    intro k' w hw _
    obtain ⟨c, hc', hp, hle⟩ := ge.2 k' w hw
    have hk : k ≼ k' := cure ▸ σe.above _ _ hc'
    have hmk := acb_le h hp hk (PcA k' c hc' hp) (PcB k' c hc' hp) (PcC k' c hc' hp)
      (PAC k' c hc' hp) (PCB k' c hc' hp) (PAB k' c hc' hp)
    exact ⟨c, hc', ⟨hmk, fun _ _ _ e => by cases e⟩, hle⟩
  let τ2 := outState σe (o2 A B C) o2e
  have step2 : SysStep basis2PL σe (.output (o2 A B C)) τ2 :=
    legal_output_step (step_output_outState o2e) exp2
  have stepγ : SysStep basis2PL σ1 (.commitment (γ2 A B C)) σe := by
    refine SysStep.commitment (fun c hc => ?_) (List.cons_ne_nil _ _) app2
    simp only [γ2, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨A, rfl⟩)
    · exact Or.inr (Or.inl ⟨B, rfl⟩)
    · exact Or.inr (Or.inl ⟨C, rfl⟩)
    · exact Or.inl ⟨A, C, rfl⟩
    · exact Or.inl ⟨C, B, rfl⟩
  -- the canonical run
  have o2_0 : σ0.R σ0.cur (o2 A B C) := r0 pACB
  let τ2' := outState σ0 (o2 A B C) o2_0
  have cstep : CanonStep σ0 (.output (o2 A B C)) τ2' :=
    ⟨canonical_support σ0 (o2 A B C) o2_0, fun _ e => by cases e⟩
  have sub2 : ∀ k u, τ2.R k u → τ2'.R k u := fun k u hu =>
    ⟨s1 k u (sa k u (sb k u (sc k u (sd k u (se k u hu.1))))), hu.2⟩
  -- both runs end at the same state
  have eq2 : τ2 = τ2' := by
    refine State.ext' (show σe.cur = k from cure) ?_
    funext k' u
    apply propext
    refine ⟨fun hu => sub2 k' u hu, ?_⟩
    rintro ⟨hu0, hle⟩
    obtain ⟨⟨c, hcc, huc⟩, hk⟩ := hu0
    have hp := hcc.1
    obtain ⟨qA, qB, qC, qAC, qCB, qAB⟩ := le_acb h hp (PO.trans hle.1 huc.1)
    have c0 : σ0.R k' c := ⟨⟨c, hcc, PO.refl _⟩, hk⟩
    have u0 : σ0.R k' u := ⟨spec_down ⟨c, hcc, PO.refl _⟩ huc, hk⟩
    obtain ⟨u1, c1⟩ := m1 u0 c0 hp huc qAB
    obtain ⟨ua, ca⟩ := ma u1 c1 hp huc qA
    obtain ⟨ub, cb⟩ := mb ua ca hp huc qB
    obtain ⟨uc, cc⟩ := mc ub cb hp huc qC
    obtain ⟨ud, cd⟩ := md uc cc hp huc qAC
    obtain ⟨ue, _⟩ := me ud cd hp huc qCB
    exact ⟨ue, hle⟩
  -- after the `TxCommit` commitments only, `[A,C,B]` is not legal
  have nonly : ¬ ∃ ρ, SysStep basis2PL σ1 (.commitment [commit A, commit B, commit C]) ρ ∧
      Exposable ρ (o2 A B C) := by
    rintro ⟨ρ, hs, hexp⟩
    have hap : ApplySeq [commit A, commit B, commit C] σ1 ρ := by
      cases hs with | commitment _ _ hap => exact hap
    have lCB : ∀ {o : Outcome T}, (mk [A, C, B] Z) ≼ o → o.lt C B := fun hle =>
      (hle.2.2 C B (by simp [mk_dom]) (by simp [mk_dom])).2 (by rw [lt_ACB hd]; simp)
    have lBC : ∀ {o : Outcome T}, (mk [A, B, C] Z) ≼ o → o.lt B C := fun hle =>
      (hle.2.2 B C (by simp [mk_dom]) (by simp [mk_dom])).2 (by rw [lt_ABC hd]; simp)
    have nle : ¬ o2 (K := K) A B C ≼ full (mk [A, B, C] Z) := fun hle => by
      have := lCB hle.1
      change (mk [A, B, C] Z).lt C B at this
      rw [lt_ABC hd] at this
      simp [hd.ab, hd.ac, hd.bc, Ne.symm hd.ab, Ne.symm hd.ac, Ne.symm hd.bc] at this
    cases hap with
    | cons ha hap =>
    cases hap with
    | cons hb hap =>
    cases hap with
    | cons hc hap =>
    cases hap
    have hcA : CommitOK A (mk [A, B, C] Z) := by simp [CommitOK, mk_X, Z]
    have hcB : CommitOK B (mk [A, B, C] Z) := by simp [CommitOK, mk_X, Z]
    have hcC : CommitOK C (mk [A, B, C] Z) := by simp [CommitOK, mk_X, Z]
    obtain ⟨u, _, hou, hxu⟩ := hexp k _
      (keep_row hc (keep_row hb (keep_row ha rABC1 pABC hcA) pABC hcB) pABC hcC) nle
    exact u.o.irrefl _ (u.o.trans _ _ _ (lCB hou.1) (lBC hxu.1))
  refine ⟨σ1, σe, τ2, τ2', stepC, cur1, keep1, rABC1, nBAC1, r0 pBAC, stepγ, exp2, step2, nonly,
    cstep, eq2, ?_⟩
  exact Lockstep.commitment stepC cur1 s1
    (Lockstep.commitment stepγ cure (fun k u hu => s1 k u (sa k u (sb k u (sc k u
      (sd k u (se k u hu))))))
      (Lockstep.cons step2 cstep rfl (by rw [eq2]) sub2 (Lockstep.nil τ2 τ2')))

end CommitEx
end Partial
end Txn
end CC
