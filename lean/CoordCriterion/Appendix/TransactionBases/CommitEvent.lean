import CoordCriterion.Appendix.TransactionBases.CanonicalExample

/-!
# A 2PL commit event: committing the lock order before any output (§4.3)

Namespace `CC.Txn.Partial.CommitEx`.  The specification of Appendix G
(`Partial.lean`) at the input `{A,B}`, with `rd`, `wr` arbitrary.

When `B` requests a lock that `A` holds, 2PL makes `B` wait.  The wait commits
`B` to serialize after `A` before anything is reported: it is the commit event
`Commit([order(A,B)])`, which applies `order(A,B)` and emits nothing.  Later,
the output event reporting the serial order `[A,B]` applies only `commit(A)` and
`commit(B)`; it needs no further ordering commitment.

* `example_commit_event` — the run `Commit([order(A,B)])`,
  `Out_[commit(A),commit(B)]([A,B])` under `B_2PL`, the canonical run
  `Out_{κ}([A,B])`, and their `Lockstep` pair (Lemma `lem:canonical-equivalent`,
  with the commit event skipped by the canonical run).
-/

namespace CC
namespace Txn
namespace Partial
namespace CommitEx

open Classical

set_option linter.unusedSimpArgs false

open CanonEx (step_close AllP allP_close allP_sub)

variable {T K : Type} {rd wr : T → K → Prop} {A B : T}

/-- The canonical state of `{A,B}`. -/
noncomputable abbrev σAB (rd wr : T → K → Prop) (hab : A ≠ B) : State (spec rd wr false) :=
  canon (spec rd wr false) (pairSet A B hab)

/-- The complete serial order `[A,B]`, no reads reported. -/
noncomputable abbrev oAB (A B : T) : ROut T K := full (mk [A, B] fun _ => False)

section Parts
variable (hab : A ≠ B)
include hab

theorem part_AB : Partitions (pairSet A B hab) (mk [A, B] fun _ => False) := by
  intro t; rw [pairSet_mem, mk_X, mk_dom]; simp

theorem part_BA : Partitions (pairSet A B hab) (mk [B, A] fun _ => False) := by
  intro t; rw [pairSet_mem, mk_X, mk_dom]; simp [or_comm]

theorem part_A_b : Partitions (pairSet A B hab) (mk [A] (· = B)) := by
  intro t; rw [pairSet_mem, mk_X, mk_dom]; simp [or_comm]
  rintro rfl; first | exact hab | exact fun e => hab e.symm | exact Ne.symm hab

/-- An outcome that refines `[A,B]` at an input commits `A` and `B` with `A`
first. -/
theorem le_ab {k : FinSet T} {o : Outcome T} (hp : Partitions k o)
    (hle : mk [A, B] (fun _ => False) ≼ o) :
    CommitOK A o ∧ CommitOK B o ∧ OrderOK A B o := by
  have mA : (mk [A, B] fun _ => False).dom A := by simp [mk_dom]
  have mB : (mk [A, B] fun _ => False).dom B := by simp [mk_dom]
  refine ⟨fun hX => (hp A).2 ⟨hX, hle.2.1 A mA⟩, fun hX => (hp B).2 ⟨hX, hle.2.1 B mB⟩,
    fun hl => ?_⟩
  have := (hle.2.2 B A mB mA).1 hl
  rw [lt2 hab] at this
  exact hab this.2

/-- An outcome at an input containing `{A,B}` that commits `A` and `B` with `A`
first refines `[A,B]`. -/
theorem ab_le {k : FinSet T} {o : Outcome T} (hp : Partitions k o) (hk : pairSet A B hab ≼ k)
    (cA : CommitOK A o) (cB : CommitOK B o) (oAB : OrderOK A B o) :
    mk [A, B] (fun _ => False) ≼ o := by
  have dom : ∀ t, (t = A ∨ t = B) → ¬ o.X t → o.dom t := fun t ht hX =>
    ((hp t).1.1 (hk t ((pairSet_mem t).2 ht))).resolve_left hX
  have dA := dom A (Or.inl rfl) cA
  have dB := dom B (Or.inr rfl) cB
  have hAB : o.lt A B := (o.total A B dA dB hab).resolve_right oAB
  refine ⟨fun _ h => h.elim, fun t ht => ?_, fun a b ha hb => ?_⟩
  · simp only [mk_dom, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with e | e <;> rw [e]
    · exact dA
    · exact dB
  · rw [lt2 hab]
    simp only [mk_dom, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    have nBA : ¬ o.lt B A := oAB
    have irr := o.irrefl
    rcases ha with e | e <;> rcases hb with e' | e' <;> rw [e, e'] <;>
      simp [hAB, nBA, irr, hab, Ne.symm hab]

end Parts

/-- **A 2PL commit event** at `{A,B}` (`rd`, `wr` arbitrary).  Let `σ₀` be the
canonical state of `{A,B}` and `[A,B]` the complete output that commits `A`
then `B` and reports no reads.

1. `B` waits for `A`'s lock: the commit event `Commit([order(A,B)])` is legal
   under `B_2PL` and takes `σ₀` to `σ₁`, which keeps the row `[A,B]` and
   removes `[B,A]`.  It emits nothing.
2. At `σ₁`, `[A,B]` is not yet exposable (rows in which `A` or `B` aborts
   remain), so `Out_ε([A,B])` is not legal there.
3. The output event `Out_[commit(A),commit(B)]([A,B])` is legal under `B_2PL`
   at `σ₁`: reporting the serial order needs no further ordering commitment.
   It ends at `τ₂`.
4. The run `Commit([order(A,B)])`, `Out_[commit(A),commit(B)]([A,B])` is an
   execution under `B_2PL` from `σ₀` and it coordinates.
5. The canonical run `Out_{κ}([A,B])` from `σ₀` ends at `τ₂' = (i, R[out ⪰
   [A,B]])`; the two runs are a `Lockstep` pair (the commit event is matched by
   no canonical event), and they end at the same state: `τ₂ = τ₂'`. -/
theorem example_commit_event (hab : A ≠ B) :
    ∃ σ1 τ2 τ2' : State (spec rd wr false),
      -- 1
      SysStep basis2PL (σAB rd wr hab) (.commit [order A B]) σ1 ∧
      σ1.cur = pairSet A B hab ∧
      σ1.R (pairSet A B hab) (oAB A B) ∧
      ¬ σ1.R (pairSet A B hab) (full (mk [B, A] fun _ => False)) ∧
      -- 2
      ¬ Exposable σ1 (oAB A B) ∧
      -- 3
      SysStep basis2PL σ1 (.output [commit A, commit B] (oAB A B)) τ2 ∧
      -- 4
      SysExec basis2PL (σAB rd wr hab)
        [.commit [order A B], .output [commit A, commit B] (oAB A B)] τ2 ∧
      Coordinates (sp := spec rd wr false)
        [.commit [order A B], .output [commit A, commit B] (oAB A B)] ∧
      -- 5
      CanonStep (σAB rd wr hab) (.output (kappa (σAB rd wr hab) (oAB A B)) (oAB A B)) τ2' ∧
      τ2'.R = outputTable (σAB rd wr hab) (oAB A B) ∧
      Lockstep basis2PL (σAB rd wr hab)
        [.commit [order A B], .output [commit A, commit B] (oAB A B)] τ2
        (σAB rd wr hab) [.output (kappa (σAB rd wr hab) (oAB A B)) (oAB A B)] τ2' ∧
      τ2 = τ2' := by
  let k2 := pairSet A B hab
  let σ0 := σAB rd wr hab
  let Z : T → Prop := fun _ => False
  have hA : k2.1 A := (pairSet_mem A).2 (Or.inl rfl)
  have hB : k2.1 B := (pairSet_mem B).2 (Or.inr rfl)
  have pAB := part_AB hab
  have pBA := part_BA hab
  have pAb := part_A_b hab
  have pAll : Partitions k2 (allAbort k2) := allAbort_part k2
  have r0 : ∀ {o : Outcome T}, Partitions k2 o → σ0.R k2 (full o) := fun hp =>
    Ex.canon_row (full_complete rd wr hp) (PO.refl _)
  -- order facts
  have okAB : OrderOK A B (mk [A, B] Z) := by
    intro hl; rw [lt2 hab] at hl; exact hab hl.2
  have nokBA : ¬ OrderOK A B (mk [B, A] Z) := by
    intro hn; apply hn; rw [lt2 (Ne.symm hab)]; exact ⟨rfl, rfl⟩
  have okAb : OrderOK A B (mk [A] (· = B)) := fun hl => lt1 A _ B A hl
  have okAll : OrderOK A B (allAbort k2) := fun hl => hl
  -- event 1: the commit event `Commit([order(A,B)])`
  obtain ⟨σ1, h1, cur1, nBA1, m1⟩ := step_close (G := fun σ : State (spec rd wr false) =>
      A ≠ B ∧ σ.cur.1 A ∧ σ.cur.1 B) (P := OrderOK A B) (σ := σ0) (k := k2) rfl
    ⟨hab, hA, hB⟩ (r0 pAB) pAB okAB (r0 pBA) pBA nokBA
  have step1 : SysStep basis2PL σ0 (.commit [order A B]) σ1 :=
    SysStep.commit (fun c hc => by
        simp only [List.mem_singleton] at hc; subst hc; exact Or.inl ⟨A, B, rfl⟩)
      (List.cons_ne_nil _ _) (ApplySeq.cons h1 (ApplySeq.nil _))
  have t1 : ∀ {o : Outcome T}, Partitions k2 o → OrderOK A B o → σ1.R k2 (full o) :=
    fun hp hq => (m1 (r0 hp) (r0 hp) hp (PO.refl _) hq).1
  have rAB1 := t1 pAB okAB
  have rAll1 := t1 pAll okAll
  have rAb1 := t1 pAb okAb
  -- 2: `[A,B]` is not exposable at σ1 (the all-abort row remains)
  have nexp : ¬ Exposable σ1 (oAB A B) := by
    intro hex
    obtain ⟨u, hu, hou, hwu⟩ := hex k2 _ rAll1 (fun hle =>
      (hle.1.2.1 A (by show A ∈ [A, B]; simp)).elim)
    obtain ⟨⟨c, ⟨⟨hp, _⟩, _⟩, huc⟩, _⟩ := (order A B).sub _ _ h1 k2 u hu
    exact (hp A).2 ⟨huc.1.1 A (hwu.1.1 A hA), huc.1.2.1 A (hou.1.2.1 A (by show A ∈ [A, B]; simp))⟩
  -- event 2: `Out_[commit(A), commit(B)]([A,B])`
  obtain ⟨σa, ha, cura, _, ma⟩ := step_close (G := fun σ : State (spec rd wr false) => σ.cur.1 A)
    (P := CommitOK A) (σ := σ1) (k := k2) cur1 (by show σ1.cur.1 A; rw [cur1]; exact hA)
    rAB1 pAB (fun h => h) rAll1 pAll (fun hn => hn hA)
  have aAB := (ma rAB1 rAB1 pAB (PO.refl _) (fun h => h)).1
  have aAb := (ma rAb1 rAb1 pAb (PO.refl _) (fun h => hab h)).1
  obtain ⟨σb, hb, curb, _, mb⟩ := step_close (G := fun σ : State (spec rd wr false) => σ.cur.1 B)
    (P := CommitOK B) (σ := σa) (k := k2) cura (by show σa.cur.1 B; rw [cura]; exact hB)
    aAB pAB (fun h => h) aAb pAb (fun hn => hn rfl)
  have bAB := (mb aAB aAB pAB (PO.refl _) (fun h => h)).1
  have sb : ∀ k u, σb.R k u → σa.R k u := (commit B).sub _ _ hb
  have sa : ∀ k u, σa.R k u → σ1.R k u := (commit A).sub _ _ ha
  have s1 : ∀ k u, σ1.R k u → σ0.R k u := (order A B).sub _ _ h1
  have PAB : AllP σb (OrderOK A B) :=
    allP_sub (fun k u h => sa k u (sb k u h)) (allP_close h1)
  have PcA : AllP σb (CommitOK A) := allP_sub sb (allP_close ha)
  have PcB : AllP σb (CommitOK B) := allP_close hb
  have gb : Good σb := good_close hb (good_close ha (good_close h1 (good_canon k2)))
  have ob : σb.R σb.cur (oAB A B) := by rw [curb]; exact bAB
  have expb : Exposable σb (oAB A B) := by
    intro k w hw _
    obtain ⟨c, hc, hp, hle⟩ := gb.2 k w hw
    have hk : k2 ≼ k := curb ▸ σb.above _ _ hc
    exact ⟨c, hc, ⟨ab_le hab hp hk (PcA k c hc hp) (PcB k c hc hp) (PAB k c hc hp),
      fun _ _ _ e => by cases e⟩, hle⟩
  let τ2 := outState σb (oAB A B) ob
  have step2 : SysStep basis2PL σ1 (.output [commit A, commit B] (oAB A B)) τ2 := by
    refine SysStep.output (fun c hc => ?_) (ApplySeq.cons ha (ApplySeq.cons hb (ApplySeq.nil _)))
      ob expb (curb.trans cur1.symm) rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact Or.inr (Or.inl ⟨A, rfl⟩)
    · exact Or.inr (Or.inl ⟨B, rfl⟩)
  -- the canonical run
  have o0 : σ0.R σ0.cur (oAB A B) := r0 pAB
  let τ2' := outState σ0 (oAB A B) o0
  have cstep : CanonStep σ0 (.output (kappa σ0 (oAB A B)) (oAB A B)) τ2' :=
    ⟨canonical_support σ0 (oAB A B) o0, ⟨(fun _ _ e => by cases e; rfl), fun _ e => by cases e⟩⟩
  have sub2 : ∀ k u, τ2.R k u → τ2'.R k u := fun k u hu =>
    ⟨s1 k u (sa k u (sb k u hu.1)), hu.2⟩
  -- both runs end at the same state
  have eq2 : τ2 = τ2' := by
    refine State.ext' (show σb.cur = k2 from curb) ?_
    funext k u
    apply propext
    refine ⟨fun hu => sub2 k u hu, ?_⟩
    rintro ⟨hu0, hle⟩
    obtain ⟨⟨c, ⟨hcc, _⟩, huc⟩, hk⟩ := hu0
    have hp := hcc.1
    obtain ⟨qA, qB, qAB⟩ := le_ab hab hp (PO.trans hle.1 huc.1)
    have c0 : σ0.R k c := Ex.canon_row hcc hk
    have u0 : σ0.R k u := ⟨spec_down ⟨c, ⟨hcc, fun h => by cases h⟩, PO.refl _⟩ huc, hk⟩
    obtain ⟨u1, c1⟩ := m1 u0 c0 hp huc qAB
    obtain ⟨ua, ca⟩ := ma u1 c1 hp huc qA
    obtain ⟨ub, _⟩ := mb ua ca hp huc qB
    exact ⟨ub, hle⟩
  refine ⟨σ1, τ2, τ2', step1, cur1, rAB1, nBA1, nexp, step2,
    SysExec.cons step1 (SysExec.cons step2 (SysExec.nil _)),
    Or.inr ⟨_, List.mem_cons_self⟩, cstep, rfl, ?_, eq2⟩
  exact Lockstep.commit step1 cur1 s1
    (Lockstep.cons step2 cstep rfl (by rw [eq2]) sub2 (Lockstep.nil τ2 τ2'))

end CommitEx
end Partial
end Txn
end CC
