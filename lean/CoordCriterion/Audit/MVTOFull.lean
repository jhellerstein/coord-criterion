/-
# Audit F (part 4): Appendix `app:cc-bases`, full specification with reads

Checks the rewritten appendix, whose specification is the read-result
specification `CC.AuditF.Reads.readSpec` (outputs `(L,X,ρ)`).  Every claim of
the appendix that is not definitional is re-proved here for that
specification (and for its abort-free variant), rather than for the simpler
`CC.AuditF.txnSpec`.

* `abortFreeFull` — the abort-free variant: the same rows with `X = ∅`.
* `full_ab_ba_rows`, `full_no_common_refinement`, `full_not_liftedMono`,
  `abortFreeFull_not_liftedMono` — `([A,B],∅,∅)` and `([B,A],∅,∅)` are
  permitted at `{A,B}` and have no common refinement: neither specification is
  monotone.
* `full_comparable_same_LX`, `abortFreeFull_comparable_same_LX`,
  `abortFreeFull_stable_lift` — comparable permitted outputs at one input have
  the same `(L,X)`, so every condition on `(L,X)` gives a commitment
  (`CC.AuditF.Reads.filterCS`).
* `orderAFR`, …, `basis2PL_R`, `basisMVTO_R` (existing), `basis2PL_AF`.
* `deadlock_state_R`, `deadlock_forces_abort_R` — 2PL deadlock.
* `abortFree_order_blocks_R`, `abortFree_order_blocks_forever_R` — abort-free
  deadlock: `order(B,A)` is never defined again.
* `orderP_noabort`, `stampP_first_noabort` — Fig. `fig:cc-commitments` (h),(i)
  on rows without aborts.
* `mvto_forced_abort` — the MVTO abort is required by the specification
  (wrapper around `CC.AuditF.Reads.forced_abort`).
-/
import CoordCriterion.Audit.MVTOReads

namespace CC
namespace AuditF
namespace Full

open Reads

variable {T K : Type}

section Spec
variable (rd wr : T → K → Prop)

/-- **The abort-free specification with reads**: the permitted rows with `X = ∅`. -/
def abortFreeFull : Spec (FinSet T) (ROut T K) where
  S k r := Permitted rd wr k r ∧ ∀ t, ¬ r.o.X t
  total k := by
    classical
    obtain ⟨l, _, hl⟩ := k.2
    refine ⟨⟨listOrder l, fun _ _ => none⟩, ⟨fun t => ⟨?_, fun h => h.1⟩,
      fun _ _ _ h => by cases h⟩, fun _ h => h⟩
    show k.1 t ↔ False ∨ t ∈ l
    rw [hl t]
    exact ⟨Or.inr, fun h => h.elim False.elim id⟩

/-- `(L, X, ∅)`. -/
def noReads (o : Outcome T) : ROut T K := ⟨o, fun _ _ => none⟩

theorem full_ab_ba_rows {A B : T} (h : A ≠ B) :
    (abortFreeFull rd wr).S (pairSet A B h) (noReads (K := K) (ordPair A B h)) ∧
    (abortFreeFull rd wr).S (pairSet A B h) (noReads (K := K) (ordPair B A (Ne.symm h))) :=
  ⟨⟨⟨(ordPair_row h).1, fun _ _ _ h => by cases h⟩, fun _ h => h⟩,
   ⟨⟨(ordPair_row' h).1, fun _ _ _ h => by cases h⟩, fun _ h => h⟩⟩

/-- `([A,B],∅,∅)` and `([B,A],∅,∅)` have no common refinement. -/
theorem full_no_common_refinement {A B : T} (h : A ≠ B) :
    ¬ ∃ u : ROut T K, noReads (ordPair A B h) ≼ u ∧ noReads (ordPair B A (Ne.symm h)) ≼ u :=
  fun ⟨u, h1, h2⟩ => ab_ba_no_common_refinement h ⟨u.o, h1.1, h2.1⟩

/-- **The specification is not monotone.** -/
theorem full_not_liftedMono {A B : T} (h : A ≠ B) :
    ¬ (readSpec (K := K) rd wr).DirectedOutputs ∧ ¬ (readSpec (K := K) rd wr).LiftedMono :=
  not_directed_of (sp := readSpec rd wr) (full_ab_ba_rows rd wr h).1.1
    (full_ab_ba_rows rd wr h).2.1 (full_no_common_refinement h)

/-- Nor is the abort-free one. -/
theorem abortFreeFull_not_liftedMono {A B : T} (h : A ≠ B) :
    ¬ (abortFreeFull (K := K) rd wr).DirectedOutputs ∧
      ¬ (abortFreeFull (K := K) rd wr).LiftedMono :=
  not_directed_of (sp := abortFreeFull rd wr) (full_ab_ba_rows rd wr h).1
    (full_ab_ba_rows rd wr h).2 (full_no_common_refinement h)

/-- Two permitted outputs at one input, one refining the other, have the same
serial order and abort set. -/
theorem full_comparable_same_LX {k : FinSet T} {u w : ROut T K}
    (hu : (readSpec rd wr).S k u) (hw : (readSpec rd wr).S k w) (h : u ≼ w) : u.o = w.o :=
  comparable_same_LX rd wr hu hw h

theorem abortFreeFull_comparable_same_LX {k : FinSet T} {u w : ROut T K}
    (hu : (abortFreeFull rd wr).S k u) (hw : (abortFreeFull rd wr).S k w) (h : u ≼ w) :
    u.o = w.o :=
  comparable_same_LX rd wr hu.1 hw.1 h

theorem abortFreeFull_stable_lift (P : FinSet T → Outcome T → Prop) :
    Stable (abortFreeFull rd wr) (lift (K := K) P) := by
  intro k u w hu hw h
  show P k u.o ↔ P k w.o
  rw [abortFreeFull_comparable_same_LX rd wr hu hw h]

end Spec

/-! ### Commitments and bases -/

section Bases
variable (rd wr : T → K → Prop)

/-- `B_2PL = {order, commit, abort}` for the specification with reads. -/
def basis2PL_R : Basis (readSpec rd wr) := fun c =>
  (∃ A B, c = orderR rd wr A B) ∨ (∃ A, c = commitR rd wr A) ∨ (∃ A, c = abortR rd wr A)

noncomputable def orderAFR (A B : T) : Commitment (abortFreeFull rd wr) :=
  filterCS (fun σ => A ≠ B ∧ σ.cur.1 A ∧ σ.cur.1 B) (lift (orderP A B))
    (abortFreeFull_stable_lift rd wr _)
noncomputable def commitAFR (A : T) : Commitment (abortFreeFull rd wr) :=
  filterCS (fun _ => True) (lift (commitP A)) (abortFreeFull_stable_lift rd wr _)
noncomputable def abortAFR (A : T) : Commitment (abortFreeFull rd wr) :=
  filterCS (fun _ => True) (lift (abortP A)) (abortFreeFull_stable_lift rd wr _)

/-- `B_2PL` for the abort-free specification with reads. -/
def basis2PL_AF : Basis (abortFreeFull rd wr) := fun c =>
  (∃ A B, c = orderAFR rd wr A B) ∨ (∃ A, c = commitAFR rd wr A) ∨ (∃ A, c = abortAFR rd wr A)

end Bases

/-! ### 2PL deadlock -/

section Deadlock
variable {rd wr : T → K → Prop}

/-- **Deadlock.**  After `order(A,B)` and then `order(B,A)`, the rows left, at
every input, are exactly the rows of `R` with `A ∈ X` or `B ∈ X`. -/
theorem deadlock_state_R {A B : T} {σ σ1 σ2 : State (readSpec (K := K) rd wr)}
    (h1 : (orderR rd wr A B).app σ = some σ1) (h2 : (orderR rd wr B A).app σ1 = some σ2) :
    σ2.cur = σ.cur ∧ ∀ k u, σ2.R k u ↔ σ.R k u ∧ (u.o.X A ∨ u.o.X B) := by
  obtain ⟨_, c1, r1⟩ := filterCS_app_iff.1 h1
  obtain ⟨_, c2, r2⟩ := filterCS_app_iff.1 h2
  refine ⟨c2.trans c1, fun k u => ?_⟩
  rw [r2, r1, ← deadlock_rows k u.o A B, and_assoc]
  rfl

/-- After the deadlock every row of every later state aborts `A` or `B`. -/
theorem deadlock_forces_abort_R {A B : T} {σ σ1 σ2 : State (readSpec (K := K) rd wr)}
    (h1 : (orderR rd wr A B).app σ = some σ1) (h2 : (orderR rd wr B A).app σ1 = some σ2)
    (τ : State (readSpec rd wr)) (hτ : ∀ k u, τ.R k u → σ2.R k u) :
    ∀ k u, τ.R k u → u.o.X A ∨ u.o.X B :=
  fun k u h => (((deadlock_state_R h1 h2).2 k u).1 (hτ k u h)).2

/-- **Abort-free deadlock.**  Once `order(A,B)` has been applied, `order(B,A)`
is undefined at every state whose table is contained in the result. -/
theorem abortFree_order_blocks_R {A B : T} {σ σ1 : State (abortFreeFull (K := K) rd wr)}
    (h : (orderAFR rd wr A B).app σ = some σ1) (τ : State (abortFreeFull rd wr))
    (hτ : ∀ k u, τ.R k u → σ1.R k u) : (orderAFR rd wr B A).app τ = none := by
  obtain ⟨_, _, r1⟩ := filterCS_app_iff.1 h
  show filterApp _ _ τ = none
  rw [filterApp_none]
  rintro ⟨_, ⟨o, ho, hp⟩, _⟩
  have hab : orderP A B _ o.o := ((r1 _ _).1 (hτ _ _ ho)).2
  have hX := (τ.sub _ _ ho).2
  have hba : orderP B A _ o.o := hp
  rcases hab with h | h | hab
  · exact hX _ h
  · exact hX _ h
  rcases hba with h | h | hba
  · exact hX _ h
  · exact hX _ h
  · exact o.o.irrefl _ (o.o.trans _ _ _ hab hba)

/-- ... at every state any later execution reaches, under any basis. -/
theorem abortFree_order_blocks_forever_R {A B : T}
    {σ σ1 : State (abortFreeFull (K := K) rd wr)}
    (h : (orderAFR rd wr A B).app σ = some σ1) (Bs : Basis (abortFreeFull rd wr))
    {es : List (SEvent (abortFreeFull rd wr))} {τ : State (abortFreeFull rd wr)}
    (hx : SysExec Bs σ1 es τ) : (orderAFR rd wr B A).app τ = none :=
  abortFree_order_blocks_R h τ hx.sub

end Deadlock

/-! ### Figure `fig:cc-commitments` on rows without aborts -/

section Figures
variable {rd wr : T → K → Prop}

/-- Fig. (h): on a permitted row with no aborts, `order(A,B)` holds iff `A`
precedes `B`. -/
theorem orderP_noabort {k : FinSet T} {r : ROut T K} (h : (readSpec rd wr).S k r)
    (hX : ∀ t, ¬ r.o.X t) (A B : T) : orderP A B k r.o ↔ r.o.lt A B :=
  orderP_abortFree ⟨h.1, hX⟩ A B

/-- Fig. (i): on a permitted row with no aborts, `stamp(B)` with `Z = ∅` holds
iff `B` precedes every other transaction. -/
theorem stampP_first_noabort {k : FinSet T} {r : ROut T K} (h : (readSpec rd wr).S k r)
    (hX : ∀ t, ¬ r.o.X t) (B : T) :
    stampP B (fun _ => False) k r.o ↔ ∀ D, k.1 D → D ≠ B → r.o.lt B D :=
  stampP_first_abortFree ⟨h.1, hX⟩ B

end Figures

/-! ### MVTO: the abort is required -/

/-- **The MVTO abort.**  `A` writes `x`; `B` was stamped after `A` (`A ∈ Z_B`);
an output event reports that `B` read `x` from version `v`, where `v` is the
initial version or the write of a transaction stamped before `A` (`∈ Z_A`).
Then that output aborts `A`, and so does every row left afterwards. -/
theorem mvto_forced_abort {rd wr : T → K → Prop} {Bs : Basis (readSpec rd wr)} {A B : T}
    {ZA ZB : T → Prop} {x : K} {v : Option T} {σ σ1 σ1' σ2 τ0 τ : State (readSpec rd wr)}
    {es1 es2 : List (SEvent (readSpec rd wr))} {γ : List (Commitment (readSpec rd wr))}
    {r : ROut T K}
    (h1 : (stampR rd wr A ZA).app σ = some σ1) (hx1 : SysExec Bs σ1 es1 σ1')
    (h2 : (stampR rd wr B ZB).app σ1' = some σ2) (hx2 : SysExec Bs σ2 es2 τ0)
    (hout : SysStep Bs τ0 (.output γ r) τ)
    (hAB : ZB A) (hwA : wr A x) (hv : ∀ W, v = some W → ZA W) (hρ : r.ρ B x = some v) :
    r.o.X A ∧ ∀ k u, τ.R k u → u.o.X A :=
  forced_abort h1 hx1 h2 hx2 hout hAB hwA hv hρ

end Full
end AuditF
end CC
