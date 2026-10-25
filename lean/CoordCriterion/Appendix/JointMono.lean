import CoordCriterion.Appendix.Guarded

/-!
# Jointly monotone composites (Section 5, Appendix D)

Namespace `CC.Joint`.  When is a composite `𝒮₂ ∘ 𝒮₁` monotone although a stage
is not, and what does that mean for running the pipeline without
commitment?  Three mechanisms, and the limit of the third.

1. **Filtering.**  `𝒮₁` never produces the inputs on which `𝒮₂` is not
   monotone.
   * `CEOn`, `ceOn_iff_restrictTo` (in `Appendix/Guarded.lean`) — `𝒮₂`
     satisfies the common-expansion condition on a set `D` of middle values
     (equivalently: `𝒮₂` restricted to `D` is Lifted-Monotone).
   * `seq_liftedMono_on` — if `𝒮₁` is Lifted-Monotone with outputs in `D`
     and `𝒮₂` is Lifted-Monotone on `D`, the composite is Lifted-Monotone.
     No closure condition on `D` is needed.
   * Instance `threshold`: `𝒮₁ = n ↦ min n 9`, `𝒮₂ = n ↦ [n < 10]`.  The
     store is not Lifted-Monotone, its empty-basis system cannot emit at all,
     the composite is Lifted-Monotone, and the pipeline is proper
     (`Guard.Proper`).
2. **Cancellation by re-ordering `M`.**  The composite's table does not depend
   on the order of `M` (`seq_under`), nor on a re-encoding of `M` that the
   downstream decodes (`reorder_seq`).  So stages that are Lifted-Monotone
   under another order on `M` (`seq_liftedMono_reorder`), or after a
   re-encoding (`seq_liftedMono_reencode`), have a Lifted-Monotone composite.
   * Boolean toggle (`bool_toggle`, the paper's example): with `false ≼ true`
     on the middle both negation stages violate monotonicity and the first
     cannot emit at `false` without commitment (`toggle_exposable_iff`,
     `toggle_empty_basis`); with the reversed order on the middle both stages
     are monotone; the composite is the identity either way.
   * Double complement (`double_complement`; no longer cited in the paper,
     which uses the boolean toggle): with `⊆` on the middle sets both
     complement stages violate monotonicity and the first can emit, without
     commitment, only the empty set (`compl_exposable_iff`,
     `compl_empty_basis`); with `⊇` on the middle both stages are monotone; the
     composite is the identity either way.
   * Constant store (`constant_store_reorder`): declaring `x ≼ y` makes the
     non-monotone `anyS` Lifted-Monotone; the composite is unchanged.
3. **Characterization (functional stages).**
   * `cf_upstream_monotone` — if the upstream `graph f` can emit at every
     canonical state under the empty basis, `f` is monotone.
   * `preorder_factorization` — `g ∘ f` is monotone iff some *preorder* on
     `M` makes both `f` and `g` monotone (pull back `O`'s order through `g`).
   * `injective_characterization` — for injective `g`, the same with a
     partial order.
   * `no_order_counterexample` — in general no partial order on `M` works:
     the composite is Lifted-Monotone (constant) but under every partial order
     on `M` the upstream is not, and its empty-basis system stalls at some
       canonical state.
     * `merge_needed` — any re-encoding of the middle that makes the upstream
       of the counterexample monotone merges its two middle values.
-/

namespace CC
namespace Joint

open Comp Guard Classical

/-! ### Basics -/

section Basics
variable {I M : Type} [PO I] [PO M]

/-- Under the empty basis an output event applies no commitment, so it emits
an exposable output of the current fiber. -/
theorem empty_step {sq : Spec I M} {σ τ : State sq} {γ : List (Commitment sq)} {o : M}
    (h : SysStep (fun _ => False) σ (.output γ o) τ) :
    γ = [] ∧ σ.R σ.cur o ∧ Exposable σ o := by
  cases γ with
  | cons c _ =>
    cases h with
    | output hb _ _ _ _ _ => exact (hb c List.mem_cons_self).elim
  | nil =>
    obtain ⟨ho, he, _, _⟩ := eps_step_iff.1 h
    exact ⟨rfl, ho, he⟩

/-- **Exposure at a canonical state of a function.**  Emitting `f i` at
`σ(i)` is commitment-free iff `f i ≼ f k` for every `k ⪰ i`. -/
theorem graph_canon_exposable_iff (f : I → M) (i : I) :
    Exposable (canon (graph f) i) (f i) ↔ ∀ k, i ≼ k → f i ≼ f k := by
  constructor
  · intro hE k hk
    refine Classical.byContradiction fun hn => ?_
    obtain ⟨u, hu, h1, _⟩ := hE k (f k) ⟨rfl, hk⟩ hn
    have e : u = f k := hu.1
    rw [e] at h1
    exact hn h1
  · intro h k x hx hn
    have e : x = f k := hx.1
    rw [e] at hn
    exact absurd (h k hx.2) hn

end Basics

/-! ### 1. Filtering -/

section Filter
variable {I M O : Type} [PO I] [PO M] [PO O]

/-- **Filtering composition.**  If `𝒮₁` satisfies Lifted Monotonicity with all
its outputs in `D`, and `𝒮₂` satisfies Lifted Monotonicity on `D`, then
`𝒮₂ ∘ 𝒮₁` satisfies Lifted Monotonicity.  (`D` needs no closure property;
`D = Img 𝒮₁` is the weakest choice, `seq_liftedMono_img`.) -/
theorem seq_liftedMono_on {sp1 : Spec I M} {sp2 : Spec M O} {D : M → Prop}
    (h1 : sp1.LiftedMono) (hD : ∀ i m, sp1.S i m → D m) (h2 : CEOn sp2 D) :
    (seq sp1 sp2).LiftedMono := by
  have h1 := (liftedMono_iff_commonExpansion _).1 h1
  apply (liftedMono_iff_commonExpansion _).2
  intro rows hrows j hj
  obtain ⟨L, hL1, hL2⟩ := choose_list (fun (r : I × O) m => sp1.S r.1 m ∧ sp2.S m r.2)
    rows hrows
  obtain ⟨m, hm, hmall⟩ := h1 (L.map fun p => (p.1.1, p.2))
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact (hL2 p hp).2.1) j
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact hj _ (hL2 p hp).1)
  obtain ⟨u, hu, huall⟩ := h2 (L.map fun p => (p.2, p.1.2))
    (by
      intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
      exact ⟨hD _ _ (hL2 p hp).2.1, (hL2 p hp).2.2⟩)
    m (hD _ _ hm)
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        exact hmall (p.1.1, p.2) (List.mem_map.2 ⟨p, hp, rfl⟩))
  refine ⟨u, ⟨m, hm, hu⟩, fun r hr => ?_⟩
  obtain ⟨b, hb⟩ := hL1 r hr
  exact huall (b, r.2) (List.mem_map.2 ⟨(r, b), hb, rfl⟩)

theorem seq_liftedMono_img {sp1 : Spec I M} {sp2 : Spec M O}
    (h1 : sp1.LiftedMono) (h2 : CEOn sp2 (Img sp1)) : (seq sp1 sp2).LiftedMono :=
  seq_liftedMono_on h1 (fun i _ h => ⟨i, h⟩) h2

end Filter

/-! #### Instance: a threshold store behind a capped counter -/

section Threshold

/-- Counts, ordered by `≤`. -/
instance instPONat : PO Nat where
  le a b := a ≤ b
  refl := Nat.le_refl
  trans := Nat.le_trans
  antisymm := Nat.le_antisymm

open Dist (B2)

/-- The upstream: a counter capped at `9`. -/
def cap (n : Nat) : Nat := min n 9

/-- The store: "is the count below `10`?", outputs ordered discretely. -/
def below (n : Nat) : B2 := decide (n < 10)

/-- Inputs the store would have to seal. -/
def Big (n : Nat) : Prop := 10 ≤ n

def up : Spec Nat Nat := graph cap
def thr : Spec Nat B2 := graph below

theorem cap_monotone : Monotone cap := by
  intro x y h
  have h' : x ≤ y := h
  show min x 9 ≤ min y 9
  omega

theorem below_eq {a b : Nat} (ha : a ≤ 9) (hb : b ≤ 9) : below a = below b := by
  have ha' : a < 10 := by omega
  have hb' : b < 10 := by omega
  show decide (a < 10) = decide (b < 10)
  simp [ha', hb']

theorem up_img {i m : Nat} (h : up.S i m) : ¬ Big m := by
  have e : m = min i 9 := h
  unfold Big; omega

theorem thr_ceOn : CEOn thr fun m => ¬ Big m :=
  graph_ceOn fun a b ha hb _ => by
    unfold Big at ha hb
    exact below_eq (by omega) (by omega)

theorem below_9_10 : ¬ (below 9 ≼ below 10) := by
  intro h
  have h' : below 9 = below 10 := h
  simp [below] at h'

/-- **Threshold store behind a capped counter.**  (1) The store is not
Lifted-Monotone; (2) under the empty basis it cannot emit at any canonical
state below `10`; (3) the composite is Lifted-Monotone; (4) the pipeline is
proper: the store restricted to the counter's outputs needs no commitment. -/
theorem threshold :
    ¬ thr.LiftedMono ∧
    (∀ m, m ≤ 9 → ∀ γ o τ, ¬ SysStep (fun _ => False) (canon thr m) (.output γ o) τ) ∧
    (seq up thr).LiftedMono ∧
    Proper up thr := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact below_9_10 ((graph_liftedMono_iff below).1 h 9 10 (show 9 ≤ 10 by omega))
  · intro m hm γ o τ hs
    obtain ⟨_, ho, he⟩ := empty_step hs
    have e : o = below m := ho.1
    subst e
    have := (graph_canon_exposable_iff below m).1 he 10 (show m ≤ 10 by omega)
    rw [below_eq hm (show 9 ≤ 9 by omega)] at this
    exact below_9_10 this
  · exact seq_liftedMono_on ((graph_liftedMono_iff _).2 cap_monotone)
      (fun _ _ h => up_img h) thr_ceOn
  · exact proper_iff.2 (ceOn_mono (fun _ ⟨_, h⟩ => up_img h) thr_ceOn)

end Threshold

/-! ### 2. Cancellation by re-ordering the middle -/

section Reorder
variable {I M M' O : Type} [PO I] [PO M] [PO M'] [PO O]

/-- `𝒮₁` with its outputs renamed by `e` (into a differently ordered `M'`). -/
def pushOut (sp : Spec I M) (e : M → M') : Spec I M' :=
  ⟨fun i m' => ∃ m, sp.S i m ∧ m' = e m, fun i => let ⟨m, h⟩ := sp.total i; ⟨e m, m, h, rfl⟩⟩

/-- `𝒮₂` read on a renamed middle. -/
def pullIn (sp : Spec M O) (e' : M' → M) : Spec M' O :=
  ⟨fun m' o => sp.S (e' m') o, fun m' => sp.total (e' m')⟩

/-- **Re-ordering the middle does not change the composite.**  For a renaming
`e : M → M'` with left inverse `e'`, `pullIn 𝒮₂ e' ∘ pushOut 𝒮₁ e = 𝒮₂ ∘ 𝒮₁`,
whatever the orders on `M` and `M'`. -/
theorem reorder_seq (sp1 : Spec I M) (sp2 : Spec M O) (e : M → M') (e' : M' → M)
    (h : ∀ m, e' (e m) = m) : seq (pushOut sp1 e) (pullIn sp2 e') = seq sp1 sp2 := by
  apply Spec.ext'
  funext i o
  apply propext
  show (∃ m', (∃ m, sp1.S i m ∧ m' = e m) ∧ sp2.S (e' m') o) ↔ ∃ m, sp1.S i m ∧ sp2.S m o
  constructor
  · rintro ⟨_, ⟨m, h1, rfl⟩, h2⟩
    rw [h m] at h2
    exact ⟨m, h1, h2⟩
  · rintro ⟨m, h1, h2⟩
    exact ⟨e m, ⟨m, h1, rfl⟩, by rw [h m]; exact h2⟩

/-- **Lifted Monotonicity through a re-encoding.**  If the re-encoded stages
`pushOut 𝒮₁ e` and `pullIn 𝒮₂ e'` (with `e' ∘ e = id`) satisfy Lifted
Monotonicity under the order on `M'`, then so does `𝒮₂ ∘ 𝒮₁`: by Lemma
`lem:composition` on `M'` and `reorder_seq`. -/
theorem seq_liftedMono_reencode {sp1 : Spec I M} {sp2 : Spec M O} {e : M → M'} {e' : M' → M}
    (h : ∀ m, e' (e m) = m) (h1 : (pushOut sp1 e).LiftedMono) (h2 : (pullIn sp2 e').LiftedMono) :
    (seq sp1 sp2).LiftedMono :=
  reorder_seq sp1 sp2 e e' h ▸ seq_liftedMono h1 h2

theorem pushOut_graph (f : I → M) (e : M → M') : pushOut (graph f) e = graph (e ∘ f) := by
  apply Spec.ext'
  funext i m'
  apply propext
  show (∃ m, m = f i ∧ m' = e m) ↔ m' = e (f i)
  exact ⟨fun ⟨_, h1, h2⟩ => h1 ▸ h2, fun h => ⟨f i, rfl, h⟩⟩

theorem pullIn_graph (g : M → O) (e' : M' → M) : pullIn (graph g) e' = graph (g ∘ e') := rfl

end Reorder

/-! #### Another order on the same middle -/

section ReorderSame
variable {I M O : Type} [PO I] [PO O]

/-! The given order on `M` is the implicit `instM`; the other order `inst` is
passed explicitly.  All instance arguments on `M` are written out, since an
explicit `inst : PO M` would otherwise be picked up by instance resolution. -/

/-- `𝒮₁` with the same table, its outputs ordered by `inst` instead. -/
def underOut {instM : PO M} (inst : PO M) (sp : @Spec I M _ instM) : @Spec I M _ inst :=
  @Spec.mk I M _ inst (@Spec.S I M _ instM sp) (@Spec.total I M _ instM sp)

/-- `𝒮₂` with the same table, its inputs ordered by `inst` instead. -/
def underIn {instM : PO M} (inst : PO M) (sp : @Spec M O instM _) : @Spec M O inst _ :=
  @Spec.mk M O inst _ (@Spec.S M O instM _ sp) (@Spec.total M O instM _ sp)

/-- **The composite does not depend on the order on `M`.**  The composite of
the two stages read under `inst` is the composite under the given order
`instM` (the type `Spec I O` does not mention `M` at all). -/
theorem seq_under {instM : PO M} (inst : PO M) (sp1 : @Spec I M _ instM)
    (sp2 : @Spec M O instM _) :
    @seq I M O _ inst _ (underOut inst sp1) (underIn inst sp2) = @seq I M O _ instM _ sp1 sp2 :=
  rfl

/-- **Case (3) of `prop:joint-monotone`.**  If, under some partial order
`inst` on `M` (possibly other than the given `instM`), both stages satisfy
Lifted Monotonicity, then `𝒮₂ ∘ 𝒮₁` satisfies Lifted Monotonicity under the
given order: Lemma `lem:composition` under `inst`, and `seq_under`. -/
theorem seq_liftedMono_reorder {instM : PO M} {sp1 : @Spec I M _ instM}
    {sp2 : @Spec M O instM _} (inst : PO M)
    (h1 : @Spec.LiftedMono I M _ inst (underOut inst sp1))
    (h2 : @Spec.LiftedMono M O inst _ (underIn inst sp2)) :
    (@seq I M O _ instM _ sp1 sp2).LiftedMono :=
  seq_under inst sp1 sp2 ▸ @seq_liftedMono I M O _ inst _ _ _ h1 h2

end ReorderSame

/-! #### Double complement -/

section DoubleComplement

/-- Subsets of `U`, ordered by inclusion. -/
structure PSet (U : Type) where
  mem : U → Prop

theorem PSet.ext' {U : Type} {X Y : PSet U} (h : ∀ u, X.mem u ↔ Y.mem u) : X = Y := by
  cases X; cases Y
  exact congrArg PSet.mk (funext fun u => propext (h u))

instance (U : Type) : PO (PSet U) where
  le X Y := ∀ u, X.mem u → Y.mem u
  refl _ _ h := h
  trans h1 h2 u h := h2 u (h1 u h)
  antisymm h1 h2 := PSet.ext' fun u => ⟨h1 u, h2 u⟩

/-- The reversed order. -/
structure Rev (α : Type) where
  val : α

instance {α : Type} [PO α] : PO (Rev α) where
  le a b := b.val ≼ a.val
  refl a := PO.refl a.val
  trans h1 h2 := PO.trans h2 h1
  antisymm {a b} h1 h2 := by
    cases a; cases b
    exact congrArg Rev.mk (PO.antisymm h2 h1)

variable {U : Type}

/-- Complement. -/
def compl (X : PSet U) : PSet U := ⟨fun u => ¬ X.mem u⟩

theorem compl_compl (X : PSet U) : compl (compl X) = X :=
  PSet.ext' fun _ => Classical.not_not

theorem compl_not_monotone [Nonempty U] : ¬ Monotone (compl (U := U)) := by
  intro h
  obtain ⟨u⟩ := (inferInstance : Nonempty U)
  exact h ⟨fun _ => False⟩ ⟨fun _ => True⟩ (fun _ h => h.elim) u (fun h => h) trivial

/-- **The commitment-free complement stage emits only `∅`.**  Under `⊆` on
the middle, emitting `Uᶜ ∖ X` at `σ(X)` without commitment is possible only
for `X = U`. -/
theorem compl_exposable_iff (X : PSet U) :
    Exposable (canon (graph compl) X) (compl X) ↔ ∀ u, X.mem u := by
  rw [graph_canon_exposable_iff]
  constructor
  · intro h u
    exact Classical.byContradiction fun hu =>
      h ⟨fun _ => True⟩ (fun _ _ => trivial) u hu trivial
  · intro hX K _ u hu
    exact absurd (hX u) hu

theorem compl_empty_basis {X : PSet U} {γ : List (Commitment (graph (compl (U := U))))}
    {o : PSet U} {τ : State (graph compl)}
    (h : SysStep (fun _ => False) (canon (graph compl) X) (.output γ o) τ) : ∀ u, ¬ o.mem u := by
  obtain ⟨_, ho, he⟩ := empty_step h
  have e : o = compl X := ho.1
  subst e
  intro u hu
  exact hu ((compl_exposable_iff X).1 he u)

/-- **Double complement.**  (1) With `⊆` on the middle, the complement stage
`𝒮₁ = 𝒮₂ = graph compl` is not Lifted-Monotone; (2) the composite is the
identity, which is Lifted-Monotone; (3) with `⊇` on the middle (`Rev`), both
re-indexed stages are Lifted-Monotone, and (4) the composite is the same
specification. -/
theorem double_complement [Nonempty U] :
    ¬ (graph (compl (U := U))).LiftedMono ∧
    seq (graph (compl (U := U))) (graph compl) = graph id ∧
    (graph (id : PSet U → PSet U)).LiftedMono ∧
    (pushOut (graph (compl (U := U))) Rev.mk).LiftedMono ∧
    (pullIn (graph (compl (U := U))) Rev.val).LiftedMono ∧
    seq (pushOut (graph (compl (U := U))) Rev.mk) (pullIn (graph compl) Rev.val) =
      seq (graph compl) (graph compl) := by
  refine ⟨fun h => compl_not_monotone ((graph_liftedMono_iff _).1 h), ?_,
    (graph_liftedMono_iff _).2 fun _ _ h => h, ?_, ?_, reorder_seq _ _ _ _ fun _ => rfl⟩
  · rw [seq_graph]
    congr 1
    funext X
    exact compl_compl X
  · rw [pushOut_graph, graph_liftedMono_iff]
    intro X Y h u hu hX
    exact hu (h u hX)
  · rw [pullIn_graph, graph_liftedMono_iff]
    intro Z Z' h u hu hZ
    exact hu (h u hZ)

end DoubleComplement

/-! #### Boolean toggle -/

section BoolToggle

/-- The booleans ordered with `false` below `true`. -/
instance boolPO : PO Bool where
  le a b := a = true → b = true
  refl _ h := h
  trans h1 h2 h := h2 (h1 h)
  antisymm {a b} h1 h2 := by cases a <;> cases b <;> simp_all

theorem not_not_monotone : ¬ Monotone not :=
  fun h => Bool.noConfusion (h false true (fun _ => rfl) rfl)

/-- **The commitment-free toggle stage emits only at `true`.**  Under
`false ≼ true` on the middle, emitting `!b` at `σ(b)` without commitment is
possible only for `b = true`. -/
theorem toggle_exposable_iff (b : Bool) :
    Exposable (canon (graph not) b) (!b) ↔ b = true := by
  rw [graph_canon_exposable_iff]
  cases b
  · exact ⟨fun h => Bool.noConfusion (h true (fun _ => rfl) rfl), fun h => Bool.noConfusion h⟩
  · exact ⟨fun _ => rfl, fun _ k hk => by
      cases k
      · exact Bool.noConfusion (hk rfl)
      · exact fun h => h⟩

/-- At input `false` the toggle stage cannot emit under the empty basis: its
output `true` is not below its output `false` at the larger input `true`. -/
theorem toggle_empty_basis {γ : List (Commitment (graph not))} {o : Bool}
    {τ : State (graph not)} :
    ¬ SysStep (fun _ => False) (canon (graph not) false) (.output γ o) τ := by
  intro h
  obtain ⟨_, ho, he⟩ := empty_step h
  have e : o = !false := ho.1
  subst e
  exact Bool.noConfusion ((toggle_exposable_iff false).1 he)

/-- **Boolean toggle.**  (1) With `false ≼ true` on the middle, the negation
stage `𝒮₁ = 𝒮₂ = graph not` is not Lifted-Monotone; (2) the composite is the
identity, which is Lifted-Monotone; (3) with the reversed order on the middle
(`Rev`), both re-indexed stages are Lifted-Monotone, and (4) the composite is
the same specification. -/
theorem bool_toggle :
    ¬ (graph not).LiftedMono ∧
    seq (graph not) (graph not) = graph (id : Bool → Bool) ∧
    (graph (id : Bool → Bool)).LiftedMono ∧
    (pushOut (graph not) Rev.mk).LiftedMono ∧
    (pullIn (graph not) Rev.val).LiftedMono ∧
    seq (pushOut (graph not) Rev.mk) (pullIn (graph not) Rev.val) =
      seq (graph not) (graph not) := by
  refine ⟨fun h => not_not_monotone ((graph_liftedMono_iff _).1 h), ?_,
    (graph_liftedMono_iff _).2 fun _ _ h => h, ?_, ?_, reorder_seq _ _ _ _ fun _ => rfl⟩
  · rw [seq_graph]
    congr 1
    funext b
    cases b <;> rfl
  · rw [pushOut_graph, graph_liftedMono_iff]
    intro a b h
    cases a <;> cases b <;> simp_all [Function.comp, PO.le]
  · rw [pullIn_graph, graph_liftedMono_iff]
    intro a b h
    cases a with | mk a => cases b with | mk b =>
      cases a <;> cases b <;> simp_all [Function.comp, PO.le]

/-- Without properness, (3) fails: with `𝒮₁` the identity on `Bool` (which
needs no commitment) and `𝒮₂` negation, the composite is negation, which
violates Lifted Monotonicity, yet `𝒮₁` emits every output without
commitment. -/
theorem needs_commit_needs_proper :
    ¬ (seq (graph (id : Bool → Bool)) (graph not)).LiftedMono ∧
      ∀ τ : State (graph (id : Bool → Bool)), ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o := by
  refine ⟨fun h => not_not_monotone ?_, (exposure_boundary _).1
    ((liftedMono_iff_commonExpansion _).1 ((graph_liftedMono_iff _).2 fun _ _ h => h))⟩
  rw [seq_graph] at h
  exact (graph_liftedMono_iff _).1 h

end BoolToggle

/-! #### The constant store, re-ordered -/

section ConstantStore

/-- `lo ↦ x`, `hi ↦ y`: inverse of `fLvl`. -/
def lvlTwo : Lvl → Two
  | .lo => .x
  | .hi => .y

theorem lvlTwo_fLvl (t : Two) : lvlTwo (fLvl t) = t := by cases t <;> rfl

/-- The constant store `Two → Pt`. -/
def constK : Spec Two Pt := graph fun _ => Pt.pt

/-- **Re-ordering the middle makes `𝒮₁` monotone.**  `anyS` (fiber `{x, y}`,
incomparable) is not Lifted-Monotone; renamed into `lo ≼ hi` it is, its output
`hi` is exposable at the canonical state (it retires `lo`), the renamed
constant store is Lifted-Monotone, and the composite is unchanged, hence
Lifted-Monotone. -/
theorem constant_store_reorder :
    ¬ anyS.LiftedMono ∧ (pushOut anyS fLvl).LiftedMono ∧
    Exposable (canon (pushOut anyS fLvl) Pt.pt) Lvl.hi ∧
    (pullIn constK lvlTwo).LiftedMono ∧
    seq (pushOut anyS fLvl) (pullIn constK lvlTwo) = seq anyS constK ∧
    (seq anyS constK).LiftedMono := by
  have hL : (pushOut anyS fLvl).LiftedMono := fun _ _ _ _ _ _ =>
    ⟨.hi, ⟨.y, trivial, rfl⟩, fun _ _ => Or.inr rfl⟩
  have hK : (pullIn constK lvlTwo).LiftedMono := by
    rw [constK, pullIn_graph, graph_liftedMono_iff]
    intro _ _ _; exact trivial
  have heq := reorder_seq anyS constK fLvl lvlTwo lvlTwo_fLvl
  refine ⟨fun h => ?_, hL, ?_, hK, heq, heq ▸ seq_liftedMono hL hK⟩
  · obtain ⟨u, _, hall⟩ := h Pt.pt Pt.pt trivial [Two.x, Two.y] (by simp) (fun _ _ => trivial)
    have h1 : Two.x = u := hall .x (by simp)
    have h2 : Two.y = u := hall .y (by simp)
    exact Two.noConfusion (h1.trans h2.symm)
  · exact commonExpansion_exposable ((liftedMono_iff_commonExpansion _).1 hL)
      ⟨Pt.pt, [], .nil _⟩ (show (pushOut anyS fLvl).S Pt.pt Lvl.hi ∧ Pt.pt ≼ Pt.pt from
        ⟨⟨.y, trivial, rfl⟩, trivial⟩)

end ConstantStore

/-! ### 3. Characterization for functional stages -/

section Char
variable {I M O : Type} [PO I] [PO O]

/-- **A commitment-free functional upstream is monotone.**  If the empty-basis
system of `graph f` can emit at every canonical state, `f` is monotone (so
`graph f` is Lifted-Monotone). -/
theorem cf_upstream_monotone [PO M] {f : I → M}
    (h : ∀ i, ∃ γ o τ, SysStep (fun _ => False) (canon (graph f) i) (.output γ o) τ) :
    Monotone f := by
  intro x y hxy
  obtain ⟨γ, o, τ, hs⟩ := h x
  obtain ⟨_, ho, he⟩ := empty_step hs
  have e : o = f x := ho.1
  subst e
  exact (graph_canon_exposable_iff f x).1 he y hxy

/-- **Preorder factorization.**  `g ∘ f` is monotone iff some preorder on `M`
makes both `f` and `g` monotone (take `a ≤ b :↔ g a ≼ g b`). -/
theorem preorder_factorization {f : I → M} {g : M → O} :
    Monotone (g ∘ f) ↔ ∃ le : M → M → Prop, (∀ a, le a a) ∧
      (∀ a b c, le a b → le b c → le a c) ∧ (∀ x y, x ≼ y → le (f x) (f y)) ∧
      ∀ a b, le a b → g a ≼ g b := by
  constructor
  · intro h
    exact ⟨fun a b => g a ≼ g b, fun a => PO.refl _, fun _ _ _ h1 h2 => PO.trans h1 h2, h,
      fun _ _ h => h⟩
  · rintro ⟨le, _, _, hf, hg⟩ x y hxy
    exact hg _ _ (hf x y hxy)

/-- The order on `M` pulled back through an injective `g`. -/
@[reducible] def pullPO (g : M → O) (hg : ∀ a b, g a = g b → a = b) : PO M where
  le a b := g a ≼ g b
  refl a := PO.refl (g a)
  trans h h' := PO.trans h h'
  antisymm h h' := hg _ _ (PO.antisymm h h')

/-- **Injective downstream.**  If `g` is injective, the composite `graph (g ∘ f)`
is Lifted-Monotone iff some partial order on `M` makes both stages
Lifted-Monotone. -/
theorem injective_characterization {f : I → M} {g : M → O} (hg : ∀ a b, g a = g b → a = b) :
    (graph (g ∘ f)).LiftedMono ↔ ∃ inst : PO M,
      @Spec.LiftedMono I M _ inst (@graph I M _ inst f) ∧
      @Spec.LiftedMono M O inst _ (@graph M O inst _ g) := by
  constructor
  · intro h
    have hm := (graph_liftedMono_iff _).1 h
    refine ⟨pullPO g hg, (@graph_liftedMono_iff I M _ (pullPO g hg) f).2 hm,
      (@graph_liftedMono_iff M O (pullPO g hg) _ g).2 fun _ _ h => h⟩
  · rintro ⟨inst, h1, h2⟩
    exact (graph_liftedMono_iff _).2 (@functional_composition I M O _ inst _ f g
      ((@graph_liftedMono_iff I M _ inst f).1 h1) ((@graph_liftedMono_iff M O inst _ g).1 h2))

end Char

section Counterexample

/-- The chain `a ≼ b ≼ c`. -/
inductive C3 where
  | a | b | c
  deriving DecidableEq

def C3.rk : C3 → Nat
  | .a => 0
  | .b => 1
  | .c => 2

instance : PO C3 where
  le x y := x.rk ≤ y.rk
  refl _ := Nat.le_refl _
  trans := Nat.le_trans
  antisymm {x y} h h' := by
    have e : x.rk = y.rk := Nat.le_antisymm h h'
    cases x <;> cases y <;> first | rfl | (simp [C3.rk] at e)

/-- Two middle values, with no order fixed. -/
inductive Mid where
  | p | q
  deriving DecidableEq

/-- `a, c ↦ p`, `b ↦ q`. -/
def fz : C3 → Mid
  | .a => .p
  | .b => .q
  | .c => .p

/-- The constant downstream. -/
def gz : Mid → Pt := fun _ => .pt

theorem no_order_monotone (inst : PO Mid) : ¬ @Monotone C3 Mid _ inst fz := by
  intro h
  have h1 : @PO.le Mid inst Mid.p Mid.q := h .a .b (show (0 : Nat) ≤ 1 by decide)
  have h2 : @PO.le Mid inst Mid.q Mid.p := h .b .c (show (1 : Nat) ≤ 2 by decide)
  exact absurd (@PO.antisymm Mid inst _ _ h1 h2) (by decide)

/-- **Repair only by merging.**  Any re-encoding `e : Mid → M'` of the middle,
into any partially ordered `M'`, under which the upstream `e ∘ fz` is monotone
merges `fz a = p` and `fz b = q`. -/
theorem merge_needed {M' : Type} (inst : PO M') (e : Mid → M')
    (h : @Monotone C3 M' _ inst (e ∘ fz)) : e .p = e .q :=
  @PO.antisymm M' inst _ _ (h .a .b (show (0 : Nat) ≤ 1 by decide))
    (h .b .c (show (1 : Nat) ≤ 2 by decide))

/-- **No order on the middle makes both stages monotone.**  The composite
`gz ∘ fz` is Lifted-Monotone (it is constant) whatever the order on `Mid`, yet
under every partial order on `Mid` the upstream `graph fz` violates Lifted
Monotonicity (`fz a = fz c ≠ fz b` with `a ≼ b ≼ c` would force `p = q`), and
its empty-basis system stalls at some canonical state. -/
theorem no_order_counterexample :
    (∀ _inst : PO Mid, (seq (graph fz) (graph gz)).LiftedMono) ∧
    (∀ _inst : PO Mid, ¬ (graph fz).LiftedMono) ∧
    ∀ _inst : PO Mid, ∃ i, ∀ γ o τ,
      ¬ SysStep (fun _ => False) (canon (graph fz) i) (.output γ o) τ := by
  refine ⟨fun inst => ?_, fun inst h => no_order_monotone inst ((graph_liftedMono_iff _).1 h),
    fun inst => ?_⟩
  · rw [seq_graph]
    exact (graph_liftedMono_iff _).2 fun _ _ _ => trivial
  · exact Classical.byContradiction fun hn => no_order_monotone inst
      (cf_upstream_monotone fun i => Classical.byContradiction fun hi =>
        hn ⟨i, fun γ o τ hs => hi ⟨γ, o, τ, hs⟩⟩)

end Counterexample

end Joint
end CC
