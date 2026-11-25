import CoordCriterion.Appendix.JointMono

/-!
# Necessary and tight guards (paper §5.2 and Appendix `app:tight`)

`𝒮₁` is a sufficient guard for `𝒮₂` (`Guard.Proper`, Def.
`def:sufficient-guard`) when the downstream `𝒮₂|_{𝒮₁}` needs no commitment,
and Corollary `cor:upstream-commitments` says the upstream must commit
whenever the composite `P₂ ∘ P₁` does.  This file asks the converse question:
does the upstream commit *more* than the composite needs?  The paper's
necessary guard (Def. `def:necessary-guard`) is `Tight` here, and a tight
guard (Def. `def:tight-guard`) is `Proper ∧ Tight`.  The Lean names predate
the paper's.

**Unit of comparison.**  At the canonical state `σ_P(i)`, emitting `a` removes
the row `(k, b)` by commitment (`Excluded`) exactly when `i ≼ k` and no output
at `k` extends both `a` and `b` (`excluded_canon_iff`).  Such a pair of rows is
a *conflict* (`Conf`, stated for an arbitrary relation so that it also makes
sense for preorders).  Lifted Monotonicity is the absence of conflicts
(`liftedMono_iff_noConf`).

**Downstream order on `M`.**  `dle P₂ m m'` is `JointLift (P₂ m) (P₂ m')`:
every finite set of answers to `m` has a common extension among the answers to
`m'`.  It is transitive (`dle_trans`) and reflexive exactly at directed fibers;
for a function `g` it is `g m ≼ g m'` (`graph_dle_iff`), the pull-back of
`Joint.preorder_factorization`.

* `proper_iff_le_dle` — the pipeline is proper iff `≼_M ⊆ dle` on the
  upstream's outputs: `dle` is the coarsest order on `M` keeping it proper.
* `dleConf_of_compConf`, `conf_of_dleConf` — in a proper pipeline, composite
  conflicts (for any witnesses) ⊆ `dle`-conflicts ⊆ `≼_M`-conflicts.
* `conf_of_dleConf_under` — for every partial order on `M` under which the same
  tables form a proper pipeline, its conflicts include the `dle`-conflicts:
  no order on `M` makes the upstream commit less than `dle` does.
* `compConf_of_dleConf`, `dleConf_iff_compConf` — when the downstream fibers
  have greatest elements, `dle`-conflicts are exactly the composite conflicts
  at those answers.
* `Tight`, `tight_iff_excluded`, `tight_iff` — the upstream is tight when every
  row its canonical commitment removes is removed by the composite's canonical
  commitment for some answers; for proper pipelines with greatest answers this
  says every `≼_M`-conflict is a `dle`-conflict.
* `seq_liftedMono_iff_noDleConf` — with greatest answers, the composite is
  Lifted-Monotone iff the upstream has no `dle`-conflict.
* Deterministic downstream: `graph_conf_iff`, `tight_graph_iff`.
* Sufficient conditions: `tight_of_liftedMono`, `tight_of_reflects`,
  `tightGuard_of_monotone_reflects` (Prop. `prop:tight-guards`).
* Examples: `SMR.log_tight_guard` (the consensus log behind deterministic
  execution is a tight guard), `Log.commuting` (two commuting increments
  behind a prefix-ordered log: a sufficient guard, not a necessary one),
  `Log.partial_order_log` (a partial-order log for them is a tight guard), and `Gap.gap` (without greatest answers no order on
  `M` is tight: a feed-forward upstream cannot see the downstream's answers).
-/

namespace CC
namespace Tight

open Comp Joint Guard Classical

/-! ### Conflicts -/

section Conflicts
variable {I X : Type} [PO I]

/-- Rows `(i, a)` and `(k, b)` of `P` **conflict** under the relation `r` when
`k` extends `i` and no row at `k` is above both outputs under `r`. -/
def Conf (P : Table I X) (r : X → X → Prop) (i : I) (a : X) (k : I) (b : X) : Prop :=
  i ≼ k ∧ P i a ∧ P k b ∧ ¬ ∃ c, P k c ∧ r a c ∧ r b c

/-- A coarser relation on the outputs of `P` has fewer conflicts. -/
theorem conf_mono {P : Table I X} {r s : X → X → Prop}
    (hrs : ∀ a b, (∃ i, P i a) → (∃ i, P i b) → r a b → s a b)
    {i a k b} (h : Conf P s i a k b) : Conf P r i a k b :=
  ⟨h.1, h.2.1, h.2.2.1, fun ⟨c, hc, h1, h2⟩ =>
    h.2.2.2 ⟨c, hc, hrs a c ⟨i, h.2.1⟩ ⟨k, hc⟩ h1, hrs b c ⟨k, h.2.2.1⟩ ⟨k, hc⟩ h2⟩⟩

variable [PO X]

/-- **Conflicts are commitments at canonical states.**  For `a ∈ P(i)`, the row
`(k, b)` is removed by `a`'s canonical commitment at `σ_P(i)` iff the two rows
conflict. -/
theorem excluded_canon_iff (sp : Spec I X) {i : I} {a : X} (ha : sp.P i a) (k : I) (b : X) :
    Excluded (canon sp i) a k b ↔ Conf sp.P PO.le i a k b := by
  constructor
  · rintro ⟨⟨hP, hik⟩, hnab, hns⟩
    exact ⟨hik, ha, hP, fun ⟨c, hc, h1, h2⟩ => hns ⟨⟨hP, hik⟩, hnab, c, ⟨hc, hik⟩, h1, h2⟩⟩
  · rintro ⟨hik, _, hP, hn⟩
    exact ⟨⟨hP, hik⟩, fun h => hn ⟨b, hP, h, PO.refl b⟩,
      fun ⟨_, _, c, hc, h1, h2⟩ => hn ⟨c, hc.1, h1, h2⟩⟩

/-- **Lifted Monotonicity is the absence of conflicts.** -/
theorem liftedMono_iff_noConf (sp : Spec I X) :
    sp.LiftedMono ↔ ∀ i a k b, ¬ Conf sp.P PO.le i a k b := by
  rw [liftedMono_iff_commonExpansion]
  constructor
  · intro hC i a k b hc
    have hE := (exposure_boundary sp).1 hC (canon sp i) ⟨i, [], ExecCF.nil _⟩ a
      ⟨hc.2.1, PO.refl i⟩
    have hnab : ¬ a ≼ b := fun h => hc.2.2.2 ⟨b, hc.2.2.1, h, PO.refl b⟩
    obtain ⟨u, hu, h1, h2⟩ := hE k b ⟨hc.2.2.1, hc.1⟩ hnab
    exact hc.2.2.2 ⟨u, hu.1, h1, h2⟩
  · intro h
    apply Guard.canon_exposable_commonExpansion
    intro i a ha k b hb _
    exact byContradiction fun hno =>
      h i a k b ⟨hb.2, ha, hb.1, fun ⟨c, hc, h1, h2⟩ => hno ⟨c, ⟨hc, hb.2⟩, h1, h2⟩⟩

end Conflicts

/-! ### The downstream order on `M` -/

section Dle
variable {M O : Type} [PO O]

/-- `m ⊑ m'`: every finite set of answers to `m` has a common extension among
the answers to `m'`. -/
def dle (P₂ : Table M O) (m m' : M) : Prop := JointLift (P₂ m) (P₂ m')

theorem dle_trans {P₂ : Table M O} {a b c : M} (h1 : dle P₂ a b) (h2 : dle P₂ b c) :
    dle P₂ a c := by
  intro X hX hA
  obtain ⟨u, hu, hXu⟩ := h1 X hX hA
  obtain ⟨v, hv, huv⟩ := h2 [u] (by simp) (by simpa using hu)
  exact ⟨v, hv, fun x hx => PO.trans (hXu x hx) (huv u (by simp))⟩

/-- `dle` is reflexive exactly at directed fibers. -/
theorem dle_refl_iff {P₂ : Table M O} {m : M} : dle P₂ m m ↔ JointLift (P₂ m) (P₂ m) :=
  Iff.rfl

/-- For a function, `dle` is the order pulled back through it. -/
theorem graph_dle_iff [PO M] {g : M → O} {a b : M} :
    dle (graph g).P a b ↔ g a ≼ g b := by
  constructor
  · intro h
    obtain ⟨u, hu, hall⟩ := h [g a] (by simp) (by simp [graph])
    have e : u = g b := hu
    exact e ▸ hall (g a) (by simp)
  · intro h X _ hX
    exact ⟨g b, rfl, fun z hz => by
      have e : z = g a := hX z hz
      rw [e]; exact h⟩

/-- `t` is the greatest answer to `m`. -/
def HasTop (P₂ : Table M O) (m : M) (t : O) : Prop := P₂ m t ∧ ∀ o, P₂ m o → o ≼ t

end Dle

/-! ### Proper pipelines and the downstream order -/

section Pipelines
variable {I M O : Type} [PO I] [PO M] [PO O]

/-- **`dle` is the coarsest order keeping the pipeline proper.** -/
theorem proper_iff_le_dle (sp : Spec I M) (sk : Spec M O) :
    Proper sp sk ↔ ∀ m m', Img sp m → Img sp m' → m ≼ m' → dle sk.P m m' := by
  rw [Guard.proper_iff, Joint.ceOn_iff_restrictTo]
  constructor
  · intro h m m' hm hm' hle
    exact h ⟨m, hm⟩ ⟨m', hm'⟩ hle
  · intro h a b hab
    exact h a.1 b.1 a.2 b.2 hab

/-- In a proper pipeline, the downstream fibers at the upstream's outputs are
directed. -/
theorem proper_directed {sp : Spec I M} {sk : Spec M O} (hP : Proper sp sk) {m : M}
    (hm : Img sp m) : dle sk.P m m :=
  (proper_iff_le_dle sp sk).1 hP m m hm hm (PO.refl m)

/-- **Every `dle`-conflict is an upstream conflict** in a proper pipeline. -/
theorem conf_of_dleConf {sp : Spec I M} {sk : Spec M O} (hP : Proper sp sk)
    {i m k x} (h : Conf sp.P (dle sk.P) i m k x) : Conf sp.P PO.le i m k x :=
  conf_mono (fun a b ha hb hab => (proper_iff_le_dle sp sk).1 hP a b ha hb hab) h

/-- **Every composite conflict comes from a `dle`-conflict**, for any choice of
witnesses, in a proper pipeline.  (This refines Theorem
Corollary `cor:upstream-commitments`.) -/
theorem dleConf_of_compConf {sp : Spec I M} {sk : Spec M O} (hP : Proper sp sk)
    {i m k x o y} (hi : sp.P i m) (hk : sp.P k x) (hm : sk.P m o) (hx : sk.P x y)
    (hc : Conf (seq sp sk).P PO.le i o k y) : Conf sp.P (dle sk.P) i m k x := by
  refine ⟨hc.1, hi, hk, fun ⟨m', hm', h1, h2⟩ => ?_⟩
  obtain ⟨u1, hu1, h1'⟩ := h1 [o] (by simp) (by simpa using hm)
  obtain ⟨u2, hu2, h2'⟩ := h2 [y] (by simp) (by simpa using hx)
  obtain ⟨u, hu, hall⟩ := proper_directed hP ⟨k, hm'⟩ [u1, u2] (by simp)
    (by simp [hu1, hu2])
  exact hc.2.2.2 ⟨u, ⟨m', hm', hu⟩, PO.trans (h1' o (by simp)) (hall u1 (by simp)),
    PO.trans (h2' y (by simp)) (hall u2 (by simp))⟩

/-- Composite conflicts ⊆ upstream conflicts, for any witnesses. -/
theorem conf_of_compConf {sp : Spec I M} {sk : Spec M O} (hP : Proper sp sk)
    {i m k x o y} (hi : sp.P i m) (hk : sp.P k x) (hm : sk.P m o) (hx : sk.P x y)
    (hc : Conf (seq sp sk).P PO.le i o k y) : Conf sp.P PO.le i m k x :=
  conf_of_dleConf hP (dleConf_of_compConf hP hi hk hm hx hc)

/-- **With greatest answers, a `dle`-conflict is a composite conflict** at
those answers (no properness needed). -/
theorem compConf_of_dleConf {sp : Spec I M} {sk : Spec M O} {i m k x t s}
    (ht : HasTop sk.P m t) (hs : HasTop sk.P x s) (hc : Conf sp.P (dle sk.P) i m k x) :
    Conf (seq sp sk).P PO.le i t k s := by
  refine ⟨hc.1, ⟨m, hc.2.1, ht.1⟩, ⟨x, hc.2.2.1, hs.1⟩, fun ⟨u, ⟨m', hm', hu⟩, h1, h2⟩ => ?_⟩
  refine hc.2.2.2 ⟨m', hm', fun X _ hX => ⟨u, hu, fun z hz => ?_⟩,
    fun X _ hX => ⟨u, hu, fun z hz => ?_⟩⟩
  · exact PO.trans (ht.2 z (hX z hz)) h1
  · exact PO.trans (hs.2 z (hX z hz)) h2

/-- **Exactness with greatest answers.**  In a proper pipeline whose downstream
answers have greatest elements, two rows of `P₁` are a `dle`-conflict exactly
when some answers to them conflict in the composite. -/
theorem dleConf_iff_compConf {sp : Spec I M} {sk : Spec M O} (hP : Proper sp sk)
    (htop : ∀ m, Img sp m → ∃ t, HasTop sk.P m t) {i m k x} (hi : sp.P i m) (hk : sp.P k x) :
    Conf sp.P (dle sk.P) i m k x ↔
      ∃ o y, sk.P m o ∧ sk.P x y ∧ Conf (seq sp sk).P PO.le i o k y := by
  constructor
  · intro hc
    obtain ⟨t, ht⟩ := htop m ⟨i, hi⟩
    obtain ⟨s, hs⟩ := htop x ⟨k, hk⟩
    exact ⟨t, s, ht.1, hs.1, compConf_of_dleConf ht hs hc⟩
  · rintro ⟨o, y, hm, hx, hc⟩
    exact dleConf_of_compConf hP hi hk hm hx hc

/-- **Exactness with greatest answers, without sufficiency.**  When every
downstream fiber at an upstream output has a greatest element, the fibers are
directed, so the sufficient-guard hypothesis of `dleConf_iff_compConf` is not
needed. -/
theorem dleConf_iff_compConf_top {sp : Spec I M} {sk : Spec M O}
    (htop : ∀ m, Img sp m → ∃ t, HasTop sk.P m t) {i m k x} (hi : sp.P i m) (hk : sp.P k x) :
    Conf sp.P (dle sk.P) i m k x ↔
      ∃ o y, sk.P m o ∧ sk.P x y ∧ Conf (seq sp sk).P PO.le i o k y := by
  constructor
  · intro hc
    obtain ⟨t, ht⟩ := htop m ⟨i, hi⟩
    obtain ⟨s, hs⟩ := htop x ⟨k, hk⟩
    exact ⟨t, s, ht.1, hs.1, compConf_of_dleConf ht hs hc⟩
  · rintro ⟨o, y, hm, hx, hc⟩
    refine ⟨hc.1, hi, hk, fun ⟨m', hm', h1, h2⟩ => ?_⟩
    obtain ⟨u1, hu1, h1'⟩ := h1 [o] (by simp) (by simpa using hm)
    obtain ⟨u2, hu2, h2'⟩ := h2 [y] (by simp) (by simpa using hx)
    obtain ⟨t, ht⟩ := htop m' ⟨k, hm'⟩
    exact hc.2.2.2 ⟨t, ⟨m', hm', ht.1⟩, PO.trans (h1' o (by simp)) (ht.2 u1 hu1),
      PO.trans (h2' y (by simp)) (ht.2 u2 hu2)⟩

/-! ### Tight pipelines -/

/-- The upstream is **tight** when every pair of rows its canonical commitments
separate is also separated in the composite, for some answers of the
downstream. -/
def Tight (sp : Spec I M) (sk : Spec M O) : Prop :=
  ∀ i m k x, Conf sp.P PO.le i m k x →
    ∃ o y, sk.P m o ∧ sk.P x y ∧ Conf (seq sp sk).P PO.le i o k y

/-- **Tightness in terms of commitments.**  Every row that the upstream's
canonical commitment `x_m` removes at `σ_{P₁}(i)` corresponds to a row that the
composite's canonical commitment `x_o` removes at `σ_{P₂∘P₁}(i)`, for some
answers `o` to `m` and `y` to `x`. -/
theorem tight_iff_excluded (sp : Spec I M) (sk : Spec M O) :
    Tight sp sk ↔ ∀ i m k x, sp.P i m → Excluded (canon sp i) m k x →
      ∃ o y, sk.P m o ∧ sk.P x y ∧ Excluded (canon (seq sp sk) i) o k y := by
  constructor
  · intro hT i m k x hi he
    obtain ⟨o, y, hm, hx, hc⟩ := hT i m k x ((excluded_canon_iff sp hi k x).1 he)
    exact ⟨o, y, hm, hx, (excluded_canon_iff (seq sp sk) ⟨m, hi, hm⟩ k y).2 hc⟩
  · intro h i m k x hc
    obtain ⟨o, y, hm, hx, he⟩ := h i m k x hc.2.1 ((excluded_canon_iff sp hc.2.1 k x).2 hc)
    exact ⟨o, y, hm, hx, (excluded_canon_iff (seq sp sk) ⟨m, hc.2.1, hm⟩ k y).1 he⟩

/-- A tight proper pipeline has every upstream conflict forced by the
downstream order. -/
theorem dleConf_of_tight {sp : Spec I M} {sk : Spec M O} (hP : Proper sp sk)
    (hT : Tight sp sk) {i m k x} (h : Conf sp.P PO.le i m k x) : Conf sp.P (dle sk.P) i m k x := by
  obtain ⟨o, y, hm, hx, hc⟩ := hT i m k x h
  exact dleConf_of_compConf hP h.2.1 h.2.2.1 hm hx hc

/-- **Tightness with greatest answers.**  A proper pipeline whose downstream
answers have greatest elements is tight iff its upstream conflicts are exactly
the `dle`-conflicts. -/
theorem tight_iff {sp : Spec I M} {sk : Spec M O} (hP : Proper sp sk)
    (htop : ∀ m, Img sp m → ∃ t, HasTop sk.P m t) :
    Tight sp sk ↔ ∀ i m k x, Conf sp.P PO.le i m k x ↔ Conf sp.P (dle sk.P) i m k x := by
  constructor
  · intro hT i m k x
    exact ⟨dleConf_of_tight hP hT, conf_of_dleConf hP⟩
  · intro h i m k x hc
    exact (dleConf_iff_compConf hP htop hc.2.1 hc.2.2.1).1 ((h i m k x).1 hc)

/-- **The composite through the downstream order.**  With greatest answers, the
composite is Lifted-Monotone iff the upstream has no `dle`-conflict. -/
theorem seq_liftedMono_iff_noDleConf {sp : Spec I M} {sk : Spec M O} (hP : Proper sp sk)
    (htop : ∀ m, Img sp m → ∃ t, HasTop sk.P m t) :
    (seq sp sk).LiftedMono ↔ ∀ i m k x, ¬ Conf sp.P (dle sk.P) i m k x := by
  rw [liftedMono_iff_noConf]
  constructor
  · intro h i m k x hc
    obtain ⟨o, y, _, _, hc'⟩ := (dleConf_iff_compConf hP htop hc.2.1 hc.2.2.1).1 hc
    exact h i o k y hc'
  · intro h i o k y hc
    obtain ⟨m, hi, hm⟩ := hc.2.1
    obtain ⟨x, hk, hx⟩ := hc.2.2.1
    exact h i m k x (dleConf_of_compConf hP hi hk hm hx hc)

/-! ### Deterministic downstream -/

/-- With a function downstream, `dle`-conflicts are exactly the composite
conflicts at the answers (no properness needed). -/
theorem graph_conf_iff (sp : Spec I M) (g : M → O) {i m k x} (hi : sp.P i m)
    (hk : sp.P k x) :
    Conf sp.P (fun a b => g a ≼ g b) i m k x ↔ Conf (seq sp (graph g)).P PO.le i (g m) k (g x) := by
  constructor
  · intro hc
    exact compConf_of_dleConf (sk := graph g) ⟨rfl, fun o h => h ▸ PO.refl _⟩
      ⟨rfl, fun o h => h ▸ PO.refl _⟩
      (conf_mono (fun a b _ _ h => graph_dle_iff.1 h) hc)
  · intro hc
    refine ⟨hc.1, hi, hk, fun ⟨m', hm', h1, h2⟩ => hc.2.2.2 ⟨g m', ⟨m', hm', rfl⟩, h1, h2⟩⟩

/-- **Deterministic tightness.**  Behind a function `g`, the upstream is tight
iff each of its conflicts is a conflict under the order pulled back through
`g`. -/
theorem tight_graph_iff (sp : Spec I M) (g : M → O) :
    Tight sp (graph g) ↔
      ∀ i m k x, Conf sp.P PO.le i m k x → Conf sp.P (fun a b => g a ≼ g b) i m k x := by
  constructor
  · intro hT i m k x hc
    obtain ⟨o, y, hm, hx, hc'⟩ := hT i m k x hc
    have e1 : o = g m := hm
    have e2 : y = g x := hx
    subst e1; subst e2
    exact (graph_conf_iff sp g hc.2.1 hc.2.2.1).2 hc'
  · intro h i m k x hc
    exact ⟨g m, g x, rfl, rfl, (graph_conf_iff sp g hc.2.1 hc.2.2.1).1 (h i m k x hc)⟩

end Pipelines

section Optimal
variable {I M O : Type} [PO I] [PO O]

/-- **Optimality.**  For every partial order `inst` on `M` under which the same
tables form a proper pipeline, the upstream's conflicts under `inst` include
the `dle`-conflicts: no order on `M` makes the upstream commit less.  (The
given order is `instM`; `inst` is passed explicitly, as in
`Joint.seq_liftedMono_reorder`.) -/
theorem conf_of_dleConf_under {instM : PO M} (inst : PO M) (sp : @Spec I M _ instM)
    (sk : @Spec M O instM _)
    (hP : @Proper I M O _ inst _ (underOut inst sp) (underIn inst sk))
    {i m k x} (h : Conf (@Spec.P I M _ instM sp) (dle (@Spec.P M O instM _ sk)) i m k x) :
    Conf (@Spec.P I M _ instM sp) (@PO.le M inst) i m k x :=
  @conf_of_dleConf I M O _ inst _ (underOut inst sp) (underIn inst sk) hP i m k x h

end Optimal

/-! ### Ordering `M` by `⊑` -/

section DleOrder
variable {I M O : Type} [PO I] [PO O]

/-- With greatest answers, `⊑` is reflexive. -/
theorem dle_refl_of_top {P₂ : Table M O} (htop : ∀ m, ∃ t, HasTop P₂ m t) (m : M) :
    dle P₂ m m := by
  intro X _ hX
  obtain ⟨t, ht⟩ := htop m
  exact ⟨t, ht.1, fun x hx => ht.2 x (hX x hx)⟩

/-- `⊑` as an order (preorder) on `M`, when it is reflexive; it is always
transitive (`dle_trans`). -/
def dleOrder (P₂ : Table M O) (hr : ∀ m, dle P₂ m m) : PO M where
  le := dle P₂
  refl := hr
  trans := dle_trans

/-- **Ordering `M` by `⊑` gives a tight guard.**  If each `P₂(m)` has a
greatest element, `⊑` is reflexive (`dle_refl_of_top`) and transitive, so an
order, and with `M` ordered by `⊑` the upstream is a sufficient and a necessary
guard. -/
theorem tightGuard_dleOrder {instM : PO M} (sp : @Spec I M _ instM) (sk : @Spec M O instM _)
    (htop : ∀ m, ∃ t, HasTop sk.P m t) :
    let inst := dleOrder sk.P (dle_refl_of_top htop)
    @Proper I M O _ inst _ (underOut inst sp) (underIn inst sk) ∧
      @Tight I M O _ inst _ (underOut inst sp) (underIn inst sk) := by
  intro inst
  have hP : @Proper I M O _ inst _ (underOut inst sp) (underIn inst sk) :=
    (@proper_iff_le_dle I M O _ inst _ (underOut inst sp) (underIn inst sk)).2
      (fun _ _ _ _ h => h)
  exact ⟨hP, (@tight_iff I M O _ inst _ (underOut inst sp) (underIn inst sk) hP
    (fun m _ => htop m)).2 (fun _ _ _ _ => Iff.rfl)⟩

end DleOrder

/-! ### Tight guards: two sufficient conditions for necessity -/

section TightGuards
variable {I M O : Type} [PO I] [PO M] [PO O]

/-- **A lifted-monotone upstream is a necessary guard**, vacuously: it has no
conflicts, so it makes no commitment at all. -/
theorem tight_of_liftedMono (sp : Spec I M) (sk : Spec M O) (h : sp.LiftedMono) :
    Tight sp sk :=
  fun i m k x hc => absurd hc ((liftedMono_iff_noConf sp).1 h i m k x)

/-- **A downstream that reflects the upstream's order makes the guard
necessary.**  If, on the upstream's outputs, `g a ≼ g b` implies `a ≼ b`, every
conflict of the upstream is also a conflict under the order pulled back
through `g`, so the upstream is tight behind `g` (`tight_graph_iff`). -/
theorem tight_of_reflects (sp : Spec I M) (g : M → O)
    (hr : ∀ a b, Img sp a → Img sp b → g a ≼ g b → a ≼ b) : Tight sp (graph g) := by
  rw [tight_graph_iff]
  intro i m k x hc
  refine ⟨hc.1, hc.2.1, hc.2.2.1, fun ⟨c, hcP, h1, h2⟩ => hc.2.2.2 ⟨c, hcP, ?_, ?_⟩⟩
  · exact hr _ _ ⟨i, hc.2.1⟩ ⟨k, hcP⟩ h1
  · exact hr _ _ ⟨k, hc.2.2.1⟩ ⟨k, hcP⟩ h2

/-- **Tight guard behind a monotone, order-reflecting function.**  A monotone
`g` makes the guard sufficient (`Guard.proper_of_ce`), and one that also
reflects the upstream's order on its outputs makes it necessary. -/
theorem tightGuard_of_monotone_reflects (sp : Spec I M) (g : M → O) (hm : Monotone g)
    (hr : ∀ a b, Img sp a → Img sp b → g a ≼ g b → a ≼ b) :
    Proper sp (graph g) ∧ Tight sp (graph g) :=
  ⟨Guard.proper_of_ce (Guard.graph_commonExpansion hm), tight_of_reflects sp g hr⟩

end TightGuards

/-! ### Example: a totally ordered log is a tight guard when the responses
determine the log -/

namespace SMR

open Inst (Pfx exec execF smrS1)

variable {Cmd Stt R : Type} (δ : Stt → Cmd → Stt × R)

/-- Each response names its command, so the response log determines the log. -/
theorem fst_exec : ∀ (σ : Stt) (l : List Cmd), (exec δ σ l).map Prod.fst = l
  | _, [] => rfl
  | σ, c :: l => by simp only [exec, List.map_cons, fst_exec _ l]

/-- Execution reflects the prefix order: if one response log extends another,
so does the log. -/
theorem execF_reflects (σ0 : Stt) (a b : Pfx Cmd) (h : execF δ σ0 a ≼ execF δ σ0 b) :
    a ≼ b := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t.map Prod.fst, ?_⟩
  have := congrArg (List.map Prod.fst) ht
  simpa [execF, fst_exec, List.map_append] using this

/-- **The consensus log is a tight guard for the replicated store.**  Behind
deterministic execution, whose response log records each command, the totally
ordered log is a sufficient guard (execution is monotone) and a necessary one
(execution reflects the prefix order): every commitment the log makes is one
the store's clients can observe. -/
theorem log_tight_guard (σ0 : Stt) :
    Proper (smrS1 (Cmd := Cmd)) (graph (execF δ σ0)) ∧ Tight (smrS1 (Cmd := Cmd)) (graph (execF δ σ0)) :=
  tightGuard_of_monotone_reflects _ _ (Inst.execF_monotone δ σ0)
    (fun a b _ _ h => execF_reflects δ σ0 a b h)

end SMR


/-! ### Example: commuting commands behind a log -/

namespace Log

/-- The commands received so far: none, `A`, `B`, or both. -/
inductive Req where
  | none | a | b | ab
  deriving DecidableEq

def Req.leb : Req → Req → Bool
  | .none, _ => true
  | .a, .a | .a, .ab => true
  | .b, .b | .b, .ab => true
  | .ab, .ab => true
  | _, _ => false

/-- Received commands, ordered by inclusion. -/
instance : PO Req where
  le x y := Req.leb x y = true
  refl x := by cases x <;> rfl
  trans {x y z} h h' := by cases x <;> cases y <;> cases z <;> simp_all [Req.leb]

instance : PO.Antisymm Req where
  antisymm {x y} h h' := by dsimp only [PO.le] at *; cases x <;> cases y <;> simp_all [Req.leb]

@[simp] theorem Req.le_iff {x y : Req} : x ≼ y ↔ Req.leb x y = true := Iff.rfl

/-- Logs of the two commands. -/
inductive L where
  | e | a | b | ab | ba
  deriving DecidableEq

def L.leb : L → L → Bool
  | .e, _ => true
  | .a, .a | .a, .ab => true
  | .b, .b | .b, .ba => true
  | .ab, .ab => true
  | .ba, .ba => true
  | _, _ => false

/-- Logs, ordered by prefix. -/
instance : PO L where
  le x y := L.leb x y = true
  refl x := by cases x <;> rfl
  trans {x y z} h h' := by cases x <;> cases y <;> cases z <;> simp_all [L.leb]

instance : PO.Antisymm L where
  antisymm {x y} h h' := by dsimp only [PO.le] at *; cases x <;> cases y <;> simp_all [L.leb]

@[simp] theorem L.le_iff {x y : L} : x ≼ y ↔ L.leb x y = true := Iff.rfl

/-- The log orders the received commands in either order. -/
def logP : Table Req L
  | .none, .e => True
  | .a, .a => True
  | .b, .b => True
  | .ab, .ab => True
  | .ab, .ba => True
  | _, _ => False

def log : Spec Req L where
  P := logP
  total i := by
    cases i with
    | none => exact ⟨.e, trivial⟩
    | a => exact ⟨.a, trivial⟩
    | b => exact ⟨.b, trivial⟩
    | ab => exact ⟨.ab, trivial⟩

/-- Both commands are increments, so the store's response is the log length. -/
def len : L → Nat
  | .e => 0
  | .a => 1
  | .b => 1
  | .ab => 2
  | .ba => 2

/-- **Commuting increments.**  The pipeline is proper, and the log's
commitment ordering `A` before `B` (emitting `[A]` at `{A}` separates the row
`({A,B}, [B,A])`) is a conflict under the prefix order; but the composite has
no conflict there, the pulled-back order `len` has none, and so the log is not
tight.  The log is not Lifted-Monotone on its own, while the composite is. -/
theorem commuting :
    Proper log (graph len) ∧ Conf log.P PO.le .a .a .ab .ba ∧
      ¬ Conf (seq log (graph len)).P PO.le .a 1 .ab 2 ∧
      ¬ Conf log.P (fun m m' => len m ≼ len m') .a .a .ab .ba ∧
      ¬ Tight log (graph len) ∧ ¬ log.LiftedMono ∧ (seq log (graph len)).LiftedMono := by
  have hproper : Proper log (graph len) :=
    Guard.proper_iff.2 (Joint.graph_ceOn fun p q _ _ h => by
      show len p ≤ len q
      cases p <;> cases q <;> simp_all [L.leb, len])
  have hconf : Conf log.P PO.le .a .a .ab .ba := by
    refine ⟨rfl, trivial, trivial, fun ⟨c, hc, h1, h2⟩ => ?_⟩
    cases c <;> simp_all [log, logP, L.leb]
  have hnot : ¬ Conf (seq log (graph len)).P PO.le .a 1 .ab 2 :=
    fun h => h.2.2.2 ⟨2, ⟨.ab, trivial, rfl⟩, show 1 ≤ 2 by decide, show 2 ≤ 2 by decide⟩
  refine ⟨hproper, hconf, hnot, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hnot ((graph_conf_iff log len (i := .a) (m := .a) (k := .ab) (x := .ba) trivial trivial).1 h)
  · intro hT
    obtain ⟨o, y, ho, hy, hc⟩ := hT _ _ _ _ hconf
    have e1 : o = 1 := ho
    have e2 : y = 2 := hy
    subst e1; subst e2
    exact hnot hc
  · intro h
    exact (liftedMono_iff_noConf log).1 h _ _ _ _ hconf
  · rw [liftedMono_iff_noConf]
    rintro i o k y ⟨hik, ⟨m, hm, ho⟩, ⟨x, hx, hy⟩, hn⟩
    have e1 : o = len m := ho
    have e2 : y = len x := hy
    subst e1; subst e2
    apply hn
    refine ⟨len x, ⟨x, hx, rfl⟩, ?_, PO.refl _⟩
    show len m ≤ len x
    cases i <;> cases k <;> cases m <;> cases x <;> simp_all [log, logP, Req.leb, len]

/-! #### A partial-order log for commuting commands -/

/-- A partial-order log for two commuting commands records only which commands
it has logged, not their order: its values are sets of commands, ordered by
inclusion (`Req`).  At received commands `i`, it may emit any logged set
contained in `i`. -/
def plogP : Table Req Req := fun i t => t ≼ i

def plog : Spec Req Req where
  P := plogP
  total i := ⟨i, PO.refl i⟩

/-- The store's response to a set of increments is its size. -/
def card : Req → Nat
  | .none => 0
  | .a => 1
  | .b => 1
  | .ab => 2

theorem card_monotone : Monotone card := by
  intro x y h
  show card x ≤ card y
  cases x <;> cases y <;> simp_all [Req.leb, card]

/-- **The partial-order log is a tight guard.**  It is a sufficient guard
(`card` is monotone) and a necessary one: it is itself lifted monotone, so it
makes no commitment at all, and the commuting commands are never ordered. -/
theorem partial_order_log :
    Proper plog (graph card) ∧ Tight plog (graph card) ∧ plog.LiftedMono := by
  have hLM : plog.LiftedMono := by
    rw [liftedMono_iff_noConf]
    intro i a k b hc
    exact hc.2.2.2 ⟨k, PO.refl k, PO.trans hc.2.1 hc.1, hc.2.2.1⟩
  exact ⟨Guard.proper_of_ce (Guard.graph_commonExpansion card_monotone),
    tight_of_liftedMono plog (graph card) hLM, hLM⟩

end Log

/-! ### Example: without greatest answers no order on `M` is tight -/

namespace Gap

/-- Two inputs, `lo ≼ hi`. -/
inductive Lv where
  | lo | hi
  deriving DecidableEq

instance : PO Lv where
  le x y := x = .lo ∨ y = .hi
  refl x := by cases x <;> simp
  trans {x y z} h h' := by cases x <;> cases y <;> cases z <;> simp_all

instance : PO.Antisymm Lv where
  antisymm {x y} h h' := by dsimp only [PO.le] at *; cases x <;> cases y <;> simp_all

/-- Intermediate values: `z`, or `n k` for a count `k`. -/
inductive Mid where
  | z
  | n (k : Nat)

/-- The discrete order on `Mid`. -/
instance midPO : PO Mid where
  le x y := x = y
  refl _ := rfl
  trans h h' := h.trans h'

instance : PO.Antisymm Mid where
  antisymm h _ := h

/-- At `lo` the upstream emits `z`; at `hi`, any `n k`. -/
def upP : Table Lv Mid
  | .lo, .z => True
  | .hi, .n _ => True
  | _, _ => False

def up : Spec Lv Mid where
  P := upP
  total i := by
    cases i with
    | lo => exact ⟨.z, trivial⟩
    | hi => exact ⟨.n 0, trivial⟩

/-- Any count answers `z`; `n k` is answered by `k`. -/
def downP : Table Mid Nat
  | .z, _ => True
  | .n k, o => o = k

def down : Spec Mid Nat where
  P := downP
  total m := by
    cases m with
    | z => exact ⟨0, trivial⟩
    | n k => exact ⟨k, rfl⟩

theorem nat_bound : ∀ X : List Nat, ∃ u, ∀ x ∈ X, x ≤ u
  | [] => ⟨0, by simp⟩
  | x :: X => by
    obtain ⟨u, hu⟩ := nat_bound X
    exact ⟨max x u, fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (hu y hy) (Nat.le_max_right _ _)⟩

/-- **The price of feed-forward.**  The pipeline is proper and the rows
`(lo, z)` and `(hi, n 0)` are a `dle`-conflict, hence a conflict under every
partial order on `Mid` that keeps the pipeline proper; yet the composite has
no conflict at all (both its fibers are all of `ℕ`).  The upstream must pick
`n k` at `hi` without seeing the downstream's answer at `lo`. -/
theorem gap :
    Proper up down ∧ Conf up.P (dle down.P) .lo .z .hi (.n 0) ∧
      (∀ inst : PO Mid, @Proper Lv Mid Nat _ inst _ (@underOut Lv Mid _ midPO inst up)
          (@underIn Mid Nat _ midPO inst down) →
        Conf upP (@PO.le Mid inst) .lo .z .hi (.n 0)) ∧
      (seq up down).LiftedMono ∧ ¬ Tight up down := by
  have hproper : Proper up down := by
    rw [proper_iff_le_dle]
    rintro m m' _ _ (rfl : m = m')
    intro X _ hX
    cases m with
    | z => obtain ⟨u, hu⟩ := nat_bound X; exact ⟨u, trivial, hu⟩
    | n k => exact ⟨k, rfl, fun x hx => by
        have e : x = k := hX x hx
        exact e ▸ Nat.le_refl k⟩
  have hdle : Conf up.P (dle down.P) .lo .z .hi (.n 0) := by
    refine ⟨Or.inl rfl, trivial, trivial, fun ⟨c, hc, h1, _⟩ => ?_⟩
    cases c with
    | z => exact hc
    | n k =>
      obtain ⟨u, hu, hall⟩ := h1 [k + 1] (by simp) (by simp [down, downP])
      have e : u = k := hu
      have := hall (k + 1) (by simp)
      rw [e] at this
      exact Nat.not_succ_le_self k this
  have hlm : (seq up down).LiftedMono := by
    rw [liftedMono_iff_noConf]
    rintro i o k y ⟨_, _, _, hn⟩
    apply hn
    cases k
    · exact ⟨max o y, ⟨.z, trivial, trivial⟩, Nat.le_max_left _ _, Nat.le_max_right _ _⟩
    · exact ⟨max o y, ⟨.n (max o y), trivial, rfl⟩, Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  refine ⟨hproper, hdle, fun inst hP => @conf_of_dleConf_under Lv Mid Nat _ _ midPO inst up down hP _ _ _ _ hdle, hlm, ?_⟩
  intro hT
  obtain ⟨o, y, _, _, hc⟩ := hT _ _ _ _ (conf_of_dleConf hproper hdle)
  exact (liftedMono_iff_noConf _).1 hlm _ _ _ _ hc

end Gap

end Tight
end CC
