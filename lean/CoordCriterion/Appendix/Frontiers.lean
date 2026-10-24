import CoordCriterion.Foundations.Core
import CoordCriterion.Foundations.Runs
import CoordCriterion.FunctionalCALM.Theorem

/-!
# Coordination-free frontiers: remembered outputs and forwarding (Appendix H, `sec:frontiers`)

Namespace `CC.Front`.  Formalizes, on top of `Foundations` and
`FunctionalCALM/Theorem.lean`:

* Theorem `thm:monotone-hull` (remembered-output frontier):
  `hull_relaxation`, `hull_relMono`, `hull_least`, and the finite pruning
  clause `pruned_equiv`, `pruned_relaxation`, `pruned_relMono`,
  `pruned_least`, `pruned_unique` (bundled as `monotone_hull`);
  the transformed specification on Hoare classes is functional and
  monotone, hence consistent (`hullSpec_consistent`);
* Table `tab:lookup-lift` as printed (`X(i₀)={o_a}`, `X(i₁)={o_b}`,
  `M = X̂`, forwarding above `X̂`): `lookup_hull_i0`, `lookup_hull_i1`,
  `lookup_pruned`, `lookup_not_relMono`, `fwdA`, `lookup_hull_le_fwd`;
* the quotient order `(𝒫(O)∖{∅})/≡_H` (`hclass_of_le_iff`,
  `hclass_of_eq_iff`, `hclass_eq_of`);
* Proposition `prop:persistent-forwarding`: `persistent_forwarding`,
  `fwdSpec_consistent`, and Eq. `forwarding-hull` (`forwarding_hull`, and via
  Eq. `hull-coverage`: `forwarding_hull_via_coverage`, `disc_hoare_iff`).

The independent-product frontier (Theorem `thm:product-frontier`) is in
`Appendix/ProductFrontier.lean`, its causal-register application in
`Appendix/Registers.lean`.

## Modeling choices

1. *Hoare carrier.*  Instead of the quotient
   `(𝒫(O) \ {∅}) / ≡_H` we use its canonical representatives: nonempty
   down-closed sets ordered by inclusion (`HClass`).  `A ⊑_H B` iff
   `↓A ⊆ ↓B` (`hoare_iff_down`), so this is order-isomorphic to the quotient.
   The theorem itself is stated on set representatives, exactly as in the
   paper; `HClass` is only used to check that the transformed object really
   is an ordered (functional) specification.
2. *Tables, not specs, in the hull theorem.*  The hull results hold for an
   arbitrary table `X : I → O → Prop` (totality is only used to make the
   transformed fibers nonempty).  This is what the forwarding example needs,
   since its exact-claim fibers may be empty.
3. *Finiteness* of `X̂(i)` is "some list enumerates it".
4. *Forwarding.*  Search positions are a fixed type `P` (obligation 1,
   stable identities, holds by construction: a step cannot rename
   positions; new nodes are positions with no edges yet).  A structure
   snapshot is a key-indexed edge relation plus a key-indexed occurrence
   predicate.  A restructuring history is a list of snapshots after a fixed
   initial one, each consecutive pair related by a step relation that is
   assumed to satisfy obligations 2–3.  Inputs are such histories ordered by
   list prefix.  The positive claims `R(h)` are ordered by inclusion.
-/

namespace CC
namespace Front

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Hoare preorder and the remembered-output hull -/

section Hull
variable {I O : Type} [PO I] [PO O]

/-- Hoare preorder (Eq. `lifted-output-order`). -/
def HoareLe (A B : O → Prop) : Prop := ∀ a, A a → ∃ b, B b ∧ a ≼ b

theorem HoareLe.refl (A : O → Prop) : HoareLe A A := fun a h => ⟨a, h, PO.refl a⟩

theorem HoareLe.trans {A B C : O → Prop} (h1 : HoareLe A B) (h2 : HoareLe B C) :
    HoareLe A C := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := h1 a ha
  obtain ⟨c, hc, hbc⟩ := h2 b hb
  exact ⟨c, hc, PO.trans hab hbc⟩

theorem HoareLe.of_sub {A B : O → Prop} (h : ∀ o, A o → B o) : HoareLe A B :=
  fun a ha => ⟨a, h a ha, PO.refl a⟩

/-- Remembered output `X̂(i) = ⋃_{j ≼ i} X(j)` (Eq. `monotone-hull`). -/
def hull (X : Table I O) : Table I O := fun i o => ∃ j, j ≼ i ∧ X j o

/-- Powerset relaxation: `X(i) ⊑_H A(i)` at every input. -/
def Relaxation (X A : Table I O) : Prop := ∀ i, HoareLe (X i) (A i)

/-- Relational Monotonicity of a powerset-valued map. -/
def HRelMono (A : Table I O) : Prop := ∀ i k, i ≼ k → HoareLe (A i) (A k)

theorem hull_relaxation (X : Table I O) : Relaxation X (hull X) :=
  fun i => HoareLe.of_sub fun o h => ⟨i, PO.refl i, h⟩

theorem hull_mono (X : Table I O) {i k : I} (h : i ≼ k) : ∀ o, hull X i o → hull X k o :=
  fun _ ⟨j, hj, hx⟩ => ⟨j, PO.trans hj h, hx⟩

theorem hull_relMono (X : Table I O) : HRelMono (hull X) :=
  fun _ _ h => HoareLe.of_sub (hull_mono X h)

/-- Eq. `hull-coverage`: every relaxation satisfying Relational Monotonicity
expands every output seen so far. -/
theorem hull_least (X A : Table I O) (hA : Relaxation X A) (hM : HRelMono A) (i : I) :
    HoareLe (hull X i) (A i) := by
  rintro o ⟨j, hji, hx⟩
  obtain ⟨a, ha, hoa⟩ := hA j o hx
  obtain ⟨b, hb, hab⟩ := hM j i hji a ha
  exact ⟨b, hb, PO.trans hoa hab⟩

/-- Finite set: enumerated by a list. -/
def FiniteSet (B : O → Prop) : Prop := ∃ L : List O, ∀ o, B o ↔ o ∈ L

/-- Maximal elements of a set. -/
def maxOf (B : O → Prop) : O → Prop := fun m => B m ∧ ∀ o, B o → m ≼ o → o = m

/-- In a finite list, every element lies below a maximal element. -/
theorem list_max_above : ∀ (L : List O) (o : O), o ∈ L →
    ∃ m, m ∈ L ∧ o ≼ m ∧ ∀ x, x ∈ L → m ≼ x → x = m
  | [], _, h => absurd h (List.not_mem_nil)
  | a :: L, o, ho => by
    classical
    by_cases hA : ∃ m, m ∈ L ∧ a ≼ m ∧ ∀ x, x ∈ L → m ≼ x → x = m
    · -- Every `L`-maximal element is `(a :: L)`-maximal.
      obtain ⟨m0, hm0, ham0, hmax0⟩ := hA
      have lift : ∀ m, m ∈ L → (∀ x, x ∈ L → m ≼ x → x = m) →
          ∀ x, x ∈ a :: L → m ≼ x → x = m := by
        intro m hm hmax x hx hmx
        rcases List.mem_cons.1 hx with rfl | hx
        · have : m0 = m := hmax m0 hm0 (PO.trans hmx ham0)
          subst this
          exact PO.antisymm ham0 hmx
        · exact hmax x hx hmx
      rcases List.mem_cons.1 ho with rfl | ho
      · exact ⟨m0, List.mem_cons_of_mem _ hm0, ham0, lift m0 hm0 hmax0⟩
      · obtain ⟨m, hm, hom, hmax⟩ := list_max_above L o ho
        exact ⟨m, List.mem_cons_of_mem _ hm, hom, lift m hm hmax⟩
    · -- `a` itself is maximal.
      have amax : ∀ x, x ∈ a :: L → a ≼ x → x = a := by
        intro x hx hax
        rcases List.mem_cons.1 hx with rfl | hx
        · rfl
        · obtain ⟨m, hm, hxm, hmax⟩ := list_max_above L x hx
          exact absurd ⟨m, hm, PO.trans hax hxm, hmax⟩ hA
      rcases List.mem_cons.1 ho with rfl | ho
      · exact ⟨o, List.mem_cons_self, PO.refl o, amax⟩
      · obtain ⟨m, hm, hom, hmax⟩ := list_max_above L o ho
        by_cases hma : m ≼ a
        · exact ⟨a, List.mem_cons_self, PO.trans hom hma, amax⟩
        · refine ⟨m, List.mem_cons_of_mem _ hm, hom, ?_⟩
          intro x hx hmx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact absurd hmx hma
          · exact hmax x hx hmx

theorem finite_max_above {B : O → Prop} (hB : FiniteSet B) {o : O} (ho : B o) :
    ∃ m, maxOf B m ∧ o ≼ m := by
  obtain ⟨L, hL⟩ := hB
  obtain ⟨m, hm, hom, hmax⟩ := list_max_above L o ((hL o).1 ho)
  exact ⟨m, ⟨(hL m).2 hm, fun x hx hmx => hmax x ((hL x).1 hx) hmx⟩, hom⟩

/-- The pruned output `M(i)`: maximal elements of `X̂(i)`. -/
def pruned (X : Table I O) : Table I O := fun i => maxOf (hull X i)

theorem pruned_sub (X : Table I O) (i : I) : ∀ o, pruned X i o → hull X i o :=
  fun _ h => h.1

/-- `M(i) ≡_H X̂(i)` when `X̂(i)` is finite. -/
theorem pruned_equiv (X : Table I O) (hfin : ∀ i, FiniteSet (hull X i)) (i : I) :
    HoareLe (hull X i) (pruned X i) ∧ HoareLe (pruned X i) (hull X i) :=
  ⟨fun _ ho => finite_max_above (hfin i) ho, HoareLe.of_sub (pruned_sub X i)⟩

theorem pruned_relaxation (X : Table I O) (hfin : ∀ i, FiniteSet (hull X i)) :
    Relaxation X (pruned X) :=
  fun i => (hull_relaxation X i).trans (pruned_equiv X hfin i).1

theorem pruned_relMono (X : Table I O) (hfin : ∀ i, FiniteSet (hull X i)) :
    HRelMono (pruned X) :=
  fun i k h => ((pruned_equiv X hfin i).2.trans (hull_relMono X i k h)).trans
    (pruned_equiv X hfin k).1

/-- Minimality: every `Y ⊆ X̂(i)` with `X̂(i) ⊑_H Y` contains `M(i)`
(no finiteness needed). -/
theorem pruned_least (X : Table I O) (i : I) (Y : O → Prop)
    (hY : ∀ o, Y o → hull X i o) (hcov : HoareLe (hull X i) Y) :
    ∀ m, pruned X i m → Y m := by
  intro m ⟨hm, hmax⟩
  obtain ⟨y, hy, hmy⟩ := hcov m hm
  have : y = m := hmax y (hY y hy) hmy
  exact this ▸ hy

/-- Uniqueness of the smallest such subset. -/
theorem pruned_unique (X : Table I O) (hfin : ∀ i, FiniteSet (hull X i)) (i : I)
    (Z : O → Prop) (hZ : ∀ o, Z o → hull X i o) (hZcov : HoareLe (hull X i) Z)
    (hZmin : ∀ Y : O → Prop, (∀ o, Y o → hull X i o) → HoareLe (hull X i) Y →
      ∀ o, Z o → Y o) :
    ∀ o, Z o ↔ pruned X i o :=
  fun o => ⟨hZmin _ (pruned_sub X i) (pruned_equiv X hfin i).1 o,
    pruned_least X i Z hZ hZcov o⟩

/-- **Theorem `thm:monotone-hull`** (Remembered-output frontier), bundled. -/
theorem monotone_hull (X : Table I O) :
    (Relaxation X (hull X) ∧ HRelMono (hull X)) ∧
    (∀ A, Relaxation X A → HRelMono A → ∀ i, HoareLe (hull X i) (A i)) ∧
    ((∀ i, FiniteSet (hull X i)) →
      (∀ i, HoareLe (hull X i) (pruned X i) ∧ HoareLe (pruned X i) (hull X i)) ∧
      HRelMono (pruned X) ∧
      (∀ i, (∀ o, pruned X i o → hull X i o) ∧ HoareLe (hull X i) (pruned X i) ∧
        ∀ Y : O → Prop, (∀ o, Y o → hull X i o) → HoareLe (hull X i) Y →
          ∀ o, pruned X i o → Y o)) :=
  ⟨⟨hull_relaxation X, hull_relMono X⟩, fun A hA hM => hull_least X A hA hM,
    fun hfin => ⟨pruned_equiv X hfin, pruned_relMono X hfin,
      fun i => ⟨pruned_sub X i, (pruned_equiv X hfin i).1, pruned_least X i⟩⟩⟩

/-! ### The transformed carrier is an ordered specification -/

/-- Down-closure. -/
def down (A : O → Prop) : O → Prop := fun o => ∃ a, A a ∧ o ≼ a

theorem hoare_iff_down (A B : O → Prop) : HoareLe A B ↔ ∀ o, down A o → down B o := by
  constructor
  · rintro h o ⟨a, ha, hoa⟩
    obtain ⟨b, hb, hab⟩ := h a ha
    exact ⟨b, hb, PO.trans hoa hab⟩
  · intro h a ha
    exact h a ⟨a, ha, PO.refl a⟩

/-- Canonical representatives of `(𝒫(O)∖{∅})/≡_H`: nonempty down-closed sets. -/
structure HClass (O : Type) [PO O] where
  D : O → Prop
  ne : ∃ o, D o
  closed : ∀ o o', D o' → o ≼ o' → D o

instance : PO (HClass O) where
  le A B := ∀ o, A.D o → B.D o
  refl _ _ h := h
  trans h1 h2 o h := h2 o (h1 o h)
  antisymm := by
    intro A B h1 h2
    have hD : A.D = B.D := funext fun o => propext ⟨h1 o, h2 o⟩
    cases A; cases B
    simp only at hD
    subst hD
    rfl

/-- The class of a nonempty set. -/
def HClass.of (A : O → Prop) (h : ∃ o, A o) : HClass O where
  D := down A
  ne := let ⟨o, ho⟩ := h; ⟨o, o, ho, PO.refl o⟩
  closed := fun _ _ ⟨a, ha, h'⟩ h => ⟨a, ha, PO.trans h h'⟩

/-- The transformed specification `i ↦ [X̂(i)]`: functional by construction. -/
def hullSpec (sp : Spec I O) : Spec I (HClass O) where
  S i c := c = HClass.of (hull sp.S i)
    (let ⟨o, ho⟩ := sp.total i; ⟨o, i, PO.refl i, ho⟩)
  total i := ⟨_, rfl⟩

theorem hullSpec_functional (sp : Spec I O) : (hullSpec sp).Functional := by
  intro i o o' h h'
  exact h.trans h'.symm

theorem hullSpec_mono (sp : Spec I O) : (hullSpec sp).MonotoneF := by
  intro i j o u hij ho hu
  subst ho; subst hu
  exact (hoare_iff_down _ _).1 (hull_relMono sp.S i j hij)

/-- The remembered-output specification is consistent (Functional CALM). -/
theorem hullSpec_consistent (sp : Spec I O) : (hullSpec sp).Consistent :=
  consistent_of_mono (hullSpec_mono sp)

end Hull

/-! ### Table `tab:lookup-lift`: input and output posets -/

section Lookup

inductive LIn | i0 | i1

def LIn.le : LIn → LIn → Prop
  | .i1, .i0 => False
  | _, _ => True

instance : PO LIn where
  le := LIn.le
  refl x := by cases x <;> trivial
  trans {x y z} h1 h2 := by cases x <;> cases y <;> cases z <;> simp_all [LIn.le]
  antisymm {x y} h1 h2 := by cases x <;> cases y <;> simp_all [LIn.le]

/-- `o_a`, `o_b`, `o_{a⇝b}`; Eq. `lookup-output-dominance`. -/
inductive LOut | a | b | ab

def LOut.le (x y : LOut) : Prop := x = y ∨ y = .ab

instance : PO LOut where
  le := LOut.le
  refl x := Or.inl rfl
  trans {x y z} h1 h2 := by cases x <;> cases y <;> cases z <;> simp_all [LOut.le]
  antisymm {x y} h1 h2 := by cases x <;> cases y <;> simp_all [LOut.le]

end Lookup

/-! ## Persistent forwarding (Prop. `prop:persistent-forwarding`) -/

section Forwarding
variable {K P : Type}

/-- A structure snapshot: key-directed search edges and current occurrences. -/
structure Snap (K P : Type) where
  edge : K → P → P → Prop
  occ : K → P → Prop

/-- Finite key-directed search paths. -/
inductive Path (G : Snap K P) (k : K) : P → P → Prop
  | refl (p : P) : Path G k p p
  | step {p q r : P} : G.edge k p q → Path G k q r → Path G k p r

theorem Path.trans {G : Snap K P} {k : K} {p q r : P}
    (h1 : Path G k p q) (h2 : Path G k q r) : Path G k p r := by
  induction h1 with
  | refl => exact h2
  | step he _ ih => exact Path.step he (ih h2)

/-- Positive forward-reachability claims `(k, p)`. -/
def claims (G : Snap K P) (k : K) (p : P) : Prop := ∃ q, Path G k p q ∧ G.occ k q

/-- Obligations 2 and 3 of a restructuring step (obligation 1, stable
identities, holds because positions live in the fixed type `P`). -/
structure Obligations (G G' : Snap K P) : Prop where
  edges : ∀ k p q, G.edge k p q → Path G' k p q
  occs : ∀ k p, G.occ k p → ∃ q, Path G' k p q ∧ G'.occ k q

theorem Path.simulate {G G' : Snap K P} (hO : Obligations G G') {k : K} {p q : P}
    (h : Path G k p q) : Path G' k p q := by
  induction h with
  | refl p => exact Path.refl p
  | step he _ ih => exact (hO.edges _ _ _ he).trans ih

/-- One restructuring step preserves every positive claim. -/
theorem claims_step {G G' : Snap K P} (hO : Obligations G G') {k : K} {p : P}
    (h : claims G k p) : claims G' k p := by
  obtain ⟨q, hpq, hocc⟩ := h
  obtain ⟨q', hqq', hocc'⟩ := hO.occs k q hocc
  exact ⟨q', (hpq.simulate hO).trans hqq', hocc'⟩

inductive Chain (st : Snap K P → Snap K P → Prop) : Snap K P → List (Snap K P) → Prop
  | nil (g : Snap K P) : Chain st g []
  | cons {g g' : Snap K P} {l : List (Snap K P)} : st g g' → Chain st g' l → Chain st g (g' :: l)

/-- The current snapshot after a history. -/
def lastSnap : Snap K P → List (Snap K P) → Snap K P
  | g, [] => g
  | _, g :: l => lastSnap g l

theorem chain_append {st : Snap K P → Snap K P → Prop} :
    ∀ {g : Snap K P} (l t : List (Snap K P)), Chain st g (l ++ t) → Chain st (lastSnap g l) t
  | _, [], _, h => h
  | _, _ :: l, t, h => by
    cases h with
    | cons _ h' => exact chain_append l t h'

theorem chain_claims {st : Snap K P → Snap K P → Prop}
    (hst : ∀ G G', st G G' → Obligations G G') {g : Snap K P} {t : List (Snap K P)}
    (h : Chain st g t) {k : K} {p : P} (hc : claims g k p) : claims (lastSnap g t) k p := by
  induction h with
  | nil => exact hc
  | cons hs _ ih => exact ih (claims_step (hst _ _ hs) hc)

/-- A restructuring algorithm: an initial snapshot and legal steps, each
satisfying the obligations. -/
structure Restructuring (K P : Type) where
  init : Snap K P
  step : Snap K P → Snap K P → Prop
  oblig : ∀ G G', step G G' → Obligations G G'

/-- Inputs: finite legal restructuring histories. -/
def Restructuring.Hist (Rs : Restructuring K P) : Type :=
  {l : List (Snap K P) // Chain Rs.step Rs.init l}

/-- Inputs are ordered by prefix extension. -/
instance (Rs : Restructuring K P) : PO Rs.Hist where
  le h h' := ∃ t, h.1 ++ t = h'.1
  refl h := ⟨[], List.append_nil _⟩
  trans := by
    rintro a b c ⟨t, h1⟩ ⟨t', h2⟩
    exact ⟨t ++ t', by rw [← List.append_assoc, h1, h2]⟩
  antisymm := by
    rintro a b ⟨t, h⟩ ⟨t', h'⟩
    have hl := congrArg List.length h
    have hl' := congrArg List.length h'
    simp only [List.length_append] at hl hl'
    have : t = [] := by
      cases t with
      | nil => rfl
      | cons _ _ => simp at hl; omega
    subst this
    exact Subtype.ext (by simpa using h)

/-- `R(h)`: claims valid in the current snapshot of `h`. -/
def Restructuring.R (Rs : Restructuring K P) (h : Rs.Hist) : K → P → Prop :=
  claims (lastSnap Rs.init h.1)

/-- **Proposition `prop:persistent-forwarding`** (first claim). -/
theorem persistent_forwarding (Rs : Restructuring K P) {h h' : Rs.Hist} (hle : h ≼ h') :
    ∀ k p, Rs.R h k p → Rs.R h' k p := by
  intro k p hc
  obtain ⟨t, ht⟩ := hle
  have hch : Chain Rs.step Rs.init (h.1 ++ t) := by rw [ht]; exact h'.2
  have := chain_claims Rs.oblig (chain_append h.1 t hch) hc
  unfold Restructuring.R
  rw [← ht]
  have e : ∀ (g : Snap K P) (l t : List (Snap K P)),
      lastSnap g (l ++ t) = lastSnap (lastSnap g l) t := by
    intro g l t
    induction l generalizing g with
    | nil => rfl
    | cons x l ih => exact ih x
  rw [e]
  exact this

/-- Claim sets ordered by inclusion. -/
structure ClaimSet (K P : Type) where
  mem : K → P → Prop

instance : PO (ClaimSet K P) where
  le A B := ∀ k p, A.mem k p → B.mem k p
  refl _ _ _ h := h
  trans h1 h2 k p h := h2 k p (h1 k p h)
  antisymm := by
    intro A B h1 h2
    have : A.mem = B.mem := funext fun k => funext fun p => propext ⟨h1 k p, h2 k p⟩
    cases A; cases B; simp only at this; subst this; rfl

/-- The functional specification `h ↦ R(h)`. -/
def fwdSpec (Rs : Restructuring K P) : Spec Rs.Hist (ClaimSet K P) where
  S h c := c = ⟨Rs.R h⟩
  total h := ⟨_, rfl⟩

theorem fwdSpec_mono (Rs : Restructuring K P) : (fwdSpec Rs).MonotoneF := by
  intro h h' c c' hle hc hc'
  subst hc; subst hc'
  exact persistent_forwarding Rs hle

/-- **Proposition `prop:persistent-forwarding`** (second claim): by
Functional CALM the forwarding specification is consistent. -/
theorem fwdSpec_consistent (Rs : Restructuring K P) : (fwdSpec Rs).Consistent :=
  consistent_of_mono (fwdSpec_mono Rs)

theorem fwdSpec_functional (Rs : Restructuring K P) : (fwdSpec Rs).Functional :=
  fun _ _ _ h h' => h.trans h'.symm

/-- A type with the discrete (equality) order. -/
structure Disc (α : Type) where
  val : α

instance (α : Type) : PO (Disc α) where
  le a b := a = b
  refl _ := rfl
  trans h1 h2 := h1.trans h2
  antisymm h _ := h

/-- Eq. `forwarding-hull`: if each fiber `X(g)` consists of claims valid at
`g` (e.g. the exact claims), then under the equality order
`X̂(h) ⊑_H R(h)`. -/
theorem forwarding_hull (Rs : Restructuring K P) (X : Table Rs.Hist (Disc (K × P)))
    (hX : ∀ g c, X g c → Rs.R g c.val.1 c.val.2) (h : Rs.Hist) :
    HoareLe (hull X h) (fun c => Rs.R h c.val.1 c.val.2) := by
  rintro c ⟨g, hg, hx⟩
  exact ⟨c, persistent_forwarding Rs hg _ _ (hX g c hx), PO.refl c⟩

end Forwarding

/-! ## A one-point poset (used by `Appendix/ProductFrontier.lean`) -/

inductive One | pt

instance : PO One where
  le _ _ := True
  refl _ := trivial
  trans _ _ := trivial
  antisymm {a b} _ _ := by cases a; cases b; rfl


/-! ## Table `tab:lookup-lift` as printed, the Hoare quotient, and Eq. `forwarding-hull` via Eq. `hull-coverage` -/

section HullD
open CC.Front

/-- Table `tab:lookup-lift`: `X(i₀) = {o_a}`, `X(i₁) = {o_b}`. -/
def lookupX : Table LIn LOut
  | .i0, o => o = .a
  | .i1, o => o = .b

theorem lookup_hull_i0 (o : LOut) : hull lookupX .i0 o ↔ o = .a := by
  constructor
  · rintro ⟨j, hj, hx⟩
    cases j
    · exact hx
    · exact absurd hj (by simp [PO.le, LIn.le])
  · rintro rfl; exact ⟨.i0, PO.refl _, rfl⟩

theorem lookup_hull_i1 (o : LOut) : hull lookupX .i1 o ↔ (o = .a ∨ o = .b) := by
  constructor
  · rintro ⟨j, _, hx⟩
    cases j
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (rfl | rfl)
    · exact ⟨.i0, trivial, rfl⟩
    · exact ⟨.i1, trivial, rfl⟩

/-- Both remembered outputs are maximal: `M = X̂`. -/
theorem lookup_pruned (i : LIn) (o : LOut) : pruned lookupX i o ↔ hull lookupX i o := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun o' ho' hle => ?_⟩⟩
  have hab : ∀ x : LOut, hull lookupX i x → x = .a ∨ x = .b := by
    intro x hx
    cases i
    · exact Or.inl ((lookup_hull_i0 x).1 hx)
    · exact (lookup_hull_i1 x).1 hx
  rcases hab o h with rfl | rfl <;> rcases hab o' ho' with rfl | rfl <;>
    first | rfl | (exfalso; revert hle; simp [PO.le, LOut.le])

/-- `X` violates Relational Monotonicity. -/
theorem lookup_not_relMono : ¬ HRelMono lookupX := by
  intro h
  obtain ⟨x, hb, hab⟩ := h .i0 .i1 trivial .a rfl
  have : x = .b := hb
  subst this
  revert hab; simp [PO.le, LOut.le]

/-- Forwarding: `A(i₀) = {o_a}`, `A(i₁) = {o_{a⇝b}}`. -/
def fwdA : Table LIn LOut
  | .i0, o => o = .a
  | .i1, o => o = .ab

theorem fwdA_relaxation : Relaxation lookupX fwdA := by
  intro i o ho
  cases i
  · exact ⟨.a, rfl, ho ▸ PO.refl _⟩
  · exact ⟨.ab, rfl, Or.inr rfl⟩

theorem fwdA_relMono : HRelMono fwdA := by
  intro i k hik o ho
  cases i <;> cases k
  · exact ⟨o, ho, PO.refl o⟩
  · exact ⟨.ab, rfl, Or.inr rfl⟩
  · exact absurd hik (by simp [PO.le, LIn.le])
  · exact ⟨o, ho, PO.refl o⟩

/-- Eq. `hull-coverage` places `X̂` below forwarding:
`{o_a, o_b} ⊑_H {o_{a⇝b}}`. -/
theorem lookup_hull_le_fwd : HoareLe (hull lookupX .i1) (fwdA .i1) :=
  hull_least _ _ fwdA_relaxation fwdA_relMono .i1

/-! ### The quotient `(𝒫(O)∖{∅})/≡_H` -/

theorem hclass_of_le_iff {O : Type} [PO O] (A B : O → Prop) (ha : ∃ o, A o) (hb : ∃ o, B o) :
    HClass.of A ha ≼ HClass.of B hb ↔ HoareLe A B :=
  (hoare_iff_down A B).symm

theorem hclass_of_eq_iff {O : Type} [PO O] (A B : O → Prop) (ha : ∃ o, A o) (hb : ∃ o, B o) :
    HClass.of A ha = HClass.of B hb ↔ (HoareLe A B ∧ HoareLe B A) := by
  constructor
  · intro e
    exact ⟨(hclass_of_le_iff A B ha hb).1 (e ▸ PO.refl _),
      (hclass_of_le_iff B A hb ha).1 (e ▸ PO.refl _)⟩
  · rintro ⟨h1, h2⟩
    exact PO.antisymm ((hclass_of_le_iff A B ha hb).2 h1) ((hclass_of_le_iff B A hb ha).2 h2)

/-- Every class is the class of a set. -/
theorem hclass_eq_of {O : Type} [PO O] (c : HClass O) : c = HClass.of c.D c.ne :=
  PO.antisymm (fun o h => ⟨o, h, PO.refl o⟩) (fun _ ⟨a, ha, h⟩ => c.closed _ a ha h)

/-! ### Eq. `forwarding-hull` via Eq. `hull-coverage` -/

/-- Under the equality order, `⊑_H` is inclusion. -/
theorem disc_hoare_iff {β : Type} (A B : Disc β → Prop) : HoareLe A B ↔ ∀ c, A c → B c :=
  ⟨fun h c hc => let ⟨b, hb, e⟩ := h c hc; (e : c = b) ▸ hb, HoareLe.of_sub⟩

theorem forwarding_hull_via_coverage {K P : Type} (Rs : Restructuring K P)
    (X : Table Rs.Hist (Disc (K × P))) (hX : ∀ g c, X g c → Rs.R g c.val.1 c.val.2)
    (h : Rs.Hist) : ∀ c, hull X h c → Rs.R h c.val.1 c.val.2 := by
  let C : Table Rs.Hist (Disc (K × P)) := fun g c => Rs.R g c.val.1 c.val.2
  have hrel : Relaxation X C := fun g => HoareLe.of_sub (hX g)
  have hmono : HRelMono C := fun g g' hle =>
    HoareLe.of_sub fun c hc => persistent_forwarding Rs hle _ _ hc
  exact (disc_hoare_iff _ _).1 (hull_least X C hrel hmono h)

end HullD

end Front
end CC

