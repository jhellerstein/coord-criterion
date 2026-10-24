/-
# Coordination-free frontiers (Appendix `sec:frontiers`)

Formalizes, on top of `Core`, `Runs` and `FunctionalCALM`:

* Theorem `thm:monotone-hull` (remembered-output frontier):
  `hull_relaxation`, `hull_relMono`, `hull_least`, and the finite pruning
  clause `pruned_equiv`, `pruned_relaxation`, `pruned_relMono`,
  `pruned_least`, `pruned_unique` (bundled as `monotone_hull`);
  the transformed specification on Hoare classes is functional and
  monotone, hence consistent (`hullSpec_consistent`);
  the lookup table `tab:lookup-lift` (`lookup_hull`, `lookup_pruned`).
* Proposition `prop:persistent-forwarding`: `persistent_forwarding`,
  `fwdSpec_consistent`, and Eq. `forwarding-hull` (`forwarding_hull`).
* Theorem `thm:product-frontier`: the product interface is monotone across
  partitions (`product_monoAcross`), hence passes the survivor test for
  every separable family (`product_partition_compat`); every strict,
  normalized, locally conservative strengthening is not monotone across
  partitions (`strengthening_not_monoAcross`); the two-replica
  configuration example (`config_product_ok`, `config_product_not_liftedMono`,
  `config_agreement_not_ok`), and a counterexample showing that the owner map
  must be injective (`agreement_ok_sole_owner`).
  Along the way: Def. `def:monotone-across-partitions` and the family-level
  content of Prop. `thm:complete-cap-deployment` (`partition_compat_iff`).

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
5. *Deployments and partitions.*  Participants are `Fin n`; a deployment is
   `A : Fin n → Table I O`; a partition is a labelling `comp : Fin n → Nat`
   with at least two distinct labels (as in `CompleteCAP`).  A participant
   run family is `Fin n → Option PRun` (absent participants are `none`), each
   run a canonical execution; its emitted rows are computed by `rowsOf`,
   pairing each output event with the current input at that point.
   "Emitted rows occur in at least two components" is read as "two
   participants in different components each emit a row".
6. *Product interface.*  Coordinates are the participants (the paper's
   `∏_{p∈P} V_p(i)`); for simplicity every coordinate has the same value
   type `W` (a sum type embeds the general case).  Partial tuples are
   `Fin n → Option W`, ordered coordinate-wise with `none` below
   everything.  The owner deployment lets `p` emit exactly the rows of the
   specification whose defined coordinates are all `p`.
7. *Maximality of complete views* is used only in the weaker form
   "the views `V_p(i)` at one input form an antichain" (`Antichain`).
-/
import CoordCriterion.Core
import CoordCriterion.Runs
import CoordCriterion.FunctionalCALM

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

/-! ### Table `tab:lookup-lift` -/

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

/-- The original fibers `X(i₀) = {o_a}`, `X(i₁) = {o_b, o_{a⇝b}}`. -/
def lookupX : Table LIn LOut
  | .i0, o => o = .a
  | .i1, o => o = .b ∨ o = .ab

theorem lookup_hull_i0 (o : LOut) : hull lookupX .i0 o ↔ o = .a := by
  constructor
  · rintro ⟨j, hj, hx⟩
    cases j
    · exact hx
    · exact absurd hj (by simp [PO.le, LIn.le])
  · rintro rfl; exact ⟨.i0, PO.refl _, rfl⟩

theorem lookup_hull_i1 (o : LOut) : hull lookupX .i1 o ↔ (o = .a ∨ o = .b ∨ o = .ab) := by
  constructor
  · rintro ⟨j, _, hx⟩
    cases j <;> cases o <;> simp_all [lookupX]
  · intro h
    rcases h with rfl | rfl | rfl
    · exact ⟨.i0, trivial, rfl⟩
    · exact ⟨.i1, trivial, Or.inl rfl⟩
    · exact ⟨.i1, trivial, Or.inr rfl⟩

theorem lookup_pruned_i0 (o : LOut) : pruned lookupX .i0 o ↔ o = .a := by
  constructor
  · intro h; exact (lookup_hull_i0 o).1 h.1
  · rintro rfl
    refine ⟨(lookup_hull_i0 _).2 rfl, fun o ho _ => (lookup_hull_i0 o).1 ho⟩

theorem lookup_pruned_i1 (o : LOut) : pruned lookupX .i1 o ↔ o = .ab := by
  constructor
  · rintro ⟨_, hmax⟩
    have hab : hull lookupX .i1 .ab := (lookup_hull_i1 _).2 (Or.inr (Or.inr rfl))
    exact (hmax .ab hab (Or.inr rfl)).symm
  · rintro rfl
    refine ⟨(lookup_hull_i1 _).2 (Or.inr (Or.inr rfl)), fun o _ h => ?_⟩
    rcases h with h | h
    · exact h.symm
    · exact h

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

/-! ## Deployments, run families, monotonicity across partitions -/

section Deploy
variable {I O : Type} [PO I] [PO O] {n : Nat}

/-- Rows `(current input, output)` emitted along an event list. -/
def rowsOf : I → List (Event I O) → List (I × O)
  | _, [] => []
  | _, .input j :: es => rowsOf j es
  | i, .output o :: es => (i, o) :: rowsOf i es

theorem mem_outs_of_rowsOf : ∀ (i : I) (es : List (Event I O)) {r : I × O},
    r ∈ rowsOf i es → r.2 ∈ outs es
  | _, [], _, h => absurd h List.not_mem_nil
  | _, .input j :: es, _, h => mem_outs_of_rowsOf j es h
  | i, .output o :: es, r, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_outs_of_rowsOf i es h)

theorem rowsOf_of_mem_outs : ∀ (i : I) (es : List (Event I O)) {o : O},
    o ∈ outs es → ∃ k, (k, o) ∈ rowsOf i es
  | _, [], _, h => absurd h List.not_mem_nil
  | _, .input j :: es, _, h => rowsOf_of_mem_outs j es h
  | i, .output o' :: es, o, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨i, List.mem_cons_self⟩
    · obtain ⟨k, hk⟩ := rowsOf_of_mem_outs i es h
      exact ⟨k, List.mem_cons_of_mem _ hk⟩

/-- A canonical participant run. -/
structure PRun (sp : Spec I O) where
  init : I
  es : List (Event I O)
  fin : State sp
  exec : Exec (canon sp init) es fin

/-- A finite participant run family (Def. `def:deployment`). -/
abbrev Family (sp : Spec I O) (n : Nat) := Fin n → Option (PRun sp)

def Family.rows {sp : Spec I O} (F : Family sp n) (p : Fin n) : List (I × O) :=
  match F p with
  | none => []
  | some ρ => rowsOf ρ.init ρ.es

theorem Family.rows_some {sp : Spec I O} {F : Family sp n} {p : Fin n} {ρ : PRun sp}
    (hp : F p = some ρ) : F.rows p = rowsOf ρ.init ρ.es := by
  simp [Family.rows, hp]

theorem Family.rows_none {sp : Spec I O} {F : Family sp n} {p : Fin n}
    (hp : F p = none) : F.rows p = [] := by
  simp [Family.rows, hp]

/-- Every emitted row of `p` lies in `A_p`. -/
def Family.Authorized {sp : Spec I O} (A : Fin n → Table I O) (F : Family sp n) : Prop :=
  ∀ p r, r ∈ F.rows p → A p r.1 r.2

/-- A partition: at least two nonempty components. -/
def IsPartition (comp : Fin n → Nat) : Prop := ∃ p q, comp p ≠ comp q

/-- Separable under `comp` (Def. `def:deployment`). -/
def Family.Separable {sp : Spec I O} (F : Family sp n) (comp : Fin n → Nat) : Prop :=
  (∃ p q r r', r ∈ F.rows p ∧ r' ∈ F.rows q ∧ comp p ≠ comp q) ∨
  (∃ p r, r ∈ F.rows p ∧ (∀ q r', r' ∈ F.rows q → q = p ∧ r' = r) ∧
    ∃ q ρ, F q = some ρ ∧ F.rows q = [] ∧ comp q ≠ comp p)

/-- `j` is a common expansion of the family's current inputs. -/
def Family.Below {sp : Spec I O} (F : Family sp n) (j : I) : Prop :=
  ∀ p ρ, F p = some ρ → ρ.fin.cur ≼ j

/-- Def. `def:monotone-across-partitions`, for one partition. -/
def MonoAcross (sp : Spec I O) (A : Fin n → Table I O) (comp : Fin n → Nat) : Prop :=
  ∀ F : Family sp n, F.Authorized A → F.Separable comp → ∀ j, F.Below j →
    ∃ u, sp.S j u ∧ ∀ p r, r ∈ F.rows p → r.2 ≼ u

/-- Def. `def:monotone-across-partitions`. -/
def MonoAcrossPartitions (sp : Spec I O) (A : Fin n → Table I O) : Prop :=
  ∀ comp, IsPartition comp → MonoAcross sp A comp

/-- Survivor form: a common expansion of the emitted outputs at `j` is the
same as a row at `j` surviving in every final remainder table. -/
theorem family_survivor {sp : Spec I O} (F : Family sp n) (j : I) (hj : F.Below j) :
    (∃ u, sp.S j u ∧ ∀ p r, r ∈ F.rows p → r.2 ≼ u) ↔
      ∃ u, sp.S j u ∧ ∀ p ρ, F p = some ρ → ρ.fin.R j u := by
  constructor
  · rintro ⟨u, hu, hall⟩
    refine ⟨u, hu, fun p ρ hp => (run_residual ρ.exec j u).2 ⟨hu, hj p ρ hp, ?_⟩⟩
    intro o ho
    obtain ⟨k, hk⟩ := rowsOf_of_mem_outs ρ.init ρ.es ho
    exact hall p (k, o) (by rw [Family.rows_some hp]; exact hk)
  · rintro ⟨u, hu, hall⟩
    refine ⟨u, hu, fun p r hr => ?_⟩
    cases hp : F p with
    | none => rw [Family.rows_none hp] at hr; exact absurd hr List.not_mem_nil
    | some ρ =>
      rw [Family.rows_some hp] at hr
      exact ((run_residual ρ.exec j u).1 (hall p ρ hp)).2.2 _ (mem_outs_of_rowsOf _ _ hr)

/-- Surviving rows give confluence of the family's runs at `j`. -/
theorem family_confluent {sp : Spec I O} (F : Family sp n) (j : I)
    (h : ∃ u, sp.S j u ∧ ∀ p ρ, F p = some ρ → ρ.fin.R j u) :
    ∃ τ : State sp, τ.cur = j ∧ ∀ p ρ, F p = some ρ → Reach ρ.fin τ := by
  obtain ⟨u, hu, hall⟩ := h
  exact ⟨meetState sp j u hu, rfl, fun p ρ hp => reach_meet (run_residual ρ.exec) (hall p ρ hp)⟩

/-- Family-level content of Prop. `thm:complete-cap-deployment`: monotone
across partitions iff every separable authorized family passes the survivor
test at every common expansion of its current inputs. -/
theorem partition_compat_iff (sp : Spec I O) (A : Fin n → Table I O) :
    MonoAcrossPartitions sp A ↔
      ∀ comp, IsPartition comp → ∀ F : Family sp n, F.Authorized A → F.Separable comp →
        ∀ j, F.Below j → ∃ u, sp.S j u ∧ ∀ p ρ, F p = some ρ → ρ.fin.R j u := by
  constructor
  · intro h comp hc F hA hS j hj
    exact (family_survivor F j hj).1 (h comp hc F hA hS j hj)
  · intro h comp hc F hA hS j hj
    exact (family_survivor F j hj).2 (h comp hc F hA hS j hj)

/-- The state after emitting `o` at the current input. -/
def emitState {sp : Spec I O} (σ : State sp) (o : O) (h : σ.R σ.cur o) : State sp where
  cur := σ.cur
  R := outputTable σ o
  sub := fun k u h => σ.sub k u h.1
  hasCur := ⟨o, h, PO.refl o⟩
  above := fun k u h => σ.above k u h.1

/-- The canonical run `canon i; output o`. -/
def emitRun (sp : Spec I O) (i : I) (o : O) (h : sp.S i o) : PRun sp where
  init := i
  es := [.output o]
  fin := emitState (canon sp i) o ⟨h, PO.refl i⟩
  exec := Exec.cons (Step.output (canon sp i) (emitState (canon sp i) o ⟨h, PO.refl i⟩) o
    ⟨h, PO.refl i⟩ rfl rfl) (Exec.nil _)

end Deploy

/-! ## Independent-product frontier (Theorem `thm:product-frontier`) -/

section Product
variable {I W : Type} [PO I] [PO W] {n : Nat}

def OptLe : Option W → Option W → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => a ≼ b

/-- Partial tuples over the participants' coordinates. -/
structure PT (W : Type) (n : Nat) where
  t : Fin n → Option W

instance : PO (PT W n) where
  le x y := ∀ p, OptLe (x.t p) (y.t p)
  refl x p := by
    cases x.t p with
    | none => trivial
    | some a => exact PO.refl a
  trans {x y z} h1 h2 p := by
    have a1 := h1 p
    have a2 := h2 p
    revert a1 a2
    cases x.t p <;> cases y.t p <;> cases z.t p <;> simp [OptLe] <;> exact PO.trans
  antisymm {x y} h1 h2 := by
    have : x.t = y.t := by
      funext p
      have a1 := h1 p
      have a2 := h2 p
      revert a1 a2
      cases x.t p <;> cases y.t p <;> simp [OptLe]
      exact PO.antisymm
    cases x; cases y; simp only at this; subst this; rfl

/-- `x` is a restriction of the complete tuple `y`. -/
def Restr (x : PT W n) (y : Fin n → W) : Prop := ∀ p, x.t p = none ∨ x.t p = some (y p)

/-- The product interface: restrictions of tuples in `∏_p V_p(i)`. -/
def prodTable (V : Fin n → I → W → Prop) : Table I (PT W n) :=
  fun i x => ∃ y, (∀ p, V p i (y p)) ∧ Restr x y

/-- Local view hypotheses: views exist, and continue as input grows. -/
structure Views (V : Fin n → I → W → Prop) : Prop where
  nonempty : ∀ p i, ∃ v, V p i v
  cont : ∀ p i j v, i ≼ j → V p i v → ∃ w, V p j w ∧ v ≼ w

/-- Complete views at one input are pairwise incomparable (implied by
"complete views are maximal"). -/
def Antichain (V : Fin n → I → W → Prop) : Prop :=
  ∀ p i v w, V p i v → V p i w → v ≼ w → v = w

def prodSpec (V : Fin n → I → W → Prop) (hV : Views V) : Spec I (PT W n) where
  S := prodTable V
  total i := ⟨⟨fun _ => none⟩, fun p => Classical.choose (hV.nonempty p i),
    fun p => Classical.choose_spec (hV.nonempty p i), fun _ => Or.inl rfl⟩

/-- The owner deployment: `p` may emit exactly the rows whose defined
coordinates are all `p`. -/
def ownerDep (sp : Spec I (PT W n)) : Fin n → Table I (PT W n) :=
  fun p i x => sp.S i x ∧ ∀ q v, x.t q = some v → q = p

/-- Every owner-authorized family (separable or not) has a common expansion
in the product interface. -/
theorem product_common (V : Fin n → I → W → Prop) (hV : Views V)
    (F : Family (prodSpec V hV) n) (hA : F.Authorized (ownerDep (prodSpec V hV)))
    (j : I) (hj : F.Below j) :
    ∃ u, (prodSpec V hV).S j u ∧ ∀ p r, r ∈ F.rows p → r.2 ≼ u := by
  have key : ∀ p, ∃ w, V p j w ∧ ∀ r, r ∈ F.rows p → ∀ v, r.2.t p = some v → v ≼ w := by
    intro p
    cases hp : F p with
    | none =>
      obtain ⟨w, hw⟩ := hV.nonempty p j
      refine ⟨w, hw, fun r hr => ?_⟩
      rw [Family.rows_none hp] at hr; exact absurd hr List.not_mem_nil
    | some ρ =>
      obtain ⟨u, hu⟩ := ρ.fin.hasCur
      have hres := (run_residual ρ.exec _ _).1 hu
      obtain ⟨y, hy, hyu⟩ := hres.1
      obtain ⟨w, hw, hyw⟩ := hV.cont p _ _ _ (hj p ρ hp) (hy p)
      refine ⟨w, hw, fun r hr v hv => ?_⟩
      rw [Family.rows_some hp] at hr
      have hle : r.2 ≼ u := hres.2.2 _ (mem_outs_of_rowsOf _ _ hr)
      have h1 : OptLe (r.2.t p) (u.t p) := hle p
      rw [hv] at h1
      rcases hyu p with h0 | h0 <;> rw [h0] at h1
      · exact False.elim h1
      · exact PO.trans h1 hyw
  let w : Fin n → W := fun p => Classical.choose (key p)
  have hw : ∀ p, V p j (w p) ∧ ∀ r, r ∈ F.rows p → ∀ v, r.2.t p = some v → v ≼ w p :=
    fun p => Classical.choose_spec (key p)
  refine ⟨⟨fun p => some (w p)⟩, ⟨w, fun p => (hw p).1, fun _ => Or.inr rfl⟩, ?_⟩
  intro q r hr p
  show OptLe (r.2.t p) (some (w p))
  cases h : r.2.t p with
  | none => trivial
  | some v =>
    have hpq : p = q := (hA q r hr).2 p v h
    subst hpq
    exact (hw p).2 r hr v h

/-- **Theorem `thm:product-frontier`**, first part: the product interface is
monotone across partitions under the owner deployment. -/
theorem product_monoAcross (V : Fin n → I → W → Prop) (hV : Views V) :
    MonoAcrossPartitions (prodSpec V hV) (ownerDep (prodSpec V hV)) :=
  fun _ _ F hA _ j hj => product_common V hV F hA j hj

/-- ... hence (Prop. `thm:complete-cap-deployment`, family level) every
authorized family's runs share a surviving row and are confluent at every
common expansion `j`. -/
theorem product_partition_compat (V : Fin n → I → W → Prop) (hV : Views V)
    (F : Family (prodSpec V hV) n) (hA : F.Authorized (ownerDep (prodSpec V hV)))
    (j : I) (hj : F.Below j) :
    ∃ τ : State (prodSpec V hV), τ.cur = j ∧ ∀ p ρ, F p = some ρ → Reach ρ.fin τ :=
  family_confluent F j ((family_survivor F j hj).1 (product_common V hV F hA j hj))

/-- A normalized strengthening: selected complete product tuples, with
exactly their restrictions as rows. -/
structure NormStr (V : Fin n → I → W → Prop) where
  sel : I → (Fin n → W) → Prop
  sub : ∀ i y, sel i y → ∀ p, V p i (y p)

def NormStr.table {V : Fin n → I → W → Prop} (T : NormStr V) : Table I (PT W n) :=
  fun i x => ∃ y, T.sel i y ∧ Restr x y

theorem NormStr.table_sub {V : Fin n → I → W → Prop} (T : NormStr V) :
    ∀ i x, T.table i x → prodTable V i x :=
  fun i _ ⟨y, hy, hr⟩ => ⟨y, T.sub i y hy, hr⟩

/-- Local conservativity: each coordinate's projection is all of `V_p(i)`. -/
def NormStr.LocCons {V : Fin n → I → W → Prop} (T : NormStr V) : Prop :=
  ∀ i p v, V p i v → ∃ y, T.sel i y ∧ y p = v

/-- Strictness: some product row is removed. -/
def NormStr.Strict {V : Fin n → I → W → Prop} (T : NormStr V) : Prop :=
  ∃ i x, prodTable V i x ∧ ¬ T.table i x

/-- The singleton partial tuple `p ↦ v`. -/
def single (p : Fin n) (v : W) : PT W n := ⟨fun q => if q = p then some v else none⟩

/-- **Theorem `thm:product-frontier`**, second part: every strict,
normalized, locally conservative strengthening is not monotone across
partitions (under its owner deployment). -/
theorem strengthening_not_monoAcross (V : Fin n → I → W → Prop) (hAC : Antichain V)
    (T : NormStr V) (sp : Spec I (PT W n)) (hsp : ∀ i x, sp.S i x ↔ T.table i x)
    (hLC : T.LocCons) (hst : T.Strict) :
    ¬ MonoAcrossPartitions sp (ownerDep sp) := by
  intro hM
  obtain ⟨i, x, ⟨y, hyV, hxy⟩, hnot⟩ := hst
  have hny : ¬ T.sel i y := fun hs => hnot ⟨y, hs, hxy⟩
  have hsing : ∀ p, sp.S i (single p (y p)) := by
    intro p
    obtain ⟨z, hz, hzp⟩ := hLC i p (y p) (hyV p)
    refine (hsp _ _).2 ⟨z, hz, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq; right; simp [single, hzp]
    · left; simp [single, hq]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- Fewer than two participants: no strict locally conservative strengthening.
    have : ∃ z, T.sel i z ∧ ∀ p, z p = y p := by
      rcases Nat.lt_or_ge n 1 with h0 | h1
      · obtain ⟨u, hu⟩ := sp.total i
        obtain ⟨z, hz, _⟩ := (hsp _ _).1 hu
        exact ⟨z, hz, fun p => absurd p.2 (by omega)⟩
      · let p0 : Fin n := ⟨0, by omega⟩
        obtain ⟨z, hz, hzp⟩ := hLC i p0 (y p0) (hyV p0)
        refine ⟨z, hz, fun p => ?_⟩
        have : p = p0 := Fin.ext (by have := p.2; simp [p0]; omega)
        subst this; exact hzp
    obtain ⟨z, hz, hzy⟩ := this
    exact hny (by have : z = y := funext hzy; rw [← this]; exact hz)
  · let comp : Fin n → Nat := fun p => p.val
    let p0 : Fin n := ⟨0, by omega⟩
    let p1 : Fin n := ⟨1, by omega⟩
    have hpart : IsPartition comp := ⟨p0, p1, by simp [comp, p0, p1]⟩
    let F : Family sp n := fun p => some (emitRun sp i (single p (y p)) (hsing p))
    have hrows : ∀ p, F.rows p = [(i, single p (y p))] := fun p => by
      simp [Family.rows, F, emitRun, rowsOf]
    have hAuth : F.Authorized (ownerDep sp) := by
      intro p r hr
      rw [hrows p, List.mem_singleton] at hr
      subst hr
      refine ⟨hsing p, fun q v hq => ?_⟩
      by_cases h : q = p
      · exact h
      · simp [single, h] at hq
    have hSep : F.Separable comp :=
      Or.inl ⟨p0, p1, _, _, by rw [hrows]; exact List.mem_cons_self,
        by rw [hrows]; exact List.mem_cons_self, by simp [comp, p0, p1]⟩
    have hBelow : F.Below i := by
      intro p ρ hp
      cases hp
      exact PO.refl i
    obtain ⟨u, hu, hall⟩ := hM comp hpart F hAuth hSep i hBelow
    obtain ⟨z, hz, hzu⟩ := (hsp _ _).1 hu
    have hyz : ∀ p, y p = z p := by
      intro p
      have h1 : OptLe ((single p (y p)).t p) (u.t p) :=
        hall p (i, single p (y p)) (by rw [hrows]; exact List.mem_cons_self) p
      have e : (single p (y p)).t p = some (y p) := by simp [single]
      rw [e] at h1
      rcases hzu p with h0 | h0 <;> rw [h0] at h1
      · exact False.elim h1
      · exact hAC p i _ _ (hyV p) (T.sub i z hz p) h1
    exact hny (by have : y = z := funext hyz; rw [this]; exact hz)

end Product

/-! ### Example `product-config-example` -/

section Config

inductive One | pt

instance : PO One where
  le _ _ := True
  refl _ := trivial
  trans _ _ := trivial
  antisymm {a b} _ _ := by cases a; cases b; rfl

/-- Two replicas, each may expose configuration `false` (0) or `true` (1). -/
def cfgV : Fin 2 → One → Disc Bool → Prop := fun _ _ _ => True

theorem cfgV_views : Views cfgV :=
  ⟨fun _ _ => ⟨⟨false⟩, trivial⟩, fun _ _ _ v _ _ => ⟨v, trivial, PO.refl v⟩⟩

theorem cfgV_antichain : Antichain cfgV := fun _ _ _ _ _ _ h => h

/-- No cross-replica constraint: monotone across partitions. -/
theorem config_product_ok :
    MonoAcrossPartitions (prodSpec cfgV cfgV_views) (ownerDep (prodSpec cfgV cfgV_views)) :=
  product_monoAcross cfgV cfgV_views

/-- ... although the product is not monotone: two views of one replica are
incompatible, so the deployment is what makes it partition-compatible. -/
theorem config_product_not_liftedMono : ¬ (prodSpec cfgV cfgV_views).LiftedMono := by
  intro h
  let a : PT (Disc Bool) 2 := single 0 ⟨false⟩
  let b : PT (Disc Bool) 2 := single 0 ⟨true⟩
  have hrow : ∀ (v : Disc Bool), (prodSpec cfgV cfgV_views).S .pt (single 0 v) :=
    fun v => ⟨fun _ => v, fun _ => trivial, fun q => by
      by_cases hq : q = 0
      · subst hq; right; simp [single]
      · left; simp [single, hq]⟩
  obtain ⟨u, _, hu⟩ := h .pt .pt trivial [a, b] (by simp)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> exact hrow _)
  have ha : OptLe (a.t 0) (u.t 0) := hu a (by simp) 0
  have hb : OptLe (b.t 0) (u.t 0) := hu b (by simp) 0
  simp only [a, b, single, ite_true] at ha hb
  cases h0 : u.t 0 with
  | none => rw [h0] at ha; exact ha
  | some w =>
    rw [h0] at ha hb
    have : (⟨false⟩ : Disc Bool) = ⟨true⟩ := ha.trans hb.symm
    cases this

/-- The agreement strengthening keeps only `(0,0)` and `(1,1)`. -/
def agree : NormStr cfgV where
  sel _ y := y 0 = y 1
  sub _ _ _ _ := trivial

def agreeSpec : Spec One (PT (Disc Bool) 2) where
  S := agree.table
  total _ := ⟨⟨fun _ => none⟩, fun _ => ⟨false⟩, rfl, fun _ => Or.inl rfl⟩

theorem agree_locCons : agree.LocCons := fun _ _ v _ => ⟨fun _ => v, rfl, rfl⟩

theorem agree_strict : agree.Strict := by
  let y : Fin 2 → Disc Bool := fun p => ⟨p.val == 1⟩
  refine ⟨.pt, ⟨fun p => some (y p)⟩, ⟨y, fun _ => trivial, fun _ => Or.inr rfl⟩, ?_⟩
  rintro ⟨z, hz, hr⟩
  have e : ∀ p, z p = y p := by
    intro p
    rcases hr p with h | h
    · cases h
    · exact (Option.some.inj h).symm
  have : y 0 = y 1 := (e 0).symm.trans (hz.trans (e 1))
  simp [y] at this

/-- The agreement strengthening is not monotone across partitions. -/
theorem config_agreement_not_ok : ¬ MonoAcrossPartitions agreeSpec (ownerDep agreeSpec) :=
  strengthening_not_monoAcross cfgV cfgV_antichain agree agreeSpec (fun _ _ => Iff.rfl)
    agree_locCons agree_strict

/-- Ownership must be one coordinate per participant.  If participant `0`
owns *both* coordinates (participant `1` may emit only the empty tuple), the
same strict, locally conservative agreement strengthening *is* monotone
across partitions: no partition separates its two coordinates. -/
def soleOwnerDep : Fin 2 → Table One (PT (Disc Bool) 2) :=
  fun p i x => agreeSpec.S i x ∧ (p ≠ 0 → ∀ q, x.t q = none)

theorem agreement_ok_sole_owner : MonoAcrossPartitions agreeSpec soleOwnerDep := by
  intro comp _ F hA _ j _
  have hone : ∀ a b : One, a = b := by intro a b; cases a; cases b; rfl
  have hlow : ∀ p r u, r ∈ F.rows p → p ≠ 0 → r.2 ≼ u := by
    intro p r u hr hp q
    show OptLe (r.2.t q) (u.t q)
    rw [(hA p r hr).2 hp q]; trivial
  cases h0 : F 0 with
  | none =>
    refine ⟨⟨fun _ => none⟩, ⟨fun _ => ⟨false⟩, rfl, fun _ => Or.inl rfl⟩, fun p r hr => ?_⟩
    by_cases hp : p = 0
    · subst hp; rw [Family.rows_none h0] at hr; exact absurd hr List.not_mem_nil
    · exact hlow p r _ hr hp
  | some ρ =>
    obtain ⟨u, hu⟩ := ρ.fin.hasCur
    have hres := (run_residual ρ.exec _ _).1 hu
    have hj : ρ.fin.cur = j := hone _ _
    refine ⟨u, hj ▸ hres.1, fun p r hr => ?_⟩
    by_cases hp : p = 0
    · subst hp; rw [Family.rows_some h0] at hr
      exact hres.2.2 _ (mem_outs_of_rowsOf _ _ hr)
    · exact hlow p r _ hr hp

end Config

end Front
end CC

