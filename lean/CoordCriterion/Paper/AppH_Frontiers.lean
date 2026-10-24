import CoordCriterion.Appendix.Frontiers
import CoordCriterion.Appendix.ProductFrontier
import CoordCriterion.Appendix.Registers

/-!
# Paper, Appendix H: Coordination-Free Frontiers

Source: `appendices/frontiers.tex` (Appendix `sec:frontiers`).

How to read this file: open it beside the appendix.  Every numbered result
and every claim the text proves or justifies appears below in paper order,
under headers naming the paper's subsections.  Numbered results carry their
LaTeX label (`«thm:monotone-hull»`, `«prop:persistent-forwarding»`,
`«thm:product-frontier»`, equations `«eq:…»`, table `«tab:lookup-lift»`);
unlabeled inline claims are named `«sec:frontiers/<slug>»`.  Each docstring
quotes the paper (LaTeX lightly normalized to Unicode) and, where the Lean
statement reads differently, says how the two correspond.  Proofs are one-line
references to the library (`Appendix/Frontiers.lean`,
`Appendix/ProductFrontier.lean`, `Appendix/Registers.lean`).

Conventions: subsets of `O` are predicates `O → Prop`; a table is
`Table I O = I → O → Prop`, so `X i` is the fiber `X(i)`; `A ⊑_H B` is
`HoareLe A B`; finite sets are those enumerated by a list (`FiniteSet`).
-/

namespace CC
namespace Paper

open CC.Front CC.Deploy

set_option linter.unusedSectionVars false

/-! ## Appendix H: Coordination-Free Frontiers -/

/-! ### Remembered outputs -/

section Hull
variable {I O : Type} [PO I] [PO O]

/-- **Eq. `eq:lifted-output-order`** (Hoare preorder).  "For `A, B ⊆ O`,
`A ⊑_H B ⟺ ∀ a ∈ A ∃ b ∈ B : a ≼ b`." -/
theorem «eq:lifted-output-order» (A B : O → Prop) :
    HoareLe A B ↔ ∀ a, A a → ∃ b, B b ∧ a ≼ b :=
  Iff.rfl

/-- "Fix a table `X ⊆ I × O`, with fibers `X(i)` possibly empty.  A *powerset
relaxation* of `X` is a map `A : I → 𝒫(O)` with `X(i) ⊑_H A(i)` for every
`i`; it satisfies *Relational Monotonicity* when `i ⊑ k` implies
`A(i) ⊑_H A(k)`."  Lean: `A` is itself a table. -/
theorem «sec:frontiers/powerset-relaxation» (X A : Table I O) :
    (Relaxation X A ↔ ∀ i, HoareLe (X i) (A i)) ∧
    (HRelMono A ↔ ∀ i k, i ≼ k → HoareLe (A i) (A k)) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- **Eq. `eq:monotone-hull`** (remembered output).
"`X̂(i) = ⋃_{j ⊑ i} X(j)`." -/
theorem «eq:monotone-hull» (X : Table I O) (i : I) (o : O) :
    hull X i o ↔ ∃ j, j ≼ i ∧ X j o :=
  Iff.rfl

/-- **Eq. `eq:hull-coverage`**: every powerset relaxation `A` of `X`
satisfying Relational Monotonicity has "`X̂(i) ⊑_H A(i)` for every `i`". -/
theorem «eq:hull-coverage» (X A : Table I O) (hA : Relaxation X A) (hM : HRelMono A)
    (i : I) : HoareLe (hull X i) (A i) :=
  hull_least X A hA hM i

/-- **Theorem `thm:monotone-hull`** (Remembered-output frontier).
"`X̂` is a powerset relaxation of `X` satisfying Relational Monotonicity, and
every such relaxation `A` satisfies `X̂(i) ⊑_H A(i)` for every `i`
(Eq. `eq:hull-coverage`).  If every `X̂(i)` is finite and `M(i)` is its set of
maximal elements, then `M(i) ⊑_H X̂(i) ⊑_H M(i)`, `M` satisfies Relational
Monotonicity, and `M(i)` is the least subset `Y ⊆ X̂(i)` with `X̂(i) ⊑_H Y`."

Lean: `M` is `pruned X` (`maxOf (hull X i)`); the third conjunct lists, at each
`i`, `M(i) ⊆ X̂(i)`, `X̂(i) ⊑_H M(i)` and `M(i) ⊆ Y` for every such `Y`.  As the
proof remarks, minimality does not use finiteness (`pruned_least`). -/
theorem «thm:monotone-hull» (X : Table I O) :
    (Relaxation X (hull X) ∧ HRelMono (hull X)) ∧
    (∀ A, Relaxation X A → HRelMono A → ∀ i, HoareLe (hull X i) (A i)) ∧
    ((∀ i, FiniteSet (hull X i)) →
      (∀ i, HoareLe (pruned X i) (hull X i) ∧ HoareLe (hull X i) (pruned X i)) ∧
      HRelMono (pruned X) ∧
      (∀ i, (∀ o, pruned X i o → hull X i o) ∧ HoareLe (hull X i) (pruned X i) ∧
        ∀ Y : O → Prop, (∀ o, Y o → hull X i o) → HoareLe (hull X i) Y →
          ∀ o, pruned X i o → Y o)) :=
  let h := monotone_hull X
  ⟨h.1, h.2.1, fun hfin =>
    let k := h.2.2 hfin
    ⟨fun i => ⟨(k.1 i).2, (k.1 i).1⟩, k.2.1, k.2.2⟩⟩

/-- `M(i)` is the set of maximal elements of `X̂(i)`, and the least subset is
unique: any `Z ⊆ X̂(i)` with `X̂(i) ⊑_H Z` contained in every other such `Y`
equals `M(i)`. -/
theorem «thm:monotone-hull/pruned-unique» (X : Table I O)
    (hfin : ∀ i, FiniteSet (hull X i)) (i : I) (Z : O → Prop)
    (hZ : ∀ o, Z o → hull X i o) (hZcov : HoareLe (hull X i) Z)
    (hZmin : ∀ Y : O → Prop, (∀ o, Y o → hull X i o) → HoareLe (hull X i) Y →
      ∀ o, Z o → Y o) :
    (∀ m, pruned X i m ↔ hull X i m ∧ ∀ o, hull X i o → m ≼ o → o = m) ∧
    ∀ o, Z o ↔ pruned X i o :=
  ⟨fun _ => Iff.rfl, pruned_unique X hfin i Z hZ hZcov hZmin⟩

/-- "When `X = S` is a specification, every `X̂(i)` is nonempty.  Let
`A ≡_H B` mean `A ⊑_H B ⊑_H A`, and order the quotient
`(𝒫(O) ∖ {∅})/≡_H` by the order that `⊑_H` induces on classes."

Lean (modeling choice 1 of `Appendix/Frontiers.lean`): classes are represented
by nonempty down-closed sets `HClass O` ordered by inclusion; `HClass.of A`
is the class of a nonempty `A`.  The class order is `⊑_H`, equal classes are
exactly `≡_H`-equivalent sets, and every class is the class of a set. -/
theorem «sec:frontiers/hoare-quotient» :
    (∀ (A B : O → Prop) (ha : ∃ o, A o) (hb : ∃ o, B o),
      (HClass.of A ha ≼ HClass.of B hb ↔ HoareLe A B) ∧
      (HClass.of A ha = HClass.of B hb ↔ HoareLe A B ∧ HoareLe B A)) ∧
    ∀ c : HClass O, c = HClass.of c.D c.ne :=
  ⟨fun A B ha hb => ⟨hclass_of_le_iff A B ha hb, hclass_of_eq_iff A B ha hb⟩, hclass_eq_of⟩

/-- "Then `i ↦ X̂(i)`, read in this quotient, is a functional specification.
It is monotone, hence consistent by Theorem `thm:functional-calm`."

Lean: `hullSpec sp` has the single row `(i, [X̂(i)])` at each `i` (with
`X = sp.S`). -/
theorem «sec:frontiers/hull-spec-consistent» (sp : Spec I O) :
    (hullSpec sp).Functional ∧ (hullSpec sp).MonotoneF ∧ (hullSpec sp).Consistent :=
  ⟨hullSpec_functional sp, hullSpec_mono sp, hullSpec_consistent sp⟩

end Hull

/-! ### Table `tab:lookup-lift` -/

/-- **Table `tab:lookup-lift`** (Original, remembered, and pruned fibers for
the lookup example).  "A data item moves from node `a` to node `b` as input
grows from `i₀` to `i₁`. … `o_a, o_b ≼ o_{a⇝b}`."  Rows of the table:
`X(i₀) = {o_a}`, `X̂(i₀) = {o_a}`; `X(i₁) = {o_b}`, `X̂(i₁) = {o_a, o_b}`; and
"both are maximal, so `M = X̂`".

Lean: inputs `LIn` (`i0 ≼ i1`), outputs `LOut` (`a`, `b`, `ab = o_{a⇝b}`). -/
theorem «tab:lookup-lift» :
    (LIn.i0 ≼ LIn.i1) ∧ (LOut.a ≼ LOut.ab) ∧ (LOut.b ≼ LOut.ab) ∧
    (∀ o, lookupX .i0 o ↔ o = .a) ∧ (∀ o, lookupX .i1 o ↔ o = .b) ∧
    (∀ o, hull lookupX .i0 o ↔ o = .a) ∧ (∀ o, hull lookupX .i1 o ↔ (o = .a ∨ o = .b)) ∧
    (∀ i o, pruned lookupX i o ↔ hull lookupX i o) :=
  ⟨trivial, Or.inr rfl, Or.inr rfl, fun _ => Iff.rfl, fun _ => Iff.rfl,
   lookup_hull_i0, lookup_hull_i1, lookup_pruned⟩

/-- "It violates Relational Monotonicity, since `o_a` at `i₀` has nothing
above it in `X(i₁)`."  (`X` read as a powerset-valued map.) -/
theorem «tab:lookup-lift/not-rel-mono» : ¬ HRelMono lookupX :=
  lookup_not_relMono

/-- "Forwarding, `A(i₀) = {o_a}` and `A(i₁) = {o_{a⇝b}}`, is another
relaxation satisfying Relational Monotonicity, and Equation `eq:hull-coverage`
places `X̂` below it: `{o_a, o_b} ⊑_H {o_{a⇝b}}`." -/
theorem «tab:lookup-lift/forwarding» :
    (∀ o, fwdA .i0 o ↔ o = .a) ∧ (∀ o, fwdA .i1 o ↔ o = .ab) ∧
    Relaxation lookupX fwdA ∧ HRelMono fwdA ∧ HoareLe (hull lookupX .i1) (fwdA .i1) :=
  ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fwdA_relaxation, fwdA_relMono, lookup_hull_le_fwd⟩

/-! ### Persistent forwarding -/

section Forwarding
variable {K P : Type}

/-- "The structure after `h` is a finite directed graph whose nodes are
*positions* … For each key `k`, every position has at most one outgoing
*search edge for `k`* …  The *claim* `(k,π)` belongs to `C(h)` when the search
for `k` from `π` reaches a current occurrence of `k` after finitely many
edges."

Lean (modeling choice 4 of `Appendix/Frontiers.lean`): a snapshot `Snap K P`
has key-indexed search edges `edge k` and occurrences `occ k`; positions are a
fixed type `P`.  The child/link distinction, finiteness of the graph and
uniqueness of search edges are not needed and not modeled. -/
theorem «sec:frontiers/claims» (G : Snap K P) (k : K) (π : P) :
    claims G k π ↔ ∃ q, Path G k π q ∧ G.occ k q :=
  Iff.rfl

/-- "Each restructuring step must satisfy: (1) positions keep stable
identities; (2) if `π → π'` was the search edge for `k` at `π` before the step,
the search for `k` from `π` reaches `π'` after it; and (3) from every position
that held `k` before the step, the search for `k` reaches a current occurrence
of `k` after it."

Lean: (1) holds by construction (positions live in `P`); (2) and (3) are the
fields of `Obligations`.  Inputs are histories `Rs.Hist` of a `Restructuring`
(lists of snapshots linked by steps satisfying the obligations) ordered by
prefix, and `Rs.R h` is `C(h)`. -/
theorem «sec:frontiers/obligations» (G G' : Snap K P) :
    Obligations G G' ↔
      ((∀ k p q, G.edge k p q → Path G' k p q) ∧
       (∀ k p, G.occ k p → ∃ q, Path G' k p q ∧ G'.occ k q)) :=
  ⟨fun h => ⟨h.edges, h.occs⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **Proposition `prop:persistent-forwarding`** (Persistent-forwarding
monotonicity).  "Under (1)–(3), `h ⊑ h'` implies `C(h) ⊆ C(h')`.  The
functional specification `h ↦ C(h)`, ordered by inclusion, is therefore
monotone and, by Theorem `thm:functional-calm`, consistent." -/
theorem «prop:persistent-forwarding» (Rs : Restructuring K P) :
    (∀ h h' : Rs.Hist, h ≼ h' → ∀ k p, Rs.R h k p → Rs.R h' k p) ∧
    (fwdSpec Rs).Functional ∧ (fwdSpec Rs).MonotoneF ∧ (fwdSpec Rs).Consistent :=
  ⟨fun _ _ hle => persistent_forwarding Rs hle, fwdSpec_functional Rs, fwdSpec_mono Rs,
   fwdSpec_consistent Rs⟩

/-- Proof of Prop. `prop:persistent-forwarding`: "By induction it suffices to
treat one step.  Let the search for `k` from `π` reach an occurrence before
the step.  After the step, by (2) the search from each position on that path
reaches the next one, so the search from `π` reaches the old occurrence, and
by (3) it continues to a current occurrence." -/
theorem «prop:persistent-forwarding/one-step» {G G' : Snap K P} (hO : Obligations G G')
    {k : K} {p : P} (h : claims G k p) : claims G' k p :=
  claims_step hO h

/-- **Eq. `eq:forwarding-hull`**.  "Let `X(h) ⊆ C(h)` be the claims that are
*exact* at `h` … Order claims by equality, so that `⊑_H` is inclusion.  By
Proposition `prop:persistent-forwarding`, `C` is a powerset relaxation of `X`
satisfying Relational Monotonicity, so Equation `eq:hull-coverage` gives
`X̂(h) ⊆ C(h)`: every claim that was ever exact remains valid, possibly through
link edges."

Lean: claims are `Disc (K × P)` (equality order, under which `⊑_H` is
inclusion, `disc_hoare_iff`).  Exactness is not modeled; the statement holds
for every table `X` of claims valid at their input, in particular the exact
ones.  The proof goes through Eq. `eq:hull-coverage` as in the paper.  "Here
`X` has empty fibers, which is why Theorem `thm:monotone-hull` is stated for
tables": `X` is an arbitrary `Table`, not a `Spec`. -/
theorem «eq:forwarding-hull» (Rs : Restructuring K P) (X : Table Rs.Hist (Disc (K × P)))
    (hX : ∀ g c, X g c → Rs.R g c.val.1 c.val.2) (h : Rs.Hist) :
    (∀ (A B : Disc (K × P) → Prop), HoareLe A B ↔ ∀ c, A c → B c) ∧
    ∀ c, hull X h c → Rs.R h c.val.1 c.val.2 :=
  ⟨disc_hoare_iff, forwarding_hull_via_coverage Rs X hX h⟩

end Forwarding

/-! ### Preserving independent local choices -/

section Product
variable {I : Type} [PO I] {n : Nat} {W : Fin n → Type} [∀ p, PO (W p)]

/-- "A *partial tuple* assigns to each `p` either a value in `W_p` or `⊥`;
partial tuples are ordered coordinate-wise, with `⊥` below every value.  `x`
is a *restriction* of a complete tuple `y` when each `x_p` is `⊥` or `y_p`."

Lean: `PTd W` with `⊥ = none`; `OLe` is the coordinate order. -/
theorem «sec:frontiers/partial-tuples» (x x' : PTd W) (y : (p : Fin n) → W p) :
    (x ≼ x' ↔ ∀ p, OLe (x.t p) (x'.t p)) ∧
    (Restr x y ↔ ∀ p, x.t p = none ∨ x.t p = some (y p)) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- Definitions of the product interface, normalized strengthenings, local
conservativity and the owner deployment.

* "The *product interface* `S` has a row `(i,x)` for every restriction `x` of
  every `y ∈ ∏_p V_p(i)`."  (`prodSpec V hne`, `hne`: each `V_p(i)` nonempty.)
* "A *normalized strengthening* `T` selects, at each input, a set of tuples in
  `∏_p V_p(i)` and has as rows exactly their restrictions.  It is *locally
  conservative* when for every `i`, `p`, and `v ∈ V_p(i)` some selected tuple
  `z` at `i` has `z_p = v`."  (`NormStr V`, `T.table`, `T.LocCons`; "strict",
  `T ⊊ S`, is `T.Strict`.)
* "The *owner deployment* of a specification over partial tuples lets `p`
  emit exactly its rows whose tuple is `⊥` outside coordinate `p`.
  Participant `p` is the sole owner of coordinate `p` and owns no other."
  (`ownerD sp`.) -/
theorem «sec:frontiers/product-definitions» (V : (p : Fin n) → I → W p → Prop)
    (hne : ∀ p i, ∃ v, V p i v) (T : NormStr V) (sp : Spec I (PTd W)) :
    (∀ i x, (prodSpec V hne).S i x ↔ ∃ y, (∀ p, V p i (y p)) ∧ Restr x y) ∧
    (∀ i x, T.table i x ↔ ∃ y, T.sel i y ∧ Restr x y) ∧
    (T.LocCons ↔ ∀ i p v, V p i v → ∃ z, T.sel i z ∧ z p = v) ∧
    (T.Strict ↔ ∃ i x, prodTable V i x ∧ ¬ T.table i x) ∧
    (∀ p i x, (ownerD sp).A p i x ↔ sp.S i x ∧ ∀ q, q ≠ p → x.t q = none) :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, Iff.rfl, Iff.rfl, fun _ _ _ => Iff.rfl⟩

/-- **Theorem `thm:product-frontier`** (Independent-product frontier), part (1).
"If views continue (for `i ⊑ j` and `v ∈ V_p(i)` there is `w ∈ V_p(j)` with
`v ≤_p w`), the product interface is monotone across partitions under the
owner deployment, so every separable run family is confluent at every common
expansion of its participants' current inputs
(Proposition `thm:complete-cap-deployment`)."

Lean: the first conjunct is the construction of the proof, which "does not
use separability": every owner-authorized family has a common expansion. -/
theorem «thm:product-frontier/1» (V : (p : Fin n) → I → W p → Prop)
    (hne : ∀ p i, ∃ v, V p i v) (hc : Continue V) :
    (∀ F : Family (prodSpec V hne) n, Authorized (ownerD (prodSpec V hne)) F →
      ∀ j, UB F j → ∃ u, (prodSpec V hne).S j u ∧ ∀ p r, Emits F p r → r.2 ≼ u) ∧
    MonoAcrossPartitions (ownerD (prodSpec V hne)) ∧
    PartitionConfluent (ownerD (prodSpec V hne)) :=
  ⟨fun F hA j hj => product_common V hne hc F hA j hj, product_monoAcross V hne hc,
   product_confluent V hne hc⟩

/-- **Theorem `thm:product-frontier`**, part (2).  "If each `V_p(i)` is an
antichain, no strict, normalized, locally conservative strengthening
`T ⊊ S` is monotone across partitions under its owner deployment.  (Here
Definition `def:monotone-across-partitions` is applied to `T`: read `T(j)` for
`S(j)`.)"

Lean: `|P| ≥ 2` (the standing assumption of the subsection) is `2 ≤ n`; `sp`
is any specification whose table is `T`'s. -/
theorem «thm:product-frontier/2» (hn : 2 ≤ n) (V : (p : Fin n) → I → W p → Prop)
    (hAC : Antichain V) (T : NormStr V) (sp : Spec I (PTd W))
    (hsp : ∀ i x, sp.S i x ↔ T.table i x) (hLC : T.LocCons) (hst : T.Strict) :
    ¬ MonoAcrossPartitions (ownerD sp) :=
  strengthening_not_monoAcross hn V hAC T sp hsp hLC hst

/-- **Theorem `thm:product-frontier`**, both parts together, each with its
own hypotheses. -/
theorem «thm:product-frontier» (hn : 2 ≤ n) (V : (p : Fin n) → I → W p → Prop)
    (hne : ∀ p i, ∃ v, V p i v) :
    (Continue V → MonoAcrossPartitions (ownerD (prodSpec V hne))) ∧
    (Antichain V → ∀ (T : NormStr V) (sp : Spec I (PTd W)),
      (∀ i x, sp.S i x ↔ T.table i x) → T.LocCons → T.Strict →
      ¬ MonoAcrossPartitions (ownerD sp)) :=
  ⟨product_monoAcross V hne, fun hAC T sp hsp hLC hst =>
    strengthening_not_monoAcross hn V hAC T sp hsp hLC hst⟩

/-- "The hypotheses matter.  The deployment is essential: if some `V_p(i)` has
two views with no common upper bound in `V_p(i)` (for instance, two distinct
views when `V_p(i)` is an antichain), the product interface has no Lifted
Monotonicity, since those two rows have no common expansion; with `A_p = S`
for every `p`, the two rows form a separable family." -/
theorem «sec:frontiers/deployment-essential» (hn : 2 ≤ n) (V : (p : Fin n) → I → W p → Prop)
    (hne : ∀ p i, ∃ v, V p i v) {p : Fin n} {i : I} {v w : W p} (hv : V p i v)
    (hw : V p i w) (hnb : ¬ ∃ t, V p i t ∧ v ≼ t ∧ w ≼ t) :
    ¬ (prodSpec V hne).LiftedMono ∧
    ∀ Dp : Deployment (prodSpec V hne) n, (∀ q, Dp.A q = (prodSpec V hne).S) →
      ¬ MonoAcrossPartitions Dp :=
  ⟨product_not_liftedMono V hne hv hw hnb,
   fun Dp hA => product_full_not_monoAcross hn V hne Dp hA hv hw hnb⟩

end Product

/-- Why the remark says "no common upper bound *in `V_p(i)`*" rather than
"incomparable" (not a claim of the paper): two incomparable views `lo1, lo2`
below a third view `t` in the same `V_0(i)` leave the product interface
monotone. -/
theorem «sec:frontiers/deployment-essential/upper-bound-needed» :
    (triV 0 .pt .lo1 ∧ triV 0 .pt .lo2 ∧ ¬ (Tri.lo1 ≼ Tri.lo2) ∧ ¬ (Tri.lo2 ≼ Tri.lo1)) ∧
    (prodSpec (W := fun _ => Tri) triV triV_ne).LiftedMono :=
  ⟨tri_incomparable, tri_liftedMono⟩

/-- "Owning only its own coordinate is needed: let two replicas each expose
configuration 0 or 1 at every input, with views ordered by equality (so each
`V_p(i) = {0,1}` is an antichain), and let `T` require them to agree, keeping
`(0,0)` and `(1,1)`.  This `T` is strict and locally conservative, so by part
(2) it is not monotone across partitions under its owner deployment."

Lean: any input poset `I` with an input `i`; views `cfgV I` in `Disc Bool`;
`agree I` selects tuples `y` with `y 0 = y 1`. -/
theorem «sec:frontiers/configuration-example» {I : Type} [PO I] (i : I) :
    Antichain (W := fun _ => Disc Bool) (cfgV I) ∧
    (∀ j y, (agree I).sel j y ↔ y 0 = y 1) ∧
    (agree I).Strict ∧ (agree I).LocCons ∧
    ¬ MonoAcrossPartitions (ownerD (agreeSpec I)) :=
  ⟨cfgV_antichain, fun _ _ => Iff.rfl, agree_strict i, agree_locCons, cfg_agree_not_monoAcross i⟩

/-- "If instead one participant owns both coordinates, the other may emit only
the empty tuple, which every output refines, and `T` is monotone across
partitions; forbidding even that makes the deployment single-authority
(Appendix `app:deployment`)."

Lean: `agreeSoleOwnerD I` lets participant `0` emit every row of `T` and
participant `1` only the empty tuple `ptEmpty`; `agreeSingleD I` is the
single-authority variant (participant `1` emits nothing). Both are monotone
across partitions. -/
theorem «sec:frontiers/configuration-example/sole-owner» {I : Type} [PO I] :
    (∀ i x, (agreeSoleOwnerD I).A 0 i x ↔ (agreeSpec I).S i x) ∧
    (∀ i x, (agreeSoleOwnerD I).A 1 i x ↔ x = ptEmpty) ∧
    (∀ x, ptEmpty ≼ x) ∧
    MonoAcrossPartitions (agreeSoleOwnerD I) ∧
    SingleAuthority (agreeSingleD I) 0 ∧ MonoAcrossPartitions (agreeSingleD I) :=
  ⟨fun _ _ => ⟨fun h => h.1, fun h => ⟨h, fun h' => absurd h' (by decide)⟩⟩,
   fun _ _ => ⟨fun h => h.2 rfl,
     fun h => ⟨h ▸ ⟨fun _ => ⟨false⟩, rfl, fun _ => Or.inl rfl⟩, fun _ => h⟩⟩,
   ptEmpty_le, cfg_agree_sole_owner,
   fun _ hq _ _ h => hq h.1, cfg_agree_single_authority⟩

/-! #### Causal register -/

section CausalFrontier
variable {α : Type} {n : Nat}

/-- "Take the causal register of Appendix `app:registers`.  Let `V_p(h)` be the
maps from the reads of replica `p` in `h` to writes of `h` or `v₀` that some
serialization for `p` explains, ordered by extension; each `V_p(h)` is an
antichain, since its maps share a domain. … Views continue by the argument
given there, so part (1) applies."

Lean: `CView G p h`; views are nonempty (`cviews_ne`), form antichains and
continue; part (1) gives monotonicity across partitions of the causal product
interface under its owner deployment (each replica answers only its own
reads). -/
theorem «sec:frontiers/causal-register» (G : OpSig α n) :
    (∀ p h v, CView G p h v ↔ ((∀ r, (∃ s, v.f r = some s) ↔ PRead G h p r) ∧
      ∃ lt, Ser G h p lt ∧ ∀ r s, v.f r = some s → Explains G h lt r s)) ∧
    Antichain (W := fun _ => SMap α) (CView G) ∧
    Continue (W := fun _ => SMap α) (CView G) ∧
    MonoAcrossPartitions (ownerD (prodSpec (W := fun _ => SMap α) (CView G) (cviews_ne G))) :=
  ⟨fun _ _ _ => Iff.rfl, cviews_antichain G, cviews_cont G, causal_product_monoAcross G⟩

/-- "Linearizability selects the tuples that a single total order of all
operations explains.  It is locally conservative: a serialization `L_p` for
`p`, together with `→`, has no cycle …; so some total order of all operations
extends both, and it gives `p`'s reads the same sources as `L_p`." -/
theorem «sec:frontiers/linearizability-locally-conservative» (G : OpSig α n) :
    (∀ h y, (linNS G).sel h y ↔ ((∀ p, CView G p h (y p)) ∧ ∃ T, STO h.mem T ∧
      Ext h.hb h.mem T ∧ ∀ p r s, (y p).f r = some s → Explains G h T r s)) ∧
    (linNS G).LocCons :=
  ⟨fun _ _ => Iff.rfl, lin_locCons G⟩

end CausalFrontier

/-- "The two-write history of Appendix `app:registers` shows that it is
strict, so part (2) recovers, for the product form of linearizability, the
obstruction of Appendix `app:registers`." -/
theorem «sec:frontiers/linearizability-strict» :
    (linNS G2).Strict ∧ ¬ MonoAcrossPartitions (ownerD (linSpecP G2)) :=
  ⟨lin_strict, lin_product_not_monoAcross⟩

/-- "This depends on the input recording only causal precedence.  If the
input also records real-time precedence, a write that finished before `p`'s
read in real time but lies outside its causal past must precede that read in
every linearization, so some causal view of `p` alone is excluded;
linearizability is then not locally conservative and part (2) does not
apply."

Lean: history `hR` with a write `w_q = 0` and a read `r_p = 1`, no causal
precedence, real-time precedence `rt` from `w_q` to `r_p`; the causal view
`r_p ↦ v₀` is in `V_p` but is the `p`-coordinate of no tuple selected by
real-time linearizability `linRT`. -/
theorem «sec:frontiers/real-time-precedence» :
    CView G1 0 hR vInit ∧ ¬ linRT.LocCons :=
  ⟨cview_vInit, linRT_not_locCons⟩

end Paper
end CC
