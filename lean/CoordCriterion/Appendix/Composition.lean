import CoordCriterion.CompleteCALM.Theorem

/-!
# Composition and Proper Coordination (Appendix D, `appendices/composition.tex`)

Namespace `CC.Comp`.  Further examples of the appendix (converse example,
curried form on graph tables, committed-log composition) are in
`Instances/Examples.lean`.

* `seq_liftedMono`                 — Lemma lem:composition
* `tcomp_assoc`                    — associativity remark after the lemma
* `functional_composition`         — Cor. cor:functional-composition
* `curried_query_plan`             — Prop. prop:curried-query-plan
* `par_liftedMono`                 — Lemma lem:parameterized-composition
* `parameterized_graph`, `parameterized_functional_composition`
                                   — Eq. curried-composition (graph instance)
* `Proper`, `ProperSeq`, `ProperPar` — Def. def:proper-coordination
* `proper_second_clause`           — "the second clause is implied by the first"
* `proper_coordination_seq/par`    — Cor. thm:proper-coordination
* `monotone_commitment_seq/par`    — Cor. cor:monotone-commitment
* `monotone_commitment_neither_monotone` — "Neither S₁ nor the unresolved
  composition need be monotone"
* `proper_strictly_more_general`   — remark after Cor. cor:monotone-commitment
* `restricted_middle_counterexample` — why `S₂` must be total on all of `M`

Modeling choices.

* `Spec I O` is total on its whole input type (the paper's convention of
  restricting every specification to inputs with a nonempty fiber).  Because
  `S₁` is total on `I` and `S₂` is total on `M`, the composed table is total on
  `I`, so the paper's "restrict the composed input domain to inputs with a
  nonempty fiber" is vacuous; `seq` and `par` are genuine `Spec`s.  The
  counterexample `restricted_middle_counterexample` shows this totality of
  `S₂` on *all* of `M` (not just on the outputs `S₁` happens to produce) is
  necessary for Lemma lem:composition.
* Products carry the componentwise order (`instPOProd`).  The composed input
  `I × J × A` of independently parameterized composition is `I × (J × A)`.
* A commitment strategy is represented, as in the paper, only by its declared
  committed table `K ⊆ S₁` (`CommitTable`).  Totality-preservation is the field
  `total`; without it the resolved table would not be a `Spec`.
* "Monotone function" is `Monotone f : ∀ i j, i ≼ j → f i ≼ f j`; its graph
  table is `graph f`.
-/

namespace CC
namespace Comp

/-! ### Order constructions -/

/-- Componentwise (product) order. -/
instance instPOProd {α β : Type} [PO α] [PO β] : PO (α × β) where
  le p q := p.1 ≼ q.1 ∧ p.2 ≼ q.2
  refl _ := ⟨PO.refl _, PO.refl _⟩
  trans h h' := ⟨PO.trans h.1 h'.1, PO.trans h.2 h'.2⟩
  antisymm h h' := Prod.ext (PO.antisymm h.1 h'.1) (PO.antisymm h.2 h'.2)

theorem prod_le_iff {α β : Type} [PO α] [PO β] {p q : α × β} :
    p ≼ q ↔ p.1 ≼ q.1 ∧ p.2 ≼ q.2 := Iff.rfl

/-- Specifications are determined by their tables. -/
theorem Spec.ext' {I O : Type} [PO I] [PO O] {a b : Spec I O} (h : a.S = b.S) : a = b := by
  cases a; cases b; cases h; rfl

/-- Choosing a witness for each element of a finite list (no choice axiom
needed: we are proving a proposition). -/
theorem choose_list {α β : Type} (P : α → β → Prop) :
    ∀ l : List α, (∀ a ∈ l, ∃ b, P a b) →
      ∃ L : List (α × β), (∀ a ∈ l, ∃ b, (a, b) ∈ L) ∧ ∀ p ∈ L, p.1 ∈ l ∧ P p.1 p.2
  | [], _ => ⟨[], by simp, by simp⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (List.mem_cons_self ..)
    obtain ⟨L, h1, h2⟩ := choose_list P l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨(a, b) :: L, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨b, List.mem_cons_self ..⟩
      · obtain ⟨b', hb'⟩ := h1 x hx; exact ⟨b', List.mem_cons_of_mem _ hb'⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨List.mem_cons_self .., hb⟩
      · exact ⟨List.mem_cons_of_mem _ (h2 p hp).1, (h2 p hp).2⟩

/-! ### Sequential composition -/

section Seq
variable {I M O : Type} [PO I] [PO M] [PO O]

/-- `S₂ ∘ S₁ = π_{I,O}(S₁ ⋈_M S₂)` (Eq. spec-composition). -/
def tcomp (S1 : Table I M) (S2 : Table M O) : Table I O :=
  fun i o => ∃ m, S1 i m ∧ S2 m o

omit [PO I] [PO M] [PO O] in
/-- Relational composition is associative, so the lemma extends to finite
pipelines. -/
theorem tcomp_assoc {P : Type} (S1 : Table I M) (S2 : Table M O) (S3 : Table O P) :
    tcomp (tcomp S1 S2) S3 = tcomp S1 (tcomp S2 S3) := by
  funext i p
  apply propext
  constructor
  · rintro ⟨o, ⟨m, h1, h2⟩, h3⟩; exact ⟨m, h1, o, h2, h3⟩
  · rintro ⟨m, h1, o, h2, h3⟩; exact ⟨o, ⟨m, h1, h2⟩, h3⟩

/-- The sequential composition as an ordered specification; it is total
because `S₁` is total on `I` and `S₂` is total on `M`. -/
def seq (sp1 : Spec I M) (sp2 : Spec M O) : Spec I O where
  S := tcomp sp1.S sp2.S
  total i := by
    obtain ⟨m, hm⟩ := sp1.total i
    obtain ⟨o, ho⟩ := sp2.total m
    exact ⟨o, m, hm, ho⟩

/-- **Lemma (Composition).** -/
theorem seq_liftedMono {sp1 : Spec I M} {sp2 : Spec M O}
    (h1 : sp1.LiftedMono) (h2 : sp2.LiftedMono) : (seq sp1 sp2).LiftedMono := by
  rw [liftedMono_iff_commonExpansion] at *
  intro rows hrows j hj
  obtain ⟨L, hL1, hL2⟩ := choose_list (fun (r : I × O) m => sp1.S r.1 m ∧ sp2.S m r.2)
    rows hrows
  -- upstream: the witnesses `m_r` have a common expansion `m ∈ S₁(j)`
  obtain ⟨m, hm, hmall⟩ := h1 (L.map fun p => (p.1.1, p.2))
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact (hL2 p hp).2.1) j
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact hj _ (hL2 p hp).1)
  -- downstream: the rows `(m_r, o_r)` have common input expansion `m`
  obtain ⟨u, hu, huall⟩ := h2 (L.map fun p => (p.2, p.1.2))
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact (hL2 p hp).2.2) m
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        exact hmall (p.1.1, p.2) (List.mem_map.2 ⟨p, hp, rfl⟩))
  refine ⟨u, ⟨m, hm, hu⟩, fun r hr => ?_⟩
  obtain ⟨b, hb⟩ := hL1 r hr
  exact huall (b, r.2) (List.mem_map.2 ⟨(r, b), hb, rfl⟩)

/-! ### Functional composition -/

/-- A monotone function. -/
def Monotone {α β : Type} [PO α] [PO β] (f : α → β) : Prop := ∀ x y, x ≼ y → f x ≼ f y

/-- The graph table `{(x, f x)}` as a specification. -/
def graph {α β : Type} [PO α] [PO β] (f : α → β) : Spec α β where
  S x y := y = f x
  total x := ⟨f x, rfl⟩

theorem graph_liftedMono_iff {α β : Type} [PO α] [PO β] (f : α → β) :
    (graph f).LiftedMono ↔ Monotone f := by
  constructor
  · intro h x y hxy
    obtain ⟨u, hu, hall⟩ := h x y hxy [f x] (by simp) (by simp [graph])
    have : u = f y := hu
    exact this ▸ hall (f x) (by simp)
  · intro hf x y hxy X _ hX
    refine ⟨f y, rfl, fun z hz => ?_⟩
    have : z = f x := hX z hz
    exact this ▸ hf x y hxy

theorem seq_graph (f : I → M) (g : M → O) : seq (graph f) (graph g) = graph (g ∘ f) := by
  apply Spec.ext'
  funext i o
  apply propext
  show (∃ m, m = f i ∧ o = g m) ↔ o = g (f i)
  constructor
  · rintro ⟨m, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨f i, rfl, rfl⟩

/-- **Corollary (Functional composition)**, proved as in the paper through the
graph tables and Lemma lem:composition. -/
theorem functional_composition {f : I → M} {g : M → O} (hf : Monotone f) (hg : Monotone g) :
    Monotone (g ∘ f) := by
  rw [← graph_liftedMono_iff, ← seq_graph]
  exact seq_liftedMono ((graph_liftedMono_iff f).2 hf) ((graph_liftedMono_iff g).2 hg)

end Seq

/-! ### Composition with independent inputs -/

section Par
variable {I J A B C : Type} [PO I] [PO J] [PO A] [PO B] [PO C]

/-- `G ⋆ F = π_{I,J,A,C}(F ⋈_B G)` (Eq. parameterized-composition), with
composed input `(i, j, a) = (i, (j, a))`. -/
def ptable (F : Table (I × A) B) (G : Table (J × B) C) : Table (I × (J × A)) C :=
  fun x c => ∃ b, F (x.1, x.2.2) b ∧ G (x.2.1, b) c

def par (F : Spec (I × A) B) (G : Spec (J × B) C) : Spec (I × (J × A)) C where
  S := ptable F.S G.S
  total x := by
    obtain ⟨b, hb⟩ := F.total (x.1, x.2.2)
    obtain ⟨c, hc⟩ := G.total (x.2.1, b)
    exact ⟨c, b, hb, hc⟩

/-- Curried fibers `F_i = π_{A,B}(F[I=i])`, `G_j = π_{B,C}(G[J=j])`
(Eq. curried-fibers). -/
def fiberF (F : Table (I × A) B) (i : I) : Table A B := fun a b => F (i, a) b
def fiberG (G : Table (J × B) C) (j : J) : Table B C := fun b c => G (j, b) c

/-- The curried plan (Eq. curried-query-plan):
`⋃_{(i,j) ∈ I×J} {((i,j,a),c) : (a,c) ∈ π_{A,C}(F_i ⋈_B G_j)}`. -/
def curriedPlan (F : Table (I × A) B) (G : Table (J × B) C) : Table (I × (J × A)) C :=
  fun x c => ∃ p : I × J, x.1 = p.1 ∧ x.2.1 = p.2 ∧ tcomp (fiberF F p.1) (fiberG G p.2) x.2.2 c

omit [PO I] [PO J] [PO A] [PO B] [PO C] in
/-- **Proposition (Curried equijoin plan).** -/
theorem curried_query_plan (F : Table (I × A) B) (G : Table (J × B) C) :
    ptable F G = curriedPlan F G := by
  funext x c
  apply propext
  constructor
  · rintro ⟨b, hF, hG⟩; exact ⟨(x.1, x.2.1), rfl, rfl, b, hF, hG⟩
  · rintro ⟨p, h1, h2, b, hF, hG⟩
    refine ⟨b, ?_, ?_⟩
    · show F (x.1, x.2.2) b; rw [h1]; exact hF
    · show G (x.2.1, b) c; rw [h2]; exact hG

/-- **Lemma (Independently parameterized composition).** -/
theorem par_liftedMono {F : Spec (I × A) B} {G : Spec (J × B) C}
    (hF : F.LiftedMono) (hG : G.LiftedMono) : (par F G).LiftedMono := by
  rw [liftedMono_iff_commonExpansion] at *
  intro rows hrows x hx
  obtain ⟨L, hL1, hL2⟩ := choose_list
    (fun (r : (I × (J × A)) × C) b => F.S (r.1.1, r.1.2.2) b ∧ G.S (r.1.2.1, b) r.2)
    rows hrows
  obtain ⟨b, hb, hball⟩ := hF (L.map fun p => ((p.1.1.1, p.1.1.2.2), p.2))
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact (hL2 p hp).2.1)
    (x.1, x.2.2)
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        have h := hx _ (hL2 p hp).1
        exact ⟨h.1, h.2.2⟩)
  obtain ⟨c, hc, hcall⟩ := hG (L.map fun p => ((p.1.1.2.1, p.2), p.1.2))
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact (hL2 p hp).2.2)
    (x.2.1, b)
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        exact ⟨(hx _ (hL2 p hp).1).2.1,
          hball ((p.1.1.1, p.1.1.2.2), p.2) (List.mem_map.2 ⟨p, hp, rfl⟩)⟩)
  refine ⟨c, ⟨b, hb, hc⟩, fun r hr => ?_⟩
  obtain ⟨b', hb'⟩ := hL1 r hr
  exact hcall ((r.1.2.1, b'), r.2) (List.mem_map.2 ⟨(r, b'), hb', rfl⟩)

/-- The graph-table instance: `G ⋆ F` for graphs is the graph of
`h(i,j,a) = g(j, f(i,a))` (Eq. curried-composition). -/
theorem parameterized_graph (f : I × A → B) (g : J × B → C) :
    par (graph f) (graph g) = graph (fun x => g (x.2.1, f (x.1, x.2.2))) := by
  apply Spec.ext'
  funext x c
  apply propext
  show (∃ b, b = f (x.1, x.2.2) ∧ c = g (x.2.1, b)) ↔ c = g (x.2.1, f (x.1, x.2.2))
  constructor
  · rintro ⟨b, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨_, rfl, rfl⟩

theorem parameterized_functional_composition {f : I × A → B} {g : J × B → C}
    (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun x : I × (J × A) => g (x.2.1, f (x.1, x.2.2))) := by
  rw [← graph_liftedMono_iff, ← parameterized_graph]
  exact par_liftedMono ((graph_liftedMono_iff f).2 hf) ((graph_liftedMono_iff g).2 hg)

end Par

/-! ### Proper Coordination -/

section Proper
variable {I M O : Type} [PO I] [PO M] [PO O]

/-- A totality-preserving commitment strategy for `sp1`, recorded (as in the
paper) by its declared committed table `K ⊆ S₁`. -/
structure CommitTable (sp1 : Spec I M) where
  K : Table I M
  sub : ∀ i m, K i m → sp1.S i m
  total : ∀ i, ∃ m, K i m

/-- The committed table as a specification (possible by totality). -/
def CommitTable.spec {sp1 : Spec I M} (κ : CommitTable sp1) : Spec I M := ⟨κ.K, κ.total⟩

/-- The two clauses of Def. proper-coordination, about a resolved
specification. -/
def Proper (sp : Spec I O) : Prop :=
  sp.Consistent ∧ ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o

/-- Proper for a sequential composition: the resolved spec is `S₂ ∘ K`. -/
def ProperSeq {sp1 : Spec I M} (κ : CommitTable sp1) (sp2 : Spec M O) : Prop :=
  Proper (seq κ.spec sp2)

/-- Proper for an independently parameterized composition: `G ⋆ K`. -/
def ProperPar {I J A B C : Type} [PO I] [PO J] [PO A] [PO B] [PO C]
    {F : Spec (I × A) B} (κ : CommitTable F) (G : Spec (J × B) C) : Prop :=
  Proper (par κ.spec G)

/-- The second clause is implied by the first (via Complete CALM and the
exposure boundary). -/
theorem proper_second_clause (sp : Spec I O) (h : sp.Consistent) :
    ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  (exposure_boundary sp).1 ((complete_calm_commonExpansion sp).1 h)

theorem proper_iff (sp : Spec I O) : Proper sp ↔ sp.LiftedMono := by
  constructor
  · intro h; exact (complete_calm sp).1 h.1
  · intro h
    have hc := (complete_calm sp).2 h
    exact ⟨hc, proper_second_clause sp hc⟩

/-- **Corollary (Proper Coordination)**, sequential case. -/
theorem proper_coordination_seq {sp1 : Spec I M} (κ : CommitTable sp1) (sp2 : Spec M O) :
    ProperSeq κ sp2 ↔ (seq κ.spec sp2).LiftedMono :=
  proper_iff _

/-- **Corollary (Proper Coordination)**, independently parameterized case. -/
theorem proper_coordination_par {I J A B C : Type} [PO I] [PO J] [PO A] [PO B] [PO C]
    {F : Spec (I × A) B} (κ : CommitTable F) (G : Spec (J × B) C) :
    ProperPar κ G ↔ (par κ.spec G).LiftedMono :=
  proper_iff _

/-- **Corollary (Committing upstream to a monotone function)**, sequential. -/
theorem monotone_commitment_seq {sp1 : Spec I M} (κ : CommitTable sp1) (sp2 : Spec M O)
    (f : I → M) (hK : κ.K = (graph f).S) (hf : Monotone f) (h2 : sp2.LiftedMono) :
    ProperSeq κ sp2 := by
  have hk : κ.spec = graph f := Spec.ext' hK
  rw [ProperSeq, proper_iff, hk]
  exact seq_liftedMono ((graph_liftedMono_iff f).2 hf) h2

/-- **Corollary (Committing upstream to a monotone function)**, parameterized. -/
theorem monotone_commitment_par {I J A B C : Type} [PO I] [PO J] [PO A] [PO B] [PO C]
    {F : Spec (I × A) B} (κ : CommitTable F) (G : Spec (J × B) C)
    (f : I × A → B) (hK : κ.K = (graph f).S) (hf : Monotone f) (hG : G.LiftedMono) :
    ProperPar κ G := by
  have hk : κ.spec = graph f := Spec.ext' hK
  rw [ProperPar, proper_iff, hk]
  exact par_liftedMono ((graph_liftedMono_iff f).2 hf) hG

end Proper

/-! ### Examples and counterexamples -/

section Examples

/-- One-point order. -/
inductive Pt where
  | pt
  deriving DecidableEq

instance : PO Pt where
  le _ _ := True
  refl _ := trivial
  trans _ _ := trivial
  antisymm {a b} _ _ := by cases a; cases b; rfl

/-- Two incomparable points (discrete order). -/
inductive Two where
  | x | y
  deriving DecidableEq

instance : PO Two where
  le a b := a = b
  refl _ := rfl
  trans h h' := h.trans h'
  antisymm h _ := h

/-- A non-monotone upstream: one input, fiber `{x, y}` of incomparable outputs. -/
def anyS : Spec Pt Two := ⟨fun _ _ => True, fun _ => ⟨.x, trivial⟩⟩

/-- Monotone downstream: the identity. -/
def idS : Spec Two Two := graph id

/-- Commit upstream to `x`. -/
def kappaX : CommitTable anyS :=
  ⟨(graph fun _ : Pt => Two.x).S, fun _ _ _ => trivial, fun _ => ⟨_, rfl⟩⟩

theorem two_ne : ¬ (Two.x ≼ Two.y) := fun h => Two.noConfusion h

/-- "Neither `S₁` nor the unresolved composition need be monotone":
here `S₁` and `S₂ ∘ S₁` violate Lifted Monotonicity, yet committing to a
monotone function makes the composition proper. -/
theorem monotone_commitment_neither_monotone :
    ¬ anyS.LiftedMono ∧ ¬ (seq anyS idS).LiftedMono ∧ ProperSeq kappaX idS := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨u, _, hall⟩ := h .pt .pt trivial [.x, .y] (by simp) (fun _ _ => trivial)
    have h1 : Two.x = u := hall .x (by simp)
    have h2 : Two.y = u := hall .y (by simp)
    exact two_ne (h1.trans h2.symm)
  · intro h
    obtain ⟨u, _, hall⟩ := h .pt .pt trivial [.x, .y] (by simp)
      (fun z _ => ⟨z, trivial, rfl⟩)
    have h1 : Two.x = u := hall .x (by simp)
    have h2 : Two.y = u := hall .y (by simp)
    exact two_ne (h1.trans h2.symm)
  · exact monotone_commitment_seq kappaX idS (fun _ => .x) rfl (fun _ _ _ => rfl)
      ((graph_liftedMono_iff id).2 (fun _ _ h => h))

/-- A non-monotone downstream: `S₂(x) = {x}`, `S₂(y) = {x, y}`. -/
def s2NM : Spec Two Two := ⟨fun m o => m = .y ∨ o = .x, fun _ => ⟨.x, Or.inr rfl⟩⟩

/-- Cor. thm:proper-coordination is strictly more general than
Cor. cor:monotone-commitment: the downstream `s2NM` violates Lifted
Monotonicity (so Cor. cor:monotone-commitment does not apply), but the
resolved composition is proper. -/
theorem proper_strictly_more_general :
    ¬ s2NM.LiftedMono ∧ ProperSeq kappaX s2NM := by
  refine ⟨?_, ?_⟩
  · intro h
    obtain ⟨u, _, hall⟩ := h .y .y rfl [.x, .y] (by simp) (fun _ _ => Or.inl rfl)
    have h1 : Two.x = u := hall .x (by simp)
    have h2 : Two.y = u := hall .y (by simp)
    exact two_ne (h1.trans h2.symm)
  · rw [proper_coordination_seq]
    intro i j _ X _ hX
    refine ⟨.x, ⟨.x, rfl, Or.inr rfl⟩, fun z hz => ?_⟩
    obtain ⟨m, hm, h⟩ := hX z hz
    have hm' : m = Two.x := hm
    rcases h with h | h
    · rw [hm'] at h; exact Two.noConfusion h
    · exact h

/-! #### The middle domain must be all of `M`

If `S₂` is only total on a proper subset of `M` (its "domain" in the
restricted-fiber convention) then Lemma lem:composition fails, even though
the composed table is total on `I`.  So the lemma genuinely uses that the
input domain of `S₂` is all of `(M, ≼_M)`, not merely the outputs of `S₁`. -/

/-- `a, b` incomparable, both below `t`. -/
inductive M3 where
  | a | b | t
  deriving DecidableEq

def M3.le : M3 → M3 → Prop
  | x, y => x = y ∨ y = .t

instance : PO M3 where
  le := M3.le
  refl _ := Or.inl rfl
  trans := by
    intro x y z h1 h2
    unfold M3.le at *
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp
  antisymm := by
    intro x y h1 h2
    unfold M3.le at *
    cases x <;> cases y <;> simp_all

/-- Input domain of a table (inputs with a nonempty fiber). -/
def Dom {α β : Type} (T : Table α β) := {x : α // ∃ y, T x y}

instance {α β : Type} [PO α] (T : Table α β) : PO (Dom T) where
  le x y := x.1 ≼ y.1
  refl x := PO.refl x.1
  trans h h' := PO.trans h h'
  antisymm h h' := Subtype.ext (PO.antisymm h h')

/-- A table read as a specification on its own input domain. -/
def restrict {α β : Type} [PO α] [PO β] (T : Table α β) : Spec (Dom T) β :=
  ⟨fun x y => T x.1 y, fun x => x.2⟩

/-- `S₁(a) = S₁(b) = {a}`, `S₁(t) = {b, t}`. -/
def s1Tab : M3 → M3 → Prop
  | .t, m => m = .b ∨ m = .t
  | _, m => m = .a

def s1 : Spec M3 M3 := ⟨s1Tab, fun i => by cases i <;> first | exact ⟨_, Or.inr rfl⟩ | exact ⟨_, rfl⟩⟩

/-- `S₂(a) = {x}`, `S₂(b) = {y}`, no row at `t`: domain `{a, b}`. -/
def t2 : M3 → Two → Prop
  | .a, o => o = .x
  | .b, o => o = .y
  | .t, _ => False

theorem t2_fun {m : M3} {o o' : Two} (h : t2 m o) (h' : t2 m o') : o = o' := by
  cases m
  · exact (h : o = _).trans (h' : o' = _).symm
  · exact (h : o = _).trans (h' : o' = _).symm
  · exact (h : False).elim

theorem s1_liftedMono : s1.LiftedMono := by
  intro i j hij X _ hX
  have hij' : i = j ∨ j = M3.t := hij
  cases j with
  | t => exact ⟨.t, Or.inr rfl, fun _ _ => Or.inr rfl⟩
  | a =>
    rcases hij' with rfl | h
    · exact ⟨.a, rfl, fun z hz => Or.inl (hX z hz)⟩
    · cases h
  | b =>
    rcases hij' with rfl | h
    · exact ⟨.a, rfl, fun z hz => Or.inl (hX z hz)⟩
    · cases h

theorem restrict_t2_liftedMono : (restrict t2).LiftedMono := by
  intro i j hij X _ hX
  have hij' : i.1 = j.1 ∨ j.1 = M3.t := hij
  have hi : i.1 = j.1 := by
    rcases hij' with h | h
    · exact h
    · obtain ⟨o, ho⟩ := j.2
      rw [h] at ho
      exact (ho : False).elim
  obtain ⟨u, hu⟩ := j.2
  refine ⟨u, hu, fun z hz => ?_⟩
  have h : t2 i.1 z := hX z hz
  rw [hi] at h
  exact t2_fun h hu

/-- **Counterexample.** `S₁` satisfies Lifted Monotonicity, `S₂` satisfies it
on its own input domain `{a, b} ⊊ M`, the composed table `S₂ ∘ S₁` has a row
at every input, but the composition violates Lifted Monotonicity. -/
theorem restricted_middle_counterexample :
    s1.LiftedMono ∧ (restrict t2).LiftedMono ∧ (∀ i, ∃ o, tcomp s1.S t2 i o) ∧
      ¬ (restrict (tcomp s1.S t2)).LiftedMono := by
  have htot : ∀ i, ∃ o, tcomp s1.S t2 i o := by
    intro i
    cases i
    · exact ⟨.x, .a, rfl, rfl⟩
    · exact ⟨.x, .a, rfl, rfl⟩
    · exact ⟨.y, .b, Or.inl rfl, rfl⟩
  refine ⟨s1_liftedMono, restrict_t2_liftedMono, htot, ?_⟩
  intro h
  obtain ⟨u, ⟨m, hm, hu⟩, hall⟩ :=
    h ⟨.a, htot .a⟩ ⟨.t, htot .t⟩ (Or.inr rfl) [.x] (by simp)
      (fun z hz => by
        have : z = Two.x := by simpa using hz
        subst this; exact ⟨.a, rfl, rfl⟩)
  have hxu : Two.x = u := hall .x (by simp)
  rcases (hm : m = .b ∨ m = .t) with rfl | rfl
  · have : u = Two.y := hu
    exact two_ne (hxu.trans this)
  · exact (hu : False).elim

end Examples

end Comp
end CC
