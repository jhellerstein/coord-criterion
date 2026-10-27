import CoordCriterion.CompleteCALM.Theorem

/-!
# Cofinal specifications (not yet in the paper text)

A declared specification `S` is *cofinal* in a specification `T` over the
same ordered inputs and outputs when

* (Realizability) every row of `S` is a row of `T`, and
* (Domination) every row `(i, o)` of `T` is dominated by a row `(i, u)` of
  `S` at the same input, `o ≼ u`.

Then `S` satisfies Lifted Monotonicity iff `T` does, and (by Complete CALM)
`S` is consistent iff `T` is (`liftedMono_iff_of_cofinal`,
`consistent_iff_of_cofinal`).  Both directions go through the
common-expansion form, and each direction uses both conditions.  No extra
hypothesis is needed.  (Over the same inputs totality plays no role: the
upper bound of a family of rows is an input of both specifications.  The
Lean proof goes through `CofinalAlong id`, which reads the bound's preimage
off a row of `S` and so cites `S.total`.)

When the inputs differ, `CofinalAlong φ S T` compares `T` over inputs `I`
with `S` over inputs `J` along a map `φ : I → J`:

* (Embedding) `a ≼ b ↔ φ a ≼ φ b`;
* (Realizability) every row `(j, o)` of `S` is `(φ i, o)` for a row `(i, o)`
  of `T`;
* (Domination) every row `(i, o)` of `T` is dominated by a row `(φ i, u)`
  of `S`.

Then again `S.LiftedMono ↔ T.LiftedMono` (`liftedMono_iff_of_cofinalAlong`).
Here the totality of `S` is used: with Realizability it makes `φ`
surjective, so `φ` is an order isomorphism.  The direction
`S.LiftedMono → T.LiftedMono` uses only that `φ` is monotone and injective
(`liftedMono_of_cofinalAlong`), and the converse uses only that `φ`
reflects the order (`liftedMono_of_cofinalAlong'`).  Without surjectivity
the converse fails: `S` may be arbitrary at inputs outside the image.
-/

namespace CC

section
variable {I J O : Type} [PO I] [PO J] [PO O]

/-- `S` is cofinal in `T` along `φ : I → J`: `φ` is an order embedding,
every row of `S` is realized by a row of `T`, and every row of `T` is
dominated by a row of `S` at the image of its input. -/
structure CofinalAlong (φ : I → J) (S : Spec J O) (T : Spec I O) : Prop where
  emb : ∀ a b, a ≼ b ↔ φ a ≼ φ b
  real : ∀ j o, S.S j o → ∃ i, φ i = j ∧ T.S i o
  dom : ∀ i o, T.S i o → ∃ u, S.S (φ i) u ∧ o ≼ u

/-- `S` is cofinal in `T` (same inputs): every row of `S` is a row of `T`
(Realizability), and every row of `T` is dominated by a row of `S` at the
same input (Domination). -/
structure Cofinal (S T : Spec I O) : Prop where
  real : ∀ i o, S.S i o → T.S i o
  dom : ∀ i o, T.S i o → ∃ u, S.S i u ∧ o ≼ u

/-- Choice over a finite list. -/
theorem choose_list' {R X : Type} {p : R → X → Prop} :
    ∀ rows : List R, (∀ r ∈ rows, ∃ x, p r x) →
      ∃ l : List (R × X), l.map Prod.fst = rows ∧ ∀ q ∈ l, p q.1 q.2
  | [], _ => ⟨[], rfl, fun _ h => nomatch h⟩
  | r :: rows, h => by
    obtain ⟨x, hx⟩ := h r (List.mem_cons_self ..)
    obtain ⟨l, hl, hp⟩ := choose_list' rows fun r hr => h r (List.mem_cons_of_mem _ hr)
    refine ⟨(r, x) :: l, by simp [hl], fun q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hx
    · exact hp q hq

/-- From `S` to `T`: if `φ` is monotone and injective, every row of `T` is
dominated by a row of `S` at the image of its input, and rows of `S` at
images are rows of `T`, then the common-expansion condition passes from `S`
to `T`. -/
theorem commonExpansion_of_dominated (φ : I → J) {S : Spec J O} {T : Spec I O}
    (hmono : ∀ a b, a ≼ b → φ a ≼ φ b)
    (hreal : ∀ i o, S.S (φ i) o → T.S i o)
    (hdom : ∀ i o, T.S i o → ∃ u, S.S (φ i) u ∧ o ≼ u)
    (hS : S.CommonExpansion) : T.CommonExpansion := by
  intro rows hrows j hj
  obtain ⟨l, hl, hp⟩ := choose_list' (p := fun (r : I × O) u => S.S (φ r.1) u ∧ r.2 ≼ u)
    rows fun r hr => hdom r.1 r.2 (hrows r hr)
  have hmem : ∀ q ∈ l, q.1 ∈ rows := fun q hq => hl ▸ List.mem_map_of_mem hq
  obtain ⟨u, hu, hall⟩ := hS (l.map fun q => (φ q.1.1, q.2))
    (fun r hr => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
      exact (hp q hq).1)
    (φ j)
    (fun r hr => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
      exact hmono _ _ (hj q.1 (hmem q hq)))
  refine ⟨u, hreal j u hu, fun r hr => ?_⟩
  rw [← hl] at hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
  exact PO.trans (hp q hq).2 (hall _ (List.mem_map_of_mem hq))

/-- From `T` to `S`: if `φ` reflects the order, every row of `S` is realized
by a row of `T` at a preimage of its input, and every row of `T` is
dominated by a row of `S`, then the common-expansion condition passes from
`T` to `S`.  (Totality of `S` makes `φ` surjective here.) -/
theorem commonExpansion_of_realized (φ : I → J) {S : Spec J O} {T : Spec I O}
    (hrefl : ∀ a b, φ a ≼ φ b → a ≼ b)
    (hreal : ∀ j o, S.S j o → ∃ i, φ i = j ∧ T.S i o)
    (hdom : ∀ i o, T.S i o → ∃ u, S.S (φ i) u ∧ o ≼ u)
    (hT : T.CommonExpansion) : S.CommonExpansion := by
  intro rows hrows j hj
  obtain ⟨l, hl, hp⟩ := choose_list' (p := fun (r : J × O) i => φ i = r.1 ∧ T.S i r.2)
    rows fun r hr => hreal r.1 r.2 (hrows r hr)
  have hmem : ∀ q ∈ l, q.1 ∈ rows := fun q hq => hl ▸ List.mem_map_of_mem hq
  obtain ⟨o0, ho0⟩ := S.total j
  obtain ⟨i, rfl, _⟩ := hreal j o0 ho0
  obtain ⟨u, hu, hall⟩ := hT (l.map fun q => (q.2, q.1.2))
    (fun r hr => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
      exact (hp q hq).2)
    i
    (fun r hr => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
      apply hrefl
      rw [(hp q hq).1]
      exact hj q.1 (hmem q hq))
  obtain ⟨u', hu', huu'⟩ := hdom i u hu
  refine ⟨u', hu', fun r hr => ?_⟩
  rw [← hl] at hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
  exact PO.trans (hall _ (List.mem_map_of_mem hq)) huu'

theorem CofinalAlong.inj {φ : I → J} {S : Spec J O} {T : Spec I O}
    (h : CofinalAlong φ S T) {a b : I} (e : φ a = φ b) : a = b :=
  PO.antisymm ((h.emb a b).2 (e ▸ PO.refl _)) ((h.emb b a).2 (e ▸ PO.refl _))

/-- Rows of `S` at images are rows of `T`. -/
theorem CofinalAlong.real' {φ : I → J} {S : Spec J O} {T : Spec I O}
    (h : CofinalAlong φ S T) (i : I) (o : O) (ho : S.S (φ i) o) : T.S i o := by
  obtain ⟨i', e, h'⟩ := h.real _ o ho
  exact h.inj e ▸ h'

/-- `S.LiftedMono → T.LiftedMono` along a cofinal map. -/
theorem liftedMono_of_cofinalAlong {φ : I → J} {S : Spec J O} {T : Spec I O}
    (h : CofinalAlong φ S T) (hS : S.LiftedMono) : T.LiftedMono :=
  (liftedMono_iff_commonExpansion T).2 <|
    commonExpansion_of_dominated φ (fun a b => (h.emb a b).1) h.real' h.dom
      ((liftedMono_iff_commonExpansion S).1 hS)

/-- `T.LiftedMono → S.LiftedMono` along a cofinal map. -/
theorem liftedMono_of_cofinalAlong' {φ : I → J} {S : Spec J O} {T : Spec I O}
    (h : CofinalAlong φ S T) (hT : T.LiftedMono) : S.LiftedMono :=
  (liftedMono_iff_commonExpansion S).2 <|
    commonExpansion_of_realized φ (fun a b => (h.emb a b).2) h.real h.dom
      ((liftedMono_iff_commonExpansion T).1 hT)

/-- **Cofinality along an order embedding.**  If `S` is cofinal in `T`
along `φ`, then `S` satisfies Lifted Monotonicity iff `T` does, and `S` is
consistent iff `T` is. -/
theorem liftedMono_iff_of_cofinalAlong {φ : I → J} {S : Spec J O} {T : Spec I O}
    (h : CofinalAlong φ S T) :
    (S.LiftedMono ↔ T.LiftedMono) ∧ (S.Consistent ↔ T.Consistent) := by
  have e : S.LiftedMono ↔ T.LiftedMono :=
    ⟨liftedMono_of_cofinalAlong h, liftedMono_of_cofinalAlong' h⟩
  exact ⟨e, by rw [complete_calm, complete_calm]; exact e⟩

end

section
variable {I O : Type} [PO I] [PO O]

/-- Cofinality over the same inputs is cofinality along the identity. -/
theorem Cofinal.along {S T : Spec I O} (h : Cofinal S T) : CofinalAlong id S T where
  emb _ _ := Iff.rfl
  real i o ho := ⟨i, rfl, h.real i o ho⟩
  dom := h.dom

/-- **Cofinality lemma.**  If every row of `S` is a row of `T` and every
row of `T` is dominated by a row of `S` at the same input, then `S`
satisfies Lifted Monotonicity iff `T` does. -/
theorem liftedMono_iff_of_cofinal {S T : Spec I O} (h : Cofinal S T) :
    S.LiftedMono ↔ T.LiftedMono :=
  (liftedMono_iff_of_cofinalAlong h.along).1

/-- The same for consistency (via Complete CALM). -/
theorem consistent_iff_of_cofinal {S T : Spec I O} (h : Cofinal S T) :
    S.Consistent ↔ T.Consistent :=
  (liftedMono_iff_of_cofinalAlong h.along).2

/-- The common-expansion form of the cofinality lemma. -/
theorem commonExpansion_iff_of_cofinal {S T : Spec I O} (h : Cofinal S T) :
    S.CommonExpansion ↔ T.CommonExpansion := by
  rw [← liftedMono_iff_commonExpansion, ← liftedMono_iff_commonExpansion]
  exact liftedMono_iff_of_cofinal h

end

end CC
