import CoordCriterion.Appendix.Guarded
import CoordCriterion.Appendix.JointMono

/-!
# Dataflow graphs of stages (not in the paper; exploration)

Namespace `CC.Graph`.  Not cited by the paper.  Can arbitrary DAGs of
stages be assembled from sequential composition (`Comp.seq`) and a few
combinators, and do Lifted Monotonicity and Proper Coordination compose along
them?

* **Product** `prod sa sb` (independent sources side by side):
  `prod_liftedMono_iff` (LM componentwise; the `→` direction needs the other
  input type inhabited), `pstate`, `pstate_canon`, `exposable_pstate`
  (exposability at product states is componentwise), `step_pstate`,
  `reach_pstate` (every state reached by the product is a product state),
  `needsNoCommit_prod_iff`.
* **Tee** `tee : M → M × M` (copy).  `seq_tee_liftedMono_iff`: teeing an
  output changes nothing.  `dup S = seq tee (prod S S)` (run `S` twice) is
  also LM iff `S` is (`dup_liftedMono_iff`), but it is a different table
  unless `S` is functional (`seqTee_le_dup`, `seqTee_eq_dup_iff`).  The two
  copies of `dup S` may choose differently, so a downstream stage that relies
  on their agreement (`agree`) is proper behind `seq S tee` and not behind
  `dup S` (`tee_vs_dup`).
* **Merge** `merge : D × D → D` (join of a join-semilattice, e.g. union):
  `merge_monotone`, `merge_liftedMono`.
* **Partition** `split p : St V → St V × St V`: `split_monotone`,
  `merge_split` (partition then merge is the identity), `pair_monotone_iff`.
* **Graph-level theorem.**  `Expr` (stage expressions: nodes, sequential
  composition, product), `Expr.sem`, offered domains `ImgOn`, the per-node
  test `Expr.Ok`; `ok_ceOn`, `ok_liftedMono` (every node passes ⇒ the whole
  expression is LM on the offered inputs); `imgOn_prod` (independent sources
  offer the product of their images), `imgOn_seqTee` (a tee offers the
  diagonal), `ok_seq_node_iff` (the test of a node is Proper Coordination of
  its upstream).
* **Proper Coordination for products**: `img_prod`, `proper_prod`,
  `proper_prod_iff`, `proper_merge_iff` (a merging stage after two guards is
  proper iff it is LM on the product of their images), `proper_union`.
* **Parameterized composition** (App. D) as `seq (prod F id) G` up to
  re-association: `par_eq_seq_prod`, `par_liftedMono'`.
-/

namespace CC
namespace Graph

open Comp Joint Guard Classical

/-! ### Products of specifications -/

section Prod
variable {Ia Ib Ma Mb : Type} [PO Ia] [PO Ib] [PO Ma] [PO Mb]

/-- `𝒮_a ⊗ 𝒮_b`: rows `((i_a,i_b),(m_a,m_b))` with both component rows.  It
is total because both components are. -/
def prod (sa : Spec Ia Ma) (sb : Spec Ib Mb) : Spec (Ia × Ib) (Ma × Mb) where
  S i m := sa.S i.1 m.1 ∧ sb.S i.2 m.2
  total i :=
    let ⟨a, ha⟩ := sa.total i.1
    let ⟨b, hb⟩ := sb.total i.2
    ⟨(a, b), ha, hb⟩

variable {sa : Spec Ia Ma} {sb : Spec Ib Mb}

theorem prod_commonExpansion (ha : sa.CommonExpansion) (hb : sb.CommonExpansion) :
    (prod sa sb).CommonExpansion := by
  intro rows hrows j hj
  obtain ⟨ua, hua, halla⟩ := ha (rows.map fun r => (r.1.1, r.2.1))
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact (hrows p hp).1) j.1
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact (hj p hp).1)
  obtain ⟨ub, hub, hallb⟩ := hb (rows.map fun r => (r.1.2, r.2.2))
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact (hrows p hp).2) j.2
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact (hj p hp).2)
  exact ⟨(ua, ub), ⟨hua, hub⟩, fun r hr =>
    ⟨halla _ (List.mem_map.2 ⟨r, hr, rfl⟩), hallb _ (List.mem_map.2 ⟨r, hr, rfl⟩)⟩⟩

theorem commonExpansion_of_prod_left (b0 : Ib) (h : (prod sa sb).CommonExpansion) :
    sa.CommonExpansion := by
  intro rows hrows j hj
  obtain ⟨mb, hmb⟩ := sb.total b0
  obtain ⟨u, hu, hall⟩ := h (rows.map fun r => ((r.1, b0), (r.2, mb)))
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact ⟨hrows p hp, hmb⟩) (j, b0)
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact ⟨hj p hp, PO.refl _⟩)
  exact ⟨u.1, hu.1, fun r hr => (hall _ (List.mem_map.2 ⟨r, hr, rfl⟩)).1⟩

theorem commonExpansion_of_prod_right (a0 : Ia) (h : (prod sa sb).CommonExpansion) :
    sb.CommonExpansion := by
  intro rows hrows j hj
  obtain ⟨ma, hma⟩ := sa.total a0
  obtain ⟨u, hu, hall⟩ := h (rows.map fun r => ((a0, r.1), (ma, r.2)))
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact ⟨hma, hrows p hp⟩) (a0, j)
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact ⟨PO.refl _, hj p hp⟩)
  exact ⟨u.2, hu.2, fun r hr => (hall _ (List.mem_map.2 ⟨r, hr, rfl⟩)).2⟩

/-- **Products are LM componentwise.**  `←` always holds; `→` needs each
input type inhabited (with `I_b` empty the product is vacuously LM). -/
theorem prod_liftedMono_iff [Nonempty Ia] [Nonempty Ib] :
    (prod sa sb).LiftedMono ↔ sa.LiftedMono ∧ sb.LiftedMono := by
  simp only [liftedMono_iff_commonExpansion]
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => prod_commonExpansion h.1 h.2⟩
  · obtain ⟨b0⟩ := ‹Nonempty Ib›; exact commonExpansion_of_prod_left b0 h
  · obtain ⟨a0⟩ := ‹Nonempty Ia›; exact commonExpansion_of_prod_right a0 h

theorem prod_liftedMono (ha : sa.LiftedMono) (hb : sb.LiftedMono) : (prod sa sb).LiftedMono := by
  rw [liftedMono_iff_commonExpansion] at *
  exact prod_commonExpansion ha hb

/-- The product state `σ_a ⊗ σ_b`: remainder table the product of the two. -/
def pstate (σa : State sa) (σb : State sb) : State (prod sa sb) where
  cur := (σa.cur, σb.cur)
  R k u := σa.R k.1 u.1 ∧ σb.R k.2 u.2
  sub _ _ h := ⟨σa.sub _ _ h.1, σb.sub _ _ h.2⟩
  hasCur :=
    let ⟨a, ha⟩ := σa.hasCur
    let ⟨b, hb⟩ := σb.hasCur
    ⟨(a, b), ha, hb⟩
  above _ _ h := ⟨σa.above _ _ h.1, σb.above _ _ h.2⟩

theorem pstate_canon (ia : Ia) (ib : Ib) :
    pstate (canon sa ia) (canon sb ib) = canon (prod sa sb) (ia, ib) := by
  refine State.ext' rfl ?_
  funext k u; apply propext
  exact ⟨fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨h1, h3⟩, h2, h4⟩, fun ⟨⟨h1, h3⟩, h2, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩⟩

/-- **Exposability at a product state is componentwise.** -/
theorem exposable_pstate (σa : State sa) (σb : State sb) (oa : Ma) (ob : Mb) :
    Exposable (pstate σa σb) (oa, ob) ↔ Exposable σa oa ∧ Exposable σb ob := by
  constructor
  · intro hE
    refine ⟨fun k x hx hn => ?_, fun k x hx hn => ?_⟩
    · obtain ⟨b, hb⟩ := σb.hasCur
      obtain ⟨u, hu, h1, h2⟩ := hE (k, σb.cur) (x, b) ⟨hx, hb⟩ (fun h => hn h.1)
      exact ⟨u.1, hu.1, h1.1, h2.1⟩
    · obtain ⟨a, ha⟩ := σa.hasCur
      obtain ⟨u, hu, h1, h2⟩ := hE (σa.cur, k) (a, x) ⟨ha, hx⟩ (fun h => hn h.2)
      exact ⟨u.2, hu.2, h1.2, h2.2⟩
  · intro ⟨Ea, Eb⟩ k x hx _
    have ha : ∃ ua, σa.R k.1 ua ∧ oa ≼ ua ∧ x.1 ≼ ua :=
      if h : oa ≼ x.1 then ⟨x.1, hx.1, h, PO.refl _⟩ else Ea k.1 x.1 hx.1 h
    have hb : ∃ ub, σb.R k.2 ub ∧ ob ≼ ub ∧ x.2 ≼ ub :=
      if h : ob ≼ x.2 then ⟨x.2, hx.2, h, PO.refl _⟩ else Eb k.2 x.2 hx.2 h
    obtain ⟨ua, hua, h1a, h2a⟩ := ha
    obtain ⟨ub, hub, h1b, h2b⟩ := hb
    exact ⟨(ua, ub), ⟨hua, hub⟩, ⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩

/-- One event of the product from a product state ends at a product state,
reached by an event of each component (an input event `(j_a,j_b)` is an input
event on each side, an output event `(o_a,o_b)` an output event on each). -/
theorem step_pstate {σa : State sa} {σb : State sb} {e : Event (Ia × Ib) (Ma × Mb)}
    {τ : State (prod sa sb)} (h : Step (pstate σa σb) e τ) :
    ∃ (σa' : State sa) (σb' : State sb), τ = pstate σa' σb' ∧
      ∃ ea eb, Step σa ea σa' ∧ Step σb eb σb' := by
  cases h with
  | input _ j hj hc hR =>
    obtain ⟨u, hu1, hu2⟩ := hj
    refine ⟨⟨j.1, inputTable σa j.1, fun k x h => σa.sub k x h.1, ⟨u.1, hu1, PO.refl _⟩,
        fun _ _ h => h.2⟩,
      ⟨j.2, inputTable σb j.2, fun k x h => σb.sub k x h.1, ⟨u.2, hu2, PO.refl _⟩,
        fun _ _ h => h.2⟩, ?_, .input j.1, .input j.2,
      Step.input _ _ _ ⟨u.1, hu1⟩ rfl rfl, Step.input _ _ _ ⟨u.2, hu2⟩ rfl rfl⟩
    refine State.ext' hc ?_
    rw [hR]; funext k x; apply propext
    exact ⟨fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨h1, h3⟩, h2, h4⟩, fun ⟨⟨h1, h3⟩, h2, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩⟩
  | output _ o ho hc hR =>
    refine ⟨⟨σa.cur, outputTable σa o.1, fun k x h => σa.sub k x h.1, ⟨o.1, ho.1, PO.refl _⟩,
        fun k x h => σa.above k x h.1⟩,
      ⟨σb.cur, outputTable σb o.2, fun k x h => σb.sub k x h.1, ⟨o.2, ho.2, PO.refl _⟩,
        fun k x h => σb.above k x h.1⟩, ?_, .output o.1, .output o.2,
      Step.output _ _ _ ho.1 rfl rfl, Step.output _ _ _ ho.2 rfl rfl⟩
    refine State.ext' hc ?_
    rw [hR]; funext k x; apply propext
    exact ⟨fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨h1, h3⟩, h2, h4⟩, fun ⟨⟨h1, h3⟩, h2, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩⟩

/-- Every state reached by the product from a product state is a product
state. -/
theorem reach_pstate {σa : State sa} {σb : State sb} {es : List (Event (Ia × Ib) (Ma × Mb))}
    {τ : State (prod sa sb)} (h : Exec (pstate σa σb) es τ) :
    ∃ (σa' : State sa) (σb' : State sb), τ = pstate σa' σb' ∧ Reach σa σa' ∧ Reach σb σb' := by
  generalize hσ : pstate σa σb = σ at h
  induction h generalizing σa σb with
  | nil _ => exact ⟨σa, σb, hσ.symm, ⟨[], .nil _⟩, ⟨[], .nil _⟩⟩
  | cons hs _ ih =>
    subst hσ
    obtain ⟨σa', σb', rfl, ea, eb, ha, hb⟩ := step_pstate hs
    obtain ⟨σa'', σb'', h, ⟨la, hla⟩, ⟨lb, hlb⟩⟩ := ih rfl
    exact ⟨σa'', σb'', h, ⟨ea :: la, .cons ha hla⟩, ⟨eb :: lb, .cons hb hlb⟩⟩

/-- **Needing no commitment is componentwise** (through the exposure
boundary). -/
theorem needsNoCommit_prod_iff [Nonempty Ia] [Nonempty Ib] :
    NeedsNoCommit (prod sa sb) ↔ NeedsNoCommit sa ∧ NeedsNoCommit sb := by
  simp only [NeedsNoCommit, ← exposure_boundary, ← liftedMono_iff_commonExpansion]
  exact prod_liftedMono_iff

end Prod

/-! ### Tee: copying an output, versus running a stage twice -/

section Tee
variable {I M : Type} [PO I] [PO M]

/-- The copy `Δ(m) = (m, m)`. -/
def diag (m : M) : M × M := (m, m)

/-- The tee table `Δ`. -/
abbrev tee : Spec M (M × M) := graph diag

theorem diag_monotone : Monotone (diag (M := M)) := fun _ _ h => ⟨h, h⟩

/-- **Teeing an output changes nothing**: `Δ ∘ 𝒮` is LM iff `𝒮` is. -/
theorem seq_tee_liftedMono_iff (S : Spec I M) : (seq S tee).LiftedMono ↔ S.LiftedMono := by
  refine ⟨fun h => ?_, fun h => seq_liftedMono h ((graph_liftedMono_iff _).2 diag_monotone)⟩
  rw [liftedMono_iff_commonExpansion] at *
  intro rows hrows j hj
  obtain ⟨u, ⟨m, hm, hu⟩, hall⟩ := h (rows.map fun r => (r.1, diag r.2))
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact ⟨p.2, hrows p hp, rfl⟩) j
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact hj p hp)
  have e : u = diag m := hu
  subst e
  exact ⟨m, hm, fun r hr => (hall _ (List.mem_map.2 ⟨r, hr, rfl⟩)).1⟩

/-- Running `𝒮` twice on a copied input: `(𝒮 ⊗ 𝒮) ∘ Δ`. -/
def dup (S : Spec I M) : Spec I (M × M) := seq tee (prod S S)

theorem dup_S {S : Spec I M} {i : I} {p : M × M} : (dup S).S i p ↔ S.S i p.1 ∧ S.S i p.2 :=
  ⟨fun ⟨q, hq, h⟩ => by have e : q = diag i := hq; subst e; exact h,
   fun h => ⟨diag i, rfl, h⟩⟩

theorem seqTee_S {S : Spec I M} {i : I} {p : M × M} :
    (seq S tee).S i p ↔ p.1 = p.2 ∧ S.S i p.1 :=
  ⟨fun ⟨m, hm, hp⟩ => by have e : p = diag m := hp; subst e; exact ⟨rfl, hm⟩,
   fun ⟨h1, h2⟩ => ⟨p.1, h2, Prod.ext rfl h1.symm⟩⟩

/-- `dup 𝒮` is LM iff `𝒮` is: each copy alone is no harder than `𝒮`. -/
theorem dup_liftedMono_iff (S : Spec I M) : (dup S).LiftedMono ↔ S.LiftedMono := by
  refine ⟨fun h => ?_, fun h => seq_liftedMono ((graph_liftedMono_iff _).2 diag_monotone)
    (prod_liftedMono h h)⟩
  rw [liftedMono_iff_commonExpansion] at *
  intro rows hrows j hj
  obtain ⟨u, hu, hall⟩ := h (rows.map fun r => (r.1, diag r.2))
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        exact dup_S.2 ⟨hrows p hp, hrows p hp⟩) j
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact hj p hp)
  exact ⟨u.1, (dup_S.1 hu).1, fun r hr => (hall _ (List.mem_map.2 ⟨r, hr, rfl⟩)).1⟩

/-- Copying a chosen output is one of the behaviours of running twice. -/
theorem seqTee_le_dup (S : Spec I M) (i : I) (p : M × M) : (seq S tee).S i p → (dup S).S i p :=
  fun h => let ⟨e, h⟩ := seqTee_S.1 h; dup_S.2 ⟨h, e ▸ h⟩

/-- The two agree exactly when `𝒮` is functional: two copies of a
nondeterministic stage may choose differently. -/
theorem seqTee_eq_dup_iff (S : Spec I M) : (seq S tee).S = (dup S).S ↔ S.Functional := by
  constructor
  · intro h i o o' ho ho'
    have : (seq S tee).S i (o, o') := by rw [h]; exact dup_S.2 ⟨ho, ho'⟩
    exact (seqTee_S.1 this).1
  · intro hf
    funext i p; apply propext
    exact ⟨seqTee_le_dup S i p, fun h => let ⟨h1, h2⟩ := dup_S.1 h; seqTee_S.2 ⟨hf _ _ _ h1 h2, h1⟩⟩

end Tee

/-! #### The counterexample: one input, a nondeterministic LM stage -/

section TeeExample

/-- The two-element chain `lo ≼ hi`. -/
inductive Bit where
  | lo | hi
  deriving DecidableEq

instance : PO Bit where
  le a b := a = .lo ∨ b = .hi
  refl a := by cases a <;> simp
  trans := by
    intro a b c h1 h2
    rcases h1 with rfl | rfl
    · exact Or.inl rfl
    · rcases h2 with h | rfl
      · exact absurd h (by decide)
      · exact Or.inr rfl
  antisymm := by
    intro a b h1 h2
    cases a <;> cases b <;> simp_all

/-- One input; the stage may output `lo` or `hi`.  It is LM (`hi` refines
both), but not functional. -/
def coin : Spec Pt Bit := ⟨fun _ _ => True, fun _ => ⟨.lo, trivial⟩⟩

theorem coin_liftedMono : coin.LiftedMono :=
  fun _ _ _ _ _ _ => ⟨.hi, trivial, fun _ _ => Or.inr rfl⟩

/-- A downstream stage that compares the two copies. -/
def agree (p : Bit × Bit) : Two := if p.1 = p.2 then .x else .y

/-- **Tee versus running twice.**  For the LM, nondeterministic `coin`:
(1) `Δ ∘ coin` and `dup coin` are both LM;
(2) `agree ∘ Δ ∘ coin` is LM and the pipeline `Δ ∘ coin` guarding `agree` is
proper;
(3) `agree ∘ dup coin` is not LM, and the pipeline `dup coin` guarding `agree`
is not proper, although `agree` is not changed.
So the copies of `dup` must coordinate to agree; the tee needs nothing. -/
theorem tee_vs_dup :
    (seq coin tee).LiftedMono ∧ (dup coin).LiftedMono ∧
    (seq (seq coin tee) (graph agree)).LiftedMono ∧ Proper (seq coin tee) (graph agree) ∧
    ¬ (seq (dup coin) (graph agree)).LiftedMono ∧ ¬ Proper (dup coin) (graph agree) := by
  have hP : Proper (seq coin tee) (graph agree) := by
    rw [proper_iff]
    apply graph_ceOn
    intro a b ⟨_, ha⟩ ⟨_, hb⟩ _
    have ea := (seqTee_S.1 ha).1
    have eb := (seqTee_S.1 hb).1
    show agree a = agree b
    simp [agree, ea, eb]
  have hnot : ¬ (seq (dup coin) (graph agree)).LiftedMono := by
    intro h
    obtain ⟨u, _, hall⟩ := h Pt.pt Pt.pt trivial [Two.x, Two.y] (by simp)
      (by
        intro o ho
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
        rcases ho with rfl | rfl
        · exact ⟨(.lo, .lo), dup_S.2 ⟨trivial, trivial⟩, rfl⟩
        · exact ⟨(.lo, .hi), dup_S.2 ⟨trivial, trivial⟩, rfl⟩)
    have h1 : Two.x = u := hall _ (by simp)
    have h2 : Two.y = u := hall _ (by simp)
    exact two_ne (h1.trans h2.symm)
  refine ⟨(seq_tee_liftedMono_iff _).2 coin_liftedMono, (dup_liftedMono_iff _).2 coin_liftedMono,
    seq_liftedMono_img ((seq_tee_liftedMono_iff _).2 coin_liftedMono) (proper_iff.1 hP), hP,
    hnot, fun hP' => hnot (seq_liftedMono_img ((dup_liftedMono_iff _).2 coin_liftedMono)
      (proper_iff.1 hP'))⟩

end TeeExample

/-! ### Merge and partition -/

section MergeSplit
open Inst (JSL)

/-- Merge two streams: the join `(a, b) ↦ a ⊔ b` of a join-semilattice
(union, for sets). -/
def merge {D : Type} [PO D] [JSL D] (p : D × D) : D := JSL.join p.1 p.2

theorem merge_monotone {D : Type} [PO D] [JSL D] : Monotone (merge (D := D)) :=
  fun _ _ h => JSL.lub (PO.trans h.1 (JSL.le_l _ _)) (PO.trans h.2 (JSL.le_r _ _))

/-- **Merging two LM sources is LM** (product, then the composition lemma). -/
theorem merge_liftedMono {Ia Ib D : Type} [PO Ia] [PO Ib] [PO D] [JSL D]
    {sa : Spec Ia D} {sb : Spec Ib D} (ha : sa.LiftedMono) (hb : sb.LiftedMono) :
    (seq (prod sa sb) (graph merge)).LiftedMono :=
  seq_liftedMono (prod_liftedMono ha hb) ((graph_liftedMono_iff _).2 merge_monotone)

/-- A function into a product is monotone iff both components are. -/
theorem pair_monotone_iff {A B C : Type} [PO A] [PO B] [PO C] (f : A → B) (g : A → C) :
    Monotone (fun a => (f a, g a)) ↔ Monotone f ∧ Monotone g :=
  ⟨fun h => ⟨fun x y hxy => (h x y hxy).1, fun x y hxy => (h x y hxy).2⟩,
   fun ⟨hf, hg⟩ x y hxy => ⟨hf x y hxy, hg x y hxy⟩⟩

variable {V : Type}

/-- Route a set by a fixed predicate: `X ↦ (X ∩ p, X ∖ p)`. -/
def split (p : V → Prop) (X : IConf.St V) : IConf.St V × IConf.St V :=
  (fun v => X v ∧ p v, fun v => X v ∧ ¬ p v)

theorem split_monotone (p : V → Prop) : Monotone (split p) :=
  fun _ _ h => ⟨fun v hv => ⟨h v hv.1, hv.2⟩, fun v hv => ⟨h v hv.1, hv.2⟩⟩

/-- Partition then merge is the identity. -/
theorem merge_split (p : V → Prop) (X : IConf.St V) : merge (split p X) = X := by
  funext v; apply propext
  show (X v ∧ p v) ∨ (X v ∧ ¬ p v) ↔ X v
  exact ⟨fun h => h.elim (·.1) (·.1), fun h => if hp : p v then .inl ⟨h, hp⟩ else .inr ⟨h, hp⟩⟩

theorem seq_split_merge (p : V → Prop) :
    seq (graph (split p)) (graph merge) = graph (fun X : IConf.St V => X) := by
  rw [seq_graph]
  congr 1
  funext X; exact merge_split p X

end MergeSplit

/-! ### Offered domains and LM on a domain -/

section Offered
variable {I M O : Type} [PO I] [PO M] [PO O]

/-- The outputs `𝒮` offers when its inputs range over `D`. -/
def ImgOn (D : I → Prop) (sp : Spec I M) (m : M) : Prop := ∃ i, D i ∧ sp.S i m

theorem imgOn_univ (sp : Spec I M) : ImgOn (fun _ => True) sp = Img sp :=
  funext fun _ => propext ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, trivial, h⟩⟩

theorem ceOn_univ (sp : Spec I M) : CEOn sp (fun _ => True) ↔ sp.CommonExpansion :=
  ⟨fun h rows hr j hj => h rows (fun r h' => ⟨trivial, hr r h'⟩) j trivial hj,
   fun h => ceOn_of_ce h _⟩

/-- **Sequential composition on a domain.**  `𝒮₁` LM on `D` and `𝒮₂` LM on
what `𝒮₁` offers from `D` give `𝒮₂ ∘ 𝒮₁` LM on `D`.  With `D` everything
this is `Joint.seq_liftedMono_img`. -/
theorem ceOn_seq {s1 : Spec I M} {s2 : Spec M O} {D : I → Prop}
    (h1 : CEOn s1 D) (h2 : CEOn s2 (ImgOn D s1)) : CEOn (seq s1 s2) D := by
  intro rows hrows j hDj hj
  obtain ⟨L, hL1, hL2⟩ := choose_list (fun (r : I × O) m => s1.S r.1 m ∧ s2.S m r.2)
    rows (fun r h => (hrows r h).2)
  obtain ⟨m, hm, hmall⟩ := h1 (L.map fun p => (p.1.1, p.2))
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        exact ⟨(hrows _ (hL2 p hp).1).1, (hL2 p hp).2.1⟩) j hDj
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact hj _ (hL2 p hp).1)
  obtain ⟨u, hu, huall⟩ := h2 (L.map fun p => (p.2, p.1.2))
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        exact ⟨⟨p.1.1, (hrows _ (hL2 p hp).1).1, (hL2 p hp).2.1⟩, (hL2 p hp).2.2⟩)
    m ⟨j, hDj, hm⟩
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        exact hmall (p.1.1, p.2) (List.mem_map.2 ⟨p, hp, rfl⟩))
  refine ⟨u, ⟨m, hm, hu⟩, fun r hr => ?_⟩
  obtain ⟨b, hb⟩ := hL1 r hr
  exact huall (b, r.2) (List.mem_map.2 ⟨(r, b), hb, rfl⟩)

variable {Ia Ib Ma Mb : Type} [PO Ia] [PO Ib] [PO Ma] [PO Mb]

/-- **Products on product domains.** -/
theorem ceOn_prod {sa : Spec Ia Ma} {sb : Spec Ib Mb} {Da : Ia → Prop} {Db : Ib → Prop}
    (ha : CEOn sa Da) (hb : CEOn sb Db) : CEOn (prod sa sb) (fun i => Da i.1 ∧ Db i.2) := by
  intro rows hrows j hDj hj
  obtain ⟨ua, hua, halla⟩ := ha (rows.map fun r => (r.1.1, r.2.1))
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        exact ⟨(hrows p hp).1.1, (hrows p hp).2.1⟩) j.1 hDj.1
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact (hj p hp).1)
  obtain ⟨ub, hub, hallb⟩ := hb (rows.map fun r => (r.1.2, r.2.2))
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        exact ⟨(hrows p hp).1.2, (hrows p hp).2.2⟩) j.2 hDj.2
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact (hj p hp).2)
  exact ⟨(ua, ub), ⟨hua, hub⟩, fun r hr =>
    ⟨halla _ (List.mem_map.2 ⟨r, hr, rfl⟩), hallb _ (List.mem_map.2 ⟨r, hr, rfl⟩)⟩⟩

/-- Products on any domain: test each component on its projection.  (Sound,
but it forgets correlation between the components; that is harmless here,
since each component sees only its own coordinate.) -/
theorem ceOn_prod_proj {sa : Spec Ia Ma} {sb : Spec Ib Mb} {D : Ia × Ib → Prop}
    (ha : CEOn sa (fun a => ∃ b, D (a, b))) (hb : CEOn sb (fun b => ∃ a, D (a, b))) :
    CEOn (prod sa sb) D :=
  ceOn_mono (fun i h => ⟨⟨i.2, h⟩, ⟨i.1, h⟩⟩) (ceOn_prod ha hb)

/-- Conversely, a product on a product domain with `D_b` inhabited is LM on
`D_a` in its first component. -/
theorem ceOn_of_prod_left {sa : Spec Ia Ma} {sb : Spec Ib Mb} {Da : Ia → Prop} {Db : Ib → Prop}
    {b0 : Ib} (hb0 : Db b0) (h : CEOn (prod sa sb) (fun i => Da i.1 ∧ Db i.2)) : CEOn sa Da := by
  intro rows hrows j hDj hj
  obtain ⟨mb, hmb⟩ := sb.total b0
  obtain ⟨u, hu, hall⟩ := h (rows.map fun r => ((r.1, b0), (r.2, mb)))
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        exact ⟨⟨(hrows p hp).1, hb0⟩, (hrows p hp).2, hmb⟩) (j, b0) ⟨hDj, hb0⟩
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact ⟨hj p hp, PO.refl _⟩)
  exact ⟨u.1, hu.1, fun r hr => (hall _ (List.mem_map.2 ⟨r, hr, rfl⟩)).1⟩

theorem ceOn_of_prod_right {sa : Spec Ia Ma} {sb : Spec Ib Mb} {Da : Ia → Prop} {Db : Ib → Prop}
    {a0 : Ia} (ha0 : Da a0) (h : CEOn (prod sa sb) (fun i => Da i.1 ∧ Db i.2)) : CEOn sb Db := by
  intro rows hrows j hDj hj
  obtain ⟨ma, hma⟩ := sa.total a0
  obtain ⟨u, hu, hall⟩ := h (rows.map fun r => ((a0, r.1), (ma, r.2)))
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        exact ⟨⟨ha0, (hrows p hp).1⟩, hma, (hrows p hp).2⟩) (a0, j) ⟨ha0, hDj⟩
    (by intro r hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr; exact ⟨PO.refl _, hj p hp⟩)
  exact ⟨u.2, hu.2, fun r hr => (hall _ (List.mem_map.2 ⟨r, hr, rfl⟩)).2⟩

/-- **Independent sources offer the product of their offers.** -/
theorem imgOn_prod {sa : Spec Ia Ma} {sb : Spec Ib Mb} {Da : Ia → Prop} {Db : Ib → Prop}
    (m : Ma × Mb) :
    ImgOn (fun i => Da i.1 ∧ Db i.2) (prod sa sb) m ↔ ImgOn Da sa m.1 ∧ ImgOn Db sb m.2 :=
  ⟨fun ⟨i, ⟨h1, h2⟩, h3, h4⟩ => ⟨⟨i.1, h1, h3⟩, ⟨i.2, h2, h4⟩⟩,
   fun ⟨⟨a, h1, h3⟩, ⟨b, h2, h4⟩⟩ => ⟨(a, b), ⟨h1, h2⟩, h3, h4⟩⟩

/-- **A tee offers the diagonal** of what its upstream offers. -/
theorem imgOn_seqTee {S : Spec I M} {D : I → Prop} (p : M × M) :
    ImgOn D (seq S tee) p ↔ p.1 = p.2 ∧ ImgOn D S p.1 :=
  ⟨fun ⟨i, hi, h⟩ => let ⟨e, h⟩ := seqTee_S.1 h; ⟨e, i, hi, h⟩,
   fun ⟨e, i, hi, h⟩ => ⟨i, hi, seqTee_S.2 ⟨e, h⟩⟩⟩

/-- Running twice offers the pairs of outputs at a common input. -/
theorem imgOn_dup {S : Spec I M} {D : I → Prop} (p : M × M) :
    ImgOn D (dup S) p ↔ ∃ i, D i ∧ S.S i p.1 ∧ S.S i p.2 :=
  ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, dup_S.1 h⟩, fun ⟨i, hi, h⟩ => ⟨i, hi, dup_S.2 h⟩⟩

end Offered

/-! ### Stage expressions and the graph-level theorem -/

/-- A partially ordered type, bundled so that expressions can be indexed by
their input and output orders. -/
structure POT where
  carrier : Type
  po : PO carrier

instance (A : POT) : PO A.carrier := A.po

/-- The product order. -/
def POT.prod (A B : POT) : POT := ⟨A.carrier × B.carrier, instPOProd⟩

/-- **Stage expressions**: nodes (any specification, including glue tables),
sequential composition, and products.  Fan-out is a `tee` node, fan-in a
node on a product (e.g. `merge`). -/
inductive Expr : POT → POT → Type 1 where
  | node {A B : POT} (sp : Spec A.carrier B.carrier) : Expr A B
  | comp {A B C : POT} (e1 : Expr A B) (e2 : Expr B C) : Expr A C
  | par {A B C D : POT} (e1 : Expr A B) (e2 : Expr C D) : Expr (A.prod C) (B.prod D)

namespace Expr

/-- The specification an expression denotes. -/
def sem : {A B : POT} → Expr A B → Spec A.carrier B.carrier
  | _, _, node sp => sp
  | _, _, comp e1 e2 => seq e1.sem e2.sem
  | _, _, par e1 e2 => prod e1.sem e2.sem

/-- **The per-node test** on offered domains: each node is LM on what
everything upstream of it offers, given that the expression's inputs range
over `D`.  Through a product each component is tested on its projection. -/
def Ok : {A B : POT} → Expr A B → (A.carrier → Prop) → Prop
  | _, _, node sp, D => CEOn sp D
  | _, _, comp e1 e2, D => Ok e1 D ∧ Ok e2 (ImgOn D e1.sem)
  | _, _, par e1 e2, D => Ok e1 (fun a => ∃ c, D (a, c)) ∧ Ok e2 (fun c => ∃ a, D (a, c))

/-- **Graph-level theorem.**  If every node passes its test, the whole
expression is LM on `D`. -/
theorem ok_ceOn {A B : POT} (e : Expr A B) {D : A.carrier → Prop} (h : e.Ok D) :
    CEOn e.sem D := by
  induction e with
  | node sp => exact h
  | comp e1 e2 ih1 ih2 => exact ceOn_seq (ih1 h.1) (ih2 h.2)
  | par e1 e2 ih1 ih2 => exact ceOn_prod_proj (ih1 h.1) (ih2 h.2)

/-- With all inputs offered, every node passing its test makes the whole
expression Lifted-Monotone. -/
theorem ok_liftedMono {A B : POT} (e : Expr A B) (h : e.Ok (fun _ => True)) :
    e.sem.LiftedMono :=
  (liftedMono_iff_commonExpansion _).2 ((ceOn_univ _).1 (ok_ceOn e h))

/-- An LM node passes on any domain. -/
theorem ok_node_of_liftedMono {A B : POT} {sp : Spec A.carrier B.carrier} (h : sp.LiftedMono)
    (D : A.carrier → Prop) : (node sp).Ok D :=
  ceOn_of_ce ((liftedMono_iff_commonExpansion _).1 h) D

/-- A function node passes on `D` when the function is monotone on `D`. -/
theorem ok_fn {A B : POT} {f : A.carrier → B.carrier} {D : A.carrier → Prop}
    (hf : ∀ a b, D a → D b → a ≼ b → f a ≼ f b) : (node (graph f)).Ok D :=
  graph_ceOn hf

/-- **The test of a node is Proper Coordination** of its upstream: a node
`𝒦` after `e` passes iff `e` passes and the pipeline `e` guarding `𝒦` is
proper. -/
theorem ok_comp_node_iff {A B C : POT} (e : Expr A B) (sk : Spec B.carrier C.carrier) :
    (comp e (node sk)).Ok (fun _ => True) ↔ e.Ok (fun _ => True) ∧ Proper e.sem sk := by
  show e.Ok _ ∧ CEOn sk (ImgOn _ e.sem) ↔ _
  rw [imgOn_univ, proper_iff]

end Expr

/-! #### Tee versus running twice, as expressions -/

section ExprExample
open Expr

def PtT : POT := ⟨Pt, inferInstance⟩
def BitT : POT := ⟨Bit, inferInstance⟩
def TwoT : POT := ⟨Two, inferInstance⟩

/-- `agree ∘ Δ ∘ coin`: the node test passes. -/
def teeE : Expr PtT TwoT :=
  comp (comp (node (A := PtT) (B := BitT) coin) (node (B := BitT.prod BitT) (graph diag)))
    (node (graph agree))

/-- `agree ∘ (coin ⊗ coin) ∘ Δ`: the test fails at `agree`, whose offered
domain is all of `{lo,hi}²`, and the composite is not LM. -/
def dupE : Expr PtT TwoT :=
  comp (comp (node (B := PtT.prod PtT) (graph diag))
      (par (node (A := PtT) (B := BitT) coin) (node (A := PtT) (B := BitT) coin)))
    (node (A := BitT.prod BitT) (graph agree))

theorem teeE_ok : teeE.Ok (fun _ => True) ∧ teeE.sem.LiftedMono := by
  have : teeE.Ok (fun _ => True) := by
    refine ⟨⟨ok_node_of_liftedMono coin_liftedMono _, ok_fn fun a b _ _ h => ⟨h, h⟩⟩, ?_⟩
    apply ok_fn
    rintro a b ⟨_, _, m, _, ha⟩ ⟨_, _, m', _, hb⟩ _
    have ea : a = diag m := ha
    have eb : b = diag m' := hb
    subst ea eb
    show agree (m, m) = agree (m', m')
    cases m <;> cases m' <;> rfl
  exact ⟨this, ok_liftedMono _ this⟩

theorem dupE_not : ¬ dupE.Ok (fun _ => True) ∧ ¬ dupE.sem.LiftedMono := by
  have hnot : ¬ dupE.sem.LiftedMono := (tee_vs_dup).2.2.2.2.1
  exact ⟨fun h => hnot (ok_liftedMono _ h), hnot⟩

end ExprExample

/-! ### Proper Coordination for products -/

section ProperProd
variable {Ia Ib Ma Mb Oa Ob O : Type} [PO Ia] [PO Ib] [PO Ma] [PO Mb] [PO Oa] [PO Ob] [PO O]
variable {sa : Spec Ia Ma} {sb : Spec Ib Mb}

theorem img_prod : Img (prod sa sb) = fun m => Img sa m.1 ∧ Img sb m.2 :=
  funext fun _ => propext
    ⟨fun ⟨i, h1, h2⟩ => ⟨⟨i.1, h1⟩, ⟨i.2, h2⟩⟩, fun ⟨⟨a, h1⟩, ⟨b, h2⟩⟩ => ⟨(a, b), h1, h2⟩⟩

/-- **A stage after two independent guards** (e.g. a merge) is proper iff it
is LM on the product of their images. -/
theorem proper_merge_iff {mg : Spec (Ma × Mb) O} :
    Proper (prod sa sb) mg ↔ CEOn mg (fun m => Img sa m.1 ∧ Img sb m.2) := by
  rw [proper_iff, img_prod]

/-- **Products of proper pipelines are proper.** -/
theorem proper_prod {ka : Spec Ma Oa} {kb : Spec Mb Ob} (ha : Proper sa ka) (hb : Proper sb kb) :
    Proper (prod sa sb) (prod ka kb) :=
  proper_merge_iff.2 (ceOn_prod (proper_iff.1 ha) (proper_iff.1 hb))

theorem proper_prod_iff [Nonempty Ia] [Nonempty Ib] {ka : Spec Ma Oa} {kb : Spec Mb Ob} :
    Proper (prod sa sb) (prod ka kb) ↔ Proper sa ka ∧ Proper sb kb := by
  refine ⟨fun h => ?_, fun h => proper_prod h.1 h.2⟩
  have h := proper_merge_iff.1 h
  obtain ⟨a0⟩ := ‹Nonempty Ia›
  obtain ⟨b0⟩ := ‹Nonempty Ib›
  obtain ⟨ma, hma⟩ := sa.total a0
  obtain ⟨mb, hmb⟩ := sb.total b0
  exact ⟨proper_iff.2 (ceOn_of_prod_left ⟨b0, hmb⟩ h),
    proper_iff.2 (ceOn_of_prod_right ⟨a0, hma⟩ h)⟩

/-- Merging by a join is always proper. -/
theorem proper_union {D : Type} [PO D] [Inst.JSL D] {sa : Spec Ia D} {sb : Spec Ib D} :
    Proper (prod sa sb) (graph merge) :=
  proper_of_ce (graph_commonExpansion merge_monotone)

end ProperProd

/-! ### Independently parameterized composition is a product -/

section Par
variable {I J A B C : Type} [PO I] [PO J] [PO A] [PO B] [PO C]

/-- Re-associate the input `(i, (j, a))` as `((i, a), j)`. -/
def assocIn (x : I × (J × A)) : (I × A) × J := ((x.1, x.2.2), x.2.1)

def swapP (p : B × J) : J × B := (p.2, p.1)

theorem assocIn_monotone : Monotone (assocIn (I := I) (J := J) (A := A)) :=
  fun _ _ h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩

theorem swapP_monotone : Monotone (swapP (B := B) (J := J)) := fun _ _ h => ⟨h.2, h.1⟩

/-- **`G ⋆ F` is `G ∘ swap ∘ (F ⊗ id_J) ∘ assoc`.** -/
theorem par_eq_seq_prod (F : Spec (I × A) B) (G : Spec (J × B) C) :
    par F G = seq (graph assocIn) (seq (prod F (graph (fun j : J => j)))
      (seq (graph swapP) G)) := by
  apply Comp.Spec.ext'
  funext x c; apply propext
  constructor
  · rintro ⟨b, hF, hG⟩
    exact ⟨assocIn x, rfl, (b, x.2.1), ⟨hF, rfl⟩, (x.2.1, b), rfl, hG⟩
  · rintro ⟨y, hy, m, ⟨hF, hm⟩, z, hz, hG⟩
    have ey : y = assocIn x := hy
    have ez : z = swapP m := hz
    subst ey ez
    have e2 : m.2 = x.2.1 := hm
    exact ⟨m.1, hF, by rw [← e2]; exact hG⟩

/-- Lemma lem:parameterized-composition, re-derived from products and the
composition lemma. -/
theorem par_liftedMono' {F : Spec (I × A) B} {G : Spec (J × B) C}
    (hF : F.LiftedMono) (hG : G.LiftedMono) : (par F G).LiftedMono := by
  rw [par_eq_seq_prod]
  exact seq_liftedMono ((graph_liftedMono_iff _).2 assocIn_monotone)
    (seq_liftedMono (prod_liftedMono hF ((graph_liftedMono_iff _).2 fun _ _ h => h))
      (seq_liftedMono ((graph_liftedMono_iff _).2 swapP_monotone) hG))

end Par

end Graph
end CC
