import CoordCriterion.Appendix.Applications

/-!
# Classical problems: four patterns and their instances (Appendix G, `app:additional-applications`)

Namespace `CC.Apps` (extends `Appendix/Applications.lean`).

* Pattern lemmas: `directed_of_join`, `liftedMono_of_join` (fibers closed under a
  binary upper bound, plus Relational Monotonicity), `accumulating_monotone`
  (sets of facts under inclusion; Lemma `lem:accumulating`);
  `order_no_common`, `order_conflict`, `order_conflict_fiber` (Lemma
  `lem:order-commitment`); `bounded_no_common`, `bounded_values` (Lemma
  `lem:bounded-values`); `ruling_out` (Lemma `lem:ruling-out`); `no_cap_of_not_liftedMono`, `canon_incompatible`,
  `pattern_consequences_neg`, `pattern_consequences_pos`.
* Table `tab:classical-problems`: `bcastSpec` (reliable broadcast),
  `prefixSpec` (causal broadcast, global snapshot), `counterSpec` (grow-only
  counter), `tobSpec` (total-order broadcast), `queueSpec` (causal FIFO
  queue), `snapSpec` (atomic snapshot), `ksetSpec` (consensus, `k`-set
  agreement, leader election), `renSpec` / `renSpecB` (renaming);
  `bcast_liftedMono`, `prefix_liftedMono_accumulating`, `counter_liftedMono`,
  `Seq`, `PlacesBefore`, `placesBefore_mono`, `placesBefore_asymm`,
  `seq_common_iff`, `tob_not_liftedMono`, `Decides`, `leader_not_liftedMono`.
* Consensus: `evidence_liftedMono`, `evidence_legal`, `evidenceSpec`,
  `evidenceSpec_monotone` (Prop. `prop:monotone-evidence`).
* `k`-set agreement: `kset_grow`, `kset_relMono`, `kset_union_row`,
  `kset_not_directed`.
* Renaming: `ren_relMono` (tight renaming), `ren_via_bounded`, `renSpecB` and
  `renB_not_liftedMono` (any namespace bound `f` with `n ≤ f n`).
* Atomic snapshot: `snapSpec`, `Reflects`, `reflects_mono`,
  `reflects_asymm`, `snap_not_liftedMono`.
* Causal FIFO queue: `queueSpec`, `queue_grow`, `queue_relMono`, `below_seq`,
  `queue_concurrent`, `queue_not_directed`, `queue_chain_comparable`, `queue_directed_iff`,
  `queueChain_liftedMono`, `queue_order_commitment`, and the variant without
  the no-skipping rule, `skipSpec_not_directed`.

Modeling choices are noted on each definition.  Decidable equality is
assumed where a construction compares events; classical choice is used to
sort finite sets.
-/

namespace CC
namespace Apps

open CC.Txn

/-! ### Pattern lemmas -/

section Patterns
variable {I O : Type} [PO I] [PO O]

/-- Fibers closed under a binary upper bound are directed. -/
theorem directed_of_join {sp : Spec I O} (join : O → O → O)
    (hl : ∀ a b, a ≼ join a b) (hr : ∀ a b, b ≼ join a b)
    (hc : ∀ j a b, sp.P j a → sp.P j b → sp.P j (join a b)) : sp.DirectedOutputs := by
  intro i X hX hall
  have key : ∀ (Y : List O) (x0 : O), sp.P i x0 → (∀ y ∈ Y, sp.P i y) →
      ∃ u, sp.P i u ∧ x0 ≼ u ∧ ∀ y ∈ Y, y ≼ u := by
    intro Y
    induction Y with
    | nil => intro x0 h0 _; exact ⟨x0, h0, PO.refl _, by simp⟩
    | cons y ys ih =>
      intro x0 h0 hY
      obtain ⟨u, hu, h0u, hys⟩ := ih x0 h0 (fun z hz => hY z (List.mem_cons_of_mem _ hz))
      refine ⟨join y u, hc _ _ _ (hY y (by simp)) hu, PO.trans h0u (hr _ _), ?_⟩
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hl _ _
      · exact PO.trans (hys z hz) (hr _ _)
  match X, hX with
  | x :: xs, _ =>
    obtain ⟨u, hu, hxu, hxs⟩ := key xs x (hall x (by simp))
      (fun z hz => hall z (List.mem_cons_of_mem _ hz))
    refine ⟨u, hu, fun z hz => ?_⟩
    rcases List.mem_cons.1 hz with rfl | hz
    · exact hxu
    · exact hxs z hz

/-- Relational Monotonicity plus fibers closed under a binary upper bound give
Lifted Monotonicity. -/
theorem liftedMono_of_join {sp : Spec I O} (join : O → O → O)
    (hl : ∀ a b, a ≼ join a b) (hr : ∀ a b, b ≼ join a b)
    (hc : ∀ j a b, sp.P j a → sp.P j b → sp.P j (join a b)) (hR : sp.RelMono) :
    sp.LiftedMono :=
  (liftedMono_iff_relMono_directed sp).2 ⟨hR, directed_of_join join hl hr hc⟩

/-- Union of two sets of facts. -/
def ESet.union {F : Type} (a b : ESet F) : ESet F := ⟨fun x => a.mem x ∨ b.mem x⟩

/-- **Lemma `lem:accumulating`** (sets of facts under inclusion): if every
permitted output stays permitted at each input extension, and fibers are closed
under binary union, the spec is monotone. -/
theorem accumulating_monotone {F : Type} {sp : Spec I (ESet F)}
    (hgrow : ∀ i j o, i ≼ j → sp.P i o → sp.P j o)
    (hunion : ∀ j a b, sp.P j a → sp.P j b → sp.P j (ESet.union a b)) : sp.LiftedMono :=
  liftedMono_of_join ESet.union (fun _ _ _ h => Or.inl h) (fun _ _ _ h => Or.inr h) hunion
    (fun i j o hij ho => ⟨o, hgrow i j o hij ho, PO.refl _⟩)

/-- Two outputs that place `a`, `b` in opposite orders have no common output
extension in a fiber where no output places two events both ways. -/
theorem order_no_common {sp : Spec I O} {E : Type} (before : O → E → E → Prop)
    (hmono : ∀ o u a b, o ≼ u → before o a b → before u a b) {j : I}
    (hasym : ∀ u a b, sp.P j u → before u a b → ¬ before u b a)
    {o1 o2 : O} {a b : E} (hb1 : before o1 a b) (hb2 : before o2 b a) :
    ¬ ∃ u, sp.P j u ∧ o1 ≼ u ∧ o2 ≼ u :=
  fun ⟨u, hu, h1, h2⟩ => hasym u a b hu (hmono _ _ _ _ h1 hb1) (hmono _ _ _ _ h2 hb2)

/-- **Lemma `lem:order-commitment`** (rows at a common input extension). -/
theorem order_conflict {sp : Spec I O} {E : Type} (before : O → E → E → Prop)
    (hmono : ∀ o u a b, o ≼ u → before o a b → before u a b) {j : I}
    (hasym : ∀ u a b, sp.P j u → before u a b → ¬ before u b a)
    {i1 i2 : I} {o1 o2 : O} {a b : E} (h1 : sp.P i1 o1) (h2 : sp.P i2 o2)
    (hj1 : i1 ≼ j) (hj2 : i2 ≼ j) (hb1 : before o1 a b) (hb2 : before o2 b a) :
    ¬ sp.CommonExpansion ∧ ¬ sp.LiftedMono := by
  have hce : ¬ sp.CommonExpansion := by
    intro hC
    obtain ⟨u, hu, hall⟩ := hC [(i1, o1), (i2, o2)] (by simp [h1, h2]) j (by simp [hj1, hj2])
    exact order_no_common before hmono hasym hb1 hb2
      ⟨u, hu, hall (i1, o1) (by simp), hall (i2, o2) (by simp)⟩
  exact ⟨hce, fun h => hce ((liftedMono_iff_commonExpansion sp).1 h)⟩

/-- **Lemma `lem:order-commitment`**, same input: the fiber is not directed. -/
theorem order_conflict_fiber {sp : Spec I O} {E : Type} (before : O → E → E → Prop)
    (hmono : ∀ o u a b, o ≼ u → before o a b → before u a b) {j : I}
    (hasym : ∀ u a b, sp.P j u → before u a b → ¬ before u b a)
    {o1 o2 : O} {a b : E} (h1 : sp.P j o1) (h2 : sp.P j o2)
    (hb1 : before o1 a b) (hb2 : before o2 b a) :
    ¬ sp.DirectedOutputs ∧ ¬ sp.LiftedMono := by
  have hd : ¬ sp.DirectedOutputs := by
    intro hD
    obtain ⟨u, hu, hall⟩ := hD j [o1, o2] (by simp) (by simp [h1, h2])
    exact order_no_common before hmono hasym hb1 hb2 ⟨u, hu, hall o1 (by simp), hall o2 (by simp)⟩
  exact ⟨hd, fun h => hd ((liftedMono_iff_relMono_directed sp).1 h).2⟩

/-- No output of the fiber at `j` decides `k+1` distinct values. -/
theorem bounded_no_common {sp : Spec I O} {V : Type} (dec : O → V → Prop)
    (hmono : ∀ o u v, o ≼ u → dec o v → dec u v) {k : Nat} {j : I}
    (hbound : ∀ u, sp.P j u → ∃ l : List V, l.length ≤ k ∧ ∀ v, dec u v → v ∈ l)
    (o : Fin (k + 1) → O) (v : Fin (k + 1) → V) (hv : ∀ r r', v r = v r' → r = r')
    (hd : ∀ r, dec (o r) (v r)) : ¬ ∃ u, sp.P j u ∧ ∀ r, o r ≼ u := by
  rintro ⟨u, hu, hall⟩
  obtain ⟨l, hl, hcov⟩ := hbound u hu
  have hsub : (List.finRange (k + 1)).map v ⊆ l := by
    intro a ha
    obtain ⟨r, _, rfl⟩ := List.mem_map.1 ha
    exact hcov _ (hmono _ _ _ (hall r) (hd r))
  have hnd : ((List.finRange (k + 1)).map v).Nodup :=
    List.Pairwise.map _ (fun a b hab h => hab (hv a b h)) (List.nodup_finRange (k + 1))
  have := hnd.length_le_of_subset hsub
  rw [List.length_map, List.length_finRange] at this
  omega

/-- **Lemma `lem:bounded-values`.** -/
theorem bounded_values {sp : Spec I O} {V : Type} (dec : O → V → Prop)
    (hmono : ∀ o u v, o ≼ u → dec o v → dec u v) {k : Nat} {j : I}
    (hbound : ∀ u, sp.P j u → ∃ l : List V, l.length ≤ k ∧ ∀ v, dec u v → v ∈ l)
    (i : Fin (k + 1) → I) (o : Fin (k + 1) → O) (v : Fin (k + 1) → V)
    (hv : ∀ r r', v r = v r' → r = r') (hrow : ∀ r, sp.P (i r) (o r)) (hj : ∀ r, i r ≼ j)
    (hd : ∀ r, dec (o r) (v r)) : ¬ sp.CommonExpansion ∧ ¬ sp.LiftedMono := by
  have hce : ¬ sp.CommonExpansion := by
    intro hC
    let rows := (List.finRange (k + 1)).map fun r => (i r, o r)
    obtain ⟨u, hu, hall⟩ := hC rows
      (by intro x hx; obtain ⟨r, _, rfl⟩ := List.mem_map.1 hx; exact hrow r) j
      (by intro x hx; obtain ⟨r, _, rfl⟩ := List.mem_map.1 hx; exact hj r)
    exact bounded_no_common dec hmono hbound o v hv hd
      ⟨u, hu, fun r => hall _ (List.mem_map.2 ⟨r, List.mem_finRange r, rfl⟩)⟩
  exact ⟨hce, fun h => hce ((liftedMono_iff_commonExpansion sp).1 h)⟩

/-- Lemma `lem:ruling-out`: an output that rules out an input fact contained
in some input extension has no output extension there, so Relational
Monotonicity, and with it Lifted Monotonicity, fails. -/
theorem ruling_out {sp : Spec I O} {F : Type} (has : I → F → Prop) (rules : O → F → Prop)
    (hmono : ∀ o u f, o ≼ u → rules o f → rules u f)
    (hsafe : ∀ j u f, sp.P j u → has j f → ¬ rules u f)
    {i j : I} {o : O} {f : F} (hrow : sp.P i o) (hij : i ≼ j) (hr : rules o f)
    (hj : has j f) : ¬ sp.RelMono ∧ ¬ sp.LiftedMono := by
  have hR : ¬ sp.RelMono := by
    intro hR
    obtain ⟨u, hu, hou⟩ := hR i j o hij hrow
    exact hsafe j u f hu hj (hmono o u f hou hr)
  exact ⟨hR, fun hL => hR ((liftedMono_iff_relMono_directed sp).1 hL).1⟩

/-- The negative side of Complete CAP (`E = P`), from `CC.CAP.complete_cap`. -/
theorem no_cap_of_not_liftedMono {sp : Spec I O} (h : ¬ sp.LiftedMono) (D : Type) :
    ¬ ∃ Sys : CAP.System sp D, CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  fun hs => h ((CAP.complete_cap sp D).1 hs)

/-- Outputs with no common output extension in the fiber at the current
input of a canonical state: emitting one is a commitment. -/
theorem canon_incompatible {sp : Spec I O} {i : I} {o o' : O} (ho : sp.P i o) (ho' : sp.P i o')
    (hn : ¬ ∃ u, sp.P i u ∧ o ≼ u ∧ o' ≼ u) :
    Excluded (canon sp i) o i o' ∧ ¬ Exposable (canon sp i) o ∧
      ∀ (B : CommitmentBasis sp) τ, SysStep B (canon sp i) (.output o) τ →
        B (canonicalCommitment o) :=
  incompatible_excluded (σ := canon sp i) ⟨ho, PO.refl i⟩ ⟨ho', PO.refl i⟩
    fun ⟨u, hu, h1, h2⟩ => hn ⟨u, hu.1, h1, h2⟩

/-- Consequences when a pattern shows that Lifted Monotonicity fails: the runs
are not consistent (Complete CALM); some output at a state reachable without
commitment is not legal and its output event applies `x_o` (No-commitment
test); no system has Availability and Partition Consistency (Complete CAP,
`E = P`). -/
theorem pattern_consequences_neg {sp : Spec I O} (h : ¬ sp.LiftedMono) (D : Type) :
    ¬ sp.Consistent ∧
    (∃ τ : State sp, ReachableCF τ ∧ ∃ o, τ.R τ.cur o ∧ ¬ Exposable τ o ∧
      ∀ (B : CommitmentBasis sp) τ', SysStep B τ (.output o) τ' → B (canonicalCommitment o)) ∧
    ¬ ∃ Sys : CAP.System sp D, CAP.Availability Sys ∧ CAP.PartitionConsistency Sys := by
  refine ⟨fun hc => h ((complete_calm sp).1 hc), ?_, no_cap_of_not_liftedMono h D⟩
  apply Classical.byContradiction
  intro hno
  apply h
  apply (liftedMono_iff_commonExpansion sp).2
  apply (exposure_boundary sp).2
  intro τ hτ o ho
  apply Classical.byContradiction
  intro hne
  exact hno ⟨τ, hτ, o, ho, hne, fun B τ' hs => needs_canonical hs hne⟩

/-- Consequences when Lifted Monotonicity holds: the runs are consistent,
every output at every state reachable without commitment is legal, and the
commitment-free (canonical) system has Availability and Partition
Consistency. -/
theorem pattern_consequences_pos {sp : Spec I O} (h : sp.LiftedMono) (D : Type) :
    sp.Consistent ∧ (∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o) ∧
    CAP.Availability (CAP.cfSystem sp D) ∧ CAP.PartitionConsistency (CAP.cfSystem sp D) :=
  ⟨(complete_calm sp).2 h, (exposure_boundary sp).1 ((liftedMono_iff_commonExpansion sp).1 h),
   CAP.complete_cap_cf sp D h⟩

end Patterns

/-! ### Accumulating instances -/

section Accum

/-- Reliable broadcast: inputs are finite sets of broadcast messages; an
output is a set of delivered messages, any subset of those broadcast. -/
def bcastSpec (M : Type) : Spec (FinSet M) (ESet M) where
  P i o := ∀ x, o.mem x → i.1 x
  total _ := ⟨⟨fun _ => False⟩, fun _ h => h.elim⟩

theorem bcast_liftedMono {M : Type} : (bcastSpec M).LiftedMono :=
  accumulating_monotone (fun _ _ _ hij ho x hx => hij x (ho x hx))
    (fun _ _ _ ha hb x hx => hx.elim (ha x) (hb x))

/-- The prefix spec (causal broadcast, global snapshot) via Lemma `lem:accumulating`. -/
theorem prefix_liftedMono_accumulating {Ev : Type} : (prefixSpec Ev).LiftedMono :=
  accumulating_monotone (fun _ _ _ hij ho => prefix_mono hij ho)
    (fun _ _ _ ha hb =>
      ⟨fun x hx => hx.elim (ha.1 x) (hb.1 x),
       fun x y hy hxy => hy.elim (fun h => Or.inl (ha.2 x y h hxy))
         (fun h => Or.inr (hb.2 x y h hxy))⟩)

/-- Counter values, ordered by `≤` (a wrapper, to avoid a global `PO Nat`). -/
structure Count where
  n : Nat

instance instPOCount : PO Count where
  le a b := a.n ≤ b.n
  refl _ := Nat.le_refl _
  trans h1 h2 := Nat.le_trans h1 h2
  antisymm := by
    rintro ⟨a⟩ ⟨b⟩ h1 h2
    have : a = b := Nat.le_antisymm h1 h2
    subst this; rfl

variable {P : Type} [DecidableEq P]

omit [DecidableEq P] in
theorem card_mono {N N' : FinSet P} (h : N ≼ N') : card N ≤ card N' := by
  have hc := Classical.choose_spec N.2
  have hc' := Classical.choose_spec N'.2
  exact hc.1.length_le_of_subset fun x hx => (hc'.2 x).1 (h x ((hc.2 x).2 hx))

/-- Grow-only counter: inputs are finite sets of increments; an output is a
count no larger than the number of increments. -/
noncomputable def counterSpec (Inc : Type) [DecidableEq Inc] : Spec (FinSet Inc) Count where
  P i c := c.n ≤ card i
  total _ := ⟨⟨0⟩, Nat.zero_le _⟩

theorem counter_liftedMono {Inc : Type} [DecidableEq Inc] : (counterSpec Inc).LiftedMono :=
  liftedMono_of_join (fun a b => ⟨max a.n b.n⟩) (fun _ _ => Nat.le_max_left _ _)
    (fun _ _ => Nat.le_max_right _ _) (fun _ _ _ ha hb => Nat.max_le.2 ⟨ha, hb⟩)
    (fun _ _ o hij ho => ⟨o, Nat.le_trans ho (card_mono hij), Nat.le_refl _⟩)

end Accum

/-! ### Sequences under the prefix order; "places `a` before `b`" -/

section Seqs

/-- Sequences ordered by prefix. -/
structure Seq (α : Type) where
  l : List α

instance instPOSeq (α : Type) : PO (Seq α) where
  le a b := a.l <+: b.l
  refl a := List.prefix_refl a.l
  trans h1 h2 := List.IsPrefix.trans h1 h2
  antisymm := by
    rintro ⟨a⟩ ⟨b⟩ h1 h2
    have : a = b := h1.eq_of_length (Nat.le_antisymm h1.length_le h2.length_le)
    subst this; rfl

variable {α : Type} [DecidableEq α]

/-- `s` places `a` before `b`: `a` is listed, and `b`, if listed, comes later. -/
def PlacesBefore (s : Seq α) (a b : α) : Prop :=
  a ∈ s.l ∧ (b ∈ s.l → s.l.idxOf a < s.l.idxOf b)

theorem placesBefore_mono {s u : Seq α} {a b : α} (h : s ≼ u) (hb : PlacesBefore s a b) :
    PlacesBefore u a b := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨ha, hab⟩ := hb
  have hia : u.l.idxOf a = s.l.idxOf a := by rw [← ht, List.idxOf_append]; simp [ha]
  refine ⟨ht ▸ List.mem_append_left _ ha, fun hbu => ?_⟩
  rw [hia]
  by_cases hbs : b ∈ s.l
  · have hib : u.l.idxOf b = s.l.idxOf b := by rw [← ht, List.idxOf_append]; simp [hbs]
    rw [hib]; exact hab hbs
  · have hib : u.l.idxOf b = s.l.length + t.idxOf b := by
      rw [← ht, List.idxOf_append]; simp [hbs]; omega
    rw [hib]
    have := List.idxOf_lt_length_of_mem ha
    omega

omit [DecidableEq α] in
/-- Two sequences have a common output extension iff one is a prefix of the other. -/
theorem seq_common_iff (s t : Seq α) : (∃ u, s ≼ u ∧ t ≼ u) ↔ s ≼ t ∨ t ≼ s := by
  constructor
  · rintro ⟨u, hs, ht⟩
    rcases Nat.le_total s.l.length t.l.length with hl | hl
    · exact Or.inl (List.prefix_of_prefix_length_le hs ht hl)
    · exact Or.inr (List.prefix_of_prefix_length_le ht hs hl)
  · rintro (h | h)
    · exact ⟨t, h, PO.refl _⟩
    · exact ⟨s, PO.refl _, h⟩

theorem placesBefore_asymm {s : Seq α} {a b : α} (h1 : PlacesBefore s a b)
    (h2 : PlacesBefore s b a) : False := by
  have := h1.2 h2.1; have := h2.2 h1.1; omega

/-- Total-order broadcast: inputs are finite sets of broadcast messages; an
output is a delivery sequence of distinct broadcast messages, under prefix. -/
def tobSpec (M : Type) : Spec (FinSet M) (Seq M) where
  P i s := s.l.Nodup ∧ ∀ x ∈ s.l, i.1 x
  total _ := ⟨⟨[]⟩, List.nodup_nil, by simp⟩

omit [DecidableEq α] in
theorem tob_row {a : α} {i : FinSet α} (h : i.1 a) : (tobSpec α).P i ⟨[a]⟩ :=
  ⟨by simp, by simpa using h⟩

/-- Rows `({a},[a])` and `({b},[b])` with common input extension `{a,b}`: not
monotone (Lemma `lem:order-commitment`). -/
theorem tob_not_liftedMono {a b : α} (h : a ≠ b) :
    ¬ (tobSpec α).CommonExpansion ∧ ¬ (tobSpec α).LiftedMono := by
  refine order_conflict (sp := tobSpec α) (j := pairSet a b h) PlacesBefore
    (fun _ _ _ _ h1 h2 => placesBefore_mono h1 h2)
    (fun _ _ _ _ h1 h2 => placesBefore_asymm h1 h2)
    (i1 := sing a) (i2 := sing b) (a := a) (b := b) (tob_row (a := a) (i := sing a) (by simp [sing, FinSet.ofList]))
    (tob_row (a := b) (i := sing b) (by simp [sing, FinSet.ofList])) ?_ ?_ ?_ ?_
  · intro x hx; simp [sing, FinSet.ofList] at hx; subst hx; exact (pairSet_mem _).2 (Or.inl rfl)
  · intro x hx; simp [sing, FinSet.ofList] at hx; subst hx; exact (pairSet_mem _).2 (Or.inr rfl)
  · exact ⟨by simp, fun hb => by simp at hb; exact absurd hb.symm h⟩
  · exact ⟨by simp, fun hb => by simp at hb; exact absurd hb h⟩

end Seqs

/-! ### Consensus, k-set agreement, leader election -/

section Agreement
variable {P Val : Type}

/-- `m` decides `a`: some participant is mapped to `a`. -/
def Decides (m : PMap P Val) (a : Val) : Prop := ∃ p, m.f p = some a

theorem decides_mono {m m' : PMap P Val} {a : Val} (h : m ≼ m') (hd : Decides m a) :
    Decides m' a := let ⟨p, hp⟩ := hd; ⟨p, h p a hp⟩

/-- Outputs permitted at an input stay permitted at its extensions. -/
theorem kset_grow {k : Nat} {I J : KInput P Val} (hIJ : I ≼ J) {m : PMap P Val}
    (hm : (ksetSpec P Val k).P I m) : (ksetSpec P Val k).P J m :=
  ⟨fun p a h => let ⟨b, hb⟩ := hm.1 p a h; ⟨b, hIJ _ hb⟩,
   fun p a h => let ⟨q, hq⟩ := hm.2.1 p a h; ⟨q, hIJ _ hq⟩, hm.2.2⟩

theorem kset_relMono {k : Nat} : (ksetSpec P Val k).RelMono :=
  fun _ _ m hIJ hm => ⟨m, kset_grow hIJ hm, PO.refl _⟩

variable [DecidableEq P] {k : Nat} {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val}

/-- `{p_r ↦ v_r}` is permitted at the union of the proposal inputs. -/
theorem kset_union_row (hp : ∀ r r', p r = p r' → r = r') (hk : 1 ≤ k) (r : Fin (k + 1)) :
    (ksetSpec P Val k).P (unionIn p v hp) (single p v r) :=
  kset_grow (kset_union_upper hp r) (kset_single_row hk r)

/-- k-set agreement through Lemma `lem:bounded-values`: the fiber at the union
is not directed, and the spec is not monotone. -/
theorem kset_not_directed (hp : ∀ r r', p r = p r' → r = r')
    (hv : ∀ r r', v r = v r' → r = r') (hk : 1 ≤ k) :
    ¬ (ksetSpec P Val k).DirectedOutputs ∧ ¬ (ksetSpec P Val k).LiftedMono := by
  have hb : ∀ u, (ksetSpec P Val k).P (unionIn p v hp) u →
      ∃ l : List Val, l.length ≤ k ∧ ∀ a, Decides u a → a ∈ l :=
    fun u ⟨_, _, l, hl, hc⟩ => ⟨l, hl, fun a ⟨q, hq⟩ => hc q a hq⟩
  have hd : ¬ (ksetSpec P Val k).DirectedOutputs := by
    intro hD
    obtain ⟨u, hu, hall⟩ := hD (unionIn p v hp)
      ((List.finRange (k + 1)).map (single p v))
      (List.ne_nil_of_mem (List.mem_map.2 ⟨0, List.mem_finRange 0, rfl⟩))
      (by intro x hx; obtain ⟨r, _, rfl⟩ := List.mem_map.1 hx; exact kset_union_row hp hk r)
    exact bounded_no_common (sp := ksetSpec P Val k) Decides (fun _ _ _ h1 h2 => decides_mono h1 h2)
      hb (single p v) v hv (fun r => ⟨p r, by simp [single]⟩)
      ⟨u, hu, fun r => hall _ (List.mem_map.2 ⟨r, List.mem_finRange r, rfl⟩)⟩
  refine ⟨hd, (bounded_values (sp := ksetSpec P Val k) Decides
    (fun _ _ _ h1 h2 => decides_mono h1 h2) hb (propIn p v) (single p v) v hv
    (fun r => kset_single_row hk r) (fun r => kset_union_upper hp r)
    (fun r => ⟨p r, by simp [single]⟩)).2⟩

end Agreement

/-- Leader election, modeled as consensus in which each candidate proposes its
own identifier: two candidates give a witness. -/
theorem leader_not_liftedMono {P : Type} [DecidableEq P] {p : Fin 2 → P}
    (hp : ∀ r r', p r = p r' → r = r') (D : Type) :
    ¬ (ksetSpec P P 1).LiftedMono ∧
      ¬ ∃ Sys : CAP.System (ksetSpec P P 1) D, CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  ⟨kset_not_liftedMono hp hp (Nat.le_refl 1), kset_no_cap hp hp (Nat.le_refl 1) D⟩

/-! ### Renaming -/

section RenamingC
variable {P : Type} [DecidableEq P]

/-- `x` holds the name `1` in `m`. -/
def HoldsName1 (m : PMap P Nat) (x : P) : Prop := m.f x = some 1

omit [DecidableEq P] in
theorem inj_bound {u : PMap P Nat} (hu : Injective u) :
    ∃ l : List P, l.length ≤ 1 ∧ ∀ x, HoldsName1 u x → x ∈ l := by
  by_cases h : ∃ x, u.f x = some 1
  · refine ⟨[Classical.choose h], by simp, fun x hx => ?_⟩
    simp only [List.mem_singleton]
    exact hu x _ 1 hx (Classical.choose_spec h)
  · exact ⟨[], by simp, fun x hx => absurd ⟨x, hx⟩ h⟩

omit [DecidableEq P] in
/-- The two participants `p`, `q`, indexed by `Fin 2`. -/
def two (p q : P) : Fin 2 → P := fun r => if r.val = 0 then p else q

omit [DecidableEq P] in
theorem two_inj {p q : P} (h : p ≠ q) : ∀ r r' : Fin 2, two p q r = two p q r' → r = r' := by
  intro ⟨r, hr⟩ ⟨r', hr'⟩ he
  apply Fin.ext
  simp only [two] at he ⊢
  by_cases h0 : r = 0 <;> by_cases h0' : r' = 0 <;> simp only [h0, h0', ↓reduceIte] at he
  · omega
  · exact absurd he h
  · exact absurd he.symm h
  · omega

omit [DecidableEq P] in
theorem sing_le_pair {p q : P} (h : p ≠ q) (r : Fin 2) : sing (two p q r) ≼ pairSet p q h := by
  intro x hx
  simp only [sing, FinSet.ofList, List.mem_singleton] at hx
  subst hx
  rw [pairSet_mem]
  simp only [two]
  split <;> simp

/-- Tight renaming through Lemma `lem:bounded-values` (`k = 1`): at most one
participant holds the name `1` in any injective map. -/
theorem ren_via_bounded {p q : P} (h : p ≠ q) :
    ¬ (renSpec P).CommonExpansion ∧ ¬ (renSpec P).LiftedMono :=
  bounded_values (sp := renSpec P) HoldsName1 (fun _ _ _ h1 h2 => h1 _ 1 h2) (k := 1)
    (j := pairSet p q h) (fun _ hu => inj_bound hu.2.1) (fun r => sing (two p q r))
    (fun r => name1 (two p q r)) (two p q) (two_inj h)
    (fun r => (ren_singleton_iff _ _).2 rfl) (sing_le_pair h) (fun r => by simp [HoldsName1, name1])

/-- **Relational Monotonicity holds for tight renaming**: participants that join
take fresh names above `|N|`. -/
theorem ren_relMono : (renSpec P).RelMono := by
  classical
  intro N N' m hNN' hm
  obtain ⟨hdom, hinj, hrange⟩ := hm
  have hl := Classical.choose_spec N.2
  have hl' := Classical.choose_spec N'.2
  let l := Classical.choose N.2
  let l' := Classical.choose N'.2
  let d := l'.filter (fun x => decide (¬ N.1 x))
  have hd : ∀ x, x ∈ d ↔ N'.1 x ∧ ¬ N.1 x := by
    intro x; simp only [d, List.mem_filter, decide_eq_true_eq]; rw [← hl'.2 x]
  have hdnd : d.Nodup := List.Pairwise.filter _ hl'.1
  have hcardN : card N = l.length := rfl
  have hcardN' : card N' = l'.length := rfl
  have hlen : l.length + d.length ≤ l'.length := by
    have hnd : (l ++ d).Nodup := by
      refine List.nodup_append.2 ⟨hl.1, hdnd, fun a ha b hb hab => ?_⟩
      subst hab
      exact ((hd a).1 hb).2 ((hl.2 a).2 ha)
    have := hnd.length_le_of_subset (fun x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · exact (hl'.2 x).1 (hNN' x ((hl.2 x).2 hx))
      · exact (hl'.2 x).1 ((hd x).1 hx).1)
    simpa using this
  let m' : PMap P Nat := ⟨fun x => if N.1 x then m.f x else
    if x ∈ d then some (card N + d.idxOf x + 1) else none⟩
  have hfresh : ∀ x n, ¬ N.1 x → m'.f x = some n → x ∈ d ∧ n = card N + d.idxOf x + 1 := by
    intro x n hx he
    simp only [m', hx, ↓reduceIte] at he
    split at he
    · exact ⟨‹_›, (Option.some.inj he).symm⟩
    · exact nomatch he
  refine ⟨m', ⟨fun x => ?_, fun x y n hx hy => ?_, fun x n hx => ?_⟩, fun x n hx => ?_⟩
  · constructor
    · intro hx'
      by_cases hx : N.1 x
      · obtain ⟨n, hn⟩ := (hdom x).1 hx
        exact ⟨n, by simp only [m', hx, ↓reduceIte]; exact hn⟩
      · have : x ∈ d := (hd x).2 ⟨hx', hx⟩
        exact ⟨card N + d.idxOf x + 1, by simp only [m', hx, this, ↓reduceIte]⟩
    · rintro ⟨n, hn⟩
      by_cases hx : N.1 x
      · exact hNN' x hx
      · exact ((hd x).1 (hfresh x n hx hn).1).1
  · by_cases hxN : N.1 x <;> by_cases hyN : N.1 y
    · simp only [m', hxN, ↓reduceIte, hyN, ↓reduceIte] at hx hy
      exact hinj x y n hx hy
    · simp only [m', hxN, ↓reduceIte] at hx
      obtain ⟨_, rfl⟩ := hfresh y n hyN hy
      have := (hrange x _ hx).2; omega
    · simp only [m', hyN, ↓reduceIte] at hy
      obtain ⟨_, rfl⟩ := hfresh x n hxN hx
      have := (hrange y _ hy).2; omega
    · obtain ⟨hxd, rfl⟩ := hfresh x n hxN hx
      obtain ⟨hyd, he⟩ := hfresh y _ hyN hy
      have hidx : d.idxOf x = d.idxOf y := by omega
      have e1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hxd)
      have e2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hyd)
      rw [← e1, ← e2]; simp only [hidx]
  · by_cases hxN : N.1 x
    · simp only [m', hxN, ↓reduceIte] at hx
      have := hrange x n hx
      exact ⟨this.1, Nat.le_trans this.2 (card_mono hNN')⟩
    · obtain ⟨hxd, rfl⟩ := hfresh x n hxN hx
      have := List.idxOf_lt_length_of_mem hxd
      constructor
      · omega
      · rw [hcardN', ← hcardN] at *; omega
  · have hxN : N.1 x := (hdom x).2 ⟨n, hx⟩
    simp only [m', hxN, ↓reduceIte]; exact hx

/-- Renaming with namespace bound `f(|N|)`, `n ≤ f n` (tight renaming is
`f n = n`; the classical non-tight problem has `f n = 2n - 1`). -/
def renBS (f : Nat → Nat) (N : FinSet P) (m : PMap P Nat) : Prop :=
  (∀ x, N.1 x ↔ ∃ n, m.f x = some n) ∧ Injective m ∧
  ∀ x n, m.f x = some n → 1 ≤ n ∧ n ≤ f (card N)

omit [DecidableEq P] in
theorem renBS_of_renS {f : Nat → Nat} (hf : ∀ n, n ≤ f n) {N : FinSet P} {m : PMap P Nat}
    (h : renS N m) : renBS f N m :=
  ⟨h.1, h.2.1, fun x n hx => ⟨(h.2.2 x n hx).1, Nat.le_trans (h.2.2 x n hx).2 (hf _)⟩⟩

noncomputable def renSpecB (P : Type) [DecidableEq P] (f : Nat → Nat) (hf : ∀ n, n ≤ f n) :
    Spec (FinSet P) (PMap P Nat) where
  P := renBS f
  total N := let ⟨m, hm⟩ := (renSpec P).total N; ⟨m, renBS_of_renS hf hm⟩

/-- **Renaming with any namespace bound `f(|N|) ≥ |N|` is not monotone.** -/
theorem renB_not_liftedMono {f : Nat → Nat} (hf : ∀ n, n ≤ f n) {p q : P} (h : p ≠ q) (D : Type) :
    ¬ (renSpecB P f hf).LiftedMono ∧
      ¬ ∃ Sys : CAP.System (renSpecB P f hf) D,
        CAP.Availability Sys ∧ CAP.PartitionConsistency Sys := by
  have hn := (bounded_values (sp := renSpecB P f hf) HoldsName1 (fun _ _ _ h1 h2 => h1 _ 1 h2)
    (k := 1) (j := pairSet p q h) (fun _ hu => inj_bound hu.2.1) (fun r => sing (two p q r))
    (fun r => name1 (two p q r)) (two p q) (two_inj h)
    (fun r => renBS_of_renS hf ((ren_singleton_iff _ _).2 rfl)) (sing_le_pair h)
    (fun r => by simp [HoldsName1, name1])).2
  exact ⟨hn, no_cap_of_not_liftedMono hn D⟩

end RenamingC

/-! ### Consensus: certified evidence -/

section Evidence
variable {I O : Type} [PO I] [PO O]

/-- **Evidence spec**: if the certified evidence `c i` grows with the input and
the permitted outputs at `i` are exactly those that `c i` extends, the spec is
monotone. -/
theorem evidence_liftedMono {sp : Spec I O} (c : I → O) (hc : ∀ i j, i ≼ j → c i ≼ c j)
    (hP : ∀ i o, sp.P i o ↔ o ≼ c i) : sp.LiftedMono :=
  (liftedMono_iff_commonExpansion sp).2 fun _ hr j hj =>
    ⟨c j, (hP j _).2 (PO.refl _),
     fun r hrr => PO.trans ((hP _ _).1 (hr r hrr)) (hc _ _ (hj r hrr))⟩

/-- … so every output at every state reachable without commitment is legal
(Prop. `prop:exposure-boundary`). -/
theorem evidence_legal {sp : Spec I O} (c : I → O) (hc : ∀ i j, i ≼ j → c i ≼ c j)
    (hP : ∀ i o, sp.P i o ↔ o ≼ c i) :
    ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  (exposure_boundary sp).1 ((liftedMono_iff_commonExpansion sp).1 (evidence_liftedMono c hc hP))

/-- The evidence spec: at `i`, exactly the outputs that the certified evidence
`c i` extends. -/
def evidenceSpec (c : I → O) : Spec I O where
  P i o := o ≼ c i
  total i := ⟨c i, PO.refl _⟩

/-- **Prop. `prop:monotone-evidence`** for `evidenceSpec`. -/
theorem evidenceSpec_monotone (c : I → O) (hc : ∀ i j, i ≼ j → c i ≼ c j) :
    (evidenceSpec c).LiftedMono ∧
      ∀ τ : State (evidenceSpec c), ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  ⟨evidence_liftedMono c hc (fun _ _ => Iff.rfl), evidence_legal c hc (fun _ _ => Iff.rfl)⟩

end Evidence

/-! ### Atomic snapshot -/

section AtomicSnapshot

/-- Operations: updates and scans. -/
inductive SOp (U S : Type) where
  | upd (u : U)
  | scan (s : S)

variable {U S : Type}

/-- Permitted: each answered scan is in the input and its view is a set of
updates of the input, and any two views are comparable by inclusion. -/
def snapS (i : FinSet (SOp U S)) (o : PMap S (ESet U)) : Prop :=
  (∀ s V, o.f s = some V → i.1 (.scan s) ∧ ∀ u, V.mem u → i.1 (.upd u)) ∧
  (∀ s s' V V', o.f s = some V → o.f s' = some V' → V ≼ V' ∨ V' ≼ V)

/-- Atomic snapshot: inputs are finite sets of operations; an output maps
answered scans to their views, ordered by extension. -/
def snapSpec (U S : Type) : Spec (FinSet (SOp U S)) (PMap S (ESet U)) where
  P := snapS
  total _ := ⟨⟨fun _ => none⟩, by
    show snapS _ _
    exact ⟨fun _ _ h => (nomatch h), fun _ _ _ _ h => (nomatch h)⟩⟩

/-- `o` has a scan whose view contains `a` and not `b`. -/
def Reflects (o : PMap S (ESet U)) (a b : U) : Prop :=
  ∃ s V, o.f s = some V ∧ V.mem a ∧ ¬ V.mem b

theorem reflects_mono {o w : PMap S (ESet U)} {a b : U} (h : o ≼ w) (hr : Reflects o a b) :
    Reflects w a b := let ⟨s, V, hs, ha, hb⟩ := hr; ⟨s, V, h s V hs, ha, hb⟩

theorem reflects_asymm {i : FinSet (SOp U S)} {w : PMap S (ESet U)} {a b : U}
    (hw : (snapSpec U S).P i w) (h1 : Reflects w a b) (h2 : Reflects w b a) : False := by
  have hw : snapS i w := hw
  obtain ⟨s, V, hs, ha, hb⟩ := h1
  obtain ⟨s', V', hs', hb', ha'⟩ := h2
  rcases hw.2 s s' V V' hs hs' with h | h
  · exact ha' (h a ha)
  · exact hb (h b hb')

variable [DecidableEq S]

/-- The answer `s ↦ {u}`. -/
def scanAns (s : S) (u : U) : PMap S (ESet U) :=
  ⟨fun s' => if s' = s then some ⟨fun x => x = u⟩ else none⟩

/-- The input `{upd u₁, upd u₂, scan s₁, scan s₂}`. -/
def snapIn {u1 u2 : U} {s1 s2 : S} (hu : u1 ≠ u2) (hs : s1 ≠ s2) : FinSet (SOp U S) :=
  FinSet.ofList [.upd u1, .upd u2, .scan s1, .scan s2] (by simp [hu, hs])

theorem scanAns_row {u1 u2 : U} {s1 s2 : S} (hu : u1 ≠ u2) (hs : s1 ≠ s2) {s : S} {u : U}
    (hsm : s = s1 ∨ s = s2) (hum : u = u1 ∨ u = u2) :
    (snapSpec U S).P (snapIn hu hs) (scanAns s u) := by
  show snapS _ _
  refine ⟨fun s' V h => ?_, fun s' s'' V V' h1 h2 => ?_⟩
  · simp only [scanAns] at h
    split at h
    · rename_i he; subst he
      cases h
      refine ⟨by rcases hsm with rfl | rfl <;> simp [snapIn, FinSet.ofList], fun x hx => ?_⟩
      have hx : x = u := hx
      subst hx
      rcases hum with rfl | rfl <;> simp [snapIn, FinSet.ofList]
    · exact nomatch h
  · simp only [scanAns] at h1 h2
    split at h1 <;> split at h2
    · cases h1; cases h2; exact Or.inl (PO.refl _)
    all_goals exact nomatch ‹none = some _›

/-- **Atomic snapshot is not monotone**: two scans whose views order two
updates oppositely are each permitted at one input, with no common output
extension (Lemma `lem:order-commitment`). -/
theorem snap_not_liftedMono {u1 u2 : U} {s1 s2 : S} (hu : u1 ≠ u2) (hs : s1 ≠ s2) (D : Type) :
    ¬ (snapSpec U S).DirectedOutputs ∧ ¬ (snapSpec U S).LiftedMono ∧
      ¬ ∃ Sys : CAP.System (snapSpec U S) D,
        CAP.Availability Sys ∧ CAP.PartitionConsistency Sys := by
  have h := order_conflict_fiber (sp := snapSpec U S) (j := snapIn hu hs) Reflects
    (fun _ _ _ _ h1 h2 => reflects_mono h1 h2) (fun _ _ _ hw h1 h2 => reflects_asymm hw h1 h2)
    (o1 := scanAns s1 u1) (o2 := scanAns s2 u2) (a := u1) (b := u2)
    (scanAns_row hu hs (Or.inl rfl) (Or.inl rfl)) (scanAns_row hu hs (Or.inr rfl) (Or.inr rfl))
    ⟨s1, ⟨fun x => x = u1⟩, by simp [scanAns], rfl, fun h => hu h.symm⟩
    ⟨s2, ⟨fun x => x = u2⟩, by simp [scanAns], rfl, fun h => hu h⟩
  exact ⟨h.1, h.2, no_cap_of_not_liftedMono h.2 D⟩

end AtomicSnapshot

/-! ### Causal FIFO queue -/

section Queue
variable {Ev : Type}

/-- No element is causally before an element listed earlier. -/
def Sorted (h : Hist Ev) (σ : List Ev) : Prop := σ.Pairwise (fun x y => ¬ h.lt y x)

/-- A permitted dequeue sequence at `h`: distinct enqueued values, listed in
an order that respects causality, with no value skipped before a listed one. -/
def QPerm (h : Hist Ev) (σ : List Ev) : Prop :=
  σ.Nodup ∧ (∀ x ∈ σ, h.s.1 x) ∧ (∀ a b, b ∈ σ → h.lt a b → a ∈ σ) ∧ Sorted h σ

/-- The causal FIFO queue: inputs are causal histories of enqueues; an output
is a dequeue sequence, ordered by prefix. -/
def queueSpec (Ev : Type) : Spec (Hist Ev) (Seq Ev) where
  P h s := QPerm h s.l
  total _ := ⟨⟨[]⟩, List.nodup_nil, by simp, by simp, List.Pairwise.nil⟩

/-- Permitted dequeue sequences stay permitted as the history grows. -/
theorem queue_grow {h h' : Hist Ev} (hle : h ≼ h') {σ : List Ev} (hp : QPerm h σ) :
    QPerm h' σ := by
  obtain ⟨hnd, hin, hdown, hsort⟩ := hp
  refine ⟨hnd, fun x hx => hle.1 x (hin x hx), fun a b hb hab => ?_, ?_⟩
  · have hsb := hin b hb
    have hsa := hle.2.1 a b hsb hab
    exact hdown a b hb ((hle.2.2 a b hsa hsb).2 hab)
  · exact List.Pairwise.imp_of_mem (fun hx hy hn h' => hn ((hle.2.2 _ _ (hin _ hy) (hin _ hx)).2 h')) hsort

/-- **Relational Monotonicity holds for the causal FIFO queue.** -/
theorem queue_relMono : (queueSpec Ev).RelMono :=
  fun _ _ σ hle hp => ⟨σ, queue_grow hle hp, PO.refl _⟩

theorem sorted_insert (h : Hist Ev) (x : Ev) : ∀ σ : List Ev, x ∉ σ → σ.Nodup → Sorted h σ →
    ∃ τ : List Ev, τ.Nodup ∧ (∀ z, z ∈ τ ↔ z = x ∨ z ∈ σ) ∧ Sorted h τ
  | [], _, _, _ => ⟨[x], by simp, by simp, by simp [Sorted]⟩
  | y :: σ, hx, hnd, hs => by
    by_cases hxy : h.lt x y
    · refine ⟨x :: y :: σ, List.nodup_cons.2 ⟨hx, hnd⟩, by simp, ?_⟩
      refine List.Pairwise.cons (fun z hz hzx => ?_) hs
      rcases List.mem_cons.1 hz with rfl | hz
      · exact h.irrefl _ (h.trans _ _ _ hzx hxy)
      · exact (List.rel_of_pairwise_cons hs hz) (h.trans _ _ _ hzx hxy)
    · obtain ⟨τ, hτn, hτm, hτs⟩ := sorted_insert h x σ
        (fun h' => hx (List.mem_cons_of_mem _ h')) (List.nodup_cons.1 hnd).2
        (List.Pairwise.of_cons hs)
      refine ⟨y :: τ, List.nodup_cons.2 ⟨fun hy => ?_, hτn⟩, fun z => ?_,
        List.Pairwise.cons (fun z hz => ?_) hτs⟩
      · rcases (hτm y).1 hy with rfl | hy
        · exact hx (by simp)
        · exact (List.nodup_cons.1 hnd).1 hy
      · simp only [List.mem_cons, hτm]; exact or_left_comm
      · rcases (hτm z).1 hz with rfl | hz
        · exact hxy
        · exact List.rel_of_pairwise_cons hs hz

/-- Every finite set of events can be listed in an order that respects causality. -/
theorem exists_sorted (h : Hist Ev) : ∀ l : List Ev, l.Nodup →
    ∃ τ : List Ev, τ.Nodup ∧ (∀ z, z ∈ τ ↔ z ∈ l) ∧ Sorted h τ
  | [], _ => ⟨[], by simp, by simp, List.Pairwise.nil⟩
  | x :: l, hnd => by
    obtain ⟨τ, h1, h2, h3⟩ := exists_sorted h l (List.nodup_cons.1 hnd).2
    obtain ⟨τ', h1', h2', h3'⟩ := sorted_insert h x τ
      (fun hx => (List.nodup_cons.1 hnd).1 ((h2 x).1 hx)) h1 h3
    exact ⟨τ', h1', fun z => by rw [h2', h2, List.mem_cons], h3'⟩

/-- A permitted dequeue sequence that ends with `a` and lists exactly the
events causally before it. -/
theorem below_seq (h : Hist Ev) {a : Ev} (ha : h.s.1 a) :
    ∃ σ : List Ev, QPerm h (σ ++ [a]) ∧ ∀ z, z ∈ σ ↔ h.lt z a := by
  classical
  obtain ⟨l, hl, hm⟩ := h.s.2
  obtain ⟨σ, hn, hmem, hs⟩ :=
    exists_sorted h (l.filter fun z => decide (h.lt z a)) (List.Pairwise.filter _ hl)
  have hσ : ∀ z, z ∈ σ ↔ h.lt z a := by
    intro z
    rw [hmem, List.mem_filter, decide_eq_true_eq, ← hm]
    exact ⟨fun h' => h'.2, fun h' => ⟨(h.supp _ _ h').1, h'⟩⟩
  refine ⟨σ, ⟨?_, ?_, ?_, ?_⟩, hσ⟩
  · refine List.nodup_append.2 ⟨hn, by simp, fun x hx y hy hxy => ?_⟩
    simp only [List.mem_singleton] at hy
    subst hy; subst hxy
    exact h.irrefl _ ((hσ _).1 hx)
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact (h.supp _ _ ((hσ x).1 hx)).1
    · simp only [List.mem_singleton] at hx; subst hx; exact ha
  · intro c b hb hcb
    rcases List.mem_append.1 hb with hb | hb
    · exact List.mem_append_left _ ((hσ c).2 (h.trans _ _ _ hcb ((hσ b).1 hb)))
    · simp only [List.mem_singleton] at hb; subst hb
      exact List.mem_append_left _ ((hσ c).2 hcb)
  · refine List.pairwise_append.2 ⟨hs, by simp, fun x hx y hy hyx => ?_⟩
    simp only [List.mem_singleton] at hy
    subst hy
    exact h.irrefl _ (h.trans _ _ _ hyx ((hσ x).1 hx))

variable [DecidableEq Ev]

/-- At a history with concurrent enqueues `a` and `b`, one permitted dequeue
sequence places `a` before `b` and another places `b` before `a`. -/
theorem queue_concurrent {h : Hist Ev} {a b : Ev} (ha : h.s.1 a) (hb : h.s.1 b) (hab : a ≠ b)
    (h1 : ¬ h.lt a b) (h2 : ¬ h.lt b a) :
    ∃ σa σb : Seq Ev, (queueSpec Ev).P h σa ∧ (queueSpec Ev).P h σb ∧
      PlacesBefore σa a b ∧ PlacesBefore σb b a := by
  obtain ⟨sa, hpa, hma⟩ := below_seq h ha
  obtain ⟨sb, hpb, hmb⟩ := below_seq h hb
  refine ⟨⟨sa ++ [a]⟩, ⟨sb ++ [b]⟩, hpa, hpb, ⟨by simp, fun hm => ?_⟩, ⟨by simp, fun hm => ?_⟩⟩
  · rcases List.mem_append.1 hm with hm | hm
    · exact absurd ((hma b).1 hm) h2
    · simp only [List.mem_singleton] at hm; exact absurd hm.symm hab
  · rcases List.mem_append.1 hm with hm | hm
    · exact absurd ((hmb a).1 hm) h1
    · simp only [List.mem_singleton] at hm; exact absurd hm hab

/-- **Concurrent enqueues: the fiber is not directed, and the spec is not
monotone** (Lemma `lem:order-commitment`). -/
theorem queue_not_directed {h : Hist Ev} {a b : Ev} (ha : h.s.1 a) (hb : h.s.1 b) (hab : a ≠ b)
    (h1 : ¬ h.lt a b) (h2 : ¬ h.lt b a) :
    ¬ JointLift ((queueSpec Ev).P h) ((queueSpec Ev).P h) ∧ ¬ (queueSpec Ev).LiftedMono := by
  obtain ⟨σa, σb, hpa, hpb, hba, hbb⟩ := queue_concurrent ha hb hab h1 h2
  have hn := order_no_common (sp := queueSpec Ev) (j := h) PlacesBefore
    (fun _ _ _ _ h1 h2 => placesBefore_mono h1 h2) (fun _ _ _ _ h1 h2 => placesBefore_asymm h1 h2)
    hba hbb
  have hd : ¬ JointLift ((queueSpec Ev).P h) ((queueSpec Ev).P h) := by
    intro hD
    obtain ⟨u, hu, hall⟩ := hD [σa, σb] (by simp) (by simp [hpa, hpb])
    exact hn ⟨u, hu, hall σa (by simp), hall σb (by simp)⟩
  exact ⟨hd, fun hL => hd (hL h h (PO.refl h))⟩

/-- … and emitting the first sequence at the canonical state is a commitment. -/
theorem queue_order_commitment {h : Hist Ev} {a b : Ev} (ha : h.s.1 a) (hb : h.s.1 b)
    (hab : a ≠ b) (h1 : ¬ h.lt a b) (h2 : ¬ h.lt b a) :
    ∃ σa σb : Seq Ev, PlacesBefore σa a b ∧ PlacesBefore σb b a ∧
      Excluded (canon (queueSpec Ev) h) σa h σb ∧ ¬ Exposable (canon (queueSpec Ev) h) σa ∧
      ∀ (B : CommitmentBasis (queueSpec Ev)) τ, SysStep B (canon (queueSpec Ev) h) (.output σa) τ →
        B (canonicalCommitment σa) := by
  obtain ⟨σa, σb, hpa, hpb, hba, hbb⟩ := queue_concurrent ha hb hab h1 h2
  exact ⟨σa, σb, hba, hbb, canon_incompatible hpa hpb
    (order_no_common (sp := queueSpec Ev) (j := h) PlacesBefore
      (fun _ _ _ _ h1 h2 => placesBefore_mono h1 h2)
      (fun _ _ _ _ h1 h2 => placesBefore_asymm h1 h2) hba hbb)⟩

omit [DecidableEq Ev] in
/-- The enqueues of `h` are causally totally ordered. -/
def Chain (h : Hist Ev) : Prop := ∀ a b, h.s.1 a → h.s.1 b → a ≠ b → h.lt a b ∨ h.lt b a

omit [DecidableEq Ev] in
theorem qperm_pred {h : Hist Ev} (hc : Chain h) {σ : List Ev} (hp : QPerm h σ) {n : Nat}
    (hn : n < σ.length) (e : Ev) :
    h.lt e σ[n] ↔ ∃ m, ∃ hm : m < σ.length, m < n ∧ σ[m] = e := by
  obtain ⟨hnd, hin, hdown, hsort⟩ := hp
  have hsort' := List.pairwise_iff_getElem.1 hsort
  constructor
  · intro hlt
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 (hdown _ _ (List.getElem_mem hn) hlt)
    refine ⟨m, hm, ?_, rfl⟩
    rcases Nat.lt_trichotomy m n with h1 | h1 | h1
    · exact h1
    · subst h1; exact absurd hlt (h.irrefl _)
    · exact absurd hlt (hsort' n m hn hm h1)
  · rintro ⟨m, hm, hmn, rfl⟩
    have hne : σ[m] ≠ σ[n] := fun he => by have := (hnd.getElem_inj).1 he; omega
    rcases hc _ _ (hin _ (List.getElem_mem hm)) (hin _ (List.getElem_mem hn)) hne with h1 | h1
    · exact h1
    · exact absurd h1 (hsort' m n hm hn hmn)

omit [DecidableEq Ev] in
theorem qperm_eq {h : Hist Ev} (hc : Chain h) {σ τ : List Ev} (hσ : QPerm h σ)
    (hτ : QPerm h τ) : ∀ n (h1 : n < σ.length) (h2 : n < τ.length), σ[n] = τ[n] := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro h1 h2
  apply Classical.byContradiction
  intro hne
  have hin : ∀ {l : List Ev}, QPerm h l → ∀ {k} (hk : k < l.length), h.s.1 l[k] :=
    fun hl _ hk => hl.2.1 _ (List.getElem_mem hk)
  rcases hc _ _ (hin hσ h1) (hin hτ h2) hne with hl | hl
  · obtain ⟨m, hm, hmn, he⟩ := (qperm_pred hc hτ h2 _).1 hl
    have := ih m hmn (by omega) hm
    rw [he] at this
    have := (hσ.1.getElem_inj).1 this
    omega
  · obtain ⟨m, hm, hmn, he⟩ := (qperm_pred hc hσ h1 _).1 hl
    have := ih m hmn hm (by omega)
    rw [he] at this
    have := (hτ.1.getElem_inj).1 this.symm
    omega

omit [DecidableEq Ev] in
/-- At a chain history, the shorter of two permitted dequeue sequences is a
prefix of the longer. -/
theorem qperm_prefix {h : Hist Ev} (hc : Chain h) {σ τ : List Ev} (hσ : QPerm h σ)
    (hτ : QPerm h τ) (hl : σ.length ≤ τ.length) : σ <+: τ := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp [Nat.min_eq_left hl]
  · intro n h1 h2
    rw [List.getElem_take]
    exact qperm_eq hc hσ hτ n h1 (by omega)

omit [DecidableEq Ev] in
theorem queue_chain_comparable {h : Hist Ev} (hc : Chain h) {σ τ : Seq Ev}
    (hσ : (queueSpec Ev).P h σ) (hτ : (queueSpec Ev).P h τ) : σ ≼ τ ∨ τ ≼ σ := by
  rcases Nat.le_total σ.l.length τ.l.length with hl | hl
  · exact Or.inl (qperm_prefix hc hσ hτ hl)
  · exact Or.inr (qperm_prefix hc hτ hσ hl)

omit [DecidableEq Ev] in
/-- A fiber whose outputs are pairwise comparable is directed. -/
theorem directed_of_comparable {I O : Type} [PO I] [PO O] {sp : Spec I O} {i : I}
    (hcmp : ∀ a b, sp.P i a → sp.P i b → a ≼ b ∨ b ≼ a) : JointLift (sp.P i) (sp.P i) := by
  intro X hX hall
  have key : ∀ (Y : List O) (x0 : O), sp.P i x0 → (∀ y ∈ Y, sp.P i y) →
      ∃ u, sp.P i u ∧ x0 ≼ u ∧ ∀ y ∈ Y, y ≼ u := by
    intro Y
    induction Y with
    | nil => intro x0 h0 _; exact ⟨x0, h0, PO.refl _, by simp⟩
    | cons y ys ih =>
      intro x0 h0 hY
      obtain ⟨u, hu, h0u, hys⟩ := ih x0 h0 (fun z hz => hY z (List.mem_cons_of_mem _ hz))
      rcases hcmp y u (hY y (by simp)) hu with hyu | huy
      · refine ⟨u, hu, h0u, fun z hz => ?_⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hyu
        · exact hys z hz
      · refine ⟨y, hY y (by simp), PO.trans h0u huy, fun z hz => ?_⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact PO.refl _
        · exact PO.trans (hys z hz) huy
  match X, hX with
  | x :: xs, _ =>
    obtain ⟨u, hu, hxu, hxs⟩ := key xs x (hall x (by simp))
      (fun z hz => hall z (List.mem_cons_of_mem _ hz))
    refine ⟨u, hu, fun z hz => ?_⟩
    rcases List.mem_cons.1 hz with rfl | hz
    · exact hxu
    · exact hxs z hz

/-- **The fiber at `h` is directed iff the enqueues of `h` are causally
totally ordered.** -/
theorem queue_directed_iff (h : Hist Ev) :
    JointLift ((queueSpec Ev).P h) ((queueSpec Ev).P h) ↔ Chain h := by
  constructor
  · intro hD a b ha hb hab
    apply Classical.byContradiction
    intro hn
    exact (queue_not_directed ha hb hab (fun h' => hn (Or.inl h')) (fun h' => hn (Or.inr h'))).1 hD
  · intro hc
    exact directed_of_comparable (fun _ _ ha hb => queue_chain_comparable hc ha hb)

omit [DecidableEq Ev] in
/-- Histories whose enqueues are causally totally ordered. -/
structure ChainHist (Ev : Type) where
  h : Hist Ev
  chain : Chain h

instance instPOChainHist (Ev : Type) : PO (ChainHist Ev) where
  le a b := a.h ≼ b.h
  refl a := PO.refl a.h
  trans h1 h2 := PO.trans h1 h2
  antisymm := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ h1 h2
    have : a = b := PO.antisymm h1 h2
    subst this; rfl

/-- The causal FIFO queue restricted to chain histories. -/
def queueChainSpec (Ev : Type) : Spec (ChainHist Ev) (Seq Ev) where
  P c s := QPerm c.h s.l
  total c := (queueSpec Ev).total c.h

omit [DecidableEq Ev] in
/-- **Restricted to chain histories, the causal FIFO queue is monotone.** -/
theorem queueChain_liftedMono : (queueChainSpec Ev).LiftedMono :=
  (liftedMono_iff_relMono_directed _).2
    ⟨fun _ _ σ hle hp => ⟨σ, queue_grow hle hp, PO.refl _⟩,
     fun c => directed_of_comparable (sp := queueChainSpec Ev)
       (fun _ _ ha hb => queue_chain_comparable (h := c.h) c.chain ha hb)⟩

/-- The queue without the no-skipping rule. -/
def skipSpec (Ev : Type) : Spec (Hist Ev) (Seq Ev) where
  P h s := s.l.Nodup ∧ (∀ x ∈ s.l, h.s.1 x) ∧ Sorted h s.l
  total _ := ⟨⟨[]⟩, List.nodup_nil, by simp, List.Pairwise.nil⟩

/-- **Without the no-skipping rule, the fiber at any history with two distinct
enqueues is not directed**, whether or not they are causally ordered. -/
theorem skipSpec_not_directed {h : Hist Ev} {a b : Ev} (ha : h.s.1 a) (hb : h.s.1 b)
    (hab : a ≠ b) : ¬ (skipSpec Ev).DirectedOutputs ∧ ¬ (skipSpec Ev).LiftedMono :=
  order_conflict_fiber (sp := skipSpec Ev) (j := h) PlacesBefore
    (fun _ _ _ _ h1 h2 => placesBefore_mono h1 h2) (fun _ _ _ _ h1 h2 => placesBefore_asymm h1 h2)
    (o1 := ⟨[a]⟩) (o2 := ⟨[b]⟩) (a := a) (b := b)
    ⟨by simp, by simpa using ha, by simp [Sorted]⟩ ⟨by simp, by simpa using hb, by simp [Sorted]⟩
    ⟨by simp, fun hm => by simp at hm; exact absurd hm.symm hab⟩
    ⟨by simp, fun hm => by simp at hm; exact absurd hm hab⟩

end Queue

end Apps
end CC
