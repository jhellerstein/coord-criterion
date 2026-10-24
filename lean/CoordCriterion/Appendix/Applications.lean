import CoordCriterion.Appendix.TransactionBases.NoReads
import CoordCriterion.CAP.CompleteCAP
import CoordCriterion.FunctionalCALM.Theorem

/-!
# Additional applications (Appendix I, `app:additional-applications`)

Namespace `CC.Apps` (reuses the finite sets and generic commitment lemmas of
`Appendix/TransactionBases/NoReads.lean`).

* Committed authority:  `Auth`, `prefix_antisymm`, the output order of
  Eq. `authority-refinement` (`instPOAuth`); `safety_exposable` (if every
  remaining row refines the certified evidence `o`, then `o` is exposable and
  `Out_ε(o)` is legal); `incompatible_rejected` (generic: two outputs at the
  current input with no common refinement there ⇒ emitting one rejects the
  other, is not exposable, and needs a commitment); `slot_conflict` and
  `epoch_conflict` instantiate it for competing decisions of one slot and for
  competing next epochs.  The decision claim needs the extra hypothesis that
  permitted outputs decide at most one value per epoch and slot (`SlotUnique`),
  as the paper's definition of `D` states.
* `k`-set agreement (general `k ≥ 1`): `ksetSpec`, `kset_single_row`,
  `kset_union_upper`, `kset_any_k`, `kset_all_fail`,
  `kset_not_commonExpansion`, `kset_not_liftedMono`, `kset_no_cap`.
* Tight renaming: `renSpec`, `ren_singleton_iff`, `ren_each_extends`,
  `ren_no_injective_extends_both`, `ren_not_directed`, `ren_not_liftedMono`,
  `ren_no_cap`.
* Snapshots: `Hist` (finite causal histories under "downward-closed subset
  carrying the restricted order"), `prefixSpec`, `prefix_mono`,
  `prefix_union`, `prefixSpec_liftedMono`, `prefix_empty`;
  `completeSpec_functional`, `completeSpec_not_monotone`,
  `completeSpec_seal_needed` (via Prop. `prop:functional-exposure-boundary`).

Modeling choices: output types contain all partial maps / sets (permitted
outputs are finite); "no common refinement" is proved in the whole output
type, which is stronger.  Decidable equality is assumed on participants and
values (harmless).  The negative side of Complete CAP is
`¬ ∃ Sys, Availability Sys ∧ PartitionConsistency Sys` from
`CC.CAP.complete_cap`; its proof (`cap_necessary`) builds exactly the
partition placing each row's input at a separate participant.
-/

namespace CC
namespace Apps

open CC.Txn

/-! ### Generic: incompatible outputs at the current input -/

section Generic
variable {I O : Type} [PO I] [PO O] {sp : Spec I O}

/-- If `o, o' ∈ R(i)` have no common refinement in `R(i)`, emitting `o`
rejects `(i,o')` (a choice), `o` is not exposable, and every legal output
event emitting `o` applies a commitment. -/
theorem incompatible_rejected {σ : State sp} {o o' : O} (ho : σ.R σ.cur o)
    (ho' : σ.R σ.cur o') (hn : ¬ ∃ u, σ.R σ.cur u ∧ o ≼ u ∧ o' ≼ u) :
    Rejected σ o σ.cur o' ∧ ¬ Exposable σ o ∧
      ∀ (B : Basis sp) γ τ, SysStep B σ (.output γ o) τ → γ ≠ [] := by
  have hno : ¬ o ≼ o' := fun h => hn ⟨o', ho', h, PO.refl _⟩
  have hrej : Rejected σ o σ.cur o' :=
    ⟨ho', hno, fun hs => hs.2 ⟨o, ho, PO.refl _⟩,
     fun hr => let ⟨_, _, u, hu, h1, h2⟩ := hr; hn ⟨u, hu, h1, h2⟩⟩
  refine ⟨hrej, fun he => ?_, fun B γ τ hs => containment_nonempty hs ⟨_, _, Or.inr hrej⟩⟩
  exact ((exposable_iff_empty σ o).1 he).2 ⟨_, _, hrej⟩

/-- If every remaining row refines `o` (what protocol safety is assumed to
guarantee for certified evidence), `o` is exposable and `Out_ε(o)` is legal. -/
theorem safety_exposable {σ : State sp} {o : O} (ho : σ.R σ.cur o)
    (hsafe : ∀ k x, σ.R k x → o ≼ x) (B : Basis sp) :
    Exposable σ o ∧ SysStep B σ (.output [] o) (outState σ o ho) :=
  have he : Exposable σ o := fun k x hx hn => absurd (hsafe k x hx) hn
  ⟨he, eps_step_iff.2 ⟨ho, he, rfl, rfl⟩⟩

end Generic

/-! ### Committed authority, then monotone evidence -/

theorem prefix_antisymm {α : Type} {a b t t' : List α} (h1 : b = a ++ t) (h2 : a = b ++ t') :
    a = b := by
  have hl : t.length = 0 := by
    have := congrArg List.length h1; have := congrArg List.length h2
    simp only [List.length_append] at *; omega
  have ht : t = [] := List.eq_nil_of_length_eq_zero hl
  rw [h1, ht, List.append_nil]

/-- Outputs `(E,V,D)`. -/
structure Auth (Ep Vt Dc : Type) where
  E : List Ep
  V : Vt → Prop
  D : Dc → Prop

variable {Ep Vt Dc : Type}

/-- Eq. `authority-refinement`: prefix, inclusion, inclusion. -/
instance instPOAuth (Ep Vt Dc : Type) : PO (Auth Ep Vt Dc) where
  le a b := (∃ t, b.E = a.E ++ t) ∧ (∀ v, a.V v → b.V v) ∧ (∀ d, a.D d → b.D d)
  refl a := ⟨⟨[], (List.append_nil _).symm⟩, fun _ h => h, fun _ h => h⟩
  trans := by
    rintro a b c ⟨⟨t1, h1⟩, v1, d1⟩ ⟨⟨t2, h2⟩, v2, d2⟩
    exact ⟨⟨t1 ++ t2, by rw [h2, h1, List.append_assoc]⟩,
      fun v h => v2 v (v1 v h), fun d h => d2 d (d1 d h)⟩
  antisymm := by
    rintro ⟨E, V, D⟩ ⟨E', V', D'⟩ ⟨⟨t1, h1⟩, v1, d1⟩ ⟨⟨t2, h2⟩, v2, d2⟩
    have hE : E = E' := prefix_antisymm h1 h2
    have hV : V = V' := funext fun x => propext ⟨v1 x, v2 x⟩
    have hD : D = D' := funext fun x => propext ⟨d1 x, d2 x⟩
    subst hE hV hD; rfl

/-- At most one decision per epoch and slot (`slot d` names the pair). -/
def SlotUnique {κ : Type} (slot : Dc → κ) (D : Dc → Prop) : Prop :=
  ∀ d d', D d → D d' → slot d = slot d' → d = d'

/-- Competing decisions for one slot have no common refinement among outputs
that decide at most one value per slot. -/
theorem slot_no_common {κ : Type} (slot : Dc → κ) {o o' : Auth Ep Vt Dc} {d d' : Dc}
    (hd : o.D d) (hd' : o'.D d') (hs : slot d = slot d') (hne : d ≠ d') :
    ¬ ∃ u : Auth Ep Vt Dc, SlotUnique slot u.D ∧ o ≼ u ∧ o' ≼ u :=
  fun ⟨_, hU, h1, h2⟩ => hne (hU _ _ (h1.2.2 d hd) (h2.2.2 d' hd') hs)

/-- **Certifying one of two competing proposals is a commitment**, in any
specification on these outputs whose permitted outputs are slot-unique. -/
theorem slot_conflict {I : Type} [PO I] {κ : Type} (slot : Dc → κ)
    {sp : Spec I (Auth Ep Vt Dc)} (hU : ∀ k u, sp.S k u → SlotUnique slot u.D)
    {σ : State sp} {o o' : Auth Ep Vt Dc} (ho : σ.R σ.cur o) (ho' : σ.R σ.cur o')
    {d d' : Dc} (hd : o.D d) (hd' : o'.D d') (hs : slot d = slot d') (hne : d ≠ d') :
    Rejected σ o σ.cur o' ∧ ¬ Exposable σ o ∧
      ∀ (B : Basis sp) γ τ, SysStep B σ (.output γ o) τ → γ ≠ [] :=
  incompatible_rejected ho ho' fun ⟨u, hu, h1, h2⟩ =>
    slot_no_common slot hd hd' hs hne ⟨u, hU _ _ (σ.sub _ _ hu), h1, h2⟩

theorem epoch_no_common {o o' : Auth Ep Vt Dc} {e : List Ep} {a b : Ep}
    (he : o.E = e ++ [a]) (he' : o'.E = e ++ [b]) (hne : a ≠ b) :
    ¬ ∃ u : Auth Ep Vt Dc, o ≼ u ∧ o' ≼ u := by
  rintro ⟨u, ⟨⟨t, ht⟩, _⟩, ⟨⟨t', ht'⟩, _⟩⟩
  rw [he, ht', he', List.append_assoc, List.append_assoc] at ht
  have := List.append_cancel_left ht
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at this
  exact hne this.1.symm

/-- **Competing next epochs would require a commitment** if the succession
rule did not fix the successor. -/
theorem epoch_conflict {I : Type} [PO I] {sp : Spec I (Auth Ep Vt Dc)} {σ : State sp}
    {o o' : Auth Ep Vt Dc} (ho : σ.R σ.cur o) (ho' : σ.R σ.cur o') {e : List Ep} {a b : Ep}
    (he : o.E = e ++ [a]) (he' : o'.E = e ++ [b]) (hne : a ≠ b) :
    Rejected σ o σ.cur o' ∧ ¬ Exposable σ o ∧
      ∀ (B : Basis sp) γ τ, SysStep B σ (.output γ o) τ → γ ≠ [] :=
  incompatible_rejected ho ho' fun ⟨u, _, h1, h2⟩ => epoch_no_common he he' hne ⟨u, h1, h2⟩

/-! ### Partial maps ordered by extension -/

structure PMap (P V : Type) where
  f : P → Option V

instance instPOPMap (P V : Type) : PO (PMap P V) where
  le m m' := ∀ p a, m.f p = some a → m'.f p = some a
  refl _ _ _ h := h
  trans h1 h2 p a h := h2 p a (h1 p a h)
  antisymm := by
    rintro ⟨f⟩ ⟨g⟩ h1 h2
    congr
    funext p
    cases hf : f p with
    | some a => exact (h1 p a hf).symm
    | none =>
      cases hg : g p with
      | none => rfl
      | some a => have := h2 p a hg; simp_all

/-! ### k-set agreement -/

section KSet
variable {P Val : Type}

/-- Inputs: finite sets of proposals, at most one per participant. -/
def KInput (P Val : Type) : Type :=
  {s : FinSet (P × Val) // ∀ p a b, s.1 (p, a) → s.1 (p, b) → a = b}

instance instPOKInput (P Val : Type) : PO (KInput P Val) where
  le a b := ∀ x, a.1.1 x → b.1.1 x
  refl _ _ h := h
  trans h1 h2 x hx := h2 x (h1 x hx)
  antisymm {a b} h1 h2 := by
    apply Subtype.ext; apply Subtype.ext
    exact funext fun x => propext ⟨h1 x, h2 x⟩

/-- Permitted: decides only proposers, validity, at most `k` values. -/
def ksetS (k : Nat) (I : KInput P Val) (m : PMap P Val) : Prop :=
  (∀ p a, m.f p = some a → ∃ b, I.1.1 (p, b)) ∧
  (∀ p a, m.f p = some a → ∃ q, I.1.1 (q, a)) ∧
  ∃ l : List Val, l.length ≤ k ∧ ∀ p a, m.f p = some a → a ∈ l

def ksetSpec (P Val : Type) (k : Nat) : Spec (KInput P Val) (PMap P Val) where
  S := ksetS k
  total _ := ⟨⟨fun _ => none⟩, by
    unfold ksetS
    refine ⟨?_, ?_, [], Nat.zero_le _, ?_⟩ <;> intro _ _ h <;> simp at h⟩

variable [DecidableEq P] {k : Nat}

/-- `p_r`'s proposal input `{(p_r, v_r)}`. -/
def propIn (p : Fin (k + 1) → P) (v : Fin (k + 1) → Val) (r : Fin (k + 1)) : KInput P Val :=
  ⟨FinSet.ofList [(p r, v r)] (by simp), fun _ _ _ h1 h2 => by
    simp only [FinSet.ofList, List.mem_singleton, Prod.mk.injEq] at h1 h2
    rw [h1.2, h2.2]⟩

/-- `{p_r ↦ v_r}`. -/
def single (p : Fin (k + 1) → P) (v : Fin (k + 1) → Val) (r : Fin (k + 1)) : PMap P Val :=
  ⟨fun q => if q = p r then some (v r) else none⟩

theorem single_some {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val} {r : Fin (k + 1)} {q : P}
    {a : Val} (h : (single p v r).f q = some a) : q = p r ∧ a = v r := by
  simp only [single] at h
  split at h
  · exact ⟨‹_›, (Option.some.inj h).symm⟩
  · exact nomatch h

def unionList (p : Fin (k + 1) → P) (v : Fin (k + 1) → Val) : List (P × Val) :=
  (List.finRange (k + 1)).map fun r => (p r, v r)

theorem mem_unionList {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val} {x : P × Val} :
    x ∈ unionList p v ↔ ∃ r, (p r, v r) = x := by
  simp [unionList]

/-- The union of the proposal inputs (an input since the `p_r` are distinct). -/
def unionIn (p : Fin (k + 1) → P) (v : Fin (k + 1) → Val)
    (hp : ∀ r r', p r = p r' → r = r') : KInput P Val :=
  ⟨FinSet.ofList (unionList p v)
    (List.Pairwise.map _ (fun a b hab h => hab (hp a b (Prod.mk.inj h).1))
      (List.nodup_finRange (k + 1))),
   fun q a b h1 h2 => by
    obtain ⟨r, hr⟩ := mem_unionList.1 h1
    obtain ⟨r', hr'⟩ := mem_unionList.1 h2
    simp only [Prod.mk.injEq] at hr hr'
    have : r = r' := hp r r' (hr.1.trans hr'.1.symm)
    subst this
    rw [← hr.2, ← hr'.2]⟩

variable {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val}

/-- At `p_r`'s proposal input, `{p_r ↦ v_r}` is permitted (`k ≥ 1`). -/
theorem kset_single_row (hk : 1 ≤ k) (r : Fin (k + 1)) :
    (ksetSpec P Val k).S (propIn p v r) (single p v r) := by
  show ksetS k _ _
  refine ⟨fun q a h => ?_, fun q a h => ?_, [v r], hk, fun q a h => ?_⟩
  · obtain ⟨rfl, _⟩ := single_some h; exact ⟨v r, List.mem_singleton_self _⟩
  · obtain ⟨_, rfl⟩ := single_some h; exact ⟨p r, List.mem_singleton_self _⟩
  · obtain ⟨_, rfl⟩ := single_some h; exact List.mem_singleton_self _

variable (hp : ∀ r r', p r = p r' → r = r')
include hp

/-- The union of the proposal inputs is a common expansion. -/
theorem kset_union_upper (r : Fin (k + 1)) : propIn p v r ≼ unionIn p v hp := by
  intro x hx
  simp only [propIn, FinSet.ofList, List.mem_singleton] at hx
  subst hx
  exact mem_unionList.2 ⟨r, rfl⟩
omit hp

open Classical in
/-- The map deciding `p_r ↦ v_r` for every `r ≠ r₀`. -/
noncomputable def allBut (p : Fin (k + 1) → P) (v : Fin (k + 1) → Val) (r0 : Fin (k + 1)) :
    PMap P Val :=
  ⟨fun q => if h : ∃ r, r ≠ r0 ∧ p r = q then some (v (Classical.choose h)) else none⟩

theorem allBut_some {r0 : Fin (k + 1)} {q : P} {a : Val} (h : (allBut p v r0).f q = some a) :
    ∃ r, r ≠ r0 ∧ p r = q ∧ a = v r := by
  simp only [allBut] at h
  split at h
  · rename_i hex
    have hc := Classical.choose_spec hex
    exact ⟨_, hc.1, hc.2, (Option.some.inj h).symm⟩
  · exact nomatch h

include hp in
theorem allBut_at {r0 r : Fin (k + 1)} (hr : r ≠ r0) : (allBut p v r0).f (p r) = some (v r) := by
  have hex : ∃ r', r' ≠ r0 ∧ p r' = p r := ⟨r, hr, rfl⟩
  simp only [allBut, dif_pos hex]
  have := hp _ _ (Classical.choose_spec hex).2
  rw [this]

include hp in
/-- **Any `k` of the `k+1` rows have a common refinement at the union.** -/
theorem kset_any_k (r0 : Fin (k + 1)) :
    ∃ u, (ksetSpec P Val k).S (unionIn p v hp) u ∧ ∀ r, r ≠ r0 → single p v r ≼ u := by
  refine ⟨allBut p v r0, ?_, fun r hr q a h => ?_⟩
  · show ksetS k _ _
    refine ⟨fun q a h => ?_, fun q a h => ?_,
      ((List.finRange (k + 1)).erase r0).map v, ?_, fun q a h => ?_⟩
    · obtain ⟨r, _, rfl, rfl⟩ := allBut_some h
      exact ⟨v r, mem_unionList.2 ⟨r, rfl⟩⟩
    · obtain ⟨r, _, rfl, rfl⟩ := allBut_some h
      exact ⟨p r, mem_unionList.2 ⟨r, rfl⟩⟩
    · rw [List.length_map, List.length_erase_of_mem (List.mem_finRange r0),
        List.length_finRange]
      omega
    · obtain ⟨r, hr, rfl, rfl⟩ := allBut_some h
      exact List.mem_map.2 ⟨r, (List.mem_erase_of_ne hr).2 (List.mem_finRange r), rfl⟩
  · obtain ⟨rfl, rfl⟩ := single_some h
    exact allBut_at hp hr

variable (hv : ∀ r r', v r = v r' → r = r')
include hp hv

/-- **All `k+1` rows have no common refinement at the union** (it would have
`k+1` values). -/
theorem kset_all_fail :
    ¬ ∃ u, (ksetSpec P Val k).S (unionIn p v hp) u ∧ ∀ r, single p v r ≼ u := by
  rintro ⟨u, ⟨_, _, l, hl, hcov⟩, hall⟩
  have hsub : (List.finRange (k + 1)).map v ⊆ l := by
    intro a ha
    obtain ⟨r, _, rfl⟩ := List.mem_map.1 ha
    exact hcov (p r) (v r) (hall r (p r) (v r) (by simp [single]))
  have hnd : ((List.finRange (k + 1)).map v).Nodup :=
    List.Pairwise.map _ (fun a b hab h => hab (hv a b h)) (List.nodup_finRange (k + 1))
  have := hnd.length_le_of_subset hsub
  rw [List.length_map, List.length_finRange] at this
  omega

/-- **The common-expansion condition fails.** -/
theorem kset_not_commonExpansion (hk : 1 ≤ k) : ¬ (ksetSpec P Val k).CommonExpansion := by
  intro hce
  let rows := (List.finRange (k + 1)).map fun r => (propIn p v r, single p v r)
  obtain ⟨u, hu, hall⟩ := hce rows
    (by
      intro x hx
      obtain ⟨r, _, rfl⟩ := List.mem_map.1 hx
      exact kset_single_row hk r)
    (unionIn p v hp)
    (by
      intro x hx
      obtain ⟨r, _, rfl⟩ := List.mem_map.1 hx
      exact kset_union_upper hp r)
  exact kset_all_fail hp hv
    ⟨u, hu, fun r => hall _ (List.mem_map.2 ⟨r, List.mem_finRange r, rfl⟩)⟩

/-- **Not monotone** (Prop. `prop:common-expansion-form`). -/
theorem kset_not_liftedMono (hk : 1 ≤ k) : ¬ (ksetSpec P Val k).LiftedMono :=
  fun h => kset_not_commonExpansion hp hv hk ((liftedMono_iff_commonExpansion _).1 h)

/-- **Negative side of Complete CAP.** -/
theorem kset_no_cap (hk : 1 ≤ k) (D : Type) :
    ¬ ∃ Sys : CAP.System (ksetSpec P Val k) D,
      CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  fun h => kset_not_liftedMono hp hv hk ((CAP.complete_cap _ D).1 h)

end KSet

/-! ### Tight renaming -/

section Renaming
variable {P : Type} [DecidableEq P]

/-- `|N|`. -/
noncomputable def card (N : FinSet P) : Nat := (Classical.choose N.2).length

theorem card_eq (N : FinSet P) {l : List P} (hl : l.Nodup) (hm : ∀ x, N.1 x ↔ x ∈ l) :
    card N = l.length := by
  have hc := Classical.choose_spec N.2
  apply Nat.le_antisymm
  · exact hc.1.length_le_of_subset fun x hx => (hm x).1 ((hc.2 x).2 hx)
  · exact hl.length_le_of_subset fun x hx => (hc.2 x).1 ((hm x).2 hx)

def Injective (m : PMap P Nat) : Prop := ∀ x y n, m.f x = some n → m.f y = some n → x = y

/-- Outputs at `N`: injective maps `N → {1,…,|N|}`. -/
def renS (N : FinSet P) (m : PMap P Nat) : Prop :=
  (∀ x, N.1 x ↔ ∃ n, m.f x = some n) ∧ Injective m ∧
  ∀ x n, m.f x = some n → 1 ≤ n ∧ n ≤ card N

noncomputable def renSpec (P : Type) [DecidableEq P] : Spec (FinSet P) (PMap P Nat) where
  S := renS
  total N := by
    obtain ⟨l, hl, hm⟩ := N.2
    refine ⟨⟨fun x => if x ∈ l then some (l.idxOf x + 1) else none⟩, fun x => ?_, ?_, ?_⟩
    · rw [hm x]; by_cases h : x ∈ l <;> simp [h]
    · intro x y n hx hy
      simp only at hx hy
      split at hx <;> split at hy <;> simp_all
      rename_i h1 h2
      have e1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem h1)
      have e2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem h2)
      have hxy : l.idxOf x = l.idxOf y := by omega
      rw [← e1, ← e2]; simp only [hxy]
    · intro x n hx
      simp only at hx
      split at hx
      · rename_i h
        simp only [Option.some.injEq] at hx
        rw [card_eq N hl hm]
        have := List.idxOf_lt_length_of_mem h
        omega
      · exact nomatch hx

/-- `{p}`. -/
def sing (p : P) : FinSet P := FinSet.ofList [p] (by simp)

/-- `p ↦ 1`. -/
def name1 (p : P) : PMap P Nat := ⟨fun x => if x = p then some 1 else none⟩

theorem card_sing (p : P) : card (sing p) = 1 := card_eq _ (l := [p]) (by simp) fun _ => Iff.rfl

/-- **At `{p}` the only output is `p ↦ 1`.** -/
theorem ren_singleton_iff (p : P) (m : PMap P Nat) : (renSpec P).S (sing p) m ↔ m = name1 p := by
  constructor
  · rintro ⟨hdom, _, hb⟩
    cases m with
    | mk f =>
    congr
    funext x
    by_cases hx : x = p
    · subst hx
      obtain ⟨n, hn⟩ := (hdom x).1 (List.mem_singleton_self x)
      have := hb x n hn
      rw [card_sing] at this
      have : n = 1 := by omega
      subst this; rw [if_pos rfl]; exact hn
    · simp only [name1, if_neg hx]
      cases hf : f x with
      | none => rfl
      | some n =>
        have := (hdom x).2 ⟨n, hf⟩
        simp [sing, FinSet.ofList] at this
        exact absurd this hx
  · rintro rfl
    refine ⟨fun x => ?_, fun x y n hx hy => ?_, fun x n hx => ?_⟩
    · simp only [sing, FinSet.ofList, List.mem_singleton, name1]
      by_cases h : x = p <;> simp [h]
    · simp only [name1] at hx hy
      split at hx <;> split at hy <;> simp_all
    · simp only [name1] at hx
      split at hx
      · simp only [Option.some.injEq] at hx; subst hx; rw [card_sing]; omega
      · exact nomatch hx

/-- `{p ↦ a, q ↦ b}`. -/
def name2 (p q : P) (a b : Nat) : PMap P Nat :=
  ⟨fun x => if x = p then some a else if x = q then some b else none⟩

theorem card_pair {p q : P} (h : p ≠ q) : card (pairSet p q h) = 2 :=
  card_eq _ (l := [p, q]) (by simp [h]) fun _ => Iff.rfl

theorem name2_row {p q : P} (h : p ≠ q) {a b : Nat} (hab : a ≠ b) (ha : 1 ≤ a ∧ a ≤ 2)
    (hb : 1 ≤ b ∧ b ≤ 2) : (renSpec P).S (pairSet p q h) (name2 p q a b) := by
  refine ⟨fun x => ?_, fun x y n hx hy => ?_, fun x n hx => ?_⟩
  · rw [pairSet_mem]
    by_cases h1 : x = p
    · simp [name2, h1]
    · by_cases h2 : x = q <;> simp [name2, h1, h2, Ne.symm h]
  · simp only [name2] at hx hy
    split at hx <;> split at hy <;> (try split at hx) <;> (try split at hy) <;> simp_all
  · rw [card_pair h]
    simp only [name2] at hx
    split at hx
    · simp only [Option.some.injEq] at hx; omega
    · split at hx
      · simp only [Option.some.injEq] at hx; omega
      · exact nomatch hx

/-- **Each of `p ↦ 1`, `q ↦ 1` has a refinement at `{p,q}`** (so Relational
Monotonicity does not fail here). -/
theorem ren_each_extends {p q : P} (h : p ≠ q) :
    (∃ u, (renSpec P).S (pairSet p q h) u ∧ name1 p ≼ u) ∧
    (∃ u, (renSpec P).S (pairSet p q h) u ∧ name1 q ≼ u) := by
  refine ⟨⟨name2 p q 1 2, name2_row h (by decide) (by decide) (by decide), ?_⟩,
          ⟨name2 p q 2 1, name2_row h (by decide) (by decide) (by decide), ?_⟩⟩
  · intro x n hx
    simp only [name1] at hx; split at hx
    · rename_i hxp; subst hxp; simp_all [name2]
    · exact nomatch hx
  · intro x n hx
    simp only [name1] at hx; split at hx
    · rename_i hxq; subst hxq; simp [name2, Ne.symm h] at hx ⊢; exact hx
    · exact nomatch hx

/-- **No injective map extends both.** -/
theorem ren_no_injective_extends_both {p q : P} (h : p ≠ q) :
    ¬ ∃ u : PMap P Nat, Injective u ∧ name1 p ≼ u ∧ name1 q ≼ u :=
  fun ⟨u, hi, h1, h2⟩ => h (hi p q 1 (h1 p 1 (by simp [name1])) (h2 q 1 (by simp [name1])))

/-- Hence the common-expansion condition fails at `{p}`, `{q}` ⊑ `{p,q}`. -/
theorem ren_not_commonExpansion {p q : P} (h : p ≠ q) : ¬ (renSpec P).CommonExpansion := by
  intro hce
  obtain ⟨u, hu, hall⟩ := hce [(sing p, name1 p), (sing q, name1 q)]
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (ren_singleton_iff _ _).2 rfl
      · exact (ren_singleton_iff _ _).2 rfl)
    (pairSet p q h)
    (by
      intro r hr x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [pairSet_mem]
      rcases hr with rfl | rfl <;>
        simp only [sing, FinSet.ofList, List.mem_singleton] at hx <;> simp [hx])
  exact ren_no_injective_extends_both h ⟨u, hu.2.1, hall (sing p, name1 p) (by simp), hall (sing q, name1 q) (by simp)⟩

/-- **Directed Outputs fails at `{p,q}`**: `{p↦1,q↦2}` and `{p↦2,q↦1}` have no
common refinement; so Lifted Monotonicity fails. -/
theorem ren_not_directed {p q : P} (h : p ≠ q) :
    (¬ ∃ u, name2 p q 1 2 ≼ u ∧ name2 p q 2 1 ≼ u) ∧
    ¬ (renSpec P).DirectedOutputs ∧ ¬ (renSpec P).LiftedMono := by
  have hn : ¬ ∃ u, name2 p q 1 2 ≼ u ∧ name2 p q 2 1 ≼ u := by
    rintro ⟨u, h1, h2⟩
    have a := h1 p 1 (by simp [name2])
    have b := h2 p 2 (by simp [name2])
    rw [a] at b; exact absurd (Option.some.inj b) (by decide)
  exact ⟨hn, not_directed_of (name2_row h (by decide) (by decide) (by decide))
    (name2_row h (by decide) (by decide) (by decide)) hn⟩

theorem ren_not_liftedMono {p q : P} (h : p ≠ q) : ¬ (renSpec P).LiftedMono :=
  (ren_not_directed h).2.2

/-- **Negative side of Complete CAP** for tight renaming. -/
theorem ren_no_cap {p q : P} (h : p ≠ q) (D : Type) :
    ¬ ∃ Sys : CAP.System (renSpec P) D, CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  fun hs => ren_not_liftedMono h ((CAP.complete_cap _ D).1 hs)

end Renaming

/-! ### Snapshots -/

section Snapshots
variable {Ev : Type}

/-- A finite causal history: a finite set of events with a strict causal order. -/
structure Hist (Ev : Type) where
  s : FinSet Ev
  lt : Ev → Ev → Prop
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ a b c, lt a b → lt b c → lt a c
  supp : ∀ a b, lt a b → s.1 a ∧ s.1 b

theorem Hist.ext' {h h' : Hist Ev} (hs : h.s = h'.s) (hl : h.lt = h'.lt) : h = h' := by
  cases h; cases h'; cases hs; cases hl; rfl

/-- `h ⊑ h'`: `h` is a downward-closed subset of `h'` carrying the restricted
order. -/
def Hist.le (h h' : Hist Ev) : Prop :=
  (∀ x, h.s.1 x → h'.s.1 x) ∧ (∀ a b, h.s.1 b → h'.lt a b → h.s.1 a) ∧
  ∀ a b, h.s.1 a → h.s.1 b → (h.lt a b ↔ h'.lt a b)

instance instPOHist (Ev : Type) : PO (Hist Ev) where
  le := Hist.le
  refl _ := ⟨fun _ h => h, fun a b hb hab => ((‹Hist Ev›).supp a b hab).1,
    fun _ _ _ _ => Iff.rfl⟩
  trans {h1 h2 h3} A B :=
    ⟨fun x hx => B.1 x (A.1 x hx),
     fun a b hb hab => by
       have h2b := A.1 b hb
       have h2a := B.2.1 a b h2b hab
       exact A.2.1 a b hb ((B.2.2 a b h2a h2b).2 hab),
     fun a b ha hb => (A.2.2 a b ha hb).trans (B.2.2 a b (A.1 a ha) (A.1 b hb))⟩
  antisymm {h h'} A B := by
    apply Hist.ext'
    · exact Subtype.ext (funext fun x => propext ⟨A.1 x, B.1 x⟩)
    · funext a b
      apply propext
      constructor
      · intro hab; have hs := h.supp a b hab; exact (A.2.2 a b hs.1 hs.2).1 hab
      · intro hab
        have hs := h'.supp a b hab
        exact (A.2.2 a b (B.1 a hs.1) (B.1 b hs.2)).2 hab

/-- Sets of events ordered by inclusion. -/
structure ESet (Ev : Type) where
  mem : Ev → Prop

instance instPOESet (Ev : Type) : PO (ESet Ev) where
  le a b := ∀ x, a.mem x → b.mem x
  refl _ _ h := h
  trans h1 h2 x hx := h2 x (h1 x hx)
  antisymm := by
    rintro ⟨a⟩ ⟨b⟩ h1 h2
    congr; funext x; exact propext ⟨h1 x, h2 x⟩

/-- A downward-closed subset of `h`. -/
def IsPrefix (h : Hist Ev) (p : ESet Ev) : Prop :=
  (∀ x, p.mem x → h.s.1 x) ∧ ∀ a b, p.mem b → h.lt a b → p.mem a

/-- The prefix specification. -/
def prefixSpec (Ev : Type) : Spec (Hist Ev) (ESet Ev) where
  S := IsPrefix
  total _ := ⟨⟨fun _ => False⟩, by
    show IsPrefix _ _
    exact ⟨fun _ h => h.elim, fun _ _ h => h.elim⟩⟩

/-- The empty prefix is always permitted (no freshness or completeness). -/
theorem prefix_empty (h : Hist Ev) : (prefixSpec Ev).S h ⟨fun _ => False⟩ :=
  show IsPrefix _ _ from ⟨fun _ h => h.elim, fun _ _ h => h.elim⟩

/-- **Old prefixes stay legal as history grows.** -/
theorem prefix_mono {h h' : Hist Ev} (hle : h ≼ h') {p : ESet Ev} (hp : IsPrefix h p) :
    IsPrefix h' p := by
  refine ⟨fun x hx => hle.1 x (hp.1 x hx), fun a b hb hab => ?_⟩
  have hsb := hp.1 b hb
  have hsa := hle.2.1 a b hsb hab
  exact hp.2 a b hb ((hle.2.2 a b hsa hsb).2 hab)

/-- **Finite unions of prefixes are prefixes.** -/
theorem prefix_union {j : Hist Ev} (ps : List (ESet Ev)) (hps : ∀ p ∈ ps, IsPrefix j p) :
    IsPrefix j ⟨fun x => ∃ p ∈ ps, p.mem x⟩ :=
  ⟨fun _ ⟨p, hp, hx⟩ => (hps p hp).1 _ hx,
   fun a b ⟨p, hp, hb⟩ hab => ⟨p, hp, (hps p hp).2 a b hb hab⟩⟩

theorem prefixSpec_commonExpansion : (prefixSpec Ev).CommonExpansion := by
  intro rows hrows j hj
  refine ⟨⟨fun x => ∃ p ∈ rows.map Prod.snd, p.mem x⟩, prefix_union _ ?_, fun r hr x hx =>
    ⟨r.2, List.mem_map.2 ⟨r, hr, rfl⟩, hx⟩⟩
  intro p hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hp
  exact prefix_mono (hj r hr) (hrows r hr)

/-- **The prefix specification satisfies Lifted Monotonicity.** -/
theorem prefixSpec_liftedMono : (prefixSpec Ev).LiftedMono :=
  (liftedMono_iff_commonExpansion _).2 prefixSpec_commonExpansion

/-- Outputs ordered by equality. -/
structure Eqd (α : Type) where
  val : α

instance instPOEqd (α : Type) : PO (Eqd α) where
  le a b := a = b
  refl _ := rfl
  trans h1 h2 := h1.trans h2
  antisymm h _ := h

/-- The complete-history specification: output `h` at `h`. -/
def completeSpec (Ev : Type) : Spec (Hist Ev) (Eqd (Hist Ev)) where
  S h o := o = ⟨h⟩
  total h := ⟨⟨h⟩, rfl⟩

theorem completeSpec_functional : (completeSpec Ev).Functional :=
  fun _ _ _ h1 h2 => h1.trans h2.symm

def emptyHist : Hist Ev where
  s := FinSet.ofList [] List.nodup_nil
  lt _ _ := False
  irrefl _ h := h
  trans _ _ _ h _ := h
  supp _ _ h := h.elim

def singleHist (e : Ev) : Hist Ev where
  s := FinSet.ofList [e] (by simp)
  lt _ _ := False
  irrefl _ h := h
  trans _ _ _ h _ := h
  supp _ _ h := h.elim

theorem empty_le_single (e : Ev) : (emptyHist : Hist Ev) ≼ singleHist e :=
  show Hist.le _ _ from
    ⟨fun _ h => by simp [emptyHist, FinSet.ofList] at h,
     fun _ _ h => by simp [emptyHist, FinSet.ofList] at h,
     fun _ _ h => by simp [emptyHist, FinSet.ofList] at h⟩

/-- **The complete-history specification is not monotone** (whenever an event
can arrive): its required output changes. -/
theorem completeSpec_not_monotone (e : Ev) :
    ¬ (completeSpec Ev).MonotoneF ∧ ¬ (completeSpec Ev).LiftedMono := by
  have hne : (⟨emptyHist⟩ : Eqd (Hist Ev)) ≠ ⟨singleHist e⟩ := by
    intro h
    have : (emptyHist : Hist Ev).s.1 e := by
      have h' := congrArg (fun x : Eqd (Hist Ev) => x.val.s.1 e) h
      simp only at h'
      rw [h']; exact List.mem_singleton_self e
    exact nomatch this
  refine ⟨fun hm => hne (hm _ _ _ _ (empty_le_single e) rfl rfl), fun hl => ?_⟩
  obtain ⟨u, hu, hall⟩ := hl _ _ (empty_le_single e) [⟨emptyHist⟩] (by simp) (by simp [completeSpec])
  exact hne ((hall _ (by simp)).trans hu)

/-- **Some output can be exposed only after a commitment that seals an
input** (Prop. `prop:functional-exposure-boundary`): there is a state
reachable without commitment and an output there whose `Sealed` class is
nonempty, so every legal output event emitting it applies a commitment, and
every such commitment seals each input where it removes rows. -/
theorem completeSpec_seal_needed (e : Ev) :
    ∃ (τ : State (completeSpec Ev)) (o : Eqd (Hist Ev)), ReachableCF τ ∧ τ.R τ.cur o ∧
      (∃ k x, Sealed τ o k x) ∧ (∀ k x, ¬ Rejected τ o k x) ∧
      ∀ (B : Basis (completeSpec Ev)) γ τ', SysStep B τ (.output γ o) τ' → γ ≠ [] := by
  have hb := fun h => (completeSpec_not_monotone e).1
    ((functional_exposure_boundary (completeSpec_functional (Ev := Ev))).2 h)
  apply Classical.byContradiction
  intro hno
  apply hb
  intro τ hτ o ho
  apply Classical.byContradiction
  intro hne
  apply hno
  have hrej : ∀ k x, ¬ Rejected τ o k x := by
    intro k x hr
    have : ∃ u, τ.R k u ∧ o ≼ u :=
      Classical.byContradiction fun hn => hr.2.2.1 ⟨hr.1, hn⟩
    obtain ⟨u, hu, hou⟩ := this
    have : u = x := completeSpec_functional k u x (τ.sub _ _ hu) (τ.sub _ _ hr.1)
    exact hr.2.1 (this ▸ hou)
  have hseal : ∃ k x, Sealed τ o k x := by
    apply Classical.byContradiction
    intro hs
    exact hne ((exposable_iff_empty τ o).2 ⟨hs, fun ⟨k, x, h⟩ => hrej k x h⟩)
  obtain ⟨k, x, hs⟩ := hseal
  exact ⟨τ, o, hτ, ho, ⟨k, x, hs⟩, hrej,
    fun B γ τ' hst => containment_nonempty hst ⟨k, x, Or.inl hs⟩⟩

end Snapshots

end Apps
end CC
