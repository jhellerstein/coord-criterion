import CoordCriterion.Appendix.Deployment
import CoordCriterion.Appendix.Frontiers

/-!
# Deployment: generic facts and the leader example (Appendix `app:deployment`)

Claims of `appendices/deployment.tex` beyond the definitions and the
proposition in `Appendix/Deployment.lean`, all for the definitions of
`CC.Deploy`:

* a single run's emitted outputs form a chain (`rows_chain`, `rows_max`);
* rows authorized only to `p` form a separable family only as a single row
  (`sole_rows_separable`, `sole_rows_two_not_separable`);
* single-authority deployments (`single_authority_shape`,
  `single_authority_iff`);
* the leader example (fibers `{a,b}` ordered by equality, `A_p = S`,
  `A_q = ∅`, arbitrary input poset): `lead_monoAcross`, `lead_not_liftedMono`,
  `lead_separable_shape`, `lead_run_one_output`;
* the sufficient condition "each authorized row has an expansion at every
  expansion of its input, and every set of authorized rows lacking a common
  expansion is authorized only to one participant"
  (`monoAcross_of_sole_conflicts`).
-/

namespace CC
namespace Deploy

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CC.CAP (step_input_inv step_output_inv)

/-! ## Part A: deployments -/

section Chain
variable {I O : Type} [PO I] [PO O] {sp : Spec I O}

/-- Along an execution, emitted outputs form a chain, and every emitted row
lies in the starting remainder table. -/
theorem exec_chain {σ τ : State sp} {es : List (Event I O)} (hx : Exec σ es τ) :
    List.Pairwise (fun a b : I × O => a.2 ≼ b.2) (emitted σ.cur es) ∧
      ∀ r ∈ emitted σ.cur es, σ.R r.1 r.2 := by
  induction hx with
  | nil => exact ⟨List.Pairwise.nil, by simp [emitted]⟩
  | @cons σ τ' ρ e es hs _ ih =>
    cases e with
    | input j =>
      obtain ⟨_, hcur, hR⟩ := step_input_inv hs
      rw [hcur] at ih
      refine ⟨by simpa [emitted] using ih.1, ?_⟩
      intro r hr
      have := ih.2 r (by simpa [emitted] using hr)
      rw [hR] at this; exact this.1
    | output o =>
      obtain ⟨hleg, hcur, hR⟩ := step_output_inv hs
      rw [hcur] at ih
      simp only [emitted]
      refine ⟨List.Pairwise.cons (fun r hr => ?_) ih.1, ?_⟩
      · have := ih.2 r hr; rw [hR] at this; exact this.2
      · intro r hr
        rcases List.mem_cons.1 hr with rfl | hr
        · exact hleg
        · have := ih.2 r hr; rw [hR] at this; exact this.1

/-- "Each output event keeps only rows refining it": a participant run's
emitted outputs form a chain in emission order. -/
theorem rows_chain (m : PRun sp) :
    List.Pairwise (fun a b : I × O => a.2 ≼ b.2) m.rows :=
  (exec_chain m.exec).1

theorem pairwise_max : ∀ (l : List (I × O)), l ≠ [] →
    List.Pairwise (fun a b : I × O => a.2 ≼ b.2) l → ∃ r ∈ l, ∀ r' ∈ l, r'.2 ≼ r.2
  | [], h, _ => absurd rfl h
  | [a], _, _ => ⟨a, by simp, fun r' hr' => by
      simp at hr'; subst hr'; exact PO.refl _⟩
  | a :: b :: l, _, hp => by
    obtain ⟨r, hr, hmax⟩ := pairwise_max (b :: l) (by simp) (List.Pairwise.of_cons hp)
    refine ⟨r, List.mem_cons_of_mem _ hr, fun r' hr' => ?_⟩
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact List.rel_of_pairwise_cons hp hr
    · exact hmax r' hr'

/-- The last emitted row of a run refines every output the run emitted. -/
theorem rows_max (m : PRun sp) (h : m.rows ≠ []) :
    ∃ r ∈ m.rows, ∀ r' ∈ m.rows, r'.2 ≼ r.2 :=
  pairwise_max m.rows h (rows_chain m)

/-- The silent run at `i`. -/
def silentRun (sp : Spec I O) (i : I) : PRun sp where
  init := i
  es := []
  fin := canon sp i
  exec := Exec.nil _

@[simp] theorem silentRun_rows (i : I) : (silentRun sp i).rows = [] := rfl

theorem emits_some {n : Nat} {F : Family sp n} {p : Fin n} {m : PRun sp}
    (hp : F p = some m) {r : I × O} : Emits F p r ↔ r ∈ m.rows := by
  constructor
  · rintro ⟨m', hm', hr⟩
    rw [hp] at hm'; cases hm'; exact hr
  · exact fun hr => ⟨m, hp, hr⟩

theorem emits_none {n : Nat} {F : Family sp n} {p : Fin n}
    (hp : F p = none) {r : I × O} : ¬ Emits F p r := by
  rintro ⟨m', hm', _⟩; rw [hp] at hm'; cases hm'

theorem emits_le {n : Nat} {F : Family sp n} {j : I} (hj : UB F j) {p : Fin n} {r : I × O}
    (h : Emits F p r) : sp.S r.1 r.2 ∧ r.1 ≼ j := by
  obtain ⟨m, hm, hr⟩ := h
  exact ⟨(m.rows_spec.2 r hr).1, PO.trans (m.rows_spec.2 r hr).2 (hj p m hm)⟩

end Chain

section SoleRows
variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {n : Nat}

/-- "Rows authorized only to `p` ... never form a separable family", made
precise: an authorized family all of whose emitted rows are authorized only
to `p` is separable only when `p` alone emits, and emits one distinct row. -/
theorem sole_rows_separable (Dp : Deployment sp n) (F : Family sp n)
    (hA : Authorized Dp F) (p : Fin n)
    (honly : ∀ q r, Emits F q r → ∀ q', Dp.A q' r.1 r.2 → q' = p)
    (comp : Fin n → Nat) (hs : Separable F comp) :
    ∃ r₀, ∀ q r, Emits F q r → q = p ∧ r = r₀ := by
  have hemit : ∀ q r, Emits F q r → q = p := fun q r h => honly q r h q (hA q r h)
  rcases hs with ⟨q, q', r, r', hq, hq', hne⟩ | ⟨r₀, _, _, _, hone, _, _⟩
  · exact absurd (by rw [hemit q r hq, hemit q' r' hq']) hne
  · exact ⟨r₀, fun q r h => ⟨hemit q r h, hone q r h⟩⟩

theorem sole_rows_two_not_separable (Dp : Deployment sp n) (F : Family sp n)
    (hA : Authorized Dp F) (p : Fin n)
    (honly : ∀ q r, Emits F q r → ∀ q', Dp.A q' r.1 r.2 → q' = p)
    {q q' : Fin n} {r r' : I × O} (h1 : Emits F q r) (h2 : Emits F q' r') (hne : r ≠ r')
    (comp : Fin n → Nat) : ¬ Separable F comp := by
  intro hs
  obtain ⟨r₀, h⟩ := sole_rows_separable Dp F hA p honly comp hs
  exact hne ((h q r h1).2.trans (h q' r' h2).2.symm)

/-- The sufficient condition stated after the leader example: if each
authorized row has an expansion at every expansion of its input, and every
finite set of authorized rows lacking a common expansion at some common
expansion of their inputs is authorized only to a single participant, then
the specification is monotone across partitions. -/
theorem monoAcross_of_sole_conflicts (Dp : Deployment sp n)
    (h1 : ∀ p i o, Dp.A p i o → ∀ j, i ≼ j → ∃ u, sp.S j u ∧ o ≼ u)
    (h2 : ∀ E : List (I × O), (∀ r ∈ E, ∃ p, Dp.A p r.1 r.2) → ∀ j, (∀ r ∈ E, r.1 ≼ j) →
      (¬ ∃ u, sp.S j u ∧ ∀ r ∈ E, r.2 ≼ u) →
      ∃ p, ∀ r ∈ E, ∀ q, Dp.A q r.1 r.2 → q = p) :
    MonoAcrossPartitions Dp := by
  intro comp _ F hA hs j hj
  apply Classical.byContradiction
  intro hno
  have hno' : ¬ ∃ u, sp.S j u ∧ ∀ r ∈ allRows F, r.2 ≼ u := by
    rintro ⟨u, hu, hall⟩
    exact hno ⟨u, hu, fun p r he => hall r ((mem_allRows F r).2 ⟨p, he⟩)⟩
  obtain ⟨p, hp⟩ := h2 (allRows F)
    (fun r hr => let ⟨q, hq⟩ := (mem_allRows F r).1 hr; ⟨q, hA q r hq⟩) j
    (fun r hr => let ⟨q, hq⟩ := (mem_allRows F r).1 hr; (emits_le hj hq).2) hno'
  obtain ⟨r₀, hr₀⟩ := sole_rows_separable Dp F hA p
    (fun q r he => hp r ((mem_allRows F r).2 ⟨q, he⟩)) comp hs
  -- a separable family emits at least one row
  have hex : ∃ q, Emits F q r₀ := by
    rcases hs with ⟨q, _, r, _, hq, _, _⟩ | ⟨r₁, q, _, hq, _, _, _⟩
    · exact ⟨q, (hr₀ q r hq).2 ▸ hq⟩
    · exact ⟨q, (hr₀ q r₁ hq).2 ▸ hq⟩
  obtain ⟨q, hq⟩ := hex
  obtain ⟨u, hu, hou⟩ := h1 q r₀.1 r₀.2 (hA q r₀ hq) j (emits_le hj hq).2
  exact hno ⟨u, hu, fun q' r he => (hr₀ q' r he).2 ▸ hou⟩

/-! ### Single-authority deployments -/

/-- Def. (single-authority): `A_q = ∅` for every participant `q` but `p₀`. -/
def SingleAuthority (Dp : Deployment sp n) (p₀ : Fin n) : Prop :=
  ∀ q, q ≠ p₀ → ∀ i o, ¬ Dp.A q i o

/-- "Every separable family is then one row emitted by the single authority
beside a silent participant." -/
theorem single_authority_shape (Dp : Deployment sp n) (p₀ : Fin n)
    (hSA : SingleAuthority Dp p₀) (F : Family sp n) (hA : Authorized Dp F)
    (comp : Fin n → Nat) (hs : Separable F comp) :
    ∃ r₀, (∀ q r, Emits F q r → q = p₀ ∧ r = r₀) ∧ Emits F p₀ r₀ ∧
      ∃ q, Silent F q ∧ comp q ≠ comp p₀ := by
  have hemit : ∀ q r, Emits F q r → q = p₀ := fun q r h =>
    Classical.byContradiction fun hq => hSA q hq _ _ (hA q r h)
  rcases hs with ⟨q, q', r, r', hq, hq', hne⟩ | ⟨r₀, p, q, hp, hone, hsil, hc⟩
  · exact absurd (by rw [hemit q r hq, hemit q' r' hq']) hne
  · have := hemit p r₀ hp; subst this
    exact ⟨r₀, fun q r h => ⟨hemit q r h, hone q r h⟩, hp, q, hsil, hc⟩

/-- Under a single-authority deployment (with at least two participants),
monotonicity across partitions says only that each authorized row has an
expansion at every expansion of its input. -/
theorem single_authority_iff (hn : 2 ≤ n) (Dp : Deployment sp n) (p₀ : Fin n)
    (hSA : SingleAuthority Dp p₀) :
    MonoAcrossPartitions Dp ↔ ∀ i o, Dp.A p₀ i o → ∀ j, i ≼ j → ∃ u, sp.S j u ∧ o ≼ u := by
  constructor
  · intro hM i o hio j hij
    have hS : sp.S i o := Dp.sub _ _ _ hio
    let q : Fin n := if p₀.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
    have hq : q ≠ p₀ := by
      intro h
      have := congrArg Fin.val h
      by_cases h0 : p₀.val = 0 <;> simp [q, h0] at this <;> omega
    let F : Family sp n := fun p =>
      if p = p₀ then some (oneShot sp i o hS) else if p = q then some (silentRun sp i) else none
    have hF0 : F p₀ = some (oneShot sp i o hS) := by simp [F]
    have hFq : F q = some (silentRun sp i) := by simp [F, hq]
    have hem : ∀ p r, Emits F p r → p = p₀ ∧ r = (i, o) := by
      rintro p r ⟨m, hm, hr⟩
      by_cases h1 : p = p₀
      · subst h1; rw [hF0] at hm; cases hm; simp at hr; exact ⟨rfl, hr⟩
      · by_cases h2 : p = q
        · subst h2; rw [hFq] at hm; cases hm; simp at hr
        · simp [F, h1, h2] at hm
    have hauth : Authorized Dp F := by
      intro p r he
      obtain ⟨rfl, rfl⟩ := hem p r he
      exact hio
    have hsep : Separable F (fun p => p.val) :=
      Or.inr ⟨(i, o), p₀, q, ⟨_, hF0, by simp⟩, fun p r he => (hem p r he).2,
        ⟨_, hFq, rfl⟩, fun h => hq (Fin.ext h)⟩
    have hub : UB F j := by
      intro p m hm
      by_cases h1 : p = p₀
      · subst h1; rw [hF0] at hm; cases hm; exact hij
      · by_cases h2 : p = q
        · subst h2; rw [hFq] at hm; cases hm; exact hij
        · simp [F, h1, h2] at hm
    obtain ⟨u, hu, hall⟩ := hM _ ⟨p₀, q, fun h => hq (Fin.ext h).symm⟩ F hauth hsep j hub
    exact ⟨u, hu, hall p₀ (i, o) ⟨_, hF0, by simp⟩⟩
  · intro h comp _ F hA hs j hj
    obtain ⟨r₀, hall, hp₀, _⟩ := single_authority_shape Dp p₀ hSA F hA comp hs
    obtain ⟨u, hu, hou⟩ := h r₀.1 r₀.2 (hA p₀ r₀ hp₀) j (emits_le hj hp₀).2
    exact ⟨u, hu, fun q r he => (hall q r he).2 ▸ hou⟩

end SoleRows

/-! ### The leader example -/

section Leader
variable {I : Type} [PO I]

open CC.Front (Disc)

/-- Every fiber is `{a, b}` (`false`, `true`), ordered by equality. -/
def leadSpec (I : Type) [PO I] : Spec I (Disc Bool) where
  S := fun _ _ => True
  total := fun _ => ⟨⟨false⟩, trivial⟩

/-- `A_p = S` for `p = 0`, `A_q = ∅` for `q = 1`. -/
def leadD (I : Type) [PO I] : Deployment (leadSpec I) 2 where
  A := fun p _ _ => p = 0
  sub := fun _ _ _ _ => trivial

theorem leadD_single : SingleAuthority (leadD I) 0 := fun q hq _ _ h => hq h

/-- The leader specification is monotone across partitions under `leadD`. -/
theorem lead_monoAcross : MonoAcrossPartitions (leadD I) :=
  (single_authority_iff (by decide) (leadD I) 0 leadD_single).2
    fun _ o _ j _ => ⟨o, trivial, PO.refl o⟩

/-- ... yet it is not monotone (`(i,a)` and `(i,b)` have no common
expansion), for any nonempty input poset. -/
theorem lead_not_liftedMono (i : I) : ¬ (leadSpec I).LiftedMono := by
  intro h
  obtain ⟨u, _, hall⟩ := h i i (PO.refl i) [⟨false⟩, ⟨true⟩] (by simp) (fun _ _ => trivial)
  have h1 : (⟨false⟩ : Disc Bool) = u := hall _ (by simp)
  have h2 : (⟨true⟩ : Disc Bool) = u := hall _ (by simp)
  have := h1.trans h2.symm
  cases this

/-- A run of `p` emits at most one distinct output. -/
theorem lead_run_one_output (m : PRun (leadSpec I)) :
    ∀ r ∈ m.rows, ∀ r' ∈ m.rows, r.2 = r'.2 := by
  intro r hr r' hr'
  have hne : m.rows ≠ [] := fun h => by rw [h] at hr; cases hr
  obtain ⟨t, _, ht⟩ := rows_max m hne
  exact (ht r hr).trans (ht r' hr').symm

/-- Every separable family consists of one row, emitted by `p`, beside a
silent `q`. -/
theorem lead_separable_shape (F : Family (leadSpec I) 2) (hA : Authorized (leadD I) F)
    (comp : Fin 2 → Nat) (hs : Separable F comp) :
    ∃ r₀, (∀ q r, Emits F q r → q = 0 ∧ r = r₀) ∧ Emits F 0 r₀ ∧ Silent F 1 := by
  obtain ⟨r₀, hall, h0, q, hq, hc⟩ := single_authority_shape (leadD I) 0 leadD_single F hA comp hs
  have : q = 1 := by
    have : q ≠ 0 := fun h => hc (by rw [h])
    apply Fin.ext
    have h2 := q.2
    have h3 : q.val ≠ 0 := fun h => this (Fin.ext h)
    show q.val = 1
    omega
  subst this
  exact ⟨r₀, hall, h0, hq⟩

end Leader
end Deploy
end CC
