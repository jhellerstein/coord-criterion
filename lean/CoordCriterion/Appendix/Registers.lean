import CoordCriterion.Appendix.ProductFrontier

/-!
# Registers (Appendix `app:registers`) and the causal-register frontier

The register examples of `appendices/deployment.tex` (subsection Registers)
and their frontier application in `appendices/frontiers.tex`:

* strict total orders on finite sets and linear extensions of finite strict
  partial orders (`STO`, `linExt`, `concat_sto`, `sto_max`);
* histories with causally closed sub-history order (`Hist`), source maps
  (`SMap`), serializations, the causal and linearizable fibers;
* the causal register is monotone across partitions under the replica
  deployment, at every history, without separability
  (`causal_monoAcross`, `causal_confluent`, `ser_extend`);
* the two-write history: linearizable is not monotone across `{{p},{q}}`
  (`lin_not_monoAcross`), the causal map (`causal_two_write`), causal is not
  monotone (`causal_not_liftedMono`);
* the frontier application: views form an antichain and continue
  (`cviews_antichain`, `cviews_cont`), part (1)
  (`causal_product_monoAcross`); linearizability is locally conservative and
  strict (`lin_locCons`, `lin_strict`), part (2)
  (`lin_product_not_monoAcross`);
* real-time precedence breaks local conservativity (`linRT_not_locCons`).
-/

namespace CC
namespace Deploy

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CC.CAP (step_input_inv step_output_inv)

/-! ## Part C: the causal register (Appendix `app:registers`) -/

/-! ### Strict total orders on finite sets -/

section Orders
variable {α : Type}

/-- `lt` is a strict total order on the set `M` (and relates only members). -/
structure STO (M : α → Prop) (lt : α → α → Prop) : Prop where
  dom : ∀ a b, lt a b → M a ∧ M b
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ {a b c}, lt a b → lt b c → lt a c
  total : ∀ a b, M a → M b → a ≠ b → lt a b ∨ lt b a

/-- `lt` extends `r` on `M`. -/
def Ext (r : α → α → Prop) (M : α → Prop) (lt : α → α → Prop) : Prop :=
  ∀ a b, M a → M b → r a b → lt a b

theorem STO.congr {M N : α → Prop} {lt : α → α → Prop} (h : STO M lt)
    (e : ∀ a, M a ↔ N a) : STO N lt :=
  ⟨fun a b hab => ⟨(e a).1 (h.dom a b hab).1, (e b).1 (h.dom a b hab).2⟩, h.irrefl, h.trans,
    fun a b ha hb => h.total a b ((e a).2 ha) ((e b).2 hb)⟩

/-- Insert a new element `x` into a linear extension. -/
theorem insert_sto (r : α → α → Prop) (hirr : ∀ a, ¬ r a a)
    (htr : ∀ a b c, r a b → r b c → r a c)
    {M : α → Prop} {lt : α → α → Prop} (h : STO M lt) (hE : Ext r M lt) (x : α) (hx : ¬ M x) :
    ∃ lt', STO (fun a => M a ∨ a = x) lt' ∧ Ext r (fun a => M a ∨ a = x) lt' := by
  classical
  let D : α → Prop := fun z => M z ∧ ∃ z', M z' ∧ r z' x ∧ (z = z' ∨ lt z z')
  have Ddown : ∀ a b, lt a b → D b → D a := by
    rintro a b hab ⟨_, z', hz', hr, hbz⟩
    refine ⟨(h.dom a b hab).1, z', hz', hr, Or.inr ?_⟩
    rcases hbz with e | hbz
    · exact e ▸ hab
    · exact h.trans hab hbz
  refine ⟨fun a b => lt a b ∨ (D a ∧ b = x) ∨ (a = x ∧ M b ∧ ¬ D b), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro a b (hab | ⟨hD, hb⟩ | ⟨ha, hb, _⟩)
    · exact ⟨Or.inl (h.dom a b hab).1, Or.inl (h.dom a b hab).2⟩
    · exact ⟨Or.inl hD.1, Or.inr hb⟩
    · exact ⟨Or.inr ha, Or.inl hb⟩
  · rintro a (haa | ⟨hD, ha⟩ | ⟨ha, hm, _⟩)
    · exact h.irrefl a haa
    · exact hx (ha ▸ hD.1)
    · exact hx (ha ▸ hm)
  · intro a b c hab hbc
    rcases hab with hab | ⟨hDa, hbx⟩ | ⟨hax, hb, hnb⟩ <;>
      rcases hbc with hbc | ⟨hDb, hcx⟩ | ⟨hbx', hc, hnc⟩
    · exact Or.inl (h.trans hab hbc)
    · exact Or.inr (Or.inl ⟨Ddown a b hab hDb, hcx⟩)
    · exact absurd (hbx' ▸ (h.dom a b hab).2) hx
    · exact absurd (hbx ▸ (h.dom b c hbc).1) hx
    · exact absurd (hbx ▸ hDb.1) hx
    · by_cases hac : a = c
      · exact absurd (hac ▸ hDa) hnc
      · rcases h.total a c hDa.1 hc hac with h1 | h1
        · exact Or.inl h1
        · exact absurd (Ddown c a h1 hDa) hnc
    · exact Or.inr (Or.inr ⟨hax, (h.dom b c hbc).2, fun hDc => hnb (Ddown b c hbc hDc)⟩)
    · exact absurd hDb hnb
    · exact absurd (hbx' ▸ hb) hx
  · intro a b ha hb hab
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rcases h.total a b ha hb hab with h1 | h1
      · exact Or.inl (Or.inl h1)
      · exact Or.inr (Or.inl h1)
    · by_cases hD : D a
      · exact Or.inl (Or.inr (Or.inl ⟨hD, hb⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hb, ha, hD⟩))
    · by_cases hD : D b
      · exact Or.inr (Or.inr (Or.inl ⟨hD, ha⟩))
      · exact Or.inl (Or.inr (Or.inr ⟨ha, hb, hD⟩))
    · exact absurd (ha.trans hb.symm) hab
  · intro a b ha hb hr
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (hE a b ha hb hr)
    · exact Or.inr (Or.inl ⟨⟨ha, a, ha, hb ▸ hr, Or.inl rfl⟩, hb⟩)
    · refine Or.inr (Or.inr ⟨ha, hb, ?_⟩)
      rintro ⟨_, z', hz', hzx, hbz⟩
      have hzb : r z' b := htr _ _ _ hzx (ha ▸ hr)
      rcases hbz with e | hbz
      · exact hirr b (e ▸ hzb)
      · exact h.irrefl b (h.trans hbz (hE z' b hz' hb hzb))
    · exact absurd (hb ▸ ha ▸ hr) (hirr _)

/-- Every strict partial order has a linear extension on every finite set. -/
theorem linExt (r : α → α → Prop) (hirr : ∀ a, ¬ r a a)
    (htr : ∀ a b c, r a b → r b c → r a c) :
    ∀ (l : List α) (M : α → Prop), (∀ a, M a → a ∈ l) → ∃ lt, STO M lt ∧ Ext r M lt
  | [], M, hc => ⟨fun _ _ => False,
      ⟨fun _ _ h => h.elim, fun _ h => h, fun h _ => h.elim,
        fun a _ ha _ _ => absurd (hc a ha) List.not_mem_nil⟩,
      fun a _ ha _ _ => absurd (hc a ha) List.not_mem_nil⟩
  | x :: l, M, hc => by
    classical
    obtain ⟨lt, hS, hE⟩ := linExt r hirr htr l (fun a => M a ∧ a ≠ x) (fun a ⟨ha, hne⟩ => by
      rcases List.mem_cons.1 (hc a ha) with h | h
      · exact absurd h hne
      · exact h)
    by_cases hMx : M x
    · obtain ⟨lt', hS', hE'⟩ := insert_sto r hirr htr hS hE x (fun h => h.2 rfl)
      have e : ∀ a, ((M a ∧ a ≠ x) ∨ a = x) ↔ M a := fun a =>
        ⟨fun h => h.elim And.left (fun h => h ▸ hMx),
          fun h => if hax : a = x then Or.inr hax else Or.inl ⟨h, hax⟩⟩
      exact ⟨lt', hS'.congr e, fun a b ha hb => hE' a b ((e a).2 ha) ((e b).2 hb)⟩
    · have e : ∀ a, (M a ∧ a ≠ x) ↔ M a := fun a =>
        ⟨And.left, fun h => ⟨h, fun hax => hMx (hax ▸ h)⟩⟩
      exact ⟨lt, hS.congr e, fun a b ha hb => hE a b ((e a).2 ha) ((e b).2 hb)⟩

/-- Appending a linear order on new elements after one on old elements. -/
theorem concat_sto {M₁ M₂ : α → Prop} {lt₁ lt₂ : α → α → Prop} (h₁ : STO M₁ lt₁)
    (h₂ : STO M₂ lt₂) (hdis : ∀ a, M₁ a → ¬ M₂ a) :
    STO (fun a => M₁ a ∨ M₂ a) (fun a b => lt₁ a b ∨ lt₂ a b ∨ (M₁ a ∧ M₂ b)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro a b (h | h | ⟨ha, hb⟩)
    · exact ⟨Or.inl (h₁.dom a b h).1, Or.inl (h₁.dom a b h).2⟩
    · exact ⟨Or.inr (h₂.dom a b h).1, Or.inr (h₂.dom a b h).2⟩
    · exact ⟨Or.inl ha, Or.inr hb⟩
  · rintro a (h | h | ⟨ha, hb⟩)
    · exact h₁.irrefl a h
    · exact h₂.irrefl a h
    · exact hdis a ha hb
  · intro a b c hab hbc
    rcases hab with hab | hab | ⟨ha, hb⟩ <;> rcases hbc with hbc | hbc | ⟨hb', hc⟩
    · exact Or.inl (h₁.trans hab hbc)
    · exact absurd (h₂.dom b c hbc).1 (hdis b (h₁.dom a b hab).2)
    · exact Or.inr (Or.inr ⟨(h₁.dom a b hab).1, hc⟩)
    · exact absurd (h₂.dom a b hab).2 (hdis b (h₁.dom b c hbc).1)
    · exact Or.inr (Or.inl (h₂.trans hab hbc))
    · exact absurd (h₂.dom a b hab).2 (hdis b hb')
    · exact absurd hb (hdis b (h₁.dom b c hbc).1)
    · exact Or.inr (Or.inr ⟨ha, (h₂.dom b c hbc).2⟩)
    · exact absurd hb (hdis b hb')
  · intro a b ha hb hab
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rcases h₁.total a b ha hb hab with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr (Or.inr ⟨ha, hb⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hb, ha⟩))
    · rcases h₂.total a b ha hb hab with h | h
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inl h))

/-- A finite nonempty subset of a strict total order has a maximum. -/
theorem sto_max {M : α → Prop} {lt : α → α → Prop} (hS : STO M lt) :
    ∀ (l : List α) (B : α → Prop), (∀ b, B b → M b) → (∀ b, B b → b ∈ l) → (∃ b, B b) →
      ∃ m, B m ∧ ∀ b, B b → b = m ∨ lt b m
  | [], B, _, hc, ⟨b, hb⟩ => absurd (hc b hb) List.not_mem_nil
  | x :: l, B, hM, hc, hne => by
    classical
    by_cases hrest : ∃ b, B b ∧ b ≠ x
    · obtain ⟨m, ⟨hm, hmx⟩, hmax⟩ := sto_max hS l (fun b => B b ∧ b ≠ x)
        (fun b h => hM b h.1)
        (fun b ⟨hb, hbx⟩ => by
          rcases List.mem_cons.1 (hc b hb) with h | h
          · exact absurd h hbx
          · exact h) hrest
      by_cases hBx : B x
      · rcases hS.total m x (hM m hm) (hM x hBx) hmx with hlt | hlt
        · refine ⟨x, hBx, fun b hb => ?_⟩
          by_cases hbx : b = x
          · exact Or.inl hbx
          · rcases hmax b ⟨hb, hbx⟩ with e | h
            · exact Or.inr (e ▸ hlt)
            · exact Or.inr (hS.trans h hlt)
        · refine ⟨m, hm, fun b hb => ?_⟩
          by_cases hbx : b = x
          · exact Or.inr (hbx ▸ hlt)
          · exact hmax b ⟨hb, hbx⟩
      · exact ⟨m, hm, fun b hb => hmax b ⟨hb, fun h => hBx (h ▸ hb)⟩⟩
    · obtain ⟨b, hb⟩ := hne
      have hbx : b = x := Classical.byContradiction fun h => hrest ⟨b, hb, h⟩
      refine ⟨b, hb, fun b' hb' => Or.inl ?_⟩
      have : b' = x := Classical.byContradiction fun h => hrest ⟨b', hb', h⟩
      rw [this, hbx]

end Orders

/-! ### Histories, source maps, serializations -/

section Causal
variable {α : Type} {n : Nat}

/-- A finite operation history: a finite set of operations with a strict
partial order `hb` of causal precedence. -/
structure Hist (α : Type) where
  mem : α → Prop
  hb : α → α → Prop
  fin : ∃ l : List α, ∀ a, mem a → a ∈ l
  hb_mem : ∀ a b, hb a b → mem a ∧ mem b
  irrefl : ∀ a, ¬ hb a a
  trans : ∀ a b c, hb a b → hb b c → hb a c

/-- `h ≼ h'`: the operations of `h` form a causally closed subset of `h'`,
and `hb'` restricted to them is `hb`. -/
instance : PO (Hist α) where
  le h h' := (∀ a, h.mem a → h'.mem a) ∧ (∀ a b, h'.hb a b → h.mem b → h.mem a) ∧
    (∀ a b, h.mem a → h.mem b → (h'.hb a b ↔ h.hb a b))
  refl h := ⟨fun _ x => x, fun a b hab _ => (h.hb_mem a b hab).1, fun _ _ _ _ => Iff.rfl⟩
  trans {h₁ h₂ h₃} h12 h23 :=
    ⟨fun a ha => h23.1 a (h12.1 a ha),
     fun a b hab hb => by
        have h2b := h12.1 b hb
        have h2a := h23.2.1 a b hab h2b
        exact h12.2.1 a b ((h23.2.2 a b h2a h2b).1 hab) hb,
     fun a b ha hb => (h23.2.2 a b (h12.1 a ha) (h12.1 b hb)).trans (h12.2.2 a b ha hb)⟩
  antisymm {h h'} h1 h2 := by
    have em : h.mem = h'.mem := funext fun a => propext ⟨h1.1 a, h2.1 a⟩
    have eh : h.hb = h'.hb := funext fun a => funext fun b => propext
      ⟨fun hab => (h1.2.2 a b (h.hb_mem a b hab).1 (h.hb_mem a b hab).2).2 hab,
       fun hab => (h2.2.2 a b (h'.hb_mem a b hab).1 (h'.hb_mem a b hab).2).2 hab⟩
    cases h; cases h'; simp only at em eh; subst em; subst eh; rfl

/-- "An expansion never adds an operation to the causal past of an existing
one." -/
theorem no_new_past {h h' : Hist α} (hle : h ≼ h') {a b : α} (hab : h'.hb a b)
    (hb : h.mem b) : h.mem a := hle.2.1 a b hab hb

/-- Source maps: `f r = none` (undefined), `some none` (`v₀`), `some (some w)`. -/
structure SMap (α : Type) where
  f : α → Option (Option α)

/-- Source maps ordered by extension. -/
instance : PO (SMap α) where
  le ρ ρ' := ∀ r s, ρ.f r = some s → ρ'.f r = some s
  refl _ _ _ h := h
  trans h1 h2 r s h := h2 r s (h1 r s h)
  antisymm {ρ ρ'} h1 h2 := by
    have : ρ.f = ρ'.f := by
      funext r
      cases e : ρ.f r with
      | none =>
        cases e' : ρ'.f r with
        | none => rfl
        | some s => have := h2 r s e'; rw [e] at this; cases this
      | some s => exact (h1 r s e).symm
    cases ρ; cases ρ'; simp only at this; subst this; rfl

/-- Operation attributes: replica and kind (`isW = true` for writes). -/
structure OpSig (α : Type) (n : Nat) where
  rep : α → Fin n
  isW : α → Bool

variable (G : OpSig α n)

/-- The operations a serialization for replica `p` orders: `p`'s operations
and all writes. -/
def Dom (h : Hist α) (p : Fin n) (a : α) : Prop := h.mem a ∧ (G.rep a = p ∨ G.isW a = true)

/-- A serialization for `p`: a total order of `Dom h p` extending `→`. -/
def Ser (h : Hist α) (p : Fin n) (lt : α → α → Prop) : Prop :=
  STO (Dom G h p) lt ∧ Ext h.hb (Dom G h p) lt

/-- `lt` explains read `r` with source `s`. -/
def Explains (h : Hist α) (lt : α → α → Prop) (r : α) : Option α → Prop
  | none => ∀ w, h.mem w → G.isW w = true → ¬ lt w r
  | some w => h.mem w ∧ G.isW w = true ∧ lt w r ∧
      ∀ w', h.mem w' → G.isW w' = true → lt w' r → w' = w ∨ lt w' w

/-- A source map of `h`: defined on reads of `h`, valued in writes of `h`. -/
def WellDom (h : Hist α) (ρ : SMap α) : Prop :=
  ∀ r s, ρ.f r = some s → h.mem r ∧ G.isW r = false ∧ ∀ w, s = some w → h.mem w ∧ G.isW w = true

/-- Causal consistency: each replica has a serialization explaining every
read of that replica in the domain. -/
def CausalFib (h : Hist α) (ρ : SMap α) : Prop :=
  WellDom G h ρ ∧ ∀ p, ∃ lt, Ser G h p lt ∧ ∀ r s, ρ.f r = some s → G.rep r = p →
    Explains G h lt r s

/-- Linearizability: one total order of all operations, extending `→`,
explains every read in the domain. -/
def LinFib (h : Hist α) (ρ : SMap α) : Prop :=
  WellDom G h ρ ∧ ∃ lt, STO h.mem lt ∧ Ext h.hb h.mem lt ∧ ∀ r s, ρ.f r = some s →
    Explains G h lt r s

theorem ser_exists (h : Hist α) (p : Fin n) : ∃ lt, Ser G h p lt := by
  obtain ⟨l, hl⟩ := h.fin
  exact linExt h.hb h.irrefl h.trans l (Dom G h p) (fun a ha => hl a ha.1)

theorem lin_exists (h : Hist α) : ∃ lt, STO h.mem lt ∧ Ext h.hb h.mem lt := by
  obtain ⟨l, hl⟩ := h.fin
  exact linExt h.hb h.irrefl h.trans l h.mem hl

def emptyMap : SMap α := ⟨fun _ => none⟩

theorem empty_wellDom (h : Hist α) : WellDom G h emptyMap := fun _ _ e => by cases e

theorem empty_causal (h : Hist α) : CausalFib G h emptyMap :=
  ⟨empty_wellDom G h, fun p =>
    let ⟨lt, hs⟩ := ser_exists G h p; ⟨lt, hs, fun _ _ e => by cases e⟩⟩

/-- The causal register. -/
def causalSpec : Spec (Hist α) (SMap α) where
  S := CausalFib G
  total h := ⟨emptyMap, empty_causal G h⟩

/-- The linearizable register. -/
def linSpec : Spec (Hist α) (SMap α) where
  S := LinFib G
  total h := ⟨emptyMap, empty_wellDom G h,
    let ⟨lt, hs, he⟩ := lin_exists h; ⟨lt, hs, he, fun _ _ e => by cases e⟩⟩

/-- Extending a serialization of `h` to an expansion `j` by appending the new
operations in an order extending `→`: the result is a serialization of `j`
and explains the same reads. -/
theorem ser_extend {h j : Hist α} (hle : h ≼ j) {p : Fin n} {lt : α → α → Prop}
    (hs : Ser G h p lt) :
    ∃ lt', Ser G j p lt' ∧ ∀ r s, Dom G h p r → Explains G h lt r s → Explains G j lt' r s := by
  classical
  let M₂ : α → Prop := fun a => Dom G j p a ∧ ¬ h.mem a
  obtain ⟨l, hl⟩ := j.fin
  obtain ⟨lt₂, hS₂, hE₂⟩ := linExt j.hb j.irrefl j.trans l M₂ (fun a ha => hl a ha.1.1)
  have hdis : ∀ a, Dom G h p a → ¬ M₂ a := fun a ha h2 => h2.2 ha.1
  have hS := concat_sto hs.1 hS₂ hdis
  have e : ∀ a, (Dom G h p a ∨ M₂ a) ↔ Dom G j p a := by
    intro a
    constructor
    · rintro (⟨hm, hk⟩ | ⟨hd, _⟩)
      · exact ⟨hle.1 a hm, hk⟩
      · exact hd
    · intro hd
      by_cases hm : h.mem a
      · exact Or.inl ⟨hm, hd.2⟩
      · exact Or.inr ⟨hd, hm⟩
  let lt' := fun a b => lt a b ∨ lt₂ a b ∨ (Dom G h p a ∧ M₂ b)
  -- nothing new precedes an old operation
  have old : ∀ a r, Dom G h p r → lt' a r → lt a r := by
    intro a r hr h'
    rcases h' with h' | h' | ⟨_, h2⟩
    · exact h'
    · exact absurd (hS₂.dom a r h').2 (hdis r hr)
    · exact absurd h2 (hdis r hr)
  refine ⟨lt', ⟨hS.congr e, ?_⟩, ?_⟩
  · intro a b ha hb hab
    rcases (e a).2 ha with ha' | ha' <;> rcases (e b).2 hb with hb' | hb'
    · exact Or.inl (hs.2 a b ha' hb' ((hle.2.2 a b ha'.1 hb'.1).1 hab))
    · exact Or.inr (Or.inr ⟨ha', hb'⟩)
    · exact absurd (hle.2.1 a b hab hb'.1) ha'.2
    · exact Or.inr (Or.inl (hE₂ a b ha' hb' hab))
  · intro r s hr hex
    cases s with
    | none =>
      intro w hw hwW hlt
      have h1 := old w r hr hlt
      exact hex w (hs.1.dom w r h1).1.1 hwW h1
    | some w =>
      obtain ⟨hw, hwW, hlt, hmax⟩ := hex
      refine ⟨hle.1 w hw, hwW, Or.inl hlt, fun w' _ hw'W hlt' => ?_⟩
      have h1 := old w' r hr hlt'
      rcases hmax w' (hs.1.dom w' r h1).1.1 hw'W h1 with e | h2
      · exact Or.inl e
      · exact Or.inr (Or.inl h2)

/-- The replica deployment: each replica answers only its own reads. -/
def replicaD : Deployment (causalSpec G) n where
  A p h ρ := CausalFib G h ρ ∧ ∀ r s, ρ.f r = some s → G.rep r = p
  sub _ _ _ h := h.1

/-- Every replica-authorized family of causal-register runs (separable or
not) has a common expansion at every common expansion of its current
inputs. -/
theorem causal_common (F : Family (causalSpec G) n) (hA : Authorized (replicaD G) F)
    (j : Hist α) (hj : UB F j) :
    ∃ u, CausalFib G j u ∧ ∀ p r, Emits F p r → r.2 ≼ u := by
  have key : ∀ p, ∃ (i : Hist α) (ρ : SMap α), i ≼ j ∧ CausalFib G i ρ ∧
      (∀ r s, ρ.f r = some s → G.rep r = p) ∧ ∀ r, Emits F p r → r.2 ≼ ρ := by
    intro p
    cases hp : F p with
    | none =>
      exact ⟨j, emptyMap, PO.refl j, empty_causal G j, fun _ _ e => (by cases e),
        fun r hr => absurd hr (emits_none hp)⟩
    | some m =>
      by_cases hnil : m.rows = []
      · exact ⟨j, emptyMap, PO.refl j, empty_causal G j, fun _ _ e => (by cases e),
          fun r hr => (by rw [emits_some hp, hnil] at hr; cases hr)⟩
      · obtain ⟨t, ht, hmax⟩ := rows_max m hnil
        obtain ⟨hfib, hdom⟩ := hA p t ⟨m, hp, ht⟩
        exact ⟨t.1, t.2, PO.trans (m.rows_spec.2 t ht).2 (hj p m hp), hfib, hdom,
          fun r hr => hmax r ((emits_some hp).1 hr)⟩
  let is : Fin n → Hist α := fun p => Classical.choose (key p)
  let ρs : Fin n → SMap α := fun p => Classical.choose (Classical.choose_spec (key p))
  have hk : ∀ p, is p ≼ j ∧ CausalFib G (is p) (ρs p) ∧
      (∀ r s, (ρs p).f r = some s → G.rep r = p) ∧ ∀ r, Emits F p r → r.2 ≼ ρs p :=
    fun p => Classical.choose_spec (Classical.choose_spec (key p))
  let u : SMap α := ⟨fun r => (ρs (G.rep r)).f r⟩
  have hu : ∀ p, ρs p ≼ u := by
    intro p r s e
    show (ρs (G.rep r)).f r = some s
    rw [(hk p).2.2.1 r s e]; exact e
  refine ⟨u, ⟨?_, ?_⟩, fun p r he => PO.trans ((hk p).2.2.2 r he) (hu p)⟩
  · intro r s e
    obtain ⟨h1, h2, h3⟩ := (hk (G.rep r)).2.1.1 r s e
    exact ⟨(hk (G.rep r)).1.1 r h1, h2, fun w hw =>
      ⟨(hk (G.rep r)).1.1 w (h3 w hw).1, (h3 w hw).2⟩⟩
  · intro p
    obtain ⟨lt, hser, hex⟩ := (hk p).2.1.2 p
    obtain ⟨lt', hser', hpres⟩ := ser_extend G (hk p).1 hser
    refine ⟨lt', hser', fun r s e hrp => ?_⟩
    have e' : (ρs p).f r = some s := by
      have : (ρs (G.rep r)).f r = some s := e
      rw [hrp] at this; exact this
    exact hpres r s ⟨((hk p).2.1.1 r s e').1, Or.inl hrp⟩ (hex r s e' hrp)

/-- **Appendix `app:registers`**: under the deployment in which each replica
answers only its own reads, the causal register is monotone across
partitions, for every history (separability is not used). -/
theorem causal_monoAcross : MonoAcrossPartitions (replicaD G) :=
  fun _ _ F hA _ j hj => causal_common G F hA j hj

theorem causal_confluent : PartitionConfluent (replicaD G) :=
  (partition_compatibility_confluent _).2 (causal_monoAcross G)

/-! ### Explanation: existence and uniqueness of sources -/

theorem exists_src {h : Hist α} {p : Fin n} {lt : α → α → Prop} (hs : STO (Dom G h p) lt)
    {r : α} (hr : Dom G h p r) : ∃ s, Explains G h lt r s := by
  classical
  obtain ⟨l, hl⟩ := h.fin
  by_cases hne : ∃ w, h.mem w ∧ G.isW w = true ∧ lt w r
  · obtain ⟨m, ⟨hm, hmW, hmr⟩, hmax⟩ := sto_max hs l
      (fun w => h.mem w ∧ G.isW w = true ∧ lt w r) (fun w hw => ⟨hw.1, Or.inr hw.2.1⟩)
      (fun w hw => hl w hw.1) hne
    exact ⟨some m, hm, hmW, hmr, fun w' h1 h2 h3 => hmax w' ⟨h1, h2, h3⟩⟩
  · exact ⟨none, fun w h1 h2 h3 => hne ⟨w, h1, h2, h3⟩⟩

theorem explains_unique {h : Hist α} {M : α → Prop} {lt : α → α → Prop} (hs : STO M lt)
    {r : α} {s s' : Option α} (h1 : Explains G h lt r s) (h2 : Explains G h lt r s') :
    s = s' := by
  cases s with
  | none =>
    cases s' with
    | none => rfl
    | some w => exact absurd h2.2.2.1 (h1 w h2.1 h2.2.1)
  | some w =>
    cases s' with
    | none => exact absurd h1.2.2.1 (h2 w h1.1 h1.2.1)
    | some w' =>
      rcases h1.2.2.2 w' h2.1 h2.2.1 h2.2.2.1 with e | l1
      · rw [e]
      · rcases h2.2.2.2 w h1.1 h1.2.1 h1.2.2.1 with e | l2
        · rw [e]
        · exact absurd (hs.trans l1 l2) (hs.irrefl _)

/-- Explanation depends on `lt` only between writes and the read. -/
theorem explains_congr {h : Hist α} {T₁ T₂ : α → α → Prop} {r : α} {s : Option α}
    (hrel : ∀ a b, h.mem a → G.isW a = true → (b = r ∨ (h.mem b ∧ G.isW b = true)) →
      (T₁ a b ↔ T₂ a b))
    (hx : Explains G h T₁ r s) : Explains G h T₂ r s := by
  cases s with
  | none => exact fun w hw hW hlt => hx w hw hW ((hrel w r hw hW (Or.inl rfl)).2 hlt)
  | some w =>
    obtain ⟨hw, hW, hlt, hmax⟩ := hx
    refine ⟨hw, hW, (hrel w r hw hW (Or.inl rfl)).1 hlt, fun w' h1 h2 h3 => ?_⟩
    rcases hmax w' h1 h2 ((hrel w' r h1 h2 (Or.inl rfl)).2 h3) with e | l
    · exact Or.inl e
    · exact Or.inr ((hrel w' w h1 h2 (Or.inr ⟨hw, hW⟩)).1 l)

/-! ### The frontier application (Appendix `sec:frontiers`, Causal register) -/

/-- `p` reads `r` in `h`. -/
def PRead (h : Hist α) (p : Fin n) (r : α) : Prop :=
  h.mem r ∧ G.isW r = false ∧ G.rep r = p

/-- `V_p(h)`: maps from the reads of replica `p` in `h` that some
serialization for `p` explains. -/
def CView (p : Fin n) (h : Hist α) (v : SMap α) : Prop :=
  (∀ r, (∃ s, v.f r = some s) ↔ PRead G h p r) ∧
    ∃ lt, Ser G h p lt ∧ ∀ r s, v.f r = some s → Explains G h lt r s

/-- Every serialization explains a full view. -/
theorem full_view {h : Hist α} {p : Fin n} {lt : α → α → Prop} (hs : STO (Dom G h p) lt) :
    ∃ v : SMap α, (∀ r, (∃ s, v.f r = some s) ↔ PRead G h p r) ∧
      ∀ r s, v.f r = some s → Explains G h lt r s := by
  classical
  have src : ∀ r, PRead G h p r → ∃ s, Explains G h lt r s :=
    fun r hr => exists_src G hs ⟨hr.1, Or.inl hr.2.2⟩
  refine ⟨⟨fun r => if hr : PRead G h p r then some (Classical.choose (src r hr)) else none⟩,
    fun r => ?_, fun r s e => ?_⟩
  · by_cases hr : PRead G h p r
    · simp [hr]
    · simp [hr]
  · by_cases hr : PRead G h p r
    · simp [hr] at e; rw [← e]; exact Classical.choose_spec (src r hr)
    · simp [hr] at e

theorem cviews_antichain : Antichain (W := fun _ => SMap α) (CView G) := by
  intro p h v w hv hw hvw
  apply PO.antisymm hvw
  intro r s e
  obtain ⟨s', e'⟩ := (hv.1 r).2 ((hw.1 r).1 ⟨s, e⟩)
  obtain ⟨lt, hser, hex⟩ := hw.2
  have := explains_unique G hser.1 (hex r s e) (hex r s' (hvw r s' e'))
  rw [this]; exact e'

theorem cviews_ne : ∀ (p : Fin n) (h : Hist α), ∃ v, CView G p h v := by
  intro p h
  obtain ⟨lt, hser⟩ := ser_exists G h p
  obtain ⟨v, hd, hx⟩ := full_view G hser.1
  exact ⟨v, hd, lt, hser, hx⟩

/-- "Views continue by the argument given there." -/
theorem cviews_cont : Continue (W := fun _ => SMap α) (CView G) := by
  intro p h j v hle ⟨hd, lt, hser, hx⟩
  obtain ⟨lt', hser', hpres⟩ := ser_extend G hle hser
  obtain ⟨w, hdw, hxw⟩ := full_view G hser'.1
  refine ⟨w, ⟨hdw, lt', hser', hxw⟩, fun r s e => ?_⟩
  have hr : PRead G h p r := (hd r).1 ⟨s, e⟩
  have hxj := hpres r s ⟨hr.1, Or.inl hr.2.2⟩ (hx r s e)
  obtain ⟨s', e'⟩ := (hdw r).2 ⟨hle.1 r hr.1, hr.2⟩
  have := explains_unique G hser'.1 hxj (hxw r s' e')
  rw [this]; exact e'

/-- Part (1) applies: the causal product interface is monotone across
partitions under its owner deployment. -/
theorem causal_product_monoAcross :
    MonoAcrossPartitions (ownerD (prodSpec (W := fun _ => SMap α) (CView G) (cviews_ne G))) :=
  product_monoAcross _ (cviews_ne G) (cviews_cont G)

/-- Linearizability as a normalized strengthening: tuples of views that a
single total order of all operations, extending `→`, explains. -/
def linNS : NormStr (W := fun _ => SMap α) (CView G) where
  sel h y := (∀ p, CView G p h (y p)) ∧ ∃ T, STO h.mem T ∧ Ext h.hb h.mem T ∧
    ∀ p r s, (y p).f r = some s → Explains G h T r s
  sub _ _ hs := hs.1

/-- A linearization restricted to `Dom h q` is a serialization for `q`, and
explains a full view of `q`. -/
theorem lin_view {h : Hist α} {T : α → α → Prop} (hT : STO h.mem T) (hE : Ext h.hb h.mem T)
    (q : Fin n) : ∃ v, CView G q h v ∧ ∀ r s, v.f r = some s → Explains G h T r s := by
  let Tq : α → α → Prop := fun a b => T a b ∧ Dom G h q a ∧ Dom G h q b
  have hS : STO (Dom G h q) Tq :=
    ⟨fun a b h => h.2, fun a h => hT.irrefl a h.1,
     fun h1 h2 => ⟨hT.trans h1.1 h2.1, h1.2.1, h2.2.2⟩,
     fun a b ha hb hab => (hT.total a b ha.1 hb.1 hab).elim
       (fun h => Or.inl ⟨h, ha, hb⟩) (fun h => Or.inr ⟨h, hb, ha⟩)⟩
  have hSer : Ser G h q Tq := ⟨hS, fun a b ha hb hab => ⟨hE a b ha.1 hb.1 hab, ha, hb⟩⟩
  obtain ⟨v, hd, hx⟩ := full_view G hS
  refine ⟨v, ⟨hd, Tq, hSer, hx⟩, fun r s e => ?_⟩
  have hr := (hd r).1 ⟨s, e⟩
  refine explains_congr G (fun a b ha hW hb => ?_) (hx r s e)
  have hDa : Dom G h q a := ⟨ha, Or.inr hW⟩
  have hDb : Dom G h q b := by
    rcases hb with rfl | ⟨hb, hbW⟩
    · exact ⟨hr.1, Or.inl hr.2.2⟩
    · exact ⟨hb, Or.inr hbW⟩
  exact ⟨fun h => h.1, fun h => ⟨h, hDa, hDb⟩⟩

/-- The linearizable product specification. -/
def linSpecP : Spec (Hist α) (PTd (fun _ : Fin n => SMap α)) where
  S := (linNS G).table
  total h := by
    obtain ⟨T, hT, hE⟩ := lin_exists h
    have hv := fun q => lin_view G hT hE q
    refine ⟨⟨fun _ => none⟩, fun q => Classical.choose (hv q),
      ⟨fun q => (Classical.choose_spec (hv q)).1, T, hT, hE,
        fun q r s e => (Classical.choose_spec (hv q)).2 r s e⟩, fun _ => Or.inl rfl⟩

theorem chain2 {h : Hist α} {u v w : α} (h1 : u = v ∨ h.hb u v) (h2 : v = w ∨ h.hb v w) :
    u = w ∨ h.hb u w := by
  rcases h1 with rfl | h1
  · exact h2
  · rcases h2 with rfl | h2
    · exact Or.inr h1
    · exact Or.inr (h.trans _ _ _ h1 h2)

/-- **Linearizability is locally conservative**: every view of `p` is the
`p`-coordinate of some linearizable tuple. -/
theorem lin_locCons : (linNS G).LocCons := by
  classical
  intro h p v ⟨hd, L, hL, hx⟩
  let c : α → α → Prop := fun a b => h.hb a b ∨ ∃ x y, Dom G h p x ∧ Dom G h p y ∧
    (a = x ∨ h.hb a x) ∧ L x y ∧ (y = b ∨ h.hb y b)
  have link : ∀ {x y}, Dom G h p x → Dom G h p y → (x = y ∨ h.hb x y) → (x = y ∨ L x y) :=
    fun hx hy e => e.elim Or.inl (fun e => Or.inr (hL.2 _ _ hx hy e))
  have cirr : ∀ a, ¬ c a a := by
    rintro a (h1 | ⟨x, y, hx, hy, h1, hxy, h2⟩)
    · exact h.irrefl a h1
    · rcases link hy hx (chain2 h2 h1) with rfl | hyx
      · exact hL.1.irrefl _ hxy
      · exact hL.1.irrefl _ (hL.1.trans hxy hyx)
  have ctr : ∀ a b d, c a b → c b d → c a d := by
    intro a b d hab hbd
    rcases hab with hab | ⟨x, y, hx, hy, h1, hxy, h2⟩ <;>
      rcases hbd with hbd | ⟨x', y', hx', hy', h1', hxy', h2'⟩
    · exact Or.inl (h.trans _ _ _ hab hbd)
    · exact Or.inr ⟨x', y', hx', hy', chain2 (Or.inr hab) h1', hxy', h2'⟩
    · exact Or.inr ⟨x, y, hx, hy, h1, hxy, chain2 h2 (Or.inr hbd)⟩
    · refine Or.inr ⟨x, y', hx, hy', h1, ?_, h2'⟩
      rcases link hy hx' (chain2 h2 h1') with rfl | hyx'
      · exact hL.1.trans hxy hxy'
      · exact hL.1.trans (hL.1.trans hxy hyx') hxy'
  obtain ⟨l, hl⟩ := h.fin
  obtain ⟨T, hT, hTE⟩ := linExt c cirr ctr l h.mem hl
  have hE : Ext h.hb h.mem T := fun a b ha hb hab => hTE a b ha hb (Or.inl hab)
  have hLT : ∀ a b, Dom G h p a → Dom G h p b → L a b → T a b := fun a b ha hb hab =>
    hTE a b ha.1 hb.1 (Or.inr ⟨a, b, ha, hb, Or.inl rfl, hab, Or.inl rfl⟩)
  have hTL : ∀ a b, Dom G h p a → Dom G h p b → T a b → L a b := by
    intro a b ha hb hab
    by_cases e : a = b
    · subst e; exact absurd hab (hT.irrefl _)
    · rcases hL.1.total a b ha hb e with h1 | h1
      · exact h1
      · exact absurd (hT.trans hab (hLT b a hb ha h1)) (hT.irrefl _)
  have hvT : ∀ r s, v.f r = some s → Explains G h T r s := by
    intro r s e
    have hr := (hd r).1 ⟨s, e⟩
    refine explains_congr G (fun a b ha hW hb => ?_) (hx r s e)
    have hDa : Dom G h p a := ⟨ha, Or.inr hW⟩
    have hDb : Dom G h p b := by
      rcases hb with rfl | ⟨hb, hbW⟩
      · exact ⟨hr.1, Or.inl hr.2.2⟩
      · exact ⟨hb, Or.inr hbW⟩
    exact ⟨hLT a b hDa hDb, hTL a b hDa hDb⟩
  have hv := fun q => lin_view G hT hE q
  let z : (q : Fin n) → SMap α := fun q => if q = p then v else Classical.choose (hv q)
  refine ⟨z, ⟨fun q => ?_, T, hT, hE, fun q r s e => ?_⟩, by simp [z]⟩
  · by_cases hq : q = p
    · subst hq; simp only [z, ite_true]; exact ⟨hd, L, hL, hx⟩
    · simp only [z, hq, ite_false]; exact (Classical.choose_spec (hv q)).1
  · by_cases hq : q = p
    · subst hq; simp only [z, ite_true] at e; exact hvT r s e
    · simp only [z, hq, ite_false] at e; exact (Classical.choose_spec (hv q)).2 r s e

end Causal

/-! ### The two-write history -/

section TwoWrite

/-- Operations `0 = w_p(x,dog)`, `1 = w_q(x,cat)`, `2 = r_p`, `3 = r_q`;
replicas `p = 0`, `q = 1`. -/
def G2 : OpSig (Fin 4) 2 := ⟨fun a => ⟨a.val % 2, Nat.mod_lt _ (by decide)⟩, fun a => decide (a.val < 2)⟩

/-- Both writes causally precede both reads; the writes are concurrent. -/
def h2 : Hist (Fin 4) where
  mem _ := True
  hb a b := a.val < 2 ∧ 2 ≤ b.val
  fin := ⟨List.finRange 4, fun a _ => List.mem_finRange a⟩
  hb_mem _ _ _ := ⟨trivial, trivial⟩
  irrefl a h := by omega
  trans a b c h1 h2 := by omega

theorem h2_shape : h2.hb 0 2 ∧ h2.hb 0 3 ∧ h2.hb 1 2 ∧ h2.hb 1 3 ∧ ¬ h2.hb 0 1 ∧ ¬ h2.hb 1 0 := by
  show ((0 : Fin 4).val < 2 ∧ 2 ≤ (2 : Fin 4).val) ∧ ((0 : Fin 4).val < 2 ∧ 2 ≤ (3 : Fin 4).val) ∧
    ((1 : Fin 4).val < 2 ∧ 2 ≤ (2 : Fin 4).val) ∧ ((1 : Fin 4).val < 2 ∧ 2 ≤ (3 : Fin 4).val) ∧
    ¬ ((0 : Fin 4).val < 2 ∧ 2 ≤ (1 : Fin 4).val) ∧ ¬ ((1 : Fin 4).val < 2 ∧ 2 ≤ (0 : Fin 4).val)
  decide

/-- Rank orders on a decidable subset of `Fin 4`. -/
abbrev rkLt (P : Fin 4 → Bool) (rk : Fin 4 → Nat) : Fin 4 → Fin 4 → Prop :=
  fun a b => P a = true ∧ P b = true ∧ rk a < rk b

theorem rk_sto (P : Fin 4 → Bool) (rk : Fin 4 → Nat)
    (hinj : ∀ a b, P a = true → P b = true → rk a = rk b → a = b) :
    STO (fun a => P a = true) (rkLt P rk) := by
  refine ⟨fun a b h => ⟨h.1, h.2.1⟩, fun a h => Nat.lt_irrefl _ h.2.2,
    fun h1 h2 => ⟨h1.1, h2.2.1, Nat.lt_trans h1.2.2 h2.2.2⟩, fun a b ha hb hab => ?_⟩
  rcases Nat.lt_trichotomy (rk a) (rk b) with h | h | h
  · exact Or.inl ⟨ha, hb, h⟩
  · exact absurd (hinj a b ha hb h) hab
  · exact Or.inr ⟨hb, ha, h⟩

/-- Build a serialization of `h2` for replica `p` from a rank order. -/
theorem rk_ser (p : Fin 2) (P : Fin 4 → Bool) (rk : Fin 4 → Nat)
    (hP : ∀ a, P a = true ↔ (G2.rep a = p ∨ G2.isW a = true))
    (hinj : ∀ a b, P a = true → P b = true → rk a = rk b → a = b)
    (hext : ∀ a b, P a = true → P b = true → a.val < 2 → 2 ≤ b.val → rk a < rk b) :
    Ser G2 h2 p (rkLt P rk) := by
  have e : ∀ a, P a = true ↔ Dom G2 h2 p a := fun a =>
    ⟨fun h => ⟨trivial, (hP a).1 h⟩, fun h => (hP a).2 h.2⟩
  refine ⟨(rk_sto P rk hinj).congr e, fun a b ha hb hab => ?_⟩
  exact ⟨(e a).2 ha, (e b).2 hb, hext a b ((e a).2 ha) ((e b).2 hb) hab.1 hab.2⟩

/-- `r_p ↦ w_q`. -/
def ρ1 : SMap (Fin 4) := ⟨fun r => if r = 2 then some (some 1) else none⟩
/-- `r_q ↦ w_p`. -/
def ρ2 : SMap (Fin 4) := ⟨fun r => if r = 3 then some (some 0) else none⟩
/-- `r_p ↦ w_q`, `r_q ↦ w_p`. -/
def ρ12 : SMap (Fin 4) := ⟨fun r => if r = 2 then some (some 1) else if r = 3 then some (some 0) else none⟩
/-- `r_p ↦ w_p`. -/
def ρa : SMap (Fin 4) := ⟨fun r => if r = 2 then some (some 0) else none⟩

/-- Replica `p`'s order `w_p < w_q < r_p` explains `r_p ↦ w_q`. -/
def P0 : Fin 4 → Bool := fun a => a.val != 3
def rk01 : Fin 4 → Nat := fun a => a.val
/-- Replica `p`'s order `w_q < w_p < r_p` explains `r_p ↦ w_p`. -/
def rk10 : Fin 4 → Nat := fun a => if a.val = 0 then 1 else if a.val = 1 then 0 else a.val
/-- Replica `q`'s order `w_q < w_p < r_q` explains `r_q ↦ w_p`. -/
def P1 : Fin 4 → Bool := fun a => a.val != 2

theorem ser0_01 : Ser G2 h2 0 (rkLt P0 rk01) :=
  rk_ser 0 P0 rk01 (by decide) (by decide) (by decide)
theorem ser0_10 : Ser G2 h2 0 (rkLt P0 rk10) :=
  rk_ser 0 P0 rk10 (by decide) (by decide) (by decide)
theorem ser1_10 : Ser G2 h2 1 (rkLt P1 rk10) :=
  rk_ser 1 P1 rk10 (by decide) (by decide) (by decide)

/-- Explanation on `h2` reduces to a decidable statement. -/
theorem ex_h2 {lt : Fin 4 → Fin 4 → Prop} {r w : Fin 4} (hw : G2.isW w = true) (hlt : lt w r)
    (hmax : ∀ w', G2.isW w' = true → lt w' r → w' = w ∨ lt w' w) :
    Explains G2 h2 lt r (some w) :=
  ⟨trivial, hw, hlt, fun w' _ hW h => hmax w' hW h⟩

theorem ex_rp_wq : Explains G2 h2 (rkLt P0 rk01) 2 (some 1) :=
  ex_h2 rfl (by decide) (by decide)
theorem ex_rp_wp : Explains G2 h2 (rkLt P0 rk10) 2 (some 0) :=
  ex_h2 rfl (by decide) (by decide)
theorem ex_rq_wp : Explains G2 h2 (rkLt P1 rk10) 3 (some 0) :=
  ex_h2 rfl (by decide) (by decide)

theorem wd_of (ρ : SMap (Fin 4))
    (h : ∀ r s, ρ.f r = some s → G2.isW r = false ∧ ∀ w, s = some w → G2.isW w = true) :
    WellDom G2 h2 ρ :=
  fun r s e => ⟨trivial, (h r s e).1, fun w hw => ⟨trivial, (h r s e).2 w hw⟩⟩

/-- Under causal consistency, one source map sends `r_p` to `w_q` and `r_q`
to `w_p`. -/
theorem causal_two_write : CausalFib G2 h2 ρ12 := by
  refine ⟨wd_of _ fun r s e => ?_, fun p => ?_⟩
  · simp only [ρ12] at e
    by_cases h2' : r = 2
    · subst h2'; simp at e; subst e; exact ⟨rfl, fun w hw => by cases hw; rfl⟩
    · by_cases h3 : r = 3
      · subst h3; simp at e; subst e; exact ⟨rfl, fun w hw => by cases hw; rfl⟩
      · simp [h2', h3] at e
  · have hp : p = 0 ∨ p = 1 := by revert p; decide
    rcases hp with rfl | rfl
    · refine ⟨_, ser0_01, fun r s e hr => ?_⟩
      simp only [ρ12] at e
      by_cases h2' : r = 2
      · subst h2'; simp at e; subst e; exact ex_rp_wq
      · by_cases h3 : r = 3
        · subst h3; exact absurd hr (by decide)
        · simp [h2', h3] at e
    · refine ⟨_, ser1_10, fun r s e hr => ?_⟩
      simp only [ρ12] at e
      by_cases h2' : r = 2
      · subst h2'; exact absurd hr (by decide)
      · by_cases h3 : r = 3
        · subst h3; simp at e; subst e; exact ex_rq_wp
        · simp [h2', h3] at e

theorem causal_ρ1 : CausalFib G2 h2 ρ1 := by
  refine ⟨wd_of _ fun r s e => ?_, fun p => ?_⟩
  · simp only [ρ1] at e
    by_cases h2' : r = 2
    · subst h2'; simp at e; subst e; exact ⟨rfl, fun w hw => by cases hw; rfl⟩
    · simp [h2'] at e
  · have hp : p = 0 ∨ p = 1 := by revert p; decide
    rcases hp with rfl | rfl
    · refine ⟨_, ser0_01, fun r s e hr => ?_⟩
      simp only [ρ1] at e
      by_cases h2' : r = 2
      · subst h2'; simp at e; subst e; exact ex_rp_wq
      · simp [h2'] at e
    · refine ⟨_, ser1_10, fun r s e hr => ?_⟩
      simp only [ρ1] at e
      by_cases h2' : r = 2
      · subst h2'; exact absurd hr (by decide)
      · simp [h2'] at e

theorem causal_ρa : CausalFib G2 h2 ρa := by
  refine ⟨wd_of _ fun r s e => ?_, fun p => ?_⟩
  · simp only [ρa] at e
    by_cases h2' : r = 2
    · subst h2'; simp at e; subst e; exact ⟨rfl, fun w hw => by cases hw; rfl⟩
    · simp [h2'] at e
  · have hp : p = 0 ∨ p = 1 := by revert p; decide
    rcases hp with rfl | rfl
    · refine ⟨_, ser0_10, fun r s e hr => ?_⟩
      simp only [ρa] at e
      by_cases h2' : r = 2
      · subst h2'; simp at e; subst e; exact ex_rp_wp
      · simp [h2'] at e
    · refine ⟨_, ser1_10, fun r s e hr => ?_⟩
      simp only [ρa] at e
      by_cases h2' : r = 2
      · subst h2'; exact absurd hr (by decide)
      · simp [h2'] at e

/-- "Two answers to the same read remain incompatible": the causal register
is not monotone. -/
theorem causal_not_liftedMono : ¬ (causalSpec G2).LiftedMono := by
  intro h
  obtain ⟨u, _, hall⟩ := h h2 h2 (PO.refl _) [ρa, ρ1] (by simp)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl
        · exact causal_ρa
        · exact causal_ρ1)
  have e1 : u.f 2 = some (some 0) := hall ρa (by simp) 2 _ (by simp [ρa])
  have e2 : u.f 2 = some (some 1) := hall ρ1 (by simp) 2 _ (by simp [ρ1])
  rw [e1] at e2
  exact absurd e2 (by decide)

/-- No single total order of all four operations extending `→` explains both
`r_p ↦ w_q` and `r_q ↦ w_p`. -/
theorem no_lin_both {T : Fin 4 → Fin 4 → Prop} (hT : STO h2.mem T) (hE : Ext h2.hb h2.mem T)
    (h1 : Explains G2 h2 T 2 (some 1)) (h2' : Explains G2 h2 T 3 (some 0)) : False := by
  have a : T 0 1 := by
    rcases h1.2.2.2 0 trivial rfl (hE 0 2 trivial trivial h2_shape.1) with e | l
    · exact absurd e (by decide)
    · exact l
  have b : T 1 0 := by
    rcases h2'.2.2.2 1 trivial rfl (hE 1 3 trivial trivial h2_shape.2.2.2.1) with e | l
    · exact absurd e (by decide)
    · exact l
  exact hT.irrefl _ (hT.trans a b)

abbrev ltAll (rk : Fin 4 → Nat) : Fin 4 → Fin 4 → Prop := rkLt (fun _ => true) rk

theorem lin_order (rk : Fin 4 → Nat) (hinj : ∀ a b, rk a = rk b → a = b)
    (hext : ∀ a b : Fin 4, a.val < 2 → 2 ≤ b.val → rk a < rk b) :
    STO h2.mem (ltAll rk) ∧ Ext h2.hb h2.mem (ltAll rk) := by
  refine ⟨(rk_sto _ rk (fun a b _ _ => hinj a b)).congr (fun _ => ⟨fun _ => trivial, fun _ => rfl⟩),
    fun a b _ _ hab => ⟨rfl, rfl, hext a b hab.1 hab.2⟩⟩

theorem lin_ρ1 : LinFib G2 h2 ρ1 := by
  obtain ⟨hS, hE⟩ := lin_order rk01 (by decide) (by decide)
  refine ⟨(causal_ρ1).1, ltAll rk01, hS, hE, fun r s e => ?_⟩
  simp only [ρ1] at e
  by_cases h2' : r = 2
  · subst h2'; simp at e; subst e
    exact ex_h2 rfl (by decide) (by decide)
  · simp [h2'] at e

theorem lin_ρ2 : LinFib G2 h2 ρ2 := by
  obtain ⟨hS, hE⟩ := lin_order rk10 (by decide) (by decide)
  refine ⟨wd_of _ fun r s e => ?_, ltAll rk10, hS, hE, fun r s e => ?_⟩
  · simp only [ρ2] at e
    by_cases h3 : r = 3
    · subst h3; simp at e; subst e; exact ⟨rfl, fun w hw => by cases hw; rfl⟩
    · simp [h3] at e
  · simp only [ρ2] at e
    by_cases h3 : r = 3
    · subst h3; simp at e; subst e
      exact ex_h2 rfl (by decide) (by decide)
    · simp [h3] at e

theorem lin_ρ1' : (linSpec G2).S h2 ρ1 := lin_ρ1
theorem lin_ρ2' : (linSpec G2).S h2 ρ2 := lin_ρ2

/-- **Appendix `app:registers`**: the linearizable register is not monotone
across the partition `{{p},{q}}` under any deployment authorizing `p`'s
answer `r_p ↦ w_q` and `q`'s answer `r_q ↦ w_p`. -/
theorem lin_not_monoAcross (Dp : Deployment (linSpec G2) 2) (h0 : Dp.A 0 h2 ρ1)
    (h1 : Dp.A 1 h2 ρ2) : ¬ MonoAcross Dp (fun p => p.val) := by
  intro hM
  let F : Family (linSpec G2) 2 := pairFam (oneShot (linSpec G2) h2 ρ1 lin_ρ1')
    (oneShot (linSpec G2) h2 ρ2 lin_ρ2')
  have hF0 : F 0 = some (oneShot (linSpec G2) h2 ρ1 lin_ρ1') := rfl
  have hF1 : F 1 = some (oneShot (linSpec G2) h2 ρ2 lin_ρ2') := rfl
  have hauth : Authorized Dp F := by
    rintro p r ⟨m, hm, hr⟩
    rcases pairFam_some hm with ⟨hp, rfl⟩ | ⟨hp, rfl⟩ <;> simp at hr <;> subst hr
    · have : p = 0 := Fin.ext hp
      subst this; exact h0
    · have : p = 1 := Fin.ext hp
      subst this; exact h1
  obtain ⟨u, ⟨_, T, hT, hE, hx⟩, hall⟩ := hM F hauth
    (Or.inl ⟨0, 1, (h2, ρ1), (h2, ρ2), ⟨_, hF0, by simp⟩, ⟨_, hF1, by simp⟩, by decide⟩)
    h2 (by
      intro p m hm
      rcases pairFam_some hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact PO.refl _)
  have e1 : u.f 2 = some (some 1) := hall 0 (h2, ρ1) ⟨_, hF0, by simp⟩ 2 _ (by simp [ρ1])
  have e2 : u.f 3 = some (some 0) := hall 1 (h2, ρ2) ⟨_, hF1, by simp⟩ 3 _ (by simp [ρ2])
  exact no_lin_both hT hE (hx 2 _ e1) (hx 3 _ e2)

theorem lin_not_monoAcrossPartitions (Dp : Deployment (linSpec G2) 2) (h0 : Dp.A 0 h2 ρ1)
    (h1 : Dp.A 1 h2 ρ2) : ¬ MonoAcrossPartitions Dp :=
  fun h => lin_not_monoAcross Dp h0 h1 (h _ ⟨0, 1, by decide⟩)

/-! #### Frontier application on the two-write history -/

theorem cview_ρ1 : CView G2 0 h2 ρ1 := by
  refine ⟨fun r => ?_, _, ser0_01, fun r s e => ?_⟩
  · have key : ∀ r : Fin 4, r = 2 ↔ (G2.isW r = false ∧ G2.rep r = 0) := by decide
    by_cases h2' : r = 2
    · subst h2'; simp [ρ1, PRead, h2]; decide
    · simp [ρ1, h2', PRead, h2]; intro hW hr; exact h2' ((key r).2 ⟨hW, hr⟩)
  · simp only [ρ1] at e
    by_cases h2' : r = 2
    · subst h2'; simp at e; subst e; exact ex_rp_wq
    · simp [h2'] at e

theorem cview_ρ2 : CView G2 1 h2 ρ2 := by
  refine ⟨fun r => ?_, _, ser1_10, fun r s e => ?_⟩
  · have key : ∀ r : Fin 4, r = 3 ↔ (G2.isW r = false ∧ G2.rep r = 1) := by decide
    by_cases h3 : r = 3
    · subst h3; simp [ρ2, PRead, h2]; decide
    · simp [ρ2, h3, PRead, h2]; intro hW hr; exact h3 ((key r).2 ⟨hW, hr⟩)
  · simp only [ρ2] at e
    by_cases h3 : r = 3
    · subst h3; simp at e; subst e; exact ex_rq_wp
    · simp [h3] at e

/-- Linearizability is a strict strengthening: the causal views `(ρ1, ρ2)`
are not selected. -/
theorem lin_strict : (linNS G2).Strict := by
  let y : (p : Fin 2) → SMap (Fin 4) := fun p => if p = 0 then ρ1 else ρ2
  have hy : ∀ p, CView G2 p h2 (y p) := by
    intro p
    have hp : p = 0 ∨ p = 1 := by revert p; decide
    rcases hp with rfl | rfl
    · exact cview_ρ1
    · exact cview_ρ2
  refine ⟨h2, ⟨fun p => some (y p)⟩, ⟨y, hy, fun _ => Or.inr rfl⟩, ?_⟩
  rintro ⟨z, ⟨_, T, hT, hE, hx⟩, hr⟩
  have e : ∀ p, z p = y p := by
    intro p
    rcases hr p with h | h
    · cases h
    · exact (Option.some.inj h).symm
  have e1 : (z 0).f 2 = some (some 1) := by rw [e 0]; simp [y, ρ1]
  have e2 : (z 1).f 3 = some (some 0) := by rw [e 1]; simp [y, ρ2]
  exact no_lin_both hT hE (hx 0 2 _ e1) (hx 1 3 _ e2)

/-- Part (2) recovers that (normalized) linearizability is not monotone
across partitions under its owner deployment. -/
theorem lin_product_not_monoAcross : ¬ MonoAcrossPartitions (ownerD (linSpecP G2)) :=
  strengthening_not_monoAcross (by decide) (CView G2) (cviews_antichain G2) (linNS G2)
    (linSpecP G2) (fun _ _ => Iff.rfl) (lin_locCons G2) lin_strict

end TwoWrite

/-! ### Real-time precedence breaks local conservativity -/

section RealTime

/-- Operations `0 = w_q` (replica `1`, write), `1 = r_p` (replica `0`,
read); no causal precedence. -/
def G1 : OpSig (Fin 2) 2 := ⟨fun a => ⟨1 - a.val, by omega⟩, fun a => decide (a.val = 0)⟩

def hR : Hist (Fin 2) where
  mem _ := True
  hb _ _ := False
  fin := ⟨List.finRange 2, fun a _ => List.mem_finRange a⟩
  hb_mem _ _ h := h.elim
  irrefl _ h := h
  trans _ _ _ h _ := h.elim

/-- Real-time precedence: `w_q` finished before `r_p` started. -/
def rt : Fin 2 → Fin 2 → Prop := fun a b => a = 0 ∧ b = 1

/-- Linearizability when the input also records real-time precedence. -/
def linRT : NormStr (W := fun _ => SMap (Fin 2)) (CView G1) where
  sel h y := (∀ p, CView G1 p h (y p)) ∧ ∃ T, STO h.mem T ∧ Ext h.hb h.mem T ∧
    Ext rt h.mem T ∧ ∀ p r s, (y p).f r = some s → Explains G1 h T r s
  sub _ _ hs := hs.1

/-- `r_p ↦ v₀`. -/
def vInit : SMap (Fin 2) := ⟨fun r => if r = 1 then some none else none⟩

/-- `r_p ↦ v₀` is a causal view of `p` (serialization `r_p, w_q`). -/
theorem cview_vInit : CView G1 0 hR vInit := by
  let lt : Fin 2 → Fin 2 → Prop := fun a b => a = 1 ∧ b = 0
  have hS : STO (Dom G1 hR 0) lt := by
    refine ⟨fun a b h => ?_, fun a h => ?_, fun h1 h2 => ?_, fun a b _ _ hab => ?_⟩
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨⟨trivial, by decide⟩, ⟨trivial, by decide⟩⟩
    · exact absurd (h.1.symm.trans h.2) (by decide)
    · exact absurd (h1.2.symm.trans h2.1) (by decide)
    · have key : ∀ a b : Fin 2, a ≠ b → (a = 1 ∧ b = 0) ∨ (b = 1 ∧ a = 0) := by decide
      exact key a b hab
  refine ⟨fun r => ?_, lt, ⟨hS, fun _ _ _ _ h => h.elim⟩, fun r s e => ?_⟩
  · have key : ∀ r : Fin 2, r = 1 ↔ (G1.isW r = false ∧ G1.rep r = 0) := by decide
    by_cases h1 : r = 1
    · subst h1; simp [vInit, PRead, hR]; decide
    · simp [vInit, h1, PRead, hR]; intro hW hr; exact h1 ((key r).2 ⟨hW, hr⟩)
  · simp only [vInit] at e
    by_cases h1 : r = 1
    · subst h1; simp at e; subst e
      intro w _ _ hlt; exact absurd hlt.2 (by decide)
    · simp [h1] at e

/-- With real-time precedence recorded, linearizability is not locally
conservative, so part (2) of `thm:product-frontier` does not apply. -/
theorem linRT_not_locCons : ¬ linRT.LocCons := by
  intro h
  obtain ⟨z, ⟨_, T, hT, _, hrt, hx⟩, hz⟩ := h hR 0 vInit cview_vInit
  have e : (z 0).f 1 = some none := by rw [hz]; simp [vInit]
  have hex : Explains G1 hR T 1 none := hx 0 1 none e
  exact hex 0 trivial rfl (hrt 0 1 trivial trivial ⟨rfl, rfl⟩)

end RealTime
end Deploy
end CC
