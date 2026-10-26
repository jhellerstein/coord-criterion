import CoordCriterion.Appendix.Registers

/-!
# Real-time causal consistency (Appendix `app:rtc`)

Mahajan, Alvisi, and Dahlin's maximality result for real-time causal
consistency (RTC), recovered with real time as input data:

* inputs `RHist G`: a causal history together with a strict partial order
  `rt` of real-time precedence that contains causal precedence; operations
  at one replica are totally ordered by causal precedence (program order);
  inputs are ordered by causally closed extension that keeps `rt` among old
  operations;
* the RTC views `RView G p i`: every read of `p` gets a source that is `v₀`
  or a write in its causal past (`v₀` only when that past has no write), the
  source did not end before another write of the read's causal past began,
  and a later read of `p` does not return a write that an earlier read of `p`
  saw but did not return (`RMono`);
* part (1): the views exist, continue, and form an antichain, so the RTC
  product interface is monotone across partitions under the owner deployment
  (`rtc_product_monoAcross`);
* forcing: for every view `v` of `p` at `i`, adding real-time edges gives an
  input with the same causal history at which `v` is `p`'s only view
  (`forceRt`, `rview_unique`);
* part (2): every real-time blind strengthening keeps every replica's views
  (`rtc_locCons`), so a strict one is not monotone across partitions under its
  owner deployment (`rtc_strengthening_not_monoAcross`).

Modeling choices: sources are single writes (Mahajan's reads return a set of
concurrent writes); real time is a strict partial order rather than interval
endpoints; "the implementation does not observe real time" is the hypothesis
`RBlind` on the strengthening.
-/

namespace CC
namespace Deploy

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section RTC
variable {α : Type} {n : Nat} (G : OpSig α n)

/-- A history with real-time precedence. -/
structure RHist (G : OpSig α n) where
  h : Hist α
  rt : α → α → Prop
  rt_mem : ∀ a b, rt a b → h.mem a ∧ h.mem b
  rt_irrefl : ∀ a, ¬ rt a a
  rt_trans : ∀ a b c, rt a b → rt b c → rt a c
  /-- Causal precedence implies real-time precedence. -/
  hb_rt : ∀ a b, h.hb a b → rt a b
  /-- Program order: operations at one replica are causally ordered. -/
  po : ∀ a b, h.mem a → h.mem b → G.rep a = G.rep b → a ≠ b → h.hb a b ∨ h.hb b a

/-- Causally closed extension that keeps real-time precedence among the old
operations. -/
instance : PO (RHist G) where
  le i j := i.h ≼ j.h ∧ ∀ a b, i.h.mem a → i.h.mem b → (j.rt a b ↔ i.rt a b)
  refl i := ⟨PO.refl _, fun _ _ _ _ => Iff.rfl⟩
  trans {i j k} hij hjk := ⟨PO.trans hij.1 hjk.1, fun a b ha hb =>
    (hjk.2 a b (hij.1.1 a ha) (hij.1.1 b hb)).trans (hij.2 a b ha hb)⟩
  antisymm {i j} hij hji := by
    have eh : i.h = j.h := PO.antisymm hij.1 hji.1
    have er : i.rt = j.rt := funext fun a => funext fun b => propext
      ⟨fun hr => (hij.2 a b (i.rt_mem a b hr).1 (i.rt_mem a b hr).2).2 hr,
       fun hr => (hji.2 a b (j.rt_mem a b hr).1 (j.rt_mem a b hr).2).2 hr⟩
    cases i; cases j; simp only at eh er; subst eh; subst er; rfl

/-- Real-time condition on the source of read `r`. -/
def RSrc (i : RHist G) (r : α) : Option α → Prop
  | none => ∀ w, G.isW w = true → ¬ i.h.hb w r
  | some w => i.h.hb w r ∧ G.isW w = true ∧
      ∀ w', G.isW w' = true → i.h.hb w' r → ¬ i.rt w w'

/-- A later read of `p` does not return a write that an earlier read of `p`
saw but did not return. -/
def RMono (i : RHist G) (p : Fin n) (v : SMap α) : Prop :=
  ∀ r₁ r₂ w, v.f r₂ = some (some w) → PRead G i.h p r₁ → i.h.hb r₁ r₂ → i.h.hb w r₁ →
    v.f r₁ = some (some w)

/-- `V_p(i)`: the real-time causal views of replica `p`. -/
def RView (p : Fin n) (i : RHist G) (v : SMap α) : Prop :=
  (∀ r, (∃ s, v.f r = some s) ↔ PRead G i.h p r) ∧
    (∀ r s, v.f r = some s → RSrc G i r s) ∧ RMono G i p v

/-- A partial view on a set of reads of `p` closed under program order. -/
def RGood (i : RHist G) (p : Fin n) (v : SMap α) : Prop :=
  (∀ r s, v.f r = some s → PRead G i.h p r ∧ RSrc G i r s) ∧ RMono G i p v ∧
    ∀ r₁ r₂ s, PRead G i.h p r₁ → i.h.hb r₁ r₂ → v.f r₂ = some s → ∃ s', v.f r₁ = some s'

theorem rview_good {p : Fin n} {i : RHist G} {v : SMap α} (hv : RView G p i v) :
    RGood G i p v :=
  ⟨fun r s e => ⟨(hv.1 r).1 ⟨s, e⟩, hv.2.1 r s e⟩, hv.2.2,
    fun r₁ _ _ h1 _ _ => (hv.1 r₁).2 h1⟩

/-! ### The forcing order -/

/-- Read `r` returns `w` although it saw the write `x ≠ w`. -/
def Ed (i : RHist G) (v : SMap α) (r x w : α) : Prop :=
  v.f r = some (some w) ∧ G.isW x = true ∧ i.h.hb x r ∧ x ≠ w

/-- Real-time precedence plus "each overwritten write ended before the source
began". -/
def Kv (i : RHist G) (v : SMap α) (a b : α) : Prop :=
  i.rt a b ∨ ∃ r x w, Ed G i v r x w ∧ (a = x ∨ i.rt a x) ∧ (w = b ∨ i.rt w b)

variable {G}

theorem rt_eq_trans (i : RHist G) {a b c : α} (h1 : a = b ∨ i.rt a b) (h2 : b = c ∨ i.rt b c) :
    a = c ∨ i.rt a c := by
  rcases h1 with rfl | h1
  · exact h2
  · rcases h2 with rfl | h2
    · exact Or.inr h1
    · exact Or.inr (i.rt_trans _ _ _ h1 h2)

theorem ed_chain {i : RHist G} {p : Fin n} {v : SMap α} (hg : RGood G i p v)
    {r x w r' x' w' : α} (e1 : Ed G i v r x w) (e2 : Ed G i v r' x' w')
    (hw : w = x' ∨ i.rt w x') : Ed G i v r' x w' := by
  obtain ⟨hr, hx, hxr, hxw⟩ := e1
  obtain ⟨hr', hx', hxr', hxw'⟩ := e2
  obtain ⟨pr, ⟨_, _, hno⟩⟩ := hg.1 r _ hr
  obtain ⟨pr', ⟨_, _, hno'⟩⟩ := hg.1 r' _ hr'
  by_cases e : r = r'
  · subst e
    rw [hr] at hr'; cases hr'
    rcases hw with rfl | hw
    · exact absurd rfl hxw'
    · exact absurd hw (hno x' hx' hxr')
  · rcases i.po r r' pr.1 pr'.1 (pr.2.2.trans pr'.2.2.symm) e with h | h
    · refine ⟨hr', hx, i.h.trans _ _ _ hxr h, fun hxe => ?_⟩
      subst hxe
      have := hg.2.1 r r' x hr' pr h hxr
      rw [hr] at this; cases this; exact hxw rfl
    · have hx'r : i.h.hb x' r := i.h.trans _ _ _ hxr' h
      rcases hw with rfl | hw
      · have := hg.2.1 r' r w hr pr' h hxr'
        rw [hr'] at this; cases this; exact absurd rfl hxw'
      · exact absurd hw (hno x' hx' hx'r)

theorem kv_trans {i : RHist G} {p : Fin n} {v : SMap α} (hg : RGood G i p v) :
    ∀ a b c, Kv G i v a b → Kv G i v b c → Kv G i v a c := by
  intro a b c h1 h2
  rcases h1 with h1 | ⟨r, x, w, e, ha, hb⟩ <;> rcases h2 with h2 | ⟨r', x', w', e', hb', hc⟩
  · exact Or.inl (i.rt_trans _ _ _ h1 h2)
  · exact Or.inr ⟨r', x', w', e', Or.inr (by
      rcases hb' with rfl | hb'
      · exact h1
      · exact i.rt_trans _ _ _ h1 hb'), hc⟩
  · refine Or.inr ⟨r, x, w, e, ha, Or.inr ?_⟩
    rcases hb with rfl | hb
    · exact h2
    · exact i.rt_trans _ _ _ hb h2
  · exact Or.inr ⟨r', x, w', ed_chain hg e e' (rt_eq_trans i hb hb'), ha, hc⟩

theorem kv_irrefl {i : RHist G} {p : Fin n} {v : SMap α} (hg : RGood G i p v) :
    ∀ a, ¬ Kv G i v a a := by
  rintro a (h | ⟨r, x, w, ⟨hr, hx, hxr, hxw⟩, ha, hb⟩)
  · exact i.rt_irrefl a h
  · obtain ⟨_, ⟨_, _, hno⟩⟩ := hg.1 r _ hr
    rcases rt_eq_trans i hb ha with h | h
    · exact hxw h.symm
    · exact hno x hx hxr h

theorem kv_mem {i : RHist G} {p : Fin n} {v : SMap α} (hg : RGood G i p v) :
    ∀ a b, Kv G i v a b → i.h.mem a ∧ i.h.mem b := by
  rintro a b (h | ⟨r, x, w, ⟨hr, hx, hxr, hxw⟩, ha, hb⟩)
  · exact i.rt_mem a b h
  · constructor
    · rcases ha with rfl | ha
      · exact (i.h.hb_mem _ _ hxr).1
      · exact (i.rt_mem _ _ ha).1
    · rcases hb with rfl | hb
      · exact (i.h.hb_mem _ _ (hg.1 r _ hr).2.1).1
      · exact (i.rt_mem _ _ hb).2

/-- The input `i` with real-time precedence replaced by `Kv`: same causal
history, more real-time edges. -/
def forceRt (i : RHist G) {p : Fin n} {v : SMap α} (hg : RGood G i p v) : RHist G where
  h := i.h
  rt := Kv G i v
  rt_mem := kv_mem hg
  rt_irrefl := kv_irrefl hg
  rt_trans := kv_trans hg
  hb_rt a b h := Or.inl (i.hb_rt a b h)
  po := i.po

theorem SMap.ext' {v w : SMap α} (h : ∀ r, v.f r = w.f r) : v = w := by
  have : v.f = w.f := funext h
  cases v; cases w; simp only at this; subst this; rfl

/-- At the forced input, `v` is `p`'s only view. -/
theorem rview_unique {i : RHist G} {p : Fin n} {v v' : SMap α} (hv : RView G p i v)
    (hv' : RView G p (forceRt i (rview_good G hv)) v') : v' = v := by
  apply SMap.ext'
  intro r
  cases hr : v.f r with
  | none =>
    cases hr' : v'.f r with
    | none => rfl
    | some s' =>
      have := (hv.1 r).2 ((hv'.1 r).1 ⟨s', hr'⟩)
      rw [hr] at this; obtain ⟨_, h⟩ := this; cases h
  | some s =>
    obtain ⟨s', hr'⟩ := (hv'.1 r).2 ((hv.1 r).1 ⟨s, hr⟩)
    rw [hr']
    have h1 := hv.2.1 r s hr
    have h2 := hv'.2.1 r s' hr'
    cases s with
    | none =>
      cases s' with
      | none => rfl
      | some w' => exact absurd h2.1 (h1 w' h2.2.1)
    | some w =>
      cases s' with
      | none => exact absurd h1.1 (h2 w h1.2.1)
      | some w' =>
        by_cases e : w' = w
        · rw [e]
        · exact absurd (Or.inr ⟨r, w', w, ⟨hr, h2.2.1, h2.1, e⟩, Or.inl rfl, Or.inl rfl⟩)
            (h2.2.2 w h1.2.1 h1.1)

/-- Views at the forced input are views at `i`: more real-time precedence
leaves fewer views. -/
theorem rview_back {i : RHist G} {p q : Fin n} {v y : SMap α} (hg : RGood G i p v)
    (hy : RView G q (forceRt i hg) y) : RView G q i y := by
  refine ⟨hy.1, fun r s e => ?_, hy.2.2⟩
  have h := hy.2.1 r s e
  cases s with
  | none => exact h
  | some w => exact ⟨h.1, h.2.1, fun w' h1 h2 h3 => h.2.2 w' h1 h2 (Or.inl h3)⟩

/-! ### Existence and continuation of views -/

/-- Every partial view closed under program order extends to a view. -/
theorem rgood_extend {i : RHist G} {p : Fin n} {v : SMap α} (hg : RGood G i p v) :
    ∃ w, RView G p i w ∧ v ≼ w := by
  classical
  obtain ⟨l, hl⟩ := i.h.fin
  obtain ⟨σ, hσ, hσE⟩ := linExt (Kv G i v) (kv_irrefl hg) (kv_trans hg) l i.h.mem hl
  let B : α → α → Prop := fun r w => i.h.mem w ∧ G.isW w = true ∧ i.h.hb w r
  let Max : α → Option α → Prop := fun r s => match s with
    | none => ¬ ∃ w, B r w
    | some m => B r m ∧ ∀ b, B r b → b = m ∨ σ b m
  have hmax : ∀ r, ∃ s, Max r s := by
    intro r
    by_cases hne : ∃ w, B r w
    · obtain ⟨m, hm, hmx⟩ := sto_max hσ l (B r) (fun b h => h.1) (fun b h => hl b h.1) hne
      exact ⟨some m, hm, hmx⟩
    · exact ⟨none, hne⟩
  let src : α → Option α := fun r => Classical.choose (hmax r)
  have hsrc : ∀ r, Max r (src r) := fun r => Classical.choose_spec (hmax r)
  have σirr : ∀ a b, σ a b → σ b a → False := fun a b h1 h2 => hσ.irrefl a (hσ.trans h1 h2)
  -- sources chosen for new reads
  have newSrc : ∀ r m, src r = some m → B r m ∧ ∀ b, B r b → b = m ∨ σ b m := by
    intro r m e; have := hsrc r; rw [e] at this; exact this
  let w : SMap α := ⟨fun r => match v.f r with
    | some s => some s
    | none => if PRead G i.h p r then some (src r) else none⟩
  have wold : ∀ r s, v.f r = some s → w.f r = some s := by
    intro r s e; show (match v.f r with
      | some s => some s
      | none => if PRead G i.h p r then some (src r) else none) = some s
    rw [e]
  have wnew : ∀ r, v.f r = none → w.f r = if PRead G i.h p r then some (src r) else none := by
    intro r e; show (match v.f r with
      | some s => some s
      | none => if PRead G i.h p r then some (src r) else none) = _
    rw [e]
  refine ⟨w, ⟨fun r => ?_, fun r s e => ?_, ?_⟩, fun r s e => wold r s e⟩
  · cases hv : v.f r with
    | some s => exact ⟨fun _ => (hg.1 r s hv).1, fun _ => ⟨s, wold r s hv⟩⟩
    | none =>
      rw [wnew r hv]
      by_cases hp : PRead G i.h p r
      · simp [hp]
      · simp [hp]
  · cases hv : v.f r with
    | some s' =>
      rw [wold r s' hv] at e; cases e; exact (hg.1 r _ hv).2
    | none =>
      rw [wnew r hv] at e
      by_cases hp : PRead G i.h p r
      · simp only [hp, ite_true, Option.some.injEq] at e
        subst e
        cases hs : src r with
        | none =>
          have := hsrc r; rw [hs] at this
          exact fun x hx hxr => this ⟨x, (i.h.hb_mem _ _ hxr).1, hx, hxr⟩
        | some m =>
          obtain ⟨⟨_, hmW, hmr⟩, hmx⟩ := newSrc r m hs
          refine ⟨hmr, hmW, fun x hx hxr hrt => ?_⟩
          have hmxσ := hσE m x (i.rt_mem _ _ hrt).1 (i.rt_mem _ _ hrt).2 (Or.inl hrt)
          rcases hmx x ⟨(i.h.hb_mem _ _ hxr).1, hx, hxr⟩ with rfl | h
          · exact hσ.irrefl _ hmxσ
          · exact σirr _ _ h hmxσ
      · simp [hp] at e
  · intro r₁ r₂ m e2 pr₁ h12 hm1
    have hmem1 : i.h.mem m := (i.h.hb_mem _ _ hm1).1
    have hW : G.isW m = true := by
      cases hv2 : v.f r₂ with
      | some s =>
        rw [wold r₂ s hv2] at e2; cases e2; exact (hg.1 r₂ _ hv2).2.2.1
      | none =>
        rw [wnew r₂ hv2] at e2
        by_cases hp : PRead G i.h p r₂
        · simp only [hp, ite_true, Option.some.injEq] at e2
          exact (newSrc r₂ m e2).1.2.1
        · simp [hp] at e2
    cases hv2 : v.f r₂ with
    | some s =>
      rw [wold r₂ s hv2] at e2; cases e2
      exact wold r₁ _ (hg.2.1 r₁ r₂ m hv2 pr₁ h12 hm1)
    | none =>
      rw [wnew r₂ hv2] at e2
      by_cases hp : PRead G i.h p r₂
      · simp only [hp, ite_true, Option.some.injEq] at e2
        obtain ⟨_, hmx⟩ := newSrc r₂ m e2
        have sub : ∀ b, B r₁ b → B r₂ b :=
          fun b ⟨h1, h2, h3⟩ => ⟨h1, h2, i.h.trans _ _ _ h3 h12⟩
        cases hv1 : v.f r₁ with
        | some s₁ =>
          rw [wold r₁ s₁ hv1]
          have h1 := (hg.1 r₁ s₁ hv1).2
          cases s₁ with
          | none => exact absurd hm1 (h1 m hW)
          | some a =>
            by_cases e : m = a
            · rw [e]
            · exfalso
              have hk : σ m a := hσE m a hmem1 (i.h.hb_mem _ _ h1.1).1
                (Or.inr ⟨r₁, m, a, ⟨hv1, hW, hm1, e⟩, Or.inl rfl, Or.inl rfl⟩)
              rcases hmx a (sub a ⟨(i.h.hb_mem _ _ h1.1).1, h1.2.1, h1.1⟩) with h | h
              · exact e h.symm
              · exact σirr _ _ h hk
        | none =>
          rw [wnew r₁ hv1]
          simp only [pr₁, ite_true, Option.some.injEq]
          cases hs : src r₁ with
          | none =>
            have := hsrc r₁; rw [hs] at this
            exact absurd ⟨m, hmem1, hW, hm1⟩ this
          | some m₁ =>
            obtain ⟨hb1, hmx1⟩ := newSrc r₁ m₁ hs
            rcases hmx1 m ⟨hmem1, hW, hm1⟩ with h | h
            · rw [h]
            · rcases hmx m₁ (sub m₁ hb1) with h' | h'
              · rw [h']
              · exact absurd (σirr _ _ h h') id
      · simp [hp] at e2

theorem rview_ne : ∀ (p : Fin n) (i : RHist G), ∃ v, RView G p i v := by
  intro p i
  have hg : RGood G i p emptyMap := by
    refine ⟨fun _ _ e => ?_, fun _ _ _ e => ?_, fun _ _ _ _ _ e => ?_⟩ <;> cases e
  obtain ⟨w, hw, _⟩ := rgood_extend hg
  exact ⟨w, hw⟩

/-- An expansion keeps a view's reads, their causal pasts, and real-time
precedence among them. -/
theorem rview_good_up {i j : RHist G} (hle : i ≼ j) {p : Fin n} {v : SMap α}
    (hv : RView G p i v) : RGood G j p v := by
  obtain ⟨hh, hrt⟩ := hle
  have pread : ∀ r, PRead G i.h p r → PRead G j.h p r :=
    fun r h => ⟨hh.1 r h.1, h.2⟩
  refine ⟨fun r s e => ?_, ?_, ?_⟩
  · have pr := (hv.1 r).1 ⟨s, e⟩
    refine ⟨pread r pr, ?_⟩
    have h := hv.2.1 r s e
    cases s with
    | none =>
      intro x hx hxr
      exact h x hx ((hh.2.2 x r (hh.2.1 x r hxr pr.1) pr.1).1 hxr)
    | some a =>
      have ha : i.h.mem a := (i.h.hb_mem _ _ h.1).1
      refine ⟨(hh.2.2 a r ha pr.1).2 h.1, h.2.1, fun x hx hxr hrt' => ?_⟩
      have hxm := hh.2.1 x r hxr pr.1
      exact h.2.2 x hx ((hh.2.2 x r hxm pr.1).1 hxr) ((hrt a x ha hxm).1 hrt')
  · intro r₁ r₂ m e pr₁ h12 hm1
    have pr₂ := (hv.1 r₂).1 ⟨_, e⟩
    have m1 := hh.2.1 r₁ r₂ h12 pr₂.1
    have mm := hh.2.1 m r₁ hm1 m1
    exact hv.2.2 r₁ r₂ m e ⟨m1, pr₁.2⟩ ((hh.2.2 r₁ r₂ m1 pr₂.1).1 h12)
      ((hh.2.2 m r₁ mm m1).1 hm1)
  · intro r₁ r₂ s pr₁ h12 e
    have pr₂ := (hv.1 r₂).1 ⟨_, e⟩
    exact (hv.1 r₁).2 ⟨hh.2.1 r₁ r₂ h12 pr₂.1, pr₁.2⟩

/-- Views continue. -/
theorem rview_cont : Continue (W := fun _ => SMap α) (RView G) := by
  intro p i j v hle hv
  exact rgood_extend (rview_good_up hle hv)

/-- Views of one replica at one input form an antichain. -/
theorem rview_antichain : Antichain (W := fun _ => SMap α) (RView G) := by
  intro p i v w hv hw hvw
  apply PO.antisymm hvw
  intro r s e
  obtain ⟨s', e'⟩ := (hv.1 r).2 ((hw.1 r).1 ⟨s, e⟩)
  have := hvw r s' e'
  rw [e] at this; cases this; exact e'

/-- **Part (1)**: the RTC product interface is monotone across partitions
under the owner deployment. -/
theorem rtc_product_monoAcross :
    MonoAcrossPartitions (ownerD (prodSpec (W := fun _ => SMap α) (RView G) rview_ne)) :=
  product_monoAcross _ rview_ne rview_cont

/-! ### Every real-time blind strict strengthening fails -/

/-- A strengthening is *real-time blind* when a tuple it selects at an input
stays selected at the same causal history with less real-time precedence,
provided its views are real-time causal there. -/
def RBlind (T : NormStr (W := fun _ => SMap α) (RView G)) : Prop :=
  ∀ (i i' : RHist G), i'.h = i.h → (∀ a b, i.rt a b → i'.rt a b) →
    ∀ y, T.sel i' y → (∀ q, RView G q i (y q)) → T.sel i y

/-- A real-time blind strengthening keeps every view of every replica. -/
theorem rtc_locCons (T : NormStr (W := fun _ => SMap α) (RView G))
    (sp : Spec (RHist G) (PTd (fun _ : Fin n => SMap α)))
    (hsp : ∀ i x, sp.S i x ↔ T.table i x) (hbl : RBlind T) : T.LocCons := by
  intro i p v hv
  have hg := rview_good G hv
  obtain ⟨x, hx⟩ := sp.total (forceRt i hg)
  obtain ⟨z, hz, _⟩ := (hsp _ _).1 hx
  refine ⟨z, hbl i (forceRt i hg) rfl (fun a b h => Or.inl h) z hz
    (fun q => rview_back hg (T.sub _ _ hz q)), rview_unique hv (T.sub _ _ hz p)⟩

/-- **Part (2)** (`|P| ≥ 2`): no strict, real-time blind strengthening of the
RTC product interface is monotone across partitions under its owner
deployment. -/
theorem rtc_strengthening_not_monoAcross (hn : 2 ≤ n)
    (T : NormStr (W := fun _ => SMap α) (RView G))
    (sp : Spec (RHist G) (PTd (fun _ : Fin n => SMap α)))
    (hsp : ∀ i x, sp.S i x ↔ T.table i x) (hbl : RBlind T) (hst : T.Strict) :
    ¬ MonoAcrossPartitions (ownerD sp) :=
  strengthening_not_monoAcross hn (RView G) rview_antichain T sp hsp
    (rtc_locCons T sp hsp hbl) hst

end RTC
end Deploy
end CC
