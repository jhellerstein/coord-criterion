import CoordCriterion.Appendix.RealTimeCausal

/-!
# A strengthening that reads real time (Appendix `app:rtc`, last paragraph)

Supports the last sentence of Appendix `app:rtc`: "The proof of Proposition
`prop:rtc-maximal` needs it too, since a strengthening may read real time from
the input, for instance to break ties between writes that overlap in real
time."

Two replicas and three operations: a write `a` (`0`) at replica `0`, a write
`b` (`1`) at replica `1`, and a read `r` (`2`) at replica `0`.  The
strengthening `tieStr` keeps every real-time causal view, except that `r`
returns `a` whenever `a` is a real-time causal source for it.  Whether `a` is
a source depends on real time: when `a` and `b` are both visible to `r`, `a` is
a source unless it ended before `b` began.  So the strengthening breaks the tie
between overlapping writes by reading real time.  It is strict, and it is
monotone across partitions under its owner deployment (`tie_counterexample`),
so the conclusion of Prop. `prop:rtc-maximal` fails without real-time
blindness; by that proposition, `tieStr` is not blind.
-/

namespace CC
namespace Deploy
namespace Tie

set_option linter.unusedSectionVars false

/-- Operations `0 = a` (write, replica `0`), `1 = b` (write, replica `1`),
`2 = r` (read, replica `0`). -/
def G : OpSig (Fin 3) 2 where
  rep x := if x = 1 then 1 else 0
  isW x := decide (x ≠ 2)

theorem isW_iff (x : Fin 3) : G.isW x = true ↔ x ≠ 2 := by simp [G]

theorem pread_iff {h : Hist (Fin 3)} {p : Fin 2} {x : Fin 3} :
    PRead G h p x ↔ h.mem x ∧ x = 2 ∧ p = 0 := by
  unfold PRead
  constructor
  · rintro ⟨hm, hw, hp⟩
    have hx : x = 2 := Classical.byContradiction fun hne => by
      rw [(isW_iff x).2 hne] at hw; cases hw
    subst hx
    exact ⟨hm, rfl, by rw [← hp]; rfl⟩
  · rintro ⟨hm, rfl, rfl⟩
    exact ⟨hm, by decide, rfl⟩

abbrev W : Fin 2 → Type := fun _ => SMap (Fin 3)

/-- A map with no read is real-time causal monotone. -/
theorem rmono_of {i : RHist G} {p : Fin 2} {v : SMap (Fin 3)}
    (hd : ∀ x s, v.f x = some s → x = 2) : RMono G i p v := by
  intro r₁ r₂ w e pr _ _
  have h1 : r₁ = 2 := (pread_iff.1 pr).2.1
  have h2 : r₂ = 2 := hd _ _ e
  subst h1; subst h2
  exact absurd (by assumption) (i.h.irrefl _)

/-- A view's only possible read is `r`. -/
theorem view_dom {p : Fin 2} {i : RHist G} {v : SMap (Fin 3)} (hv : RView G p i v) :
    ∀ x s, v.f x = some s → x = 2 :=
  fun x s e => (pread_iff.1 ((hv.1 x).1 ⟨s, e⟩)).2.1

/-- `RSrc` at an old read is unchanged by an input extension. -/
theorem rsrc_down {i j : RHist G} (hle : i ≼ j) {x : Fin 3} (hx : i.h.mem x) {s : Option (Fin 3)}
    (h : RSrc G j x s) : RSrc G i x s := by
  obtain ⟨hh, hrt⟩ := hle
  cases s with
  | none =>
    intro w hw hwx
    exact h w hw ((hh.2.2 w x (i.h.hb_mem _ _ hwx).1 hx).2 hwx)
  | some a =>
    obtain ⟨h1, h2, h3⟩ := h
    have ha : i.h.mem a := hh.2.1 a x h1 hx
    refine ⟨(hh.2.2 a x ha hx).1 h1, h2, fun w' hw' hw'x hr => ?_⟩
    have hw'm : i.h.mem w' := (i.h.hb_mem _ _ hw'x).1
    exact h3 w' hw' ((hh.2.2 w' x hw'm hx).2 hw'x) ((hrt a w' ha hw'm).2 hr)

/-- The preference: `r` returns `a` whenever `a` is a source for it. -/
def Pref (i : RHist G) (v : SMap (Fin 3)) : Prop :=
  RSrc G i 2 (some 0) → v.f 2 ≠ none → v.f 2 = some (some 0)

/-- The views kept by the strengthening. -/
def V' (p : Fin 2) (i : RHist G) (v : SMap (Fin 3)) : Prop := RView G p i v ∧ Pref i v

/-- Set `r`'s source to `a`. -/
def toA (v : SMap (Fin 3)) : SMap (Fin 3) := ⟨fun x => if x = 2 then some (some 0) else v.f x⟩

theorem toA_view {p : Fin 2} {i : RHist G} {v : SMap (Fin 3)} (hv : RView G p i v)
    (hp : p = 0) (hs : RSrc G i 2 (some 0)) : RView G p i (toA v) := by
  have hm : i.h.mem 2 := (i.h.hb_mem _ _ hs.1).2
  refine ⟨fun x => ?_, fun x s e => ?_, rmono_of fun x s e => ?_⟩
  · by_cases hx : x = 2
    · subst hx; simp only [toA, if_true]
      exact ⟨fun _ => pread_iff.2 ⟨hm, rfl, hp⟩, fun _ => ⟨_, rfl⟩⟩
    · simp only [toA, hx, if_false]; exact hv.1 x
  · by_cases hx : x = 2
    · subst hx; simp only [toA, if_true] at e; cases e; exact hs
    · simp only [toA, hx, if_false] at e; exact hv.2.1 x s e
  · by_cases hx : x = 2
    · exact hx
    · simp only [toA, hx, if_false] at e; exact view_dom hv x s e

/-- Adjust a view to satisfy the preference. -/
theorem adjust {p : Fin 2} {i : RHist G} {v : SMap (Fin 3)} (hv : RView G p i v) :
    ∃ w, V' p i w ∧ ∀ x, x ≠ 2 → w.f x = v.f x := by
  by_cases h : p = 0 ∧ RSrc G i 2 (some 0)
  · exact ⟨toA v, ⟨toA_view hv h.1 h.2, fun _ _ => by simp [toA]⟩,
      fun x hx => by simp [toA, hx]⟩
  · refine ⟨v, ⟨hv, fun hs hne => ?_⟩, fun _ _ => rfl⟩
    exfalso
    apply h
    refine ⟨?_, hs⟩
    obtain ⟨s, e⟩ := Option.ne_none_iff_exists'.1 hne
    exact (pread_iff.1 ((hv.1 2).1 ⟨s, e⟩)).2.2

theorem v'_ne (p : Fin 2) (i : RHist G) : ∃ v, V' p i v := by
  obtain ⟨v, hv⟩ := rview_ne (G := G) p i
  obtain ⟨w, hw, _⟩ := adjust hv
  exact ⟨w, hw⟩

/-- The kept views continue. -/
theorem v'_cont : Continue (W := W) V' := by
  intro p i j v hle hv
  obtain ⟨w0, hw0, hvw0⟩ := rview_cont (G := G) p i j v hle hv.1
  by_cases h : p = 0 ∧ RSrc G j 2 (some 0)
  · refine ⟨toA w0, ⟨toA_view hw0 h.1 h.2, fun _ _ => by simp [toA]⟩, fun x s e => ?_⟩
    by_cases hx : x = 2
    · subst hx
      have hm : i.h.mem 2 := (pread_iff.1 ((hv.1.1 2).1 ⟨s, e⟩)).1
      have := hv.2 (rsrc_down hle hm h.2) (by rw [e]; simp)
      rw [e] at this; cases this
      simp [toA]
    · simp only [toA, hx, if_false]; exact hvw0 x s e
  · refine ⟨w0, ⟨hw0, fun hs hne => ?_⟩, hvw0⟩
    exfalso
    apply h
    refine ⟨?_, hs⟩
    obtain ⟨s, e⟩ := Option.ne_none_iff_exists'.1 hne
    exact (pread_iff.1 ((hw0.1 2).1 ⟨s, e⟩)).2.2

/-- The strengthening: tuples of kept views. -/
def tieStr : NormStr (W := W) (RView G) where
  sel i y := ∀ p, V' p i (y p)
  sub _ _ h p := (h p).1

/-- Its spec: the product interface of the kept views. -/
noncomputable def tieSpec : Spec (RHist G) (PTd W) := prodSpec V' v'_ne

/-! ### Two overlapping writes, both visible to `r` -/

def hb0 (x y : Fin 3) : Prop := (x = 0 ∨ x = 1) ∧ y = 2

instance (x y : Fin 3) : Decidable (hb0 x y) := by unfold hb0; infer_instance

def h0 : Hist (Fin 3) where
  mem _ := True
  hb := hb0
  fin := ⟨[0, 1, 2], by decide⟩
  hb_mem _ _ _ := ⟨trivial, trivial⟩
  irrefl := by decide
  trans := by decide

/-- `a → r`, `b → r`, and `a`, `b` overlap in real time. -/
def i0 : RHist G where
  h := h0
  rt := hb0
  rt_mem _ _ _ := ⟨trivial, trivial⟩
  rt_irrefl := by decide
  rt_trans := by decide
  hb_rt _ _ h := h
  po := by
    intro a b _ _ hrep hne
    have key : ∀ a b : Fin 3, G.rep a = G.rep b → a ≠ b → hb0 a b ∨ hb0 b a := by decide
    exact key a b hrep hne

/-- The view in which `r` returns `b`. -/
def vb : SMap (Fin 3) := ⟨fun x => if x = 2 then some (some 1) else none⟩

theorem vb_view : RView G 0 i0 vb := by
  refine ⟨fun x => ?_, fun x s e => ?_, rmono_of fun x s e => ?_⟩
  · by_cases hx : x = 2
    · subst hx; simp only [vb, if_true]
      exact ⟨fun _ => pread_iff.2 ⟨trivial, rfl, rfl⟩, fun _ => ⟨_, rfl⟩⟩
    · simp only [vb, hx, if_false]
      exact ⟨fun ⟨_, e⟩ => (by cases e), fun h => absurd (pread_iff.1 h).2.1 hx⟩
  · by_cases hx : x = 2
    · subst hx; simp only [vb, if_true] at e; cases e
      refine ⟨(show hb0 1 2 by decide), by decide, fun w' hw' _ hr => ?_⟩
      exact (isW_iff w').1 hw' hr.2
    · simp only [vb, hx, if_false] at e; cases e
  · by_cases hx : x = 2
    · exact hx
    · simp only [vb, hx, if_false] at e; cases e

theorem empty_view : RView G 1 i0 emptyMap := by
  refine ⟨fun x => ⟨fun ⟨_, e⟩ => (by cases e), fun h => ?_⟩, fun _ _ e => (by cases e),
    rmono_of fun _ _ e => (by cases e)⟩
  exact absurd (pread_iff.1 h).2.2 (by decide)

theorem a_src : RSrc G i0 2 (some 0) := by
  refine ⟨(show hb0 0 2 by decide), by decide, fun w' hw' _ hr => ?_⟩
  exact (isW_iff w').1 hw' hr.2

/-- The tuple `(vb, ∅)`. -/
def yb : (p : Fin 2) → W p := fun p => if p = 0 then vb else emptyMap

theorem tie_strict : tieStr.Strict := by
  refine ⟨i0, ⟨fun p => some (yb p)⟩, ⟨yb, fun p => ?_, fun _ => Or.inr rfl⟩, ?_⟩
  · by_cases hp : p = 0
    · subst hp; simpa [yb] using vb_view
    · have : p = 1 := by revert p hp; decide
      subst this; simpa [yb] using empty_view
  · rintro ⟨y, hy, hres⟩
    have h0' : y 0 = vb := by
      rcases hres 0 with e | e
      · simp at e
      · simp [yb] at e; exact e.symm
    have := (hy 0).2 a_src (by rw [h0']; simp [vb])
    rw [h0'] at this
    simp [vb] at this

/-- **A strengthening that reads real time.**  `tieStr` is a strict
strengthening of the real-time causal product interface whose spec is
monotone across partitions under its owner deployment; it is not real-time
blind. -/
theorem tie_counterexample :
    (∀ i x, tieSpec.P i x ↔ tieStr.table i x) ∧ tieStr.Strict ∧
      MonoAcrossPartitions (ownerD tieSpec) ∧ ¬ RBlind (G := G) tieStr := by
  have hsp : ∀ i x, tieSpec.P i x ↔ tieStr.table i x := fun _ _ => Iff.rfl
  have hmono : MonoAcrossPartitions (ownerD tieSpec) := product_monoAcross V' v'_ne v'_cont
  exact ⟨hsp, tie_strict, hmono,
    fun hbl => rtc_strengthening_not_monoAcross (Nat.le_refl 2) tieStr tieSpec hsp hbl tie_strict hmono⟩

end Tie
end Deploy
end CC
