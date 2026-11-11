import CoordCriterion.Instances.HATSpec
import CoordCriterion.Appendix.Conjunction

/-!
# HAT as a conjunction (Sec. `hat-instance`, via `sec:conjunction`)

The store specification `store` permits, at each input, any subset of the
answers HAT's read rule gives (`hatOut`), and promises nothing about
isolation.  The HAT specification for a level is conjoined with it.

* `store`               — Def. `def:store-spec`
* `store_conj_rc`       — for RU and RC (timestamp condition), the conjunction
  satisfies Lifted Monotonicity (Prop. `prop:conjunction-bound` with the read
  rule as the bound)
* `store_conj_lostUpdate` — for any proscribed set containing Lost Update, the
  conjunction fails Relational Monotonicity, hence Lifted Monotonicity
-/

namespace CC
namespace HATSpec

open HATRC (tsInit tsLt)
open IConf (St)

variable {lam : Bool}

/-- The store specification: any subset of the read rule's answers. -/
def store : Spec (Inp lam) (St Fact) where
  P j F := F ≼ hatOut j
  total j := ⟨hatOut j, PO.refl _⟩

/-- The conjunction of the store with any HAT specification is total: both
permit the empty set of answers. -/
theorem store_conj_total (P : (j : Inp lam) → CH j → Prop) (hP : ∀ j, ¬ P j (serial j)) :
    ∀ j, ∃ o, (store (lam := lam)).P j o ∧ (specP P hP).P j o :=
  fun j => ⟨fun _ => False, fun _ h => h.elim, serial j, fun _ h => h.elim, hP j⟩

/-- **RU and RC, as a conjunction.**  Under the timestamp condition, the read
rule's answers are permitted by `𝒮_RU` and `𝒮_RC`, and the read rule is
monotone, so the conjunction of the store with either level satisfies Lifted
Monotonicity. -/
theorem store_conj_rc (L : Level) (hL : L = .RU ∨ L = .RC) :
    ∃ htot, (Conj.conj (store (lam := true)) (spec L) htot).LiftedMono := by
  have h₂ : ∀ j : Inp true, (spec L).P j (hatOut j) := by
    rcases hL with rfl | rfl
    · exact hatOut_ru
    · exact hatOut_rc
  exact ⟨_, Conj.conj_liftedMono_of_bound store (spec L) hatOut (fun _ _ h => hatOut_mono h)
    (fun _ _ h => h) (fun _ => PO.refl _) h₂⟩

/-- In `i₂`, the read rule answers `T₂`'s read with `x₀` (no write has been
delivered). -/
theorem i2_ans : Ans (i2 (lam := lam)) 2 tsInit := by
  refine ⟨⟨2, 1, 0, 1, rfl, Or.inl rfl⟩, fun v' hc => Or.inl ?_⟩
  obtain ⟨c, n, k, r, hr, hv⟩ := hc
  rcases hv with hv | ⟨d, c', n', f, ks, hd, -, -⟩
  · exact hv
  · have : (if keep2 d then luLab d else none) = some (.dl c' n' k r) := hd
    split at this
    · rcases luLab_cases this with ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ <;> cases hx
    · cases this

/-- **Lost Update, as a conjunction.**  For any set of proscribed phenomena
containing Lost Update, the row of `T₂`'s forced answer `x₀` at `i₂` is in the
conjunction of the store with `𝒮_P`, but no row of the conjunction at the
union `iJ` extends it.  So the conjunction fails Relational Monotonicity, and
with it Lifted Monotonicity.  This holds with or without the timestamp
condition. -/
theorem store_conj_lostUpdate (P : (j : Inp lam) → CH j → Prop) (hP : ∀ j, ¬ P j (serial j))
    (hLU : ∀ j (H : CH j), LostUpdate H → P j H) (htot) :
    ¬ (Conj.conj (store (lam := lam)) (specP P hP) htot).RelMono ∧
      ¬ (Conj.conj (store (lam := lam)) (specP P hP) htot).LiftedMono := by
  let F2 : St Fact := fun x => x = .read 2 tsInit
  have hrow : (Conj.conj (store (lam := lam)) (specP P hP) htot).P i2 F2 := by
    refine ⟨?_, serial i2, ?_, hP i2⟩
    · rintro x rfl; exact i2_ans
    · rintro x rfl
      exact ⟨⟨2, 1, 0, 1, rfl⟩, i2_ver ((serial i2).ok 2 2 1 0 1 rfl)⟩
  have hno : ∀ u, (Conj.conj (store (lam := lam)) (specP P hP) htot).P iJ u → ¬ F2 ≼ u := by
    rintro u ⟨-, H, hF, hPH⟩ hle
    have h2 : H.facts (.read 2 tsInit) := hF _ (hle _ rfl)
    exact hPH (hLU _ H (lu_cycle H h2.2).1)
  have hle : (i2 (lam := lam)) ≼ iJ := le_hJ keep2 hk2
  have hR : ¬ (Conj.conj (store (lam := lam)) (specP P hP) htot).RelMono := fun h => by
    obtain ⟨u, hu, hFu⟩ := h _ _ _ hle hrow
    exact hno u hu hFu
  refine ⟨hR, fun h => ?_⟩
  obtain ⟨u, hu, hall⟩ := h _ _ hle [F2] (by simp) (fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; exact hrow)
  exact hno u hu (hall F2 (by simp))

end HATSpec
end CC
