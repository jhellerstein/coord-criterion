import CoordCriterion.Appendix.DeploymentExamples

/-!
# Independent-product frontier (Appendix `sec:frontiers`, "Preserving independent local choices")

Theorem `thm:product-frontier` with per-participant value posets `W p`, over
the deployment notions of `CC.Deploy`:

* partial tuples `PTd`, the product interface `prodTable`/`prodSpec`, the
  owner deployment `ownerD`; `product_common`, `product_monoAcross` (part 1),
  `product_confluent`;
* normalized strengthenings `NormStr`, local conservativity and strictness;
  `strengthening_not_monoAcross` (part 2);
* the "deployment is essential" remark, in the corrected form "no common
  upper bound in `V_p(i)`" (`product_not_liftedMono`,
  `product_full_not_monoAcross`), and a counterexample to the literal wording
  (`tri_incomparable`, `tri_liftedMono`);
* Example `product-config-example` with an arbitrary input poset
  (`cfg_agree_not_monoAcross`; the sole-owner deployments
  `cfg_agree_sole_owner`, `cfg_agree_single_authority`), and the fact
  that the product interface does not satisfy the sufficient condition of
  `Appendix/DeploymentExamples.lean` (`cfg_product_conflict`).

Modeling choices: coordinates are the participants `Fin n` (the paper's
`∏_{p∈P} V_p(i)`), coordinate `p` ranging over its own poset `W p`; partial
tuples are ordered coordinate-wise with `none` (`⊥`) below every value.
Maximality of complete views is used only in the weaker form "the views
`V_p(i)` at one input form an antichain" (`Antichain`).
-/

namespace CC
namespace Deploy

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CC.CAP (step_input_inv step_output_inv)

/-! ## Part B: Theorem `thm:product-frontier`, per-participant posets -/

section Product
variable {I : Type} [PO I] {n : Nat} {W : Fin n → Type} [∀ p, PO (W p)]

/-- `⊥` below every value. -/
def OLe {β : Type} [PO β] : Option β → Option β → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => a ≼ b

/-- Partial tuples: coordinate `p` is a value of `W p` or `⊥` (`none`). -/
structure PTd (W : Fin n → Type) where
  t : (p : Fin n) → Option (W p)

instance : PO (PTd W) where
  le x y := ∀ p, OLe (x.t p) (y.t p)
  refl x p := by
    cases x.t p with
    | none => trivial
    | some a => exact PO.refl a
  trans {x y z} h1 h2 p := by
    have a1 := h1 p
    have a2 := h2 p
    revert a1 a2
    cases x.t p <;> cases y.t p <;> cases z.t p <;> simp [OLe] <;> exact PO.trans
  antisymm {x y} h1 h2 := by
    have : x.t = y.t := by
      funext p
      have a1 := h1 p
      have a2 := h2 p
      revert a1 a2
      cases x.t p <;> cases y.t p <;> simp [OLe]
      exact PO.antisymm
    cases x; cases y; simp only at this; subst this; rfl

/-- `x` is a restriction of the complete tuple `y`. -/
def Restr (x : PTd W) (y : (p : Fin n) → W p) : Prop :=
  ∀ p, x.t p = none ∨ x.t p = some (y p)

/-- The product interface. -/
def prodTable (V : (p : Fin n) → I → W p → Prop) : Table I (PTd W) :=
  fun i x => ∃ y : (p : Fin n) → W p, (∀ p, V p i (y p)) ∧ Restr x y

def prodSpec (V : (p : Fin n) → I → W p → Prop) (hne : ∀ p i, ∃ v, V p i v) :
    Spec I (PTd W) where
  S := prodTable V
  total i := ⟨⟨fun _ => none⟩, fun p => Classical.choose (hne p i),
    fun p => Classical.choose_spec (hne p i), fun _ => Or.inl rfl⟩

/-- Views continue. -/
def Continue (V : (p : Fin n) → I → W p → Prop) : Prop :=
  ∀ p i j v, i ≼ j → V p i v → ∃ w, V p j w ∧ v ≼ w

def Antichain (V : (p : Fin n) → I → W p → Prop) : Prop :=
  ∀ p i v w, V p i v → V p i w → v ≼ w → v = w

/-- The owner deployment: `p` emits exactly the rows whose tuple is `⊥`
outside coordinate `p`. -/
def ownerD (sp : Spec I (PTd W)) : Deployment sp n where
  A p i x := sp.S i x ∧ ∀ q, q ≠ p → x.t q = none
  sub _ _ _ h := h.1

/-- Every owner-authorized family (separable or not) has a common expansion
at every common expansion `j` of its current inputs. -/
theorem product_common (V : (p : Fin n) → I → W p → Prop) (hne : ∀ p i, ∃ v, V p i v)
    (hc : Continue V) (F : Family (prodSpec V hne) n)
    (hA : Authorized (ownerD (prodSpec V hne)) F) (j : I) (hj : UB F j) :
    ∃ u, (prodSpec V hne).S j u ∧ ∀ p r, Emits F p r → r.2 ≼ u := by
  have key : ∀ p, ∃ w, V p j w ∧ ∀ r, Emits F p r → ∀ v, r.2.t p = some v → v ≼ w := by
    intro p
    cases hp : F p with
    | none =>
      obtain ⟨w, hw⟩ := hne p j
      exact ⟨w, hw, fun r hr => absurd hr (emits_none hp)⟩
    | some m =>
      obtain ⟨u, hu⟩ := m.fin.hasCur
      have hres := (m.residual _ _).1 hu
      obtain ⟨y, hy, hyu⟩ := hres.1
      obtain ⟨w, hw, hyw⟩ := hc p _ _ _ (hj p m hp) (hy p)
      refine ⟨w, hw, fun r hr v hv => ?_⟩
      have hle : r.2 ≼ u := hres.2.2 r ((emits_some hp).1 hr)
      have h1 : OLe (r.2.t p) (u.t p) := hle p
      rw [hv] at h1
      rcases hyu p with h0 | h0 <;> rw [h0] at h1
      · exact False.elim h1
      · exact PO.trans h1 hyw
  let w : (p : Fin n) → W p := fun p => Classical.choose (key p)
  have hw : ∀ p, V p j (w p) ∧ ∀ r, Emits F p r → ∀ v, r.2.t p = some v → v ≼ w p :=
    fun p => Classical.choose_spec (key p)
  refine ⟨⟨fun p => some (w p)⟩, ⟨w, fun p => (hw p).1, fun _ => Or.inr rfl⟩, ?_⟩
  intro q r hr p
  show OLe (r.2.t p) (some (w p))
  cases h : r.2.t p with
  | none => trivial
  | some v =>
    have hpq : p = q := Classical.byContradiction fun hpq => by
      have := (hA q r hr).2 p hpq; rw [h] at this; cases this
    subst hpq
    exact (hw p).2 r hr v h

/-- **Theorem `thm:product-frontier` (1)**. -/
theorem product_monoAcross (V : (p : Fin n) → I → W p → Prop) (hne : ∀ p i, ∃ v, V p i v)
    (hc : Continue V) : MonoAcrossPartitions (ownerD (prodSpec V hne)) :=
  fun _ _ F hA _ j hj => product_common V hne hc F hA j hj

/-- ... so (Prop. `thm:complete-cap-deployment`) every separable run family
is confluent at every common expansion of its current inputs. -/
theorem product_confluent (V : (p : Fin n) → I → W p → Prop) (hne : ∀ p i, ∃ v, V p i v)
    (hc : Continue V) : PartitionConfluent (ownerD (prodSpec V hne)) :=
  (partition_compatibility_confluent _).2 (product_monoAcross V hne hc)

/-- A normalized strengthening. -/
structure NormStr (V : (p : Fin n) → I → W p → Prop) where
  sel : I → ((p : Fin n) → W p) → Prop
  sub : ∀ i y, sel i y → ∀ p, V p i (y p)

def NormStr.table {V : (p : Fin n) → I → W p → Prop} (T : NormStr V) : Table I (PTd W) :=
  fun i x => ∃ y, T.sel i y ∧ Restr x y

def NormStr.LocCons {V : (p : Fin n) → I → W p → Prop} (T : NormStr V) : Prop :=
  ∀ i p v, V p i v → ∃ z, T.sel i z ∧ z p = v

def NormStr.Strict {V : (p : Fin n) → I → W p → Prop} (T : NormStr V) : Prop :=
  ∃ i x, prodTable V i x ∧ ¬ T.table i x

/-- `e_p`: the restriction of `y` to coordinate `p`. -/
def restrictTo (y : (p : Fin n) → W p) (p : Fin n) : PTd W :=
  ⟨fun q => if q = p then some (y q) else none⟩

/-- **Theorem `thm:product-frontier` (2)** (with `|P| ≥ 2`): no strict,
normalized, locally conservative strengthening is monotone across partitions
under its owner deployment.  `sp` is any specification whose table is that of
`T`. -/
theorem strengthening_not_monoAcross (hn : 2 ≤ n) (V : (p : Fin n) → I → W p → Prop)
    (hAC : Antichain V) (T : NormStr V) (sp : Spec I (PTd W))
    (hsp : ∀ i x, sp.S i x ↔ T.table i x) (hLC : T.LocCons) (hst : T.Strict) :
    ¬ MonoAcrossPartitions (ownerD sp) := by
  intro hM
  obtain ⟨i, x, ⟨y, hyV, hxy⟩, hnot⟩ := hst
  have hny : ¬ T.sel i y := fun hs => hnot ⟨y, hs, hxy⟩
  have hsing : ∀ p, sp.S i (restrictTo y p) := by
    intro p
    obtain ⟨z, hz, hzp⟩ := hLC i p (y p) (hyV p)
    refine (hsp _ _).2 ⟨z, hz, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq; right; simp [restrictTo, hzp]
    · left; simp [restrictTo, hq]
  let p0 : Fin n := ⟨0, by omega⟩
  let p1 : Fin n := ⟨1, by omega⟩
  let F : Family sp n := fun p => some (oneShot sp i (restrictTo y p) (hsing p))
  have hem : ∀ p r, Emits F p r ↔ r = (i, restrictTo y p) := by
    intro p r
    rw [emits_some (rfl : F p = _)]; simp
  have hAuth : Authorized (ownerD sp) F := by
    intro p r hr
    rw [hem] at hr; subst hr
    exact ⟨hsing p, fun q hq => by simp [restrictTo, hq]⟩
  have hSep : Separable F (fun p => p.val) :=
    Or.inl ⟨p0, p1, _, _, (hem _ _).2 rfl, (hem _ _).2 rfl, by simp [p0, p1]⟩
  have hub : UB F i := by
    intro p m hm
    cases hm
    exact PO.refl i
  obtain ⟨u, hu, hall⟩ := hM _ ⟨p0, p1, by simp [p0, p1]⟩ F hAuth hSep i hub
  obtain ⟨z, hz, hzu⟩ := (hsp _ _).1 hu
  have hyz : ∀ p, y p = z p := by
    intro p
    have h1 : OLe ((restrictTo y p).t p) (u.t p) := hall p _ ((hem _ _).2 rfl) p
    have e : (restrictTo y p).t p = some (y p) := by simp [restrictTo]
    rw [e] at h1
    rcases hzu p with h0 | h0 <;> rw [h0] at h1
    · exact False.elim h1
    · exact hAC p i _ _ (hyV p) (T.sub i z hz p) h1
  exact hny (by have : y = z := funext hyz; rw [this]; exact hz)

/-! ### "The deployment is essential" -/

/-- The single-coordinate tuple `p ↦ v`. -/
def single1 (p : Fin n) (v : W p) : PTd W :=
  ⟨fun q => if h : q = p then some (h ▸ v) else none⟩

theorem single1_row (V : (p : Fin n) → I → W p → Prop) (hne : ∀ p i, ∃ v, V p i v)
    {p : Fin n} {i : I} {v : W p} (hv : V p i v) : prodTable V i (single1 p v) := by
  classical
  let y : (q : Fin n) → W q := fun q => if h : q = p then h ▸ v else Classical.choose (hne q i)
  refine ⟨y, fun q => ?_, fun q => ?_⟩
  · by_cases h : q = p
    · subst h; simp [y]; exact hv
    · simp [y, h]; exact Classical.choose_spec (hne q i)
  · by_cases h : q = p
    · subst h; right; simp [single1, y]
    · left; simp [single1, h]

theorem single1_le {p : Fin n} {v : W p} {u : PTd W} (h : single1 p v ≼ u) :
    ∃ t, u.t p = some t ∧ v ≼ t := by
  have h1 : OLe ((single1 p v).t p) (u.t p) := h p
  have e : (single1 p v).t p = some v := by simp [single1]
  rw [e] at h1
  cases hu : u.t p with
  | none => rw [hu] at h1; exact False.elim h1
  | some t => rw [hu] at h1; exact ⟨t, rfl, h1⟩

/-- Corrected remark: if some `V_p(i)` has two views with no common upper
bound *in `V_p(i)`* (e.g. two distinct views of an antichain), the product
interface is not monotone. -/
theorem product_not_liftedMono (V : (p : Fin n) → I → W p → Prop) (hne : ∀ p i, ∃ v, V p i v)
    {p : Fin n} {i : I} {v w : W p} (hv : V p i v) (hw : V p i w)
    (hnb : ¬ ∃ t, V p i t ∧ v ≼ t ∧ w ≼ t) : ¬ (prodSpec V hne).LiftedMono := by
  intro h
  obtain ⟨u, ⟨y, hy, hyu⟩, hall⟩ := h i i (PO.refl i) [single1 p v, single1 p w] (by simp)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl
        · exact single1_row V hne hv
        · exact single1_row V hne hw)
  obtain ⟨t, ht, hvt⟩ := single1_le (hall (single1 p v) (by simp))
  obtain ⟨t', ht', hwt⟩ := single1_le (hall (single1 p w) (by simp))
  rw [ht] at ht'; cases ht'
  rcases hyu p with h0 | h0 <;> rw [h0] at ht
  · cases ht
  · cases ht; exact hnb ⟨y p, hy p, hvt, hwt⟩

/-- ... and with `A_p = S` for every participant (`|P| ≥ 2`) it is not
monotone across partitions. -/
theorem product_full_not_monoAcross (hn : 2 ≤ n) (V : (p : Fin n) → I → W p → Prop)
    (hne : ∀ p i, ∃ v, V p i v) (Dp : Deployment (prodSpec V hne) n)
    (hA : ∀ p, Dp.A p = (prodSpec V hne).S)
    {p : Fin n} {i : I} {v w : W p} (hv : V p i v) (hw : V p i w)
    (hnb : ¬ ∃ t, V p i t ∧ v ≼ t ∧ w ≼ t) : ¬ MonoAcrossPartitions Dp :=
  fun h => product_not_liftedMono V hne hv hw hnb ((full_deployment_iff hn Dp hA).1 h)

end Product

/-! ### Counterexample to the literal remark: incomparable views with a
common upper bound in `V_p(i)` -/

section Tri
open CC.Front (One)

/-- `lo1, lo2 < t`. -/
inductive Tri | lo1 | lo2 | t

instance : PO Tri where
  le x y := x = y ∨ y = .t
  refl _ := Or.inl rfl
  trans {x y z} h1 h2 := by cases x <;> cases y <;> cases z <;> simp_all
  antisymm {x y} h1 h2 := by cases x <;> cases y <;> simp_all

def triV : (p : Fin 2) → One → Tri → Prop := fun _ _ _ => True

theorem triV_ne : ∀ (p : Fin 2) (i : One), ∃ x, triV p i x := fun _ _ => ⟨.t, trivial⟩

/-- `lo1` and `lo2` are two incomparable views in `V_0(i)`. -/
theorem tri_incomparable : triV 0 .pt .lo1 ∧ triV 0 .pt .lo2 ∧ ¬ (Tri.lo1 ≼ Tri.lo2) ∧
    ¬ (Tri.lo2 ≼ Tri.lo1) :=
  ⟨trivial, trivial, by simp [PO.le], by simp [PO.le]⟩

/-- ... yet the product interface is monotone: every row lies below `(t,t)`. -/
theorem tri_liftedMono : (prodSpec (W := fun _ => Tri) triV triV_ne).LiftedMono := by
  intro i j _ X _ _
  refine ⟨⟨fun _ => some .t⟩, ⟨fun _ => .t, fun _ => trivial, fun _ => Or.inr rfl⟩, ?_⟩
  intro x _ p
  show OLe (x.t p) (some Tri.t)
  cases x.t p with
  | none => trivial
  | some a => exact Or.inr rfl

end Tri

/-! ### The configuration example, arbitrary input poset -/

section Config
variable {I : Type} [PO I]
open CC.Front (Disc)

def cfgV (I : Type) : (p : Fin 2) → I → Disc Bool → Prop := fun _ _ _ => True

theorem cfgV_ne : ∀ (p : Fin 2) (i : I), ∃ v, cfgV I p i v := fun _ _ => ⟨⟨false⟩, trivial⟩

theorem cfgV_antichain : Antichain (W := fun _ => Disc Bool) (cfgV I) :=
  fun _ _ _ _ _ _ h => h

/-- Agreement keeps `(0,0)` and `(1,1)`. -/
def agree (I : Type) [PO I] : NormStr (W := fun _ => Disc Bool) (cfgV I) where
  sel _ y := y 0 = y 1
  sub _ _ _ _ := trivial

def agreeSpec (I : Type) [PO I] : Spec I (PTd (fun _ : Fin 2 => Disc Bool)) where
  S := (agree I).table
  total _ := ⟨⟨fun _ => none⟩, fun _ => ⟨false⟩, rfl, fun _ => Or.inl rfl⟩

theorem agree_locCons : (agree I).LocCons := fun _ _ v _ => ⟨fun _ => v, rfl, rfl⟩

theorem agree_strict (i : I) : (agree I).Strict := by
  let y : (p : Fin 2) → Disc Bool := fun p => ⟨p.val == 1⟩
  refine ⟨i, ⟨fun p => some (y p)⟩, ⟨y, fun _ => trivial, fun _ => Or.inr rfl⟩, ?_⟩
  rintro ⟨z, hz, hr⟩
  have e : ∀ p, z p = y p := by
    intro p
    rcases hr p with h | h
    · cases h
    · exact (Option.some.inj h).symm
  have : y 0 = y 1 := (e 0).symm.trans (hz.trans (e 1))
  simp [y] at this

/-- By part (2), agreement is not monotone across partitions under its owner
deployment. -/
theorem cfg_agree_not_monoAcross (i : I) : ¬ MonoAcrossPartitions (ownerD (agreeSpec I)) :=
  strengthening_not_monoAcross (by decide) (cfgV I) cfgV_antichain (agree I) (agreeSpec I)
    (fun _ _ => Iff.rfl) agree_locCons (agree_strict i)

/-- If participant `0` may emit every row and participant `1` none (a
single-authority deployment), agreement is monotone across partitions. -/
def agreeSingleD (I : Type) [PO I] : Deployment (agreeSpec I) 2 where
  A p i x := p = 0 ∧ (agreeSpec I).S i x
  sub _ _ _ h := h.2

theorem cfg_agree_single_authority : MonoAcrossPartitions (agreeSingleD I) :=
  (single_authority_iff (by decide) (agreeSingleD I) 0 (fun q hq _ _ h => hq h.1)).2
    fun _ x hx _ _ => ⟨x, hx.2, PO.refl x⟩

/-- The empty partial tuple `⊥`, below every partial tuple. -/
def ptEmpty : PTd (fun _ : Fin 2 => Disc Bool) := ⟨fun _ => none⟩

theorem ptEmpty_le (x : PTd (fun _ : Fin 2 => Disc Bool)) : ptEmpty ≼ x := fun _ => trivial

/-- One participant owns both coordinates: participant `0` may emit every
row of agreement, participant `1` only the empty tuple. -/
def agreeSoleOwnerD (I : Type) [PO I] : Deployment (agreeSpec I) 2 where
  A p i x := (agreeSpec I).S i x ∧ (p = 1 → x = ptEmpty)
  sub _ _ _ h := h.1

/-- Agreement is monotone across partitions under `agreeSoleOwnerD`: the
residual output of participant `0`'s run refines all its rows, every output of
participant `1` is `⊥`, and agreement does not depend on the input. -/
theorem cfg_agree_sole_owner : MonoAcrossPartitions (agreeSoleOwnerD I) := by
  intro comp _ F hA _ j _
  cases h0 : F 0 with
  | none =>
    refine ⟨ptEmpty, ⟨fun _ => ⟨false⟩, rfl, fun _ => Or.inl rfl⟩, fun p r hr => ?_⟩
    have hp : p = 1 := by
      revert hr; refine Fin.cases ?_ (fun k => ?_) p
      · exact fun hr => absurd hr (emits_none h0)
      · intro _; have := k.isLt; ext; simp
    rw [(hA p r hr).2 hp]; exact ptEmpty_le _
  | some m =>
    obtain ⟨u, hu⟩ := m.fin.hasCur
    have hres := (m.residual _ _).1 hu
    obtain ⟨y, hy, hyu⟩ := hres.1
    refine ⟨u, ⟨y, hy, hyu⟩, fun p r hr => ?_⟩
    by_cases hp : p = 1
    · rw [(hA p r hr).2 hp]; exact ptEmpty_le _
    · have hp0 : p = 0 := by
        revert hp; refine Fin.cases ?_ (fun k => ?_) p
        · exact fun _ => rfl
        · intro hk; exfalso; apply hk; have := k.isLt; ext; simp
      subst hp0
      exact hres.2.2 r ((emits_some h0).1 hr)

/-- The product interface does not satisfy the sufficient condition stated
after the leader example: three authorized rows, `e_0(0)`, `e_0(1)`, `e_1(0)`,
lack a common expansion but are authorized to two participants. -/
theorem cfg_product_conflict (i : I) :
    let sp := prodSpec (W := fun _ => Disc Bool) (cfgV I) cfgV_ne
    let E : List (I × PTd (fun _ : Fin 2 => Disc Bool)) :=
      [(i, single1 0 ⟨false⟩), (i, single1 0 ⟨true⟩), (i, single1 1 ⟨false⟩)]
    (∀ r ∈ E, ∃ p, (ownerD sp).A p r.1 r.2) ∧
      (¬ ∃ u, sp.S i u ∧ ∀ r ∈ E, r.2 ≼ u) ∧
      ¬ ∃ p, ∀ r ∈ E, ∀ q, (ownerD sp).A q r.1 r.2 → q = p := by
  intro sp E
  have hrow : ∀ (p : Fin 2) (v : Disc Bool), (ownerD sp).A p i (single1 p v) := by
    intro p v
    refine ⟨single1_row (W := fun _ => Disc Bool) (cfgV I) cfgV_ne trivial, fun q hq => ?_⟩
    simp [single1, hq]
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    simp [E] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨0, hrow 0 _⟩
    · exact ⟨0, hrow 0 _⟩
    · exact ⟨1, hrow 1 _⟩
  · rintro ⟨u, _, hall⟩
    obtain ⟨t, ht, h1⟩ := single1_le (hall (i, single1 0 ⟨false⟩) (by simp [E]))
    obtain ⟨t', ht', h2⟩ := single1_le (hall (i, single1 0 ⟨true⟩) (by simp [E]))
    rw [ht] at ht'; cases ht'
    have := h1.trans h2.symm
    cases this
  · rintro ⟨p, hp⟩
    have h0 := hp (i, single1 0 ⟨false⟩) (by simp [E]) 0 (hrow 0 ⟨false⟩)
    have h1 := hp (i, single1 1 ⟨false⟩) (by simp [E]) 1 (hrow 1 ⟨false⟩)
    exact absurd (h0.trans h1.symm) (by decide)

end Config
end Deploy
end CC
