import CoordCriterion.CAP.AvailabilityFor

/-!
# Strategies that know the participant set (robustness of necessity)

The system model of `CAP/Model.lean` gives a strategy only the participant's
number, its own initial input and its local history (`System.rule`).  Here a
*full-knowledge system* (`KSystem`) gives each strategy also the number of
participants and every participant's initial input.  Every system is one
(`System.toK`, with the same produced histories, `produced_toK`).

The necessity half of Complete CAP for an explicit relation holds for
full-knowledge systems (`consistentOn_of_availabilityFor_K`): its proof
places one solo continuation per participant side by side and uses the
system only through per-participant compliance at a fixed participant set and
fixed initial inputs, which knowledge of that set does not affect.  So the
"no system can" direction does not depend on strategies being ignorant of the
participant set.
-/

namespace CC
namespace CAP

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type}

/-- A system whose strategies see the participant set and all initial inputs. -/
structure KSystem (sp : Spec I O) (D : Type) where
  basis : Commitment sp → Prop
  strat : (n : Nat) → (Fin n → I) → Fin n → List (LEv sp D n) → LEv sp D n → Prop

/-- As `Allowed`. -/
def KAllowed (Sys : KSystem sp D) (n : Nat) (init : Fin n → I) (p : Fin n)
    (pre : List (LEv sp D n)) : LEv sp D n → Prop
  | .inp _ => True
  | .out o => (∀ σ, LRun (canon sp (init p)) pre σ → Exposable σ o ∨ Sys.basis (kcap o)) ∧
      Sys.strat n init p pre (.out o)
  | .commitment γ => (∀ c ∈ γ, Sys.basis c) ∧ Sys.strat n init p pre (.commitment γ)
  | .send j d => Sys.strat n init p pre (.send j d)
  | .recv _ _ _ _ => True

def KProduced (Sys : KSystem sp D) (n : Nat) (init : Fin n → I) (H : History sp D n) : Prop :=
  ∀ p, Compliant (KAllowed Sys n init p) (H p)

/-- Every system is a full-knowledge system. -/
def System.toK (Sys : System sp D) : KSystem sp D := ⟨Sys.basis, Sys.strat⟩

theorem produced_toK (Sys : System sp D) (n : Nat) (init : Fin n → I) (H : History sp D n) :
    KProduced Sys.toK n init H ↔ Produced Sys n init H := by
  have : ∀ p, KAllowed Sys.toK n init p = Allowed Sys n init p := by
    intro p; funext pre e; cases e <;> rfl
  simp only [KProduced, Produced, this]

/-- Availability for `A`, at the end of histories (as `AvailabilityFor`). -/
def KAvailabilityFor (A : Table I O) (Sys : KSystem sp D) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → KProduced Sys n init H → Partitioned H comp →
    ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) (H p) σ →
    ∀ o, σ.R σ.cur o → A σ.cur o →
    ∃ ext : Fin n → List (LEv sp D n),
      WF init (fun q => H q ++ ext q) ∧ KProduced Sys n init (fun q => H q ++ ext q) ∧
      Partitioned (fun q => H q ++ ext q) comp ∧
      (∀ q, comp q ≠ comp p → ext q = []) ∧
      (∀ q j, LEv.inp j ∉ ext q) ∧
      LEv.out o ∈ ext p

/-- The common output extension that Partition Consistency gives (as
`CommonRefinementAtEnd`). -/
def KCommonRefinementAtEnd (Sys : KSystem sp D) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → KProduced Sys n init H → Partitioned H comp →
    ∀ j : I, (∀ p σ, LRun (canon sp (init p)) (H p) σ → σ.cur ≼ j) →
    ∃ u, sp.P j u ∧ ∀ p o, LEv.out o ∈ H p → o ≼ u

theorem availabilityFor_toK {A : Table I O} {Sys : System sp D} :
    KAvailabilityFor A Sys.toK ↔ AvailabilityFor A Sys := by
  simp only [KAvailabilityFor, AvailabilityFor, produced_toK]

theorem commonRefinement_toK {Sys : System sp D} :
    KCommonRefinementAtEnd Sys.toK ↔ CommonRefinementAtEnd Sys := by
  simp only [KCommonRefinementAtEnd, CommonRefinementAtEnd, produced_toK]

/-- **Necessity of Complete CAP for full-knowledge systems.**  If a system
whose strategies know the participant set and all initial inputs keeps `A`
available and the emitted outputs reconcilable, `S` satisfies Lifted
Monotonicity for `A`.  The proof is that of `consistentOn_of_availabilityFor`. -/
theorem consistentOn_of_availabilityFor_K (A : Table I O) (hAS : ∀ i o, A i o → sp.P i o)
    (Sys : KSystem sp D) (hA : KAvailabilityFor A Sys) (hC : KCommonRefinementAtEnd Sys) :
    ConsistentOn sp A := by
  intro rows hrows j hj
  classical
  by_cases hne : rows = []
  · subst hne; obtain ⟨u, hu⟩ := sp.total j; exact ⟨u, hu, by simp⟩
  have hlen : 0 < rows.length := List.length_pos_iff.2 hne
  let N := rows.length + 1
  let init : Fin N → I := fun p => if h : p.val < rows.length then (rows[p.val]'h).1 else j
  let comp : Fin N → Nat := fun p => p.val
  have hcomp2 : ∃ p q : Fin N, comp p ≠ comp q :=
    ⟨⟨0, by omega⟩, ⟨rows.length, by omega⟩, by simp [comp]; omega⟩
  let H0 : History sp D N := fun _ => []
  have hwf0 : WF init H0 :=
    wf_of_ne (fun p => ⟨_, .nil _⟩) (by intro p a q k j d b h; simp [H0] at h)
  have hprod0 : KProduced Sys N init H0 := fun p a e b h => by simp [H0] at h
  have hpart0 : Partitioned H0 comp := ⟨hcomp2, by intro p a q k j d b h; simp [H0] at h⟩
  have hL : ∀ p : Fin N, ∃ L : List (LEv sp D N),
      (∃ τ, LRun (canon sp (init p)) L τ) ∧ (∀ (q : Fin N) k j d, LEv.recv q k j d ∉ L) ∧
      Compliant (KAllowed Sys N init p) L ∧ (∀ j, LEv.inp j ∉ L) ∧
      ∀ h : p.val < rows.length, LEv.out (rows[p.val]'h).2 ∈ L := by
    intro p
    by_cases hp : p.val < rows.length
    · have hinit : init p = (rows[p.val]'hp).1 := by simp [init, hp]
      have hArow : A (rows[p.val]'hp).1 (rows[p.val]'hp).2 := hrows _ (List.getElem_mem ..)
      have ho : (canon sp (init p)).R (canon sp (init p)).cur (rows[p.val]'hp).2 := by
        show sp.P (init p) _ ∧ init p ≼ init p
        rw [hinit]; exact ⟨hAS _ _ hArow, PO.refl _⟩
      have hAo : A (canon sp (init p)).cur (rows[p.val]'hp).2 := by
        show A (init p) _; rw [hinit]; exact hArow
      obtain ⟨ext, hwf', hprod', hpart', _, hnoinp, hγ⟩ :=
        hA N init H0 comp hwf0 hprod0 hpart0 p _ (.nil _) _ ho hAo
      have hH' : H0 p ++ ext p = ext p := by simp [H0]
      refine ⟨ext p, ?_, ?_, ?_, hnoinp p, fun _ => hγ⟩
      · obtain ⟨τ, h⟩ := hwf'.1 p; exact ⟨τ, hH' ▸ h⟩
      · intro q k j d hm
        obtain ⟨a, b, hab⟩ := List.append_of_mem hm
        have hab' : (fun q => H0 q ++ ext q) p = a ++ LEv.recv q k j d :: b := by
          show H0 p ++ ext p = _; rw [hH']; exact hab
        exact (hwf'.2 p a q k j d b hab').1 (Fin.ext (hpart'.2 p a q k j d b hab'))
      · have := hprod' p; simp only [H0, List.nil_append] at this; exact this
    · exact ⟨[], ⟨_, .nil _⟩, by simp, fun a e b h => by simp at h, by simp,
        fun h => absurd h hp⟩
  let Lf : History sp D N := fun p => Classical.choose (hL p)
  have hLs : ∀ p, _ := fun p => Classical.choose_spec (hL p)
  have hnrecv : ∀ (p : Fin N) a (q : Fin N) k (j' : Option I) (d : D) b,
      Lf p ≠ a ++ LEv.recv q k j' d :: b := by
    intro p a q k j' d b h
    have hm : LEv.recv q k j' d ∈ Lf p := by rw [h]; simp
    exact (hLs p).2.1 q k j' d hm
  have hwfc : WF init Lf :=
    wf_of_ne (fun p => (hLs p).1) (fun p a q k j' d b h => absurd h (hnrecv p a q k j' d b))
  have hprodc : KProduced Sys N init Lf := fun p => (hLs p).2.2.1
  have hpartc : Partitioned Lf comp :=
    ⟨hcomp2, fun p a q k j' d b h => absurd h (hnrecv p a q k j' d b)⟩
  have hjall : ∀ p σ, LRun (canon sp (init p)) (Lf p) σ → σ.cur ≼ j := by
    intro p σ h
    rw [lrun_noinp h (hLs p).2.2.2.1]
    show init p ≼ j
    simp only [init]
    split
    · exact hj _ (List.getElem_mem ..)
    · exact PO.refl j
  obtain ⟨u, hu, hall⟩ := hC N init Lf comp hwfc hprodc hpartc j hjall
  refine ⟨u, hu, fun r hr => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  exact hall _ _ ((hLs ⟨i, by omega⟩).2.2.2.2 hi)

/-- The ordinary necessity theorem is the special case `Sys.toK`. -/
theorem consistentOn_of_availabilityFor' (A : Table I O) (hAS : ∀ i o, A i o → sp.P i o)
    (Sys : System sp D) (hA : AvailabilityFor A Sys) (hC : CommonRefinementAtEnd Sys) :
    ConsistentOn sp A :=
  consistentOn_of_availabilityFor_K A hAS Sys.toK (availabilityFor_toK.2 hA)
    (commonRefinement_toK.2 hC)

end CAP
end CC
