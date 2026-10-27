import CoordCriterion.Instances.IOMachineLocal
import CoordCriterion.CompleteCALM.Cofinal

/-!
# A declared specification cofinal in a machine's behaviour (not yet in the paper text)

The induced specification `spec k G` of `Instances/IOMachine.lean` has a
row for every execution of the composed system, including transient
observations.  A designer usually has a smaller *declared* specification
`D` in mind.  This file states two obligations over executions under which
`D` and `spec k G` agree on Lifted Monotonicity, by the cofinality lemma of
`CompleteCALM/Cofinal.lean`.

Input domain of `D`.  `D` is a specification over a declared ordered input
type `J`, related to the occurring inputs `OccInp C P k G` by a map
`φ : OccInp C P k G → J` that is an order embedding (`a ⊑ b ↔ φ a ≼ φ b`).
The common case is `J = OccInp C P k G` with `φ = id` (`MachineCofinalOcc`);
for a single client over FIFO, `J` is payload sequences under prefix and
`φ = word`.  A declared spec over all of `Inp C P` does not fit: it must be
total, so it has rows at inputs no execution produces, and Realizability
fails there.

The obligations (`MachineCofinal k G φ D`):

* (Realizability) every row `(j, o)` of `D` is produced by some execution
  `β` whose input maps to `j` and whose final machine state is observed as
  `o`;
* (Domination) for every execution `β` ending in machine state `q`, some
  `o` in the fiber of `D` at the image of `input β` has `obs q ≼ o`.

Realizability with totality of `D` makes `φ` surjective, so `φ` is an order
isomorphism onto `J`.  Then (`liftedMono_iff_of_machineCofinal`)

  `D.LiftedMono ↔ (spec k G).LiftedMono ↔ ObsConfluent k G`,

and `D` is consistent iff `spec k G` is.

Sanity checks:

* single client, FIFO, stationary deterministic machine: the prefix
  encoding of the receive transitions is cofinal along `word` (its fibers
  are exactly those of `spec`, by `word_fiber_run` and `runSpec_stationary`),
  which re-derives "consistent iff `TransMono`" of `fifo_single_stationary`
  through the bridge (`fifo_stationary_cofinal`,
  `fifo_single_stationary_via_cofinal`);
* `dip`: the declared specification with the single output `2` at every
  occurring input omits the transient observations `1` and `0`, is cofinal
  in `spec k (dip C P)`, and is trivially Lifted Monotone; the bridge gives
  Lifted Monotonicity of `spec k (dip C P)` and confluence of its
  observations (`dip_cofinal`, `dip_liftedMono_via_cofinal`).
-/

namespace CC
namespace IOM
open IOA

variable {C P Q O : Type}

section bridge
variable [PO O] {J : Type} [PO J] (k : ChanKind) (G : Machine C P Q O)

/-- The input of an execution, as an occurring input. -/
def occOfExec {β : List (Act C P O)} {s : (sys (C := C) k G).St}
    (hx : Execution (sys k G) β s) : OccInp C P k G :=
  ⟨input β, β, s, hx, rfl⟩

/-- **Obligations for a declared specification `D` over inputs `J`**, along
an order embedding `φ` of the occurring inputs: every row of `D` is produced
by an execution (Realizability), and every execution's final observation is
dominated by a row of `D` at its input (Domination). -/
structure MachineCofinal (φ : OccInp C P k G → J) (D : Spec J O) : Prop where
  emb : ∀ a b, a ≼ b ↔ φ a ≼ φ b
  real : ∀ j o, D.S j o → ∃ β s, ∃ hx : Execution (sys k G) β s,
    φ (occOfExec k G hx) = j ∧ G.obs (s .mach) = o
  dom : ∀ β s, ∀ hx : Execution (sys k G) β s,
    ∃ o, D.S (φ (occOfExec k G hx)) o ∧ G.obs (s .mach) ≼ o

/-- The obligations, for a declared specification over the occurring
inputs themselves. -/
structure MachineCofinalOcc (D : Spec (OccInp C P k G) O) : Prop where
  real : ∀ h o, D.S h o → ∃ β s, Execution (sys k G) β s ∧ input β = h.val ∧ G.obs (s .mach) = o
  dom : ∀ β s, ∀ hx : Execution (sys k G) β s,
    ∃ o, D.S (occOfExec k G hx) o ∧ G.obs (s .mach) ≼ o

variable {k G}

omit [PO O] in
theorem occOfExec_eq {β : List (Act C P O)} {s : (sys (C := C) k G).St}
    (hx : Execution (sys k G) β s) {h : OccInp C P k G} (hi : input β = h.val) :
    occOfExec k G hx = h := by
  cases h; cases hi; rfl

/-- The execution-level obligations make `D` cofinal in `spec k G` along
`φ`. -/
theorem MachineCofinal.cofinalAlong {φ : OccInp C P k G → J} {D : Spec J O}
    (H : MachineCofinal k G φ D) : CofinalAlong φ D (spec k G) where
  emb := H.emb
  real j o ho := by
    obtain ⟨β, s, hx, hj, ho⟩ := H.real j o ho
    exact ⟨occOfExec k G hx, hj, β, s, hx, rfl, ho⟩
  dom h o ho := by
    obtain ⟨β, s, hx, hi, rfl⟩ := ho
    obtain ⟨u, hu, hle⟩ := H.dom β s hx
    rw [occOfExec_eq hx hi] at hu
    exact ⟨u, hu, hle⟩

theorem MachineCofinalOcc.toMachineCofinal {D : Spec (OccInp C P k G) O}
    (H : MachineCofinalOcc k G D) : MachineCofinal k G id D where
  emb _ _ := Iff.rfl
  real h o ho := by
    obtain ⟨β, s, hx, hi, ho⟩ := H.real h o ho
    exact ⟨β, s, hx, occOfExec_eq hx hi, ho⟩
  dom := H.dom

/-- **Machine bridge.**  If a declared specification `D` (over inputs `J`,
along an order embedding `φ` of the occurring inputs) satisfies
Realizability and Domination over executions, then `D` satisfies Lifted
Monotonicity iff the induced specification does, iff the machine's
observations are confluent across executions; and `D` is consistent iff
the induced specification is. -/
theorem liftedMono_iff_of_machineCofinal {φ : OccInp C P k G → J} {D : Spec J O}
    (H : MachineCofinal k G φ D) :
    (D.LiftedMono ↔ (spec (C := C) k G).LiftedMono) ∧
      (D.LiftedMono ↔ ObsConfluent (C := C) k G) ∧
      (D.Consistent ↔ (spec (C := C) k G).Consistent) := by
  obtain ⟨e1, e2⟩ := liftedMono_iff_of_cofinalAlong H.cofinalAlong
  exact ⟨e1, e1.trans (confluent_iff_liftedMono k G).1.symm, e2⟩

/-- The machine bridge for a declared specification over the occurring
inputs. -/
theorem liftedMono_iff_of_machineCofinalOcc {D : Spec (OccInp C P k G) O}
    (H : MachineCofinalOcc k G D) :
    (D.LiftedMono ↔ (spec (C := C) k G).LiftedMono) ∧
      (D.LiftedMono ↔ ObsConfluent (C := C) k G) ∧
      (D.Consistent ↔ (spec (C := C) k G).Consistent) :=
  liftedMono_iff_of_machineCofinal H.toMachineCofinal

end bridge

/-! ### Sanity check: single client, FIFO, stationary machine -/

section fifo
variable [PO O] {G : Machine Unit P Q O}

/-- For a stationary machine with a single client over FIFO, the prefix
encoding of its receive transitions is cofinal in the induced
specification along `word`. -/
theorem fifo_stationary_cofinal (hs : Stationary G) :
    MachineCofinal .fifo G word (SM.induced (recvSM G) (SM.prefixAbs P)) := by
  have hf : ∀ h o, (spec .fifo G).S h o ↔
      (SM.induced (recvSM G) (SM.prefixAbs P)).S (word h) o := fun h o =>
    (word_fiber_run h o).trans (runSpec_stationary hs _ _)
  refine ⟨word_le_iff, fun w o ho => ?_, fun β s hx => ?_⟩
  · obtain ⟨h, rfl⟩ := word_surj (G := G) w
    obtain ⟨β, s, hx, hi, ho'⟩ := (hf h o).2 ho
    exact ⟨β, s, hx, by rw [occOfExec_eq hx hi], ho'⟩
  · exact ⟨_, (hf _ _).1 ⟨β, s, hx, rfl, rfl⟩, PO.refl _⟩

/-- `fifo_single_stationary`'s consistency claim, re-derived through the
machine bridge. -/
theorem fifo_single_stationary_via_cofinal (hs : Stationary G)
    (hd : SM.Deterministic (recvSM G)) :
    (spec (C := Unit) .fifo G).Consistent ↔ SM.TransMono (recvSM G) :=
  (liftedMono_iff_of_machineCofinal (fifo_stationary_cofinal hs)).2.2.symm.trans
    (SM.induced_prefix (recvSM G) hd).2

end fifo

/-! ### Sanity check: the transient dip -/

section dip
attribute [local instance] natPO

/-- The declared specification of `dip`: at every occurring input the only
output is `2`.  It omits the transient observations `1` and `0`. -/
def dipDecl (C P : Type) (k : ChanKind) : Spec (OccInp C P k (dip C P)) Nat where
  S _ o := o = 2
  total _ := ⟨2, rfl⟩

theorem dipDecl_liftedMono (k : ChanKind) : (dipDecl C P k).LiftedMono :=
  fun _ _ _ _ _ hA => ⟨2, rfl, fun x hx => by
    have : x = 2 := hA x hx
    exact this ▸ Nat.le_refl 2⟩

/-- `dipDecl` is cofinal in the induced specification of `dip`. -/
theorem dip_cofinal [DecidableEq C] (k : ChanKind) :
    MachineCofinalOcc k (dip C P) (dipDecl C P k) := by
  refine ⟨fun h o ho => ?_, fun β s _ => ⟨2, rfl, ?_⟩⟩
  · obtain ⟨β, s, hx, hi⟩ := h.occ
    have hr : Reach k (dip C P) β (toFlat s) := ⟨s, hx, rfl⟩
    have hm : MRun (dip C P) (toFlat s).q [] .c := by
      cases (toFlat s).q with
      | a => exact .int (Or.inr (Or.inl ⟨rfl, rfl⟩)) (.int (Or.inr (Or.inr ⟨rfl, rfl⟩)) (.nil _))
      | b => exact .int (Or.inr (Or.inr ⟨rfl, rfl⟩)) (.nil _)
      | c => exact .nil _
    obtain ⟨γ, f', ⟨s', hx', hs'⟩, hi', hq⟩ := extend_int hm hr rfl
    refine ⟨β ++ γ, s', hx', hi'.trans hi, ?_⟩
    have : s' .mach = Dip.c := by rw [← hq, ← hs']; rfl
    rw [ho]; show Dip.obs (s' .mach) = 2; rw [this]; rfl
  · show Dip.obs (s .mach) ≤ 2
    cases s .mach <;> decide

/-- Lifted Monotonicity and confluence of `dip`, through the machine bridge
from its declared specification. -/
theorem dip_liftedMono_via_cofinal [DecidableEq C] (k : ChanKind) :
    (spec (C := C) k (dip C P)).LiftedMono ∧ ObsConfluent (C := C) k (dip C P) := by
  obtain ⟨e1, e2, _⟩ := liftedMono_iff_of_machineCofinalOcc (dip_cofinal (C := C) (P := P) k)
  exact ⟨e1.1 (dipDecl_liftedMono k), e2.1 (dipDecl_liftedMono k)⟩

end dip

end IOM
end CC
