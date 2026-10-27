import CoordCriterion.Instances.IOMachine
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
  observations (`dip_cofinal`, `dip_liftedMono_via_cofinal`).  `dip` takes
  an internal step that lowers the observation, and a later one that raises
  it above everything; internal steps extend an execution without changing
  its input (`extend_int`).

Testing side: a violation of Lifted Monotonicity is witnessed by finitely
many executions and one execution `β` whose input expands theirs, such that
no execution with the input of `β` refines them all
(`not_liftedMono_iff_witness`).  The last clause quantifies over all
executions with that input.  It is implied by a check over the machine
automaton's own runs on arrival orders of that input
(`not_liftedMono_of_machine_cert`, by `fiber_sub_run`), or over any finite list
of values containing the fiber (`not_liftedMono_of_fiber_list`).
-/

namespace CC
namespace IOM
open IOA

variable {C P Q O : Type}

/-! ### Internal steps of the machine -/

/-- One internal step of the machine: an output to some client, or an
internal action. -/
def IStep (G : Machine C P Q O) (q q' : Q) : Prop := (∃ c o, G.out q c o q') ∨ G.tau q q'

/-- `MRun G q w q'`: the machine goes from `q` to `q'` receiving the payloads
`w` in order, interleaved with internal steps.  `MRun G q [] q'` is a run of
internal steps only. -/
inductive MRun (G : Machine C P Q O) : Q → List P → Q → Prop where
  | nil (q : Q) : MRun G q [] q
  | int {q q1 q2 : Q} {w : List P} : IStep G q q1 → MRun G q1 w q2 → MRun G q w q2
  | recv {q q1 q2 : Q} {p : P} {w : List P} : G.recv q p q1 → MRun G q1 w q2 →
      MRun G q (p :: w) q2

/-! ### Extension by internal steps -/

section extend
variable [DecidableEq C] {k : ChanKind} {G : Machine C P Q O}

omit [DecidableEq C] in
/-- Appending an internal step does not change the input. -/
theorem input_snoc_tau (β : List (Act C P O)) : input (β ++ [.tau]) = input β := by
  have hs : ∀ i e, SendAt (β ++ [.tau]) i e ↔ SendAt β i e := fun _ _ => sendAt_snoc nofun
  have hr : ∀ e, Act.recv e ∈ β ++ [.tau] ↔ Act.recv e ∈ β := by simp
  refine Inp.ext' (funext fun e => propext (hr e)) (funext fun a => funext fun b => propext ?_)
  constructor
  · rintro ⟨⟨ha, hb⟩, i, j, hi, hj, hij⟩
    have hj' := (hs j b).1 hj
    exact ⟨⟨(hr a).1 ha, (hr b).1 hb⟩, i, j, (hs i a).1 hi, hj',
      (hb_append (sendAt_lt hj')).1 hij⟩
  · rintro ⟨⟨ha, hb⟩, i, j, hi, hj, hij⟩
    exact ⟨⟨(hr a).2 ha, (hr b).2 hb⟩, i, j, (hs i a).2 hi, (hs j b).2 hj,
      (hb_append (sendAt_lt hj)).2 hij⟩

/-- **Extension by internal steps.**  Internal steps of the machine extend
an execution without changing its input. -/
theorem extend_int {q q' : Q} (hm : MRun G q [] q') :
    ∀ {β : List (Act C P O)} {f : Flat C P Q}, Reach k G β f → f.q = q →
      ∃ γ f', Reach k G (β ++ γ) f' ∧ input (β ++ γ) = input β ∧ f'.q = q' := by
  generalize hw : ([] : List P) = w at hm
  induction hm with
  | nil => intro β f hr hq; exact ⟨[], f, by simpa using hr, by simp, hq⟩
  | @int q q1 _ _ hs _ ih =>
    intro β f hr hq
    rcases hs with ⟨c, o, ho⟩ | ht
    · have hr1 : Reach k G (β ++ [.out c o]) ⟨q1, f.cnt, f.ch⟩ :=
        reach_snoc.2 ⟨f, hr, FStep.out f c o q1 (hq ▸ ho)⟩
      obtain ⟨γ, f', hf', hi, hq'⟩ := ih hw hr1 rfl
      refine ⟨.out c o :: γ, f', by simpa using hf', ?_, hq'⟩
      have : β ++ Act.out c o :: γ = (β ++ [.out c o]) ++ γ := by simp
      rw [this, hi, input_snoc_out]
    · have hr1 : Reach k G (β ++ [.tau]) ⟨q1, f.cnt, f.ch⟩ :=
        reach_snoc.2 ⟨f, hr, FStep.tau f q1 (hq ▸ ht)⟩
      obtain ⟨γ, f', hf', hi, hq'⟩ := ih hw hr1 rfl
      refine ⟨.tau :: γ, f', by simpa using hf', ?_, hq'⟩
      have : β ++ Act.tau :: γ = (β ++ [.tau]) ++ γ := by simp
      rw [this, hi, input_snoc_tau]
  | recv _ _ _ => cases hw

end extend

/-! ### Testing: finite witnesses of a violation -/

section testing
variable [PO O] (k : ChanKind) (G : Machine C P Q O)

/-- **A violation is witnessed by finitely many executions and one input.**
Lifted Monotonicity fails iff there are finitely many executions `βᵣ` and an
execution `β` whose input expands each of theirs, such that no execution
with the input of `β` ends with an observation refining every `βᵣ`'s.  The
last clause ranges over all executions with that input. -/
theorem not_liftedMono_iff_witness :
    ¬ (spec (C := C) k G).LiftedMono ↔
      ∃ fam : List (List (Act C P O) × (sys (C := C) k G).St),
        (∀ r ∈ fam, Execution (sys k G) r.1 r.2) ∧
        ∃ β s, Execution (sys k G) β s ∧ (∀ r ∈ fam, input r.1 ≼ input β) ∧
          ∀ β' s', Execution (sys k G) β' s' → input β' = input β →
            ∃ r ∈ fam, ¬ G.obs (r.2 .mach) ≼ G.obs (s' .mach) := by
  rw [← (confluent_iff_liftedMono k G).1]
  constructor
  · intro hn
    refine Classical.byContradiction fun hne => hn ?_
    intro fam hfam β s hx hle
    refine Classical.byContradiction fun hno => hne ⟨fam, hfam, β, s, hx, hle, ?_⟩
    intro β' s' hx' hi'
    refine Classical.byContradiction fun hall => hno ⟨β', s', hx', hi', fun r hr => ?_⟩
    exact Classical.byContradiction fun h => hall ⟨r, hr, h⟩
  · rintro ⟨fam, hfam, β, s, hx, hle, hno⟩ hO
    obtain ⟨β', s', hx', hi', hall⟩ := hO fam hfam β s hx hle
    obtain ⟨r, hr, hn⟩ := hno β' s' hx' hi'
    exact hn (hall r hr)

/-- **A finite list containing the fiber suffices.**  If every execution
with the input of `β` ends with an observation in the list `L`, and every
element of `L` fails to refine some `βᵣ`'s observation, Lifted Monotonicity
fails. -/
theorem not_liftedMono_of_fiber_list
    (fam : List (List (Act C P O) × (sys (C := C) k G).St))
    (hfam : ∀ r ∈ fam, Execution (sys k G) r.1 r.2) {β : List (Act C P O)}
    {s : (sys (C := C) k G).St} (hx : Execution (sys k G) β s)
    (hle : ∀ r ∈ fam, input r.1 ≼ input β) (L : List O)
    (hL : ∀ β' s', Execution (sys (C := C) k G) β' s' → input β' = input β → G.obs (s' .mach) ∈ L)
    (hcert : ∀ u ∈ L, ∃ r ∈ fam, ¬ G.obs (r.2 .mach) ≼ u) :
    ¬ (spec (C := C) k G).LiftedMono :=
  (not_liftedMono_iff_witness k G).2 ⟨fam, hfam, β, s, hx, hle, fun β' s' hx' hi' =>
    hcert _ (hL β' s' hx' hi')⟩

/-- **A check over the machine's own runs suffices.**  If every run of the
machine automaton that receives the events of `input β`, each once, in some
order (for FIFO, a linear extension of the input order), interleaved with
any internal and output steps, ends with an observation that fails to refine
some `βᵣ`'s, Lifted Monotonicity fails.  These runs over-approximate the
fiber (`fiber_sub_run`); for a finite-state machine they reach finitely many
states. -/
theorem not_liftedMono_of_machine_cert [DecidableEq C]
    (fam : List (List (Act C P O) × (sys (C := C) k G).St))
    (hfam : ∀ r ∈ fam, Execution (sys k G) r.1 r.2) {β : List (Act C P O)}
    {s : (sys (C := C) k G).St} (hx : Execution (sys k G) β s)
    (hle : ∀ r ∈ fam, input r.1 ≼ input β)
    (hcert : ∀ γ q, Execution (machA G) γ q → (recvs γ).Nodup →
      (∀ e, e ∈ recvs γ ↔ (input β).mem e) →
      (k = .fifo → (recvs γ).Pairwise fun a b => ¬ (input β).lt b a) →
      ∃ r ∈ fam, ¬ G.obs (r.2 .mach) ≼ G.obs q) :
    ¬ (spec (C := C) k G).LiftedMono := by
  refine (not_liftedMono_iff_witness k G).2 ⟨fam, hfam, β, s, hx, hle, fun β' s' hx' hi' => ?_⟩
  obtain ⟨γ, q, hγ, ho, hn, hm, hf⟩ :=
    fiber_sub_run (k := k) (G := G) ⟨input β, β, s, hx, rfl⟩ (G.obs (s' .mach))
      ⟨β', s', hx', hi', rfl⟩
  rw [← ho]
  exact hcert γ q hγ hn hm hf

end testing

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

/-- `Nat` under `≤` (a local instance for the `dip` check). -/
@[instance_reducible] def natPO : PO Nat where
  le := Nat.le
  refl := Nat.le_refl
  trans := Nat.le_trans
  antisymm := Nat.le_antisymm

/-- States of `dip`. -/
inductive Dip where
  | a
  | b
  | c

/-- Observations of `dip`: `a ↦ 1`, `b ↦ 0`, `c ↦ 2`. -/
def Dip.obs : Dip → Nat
  | .a => 1
  | .b => 0
  | .c => 2

/-- Internal steps `a → b → c`; every receive goes to `c`; no outputs.  The
step `a → b` lowers the observation. -/
def dip (C P : Type) : Machine C P Dip Nat where
  q0 := .a
  recv _ _ q' := q' = .c
  recv_enabled _ _ := ⟨.c, rfl⟩
  out _ _ _ _ := False
  tau q q' := (q = .a ∧ q' = .b) ∨ (q = .b ∧ q' = .c)
  obs := Dip.obs

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
