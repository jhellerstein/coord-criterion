/-
Audit E: instances (`sections/instances.tex`), invariant confluence
(`appendices/proof-machinery.tex`, `app:iconfluence`) and composition
(`appendices/composition.tex`).

This file adds Lean proofs for claims of those sections that the existing
modules do not cover.  Nothing here changes an existing definition; new
models are introduced where the paper's text fixes one.

Modeling choices.

* Finite sets of payloads are `FSet P`: predicates with a finite list of
  members, ordered by inclusion.
* A join-semilattice is `JSL D` over an existing `PO D`.  The CRDT state
  `s(U) = s₀ ⊔ ⨆U` is characterized as the least upper bound of `{s₀} ∪ U`
  (`st`, `st_lub`), which is independent of any enumeration of `U`.
* The Boolean codomain `false ≼ true` is `Prop` ordered by implication
  (`instPOProp`).  The discrete order on a type is `Disc α`.
* HAT fact sets are `IConf.St Fact` (sets of facts, inclusion).  A "fact-set
  specification" exposes, at input `i`, any set of facts that is supported by
  `i` (`F ⊆ allowed i`) and satisfies the isolation predicate `P`.
* Prefix order on lists is `Pfx α`.
-/
import CoordCriterion.IConfluence
import CoordCriterion.Composition
import CoordCriterion.FunctionalCALM

namespace CC
namespace AuditE

open CC.Comp (Monotone graph graph_liftedMono_iff)

/-! ## General order constructions -/

/-- `Prop` ordered by implication: the Boolean order `false ≼ true`. -/
instance instPOProp : PO Prop where
  le p q := p → q
  refl _ h := h
  trans h₁ h₂ x := h₂ (h₁ x)
  antisymm h₁ h₂ := propext ⟨h₁, h₂⟩

/-- A type with the discrete order. -/
structure Disc (α : Type) where
  val : α

instance (α : Type) : PO (Disc α) where
  le a b := a = b
  refl _ := rfl
  trans h h' := h.trans h'
  antisymm h _ := h

/-- Finite sets, ordered by inclusion. -/
abbrev FSet (P : Type) := {p : P → Prop // ∃ l : List P, ∀ x, p x ↔ x ∈ l}

instance (P : Type) : PO (FSet P) where
  le U V := ∀ x, U.1 x → V.1 x
  refl _ _ h := h
  trans h₁ h₂ x h := h₂ x (h₁ x h)
  antisymm h₁ h₂ := Subtype.ext (funext fun x => propext ⟨h₁ x, h₂ x⟩)

def FSet.ofList {P : Type} (l : List P) : FSet P := ⟨fun x => x ∈ l, l, fun _ => Iff.rfl⟩

def FSet.union {P : Type} (U V : FSet P) : FSet P :=
  ⟨fun x => U.1 x ∨ V.1 x, by
    obtain ⟨l, hl⟩ := U.2
    obtain ⟨m, hm⟩ := V.2
    exact ⟨l ++ m, fun x => by show U.1 x ∨ V.1 x ↔ _; rw [hl, hm, List.mem_append]⟩⟩

/-- A join-semilattice structure on a partial order. -/
class JSL (D : Type) [PO D] where
  join : D → D → D
  le_l : ∀ a b, a ≼ join a b
  le_r : ∀ a b, b ≼ join a b
  lub : ∀ {a b c}, a ≼ c → b ≼ c → join a b ≼ c

theorem JSL.join_eq_right {D : Type} [PO D] [JSL D] {a b : D} (h : a ≼ b) : JSL.join a b = b :=
  PO.antisymm (JSL.lub h (PO.refl b)) (JSL.le_r a b)

/-- Sets with union. -/
instance (X : Type) : JSL (IConf.St X) where
  join := IConf.St.union
  le_l _ _ _ h := Or.inl h
  le_r _ _ _ h := Or.inr h
  lub h₁ h₂ v h := h.elim (h₁ v) (h₂ v)

/-- Componentwise join on a product. -/
instance {D E : Type} [PO D] [PO E] [JSL D] [JSL E] : JSL (D × E) where
  join p q := (JSL.join p.1 q.1, JSL.join p.2 q.2)
  le_l p q := ⟨JSL.le_l p.1 q.1, JSL.le_l p.2 q.2⟩
  le_r p q := ⟨JSL.le_r p.1 q.1, JSL.le_r p.2 q.2⟩
  lub h₁ h₂ := ⟨JSL.lub h₁.1 h₂.1, JSL.lub h₁.2 h₂.2⟩

/-! ## Instances table, "Query CALM" row and Sec. query-instance:
functional specifications have singleton, hence directed, fibers. -/

theorem functional_directed {I O : Type} [PO I] [PO O] (sp : Spec I O) (hf : sp.Functional) :
    sp.DirectedOutputs := by
  intro i X hne hX
  match X, hne with
  | x :: _, _ =>
    refine ⟨x, hX x (List.mem_cons_self ..), fun y hy => ?_⟩
    rw [hf i y x (hX y hy) (hX x (List.mem_cons_self ..))]
    exact PO.refl x

/-! ## Sec. crdt-instance: state-based CRDTs -/

section CRDT
variable {D : Type} [PO D] [JSL D]

omit [JSL D] in
/-- `d` is the least upper bound of `{s₀} ∪ U`. -/
def IsLUB (s0 : D) (U : D → Prop) (d : D) : Prop :=
  (s0 ≼ d ∧ ∀ x, U x → x ≼ d) ∧ ∀ c, s0 ≼ c → (∀ x, U x → x ≼ c) → d ≼ c

/-- `s₀ ⊔ x₁ ⊔ ⋯ ⊔ xₙ`. -/
def bigJoin (s0 : D) : List D → D
  | [] => s0
  | x :: l => JSL.join x (bigJoin s0 l)

theorem bigJoin_lub (s0 : D) : ∀ l : List D, IsLUB s0 (· ∈ l) (bigJoin s0 l)
  | [] => ⟨⟨PO.refl s0, fun _ h => nomatch h⟩, fun _ h _ => h⟩
  | x :: l => by
    have ih := bigJoin_lub s0 l
    refine ⟨⟨PO.trans ih.1.1 (JSL.le_r _ _), fun y hy => ?_⟩, fun c h0 hc => ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact JSL.le_l _ _
      · exact PO.trans (ih.1.2 y hy) (JSL.le_r _ _)
    · exact JSL.lub (hc x (List.mem_cons_self ..))
        (ih.2 c h0 fun y hy => hc y (List.mem_cons_of_mem _ hy))

omit [JSL D] in
theorem lub_unique {s0 : D} {U : D → Prop} {d d' : D} (h : IsLUB s0 U d) (h' : IsLUB s0 U d') :
    d = d' :=
  PO.antisymm (h.2 d' h'.1.1 h'.1.2) (h'.2 d h.1.1 h.1.2)

theorem exists_lub (s0 : D) (U : FSet D) : ∃ d, IsLUB s0 U.1 d := by
  obtain ⟨l, hl⟩ := U.2
  refine ⟨bigJoin s0 l, ?_⟩
  have h := bigJoin_lub s0 l
  exact ⟨⟨h.1.1, fun x hx => h.1.2 x ((hl x).1 hx)⟩,
    fun c h0 hc => h.2 c h0 fun x hx => hc x ((hl x).2 hx)⟩

/-- Eq. crdt-state-function: `s(U) = s₀ ⊔ ⨆ U`. -/
noncomputable def st (s0 : D) (U : FSet D) : D := Classical.choose (exists_lub s0 U)

theorem st_lub (s0 : D) (U : FSet D) : IsLUB s0 U.1 (st s0 U) :=
  Classical.choose_spec (exists_lub s0 U)

theorem st_eq {s0 : D} {U : FSet D} {d : D} (h : IsLUB s0 U.1 d) : st s0 U = d :=
  lub_unique (st_lub s0 U) h

theorem st_ofList (s0 : D) (l : List D) : st s0 (FSet.ofList l) = bigJoin s0 l :=
  st_eq (bigJoin_lub s0 l)

/-- `U ⊆ V` implies `s(U) ⊑ s(V)`: the state specification is monotone. -/
theorem st_mono (s0 : D) : Monotone (st s0 : FSet D → D) := fun U V hUV =>
  (st_lub s0 U).2 _ (st_lub s0 V).1.1 fun x hx => (st_lub s0 V).1.2 x (hUV x hx)

/-- `s(U₁) ⊔ s(U₂) = s(U₁ ∪ U₂)`. -/
theorem st_union (s0 : D) (U₁ U₂ : FSet D) :
    JSL.join (st s0 U₁) (st s0 U₂) = st s0 (U₁.union U₂) := by
  symm
  apply st_eq
  have h₁ := st_lub s0 U₁
  have h₂ := st_lub s0 U₂
  refine ⟨⟨PO.trans h₁.1.1 (JSL.le_l _ _), fun x hx => ?_⟩, fun c h0 hc => ?_⟩
  · rcases hx with hx | hx
    · exact PO.trans (h₁.1.2 x hx) (JSL.le_l _ _)
    · exact PO.trans (h₂.1.2 x hx) (JSL.le_r _ _)
  · exact JSL.lub (h₁.2 c h0 fun x hx => hc x (Or.inl hx))
      (h₂.2 c h0 fun x hx => hc x (Or.inr hx))

/-- "join is the least state covering both states": `s(U₁ ∪ U₂)` covers
`s(U₁)` and `s(U₂)` and lies below every common upper bound. -/
theorem st_union_least (s0 : D) (U₁ U₂ : FSet D) :
    (st s0 U₁ ≼ st s0 (U₁.union U₂) ∧ st s0 U₂ ≼ st s0 (U₁.union U₂)) ∧
      ∀ c, st s0 U₁ ≼ c → st s0 U₂ ≼ c → st s0 (U₁.union U₂) ≼ c := by
  rw [← st_union]
  exact ⟨⟨JSL.le_l _ _, JSL.le_r _ _⟩, fun _ h₁ h₂ => JSL.lub h₁ h₂⟩

/-- The CRDT state as a (monotone, hence consistent) functional specification. -/
theorem crdt_state_consistent (s0 : D) : (graph (st s0 : FSet D → D)).Consistent :=
  (complete_calm _).2 ((graph_liftedMono_iff _).2 (st_mono s0))

theorem graph_functional {α β : Type} [PO α] [PO β] (f : α → β) : (graph f).Functional :=
  fun _ _ _ h h' => h.trans h'.symm

theorem graph_monotoneF_iff {α β : Type} [PO α] [PO β] (f : α → β) :
    (graph f).MonotoneF ↔ Monotone f := by
  constructor
  · intro h x y hxy; exact h x y _ _ hxy rfl rfl
  · intro h x y o u hxy ho hu
    have ho' : o = f x := ho
    have hu' : u = f y := hu
    rw [ho', hu']; exact h x y hxy

variable {Y : Type} [PO Y]

/-- Eq. crdt-query-monotonicity, by Functional CALM: the client-visible
specification `q ∘ s` is consistent exactly when
`U ⊆ V ⟹ q(s(U)) ≼ q(s(V))`. -/
theorem crdt_query_calm (s0 : D) (q : D → Y) :
    (graph (fun U : FSet D => q (st s0 U))).Consistent ↔
      ∀ U V : FSet D, U ≼ V → q (st s0 U) ≼ q (st s0 V) := by
  rw [functional_calm (graph_functional _), graph_monotoneF_iff]
  rfl

/-- Monotonicity of `q` on all of `D` is sufficient. -/
theorem crdt_query_of_mono (s0 : D) {q : D → Y} (hq : Monotone q) :
    Monotone (fun U : FSet D => q (st s0 U)) :=
  fun U V h => hq _ _ (st_mono s0 U V h)

/-- "`q` need only be monotone on reachable states": `q ∘ s` is monotone iff
`q` is monotone between reachable states `s(U) ⊑ s(V)`. -/
theorem crdt_query_mono_iff_reachable (s0 : D) (q : D → Y) :
    Monotone (fun U : FSet D => q (st s0 U)) ↔
      ∀ U V : FSet D, st s0 U ≼ st s0 V → q (st s0 U) ≼ q (st s0 V) := by
  constructor
  · intro h U V hle
    have hV : st s0 (U.union V) = st s0 V := by
      rw [← st_union]; exact JSL.join_eq_right hle
    have := h U (U.union V) fun x hx => Or.inl hx
    simp only at this
    rwa [hV] at this
  · intro h U V hUV
    exact h U V (st_mono s0 U V hUV)

end CRDT

/-- A two-point lattice `ff ≼ tt` (join = or), for the "not required"
counterexample. -/
inductive B2 where
  | ff | tt
  deriving DecidableEq

def B2.le : B2 → B2 → Prop
  | .ff, _ => True
  | .tt, b => b = .tt

instance : PO B2 where
  le := B2.le
  refl a := by cases a <;> simp [B2.le]
  trans {a b c} h h' := by cases a <;> cases b <;> cases c <;> simp_all [B2.le]
  antisymm {a b} h h' := by cases a <;> cases b <;> simp_all [B2.le]

def B2.or : B2 → B2 → B2
  | .ff, b => b
  | .tt, _ => .tt

instance : JSL B2 where
  join := B2.or
  le_l a b := by cases a <;> cases b <;> simp [B2.or, PO.le, B2.le]
  le_r a b := by cases a <;> cases b <;> simp [B2.or, PO.le, B2.le]
  lub {a b c} h h' := by
    cases a <;> cases b <;> cases c <;> simp_all [B2.or, PO.le, B2.le]

def B2.neg : B2 → B2
  | .ff => .tt
  | .tt => .ff

/-- "Monotonicity of `q` on all of `D` is sufficient but not required": with
`s₀ = tt` every reachable state is `tt`, so `q = neg` is not monotone on `D`
but `q ∘ s` is (constant). -/
theorem crdt_query_mono_not_required :
    ¬ Monotone B2.neg ∧ Monotone (fun U : FSet B2 => B2.neg (st B2.tt U)) := by
  have htop : ∀ U : FSet B2, st B2.tt U = B2.tt := fun U => by
    have h := (st_lub B2.tt U).1.1
    revert h; cases st B2.tt U <;> simp [PO.le, B2.le]
  refine ⟨fun h => ?_, fun U V _ => by simp only; rw [htop U, htop V]; exact PO.refl _⟩
  have := h B2.ff B2.tt trivial
  simp [B2.neg, PO.le, B2.le] at this

/-! ### Two-phase set (Eq. crdt-2p-query) -/

section TwoP

inductive Item where
  | potato | ferrari
  deriving DecidableEq

abbrev PS := IConf.St Item

def emp : PS := fun _ => False
def sgl (x : Item) : PS := fun v => v = x

/-- `q_2P(Add, Del) = Add \ Del`. -/
def q2P (s : PS × PS) : PS := fun v => s.1 v ∧ ¬ s.2 v

/-- Payloads: "add potato", "add Ferrari"; `U₁` adds "remove Ferrari". -/
def U0 : FSet (PS × PS) := FSet.ofList [(sgl .potato, emp), (sgl .ferrari, emp)]
def U1 : FSet (PS × PS) :=
  FSet.ofList [(sgl .potato, emp), (sgl .ferrari, emp), (emp, sgl .ferrari)]

def both : PS := fun v => v = .potato ∨ v = .ferrari

theorem st_U0 : st (emp, emp) U0 = (both, emp) := by
  rw [U0, st_ofList]
  simp only [bigJoin, JSL.join]
  refine Prod.ext (funext fun v => propext ?_) (funext fun v => propext ?_) <;>
    simp [IConf.St.union, sgl, emp, both]

theorem st_U1 : st (emp, emp) U1 = (both, sgl .ferrari) := by
  rw [U1, st_ofList]
  simp only [bigJoin, JSL.join]
  refine Prod.ext (funext fun v => propext ?_) (funext fun v => propext ?_) <;>
    simp [IConf.St.union, sgl, emp, both]

theorem U0_le_U1 : U0 ≼ U1 := fun x hx => by
  simp only [U0, U1, FSet.ofList, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  rcases hx with h | h <;> simp [h]

/-- The displayed values: `(q ∘ s)(U₀) = {potato, Ferrari}`,
`(q ∘ s)(U₁) = {potato}`, `U₀ ⊆ U₁`, so `F_2P = q_2P ∘ s` is not monotone and
(Functional CALM) not consistent, although the state merge is. -/
theorem twoPhase_unsafe :
    q2P (st (emp, emp) U0) = both ∧ q2P (st (emp, emp) U1) = sgl .potato ∧ U0 ≼ U1 ∧
      ¬ (q2P (st (emp, emp) U0) ≼ q2P (st (emp, emp) U1)) ∧
      ¬ (graph (fun U : FSet (PS × PS) => q2P (st (emp, emp) U))).Consistent ∧
      (graph (st (emp, emp) : FSet (PS × PS) → PS × PS)).Consistent := by
  have e0 : q2P (st (emp, emp) U0) = both := by
    rw [st_U0]; funext v; apply propext; simp [q2P, emp]
  have e1 : q2P (st (emp, emp) U1) = sgl .potato := by
    rw [st_U1]; funext v; apply propext; cases v <;> simp [q2P, both, sgl]
  have hn : ¬ (q2P (st (emp, emp) U0) ≼ q2P (st (emp, emp) U1)) := by
    rw [e0, e1]; intro h
    have := h .ferrari (Or.inr rfl)
    exact Item.noConfusion (this : Item.ferrari = Item.potato)
  refine ⟨e0, e1, U0_le_U1, hn, fun h => hn ((crdt_query_calm _ _).1 h U0 U1 U0_le_U1),
    crdt_state_consistent _⟩

end TwoP

/-! ### Threshold queries (Eq. crdt-thresholds) -/

section Threshold
variable {A : Type}

/-- `|d| ≥ k`: `d` contains `k` distinct elements. -/
def AtLeast (k : Nat) (d : IConf.St A) : Prop :=
  ∃ l : List A, l.Nodup ∧ l.length = k ∧ ∀ x ∈ l, d x

/-- `q_k(d) = [|d| ≥ k]` with `false ≼ true`. -/
def qThr (k : Nat) (d : IConf.St A) : Prop := AtLeast k d

theorem qThr_mono (k : Nat) : Monotone (qThr (A := A) k) :=
  fun _ _ h ⟨l, hn, hl, hm⟩ => ⟨l, hn, hl, fun x hx => h x (hm x hx)⟩

/-- `Q_100 = q_100 ∘ s` is monotone: once true it stays true in every
expansion `V ⊇ U`. -/
theorem Q100_mono (s0 : IConf.St A) :
    Monotone (fun U : FSet (IConf.St A) => qThr 100 (st s0 U)) :=
  crdt_query_of_mono s0 (qThr_mono 100)

/-- Functional CALM: `Q_100` is consistent, and (exposure boundary) every
output at every state reachable without commitment, in particular `false`
before the threshold, is exposable. -/
theorem Q100_consistent_exposable (s0 : IConf.St A) :
    (graph (fun U : FSet (IConf.St A) => qThr 100 (st s0 U))).Consistent ∧
      ∀ τ : State (graph (fun U : FSet (IConf.St A) => qThr 100 (st s0 U))),
        ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  ⟨(crdt_query_calm _ _).2 (Q100_mono s0),
    (functional_exposure_boundary (graph_functional _)).1
      ((graph_monotoneF_iff _).2 (Q100_mono s0))⟩

/-- LVars threshold queries in general: `[t ⊑ d]` is monotone in `d`. -/
theorem lvar_threshold_mono {D : Type} [PO D] (t : D) : Monotone (fun d : D => (t ≼ d : Prop)) :=
  fun _ _ h h' => PO.trans h' h

end Threshold

/-! ### Last-writer-wins: "whether convergence is monotone depends on the
declared output order" -/

section LWW

/-- LWW register states `(timestamp, value)` in lexicographic order. -/
structure LWW where
  ts : Nat
  v : Nat

def LWW.le (a b : LWW) : Prop := a.ts < b.ts ∨ (a.ts = b.ts ∧ a.v ≤ b.v)

instance : DecidableRel LWW.le := fun a b => by unfold LWW.le; infer_instance

instance : PO LWW where
  le := LWW.le
  refl a := Or.inr ⟨rfl, Nat.le_refl _⟩
  trans {a b c} h h' := by unfold LWW.le at *; omega
  antisymm {a b} h h' := by
    unfold LWW.le at *
    cases a; cases b; simp only at *
    have : _ := And.intro h h'
    congr 1 <;> omega

instance : JSL LWW where
  join a b := if LWW.le a b then b else a
  le_l a b := by
    show LWW.le a (if LWW.le a b then b else a)
    split
    · assumption
    · exact Or.inr ⟨rfl, Nat.le_refl _⟩
  le_r a b := by
    show LWW.le b (if LWW.le a b then b else a)
    split
    · exact Or.inr ⟨rfl, Nat.le_refl _⟩
    · rename_i h; unfold LWW.le at *; omega
  lub {a b c} h h' := by
    show LWW.le (if LWW.le a b then b else a) c
    split <;> assumption

/-- The replica exposes `(ts 1, value 5)`, then the delayed write
`(ts 2, value 7)` arrives and the state converges to discard `5`.  Under the
lattice order on states the replica's output is monotone; under the
discrete order on exposed values it is not (and so is not consistent). -/
theorem lww_depends_on_order :
    Monotone (st (⟨0, 0⟩ : LWW)) ∧
      ¬ Monotone (fun U : FSet LWW => (⟨(st ⟨0, 0⟩ U).v⟩ : Disc Nat)) ∧
      ¬ (graph (fun U : FSet LWW => (⟨(st ⟨0, 0⟩ U).v⟩ : Disc Nat))).Consistent := by
  have e0 : st (⟨0, 0⟩ : LWW) (FSet.ofList [⟨1, 5⟩]) = ⟨1, 5⟩ := by
    rw [st_ofList]; rfl
  have e1 : st (⟨0, 0⟩ : LWW) (FSet.ofList [⟨1, 5⟩, ⟨2, 7⟩]) = ⟨2, 7⟩ := by
    rw [st_ofList]; rfl
  have hle : FSet.ofList [(⟨1, 5⟩ : LWW)] ≼ FSet.ofList [⟨1, 5⟩, ⟨2, 7⟩] := fun x hx => by
    simp only [FSet.ofList, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    exact Or.inl hx
  have hn : ¬ Monotone (fun U : FSet LWW => (⟨(st ⟨0, 0⟩ U).v⟩ : Disc Nat)) := by
    intro h
    have := h _ _ hle
    simp only at this
    rw [e0, e1] at this
    exact absurd (congrArg Disc.val this) (by decide)
  refine ⟨st_mono _, hn, fun h => hn ?_⟩
  exact (graph_liftedMono_iff _).1 ((complete_calm _).1 h)

end LWW

/-! ## Sec. hat-instance: highly available transactions

Inputs are abstract (any partial order `I`); `allowed i` is the set of facts
the requests in `i` can support, monotone in `i`.  At input `i` the
specification may expose any supported fact set satisfying the isolation
predicate `P`. -/

section HAT
open IConf (St)

def noFacts {Φ : Type} : St Φ := fun _ => False

/-- The fact-set specification `{F ⊆ allowed i : P F}`. -/
def factSpec {I Φ : Type} [PO I] (allowed : I → St Φ) (P : St Φ → Prop) (hP0 : P noFacts) :
    Spec I (St Φ) where
  S i F := F ≼ allowed i ∧ P F
  total _ := ⟨noFacts, fun _ h => h.elim, hP0⟩

/-- "A guarantee whose exposed facts only accumulate … has a common outcome
for whatever separated replicas expose": if `P` is closed under union, the
union of the exposed fact sets is permitted at every common expansion, so the
specification satisfies Lifted Monotonicity (hence is consistent). -/
theorem factSpec_liftedMono {I Φ : Type} [PO I] (allowed : I → St Φ) (hmono : Monotone allowed)
    (P : St Φ → Prop) (hP0 : P noFacts) (hU : ∀ F G, P F → P G → P (F.union G)) :
    (factSpec allowed P hP0).LiftedMono := by
  rw [liftedMono_iff_commonExpansion]
  intro rows hrows j hj
  induction rows with
  | nil => exact ⟨noFacts, ⟨fun _ h => h.elim, hP0⟩, fun _ h => nomatch h⟩
  | cons r rest ih =>
    obtain ⟨F, ⟨hFa, hFP⟩, hF⟩ :=
      ih (fun r h => hrows r (List.mem_cons_of_mem _ h)) (fun r h => hj r (List.mem_cons_of_mem _ h))
    obtain ⟨hra, hrP⟩ := hrows r (List.mem_cons_self ..)
    have hra' : r.2 ≼ allowed j := PO.trans hra (hmono _ _ (hj r (List.mem_cons_self ..)))
    refine ⟨r.2.union F, ⟨fun v h => h.elim (hra' v) (hFa v), hU _ _ hrP hFP⟩, fun r' hr' => ?_⟩
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact fun _ h => Or.inl h
    · exact PO.trans (hF r' hr') fun _ h => Or.inr h

/-- "One that orders or excludes concurrent transactions … rules out
combinations that separated replicas can each expose": two rows at inputs
below `j` with no permitted common upper bound at `j` refute Lifted
Monotonicity, hence (Complete CALM) consistency. -/
theorem factSpec_not_liftedMono {I Φ : Type} [PO I] (allowed : I → St Φ) (P : St Φ → Prop)
    (hP0 : P noFacts) {i₁ i₂ j : I} {F₁ F₂ : St Φ} (h₁ : i₁ ≼ j) (h₂ : i₂ ≼ j)
    (r₁ : (factSpec allowed P hP0).S i₁ F₁) (r₂ : (factSpec allowed P hP0).S i₂ F₂)
    (hno : ∀ G, F₁ ≼ G → F₂ ≼ G → G ≼ allowed j → ¬ P G) :
    ¬ (factSpec allowed P hP0).LiftedMono ∧ ¬ (factSpec allowed P hP0).Consistent := by
  have hn : ¬ (factSpec allowed P hP0).LiftedMono := by
    rw [liftedMono_iff_commonExpansion]
    intro h
    obtain ⟨G, ⟨hGa, hGP⟩, hG⟩ := h [(i₁, F₁), (i₂, F₂)]
      (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> assumption) j
      (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> assumption)
    exact hno G (hG _ (List.mem_cons_self ..)) (hG _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      hGa hGP
  exact ⟨hn, fun h => hn ((complete_calm _).1 h)⟩

/-- Public transaction facts.  Keys and values are numbers (`x = 0`, `y = 1`,
initial value `0`). -/
inductive Fact where
  | read (t k v : Nat)
  | write (t k v : Nat)
  | commit (t : Nat)

/-- Read committed, as stated: every read returns the initial version or a
version written by a committed transaction. -/
def RC (F : St Fact) : Prop :=
  ∀ t k v, F (.read t k v) → v = 0 ∨ ∃ t', F (.write t' k v) ∧ F (.commit t')

theorem rc_empty : RC noFacts := fun _ _ _ h => h.elim

theorem rc_union (F G : St Fact) (hF : RC F) (hG : RC G) : RC (F.union G) := by
  intro t k v h
  rcases h with h | h
  · rcases hF t k v h with h0 | ⟨t', hw, hc⟩
    · exact Or.inl h0
    · exact Or.inr ⟨t', Or.inl hw, Or.inl hc⟩
  · rcases hG t k v h with h0 | ⟨t', hw, hc⟩
    · exact Or.inl h0
    · exact Or.inr ⟨t', Or.inr hw, Or.inr hc⟩

/-- The read-committed specification satisfies Lifted Monotonicity and is
consistent, for any monotone `allowed`. -/
theorem rc_liftedMono_consistent {I : Type} [PO I] (allowed : I → St Fact)
    (hmono : Monotone allowed) :
    (factSpec allowed RC rc_empty).LiftedMono ∧ (factSpec allowed RC rc_empty).Consistent :=
  have h := factSpec_liftedMono allowed hmono RC rc_empty rc_union
  ⟨h, (complete_calm _).2 h⟩

/-- Accumulating facts: replica 1 exposes `read(T₁,x,0), commit(T₁)`,
replica 2 exposes `read(T₂,y,0), commit(T₂)`; the union of all four facts is
read committed. -/
def acc1 : St Fact := fun f => f = .read 1 0 0 ∨ f = .commit 1
def acc2 : St Fact := fun f => f = .read 2 1 0 ∨ f = .commit 2

theorem accumulating_example : RC acc1 ∧ RC acc2 ∧ RC (acc1.union acc2) := by
  have h1 : RC acc1 := by
    intro t k v h; rcases h with h | h <;> cases h; exact Or.inl rfl
  have h2 : RC acc2 := by
    intro t k v h; rcases h with h | h <;> cases h; exact Or.inl rfl
  exact ⟨h1, h2, rc_union _ _ h1 h2⟩

/-- The read of `k` by `t` returns `v` in the serial order `before`: `v` is
the value of the latest committed writer of `k` before `t`, or the initial
`0` if there is none. -/
def ReadOK (F : St Fact) (before : Nat → Nat → Prop) (t k v : Nat) : Prop :=
  ((¬ ∃ t' w, before t' t ∧ F (.commit t') ∧ F (.write t' k w)) ∧ v = 0) ∨
    ∃ t', before t' t ∧ F (.commit t') ∧ F (.write t' k v) ∧
      ¬ ∃ t'' w, before t' t'' ∧ before t'' t ∧ F (.commit t'') ∧ F (.write t'' k w)

/-- Serializable: some strict total order of the committed transactions
explains every read of a committed transaction. -/
def Ser (F : St Fact) : Prop :=
  ∃ before : Nat → Nat → Prop, (∀ t, ¬ before t t) ∧
    (∀ a b c, before a b → before b c → before a c) ∧
    (∀ a b, F (.commit a) → F (.commit b) → a ≠ b → before a b ∨ before b a) ∧
    ∀ t k v, F (.read t k v) → F (.commit t) → ReadOK F before t k v

theorem ser_empty : Ser noFacts :=
  ⟨fun _ _ => False, fun _ h => h, fun _ _ _ h => h.elim, fun _ _ h => h.elim,
    fun _ _ _ h => h.elim⟩

/-- `T₁` reads `x = 0`, writes `y = 1`, commits. -/
def ser1 : St Fact := fun f => f = .read 1 0 0 ∨ f = .write 1 1 1 ∨ f = .commit 1
/-- `T₂` reads `y = 0`, writes `x = 1`, commits. -/
def ser2 : St Fact := fun f => f = .read 2 1 0 ∨ f = .write 2 0 1 ∨ f = .commit 2

/-- The facts the received requests can support: `T₁`'s read of `x` (any
value), its write `y = 1` and commit, and symmetrically for `T₂`. -/
def serAllowed : St Fact := fun f =>
  (∃ v, f = .read 1 0 v) ∨ (∃ v, f = .read 2 1 v) ∨ f = .write 1 1 1 ∨ f = .write 2 0 1 ∨
    f = .commit 1 ∨ f = .commit 2

theorem ser_single {F : St Fact} {t : Nat} (hc : ∀ a, F (.commit a) → a = t)
    (hr : ∀ s k v, F (.read s k v) → v = 0) : Ser F := by
  refine ⟨fun _ _ => False, fun _ h => h, fun _ _ _ h => h.elim, fun a b ha hb hab => ?_,
    fun s k v h _ => Or.inl ⟨fun ⟨_, _, h', _⟩ => h', hr s k v h⟩⟩
  exact absurd ((hc a ha).trans (hc b hb).symm) hab

/-- Serializability and transaction ordering: each side is serializable on
its own, but no supported fact set containing both sides is serializable
(the serialization graph has a cycle). -/
theorem serializability_cycle :
    Ser ser1 ∧ Ser ser2 ∧
      ∀ G : St Fact, ser1 ≼ G → ser2 ≼ G → G ≼ serAllowed → ¬ Ser G := by
  refine ⟨ser_single (t := 1) ?_ ?_, ser_single (t := 2) ?_ ?_, ?_⟩
  · intro a h; rcases h with h | h | h <;> cases h; rfl
  · intro s k v h; rcases h with h | h | h <;> cases h; rfl
  · intro a h; rcases h with h | h | h <;> cases h; rfl
  · intro s k v h; rcases h with h | h | h <;> cases h; rfl
  intro G h1 h2 hA ⟨bf, _, _, tot, rd⟩
  have r1 : G (.read 1 0 0) := h1 _ (Or.inl rfl)
  have w1 : G (.write 1 1 1) := h1 _ (Or.inr (Or.inl rfl))
  have c1 : G (.commit 1) := h1 _ (Or.inr (Or.inr rfl))
  have r2 : G (.read 2 1 0) := h2 _ (Or.inl rfl)
  have w2 : G (.write 2 0 1) := h2 _ (Or.inr (Or.inl rfl))
  have c2 : G (.commit 2) := h2 _ (Or.inr (Or.inr rfl))
  -- the only supported write of value `0` would have to be in `serAllowed`
  have nw : ∀ t' k, G (.write t' k 0) → False := fun t' k h => by
    have := hA _ h
    simp [serAllowed] at this
  rcases tot 1 2 c1 c2 (by decide) with hb | hb
  · -- `T₁` before `T₂`: `T₂`'s read of `y = 0` fails
    rcases rd 2 1 0 r2 c2 with ⟨hno, _⟩ | ⟨t', _, _, hw, _⟩
    · exact hno ⟨1, 1, hb, c1, w1⟩
    · exact nw _ _ hw
  · -- `T₂` before `T₁`: `T₁`'s read of `x = 0` fails
    rcases rd 1 0 0 r1 c1 with ⟨hno, _⟩ | ⟨t', _, _, hw, _⟩
    · exact hno ⟨2, 1, hb, c2, w2⟩
    · exact nw _ _ hw

/-- The serializable specification (inputs: supported fact sets, ordered by
inclusion) violates Lifted Monotonicity and is not consistent. -/
theorem serializable_spec_not_consistent :
    ¬ (factSpec (fun i : St Fact => i) Ser ser_empty).LiftedMono ∧
      ¬ (factSpec (fun i : St Fact => i) Ser ser_empty).Consistent := by
  have hs1 : ser1 ≼ serAllowed := fun f h => by
    rcases h with rfl | rfl | rfl <;> simp [serAllowed]
  have hs2 : ser2 ≼ serAllowed := fun f h => by
    rcases h with rfl | rfl | rfl <;> simp [serAllowed]
  obtain ⟨S1, S2, hno⟩ := serializability_cycle
  exact factSpec_not_liftedMono _ Ser ser_empty hs1 hs2 ⟨PO.refl _, S1⟩ ⟨PO.refl _, S2⟩ hno

/-- First-committer-wins for two overlapping writers `T₁, T₂` of `x`. -/
def FCW (F : St Fact) : Prop := ¬ (F (.commit 1) ∧ F (.commit 2))

def fcw1 : St Fact := fun f => f = .commit 1
def fcw2 : St Fact := fun f => f = .commit 2

/-- Snapshot isolation: each local commit is permitted, no output contains
both, so the specification is not consistent. -/
theorem snapshot_fcw :
    FCW fcw1 ∧ FCW fcw2 ∧ (∀ G : St Fact, fcw1 ≼ G → fcw2 ≼ G → ¬ FCW G) ∧
      ¬ (factSpec (fun i : St Fact => i) FCW (fun h => h.1)).Consistent := by
  have a : FCW fcw1 := fun ⟨_, h⟩ => by cases h
  have b : FCW fcw2 := fun ⟨h, _⟩ => by cases h
  have hno : ∀ G : St Fact, fcw1 ≼ G → fcw2 ≼ G → ¬ FCW G :=
    fun G h1 h2 h => h ⟨h1 _ rfl, h2 _ rfl⟩
  refine ⟨a, b, hno, ?_⟩
  exact (factSpec_not_liftedMono (fun i : St Fact => i) FCW (fun h => h.1)
    (i₁ := fcw1) (i₂ := fcw2) (j := fcw1.union fcw2) (fun _ h => Or.inl h) (fun _ h => Or.inr h)
    ⟨PO.refl _, a⟩ ⟨PO.refl _, b⟩ fun G h1 h2 _ => hno G h1 h2).2

end HAT

/-! ## Invariant confluence (App. `app:iconfluence`, Sec. iconfluence-instance) -/

section IConfAudit
open IConf

variable {V Tx : Type} (M : Model V Tx)

/-- `pre` of an event of a downward-closed sub-history agrees with `pre` in
the larger history. -/
theorem pre_sub {c h : Hist Tx} (hc : c ≼ h) {e : Nat} (he : c.ev e) :
    pre M c e = pre M h e := by
  funext v; apply propext; unfold pre
  constructor
  · rintro (h0 | ⟨x, hl, hp⟩)
    · exact Or.inl h0
    · refine Or.inr ⟨x, ((hc.2 x e).1 hl).1, ?_⟩
      rw [← post_sub M hc (Hist.ev_of_lt_left hl)]; exact hp
  · rintro (h0 | ⟨x, hl, hp⟩)
    · exact Or.inl h0
    · have hl' := (hc.2 x e).2 ⟨hl, he⟩
      exact Or.inr ⟨x, hl', by rw [post_sub M hc (Hist.ev_of_lt_left hl')]; exact hp⟩

/-- "A downward-closed sub-order of a locally valid history is locally valid,
so the inputs are closed under the order." -/
theorem locValid_sub {c h : Hist Tx} (hc : c ≼ h) (hl : LocValid M h) : LocValid M c := by
  intro e he
  rw [pre_sub M hc he, post_sub M hc he]
  exact hl e (Hist.le_ev hc he)

/-! ### The uniqueness example

Versions are the accounts owning username `sam`; `alloc a` allocates `sam`
to account `a` if the replica sees it free.  The invariant: at most one
owner. -/

def uModel : Model Nat Nat where
  app a s := fun v => s v ∨ (v = a ∧ ¬ ∃ b, s b)
  infl _ _ _ h := Or.inl h
  s0 := fun _ => False
  Inv s := ∀ a b, s a → s b → a = b
  init _ _ h := h.elim

/-- History with the events `0 ↦ alloc 1`, `1 ↦ alloc 2`, unordered. -/
def jU : Hist Nat where
  lab m := if m = 0 then some 1 else if m = 1 then some 2 else none
  lt _ _ := False
  lt_ev h := h.elim
  lt_num h := h.elim
  lt_trans h := h.elim
  fin := ⟨2, fun e he => by
    have h0 : e ≠ 0 := by omega
    have h1 : e ≠ 1 := by omega
    simp [h0, h1]⟩

/-- One-event history `n ↦ alloc t`. -/
def oneU (n t : Nat) : Hist Nat where
  lab m := if m = n then some t else none
  lt _ _ := False
  lt_ev h := h.elim
  lt_num h := h.elim
  lt_trans h := h.elim
  fin := ⟨n + 1, fun e he => by
    have : e ≠ n := by omega
    simp [this]⟩

theorem pre_antichain (h : Hist Nat) (hl : ∀ x y, ¬ h.lt x y) (e : Nat) :
    pre uModel h e = uModel.s0 := by
  funext v; apply propext; unfold pre
  exact ⟨fun h' => h'.elim id fun ⟨x, hx, _⟩ => (hl x e hx).elim, Or.inl⟩

theorem post_antichain (h : Hist Nat) (hl : ∀ x y, ¬ h.lt x y) (e t : Nat)
    (he : h.lab e = some t) (v : Nat) : post uModel h e v ↔ v = t := by
  rw [post_eq, pre_antichain h hl, he]
  show (False ∨ (v = t ∧ ¬ ∃ b, False)) ↔ v = t
  simp

theorem eval_oneU (n t v : Nat) : eval uModel (oneU n t) v ↔ v = t := by
  unfold eval
  constructor
  · rintro (h | ⟨e, he, hp⟩)
    · exact h.elim
    · have hen : e = n := by
        false_or_by_contra
        exact he (by simp [oneU, *])
      subst hen
      exact (post_antichain _ (fun _ _ h => h) e t (by simp [oneU]) v).1 hp
  · intro hv
    exact Or.inr ⟨n, by simp [Hist.ev, oneU],
      (post_antichain _ (fun _ _ h => h) n t (by simp [oneU]) v).2 hv⟩

theorem oneU_le_jU (n t : Nat) (hn : jU.lab n = some t) : oneU n t ≼ jU := by
  refine ⟨fun e t' h => ?_, fun x y => ⟨fun h => h.elim, fun h => h.1.elim⟩⟩
  simp only [oneU] at h
  by_cases he : e = n
  · subst he; simp at h; rw [hn, h]
  · simp [he] at h

theorem valid_oneU (n t : Nat) : Valid uModel (oneU n t) := by
  intro c hc a b ha hb
  have ha' := (eval_oneU n t a).1 (eval_mono uModel hc a ha)
  have hb' := (eval_oneU n t b).1 (eval_mono uModel hc b hb)
  rw [ha', hb']

theorem locValid_jU : LocValid uModel jU := by
  intro e he
  have hpre := pre_antichain jU (fun _ _ h => h) e
  refine ⟨by rw [hpre]; intro _ _ h; exact h.elim, ?_⟩
  obtain ⟨t, ht⟩ : ∃ t, jU.lab e = some t := by
    cases h : jU.lab e with
    | none => exact absurd h he
    | some t => exact ⟨t, rfl⟩
  intro a b ha hb
  rw [(post_antichain jU (fun _ _ h => h) e t ht a).1 ha,
    (post_antichain jU (fun _ _ h => h) e t ht b).1 hb]

/-- The uniqueness example: the history `jU` in which neither allocation saw
the other is locally valid and expands both one-allocation histories; its
state has two owners; no state `S_I` permits at `jU` covers both rows; hence
`S_I` fails Lifted Monotonicity and the transactions are not invariant
confluent. -/
theorem uniqueness_example :
    LocValid uModel jU ∧ oneU 0 1 ≼ jU ∧ oneU 1 2 ≼ jU ∧
      eval uModel jU 1 ∧ eval uModel jU 2 ∧ ¬ uModel.Inv (eval uModel jU) ∧
      (∀ u, (SI uModel).S ⟨jU, locValid_jU⟩ u →
        ¬ (eval uModel (oneU 0 1) ≼ u ∧ eval uModel (oneU 1 2) ≼ u)) ∧
      ¬ (SI uModel).LiftedMono ∧ ¬ uModel.IConfluent := by
  have l1 : oneU 0 1 ≼ jU := oneU_le_jU 0 1 rfl
  have l2 : oneU 1 2 ≼ jU := oneU_le_jU 1 2 rfl
  have e1 : eval uModel jU 1 :=
    eval_mono uModel l1 1 ((eval_oneU 0 1 1).2 rfl)
  have e2 : eval uModel jU 2 :=
    eval_mono uModel l2 2 ((eval_oneU 1 2 2).2 rfl)
  have hno : ∀ u, (SI uModel).S ⟨jU, locValid_jU⟩ u →
      ¬ (eval uModel (oneU 0 1) ≼ u ∧ eval uModel (oneU 1 2) ≼ u) := by
    rintro u ⟨g, _, vg, rfl⟩ ⟨h1, h2⟩
    have := vg g (PO.refl g) 1 2 (h1 1 ((eval_oneU 0 1 1).2 rfl)) (h2 2 ((eval_oneU 1 2 2).2 rfl))
    exact absurd this (by decide)
  have hnce : ¬ (SI uModel).CommonExpansion := by
    intro h
    obtain ⟨u, hu, hall⟩ := h
      [(⟨oneU 0 1, valid_locValid uModel (valid_oneU 0 1)⟩, eval uModel (oneU 0 1)),
       (⟨oneU 1 2, valid_locValid uModel (valid_oneU 1 2)⟩, eval uModel (oneU 1 2))]
      (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨_, PO.refl _, valid_oneU 0 1, rfl⟩
          · exact ⟨_, PO.refl _, valid_oneU 1 2, rfl⟩)
      ⟨jU, locValid_jU⟩
      (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact l1
          · exact l2)
    exact hno u hu ⟨hall _ (List.mem_cons_self ..),
      hall _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩
  refine ⟨locValid_jU, l1, l2, e1, e2, fun h => absurd (h 1 2 e1 e2) (by decide), hno,
    fun h => hnce ((liftedMono_iff_commonExpansion _).1 h),
    fun h => hnce ((ic_iff_commonExpansion uModel).1 h)⟩

/-- "Concurrency, not the transactions alone, decides the outcome":
`alloc 2` after `alloc 1` is valid (a no-op), `alloc 2` without seeing
`alloc 1` is a valid step on its own replica, but the merge of the two
concurrent results is invalid.  (The local step is not invalid; the merge
is.) -/
theorem uniqueness_concurrency :
    uModel.Inv (uModel.app 2 (uModel.app 1 uModel.s0)) ∧ uModel.Inv (uModel.app 2 uModel.s0) ∧
      ¬ uModel.Inv ((uModel.app 1 uModel.s0).union (uModel.app 2 uModel.s0)) := by
  have h1 : ∀ v, uModel.app 1 uModel.s0 v ↔ v = 1 := fun v => by
    show (False ∨ (v = 1 ∧ ¬ ∃ b, False)) ↔ v = 1; simp
  have h2 : ∀ v, uModel.app 2 uModel.s0 v ↔ v = 2 := fun v => by
    show (False ∨ (v = 2 ∧ ¬ ∃ b, False)) ↔ v = 2; simp
  refine ⟨?_, ?_, ?_⟩
  · intro a b ha hb
    have key : ∀ v, uModel.app 2 (uModel.app 1 uModel.s0) v → v = 1 := by
      rintro v (hv | ⟨_, hn⟩)
      · exact (h1 v).1 hv
      · exact absurd ⟨1, (h1 1).2 rfl⟩ hn
    rw [key a ha, key b hb]
  · intro a b ha hb; rw [(h2 a).1 ha, (h2 b).1 hb]
  · intro h
    exact absurd (h 1 2 (Or.inl ((h1 1).2 rfl)) (Or.inr ((h2 2).2 rfl))) (by decide)

end IConfAudit

/-! ## Composition (App. `app:composition`) -/

section CompAudit
open Comp

/-- The converse example after Cor. `cor:monotone-commitment`:
`I = {*}`, `M = {x, y}` discrete, `S₁ = {(*,x),(*,y)}`, `K = {(*,x)}`,
`S₂ = {(x,x),(y,x),(y,y)}`.  `S₁`, `S₂` and the unresolved `S₂ ∘ S₁` all fail
Lifted Monotonicity (so also "neither `S₁`, `S₂`, nor the unresolved
composition need be monotone"), `S₂(y) = {x, y}` is not directed, the resolved
table is exactly `{(*,x)}`, and the strategy is proper. -/
theorem converse_example :
    (∀ p m, anyS.S p m) ∧ (∀ p m, kappaX.K p m ↔ m = Two.x) ∧
    (∀ m o, s2NM.S m o ↔ (m = .x ∧ o = .x) ∨ (m = .y ∧ o = .x) ∨ (m = .y ∧ o = .y)) ∧
    (∀ p o, (seq kappaX.spec s2NM).S p o ↔ o = Two.x) ∧
    ¬ JointLift (s2NM.S .y) (s2NM.S .y) ∧
    ¬ anyS.LiftedMono ∧ ¬ s2NM.LiftedMono ∧ ¬ (seq anyS s2NM).LiftedMono ∧
    ProperSeq kappaX s2NM := by
  have hxy : ¬ ∃ u : Two, Two.x ≼ u ∧ Two.y ≼ u := fun ⟨u, h1, h2⟩ =>
    two_ne ((h1 : Two.x = u).trans (h2 : Two.y = u).symm)
  refine ⟨fun _ _ => trivial, fun _ _ => Iff.rfl, ?_, ?_, ?_,
    monotone_commitment_neither_monotone.1, proper_strictly_more_general.1, ?_,
    proper_strictly_more_general.2⟩
  · intro m o; cases m <;> cases o <;> simp [s2NM]
  · intro p o
    constructor
    · rintro ⟨m, hm, h⟩
      have hm' : m = Two.x := hm
      subst hm'
      rcases h with h | h
      · exact Two.noConfusion h
      · exact h
    · rintro rfl; exact ⟨.x, rfl, Or.inr rfl⟩
  · intro h
    obtain ⟨u, _, hall⟩ := h [.x, .y] (by simp) (fun _ _ => Or.inl rfl)
    exact hxy ⟨u, hall _ (by simp), hall _ (by simp)⟩
  · intro h
    obtain ⟨u, _, hall⟩ := h .pt .pt trivial [.x, .y] (by simp) (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact ⟨.x, trivial, Or.inr rfl⟩
      · exact ⟨.y, trivial, Or.inl rfl⟩)
    exact hxy ⟨u, hall _ (by simp), hall _ (by simp)⟩

variable {I J A B C : Type} [PO I] [PO J] [PO A] [PO B] [PO C]

omit [PO I] [PO J] [PO A] [PO B] [PO C] in
/-- Curried form of the graph-table instance:
`h^♯(i,j) = g^♯(j) ∘ f^♯(i)`. -/
theorem curried_sharp (f : I × A → B) (g : J × B → C) (i : I) (j : J) :
    (fun a => g (j, f (i, a))) = (fun b => g (j, b)) ∘ (fun a => f (i, a)) := rfl

/-- "… which is the plan of Prop. `prop:curried-query-plan` on graph tables":
the curried plan of two graph tables is the graph of `h`. -/
theorem curried_plan_graph (f : I × A → B) (g : J × B → C) :
    curriedPlan (graph f).S (graph g).S = (graph (fun x : I × (J × A) => g (x.2.1, f (x.1, x.2.2)))).S := by
  rw [← curried_query_plan]
  exact congrArg Spec.S (parameterized_graph f g)

/-- Inputs satisfying a predicate, with the induced order. -/
def Sub {α : Type} (P : α → Prop) := {x : α // P x}

instance {α : Type} [PO α] (P : α → Prop) : PO (Sub P) where
  le x y := x.1 ≼ y.1
  refl x := PO.refl x.1
  trans h h' := PO.trans h h'
  antisymm h h' := Subtype.ext (PO.antisymm h h')

/-- A specification restricted to the inputs satisfying `P`. -/
def onDom {α O : Type} [PO α] [PO O] (P : α → Prop) (sp : Spec α O) : Spec (Sub P) O :=
  ⟨fun x o => sp.S x.1 o, fun x => sp.total x.1⟩

/-- Restricting the inputs preserves Lifted Monotonicity (used when
Example `ex:committed-log-composition` restricts to coherent pairs). -/
theorem onDom_liftedMono {α O : Type} [PO α] [PO O] (P : α → Prop) {sp : Spec α O}
    (h : sp.LiftedMono) : (onDom P sp).LiftedMono :=
  fun i j hij X hne hX => h i.1 j.1 hij X hne hX

end CompAudit

/-! ### Example `ex:committed-log-composition` -/

section Log
open Comp

/-- Lists under the prefix order. -/
structure Pfx (α : Type) where
  l : List α

instance (α : Type) : PO (Pfx α) where
  le a b := ∃ t, b.l = a.l ++ t
  refl a := ⟨[], (List.append_nil _).symm⟩
  trans := by
    rintro a b c ⟨t, ht⟩ ⟨t', ht'⟩
    exact ⟨t ++ t', by rw [ht', ht, List.append_assoc]⟩
  antisymm := by
    rintro ⟨a⟩ ⟨b⟩ ⟨t, ht⟩ ⟨t', ht'⟩
    simp only at ht ht'
    have hl := congrArg List.length ht
    have hl' := congrArg List.length ht'
    simp only [List.length_append] at hl hl'
    have : t = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [List.append_nil] at ht
    rw [ht]

theorem pfx_head {α : Type} {a b : α} {l m : List α} {u : Pfx α}
    (h1 : (⟨a :: l⟩ : Pfx α) ≼ u) (h2 : (⟨b :: m⟩ : Pfx α) ≼ u) : a = b := by
  obtain ⟨t, ht⟩ := h1
  obtain ⟨t', ht'⟩ := h2
  rw [ht] at ht'
  simp only [List.cons_append, List.cons.injEq] at ht'
  exact ht'.1

variable {Cmd Stt R : Type} (δ : Stt → Cmd → Stt × R)

/-- Responses obtained by executing a log on a deterministic state machine. -/
def exec : Stt → List Cmd → List (Cmd × R)
  | _, [] => []
  | σ, c :: l => (c, (δ σ c).2) :: exec (δ σ c).1 l

def final : Stt → List Cmd → Stt
  | σ, [] => σ
  | σ, c :: l => final (δ σ c).1 l

theorem exec_append : ∀ (σ : Stt) (l t : List Cmd), exec δ σ (l ++ t) = exec δ σ l ++ exec δ (final δ σ l) t
  | _, [], _ => rfl
  | σ, c :: l, t => by simp only [List.cons_append, exec, final, exec_append _ l t]

/-- `F`: at proposal stream `i`, the logs still permitted (logs of proposed
commands).  `I = B = Pfx Cmd`, `A = Pt`. -/
def logF : Spec (Pfx Cmd × Pt) (Pfx Cmd) :=
  ⟨fun p b => ∀ c ∈ b.l, c ∈ p.1.l, fun _ => ⟨⟨[]⟩, fun _ h => nomatch h⟩⟩

/-- The authority commits to the next command in arrival order: `K(i) = i`. -/
def logK : CommitTable (logF (Cmd := Cmd)) :=
  ⟨(graph fun p : Pfx Cmd × Pt => p.1).S, fun p b h => by
    have h' : b = p.1 := h
    subst h'; exact fun _ hc => hc, fun _ => ⟨_, rfl⟩⟩

/-- `G`: a request history and a log determine the responses (deterministic
execution).  `J = Pfx Cmd`, `C = Pfx (Cmd × R)`. -/
def kvG (σ0 : Stt) : Spec (Pfx Cmd × Pfx Cmd) (Pfx (Cmd × R)) :=
  graph fun q => ⟨exec δ σ0 q.2.l⟩

/-- Coherent pairs: every proposed command comes from a request in `J`. -/
def Coh (x : Pfx Cmd × (Pfx Cmd × Pt)) : Prop := ∀ c ∈ x.1.l, c ∈ x.2.1.l

theorem logK_monotone : Monotone (fun p : Pfx Cmd × Pt => p.1) := fun _ _ h => h.1

theorem kvG_monotone (σ0 : Stt) :
    Monotone (fun q : Pfx Cmd × Pfx Cmd => (⟨exec δ σ0 q.2.l⟩ : Pfx (Cmd × R))) := by
  rintro q q' ⟨_, t, ht⟩
  exact ⟨exec δ (final δ σ0 q.2.l) t, by show exec δ σ0 q'.2.l = _; rw [ht, exec_append]⟩

/-- Example `ex:committed-log-composition`, for any deterministic state
machine and any two distinct commands:
* `F` violates Lifted Monotonicity (two next entries in one fiber);
* `G ⋆ F`, restricted to coherent pairs, violates it (opposite orders give
  incompatible responses);
* `K` is the graph of a monotone function and `G` is monotone;
* the commitment is proper, and `G ⋆ K` is consistent, also on coherent
  pairs. -/
theorem committed_log_example (σ0 : Stt) {c₁ c₂ : Cmd} (hne : c₁ ≠ c₂) :
    ¬ (logF (Cmd := Cmd)).LiftedMono ∧
      ¬ (onDom Coh (par logF (kvG δ σ0))).LiftedMono ∧
      (logK (Cmd := Cmd)).K = (graph fun p : Pfx Cmd × Pt => p.1).S ∧
      Monotone (fun p : Pfx Cmd × Pt => p.1) ∧ (kvG δ σ0).LiftedMono ∧
      ProperPar logK (kvG δ σ0) ∧ (par logK.spec (kvG δ σ0)).Consistent ∧
      (onDom Coh (par logK.spec (kvG δ σ0))).Consistent := by
  have hG : (kvG δ σ0).LiftedMono := (graph_liftedMono_iff _).2 (kvG_monotone δ σ0)
  have hP : ProperPar logK (kvG δ σ0) :=
    monotone_commitment_par logK (kvG δ σ0) (fun p => p.1) rfl logK_monotone hG
  have hLM := (proper_coordination_par logK (kvG δ σ0)).1 hP
  refine ⟨?_, ?_, rfl, logK_monotone, hG, hP, hP.1,
    (complete_calm _).2 (onDom_liftedMono Coh hLM)⟩
  · intro h
    obtain ⟨u, _, hall⟩ := h (⟨[c₁, c₂]⟩, .pt) (⟨[c₁, c₂]⟩, .pt) (PO.refl _)
      [⟨[c₁]⟩, ⟨[c₂]⟩] (by simp) (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl <;> intro c hc <;> simp_all)
    exact hne (pfx_head (l := []) (m := []) (hall ⟨[c₁]⟩ (by simp)) (hall ⟨[c₂]⟩ (by simp)))
  · intro h
    let x : Sub Coh := ⟨(⟨[c₁, c₂]⟩, (⟨[c₁, c₂]⟩, .pt)), fun _ hc => hc⟩
    have r1 : (onDom Coh (par logF (kvG δ σ0))).S x ⟨exec δ σ0 [c₁, c₂]⟩ :=
      ⟨⟨[c₁, c₂]⟩, fun _ hc => hc, rfl⟩
    have r2 : (onDom Coh (par logF (kvG δ σ0))).S x ⟨exec δ σ0 [c₂, c₁]⟩ := by
      refine ⟨⟨[c₂, c₁]⟩, fun c hc => ?_, rfl⟩
      show c ∈ [c₁, c₂]
      have hc' : c ∈ [c₂, c₁] := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc' ⊢
      rcases hc' with rfl | rfl <;> simp
    obtain ⟨u, _, hall⟩ := h x x (PO.refl _)
      [⟨exec δ σ0 [c₁, c₂]⟩, ⟨exec δ σ0 [c₂, c₁]⟩] (by simp) (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact r1
        · exact r2)
    have h1 := hall ⟨exec δ σ0 [c₁, c₂]⟩ (by simp)
    have h2 := hall ⟨exec δ σ0 [c₂, c₁]⟩ (by simp)
    simp only [exec] at h1 h2
    have := pfx_head h1 h2
    exact hne (congrArg Prod.fst this)

end Log

end AuditE
end CC
