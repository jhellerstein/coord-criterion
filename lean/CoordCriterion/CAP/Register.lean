import CoordCriterion.Foundations.Core
import CoordCriterion.Foundations.Runs
import CoordCriterion.CAP.ResponseForm

/-!
# Gilbert–Lynch for the linearizable register (Corollary `cor:gilbert-lynch`)

Appendix `app:cap-response`, subsection "Recovering Gilbert–Lynch".  This
file instantiates the response-form machinery of `CAP/ResponseForm.lean` with the linearizable register and proves
Corollary `cor:gilbert-lynch` as a genuine impossibility statement over *all*
systems (`gilbert_lynch`, and the variant with full Response Partition
Consistency, `gilbert_lynch_full`).

## Modeling choices

1. *Operations and histories.*  An operation is a replica index `rep : Nat`
   and a kind (`read` or `write v`, values `v : Nat`, initial value `v0 = 0`).
   An operation history `Hist` is a finite partial map from operation ids
   (`Nat`) to operations together with a strict partial order `prec`
   (real-time precedence) on the ids present.  Finiteness is the Prop
   `∃ N, ∀ a ≥ N, ops a = none`, so that the expansion order is antisymmetric
   (histories are equal when their maps and precedence relations are).
2. *Expansion* `h ≼ h'`: every operation of `h` is in `h'` (same id, same
   operation) and every precedence edge of `h` is in `h'`.
3. *Outputs* are response maps `RMap` (id ↦ optional `ack` / `val v`),
   ordered by extension.
4. *Linearizations* are position functions `pos : Nat → Nat`, injective on the
   ids present and strictly increasing along `prec`; this is the same as a
   total order of the operations extending `prec`.  A read's value is the
   value of the last write (all writes of `h`, acknowledged or not) before it,
   or `v0` if none.  The fiber `S(h)` (`regS`) consists of the maps explained
   by some linearization: every answered id is an operation of `h`, writes are
   answered `ack`, reads by their linearized value.
5. *Obligation.*  `regQ p h` is the set of maps of `S(h)` that answer every
   operation of `h` whose replica is `p`.  We prove it total (`regQ_total`;
   this needs the existence of linearizations, `lin_exists`) and upward
   closed within fibers (`regQ_upward`).  The obligation for participant
   `p : Fin n` is `regQ p.val`.
6. *Interleavings.*  An interleaving of a distributed history is a position
   function on its events (`pos p k` for the `k`-th event of `p`), injective,
   increasing along each local order and along send→receive edges; it is
   equivalent to a linear order consistent with happens-before.  A *prefix*
   is the set of events with position `< m`; `PrefixCut H pos m c` says the
   prefix is the cut with prefix lengths `c`.
7. *Realized history.*  The invocation of an operation `a` with record `op`
   is an input event, at the participant `op.rep`, whose input contains
   `a ↦ op`; its response is an output event at that participant whose map
   answers `a`.  `Realized H pos m j` says that `j` is the realized history
   `h_C` of the prefix `m`: its operations are those invoked in the prefix,
   and `a → b` is an edge iff some response of `a` precedes (in `pos`) every
   invocation of `b` (i.e. precedes `b`'s first invocation).  This is stated
   relationally: if the data are contradictory (two records for one id) no
   `j` is realized and the hypothesis is vacuous.
8. *The atomicity hypothesis* `RealizedRPC`: Response Partition Consistency
   (`CAP.RPCAt`) at the realized history of every prefix of every interleaving
   of every well-formed, produced, partitioned history, **whenever the
   realized history is a common expansion of the current inputs** (which is
   the precondition of Def. `def:response-partition-consistency`).  This is the
   weakest reading of the corollary's hypothesis, so the impossibility is the
   strongest one.  The paper claims the precondition always holds; it does
   not in general (`realized_not_expansion`), see below.

## Notes on the corollary's hypotheses

* The hypothesis "at `h_C` whenever `h_C` is a common expansion of the
  current inputs at `C`" (as the paper now states it) cannot be dropped: the
  adversarial environment may supply, in one input event, two operations at
  the same replica with a precedence edge between them; no response
  separates them, so the edge is not realized and `h_C` does not expand the
  current inputs (`realized_not_expansion`).  In the history of the proof
  the precondition holds (proved here).
* Invocations and responses are read as in the paper: the invocation of `a`
  is an input event at `a`'s replica whose input contains `a`; its response
  is an output event at that replica whose map answers `a` (item 7).
* The proof uses only Answering, applied twice, and goes through without
  `lem:forced-answer` as an intermediate.  The route through the lemma is
  `CC.CAP.gilbert_lynch_via_forced_answer` (`CAP/ResponseAvailability.lean`).
* Monotonicity of the realized history in the prefix holds
  (`realized_mono`).
-/

namespace CC
namespace GL

open CAP

/-! ## The register specification -/

inductive Kind where
  | read
  | write (v : Nat)
  deriving DecidableEq

structure Op where
  rep : Nat
  kind : Kind
  deriving DecidableEq

/-- Initial value of the register. -/
def v0 : Nat := 0

/-- A finite operation history with a strict partial order of precedence. -/
structure Hist where
  ops : Nat → Option Op
  prec : Nat → Nat → Prop
  fin : ∃ N, ∀ a, N ≤ a → ops a = none
  dom : ∀ a b, prec a b → ops a ≠ none ∧ ops b ≠ none
  irrefl : ∀ a, ¬ prec a a
  trans : ∀ a b c, prec a b → prec b c → prec a c

theorem Hist.ext' {h h' : Hist} (h1 : h.ops = h'.ops) (h2 : h.prec = h'.prec) : h = h' := by
  cases h; cases h'; cases h1; cases h2; rfl

theorem optFun_ext {α β : Type} {f g : α → Option β}
    (h1 : ∀ a x, f a = some x → g a = some x) (h2 : ∀ a x, g a = some x → f a = some x) :
    f = g := by
  funext a
  cases hf : f a with
  | some x => exact (h1 a x hf).symm
  | none =>
    cases hg : g a with
    | none => rfl
    | some y => rw [h2 a y hg] at hf; cases hf

instance : PO Hist where
  le h h' := (∀ a op, h.ops a = some op → h'.ops a = some op) ∧
    (∀ a b, h.prec a b → h'.prec a b)
  refl _ := ⟨fun _ _ h => h, fun _ _ h => h⟩
  trans h1 h2 := ⟨fun a op h => h2.1 a op (h1.1 a op h), fun a b h => h2.2 a b (h1.2 a b h)⟩
  antisymm h1 h2 := Hist.ext' (optFun_ext h1.1 h2.1)
    (funext fun a => funext fun b => propext ⟨h1.2 a b, h2.2 a b⟩)

inductive Resp where
  | ack
  | val (v : Nat)
  deriving DecidableEq

/-- A response map. -/
structure RMap where
  f : Nat → Option Resp

theorem RMap.ext' {ρ ρ' : RMap} (h : ρ.f = ρ'.f) : ρ = ρ' := by
  cases ρ; cases ρ'; cases h; rfl

instance : PO RMap where
  le ρ ρ' := ∀ a r, ρ.f a = some r → ρ'.f a = some r
  refl _ := fun _ _ h => h
  trans h1 h2 := fun a r h => h2 a r (h1 a r h)
  antisymm h1 h2 := RMap.ext' (optFun_ext h1 h2)

/-- A linearization of `h`: positions injective on the operations of `h` and
increasing along precedence. -/
def Lin (h : Hist) (pos : Nat → Nat) : Prop :=
  (∀ a b, h.ops a ≠ none → h.ops b ≠ none → pos a = pos b → a = b) ∧
  (∀ a b, h.prec a b → pos a < pos b)

def IsWrite (h : Hist) (w v : Nat) : Prop := ∃ r, h.ops w = some ⟨r, .write v⟩

/-- The read `k` returns `v` under `pos`: `v` is the value of the last write
before `k`, or `v0` if there is none. -/
def ReadVal (h : Hist) (pos : Nat → Nat) (k v : Nat) : Prop :=
  (v = v0 ∧ ∀ w v', IsWrite h w v' → ¬ pos w < pos k) ∨
  (∃ w, IsWrite h w v ∧ pos w < pos k ∧
    ∀ w' v', IsWrite h w' v' → pos w' < pos k → pos w' ≤ pos w)

/-- `r` is a correct response to operation `a = op` under `pos`. -/
def RespOk (h : Hist) (pos : Nat → Nat) (a : Nat) : Op → Resp → Prop
  | ⟨_, .write _⟩, r => r = .ack
  | ⟨_, .read⟩, r => ∃ v, r = .val v ∧ ReadVal h pos a v

def Explains (h : Hist) (pos : Nat → Nat) (ρ : RMap) : Prop :=
  ∀ a r, ρ.f a = some r → ∃ op, h.ops a = some op ∧ RespOk h pos a op r

/-- The fiber at `h`: maps explained by some linearization of `h`. -/
def regS : Table Hist RMap := fun h ρ => ∃ pos, Lin h pos ∧ Explains h pos ρ

/-! ### Every finite history has a linearization -/

theorem filter_len_le {l : List Nat} {P Q : Nat → Bool} (hPQ : ∀ x, P x = true → Q x = true) :
    (l.filter P).length ≤ (l.filter Q).length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.filter_cons]
    cases hp : P x <;> cases hq : Q x <;> simp <;> try omega
    rw [hPQ x hp] at hq; cases hq

theorem filter_len_lt {l : List Nat} {P Q : Nat → Bool} (hPQ : ∀ x, P x = true → Q x = true)
    {x0 : Nat} (hx : x0 ∈ l) (hQ : Q x0 = true) (hP : P x0 = false) :
    (l.filter P).length < (l.filter Q).length := by
  induction l with
  | nil => cases hx
  | cons x l ih =>
    simp only [List.filter_cons]
    rcases List.mem_cons.1 hx with rfl | hx'
    · rw [hP, hQ]; simp
      exact Nat.lt_succ_of_le (filter_len_le hPQ)
    · have := ih hx'
      cases hp : P x <;> cases hq : Q x <;> simp <;> try omega
      rw [hPQ x hp] at hq; cases hq

theorem lt_of_some {h : Hist} {N : Nat} (hN : ∀ a, N ≤ a → h.ops a = none) {a : Nat}
    (ha : h.ops a ≠ none) : a < N :=
  Nat.lt_of_not_le fun hle => ha (hN a hle)

theorem lin_exists (h : Hist) : ∃ pos, Lin h pos := by
  classical
  obtain ⟨N, hN⟩ := h.fin
  let cnt : Nat → Nat := fun a => ((List.range N).filter (fun b => decide (h.prec b a))).length
  refine ⟨fun a => N * cnt a + a, ?_, ?_⟩
  · intro a b ha hb he
    have ha' := lt_of_some hN ha
    have hb' := lt_of_some hN hb
    have := congrArg (· % N) he
    simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
    exact this
  · intro a b hab
    have ha' := lt_of_some hN (h.dom a b hab).1
    have hb' := lt_of_some hN (h.dom a b hab).2
    have hlt : cnt a < cnt b := by
      apply filter_len_lt (x0 := a)
      · intro x hx
        simp only [decide_eq_true_eq] at hx ⊢
        exact h.trans _ _ _ hx hab
      · exact List.mem_range.2 ha'
      · simpa using hab
      · simpa using h.irrefl a
    have : N * cnt a + N ≤ N * cnt b := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
    show N * cnt a + a < N * cnt b + b
    omega

theorem exists_max (l : List Nat) (P : Nat → Prop) (f : Nat → Nat) (hx : ∃ x ∈ l, P x) :
    ∃ x ∈ l, P x ∧ ∀ y ∈ l, P y → f y ≤ f x := by
  classical
  induction l with
  | nil => obtain ⟨_, h, _⟩ := hx; cases h
  | cons z l ih =>
    by_cases hl : ∃ x ∈ l, P x
    · obtain ⟨x, hxl, hPx, hmax⟩ := ih hl
      by_cases hz : P z ∧ f x ≤ f z
      · refine ⟨z, List.mem_cons_self .., hz.1, ?_⟩
        intro y hy hPy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Nat.le_refl _
        · exact Nat.le_trans (hmax y hy hPy) hz.2
      · refine ⟨x, List.mem_cons_of_mem _ hxl, hPx, ?_⟩
        intro y hy hPy
        rcases List.mem_cons.1 hy with rfl | hy
        · by_cases hc : f y ≤ f x
          · exact hc
          · exact absurd ⟨hPy, by omega⟩ hz
        · exact hmax y hy hPy
    · obtain ⟨x, hx, hPx⟩ := hx
      rcases List.mem_cons.1 hx with rfl | hx
      · refine ⟨x, List.mem_cons_self .., hPx, ?_⟩
        intro y hy hPy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Nat.le_refl _
        · exact absurd ⟨y, hy, hPy⟩ hl
      · exact absurd ⟨x, hx, hPx⟩ hl

theorem readVal_exists (h : Hist) (pos : Nat → Nat) (k : Nat) : ∃ v, ReadVal h pos k v := by
  classical
  by_cases hw : ∃ w v', IsWrite h w v' ∧ pos w < pos k
  · obtain ⟨N, hN⟩ := h.fin
    have hmem : ∀ w v', IsWrite h w v' → w ∈ List.range N := by
      rintro w v' ⟨r, hr⟩
      exact List.mem_range.2 (lt_of_some hN (by rw [hr]; simp))
    obtain ⟨w0, v0', hw0, hp0⟩ := hw
    obtain ⟨w, _, ⟨v, hwv, hpw⟩, hmax⟩ :=
      exists_max (List.range N) (fun w => ∃ v', IsWrite h w v' ∧ pos w < pos k) pos
        ⟨w0, hmem w0 v0' hw0, v0', hw0, hp0⟩
    exact ⟨v, Or.inr ⟨w, hwv, hpw, fun w' v' h1 h2 => hmax w' (hmem w' v' h1) ⟨v', h1, h2⟩⟩⟩
  · exact ⟨v0, Or.inl ⟨rfl, fun w v' h1 h2 => hw ⟨w, v', h1, h2⟩⟩⟩

/-- The register specification. -/
def regSpec : Spec Hist RMap where
  S := regS
  total h := by
    obtain ⟨pos, hl⟩ := lin_exists h
    exact ⟨⟨fun _ => none⟩, pos, hl, fun _ _ h => by cases h⟩

/-- The register's obligation: replica `p` answers every operation of `h`
invoked at `p`. -/
def regQ (p : Nat) : Table Hist RMap := fun h ρ =>
  regS h ρ ∧ ∀ a op, h.ops a = some op → op.rep = p → ρ.f a ≠ none

/-- `Q_p` is total. -/
theorem regQ_total (p : Nat) (h : Hist) : ∃ ρ, regQ p h ρ := by
  obtain ⟨pos, hl⟩ := lin_exists h
  have hc : ∀ a, ∃ r : Option Resp, (h.ops a = none → r = none) ∧
      ∀ op, h.ops a = some op → ∃ x, r = some x ∧ RespOk h pos a op x := by
    intro a
    cases ho : h.ops a with
    | none => exact ⟨none, fun _ => rfl, fun _ h => by cases h⟩
    | some op =>
      rcases op with ⟨r, _ | w⟩
      · obtain ⟨v, hv⟩ := readVal_exists h pos a
        refine ⟨some (.val v), (fun h => by cases h), ?_⟩
        intro op' h'
        cases h'
        exact ⟨_, rfl, v, rfl, hv⟩
      · refine ⟨some .ack, (fun h => by cases h), ?_⟩
        intro op' h'
        cases h'
        exact ⟨_, rfl, rfl⟩
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice hc
  refine ⟨⟨f⟩, ⟨pos, hl, ?_⟩, ?_⟩
  · intro a r hr
    have hr : f a = some r := hr
    cases ho : h.ops a with
    | none => rw [(hf a).1 ho] at hr; cases hr
    | some op =>
      obtain ⟨x, hx, hok⟩ := (hf a).2 op ho
      rw [hx] at hr; cases hr
      exact ⟨op, rfl, hok⟩
  · intro a op ho _
    obtain ⟨x, hx, _⟩ := (hf a).2 op ho
    show f a ≠ none
    rw [hx]; simp

/-- `Q_p` is upward closed within fibers. -/
theorem regQ_upward {p : Nat} {h : Hist} {ρ u : RMap} (hq : regQ p h ρ) (hu : regS h u)
    (hle : ρ ≼ u) : regQ p h u := by
  refine ⟨hu, fun a op ho hr => ?_⟩
  have := hq.2 a op ho hr
  cases hρ : ρ.f a with
  | none => exact absurd hρ this
  | some x => rw [hle a x hρ]; simp

/-! ## Interleavings and realized histories -/

variable {D : Type} {n : Nat}

/-- Distributed histories over the register specification. -/
abbrev RHist (D : Type) (n : Nat) := CAP.History regSpec D n

/-- An interleaving: positions of events, injective, increasing along each
local order and along send→receive edges. -/
def Interleaving (H : RHist D n) (pos : Fin n → Nat → Nat) : Prop :=
  (∀ p k p' k', k < (H p).length → k' < (H p').length → pos p k = pos p' k' →
    p = p' ∧ k = k') ∧
  (∀ p k k', k < k' → k' < (H p).length → pos p k < pos p k') ∧
  (∀ p k q k' j d, (H p)[k]? = some (LEv.recv q k' j d : LEv regSpec D n) → pos q k' < pos p k)

/-- The prefix of the interleaving of events with position `< m` is the cut
with prefix lengths `c`. -/
def PrefixCut (H : RHist D n) (pos : Fin n → Nat → Nat) (m : Nat) (c : Fin n → Nat) : Prop :=
  ∀ p, c p ≤ (H p).length ∧ ∀ k, k < (H p).length → (k < c p ↔ pos p k < m)

/-- The `k`-th event of `p` is an invocation of `a = op`: an input event at
the operation's replica whose input contains `a ↦ op`. -/
def IsInv (H : RHist D n) (a : Nat) (op : Op) (p : Fin n) (k : Nat) : Prop :=
  p.val = op.rep ∧ ∃ h, (H p)[k]? = some (LEv.inp h) ∧ h.ops a = some op

/-- The `k`-th event of `p` is a response to `a = op`: an output event at the
operation's replica whose map answers `a`. -/
def IsResp (H : RHist D n) (a : Nat) (op : Op) (p : Fin n) (k : Nat) : Prop :=
  p.val = op.rep ∧ ∃ γ ρ, (H p)[k]? = some (LEv.out γ ρ) ∧ ρ.f a ≠ none

/-- `j` is the realized history `h_C` of the prefix `m` of `pos`. -/
def Realized (H : RHist D n) (pos : Fin n → Nat → Nat) (m : Nat) (j : Hist) : Prop :=
  (∀ a op, j.ops a = some op ↔ ∃ p k, pos p k < m ∧ IsInv H a op p k) ∧
  (∀ a b, j.prec a b ↔ ∃ opa opb, j.ops a = some opa ∧ j.ops b = some opb ∧
    ∃ p k, IsResp H a opa p k ∧ ∀ p' k', IsInv H b opb p' k' → pos p k < pos p' k')

/-- `h_{C'} ≼ h_C` for prefixes `C' ⊆ C` of the same interleaving. -/
theorem realized_mono {H : RHist D n} {pos : Fin n → Nat → Nat} {m m' : Nat} {j j' : Hist}
    (hm : m' ≤ m) (h' : Realized H pos m' j') (h : Realized H pos m j) : j' ≼ j := by
  have hops : ∀ a op, j'.ops a = some op → j.ops a = some op := by
    intro a op ha
    obtain ⟨p, k, hp, hi⟩ := (h'.1 a op).1 ha
    exact (h.1 a op).2 ⟨p, k, Nat.lt_of_lt_of_le hp hm, hi⟩
  refine ⟨hops, fun a b hab => ?_⟩
  obtain ⟨opa, opb, ha, hb, p, k, hr, hall⟩ := (h'.2 a b).1 hab
  exact (h.2 a b).2 ⟨opa, opb, hops a opa ha, hops b opb hb, p, k, hr, hall⟩

/-- Atomicity (Corollary `cor:gilbert-lynch`): Response Partition Consistency
at the realized history of every prefix of every interleaving of every
partitioned history the system produces, whenever that realized history is a
common expansion of the current inputs. -/
def RealizedRPC (Sys : System regSpec D) : Prop :=
  ∀ (n : Nat) (init : Fin n → Hist) (H : RHist D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ pos, Interleaving H pos → ∀ m c, PrefixCut H pos m c →
    ∀ j, Realized H pos m j →
    (∀ p σ, LRun (canon regSpec (init p)) ((H p).take (c p)) σ → σ.cur ≼ j) →
    RPCAt H c j

/-! ### Helpers -/

theorem decomp_of_getElem? {α : Type} {l : List α} {k : Nat} {e : α} (h : l[k]? = some e) :
    l = l.take k ++ e :: l.drop (k + 1) := by
  obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.1 h
  subst he
  rw [List.getElem_cons_drop hk, List.take_append_drop]

theorem nil_ne_app {α : Type} {a b : List α} {e : α} : ([] : List α) ≠ a ++ e :: b := by
  cases a <;> simp

theorem norecv_of_inj {init : Fin n → Hist} {H : RHist D n} {comp : Fin n → Nat}
    (hwf : WF init H) (hpart : Partitioned H comp) (hinj : ∀ p q, comp p = comp q → p = q) :
    ∀ p (k : Nat) q (k' : Nat) j d, (H p)[k]? ≠ some (LEv.recv q k' j d : LEv regSpec D n) := by
  intro p k q k' j d h
  have hd := decomp_of_getElem? h
  exact (hwf.2 p _ q k' j d _ hd).1 (hinj q p (hpart.2 p _ q k' j d _ hd))

theorem full_cut {init : Fin n → Hist} {H : RHist D n} (hwf : WF init H) :
    IsCut H (fun p => (H p).length) := by
  refine ⟨fun _ => Nat.le_refl _, ?_⟩
  intro p a q k j d b h
  rw [List.take_length] at h
  obtain ⟨_, hs⟩ := hwf.2 p a q k j d b h
  exact (List.getElem?_eq_some_iff.1 hs).1

/-- Every prefix of an interleaving is a consistent cut. -/
theorem isCut_of_prefix {init : Fin n → Hist} {H : RHist D n} (hwf : WF init H)
    {pos : Fin n → Nat → Nat} (hi : Interleaving H pos) {m : Nat} {c : Fin n → Nat}
    (hc : PrefixCut H pos m c) : IsCut H c := by
  refine ⟨fun p => (hc p).1, ?_⟩
  intro p a q k j d b h
  have hfull : H p = a ++ LEv.recv q k j d :: (b ++ (H p).drop (c p)) := by
    conv => lhs; rw [← List.take_append_drop (c p) (H p)]
    rw [h]; simp
  have hlenT : a.length < ((H p).take (c p)).length := by rw [h]; simp
  rw [List.length_take] at hlenT
  have hlt : a.length < c p := Nat.lt_of_lt_of_le hlenT (Nat.min_le_left _ _)
  have hlen : a.length < (H p).length := Nat.lt_of_lt_of_le hlt (hc p).1
  have hget : (H p)[a.length]? = some (LEv.recv q k j d) := by rw [hfull]; simp
  have hposp := ((hc p).2 _ hlen).1 hlt
  have hq := hi.2.2 p a.length q k j d hget
  obtain ⟨_, hs⟩ := hwf.2 p a q k j d _ hfull
  have hkq : k < (H q).length := (List.getElem?_eq_some_iff.1 hs).1
  exact ((hc q).2 k hkq).2 (Nat.lt_trans hq hposp)

/-- The state after an input event. -/
def inpState (σ : State regSpec) (j : Hist) (u : RMap) (hu : σ.R j u) : State regSpec where
  cur := j
  R := inputTable σ j
  sub := fun k x h => σ.sub k x h.1
  hasCur := ⟨u, hu, PO.refl j⟩
  above := fun _ _ h => h.2

theorem inp_lrun {σ : State regSpec} {j : Hist} {u : RMap} (hu : σ.R j u) :
    LRun (n := n) (D := D) σ [LEv.inp j] (inpState σ j u hu) :=
  LRun.inp (Step.input _ _ j ⟨u, hu⟩ rfl rfl) (LRun.nil _)

/-! ### The histories of the proof -/

def emptyH : Hist where
  ops := fun _ => none
  prec := fun _ _ => False
  fin := ⟨0, fun _ _ => rfl⟩
  dom := fun _ _ h => h.elim
  irrefl := fun _ h => h
  trans := fun _ _ _ h => h.elim

theorem empty_le (h : Hist) : emptyH ≼ h := ⟨fun _ _ h => (by cases h), fun _ _ h => h.elim⟩

/-- The write of `1` (the paper's "dog") at replica 0, and a read at replica 1. -/
def wOp : Op := ⟨0, .write 1⟩
def rOp : Op := ⟨1, .read⟩

/-- `p`'s input after invoking the write. -/
def h1 : Hist where
  ops := fun a => if a = 0 then some wOp else none
  prec := fun _ _ => False
  fin := ⟨1, fun a ha => by split <;> first | rfl | omega⟩
  dom := fun _ _ h => h.elim
  irrefl := fun _ h => h
  trans := fun _ _ _ h => h.elim

/-- `q`'s input after invoking the read: `i_q = {r_q}`. -/
def h2 : Hist where
  ops := fun a => if a = 1 then some rOp else none
  prec := fun _ _ => False
  fin := ⟨2, fun a ha => by split <;> first | rfl | omega⟩
  dom := fun _ _ h => h.elim
  irrefl := fun _ h => h
  trans := fun _ _ _ h => h.elim

/-- The realized history `j`: the write, the read, and an edge from the write
to the read. -/
def hj : Hist where
  ops := fun a => if a = 0 then some wOp else if a = 1 then some rOp else none
  prec := fun a b => a = 0 ∧ b = 1
  fin := ⟨2, fun a ha => by (repeat' split) <;> first | rfl | omega⟩
  dom := by rintro a b ⟨rfl, rfl⟩; simp
  irrefl := by rintro a ⟨rfl, h⟩; cases h
  trans := by rintro a b c ⟨_, rfl⟩ ⟨h, _⟩; cases h

theorem h1_ops {a : Nat} {op : Op} (h : h1.ops a = some op) : a = 0 ∧ op = wOp := by
  simp only [h1] at h
  split at h
  · cases h; exact ⟨by assumption, rfl⟩
  · cases h

theorem h2_ops {a : Nat} {op : Op} (h : h2.ops a = some op) : a = 1 ∧ op = rOp := by
  simp only [h2] at h
  split at h
  · cases h; exact ⟨by assumption, rfl⟩
  · cases h

theorem hj_ops {a : Nat} {op : Op} (h : hj.ops a = some op) :
    (a = 0 ∧ op = wOp) ∨ (a = 1 ∧ op = rOp) := by
  simp only [hj] at h
  split at h
  · cases h; exact Or.inl ⟨by assumption, rfl⟩
  · split at h
    · cases h; exact Or.inr ⟨by assumption, rfl⟩
    · cases h

theorem h1_le : h1 ≼ hj :=
  ⟨fun a op h => by obtain ⟨rfl, rfl⟩ := h1_ops h; rfl, fun _ _ h => h.elim⟩

theorem h2_le : h2 ≼ hj :=
  ⟨fun a op h => by obtain ⟨rfl, rfl⟩ := h2_ops h; rfl, fun _ _ h => h.elim⟩

/-- Every linearization of `j` places the write before the read, so no map of
`S(j)` answers the read with `v0`. -/
theorem hj_noread (u : RMap) (hu : regS hj u) (h : u.f 1 = some (.val v0)) : False := by
  obtain ⟨pos, hl, hex⟩ := hu
  obtain ⟨op, hop, hok⟩ := hex 1 _ h
  have hop' : op = rOp := by
    rcases hj_ops hop with ⟨h', _⟩ | ⟨_, h'⟩
    · cases h'
    · exact h'
  subst hop'
  obtain ⟨v, hv, hrv⟩ := hok
  cases hv
  have hw : IsWrite hj 0 1 := ⟨0, rfl⟩
  have hp : pos 0 < pos 1 := hl.2 0 1 ⟨rfl, rfl⟩
  rcases hrv with ⟨_, hno⟩ | ⟨w, ⟨r, hw'⟩, _, _⟩
  · exact hno 0 1 hw hp
  · rcases hj_ops hw' with ⟨_, he⟩ | ⟨_, he⟩ <;> simp [wOp, rOp, v0] at he

/-- Every map of `Q_q(i_q)` answers the read with `v0`. -/
theorem h2_answer {o : RMap} (ho : regQ 1 h2 o) : o.f 1 = some (.val v0) := by
  obtain ⟨⟨pos, _, hex⟩, hans⟩ := ho
  have h21 : h2.ops 1 = some rOp := rfl
  have hne := hans 1 rOp h21 rfl
  cases hf : o.f 1 with
  | none => exact absurd hf hne
  | some r =>
    obtain ⟨op, hop, hok⟩ := hex 1 r hf
    rw [h21] at hop; cases hop
    obtain ⟨v, rfl, hrv⟩ := hok
    rcases hrv with ⟨rfl, _⟩ | ⟨w, ⟨r', hw⟩, _⟩
    · rfl
    · obtain ⟨_, he⟩ := h2_ops hw
      simp [rOp] at he

def pos2 (L0 : Nat) : Fin 2 → Nat → Nat := fun p k => p.val * L0 + k

theorem fin2 : ∀ p : Fin 2, p = 0 ∨ p = 1 := by decide

theorem inp_head {α : Type} {e : α} {A : List α} {P : α → Prop} (hA : ∀ x, P x → x ∉ A)
    {k : Nat} {x : α} (hk : (e :: A)[k]? = some x) (hx : P x) : k = 0 ∧ x = e := by
  cases k with
  | zero => simp at hk; exact ⟨rfl, hk.symm⟩
  | succ k =>
    simp at hk
    exact absurd (List.mem_of_getElem? hk) (hA x hx)

/-- The final step of the proof: in the constructed history, the realized
history `j` of the full prefix of the interleaving "all of `p`, then all of
`q`" is a common expansion of the current inputs, and Response Partition
Consistency there fails. -/
theorem final_contra (Sys : System regSpec D) (hRPC : RealizedRPC Sys) {init : Fin 2 → Hist}
    {H : RHist D 2} {comp : Fin 2 → Nat}
    (hwf : WF init H) (hprod : Produced Sys 2 init H) (hpart : Partitioned H comp)
    (hinj : ∀ p q, comp p = comp q → p = q)
    {A B : List (LEv regSpec D 2)} (hA : H 0 = LEv.inp h1 :: A) (hB : H 1 = LEv.inp h2 :: B)
    (hAi : ∀ j, LEv.inp j ∉ A) (hBi : ∀ j, LEv.inp j ∉ B)
    {γ γ' : List (Commitment regSpec)} {o o' : RMap}
    (ho : LEv.out γ o ∈ A) (hoQ : regQ 0 h1 o) (ho' : LEv.out γ' o' ∈ B)
    (ho'Q : regQ 1 h2 o') : False := by
  have hnr := norecv_of_inj hwf hpart hinj
  have inp0 : ∀ k h, (H 0)[k]? = some (LEv.inp h) → k = 0 ∧ h = h1 := by
    intro k h hk
    rw [hA] at hk
    obtain ⟨hk0, he⟩ := inp_head (P := fun x => ∃ h, x = LEv.inp h)
      (fun x ⟨h, hx⟩ => hx ▸ hAi h) hk ⟨h, rfl⟩
    cases he; exact ⟨hk0, rfl⟩
  have inp1 : ∀ k h, (H 1)[k]? = some (LEv.inp h) → k = 0 ∧ h = h2 := by
    intro k h hk
    rw [hB] at hk
    obtain ⟨hk0, he⟩ := inp_head (P := fun x => ∃ h, x = LEv.inp h)
      (fun x ⟨h, hx⟩ => hx ▸ hBi h) hk ⟨h, rfl⟩
    cases he; exact ⟨hk0, rfl⟩
  have hL0 : (H 0).length = A.length + 1 := by rw [hA]; rfl
  have hL1 : (H 1).length = B.length + 1 := by rw [hB]; rfl
  let L0 := (H 0).length
  let m := (H 0).length + (H 1).length
  have p0 : ∀ k, pos2 L0 0 k = k := fun k => by simp [pos2]
  have p1 : ∀ k, pos2 L0 1 k = L0 + k := fun k => by simp [pos2]
  have il : Interleaving H (pos2 L0) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p k p' k' hk hk' he
      rcases fin2 p with rfl | rfl <;> rcases fin2 p' with rfl | rfl <;>
        simp only [p0, p1] at he <;> refine ⟨?_, ?_⟩ <;> first | rfl | omega
    · intro p k k' hkk _
      rcases fin2 p with rfl | rfl <;> simp only [p0, p1] <;> omega
    · intro p k q k' j d h
      exact absurd h (hnr p k q k' j d)
  have pc : PrefixCut H (pos2 L0) m (fun p => (H p).length) := by
    intro p
    refine ⟨Nat.le_refl _, fun k hk => ⟨fun _ => ?_, fun _ => hk⟩⟩
    rcases fin2 p with rfl | rfl <;> simp only [p0, p1] <;> omega
  have hr : Realized H (pos2 L0) m hj := by
    constructor
    · intro a op
      constructor
      · intro h
        rcases hj_ops h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨0, 0, by rw [p0]; omega, rfl, h1, by rw [hA]; rfl, rfl⟩
        · exact ⟨1, 0, by rw [p1]; omega, rfl, h2, by rw [hB]; rfl, rfl⟩
      · rintro ⟨p, k, _, _, h, hk, hop⟩
        rcases fin2 p with rfl | rfl
        · obtain ⟨_, rfl⟩ := inp0 k h hk
          obtain ⟨rfl, rfl⟩ := h1_ops hop; rfl
        · obtain ⟨_, rfl⟩ := inp1 k h hk
          obtain ⟨rfl, rfl⟩ := h2_ops hop; rfl
    · intro a b
      constructor
      · rintro ⟨rfl, rfl⟩
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ho
        have hkA := (List.getElem?_eq_some_iff.1 hk).1
        refine ⟨wOp, rOp, rfl, rfl, 0, k + 1,
          ⟨rfl, γ, o, by rw [hA]; simpa using hk, hoQ.2 0 wOp rfl rfl⟩, ?_⟩
        rintro p' k' ⟨hrep, _⟩
        have : p' = 1 := Fin.ext hrep
        subst this
        rw [p0, p1]; omega
      · rintro ⟨opa, opb, ha, hb, p, k, ⟨hrep, _⟩, hall⟩
        rcases hj_ops hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have := hall 0 0 ⟨rfl, h1, by rw [hA]; rfl, rfl⟩
          rw [p0] at this; omega
        · rcases hj_ops ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨rfl, rfl⟩
          · have hp : p = 1 := Fin.ext hrep
            subst hp
            have := hall 1 0 ⟨rfl, h2, by rw [hB]; rfl, rfl⟩
            rw [p1, p1] at this; omega
  have hcur : ∀ p σ, LRun (canon regSpec (init p)) ((H p).take (H p).length) σ → σ.cur ≼ hj := by
    intro p σ hσ
    rw [List.take_length] at hσ
    rcases fin2 p with rfl | rfl
    · rw [hA] at hσ
      cases hσ with
      | inp hs hr => rw [lrun_noinp hr hAi, (step_input_inv hs).2.1]; exact h1_le
    · rw [hB] at hσ
      cases hσ with
      | inp hs hr => rw [lrun_noinp hr hBi, (step_input_inv hs).2.1]; exact h2_le
  obtain ⟨u, hu, hall⟩ := hRPC 2 init H comp hwf hprod hpart (pos2 L0) il m _ pc hj hr hcur
  have hle := hall 1 γ' o' (by rw [List.take_length, hB]; exact List.mem_cons_of_mem _ ho')
  exact hj_noread u hu (hle 1 _ (h2_answer ho'Q))

/-! ## Corollary `cor:gilbert-lynch` -/

/-- The register obligation for participant `p : Fin n`. -/
def regQn : (n : Nat) → Fin n → Table Hist RMap := fun _ p => regQ p.val

/-- **Corollary `cor:gilbert-lynch` (Gilbert–Lynch).**  No system for the
linearizable register has Response Availability (for the register's
per-replica obligation) and Response Partition Consistency at the realized
history `h_C` of every prefix `C` of every interleaving of every partitioned
history it produces.

The proof follows the paper: replicas `p = 0` and `q = 1` are in separate
components from the start; the environment invokes the write at `p`;
Answering makes `p` acknowledge it; the environment invokes the read at `q`
(after the acknowledgment in the interleaving); Answering makes `q` answer it,
necessarily with `v0`; at the realized history (write, read, write → read) no
map of the fiber answers the read with `v0`.  (We apply Answering directly
rather than through `forced_answer`, because we need to know that the
continuation adds only output/send events of `q` in order to compute the
realized history.) -/
theorem gilbert_lynch (Sys : System regSpec D) :
    ¬ (ResponseAvailability Sys regQn ∧ RealizedRPC Sys) := by
  rintro ⟨hRA, hRPC⟩
  let init : Fin 2 → Hist := fun _ => emptyH
  let comp : Fin 2 → Nat := fun p => p.val
  have hinj : ∀ p q : Fin 2, comp p = comp q → p = q := fun p q h => Fin.ext h
  have h01 : comp 1 ≠ comp 0 := by decide
  have h10 : comp 0 ≠ comp 1 := by decide
  let H0 : RHist D 2 := fun _ => []
  have wf0 : WF init H0 :=
    ⟨fun p => ⟨_, LRun.nil _⟩, fun p a q k j d b h => absurd h nil_ne_app⟩
  have prod0 : Produced Sys 2 init H0 := fun p a e b h => absurd h nil_ne_app
  have part0 : Partitioned H0 comp :=
    ⟨⟨0, 1, by decide⟩, fun p a q k j d b h => absurd h nil_ne_app⟩
  have cut0 : IsCut H0 (fun _ => 0) :=
    ⟨fun _ => Nat.zero_le _, fun p a q k j d b h => absurd h nil_ne_app⟩
  -- the environment invokes the write at `p`
  obtain ⟨u1, hu1⟩ := regSpec.total h1
  have hR1 : (canon regSpec emptyH).R h1 u1 := ⟨hu1, empty_le h1⟩
  obtain ⟨H1, ext1, hext1, wf1, prod1, part1, he10, he1q⟩ :=
    extend_single Sys wf0 prod0 part0 cut0 (p := 0) (σ := canon regSpec emptyH)
      (LRun.nil _) (e := LEv.inp h1) (by intro q k j d h; cases h) (inp_lrun hR1) trivial
  have e10 : H1 0 = [LEv.inp h1] := by rw [hext1 0, he10]; rfl
  have e11 : H1 1 = [] := by rw [hext1 1, he1q 1 (by decide)]; rfl
  -- Answering at `p`: `p` acknowledges the write
  have hτ1 : LRun (canon regSpec (init 0)) ((H1 0).take (H1 0).length)
      (inpState (canon regSpec emptyH) h1 u1 hR1) := by
    rw [List.take_length, e10]; exact inp_lrun hR1
  obtain ⟨⟨H2, ext2, hext2, wf2, prod2, part2, hloc2, hni2, γ, o, hQo, hmo⟩, _⟩ :=
    hRA 2 init H1 comp wf1 prod1 part1 _ (full_cut wf1) 0 _ hτ1
  have hQo : regQ 0 h1 o := hQo
  have e20 : H2 0 = LEv.inp h1 :: ext2 0 := by
    rw [hext2 0, List.take_length, e10]; rfl
  have e21 : H2 1 = [] := by
    rw [hext2 1, List.take_length, e11, hloc2 1 h01]; rfl
  -- the environment invokes the read at `q`
  obtain ⟨u2, hu2⟩ := regSpec.total h2
  have hR2 : (canon regSpec emptyH).R h2 u2 := ⟨hu2, empty_le h2⟩
  obtain ⟨H3, ext3, hext3, wf3, prod3, part3, he31, he3q⟩ :=
    extend_single Sys wf2 prod2 part2 (full_cut wf2) (p := 1) (σ := canon regSpec emptyH)
      (by rw [List.take_length, e21]; exact LRun.nil _) (e := LEv.inp h2)
      (by intro q k j d h; cases h) (inp_lrun hR2) trivial
  have e30 : H3 0 = LEv.inp h1 :: ext2 0 := by
    rw [hext3 0, List.take_length, e20, he3q 0 (by decide)]; simp
  have e31 : H3 1 = [LEv.inp h2] := by
    rw [hext3 1, List.take_length, e21, he31]; rfl
  -- Answering at `q`: `q` answers the read
  have hτ2 : LRun (canon regSpec (init 1)) ((H3 1).take (H3 1).length)
      (inpState (canon regSpec emptyH) h2 u2 hR2) := by
    rw [List.take_length, e31]; exact inp_lrun hR2
  obtain ⟨⟨H4, ext4, hext4, wf4, prod4, part4, hloc4, hni4, γ', o', hQo', hmo'⟩, _⟩ :=
    hRA 2 init H3 comp wf3 prod3 part3 _ (full_cut wf3) 1 _ hτ2
  have hQo' : regQ 1 h2 o' := hQo'
  have e40 : H4 0 = LEv.inp h1 :: ext2 0 := by
    rw [hext4 0, List.take_length, e30, hloc4 0 h10]; simp
  have e41 : H4 1 = LEv.inp h2 :: ext4 1 := by
    rw [hext4 1, List.take_length, e31]; rfl
  exact final_contra Sys hRPC wf4 prod4 part4 hinj e40 e41 hni2 hni4 hmo hQo hmo' hQo'

/-- Full Response Partition Consistency (at every common expansion) implies
the realized-history form, so the impossibility holds for it too. -/
theorem realizedRPC_of_responsePC {Sys : System regSpec D} (h : ResponsePC Sys) :
    RealizedRPC Sys := by
  intro n init H comp hwf hprod hpart pos hi m c hc j _ hcur
  exact h n init H comp hwf hprod hpart c (isCut_of_prefix hwf hi hc) j hcur

theorem gilbert_lynch_full (Sys : System regSpec D) :
    ¬ (ResponseAvailability Sys regQn ∧ ResponsePC Sys) :=
  fun ⟨hRA, hRPC⟩ => gilbert_lynch Sys ⟨hRA, realizedRPC_of_responsePC hRPC⟩

/-! ## The realized history need not expand the current inputs -/

/-- Two operations at replica 0 with a precedence edge, supplied in one
input event. -/
def hab : Hist where
  ops := fun a => if a = 0 then some ⟨0, .write 1⟩ else if a = 1 then some ⟨0, .read⟩ else none
  prec := fun a b => a = 0 ∧ b = 1
  fin := ⟨2, fun a ha => by (repeat' split) <;> first | rfl | omega⟩
  dom := by rintro a b ⟨rfl, rfl⟩; simp
  irrefl := by rintro a ⟨rfl, h⟩; cases h
  trans := by rintro a b c ⟨_, rfl⟩ ⟨h, _⟩; cases h

/-- The same operations without the edge. -/
def jab : Hist where
  ops := hab.ops
  prec := fun _ _ => False
  fin := hab.fin
  dom := fun _ _ h => h.elim
  irrefl := fun _ h => h
  trans := fun _ _ _ h => h.elim

/-- **Counterexample** to the paper's claim that `h_C` is a common expansion
of every participant's current input: for every system, the history in which
the environment hands replica 0 the input `hab` (a write and a read at
replica 0 with the write preceding the read) in a single input event has
realized history `jab` (no edge, since no response separates the two
invocations), which does not expand replica 0's current input `hab`. -/
theorem realized_not_expansion (Sys : System regSpec D) :
    ∃ (init : Fin 2 → Hist) (H : RHist D 2) (comp : Fin 2 → Nat) (pos : Fin 2 → Nat → Nat)
      (m : Nat) (c : Fin 2 → Nat) (j : Hist),
      WF init H ∧ Produced Sys 2 init H ∧ Partitioned H comp ∧ Interleaving H pos ∧
      PrefixCut H pos m c ∧ Realized H pos m j ∧
      ∃ σ : State regSpec, LRun (canon regSpec (init 0)) ((H 0).take (c 0)) σ ∧
        ¬ σ.cur ≼ j := by
  let init : Fin 2 → Hist := fun _ => emptyH
  let comp : Fin 2 → Nat := fun p => p.val
  have hinj : ∀ p q : Fin 2, comp p = comp q → p = q := fun p q h => Fin.ext h
  let H0 : RHist D 2 := fun _ => []
  have wf0 : WF init H0 :=
    ⟨fun p => ⟨_, LRun.nil _⟩, fun p a q k j d b h => absurd h nil_ne_app⟩
  have prod0 : Produced Sys 2 init H0 := fun p a e b h => absurd h nil_ne_app
  have part0 : Partitioned H0 comp :=
    ⟨⟨0, 1, by decide⟩, fun p a q k j d b h => absurd h nil_ne_app⟩
  have cut0 : IsCut H0 (fun _ => 0) :=
    ⟨fun _ => Nat.zero_le _, fun p a q k j d b h => absurd h nil_ne_app⟩
  obtain ⟨u1, hu1⟩ := regSpec.total hab
  have hR1 : (canon regSpec emptyH).R hab u1 := ⟨hu1, empty_le hab⟩
  obtain ⟨H, ext1, hext1, wf, prod, part, he10, he1q⟩ :=
    extend_single Sys wf0 prod0 part0 cut0 (p := 0) (σ := canon regSpec emptyH)
      (LRun.nil _) (e := LEv.inp hab) (by intro q k j d h; cases h) (inp_lrun hR1) trivial
  have e0 : H 0 = [LEv.inp hab] := by rw [hext1 0, he10]; rfl
  have e1 : H 1 = [] := by rw [hext1 1, he1q 1 (by decide)]; rfl
  have hnr := norecv_of_inj wf part hinj
  have p0 : ∀ k, pos2 1 0 k = k := fun k => by simp [pos2]
  have p1 : ∀ k, pos2 1 1 k = 1 + k := fun k => by simp [pos2]
  refine ⟨init, H, comp, pos2 1, 1, fun p => (H p).length, jab, wf, prod, part, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro p k p' k' hk hk' _
      rcases fin2 p with rfl | rfl <;> rcases fin2 p' with rfl | rfl <;>
        simp only [e0, e1, List.length_cons, List.length_nil] at hk hk' <;>
        refine ⟨?_, ?_⟩ <;> first | rfl | omega
    · intro p k k' _ hk'
      rcases fin2 p with rfl | rfl <;> simp only [e0, e1, List.length_cons, List.length_nil] at hk' <;>
        omega
    · intro p k q k' j d h; exact absurd h (hnr p k q k' j d)
  · intro p
    refine ⟨Nat.le_refl _, fun k hk => ?_⟩
    rcases fin2 p with rfl | rfl <;> simp only [e0, e1, List.length_cons, List.length_nil] at hk ⊢ <;>
      simp only [p0, p1] <;> omega
  · constructor
    · intro a op
      constructor
      · intro h
        refine ⟨0, 0, by rw [p0]; omega, ?_, hab, by rw [e0]; rfl, h⟩
        show 0 = op.rep
        simp only [jab, hab] at h
        split at h
        · cases h; rfl
        · split at h
          · cases h; rfl
          · cases h
      · rintro ⟨p, k, _, _, h, hk, hop⟩
        rcases fin2 p with rfl | rfl
        · rw [e0] at hk
          cases k with
          | zero => simp at hk; subst hk; exact hop
          | succ k => simp at hk
        · rw [e1] at hk; simp at hk
    · intro a b
      constructor
      · intro h; exact h.elim
      · rintro ⟨_, _, _, _, p, k, ⟨_, γ, ρ, hk, _⟩, _⟩
        rcases fin2 p with rfl | rfl
        · rw [e0] at hk
          cases k with
          | zero => simp at hk
          | succ k => simp at hk
        · rw [e1] at hk; simp at hk
  · refine ⟨inpState (canon regSpec emptyH) hab u1 hR1, ?_, ?_⟩
    · show LRun _ ((H 0).take (H 0).length) _
      rw [List.take_length, e0]; exact inp_lrun hR1
    · intro hle
      exact hle.2 0 1 ⟨rfl, rfl⟩

end GL
end CC
