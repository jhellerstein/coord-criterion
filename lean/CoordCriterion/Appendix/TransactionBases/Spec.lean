import CoordCriterion.Appendix.TransactionBases.NoReads

/-!
# The transaction specification of Appendix G (`app:cc-bases`): inputs, outputs, rows

Namespace `CC.Txn.Partial`.  Inputs are finite sets of transactions, each given
by the sequence of operations its client has issued so far (reads and writes of
keys) and whether it has requested commit.  Outputs `(L,X,ρ)` may leave
transactions undecided and may report read results, identified by position, of
undecided transactions, as 2PL and MVTO schedulers do.

* `Acc`, `Seq`, `Inp` — operations, per-transaction sequences (ordered by
  prefix, frozen once commit is requested), inputs (ordered by inclusion of
  transactions and prefix of sequences).
* `ROut` — outputs `(L,X,ρ)`; `ρ a n = some v` reports that the `n`-th
  operation of `a` (a read) returned `v` (`none`: the initial version;
  `some W`: the write by `W`).
* `Valid`, `LastWrite`, `OwnW`, `ReadOK`, `Decides`, `Complete`, `spec` — the
  specification (`af = true`: the abort-free variant).

Modeling choices: the version a transaction installs for a key is its last
write of that key, so a version is named by its writer.  A complete output of
the specification decides every transaction of the input and commits only
transactions that have requested commit; in the abort-free variant a complete
output aborts nothing, commits exactly the transactions that have requested
commit, and leaves the others undecided.
-/

namespace CC
namespace Txn
namespace Partial

open Classical

set_option linter.unusedSimpArgs false

variable {T K : Type}

/-! ### Inputs -/

/-- An operation: a read or a write of a key. -/
inductive Acc (K : Type) where
  | rd (x : K)
  | wr (x : K)

/-- What a client has issued for one transaction so far: its operations in
order, and whether it has requested commit. -/
structure Seq (K : Type) where
  ops : List (Acc K)
  req : Bool

/-- Nothing issued. -/
def Seq.empty : Seq K := ⟨[], false⟩

/-- `s ≼ s'`: `s.ops` is a prefix of `s'.ops`, and once commit has been
requested the sequence no longer changes. -/
def Seq.le (s s' : Seq K) : Prop := (∃ l, s'.ops = s.ops ++ l) ∧ (s.req = true → s' = s)

theorem Seq.ext' {s s' : Seq K} (h1 : s.ops = s'.ops) (h2 : s.req = s'.req) : s = s' := by
  cases s; cases s'; cases h1; cases h2; rfl

instance instPOSeq (K : Type) : PO (Seq K) where
  le := Seq.le
  refl s := ⟨⟨[], by simp⟩, fun _ => rfl⟩
  trans {a b c} h1 h2 := by
    refine ⟨?_, fun h => ?_⟩
    · obtain ⟨l1, e1⟩ := h1.1; obtain ⟨l2, e2⟩ := h2.1
      exact ⟨l1 ++ l2, by rw [e2, e1, List.append_assoc]⟩
    · have e := h1.2 h
      have hb : b.req = true := by rw [e]; exact h
      rw [h2.2 hb, e]
  antisymm {a b} h1 h2 := by
    obtain ⟨l1, e1⟩ := h1.1
    obtain ⟨l2, e2⟩ := h2.1
    have hl : l1 = [] := by
      have := congrArg List.length (e2.trans (congrArg (· ++ l2) e1))
      simp only [List.length_append] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    have eo : a.ops = b.ops := by rw [e1, hl, List.append_nil]
    cases ha : a.req with
    | true => exact (h1.2 ha).symm
    | false =>
      cases hb : b.req with
      | true => exact h2.2 hb
      | false => exact Seq.ext' eo (ha.trans hb.symm)

/-- **An input**: a finite set of transactions, each with the sequence its
client has issued so far.  Transactions outside the set have issued nothing. -/
structure Inp (T K : Type) where
  txs : FinSet T
  tx : T → Seq K
  out : ∀ t, ¬ txs.1 t → tx t = Seq.empty

theorem Inp.ext' {i j : Inp T K} (h1 : i.txs = j.txs) (h2 : i.tx = j.tx) : i = j := by
  cases i; cases j; cases h1; cases h2; rfl

/-- `i ≼ j`: every transaction of `i` is in `j`, and its sequence in `i` is a
prefix of its sequence in `j` (frozen once commit is requested). -/
instance instPOInp (T K : Type) : PO (Inp T K) where
  le i j := (∀ t, i.txs.1 t → j.txs.1 t) ∧ ∀ t, i.tx t ≼ j.tx t
  refl i := ⟨fun _ h => h, fun t => PO.refl (i.tx t)⟩
  trans h1 h2 := ⟨fun t h => h2.1 t (h1.1 t h), fun t => PO.trans (h1.2 t) (h2.2 t)⟩
  antisymm h1 h2 :=
    Inp.ext' (PO.antisymm (α := FinSet T) h1.1 h2.1) (funext fun t => PO.antisymm (h1.2 t) (h2.2 t))

namespace Inp
variable (i : Inp T K)

/-- `t` is a transaction of `i`. -/
def mem (t : T) : Prop := i.txs.1 t
/-- `t` has requested commit in `i`. -/
def fin (t : T) : Prop := (i.tx t).req = true
/-- The `n`-th operation of `t` in `i` (counting from `0`). -/
def op (t : T) (n : Nat) : Option (Acc K) := (i.tx t).ops[n]?
/-- `t` writes `x` in `i`. -/
def writes (t : T) (x : K) : Prop := Acc.wr x ∈ (i.tx t).ops

variable {i}

theorem fin_mem {t : T} (h : i.fin t) : i.mem t :=
  Classical.byContradiction fun hn => by
    have e := i.out t hn
    unfold fin at h; rw [e] at h; cases h

theorem writes_mem {t : T} {x : K} (h : i.writes t x) : i.mem t :=
  Classical.byContradiction fun hn => by
    have e := i.out t hn
    unfold writes at h; rw [e] at h; cases h

theorem op_mem {t : T} {n : Nat} {a : Acc K} (h : i.op t n = some a) : i.mem t :=
  Classical.byContradiction fun hn => by
    have e := i.out t hn
    unfold op at h; rw [e] at h; cases h

theorem op_writes {t : T} {n : Nat} {x : K} (h : i.op t n = some (.wr x)) : i.writes t x :=
  List.mem_of_getElem? h

variable {j : Inp T K}

theorem le_mem (h : i ≼ j) {t : T} (ht : i.mem t) : j.mem t := h.1 t ht

theorem le_tx (h : i ≼ j) {t : T} (ht : i.fin t) : j.tx t = i.tx t := (h.2 t).2 ht

theorem le_fin (h : i ≼ j) {t : T} (ht : i.fin t) : j.fin t := by
  unfold fin; rw [le_tx h ht]; exact ht

theorem le_op (h : i ≼ j) {t : T} {n : Nat} {a : Acc K} (ht : i.op t n = some a) :
    j.op t n = some a := by
  obtain ⟨l, e⟩ := (h.2 t).1
  unfold op at ht ⊢
  rw [e, List.getElem?_append_left (List.getElem?_eq_some_iff.1 ht).1]; exact ht

theorem le_writes (h : i ≼ j) {t : T} {x : K} (ht : i.writes t x) : j.writes t x := by
  obtain ⟨l, e⟩ := (h.2 t).1
  unfold writes at ht ⊢
  rw [e]; exact List.mem_append_left _ ht

/-- Once `t` has requested commit, its operations and writes are fixed. -/
theorem le_op_fin (h : i ≼ j) {t : T} (ht : i.fin t) (n : Nat) : j.op t n = i.op t n := by
  unfold op; rw [le_tx h ht]

theorem le_writes_fin (h : i ≼ j) {t : T} (ht : i.fin t) (x : K) :
    j.writes t x ↔ i.writes t x := by
  unfold writes; rw [le_tx h ht]

end Inp

/-- The input whose transactions are those of `l`, with `t` having issued `s t`. -/
noncomputable def Inp.ofList (l : List T) (hl : l.Nodup) (s : T → Seq K) : Inp T K where
  txs := FinSet.ofList l hl
  tx t := if t ∈ l then s t else Seq.empty
  out t h := by
    have h' : t ∉ l := h
    simp [h']

theorem Inp.ofList_mem {l : List T} {hl : l.Nodup} {s : T → Seq K} {t : T} :
    (Inp.ofList l hl s).mem t ↔ t ∈ l := Iff.rfl

theorem Inp.ofList_tx {l : List T} {hl : l.Nodup} {s : T → Seq K} {t : T} (h : t ∈ l) :
    (Inp.ofList l hl s).tx t = s t := by simp [Inp.ofList, h]

/-! ### Outputs `(L, X, ρ)` -/

/-- An output `(L,X,ρ)`: `ρ a n = some v` reports that the `n`-th operation of
`a` returned the version `v`. -/
structure ROut (T K : Type) where
  o : Outcome T
  ρ : T → Nat → Option (Option T)

/-- `(L,X,ρ) ≼ (L',X',ρ')` iff `(L,X) ≼ (L',X')` and `ρ ⊆ ρ'`. -/
def ROut.le (r r' : ROut T K) : Prop :=
  r.o ≼ r'.o ∧ ∀ a n v, r.ρ a n = some v → r'.ρ a n = some v

theorem ROut.ext' {r r' : ROut T K} (h1 : r.o = r'.o) (h2 : r.ρ = r'.ρ) : r = r' := by
  cases r; cases r'; cases h1; cases h2; rfl

instance instPOROut (T K : Type) : PO (ROut T K) where
  le := ROut.le
  refl r := ⟨PO.refl r.o, fun _ _ _ h => h⟩
  trans h1 h2 := ⟨PO.trans h1.1 h2.1, fun a n v h => h2.2 a n v (h1.2 a n v h)⟩
  antisymm {r r'} h1 h2 := by
    apply ROut.ext' (PO.antisymm h1.1 h2.1)
    funext a n
    cases e : r.ρ a n with
    | none =>
      cases e' : r'.ρ a n with
      | none => rfl
      | some v =>
        have h := h2.2 a n v e'
        rw [e] at h; cases h
    | some v => exact (h1.2 a n v e).symm

theorem le_ρ {r r' : ROut T K} (h : r ≼ r') {a : T} {n : Nat} {v : Option T}
    (e : r.ρ a n = some v) : r'.ρ a n = some v := h.2 a n v e

/-! ### The specification -/

/-- `v` is a version of `x` present at `k`: the initial version, or the write
of `x` by a transaction of `k`. -/
def Valid (k : Inp T K) (x : K) : Option T → Prop
  | none => True
  | some W => k.writes W x

/-- `v` is the write of `x` by the last transaction before `a` in `L` that
writes `x`, or the initial version if none does. -/
def LastWrite (k : Inp T K) (o : Outcome T) (a : T) (x : K) : Option T → Prop
  | none => ∀ w, o.lt w a → ¬ k.writes w x
  | some w => o.lt w a ∧ k.writes w x ∧ ∀ w', o.lt w w' → o.lt w' a → ¬ k.writes w' x

/-- `a` writes `x` before its `n`-th operation. -/
def OwnW (k : Inp T K) (a : T) (n : Nat) (x : K) : Prop :=
  ∃ m, m < n ∧ k.op a m = some (.wr x)

/-- The read rule for a committed reader: the `n`-th operation of `a`, a read
of `x`, returns `a`'s own write if `a` writes `x` earlier, and otherwise the
last earlier write in `L`. -/
def ReadOK (k : Inp T K) (o : Outcome T) (a : T) (n : Nat) (x : K) (v : Option T) : Prop :=
  (OwnW k a n x → v = some a) ∧ (¬ OwnW k a n x → LastWrite k o a x v)

/-- `(L,X)` is complete at `k`.  `af = false`: it commits or aborts every
transaction of `k`, not both, and commits only transactions that have
requested commit.  `af = true` (abort-free): it aborts nothing and commits
exactly the transactions that have requested commit. -/
def Decides : Bool → Inp T K → Outcome T → Prop
  | false, k, o => Partitions k.txs o ∧ ∀ t, o.dom t → k.fin t
  | true, k, o => ∀ t, ¬ o.X t ∧ (o.dom t ↔ k.fin t)

/-- A permitted complete output `(L,X,ρ)` at `k`: `(L,X)` is complete, each
reported read is the result of a read operation of `k` returning a version
present at `k`, and a read by a committed transaction follows the read rule.
(Reads by other transactions are otherwise unconstrained.) -/
def Complete (af : Bool) (k : Inp T K) (r : ROut T K) : Prop :=
  Decides af k r.o ∧
    ∀ a n v, r.ρ a n = some v →
      ∃ x, k.op a n = some (.rd x) ∧ Valid k x v ∧ (r.o.dom a → ReadOK k r.o a n x v)

/-- No reads reported. -/
def full (o : Outcome T) : ROut T K := ⟨o, fun _ _ => none⟩

theorem full_complete {af : Bool} {k : Inp T K} {o : Outcome T} (h : Decides af k o) :
    Complete af k (full (K := K) o) :=
  ⟨h, fun _ _ _ e => by cases e⟩

/-- Abort everything is complete (`af = false`). -/
theorem allAbort_decides (k : Inp T K) : Decides false k (allAbort k.txs) :=
  ⟨fun _ => ⟨⟨Or.inl, fun h => h.elim id False.elim⟩, fun h => h.2⟩, fun _ h => h.elim⟩

/-- Commit exactly the transactions that requested commit, in some order
(`af = true`). -/
theorem abortFree_decides (k : Inp T K) : ∃ o : Outcome T, Decides true k o := by
  obtain ⟨l, _, hl⟩ := k.txs.2
  refine ⟨listOrder (l.filter fun t => decide (k.fin t)), fun t => ⟨fun h => h, ?_⟩⟩
  show t ∈ l.filter _ ↔ _
  rw [List.mem_filter, ← hl, decide_eq_true_iff]
  exact ⟨fun h => h.2, fun h => ⟨Inp.fin_mem h, h⟩⟩

/-- **The specification** (`af = false`) and its abort-free variant
(`af = true`): a row is permitted when some permitted complete output at the
same input refines it. -/
def spec (af : Bool) : Spec (Inp T K) (ROut T K) where
  S k u := ∃ c, Complete af k c ∧ u ≼ c
  total k := by
    cases af with
    | false => exact ⟨full (allAbort k.txs), _, full_complete (allAbort_decides k), PO.refl _⟩
    | true =>
      obtain ⟨o, ho⟩ := abortFree_decides k
      exact ⟨full o, _, full_complete ho, PO.refl _⟩

/-! ### Facts about complete outputs -/

section Decides
variable {af : Bool} {k : Inp T K}

theorem Decides.dom_fin {o : Outcome T} (h : Decides af k o) {t : T} (ht : o.dom t) : k.fin t := by
  cases af with
  | false => exact h.2 t ht
  | true => exact ((h t).2).1 ht

theorem Decides.dom_mem {o : Outcome T} (h : Decides af k o) {t : T} (ht : o.dom t) : k.mem t :=
  Inp.fin_mem (h.dom_fin ht)

theorem Decides.not_both {o : Outcome T} (h : Decides af k o) (t : T) : ¬ (o.X t ∧ o.dom t) := by
  cases af with
  | false => exact (h.1 t).2
  | true => exact fun hb => (h t).1 hb.1

/-- Comparable complete outputs at one input are equal. -/
theorem decides_antichain {a b : Outcome T} (ha : Decides af k a) (hb : Decides af k b)
    (h : a ≼ b) : a = b := by
  cases af with
  | false => exact partitions_antichain ha.1 hb.1 h
  | true =>
    have hd : ∀ t, a.dom t ↔ b.dom t := fun t => ((ha t).2).trans ((hb t).2).symm
    apply Outcome.ext'
    · funext t; exact propext ⟨fun h' => absurd h' (ha t).1, fun h' => absurd h' (hb t).1⟩
    · funext t; exact propext (hd t)
    · funext s t
      apply propext
      constructor
      · intro hl
        have hs := a.supp s t hl
        exact (h.2.2 s t hs.1 hs.2).2 hl
      · intro hl
        have hs := b.supp s t hl
        exact (h.2.2 s t ((hd s).2 hs.1) ((hd t).2 hs.2)).1 hl

/-- In the specification, a complete output decides every transaction of the
input. -/
theorem Decides.decided {o : Outcome T} (h : Decides false k o) {t : T} (ht : k.mem t) :
    o.X t ∨ o.dom t := ((h.1 t).1).1 ht

/-- In the abort-free variant, a complete output commits every transaction that
has requested commit. -/
theorem Decides.dom_of_fin {o : Outcome T} (h : Decides true k o) {t : T} (ht : k.fin t) :
    o.dom t := ((h t).2).2 ht

end Decides

/-- Comparable complete outputs at one input have the same `(L,X)`. -/
theorem same_o {af : Bool} {k : Inp T K} {a b : ROut T K} (ha : Decides af k a.o)
    (hb : Decides af k b.o) (h : a ≼ b) : a.o = b.o :=
  decides_antichain ha hb h.1

section Rows
variable {af : Bool}

/-- Rows are closed downward (within the output order). -/
theorem spec_down {k : Inp T K} {u w : ROut T K} (hw : (spec af).S k w) (h : u ≼ w) :
    (spec af).S k u :=
  let ⟨c, hc, hwc⟩ := hw; ⟨c, hc, PO.trans h hwc⟩

/-- A row that is complete is a permitted complete output. -/
theorem permitted_of_row {k : Inp T K} {c : ROut T K} (hc : (spec af).S k c)
    (hp : Decides af k c.o) : Complete af k c := by
  obtain ⟨c', ⟨hp', hρ'⟩, hle⟩ := hc
  have e := same_o hp hp' hle
  refine ⟨hp, fun a n v hv => ?_⟩
  rw [e]
  exact hρ' a n v (le_ρ hle hv)

/-- The read facts of any row are results of read operations of its input,
returning versions present there. -/
theorem row_read {k : Inp T K} {u : ROut T K} (hu : (spec af).S k u) {a : T} {n : Nat}
    {v : Option T} (e : u.ρ a n = some v) : ∃ x, k.op a n = some (.rd x) ∧ Valid k x v := by
  obtain ⟨c, ⟨_, hρ⟩, hle⟩ := hu
  obtain ⟨x, h1, h2, _⟩ := hρ a n v (le_ρ hle e)
  exact ⟨x, h1, h2⟩

/-- A row commits only transactions that have requested commit. -/
theorem row_dom {k : Inp T K} {u : ROut T K} (hu : (spec af).S k u) {t : T}
    (h : u.o.dom t) : k.fin t := by
  obtain ⟨c, ⟨hp, _⟩, hle⟩ := hu
  exact hp.dom_fin (hle.1.2.1 t h)

end Rows

end Partial
end Txn
end CC
