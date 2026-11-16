import CoordCriterion.Instances.HATSpec
import CoordCriterion.Appendix.Intersection
import CoordCriterion.CAP.AvailabilityFor

/-!
# The HAT taxonomy: model, phenomena, specifications (Bailis et al., Table 3)

Bailis et al., "Highly Available Transactions: Virtues and Limitations"
(VLDB 2014; extended version with App. A "Formal Definitions" and App. B "Monotonic
Atomic View Isolation") classify isolation levels and session guarantees as
highly available (HA: RU, RC, MAV, I-CI, P-CI, WFR, MR, MW), sticky available
(RYW, PRAM, causal), or unavailable (preventing Lost Update or Write Skew, or
requiring recency).  This file extends the HAT model of `Instances/HATSpec.lean`
(Def. `def:hat-spec`) with what the classification needs, and states each
guarantee by the phenomenon the extended paper's App. A proscribes.  The
classification itself is derived from our theorems in
`Instances/HATTaxonomyRules.lean` and `Instances/HATTaxonomyWitness.lean`.

## Inputs (`SInp reps lam`)

Legal inputs of `HATSpec` (event histories with happens-before, `WF`, and with
`lam = true` the timestamp condition `Lamport`), plus `Sess reps`:

* `reps k` lists the replicas of item `k` (partial replication, Bailis §4);
  every read is received by a replica of each item it reads;
* predicate reads (`Ev.prd c n ks r`, a read over the item range `ks`) precede
  their transaction's commit, like item reads;
* a transaction's reads are totally ordered by happens-before (client program
  order);
* a client runs its transactions one at a time: once a transaction has
  committed, the client's later committed transactions perform all their reads
  after that commit;
* a client's commit timestamps increase along its session (Bailis §5.1.3, MW: "Any
  order on transactions ... should also be consistent with any precedence that a
  global observer would see"; the patched client of `Instances/HATRC.lean`, whose
  clock advances, has this property).

A session is a client; its session order is the happens-before order of its
commits (extended paper, App. A.1: "sessions as a partial ordering on committed
transactions"; Def. 15, session-dependency).

## Outputs and complete histories

An output is a set of answers `rv e k v`: the read access `(e, k)` returned the
version with timestamp `v`.  An item read `rd c n k r` has the one access
`(e, k)`; a predicate read `prd c n ks r` has an access `(e, k)` for every `k`
in its range: its version set `Vset(P)` (extended paper, Def. 1).  A complete
history `CH2` answers every access with a version the transaction may read
(`HATSpec.Ver`).

## Phenomena (extended paper, App. A)

The direct serialization graph has the item edges of `HATSpec` (`wwI`, and
`wr2`/`rw2` from item reads) and session edges `sess`.  Following the paper:

* IMP (Def. 22, I-CI): a transaction item-read-depends by `x` on two
  different transactions.
* PMP (Def. 24, P-CI): two predicate reads of one transaction with overlapping
  ranges see different sets of transactions changing their matches.  Predicates
  are item ranges and a tuple matches when present, so the transaction that
  changes the matches of `x` is the one installing `x`'s first version (an
  insert; deletes are not modeled).  *Def. 24 says "for all predicate-based
  reads ...", which holds vacuously when a transaction has no pair of predicate
  reads; we read it as "for some".*
* OTV (Def. 26, MAV with RC): `T_i` reads `x` from `T_j` and later reads a
  version of `y` that `T_j` overwrote (a read-dependency by `x` from `T_j` to
  `T_i`, then an anti-dependency by `y` from `T_i`'s later read followed by
  write-dependencies by `y` to `T_j`).  *Def. 26 says "`T_j`'s read from `y`
  precedes its read from `x`"; in its own example (Fig. 9) it is `T_i` that
  reads, `x` before `y`, and we follow the example.*
* N-MR (Def. 28, MR): `T_i` precedes `T_j` in a session, `T_i` read `x` from
  `T_l`, and `T_j` read an earlier version of `x` (an anti-dependency by `x`
  from `T_j`, write-dependencies by `x`, a read-dependency by `x` into `T_i`).
  We allow the write-dependencies between the anti-dependency and the
  read-dependency; without them the cycle misses non-monotonic reads that skip
  an intermediate version.
* N-MW (Def. 30, MW): as written, a cycle of a transitive session-dependency
  and write-dependency edges (the version order contradicts the session order),
  *or* the anomaly of the paper's own example (Fig. 13/14): `T_k` reads `y` from
  `T_j` and an `x` older than that of `T_i`, which precedes `T_j` in their session.
  *Def. 30 requires a write-dependency edge, which Fig. 14 does not have.*
* MRWD (Defs. 32/33, WFR): `T_2` read `x` from `T_1`, `T_3` read `y` from `T_2`,
  and `T_3` directly anti-depends on `T_1` by `x`.  *Def. 32 says "for all ...
  `T_3` does not directly anti-depend on `T_1`", the condition for the absence of
  the phenomenon, and says "write-depends" where its example (Fig. 15/16) has
  read-dependencies; Defs. 33 and 37 call it MWRD.*
* MYR (Def. 34, RYW): `MYRlit` is the definition as written (a cycle of a
  transitive session-dependency, at least one anti-dependency, the remainder
  anti- or write-dependencies); `MYR` is its single-item form, which its example
  (Fig. 17/18) has: `T_i` precedes `T_j` in a session, `T_i` wrote `x`, and `T_j`
  read an earlier version of `x`.  `Instances/HATTaxonomyWitness.lean` shows that
  `MYRlit` is not sticky available (a finding), while `MYR` is.
* PRAM (Def. 36): N-MR, N-MW, MYR.  Causal (Def. 37): PRAM and MRWD.
* RC (Def. 21): G0, G1a, G1b, G1c; G1a and G1b cannot occur in the model (every
  version is a committed transaction's final write).  MAV (Def. 27): RC and OTV.
* Recency (§5.2.2; the paper gives no formal definition): a read returns a
  version at least as new as every write committed before it.  Real-time
  precedence is recorded in the input as happens-before, as in Appendix
  `app:rtc`.

## Specifications

For a phenomenon `Φ`, `gspec Φ` permits at `j` any answers that extend to a
complete history of `j` without `Φ` (as `HATSpec.spec`).  The *visibility
store* `vstore` permits an answer only if the version is the initial one or was
delivered to the reading replica before the read: a replica returns versions it
holds (Bailis §4: "a server that can handle an operation for a given data item
is called a replica for that item").  The guarantee's specification is their
intersection `tax Φ := Inter.inter vstore (gspec Φ)`, as the store held to an
isolation level in Theorem `thm:hat-levels`.  Every `gspec Φ` is total: the
serial history (each committed read returns the latest version below its
transaction's timestamp) has no cycle of session, write-, read- or
anti-dependency edges (`serial2_clean`).

## Availability notions

* `HighlyAvailable sp D`: some explicit relation `E ⊆ S` that answers every
  read access, and some system with Availability for `E` and Partition
  Consistency (Bailis §4: "every user that can contact a correct server
  eventually receives a response").  By Complete CAP for an explicit relation
  (`CAP.complete_cap_for`) this is: some `E ⊆ S` that answers every read and is
  consistent (Lifted Monotonicity for `E`) (`highlyAvailable_iff`).
* `StickyAvailable sp D`: the same with `E` answering every *sticky* access:
  one whose replica has received every write of the client's earlier committed
  transactions to the items it replicates (Bailis §4.1: a response is required
  "whenever a client's transactions is executed against a copy of database
  state that reflects all of the client's prior operations").
-/

namespace CC
namespace HATTax
open HATRC (Ts tsLt tsInit tsLt_trans tsLt_irrefl no_cycle)
open IConf (Hist St)
open HATSpec (Ev Inp WF Lamport Ver Inst Next CTs wwI lab_ev lab_sub lab_sup lt_sub lt_sup
  wf_down lamport_down exists_max allTs mem_allTs max_unique tsLt_total not_lt_init init_lt
  cts_unique cts_ne next_lt)

/-! ## Inputs -/

/-- `e` is a read (item or predicate) of transaction `(c,n)`. -/
def IsRead (h : Hist Ev) (e c n : Nat) : Prop :=
  (∃ k r, h.lab e = some (.rd c n k r)) ∨ (∃ ks r, h.lab e = some (.prd c n ks r))

/-- `(e, k)` is a read access of transaction `(c,n)` at replica `r`. -/
def Acc (h : Hist Ev) (e c n k r : Nat) : Prop :=
  h.lab e = some (.rd c n k r) ∨ ∃ ks, h.lab e = some (.prd c n ks r) ∧ k ∈ ks

theorem Acc.isRead {h : Hist Ev} {e c n k r : Nat} (ha : Acc h e c n k r) : IsRead h e c n := by
  rcases ha with h1 | ⟨ks, h1, -⟩
  · exact Or.inl ⟨k, r, h1⟩
  · exact Or.inr ⟨ks, r, h1⟩

/-- The extra legality conditions of the taxonomy (see the module docstring). -/
structure Sess (reps : Nat → List Nat) (h : Hist Ev) : Prop where
  rd_rep : ∀ {e c n k r}, h.lab e = some (.rd c n k r) → r ∈ reps k
  prd_rep : ∀ {e c n ks r k}, h.lab e = some (.prd c n ks r) → k ∈ ks → r ∈ reps k
  prd_before : ∀ {e f c n ks r t ks'}, h.lab e = some (.prd c n ks r) →
    h.lab f = some (.cm c n t ks') → h.lt e f
  txn_order : ∀ {e e' c n}, IsRead h e c n → IsRead h e' c n → e ≠ e' → h.lt e e' ∨ h.lt e' e
  seq : ∀ {f f' e c n n' t t' ks ks'}, h.lab f = some (.cm c n t ks) →
    h.lab f' = some (.cm c n' t' ks') → h.lt f f' → IsRead h e c n' → h.lt f e
  sess_ts : ∀ {f f' c n n' t t' ks ks'}, h.lab f = some (.cm c n t ks) →
    h.lab f' = some (.cm c n' t' ks') → h.lt f f' → tsLt t t'

variable {reps : Nat → List Nat} {lam : Bool}

/-- Inputs of the taxonomy. -/
abbrev SInp (reps : Nat → List Nat) (lam : Bool) :=
  {h : Hist Ev // (WF h ∧ (lam = true → Lamport h)) ∧ Sess reps h}

/-- The underlying `HATSpec` input. -/
def SInp.inp (j : SInp reps lam) : Inp lam := ⟨j.1, j.2.1⟩

instance : PO (SInp reps lam) where
  le a b := a.1 ≼ b.1
  refl a := PO.refl a.1
  trans h₁ h₂ := PO.trans h₁ h₂
  antisymm h₁ h₂ := Subtype.ext (PO.antisymm h₁ h₂)

theorem isRead_sub {a b : Hist Ev} (hab : a ≼ b) {e c n : Nat} (h : IsRead a e c n) :
    IsRead b e c n := by
  rcases h with ⟨k, r, h⟩ | ⟨ks, r, h⟩
  · exact Or.inl ⟨k, r, lab_sub hab h⟩
  · exact Or.inr ⟨ks, r, lab_sub hab h⟩

theorem isRead_ev {a : Hist Ev} {e c n : Nat} (h : IsRead a e c n) : a.ev e := by
  rcases h with ⟨k, r, h⟩ | ⟨ks, r, h⟩ <;> exact lab_ev h

theorem isRead_sup {a b : Hist Ev} (hab : a ≼ b) {e c n : Nat} (he : a.ev e)
    (h : IsRead b e c n) : IsRead a e c n := by
  rcases h with ⟨k, r, h⟩ | ⟨ks, r, h⟩
  · exact Or.inl ⟨k, r, lab_sup hab he h⟩
  · exact Or.inr ⟨ks, r, lab_sup hab he h⟩

theorem acc_sub {a b : Hist Ev} (hab : a ≼ b) {e c n k r : Nat} (h : Acc a e c n k r) :
    Acc b e c n k r := by
  rcases h with h | ⟨ks, h, hk⟩
  · exact Or.inl (lab_sub hab h)
  · exact Or.inr ⟨ks, lab_sub hab h, hk⟩

theorem acc_sup {a b : Hist Ev} (hab : a ≼ b) {e c n k r : Nat} (he : a.ev e)
    (h : Acc b e c n k r) : Acc a e c n k r := by
  rcases h with h | ⟨ks, h, hk⟩
  · exact Or.inl (lab_sup hab he h)
  · exact Or.inr ⟨ks, lab_sup hab he h, hk⟩

theorem acc_ev {a : Hist Ev} {e c n k r : Nat} (h : Acc a e c n k r) : a.ev e := by
  rcases h with h | ⟨ks, h, -⟩ <;> exact lab_ev h

theorem sess_down {a b : Hist Ev} (hab : a ≼ b) (hb : Sess reps b) : Sess reps a where
  rd_rep h := hb.rd_rep (lab_sub hab h)
  prd_rep h hk := hb.prd_rep (lab_sub hab h) hk
  prd_before h h' := lt_sup hab (hb.prd_before (lab_sub hab h) (lab_sub hab h')) (lab_ev h')
  txn_order h h' hne := by
    rcases hb.txn_order (isRead_sub hab h) (isRead_sub hab h') hne with hl | hl
    · exact Or.inl (lt_sup hab hl (isRead_ev h'))
    · exact Or.inr (lt_sup hab hl (isRead_ev h))
  seq hf hf' hl he := lt_sup hab (hb.seq (lab_sub hab hf) (lab_sub hab hf') (lt_sub hab hl)
    (isRead_sub hab he)) (isRead_ev he)
  sess_ts hf hf' hl := hb.sess_ts (lab_sub hab hf) (lab_sub hab hf') (lt_sub hab hl)

/-- Inputs are closed downward. -/
def SInp.down (j : SInp reps lam) (h : Hist Ev) (hle : h ≼ j.1) : SInp reps lam :=
  ⟨h, ⟨wf_down hle j.2.1.1, fun hl => lamport_down hle (j.2.1.2 hl)⟩, sess_down hle j.2.2⟩

/-! ## Outputs and complete histories -/

/-- `rv e k v`: the read access `(e, k)` returned the version with timestamp `v`. -/
inductive Fact2 where
  | rv (e k : Nat) (v : Ts)

/-- `(e, k)` is a read access of some transaction. -/
def IsAcc (j : SInp reps lam) (e k : Nat) : Prop := ∃ c n r, Acc j.1 e c n k r

/-- A complete history: every read access returns a version its transaction may
read. -/
structure CH2 (j : SInp reps lam) where
  val : Nat → Nat → Ts
  ok : ∀ e c n k r, Acc j.1 e c n k r → Ver j.inp c n k (val e k)

def CH2.facts {j : SInp reps lam} (H : CH2 j) : St Fact2
  | .rv e k v => IsAcc j e k ∧ H.val e k = v

/-! ## The direct serialization graph -/

section DSG
variable {j : SInp reps lam} (H : CH2 j)

/-- Item-read-dependency by `x` (Def. 4): committed `b` read `a`'s version of `x`. -/
def wr2 (x : Nat) (a b : Ts) : Prop :=
  a ≠ b ∧ Inst j.inp x a ∧ ∃ e c n r, j.1.lab e = some (.rd c n x r) ∧ CTs j.inp c n b ∧ H.val e x = a

/-- Item-anti-dependency by `x` (Def. 9): committed `a` read a version of `x`,
and `b` installs the next one. -/
def rw2 (x : Nat) (a b : Ts) : Prop :=
  a ≠ b ∧ ∃ e c n r, j.1.lab e = some (.rd c n x r) ∧ CTs j.inp c n a ∧ Next j.inp x (H.val e x) b

/-- Session-dependency (Def. 15): `a` and `b` are commits of the same client,
`a`'s before `b`'s. -/
def sess (a b : Ts) : Prop :=
  ∃ f f' c n n' ks ks', j.1.lab f = some (.cm c n a ks) ∧ j.1.lab f' = some (.cm c n' b ks') ∧
    j.1.lt f f'

def dep2 (a b : Ts) : Prop := (∃ k, wwI j.inp k a b) ∨ (∃ k, wr2 H k a b)

/-- G1c (Def. 20). -/
def G1c : Prop := ∃ t, Relation.TransGen (dep2 H) t t

/-- IMP (Def. 22). -/
def IMP : Prop := ∃ x a b t, a ≠ b ∧ wr2 H x a t ∧ wr2 H x b t

/-- The transactions changing the matches of the range `ks` for the predicate
read `e`: installers of a first (inserted) version of an item of `ks` that `e`
saw present. -/
def Chg (e : Nat) (ks : List Nat) (u : Ts) : Prop :=
  ∃ x ∈ ks, Next j.inp x tsInit u ∧ H.val e x ≠ tsInit

/-- PMP (Def. 24, "for some"). -/
def PMP : Prop :=
  ∃ e₁ e₂ c n r₁ r₂ ks₁ ks₂ t, j.1.lab e₁ = some (.prd c n ks₁ r₁) ∧
    j.1.lab e₂ = some (.prd c n ks₂ r₂) ∧ CTs j.inp c n t ∧
    ¬ ∀ u, (Chg H e₁ (ks₁.filter (· ∈ ks₂)) u ↔ Chg H e₂ (ks₁.filter (· ∈ ks₂)) u)

/-- An anti-dependency by `x` from read `e`, followed by write-dependencies by `x`, ending
at `t`: `e` read a version of `x` older than one `t` installs. -/
def RwWw (x e : Nat) (t : Ts) : Prop :=
  ∃ u, Next j.inp x (H.val e x) u ∧ (u = t ∨ Relation.TransGen (wwI j.inp x) u t)

/-- OTV (Def. 26). -/
def OTV : Prop :=
  ∃ e₁ e₂ c n r₁ r₂ x y ti tj, j.1.lab e₁ = some (.rd c n x r₁) ∧
    j.1.lab e₂ = some (.rd c n y r₂) ∧ CTs j.inp c n ti ∧ j.1.lt e₁ e₂ ∧
    H.val e₁ x = tj ∧ wr2 H x tj ti ∧ RwWw H y e₂ tj

/-- N-MR (Def. 28). -/
def NMR : Prop :=
  ∃ ti tj tl x e c n r, Relation.TransGen (sess (j := j)) ti tj ∧
    j.1.lab e = some (.rd c n x r) ∧ CTs j.inp c n tj ∧ RwWw H x e tl ∧ wr2 H x tl ti

/-- N-MW (Def. 30) as written: a session order contradicted by the version order. -/
def NMWlit : Prop :=
  ∃ ti tj, Relation.TransGen (sess (j := j)) ti tj ∧
    Relation.TransGen (fun a b => ∃ k, wwI j.inp k a b) tj ti

/-- N-MW: Def. 30, or its example (Fig. 13/14). -/
def NMW : Prop :=
  NMWlit (j := j) ∨
  ∃ ti tj tk x y e c n r, Relation.TransGen (sess (j := j)) ti tj ∧ wr2 H y tj tk ∧
    j.1.lab e = some (.rd c n x r) ∧ CTs j.inp c n tk ∧ tk ≠ ti ∧ RwWw H x e ti

/-- MRWD (Defs. 32/33, repaired). -/
def MRWD : Prop :=
  ∃ t₁ t₂ t₃ x y e c n r, wr2 H x t₁ t₂ ∧ wr2 H y t₂ t₃ ∧
    j.1.lab e = some (.rd c n x r) ∧ CTs j.inp c n t₃ ∧ t₃ ≠ t₁ ∧ Next j.inp x (H.val e x) t₁

/-- MYR (Def. 34), single-item form. -/
def MYR : Prop :=
  ∃ ti tj x e c n r, Relation.TransGen (sess (j := j)) ti tj ∧
    j.1.lab e = some (.rd c n x r) ∧ CTs j.inp c n tj ∧ tj ≠ ti ∧ RwWw H x e ti

/-- Anti- or write-dependency. -/
def rwww (a b : Ts) : Prop := (∃ k, rw2 H k a b) ∨ (∃ k, wwI j.inp k a b)

/-- MYR (Def. 34) as written. -/
def MYRlit : Prop :=
  ∃ ti tj a b, Relation.TransGen (sess (j := j)) ti tj ∧
    (tj = a ∨ Relation.TransGen (rwww H) tj a) ∧ (∃ k, rw2 H k a b) ∧
    (b = ti ∨ Relation.TransGen (rwww H) b ti)

/-- Recency: a read returns a version older than a write committed before it. -/
def Recency : Prop :=
  ∃ e c n x r f c' n' t ks, j.1.lab e = some (.rd c n x r) ∧ j.1.lab f = some (.cm c' n' t ks) ∧
    x ∈ ks ∧ (c', n') ≠ (c, n) ∧ j.1.lt f e ∧ tsLt (H.val e x) t

end DSG

/-- The guarantees, by proscribed phenomena. -/
inductive Guar where
  | RC | MAV | ICI | PCI | MR | MW | WFR | RYW | PRAM | Causal | RYWlit | Rec
  deriving DecidableEq

def Phen : Guar → (j : SInp reps lam) → CH2 j → Prop
  | .RC, j, H => HATSpec.G0 j.inp ∨ G1c H
  | .MAV, j, H => HATSpec.G0 j.inp ∨ G1c H ∨ OTV H
  | .ICI, _, H => IMP H
  | .PCI, _, H => PMP H
  | .MR, _, H => NMR H
  | .MW, _, H => NMW H
  | .WFR, _, H => MRWD H
  | .RYW, _, H => MYR H
  | .PRAM, _, H => NMR H ∨ NMW H ∨ MYR H
  | .Causal, _, H => NMR H ∨ NMW H ∨ MYR H ∨ MRWD H
  | .RYWlit, _, H => MYRlit H
  | .Rec, _, H => Recency H

/-! ## Visibility -/

/-- Version `v` of `x` was delivered to replica `r` before event `e` (or is the
initial version). -/
def Vis (h : Hist Ev) (e x r : Nat) (v : Ts) : Prop :=
  v = tsInit ∨ ∃ d c' n' f ks, h.lab d = some (.dl c' n' x r) ∧ h.lt d e ∧
    h.lab f = some (.cm c' n' v ks)

/-- The visibility store: answers only with versions the reading replica holds. -/
def vstore : Spec (SInp reps lam) (St Fact2) where
  P j F := ∀ e k v, F (.rv e k v) → ∃ c n r, Acc j.1 e c n k r ∧ Vis j.1 e k r v
  total _ := ⟨fun _ => False, fun _ _ _ h => h.elim⟩

/-! ## Basic lemmas -/

section Basic
variable {j : SInp reps lam}

theorem acc_unique {e c n k r c' n' k' r' : Nat} (h : Acc j.1 e c n k r) (h' : Acc j.1 e c' n' k' r') :
    c = c' ∧ n = n' ∧ r = r' := by
  rcases h with h | ⟨ks, h, -⟩ <;> rcases h' with h' | ⟨ks', h', -⟩ <;> rw [h] at h' <;>
    cases h' <;> exact ⟨rfl, rfl, rfl⟩

theorem isRead_unique {e c n c' n' : Nat} (h : IsRead j.1 e c n) (h' : IsRead j.1 e c' n') :
    c = c' ∧ n = n' := by
  rcases h with ⟨k, r, h⟩ | ⟨ks, r, h⟩ <;> rcases h' with ⟨k', r', h'⟩ | ⟨ks', r', h'⟩ <;>
    rw [h] at h' <;> cases h' <;> exact ⟨rfl, rfl⟩

/-- A read precedes its transaction's commit. -/
theorem read_before {e f c n : Nat} {ts : Ts} {ks : List Nat} (h : IsRead j.1 e c n)
    (hf : j.1.lab f = some (.cm c n ts ks)) : j.1.lt e f := by
  rcases h with ⟨k, r, h⟩ | ⟨ks', r, h⟩
  · exact j.2.1.1.rd_before h hf
  · exact j.2.2.prd_before h hf

theorem ts_inj {f f' c n c' n' : Nat} {t : Ts} {ks ks' : List Nat}
    (hf : j.1.lab f = some (.cm c n t ks)) (hf' : j.1.lab f' = some (.cm c' n' t ks')) :
    f = f' ∧ c = c' ∧ n = n' ∧ ks = ks' := by
  have := j.2.1.1.ts_unique hf hf'; subst this
  rw [hf] at hf'; cases hf'; exact ⟨rfl, rfl, rfl, rfl⟩

/-- `v` is the largest element of `P`. -/
def IsMax (P : Ts → Prop) (v : Ts) : Prop := P v ∧ ∀ w, P w → w = v ∨ tsLt w v

theorem isMax_unique {P : Ts → Prop} {v w : Ts} (hv : IsMax P v) (hw : IsMax P w) : v = w :=
  max_unique hv hw

theorem isMax_exists (P : Ts → Prop) (h0 : P tsInit)
    (hfin : ∀ v, P v → v = tsInit ∨ ∃ f c n ks, j.1.lab f = some (.cm c n v ks)) :
    ∃ v, IsMax P v := by
  refine exists_max (allTs j.1) P ⟨_, h0⟩ fun v hv => ?_
  rcases hfin v hv with rfl | ⟨f, c, n, ks, hf⟩
  · exact List.mem_cons_self ..
  · exact mem_allTs hf

theorem isMax_le {P Q : Ts → Prop} {v w : Ts} (hv : IsMax P v) (hw : IsMax Q w)
    (h : ∀ u, P u → Q u) : v = w ∨ tsLt v w := hw.2 v (h v hv.1)

theorem le_trans' {a b c : Ts} (h₁ : a = b ∨ tsLt a b) (h₂ : b = c ∨ tsLt b c) : a = c ∨ tsLt a c := by
  rcases h₁ with rfl | h₁ <;> rcases h₂ with rfl | h₂
  · exact Or.inl rfl
  · exact Or.inr h₂
  · exact Or.inr h₁
  · exact Or.inr (tsLt_trans h₁ h₂)

theorem not_le_lt {a b : Ts} (h₁ : a = b ∨ tsLt a b) (h₂ : tsLt b a) : False := by
  rcases h₁ with rfl | h₁
  · exact tsLt_irrefl _ h₂
  · exact tsLt_irrefl _ (tsLt_trans h₁ h₂)

theorem lt_le_trans {a b c : Ts} (h₁ : tsLt a b) (h₂ : b = c ∨ tsLt b c) : tsLt a c := by
  rcases h₂ with rfl | h₂
  · exact h₁
  · exact tsLt_trans h₁ h₂

theorem tg_lt' {R : Ts → Ts → Prop} (hR : ∀ a b, R a b → tsLt a b) {a b : Ts}
    (h : Relation.TransGen R a b) : tsLt a b := by
  induction h with
  | single h => exact hR _ _ h
  | tail _ h ih => exact tsLt_trans ih (hR _ _ h)

theorem inst_commit {x : Nat} {t : Ts} (h : Inst j.inp x t) (ht : t ≠ tsInit) :
    ∃ f c n ks, j.1.lab f = some (.cm c n t ks) ∧ x ∈ ks :=
  h.resolve_left ht

/-- An anti-dependency followed by write-dependencies ends above the version read. -/
theorem rwWw_lt {H : CH2 j} {x e : Nat} {t : Ts} (h : RwWw H x e t) :
    tsLt (H.val e x) t ∧ Inst j.inp x t := by
  obtain ⟨u, hn, rfl | hc⟩ := h
  · exact ⟨next_lt hn, hn.2.1⟩
  · refine ⟨tsLt_trans (next_lt hn) (tg_lt' (fun _ _ h => next_lt h) hc), ?_⟩
    cases hc with
    | single h => exact h.2.1
    | tail _ h => exact h.2.1

theorem sess_lt {a b : Ts} (h : sess (j := j) a b) : tsLt a b := by
  obtain ⟨f, f', c, n, n', ks, ks', hf, hf', hl⟩ := h
  exact j.2.2.sess_ts hf hf' hl

theorem sess_tg_lt {a b : Ts} (h : Relation.TransGen (sess (j := j)) a b) : tsLt a b :=
  tg_lt' (fun _ _ h => sess_lt h) h

/-- A chain of session edges joins two commits of one client, in order. -/
theorem sess_tg {a b : Ts} (h : Relation.TransGen (sess (j := j)) a b) :
    ∃ f f' c n n' ks ks', j.1.lab f = some (.cm c n a ks) ∧ j.1.lab f' = some (.cm c n' b ks') ∧
      j.1.lt f f' := by
  induction h with
  | single h => exact h
  | tail _ h ih =>
    obtain ⟨f, f', c, n, n', ks, ks', hf, hf', hl⟩ := ih
    obtain ⟨g, g', d, m, m', ls, ls', hg, hg', hl'⟩ := h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hf' hg
    exact ⟨f, g', c, n, m', ks, ls', hf, hg', j.1.lt_trans hl hl'⟩

end Basic

/-! ## The serial history, and totality -/

section Serial
variable (j : SInp reps lam)

/-- Candidates in the serial history: the initial version, or a version of `k`
below the reader's commit timestamp. -/
def SerC (c n k : Nat) (v : Ts) : Prop :=
  v = tsInit ∨ ((∃ f c' n' ks, j.1.lab f = some (.cm c' n' v ks) ∧ k ∈ ks) ∧
    ∃ t, CTs j.inp c n t ∧ tsLt v t)

def SerAns (e k : Nat) (v : Ts) : Prop := ∃ c n r, Acc j.1 e c n k r ∧ IsMax (SerC j c n k) v

theorem serC_max (c n k : Nat) : ∃ v, IsMax (SerC j c n k) v :=
  isMax_exists _ (Or.inl rfl) fun v hv => by
    rcases hv with rfl | ⟨⟨f, c', n', ks, hf, -⟩, -⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨f, c', n', ks, hf⟩

noncomputable def serial2 : CH2 j where
  val e k := @dite _ (∃ v, SerAns j e k v) (Classical.propDecidable _) (fun h => Classical.choose h)
    (fun _ => tsInit)
  ok e c n k r ha := by
    have hx : ∃ v, SerAns j e k v := by
      obtain ⟨v, hv⟩ := serC_max j c n k; exact ⟨v, c, n, r, ha, hv⟩
    simp only [dif_pos hx]
    obtain ⟨c₁, n₁, r₁, ha₁, ⟨hv, -⟩⟩ := Classical.choose_spec hx
    obtain ⟨rfl, rfl, rfl⟩ := acc_unique ha₁ ha
    rcases hv with hv | ⟨⟨f, c', n', ks, hf, hk⟩, t, ht, hlt⟩
    · exact Or.inl hv
    · refine Or.inr ⟨f, c', n', ks, hf, hk, fun e' => ?_⟩
      simp only [Prod.mk.injEq] at e'; obtain ⟨rfl, rfl⟩ := e'
      rw [cts_unique ⟨f, ks, hf⟩ ht] at hlt; exact tsLt_irrefl _ hlt

theorem serial2_val {e c n k r : Nat} (ha : Acc j.1 e c n k r) :
    IsMax (SerC j c n k) ((serial2 j).val e k) := by
  have hx : ∃ v, SerAns j e k v := by
    obtain ⟨v, hv⟩ := serC_max j c n k; exact ⟨v, c, n, r, ha, hv⟩
  show IsMax _ (@dite _ _ (Classical.propDecidable _) _ _)
  rw [dif_pos hx]
  obtain ⟨c₁, n₁, r₁, ha₁, hv⟩ := Classical.choose_spec hx
  obtain ⟨rfl, rfl, rfl⟩ := acc_unique ha₁ ha
  exact hv

variable {j}

/-- A committed transaction's serial answer is below its timestamp, and above every
version below its timestamp. -/
theorem serial2_below {e c n x r : Nat} {t : Ts} (he : j.1.lab e = some (.rd c n x r))
    (ht : CTs j.inp c n t) : tsLt ((serial2 j).val e x) t := by
  rcases (serial2_val j (Or.inl he)).1 with hv | ⟨-, t', ht', hlt⟩
  · rw [hv]; exact init_lt (cts_ne ht)
  · rwa [cts_unique ht ht'] 

theorem serial2_above {e c n x r : Nat} {t v : Ts} (he : j.1.lab e = some (.rd c n x r))
    (ht : CTs j.inp c n t) (hv : Inst j.inp x v) (hlt : tsLt v t) :
    (v = (serial2 j).val e x ∨ tsLt v ((serial2 j).val e x)) := by
  apply (serial2_val j (Or.inl he)).2
  rcases hv with hv | hv
  · exact Or.inl hv
  · exact Or.inr ⟨hv, t, ht, hlt⟩

theorem serial2_wr {x : Nat} {a b : Ts} (h : wr2 (serial2 j) x a b) : tsLt a b := by
  obtain ⟨-, -, e, c, n, r, he, hb, rfl⟩ := h
  exact serial2_below he hb

theorem serial2_rw {x : Nat} {a b : Ts} (h : rw2 (serial2 j) x a b) : tsLt a b := by
  obtain ⟨hab, e, c, n, r, he, ha, hn⟩ := h
  rcases tsLt_total hab with h | h
  · exact h
  · exfalso
    exact not_le_lt (serial2_above he ha hn.2.1 h) (next_lt hn)

theorem serial2_rwWw {x e c n r : Nat} {t t' : Ts} (he : j.1.lab e = some (.rd c n x r))
    (ht : CTs j.inp c n t) (h : RwWw (serial2 j) x e t') : t = t' ∨ tsLt t t' := by
  obtain ⟨hlt, hi⟩ := rwWw_lt h
  by_cases h' : t = t'
  · exact Or.inl h'
  · rcases tsLt_total h' with h1 | h1
    · exact Or.inr h1
    · exact absurd (serial2_above he ht hi h1) (fun h2 => not_le_lt h2 hlt)

/-- The serial history exhibits none of the DSG phenomena. -/
theorem serial2_clean (g : Guar) (hg : g ≠ .Rec) : ¬ Phen g j (serial2 j) := by
  have hdep : ∀ a b, dep2 (serial2 j) a b → tsLt a b := fun a b h =>
    h.elim (fun ⟨_, h⟩ => next_lt h) (fun ⟨_, h⟩ => serial2_wr h)
  have n0 : ¬ HATSpec.G0 j.inp := fun ⟨t, h⟩ => no_cycle (fun _ _ ⟨_, h⟩ => next_lt h) h
  have n1 : ¬ G1c (serial2 j) := fun ⟨t, h⟩ => no_cycle hdep h
  have nOTV : ¬ OTV (serial2 j) := by
    rintro ⟨e₁, e₂, c, n, r₁, r₂, x, y, ti, tj, he₁, he₂, hti, -, -, hwr, hrw⟩
    exact not_le_lt (serial2_rwWw he₂ hti hrw) (serial2_wr hwr)
  have nIMP : ¬ IMP (serial2 j) := by
    rintro ⟨x, a, b, t, hab, ⟨-, -, e, c, n, r, he, ht, rfl⟩, ⟨-, -, e', c', n', r', he', ht', rfl⟩⟩
    obtain ⟨f, ks, hf⟩ := ht; obtain ⟨f', ks', hf'⟩ := ht'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hf hf'
    exact hab (isMax_unique (serial2_val j (Or.inl he)) (serial2_val j (Or.inl he')))
  have nPMP : ¬ PMP (serial2 j) := by
    rintro ⟨e₁, e₂, c, n, r₁, r₂, ks₁, ks₂, t, he₁, he₂, -, hne⟩
    apply hne; intro u
    have hv : ∀ x ∈ ks₁.filter (· ∈ ks₂), (serial2 j).val e₁ x = (serial2 j).val e₂ x := by
      intro x hx
      simp only [List.mem_filter, decide_eq_true_eq] at hx
      exact isMax_unique (serial2_val j (Or.inr ⟨ks₁, he₁, hx.1⟩))
        (serial2_val j (Or.inr ⟨ks₂, he₂, hx.2⟩))
    constructor
    · rintro ⟨x, hx, hn, hv'⟩; exact ⟨x, hx, hn, by rw [← hv x hx]; exact hv'⟩
    · rintro ⟨x, hx, hn, hv'⟩; exact ⟨x, hx, hn, by rw [hv x hx]; exact hv'⟩
  have nMR : ¬ NMR (serial2 j) := by
    rintro ⟨ti, tj, tl, x, e, c, n, r, hs, he, htj, hrw, hwr⟩
    exact not_le_lt (serial2_rwWw he htj hrw) (tsLt_trans (serial2_wr hwr) (sess_tg_lt hs))
  have nMW : ¬ NMW (serial2 j) := by
    rintro (⟨ti, tj, hs, hw⟩ | ⟨ti, tj, tk, x, y, e, c, n, r, hs, hwr, he, htk, -, hrw⟩)
    · exact tsLt_irrefl _ (tsLt_trans (sess_tg_lt hs) (tg_lt' (fun _ _ ⟨_, h⟩ => next_lt h) hw))
    · exact not_le_lt (serial2_rwWw he htk hrw) (tsLt_trans (sess_tg_lt hs) (serial2_wr hwr))
  have nWFR : ¬ MRWD (serial2 j) := by
    rintro ⟨t₁, t₂, t₃, x, y, e, c, n, r, hw1, hw2, he, ht3, -, hn⟩
    exact not_le_lt (serial2_rwWw he ht3 ⟨t₁, hn, Or.inl rfl⟩)
      (tsLt_trans (serial2_wr hw1) (serial2_wr hw2))
  have nRYW : ¬ MYR (serial2 j) := by
    rintro ⟨ti, tj, x, e, c, n, r, hs, he, htj, -, hrw⟩
    exact not_le_lt (serial2_rwWw he htj hrw) (sess_tg_lt hs)
  have nRYWlit : ¬ MYRlit (serial2 j) := by
    have hR : ∀ a b, rwww (serial2 j) a b → tsLt a b := fun a b h =>
      h.elim (fun ⟨_, h⟩ => serial2_rw h) (fun ⟨_, h⟩ => next_lt h)
    have hle : ∀ {a b}, (a = b ∨ Relation.TransGen (rwww (serial2 j)) a b) → (a = b ∨ tsLt a b) :=
      fun h => h.imp id (tg_lt' hR)
    rintro ⟨ti, tj, a, b, hs, h1, ⟨k, hab⟩, h2⟩
    exact tsLt_irrefl _ (lt_le_trans (tsLt_trans (lt_le_trans (sess_tg_lt hs) (hle h1))
      (serial2_rw hab)) (hle h2))
  cases g with
  | RC => exact fun h => h.elim n0 n1
  | MAV => exact fun h => h.elim n0 fun h => h.elim n1 nOTV
  | ICI => exact nIMP
  | PCI => exact nPMP
  | MR => exact nMR
  | MW => exact nMW
  | WFR => exact nWFR
  | RYW => exact nRYW
  | PRAM => exact fun h => h.elim nMR fun h => h.elim nMW nRYW
  | Causal => exact fun h => h.elim nMR fun h => h.elim nMW fun h => h.elim nRYW nWFR
  | RYWlit => exact nRYWlit
  | Rec => exact absurd rfl hg

end Serial

/-! ## The recency witness -/

section RecW
variable (j : SInp reps lam)

/-- Candidates: the initial version, or a version of `k` committed before the read. -/
def RecC (e k : Nat) (v : Ts) : Prop :=
  v = tsInit ∨ ∃ f c' n' ks, j.1.lab f = some (.cm c' n' v ks) ∧ k ∈ ks ∧ j.1.lt f e

theorem recC_max (e k : Nat) : ∃ v, IsMax (RecC j e k) v :=
  isMax_exists _ (Or.inl rfl) fun v hv => by
    rcases hv with rfl | ⟨f, c', n', ks, hf, -⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨f, c', n', ks, hf⟩

noncomputable def recHist : CH2 j where
  val e k := Classical.choose (recC_max j e k)
  ok e c n k r ha := by
    rcases (Classical.choose_spec (recC_max j e k)).1 with hv | ⟨f, c', n', ks, hf, hk, hlt⟩
    · exact Or.inl hv
    · refine Or.inr ⟨f, c', n', ks, hf, hk, fun e' => ?_⟩
      simp only [Prod.mk.injEq] at e'; obtain ⟨rfl, rfl⟩ := e'
      have h2 := j.1.lt_num (read_before ha.isRead hf)
      have h1 := j.1.lt_num hlt
      omega

theorem recHist_clean : ¬ Recency (recHist j) := by
  rintro ⟨e, c, n, x, r, f, c', n', t, ks, he, hf, hx, -, hlt, hold⟩
  have := (Classical.choose_spec (recC_max j e x)).2 t (Or.inr ⟨f, c', n', ks, hf, hx, hlt⟩)
  exact not_le_lt this hold

end RecW

/-! ## The specifications -/

/-- The witness complete history of each guarantee. -/
noncomputable def wit : Guar → (j : SInp reps lam) → CH2 j
  | .Rec, j => recHist j
  | _, j => serial2 j

theorem wit_clean (g : Guar) (j : SInp reps lam) : ¬ Phen g j (wit g j) := by
  cases g <;> first
    | exact recHist_clean j
    | exact serial2_clean (j := j) _ (by decide)

/-- The guarantee as a specification on read answers: the answers extend to a
complete history of the input without the proscribed phenomenon. -/
def gspec (g : Guar) : Spec (SInp reps lam) (St Fact2) where
  P j F := ∃ H : CH2 j, F ≼ H.facts ∧ ¬ Phen g j H
  total j := ⟨fun _ => False, wit g j, fun _ h => h.elim, wit_clean g j⟩

theorem tax_total (g : Guar) :
    ∀ j : SInp reps lam, ∃ o, (vstore (reps := reps)).P j o ∧ (gspec g).P j o :=
  fun j => ⟨fun _ => False, fun _ _ _ h => h.elim, wit g j, fun _ h => h.elim, wit_clean g j⟩

/-- The store held to guarantee `g`: the intersection of the visibility store
with `gspec g` (Def. `def:intersection`). -/
def tax (g : Guar) : Spec (SInp reps lam) (St Fact2) :=
  Inter.inter vstore (gspec g) (tax_total g)

/-! ## Availability notions -/

/-- The output answers every read access. -/
def AnswersAll (j : SInp reps lam) (o : St Fact2) : Prop :=
  ∀ e c n k r, Acc j.1 e c n k r → ∃ v, o (.rv e k v)

/-- The access `(e, k)` of client `c` at replica `r` is *sticky*: replica `r`
has received every write of `c`'s earlier committed transactions to the items it
replicates. -/
def Reflects (h : Hist Ev) (e c r : Nat) : Prop :=
  ∀ f n' t ks k, h.lab f = some (.cm c n' t ks) → h.lt f e → k ∈ ks → r ∈ reps k →
    ∃ d, h.lab d = some (.dl c n' k r) ∧ h.lt d e

/-- The output answers every sticky read access. -/
def AnswersSticky (j : SInp reps lam) (o : St Fact2) : Prop :=
  ∀ e c n k r, Acc j.1 e c n k r → Reflects (reps := reps) j.1 e c r → ∃ v, o (.rv e k v)

/-- Highly available (Bailis §4): some explicit relation contained in `S` that
answers every read access, and a system with Availability for it and Partition
Consistency. -/
def HighlyAvailable (sp : Spec (SInp reps lam) (St Fact2)) (D : Type) : Prop :=
  ∃ E : Table (SInp reps lam) (St Fact2), (∀ i o, E i o → sp.P i o) ∧ (∀ i, ∃ o, E i o) ∧
    (∀ i o, E i o → AnswersAll i o) ∧
    ∃ Sys : CAP.System sp D, CAP.AvailabilityFor E Sys ∧ CAP.PartitionConsistencyAtEnd Sys

/-- Sticky available (Bailis §4.1): the same, answering every sticky read access. -/
def StickyAvailable (sp : Spec (SInp reps lam) (St Fact2)) (D : Type) : Prop :=
  ∃ E : Table (SInp reps lam) (St Fact2), (∀ i o, E i o → sp.P i o) ∧ (∀ i, ∃ o, E i o) ∧
    (∀ i o, E i o → AnswersSticky i o) ∧
    ∃ Sys : CAP.System sp D, CAP.AvailabilityFor E Sys ∧ CAP.PartitionConsistencyAtEnd Sys

/-- By Complete CAP for an explicit relation, high availability is: some
`E ⊆ S` answering every read that is consistent (Lifted Monotonicity for `E`). -/
theorem highlyAvailable_iff (sp : Spec (SInp reps lam) (St Fact2)) (D : Type) :
    HighlyAvailable sp D ↔
      ∃ E : Table (SInp reps lam) (St Fact2), (∀ i o, E i o → sp.P i o) ∧ (∀ i, ∃ o, E i o) ∧
        (∀ i o, E i o → AnswersAll i o) ∧ CAP.ConsistentOn sp E := by
  constructor
  · rintro ⟨E, hS, ht, ha, hsys⟩
    exact ⟨E, hS, ht, ha, (CAP.complete_cap_for sp D E hS).1 hsys⟩
  · rintro ⟨E, hS, ht, ha, hc⟩
    exact ⟨E, hS, ht, ha, (CAP.complete_cap_for sp D E hS).2 hc⟩

theorem stickyAvailable_iff (sp : Spec (SInp reps lam) (St Fact2)) (D : Type) :
    StickyAvailable sp D ↔
      ∃ E : Table (SInp reps lam) (St Fact2), (∀ i o, E i o → sp.P i o) ∧ (∀ i, ∃ o, E i o) ∧
        (∀ i o, E i o → AnswersSticky i o) ∧ CAP.ConsistentOn sp E := by
  constructor
  · rintro ⟨E, hS, ht, ha, hsys⟩
    exact ⟨E, hS, ht, ha, (CAP.complete_cap_for sp D E hS).1 hsys⟩
  · rintro ⟨E, hS, ht, ha, hc⟩
    exact ⟨E, hS, ht, ha, (CAP.complete_cap_for sp D E hS).2 hc⟩

end HATTax
end CC
