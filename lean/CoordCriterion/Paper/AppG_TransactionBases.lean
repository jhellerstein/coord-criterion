import CoordCriterion.Appendix.TransactionBases.MVTO

/-!
# Paper, Appendix G: Commitment bases for 2PL and MVTO (`app:cc-bases`)

Source: `appendices/commitment-bases.tex` (the whole appendix).

How to read this file: it follows the appendix paragraph by paragraph
(Specification, Commitments, 2PL, MVTO, Comparison).  The appendix has no
numbered results; every claim it states or argues gets a declaration named
`«app:cc-bases/<slug>»` in namespace `CC.Paper`.  Each docstring quotes the
claim; the statement is written out in full in terms of library definitions,
and the proof points to the library.

Library correspondence (`Appendix/TransactionBases/Spec.lean`, `Partial.lean`,
`MVTO.lean`, namespace `CC.Txn.Partial`):
* An input is `k : Inp T K`: a finite set `k.txs` of transactions, each with a
  sequence `k.tx t` of operations (`Acc.rd x`, `Acc.wr x`) and a flag for its
  commit request.  `k.mem t` (`t ∈ k`), `k.fin t` (`t` has requested commit),
  `k.op t n` (its `n`-th operation, from `0`), `k.writes t x`.
* The specification is `spec false` (abort-free variant: `spec true`).  An
  output is `r : ROut T K`, with `r.o : Outcome T` the pair `(L,X)` (`r.o.X`
  the abort set, `r.o.dom` = `dom L`, `r.o.lt` = `<_L`) and `r.ρ a n = some v`
  the reported result of the `n`-th operation of `a` (`v = none`: the initial
  version; `v = some W`: the write by `W`).
* "Complete at `k`" is `Decides false k r.o` (`Decides true` for the abort-free
  variant); a permitted complete output is `Complete false k r`.
* The commitments are *closure commitments* `closeC G Q`: the guard `G` is the
  appendix's "for `A ∈ i`" etc., the condition `Q` is on complete outputs, and
  a row is kept when a remaining complete row refines it and satisfies `Q`
  (`Keep`).
* Protocol steps are modeled by the runs that the claims are about: the MVTO
  run of `«app:cc-bases/abort-is-a-choice»` is driven by input events, one per
  arriving operation.  What a scheduler does on an arrival (request a lock,
  issue a timestamp, apply the write rule) is otherwise prose.
-/

namespace CC
namespace Paper

open CC.Txn CC.Txn.Partial

/-! ## Specification -/

/-- "An input is a finite set of transactions, each given by the sequence of
operations that its client has issued so far: reads and writes of keys,
possibly followed by a request to commit." -/
abbrev «app:cc-bases/input» (T K : Type) := Inp T K

/-- "One input precedes another when every transaction of the first is in the
second and its sequence in the first is a prefix of its sequence in the second;
once a transaction has requested commit, its sequence no longer grows." -/
theorem «app:cc-bases/input-order» {T K : Type} (a b : Inp T K) :
    a ≼ b ↔ (∀ t, a.mem t → b.mem t) ∧
      ∀ t, (∃ l, (b.tx t).ops = (a.tx t).ops ++ l) ∧ ((a.tx t).req = true → b.tx t = a.tx t) :=
  Iff.rfl

/-- "An output has three parts: the committed transactions, in a serial order;
the aborted transactions; and the read results reported so far.  A read result
says which version the `k`-th operation of a transaction, a read of a key `x`,
returned …"  Written `(L,X,ρ)`. -/
abbrev «app:cc-bases/output» (T K : Type) := Partial.ROut T K

/-- "One output refines another when it extends all three parts …"
`(L,X,ρ) ⪯ (L',X',ρ') ⟺ X ⊆ X', dom L ⊆ dom L', L'|_{dom L} = L, ρ ⊆ ρ'`. -/
theorem «app:cc-bases/output-order» {T K : Type} (r r' : Partial.ROut T K) :
    r ≼ r' ↔
      (∀ t, r.o.X t → r'.o.X t) ∧ (∀ t, r.o.dom t → r'.o.dom t) ∧
      (∀ a b, r.o.dom a → r.o.dom b → (r'.o.lt a b ↔ r.o.lt a b)) ∧
      (∀ a n v, r.ρ a n = some v → r'.ρ a n = some v) :=
  ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩⟩

/-- "An output is *complete* at an input when it commits or aborts every
transaction of the input, and not both, and commits only transactions whose
commit request is in the input." -/
theorem «app:cc-bases/complete-output» {T K : Type} (k : Inp T K) (o : Outcome T) :
    Decides false k o ↔
      (∀ t, (k.mem t ↔ o.X t ∨ o.dom t) ∧ ¬ (o.X t ∧ o.dom t)) ∧ ∀ t, o.dom t → k.fin t :=
  Iff.rfl

/-- "… each read of a key `x` by a committed transaction `T` returns `T`'s own
write of `x` if `T` writes `x` earlier in its sequence, and otherwise the write
of `x` by the last transaction before `T` in the serial order that writes `x`,
or the initial version if none does." -/
theorem «app:cc-bases/read-rule» {T K : Type} (k : Inp T K) (o : Outcome T) (a : T) (n : Nat)
    (x : K) (v : Option T) :
    ReadOK k o a n x v ↔
      ((∃ m, m < n ∧ k.op a m = some (.wr x)) → v = some a) ∧
      (¬ (∃ m, m < n ∧ k.op a m = some (.wr x)) →
        match v with
        | none => ∀ w, o.lt w a → ¬ k.writes w x
        | some W => o.lt W a ∧ k.writes W x ∧ ∀ w', o.lt W w' → o.lt w' a → ¬ k.writes w' x) := by
  cases v <;> exact Iff.rfl

/-- "A complete output is permitted when each reported read result is for a
read in the input and returns the initial version or the write of its key by a
transaction of the input, and each read of a key `x` by a committed transaction
`T` returns `T`'s own write of `x` if `T` writes `x` earlier in its sequence,
and otherwise the write of `x` by the last transaction before `T` in the serial
order that writes `x`, or the initial version if none does.  Reads by aborted
transactions are otherwise unconstrained."  (The read rule is
`«app:cc-bases/read-rule»`.) -/
theorem «app:cc-bases/complete» {T K : Type} (k : Inp T K) (r : Partial.ROut T K) :
    Complete false k r ↔
      Decides false k r.o ∧
      ∀ a n v, r.ρ a n = some v →
        ∃ x, k.op a n = some (.rd x) ∧ Valid k x v ∧ (r.o.dom a → ReadOK k r.o a n x v) :=
  Iff.rfl

/-- "Any output is permitted when some permitted complete output refines it,
that is, when it can still be completed." -/
theorem «app:cc-bases/permitted» {T K : Type} (k : Inp T K) (u : Partial.ROut T K) :
    (spec false).S k u ↔ ∃ c, Complete false k c ∧ u ≼ c :=
  Iff.rfl

/-- The specification. -/
abbrev «app:cc-bases/spec» (T K : Type) := spec (T := T) (K := K) false

/-- "The figures … show only complete outputs without aborts or read results,
as serial orders, at inputs in which every transaction has requested commit":
at such an input, a serial order of its transactions, with nothing aborted and
no reads, is a row of both specifications. -/
theorem «app:cc-bases/figure-rows» {T K : Type} (af : Bool) (k : Inp T K)
    (hf : ∀ t, k.mem t → k.fin t) (o : Outcome T) (hp : Partitions k.txs o)
    (hX : ∀ t, ¬ o.X t) :
    (spec (T := T) (K := K) af).S k (full o) :=
  ⟨full o, full_complete (decides_of_all_fin hf hp hX), PO.refl _⟩

/-- "Every input has a permitted row: the one that aborts every transaction and
reports nothing." -/
theorem «app:cc-bases/total» {T K : Type} (k : Inp T K) :
    (spec (T := T) (K := K) false).S k (full (allAbort k.txs)) :=
  ⟨_, full_complete (allAbort_decides k), PO.refl _⟩

/-- "Let `{A,B}` be an input in which `A` and `B` have each requested commit.
The rows `({A,B},([A,B],∅,∅))` and `({A,B},([B,A],∅,∅))` of Figure
ambiguity-frames(f) have no common refinement, which would order `A` both before
and after `B`, so the specification is not monotone."  Not monotone: no
Directed Outputs, no Lifted Monotonicity.  (Such an input exists for any two
transactions: `pairDone`.) -/
theorem «app:cc-bases/ab-ba-not-monotone» {T K : Type} {A B : T} (h : A ≠ B) {k : Inp T K}
    (hk : ∀ t, k.mem t ↔ t = A ∨ t = B) (hf : ∀ t, k.mem t → k.fin t) :
    (spec false).S k (full (ordPair A B h)) ∧
    (spec false).S k (full (ordPair B A (Ne.symm h))) ∧
    (¬ ∃ u : Partial.ROut T K, full (ordPair A B h) ≼ u ∧ full (ordPair B A (Ne.symm h)) ≼ u) ∧
    ¬ (spec (T := T) (K := K) false).DirectedOutputs ∧
    ¬ (spec (T := T) (K := K) false).LiftedMono :=
  ⟨(ab_ba_rows false h hk hf).1, (ab_ba_rows false h hk hf).2, ab_ba_no_common h,
    spec_not_liftedMono false h hk hf⟩

/-- "The *abort-free* specification permits a row when it can be completed with
`X = ∅`, where a complete output now commits exactly the transactions whose
commit request is in the input and leaves the others undecided …" -/
theorem «app:cc-bases/abort-free-spec» {T K : Type} (k : Inp T K) (u : Partial.ROut T K) :
    (spec true).S k u ↔ ∃ c, Complete true k c ∧ u ≼ c ∧
      ∀ t, ¬ c.o.X t ∧ (c.o.dom t ↔ k.fin t) :=
  ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, h, hc.1⟩, fun ⟨c, hc, h, _⟩ => ⟨c, hc, h⟩⟩

/-- "… the same two rows show that it is not monotone either." -/
theorem «app:cc-bases/abort-free-not-monotone» {T K : Type} {A B : T} (h : A ≠ B) {k : Inp T K}
    (hk : ∀ t, k.mem t ↔ t = A ∨ t = B) (hf : ∀ t, k.mem t → k.fin t) :
    ¬ (spec (T := T) (K := K) true).DirectedOutputs ∧
    ¬ (spec (T := T) (K := K) true).LiftedMono :=
  spec_not_liftedMono true h hk hf

/-! ## Commitments -/

/-- "Applied at a state `(i,R)`, it keeps the rows of `R` that can still be
completed, within `R`, by a complete row satisfying the condition, and removes
the rest.  It is defined when it keeps some row at `i` and removes some row."
(Guards such as "for `A ∈ i`" are part of definedness.) -/
theorem «app:cc-bases/applied» {T K : Type} {af : Bool}
    (G : State (spec (T := T) (K := K) af) → Prop) (Q : Partial.ROut T K → Prop)
    (σ τ : State (spec af)) :
    (closeC G Q).app σ = some τ ↔
      (G σ ∧ (∃ u, Keep σ Q σ.cur u) ∧ ∃ k u, σ.R k u ∧ ¬ Keep σ Q k u) ∧
      τ.cur = σ.cur ∧
      ∀ k u, τ.R k u ↔ σ.R k u ∧ ∃ c, σ.R k c ∧ Decides af k c.o ∧ u ≼ c ∧ Q c :=
  closeC_app_iff

/-- The four conditions.  "`order(A,B)` …: `B` is not committed before `A`,
that is, not `B <_L A`.  `TxCommit(A)` …: `A ∉ X`.  `abort(A)` …:
`A ∉ dom L`.  `stamp(A)` …: no committed transaction outside `Z ∪ {A}`
precedes `A` in `L`, and no committed transaction of `Z` follows `A`.
`read(A,k,v)` …: the output reports that this read returned the version `v`." -/
theorem «app:cc-bases/conditions» {T K : Type} (A B : T) (Z : T → Prop) (o : Outcome T)
    (r : Partial.ROut T K) (n : Nat) (v : Option T) :
    (OrderOK A B o ↔ ¬ o.lt B A) ∧ (CommitOK A o ↔ ¬ o.X A) ∧ (AbortOK A o ↔ ¬ o.dom A) ∧
    (StampOK A Z o ↔ (∀ D, ¬ Z D → D ≠ A → ¬ o.lt D A) ∧ ∀ z, Z z → ¬ o.lt A z) ∧
    ((fun c : Partial.ROut T K => c.ρ A n = some v) r ↔ r.ρ A n = some v) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- `order(A,B)`, for distinct `A,B ∈ i`. -/
noncomputable abbrev «app:cc-bases/order» {T K : Type} {af : Bool} (A B : T) :
    Commitment (spec (T := T) (K := K) af) := order A B
/-- `TxCommit(A)`, for `A` whose commit request is in `i`. -/
noncomputable abbrev «app:cc-bases/commit» {T K : Type} {af : Bool} (A : T) :
    Commitment (spec (T := T) (K := K) af) := commit A
/-- `abort(A)`, for `A ∈ i`. -/
noncomputable abbrev «app:cc-bases/abort» {T K : Type} {af : Bool} (A : T) :
    Commitment (spec (T := T) (K := K) af) := abort A
/-- `stamp(A)`, for `A ∈ i ∖ Z`, `Z ⊆ i`. -/
noncomputable abbrev «app:cc-bases/stamp» {T K : Type} {af : Bool} (A : T) (Z : T → Prop) :
    Commitment (spec (T := T) (K := K) af) := stamp A Z
/-- `read(A,k,v)`, for `A ∈ i` whose `k`-th operation in `i` is a read. -/
noncomputable abbrev «app:cc-bases/read» {T K : Type} {af : Bool} (A : T) (n : Nat)
    (v : Option T) : Commitment (spec (T := T) (K := K) af) := read A n v

/-- "Each is a commitment (Definition `def:commitment`).  If a kept row refines
another row at the same input, the complete row that keeps it also refines the
other, which is therefore kept; so no removed row is refined by a kept one, as
Equation `eq:commitment-excludes` requires."  Every closure commitment, for
every guard and condition, is a `Commitment` (`closeC`); this states
Eq. `commitment-excludes` for it. -/
theorem «app:cc-bases/each-is-commitment» {T K : Type} {af : Bool}
    (G : State (spec (T := T) (K := K) af) → Prop) (Q : Partial.ROut T K → Prop)
    (σ τ : State (spec af)) (h : (closeC G Q).app σ = some τ) :
    ∀ k u w, σ.R k u → ¬ τ.R k u → τ.R k w → ¬ (u ≼ w) :=
  (closeC G Q).excludes σ τ h

/-- "… for them a complete row is kept exactly when it satisfies the condition,
since two permitted complete outputs at one input, one refining the other, have
the same serial order and abort set."  (In both specifications.) -/
theorem «app:cc-bases/complete-kept-iff» {T K : Type} {af : Bool}
    {σ : State (spec (T := T) (K := K) af)} {P : Outcome T → Prop} {k : Inp T K}
    {c : Partial.ROut T K} (hp : Decides af k c.o) :
    Keep σ (fun c => P c.o) k c ↔ σ.R k c ∧ P c.o :=
  keep_complete hp

/-- "The bases are `B_2PL = {order, TxCommit, abort, read}` and
`B_MVTO = {stamp, TxCommit, abort, read}`, over all transactions, positions,
and versions." -/
theorem «app:cc-bases/bases» {T K : Type} {af : Bool} (c : Commitment (spec (T := T) (K := K) af)) :
    (basis2PL c ↔ (∃ A B, c = order A B) ∨ (∃ A, c = commit A) ∨ (∃ A, c = abort A) ∨
      (∃ A n v, c = read A n v)) ∧
    (basisMVTO c ↔ (∃ A Z, c = stamp A Z) ∨ (∃ A, c = commit A) ∨ (∃ A, c = abort A) ∨
      (∃ A n v, c = read A n v)) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- "… and differ in how they order.  Let `{A,B,C}` be an input in which `A`,
`B`, and `C` have each requested commit, after any operations.  At its
canonical state, no commitment of `B_MVTO` has the effect of `order(A,B)`, and
no commitment of `B_2PL` has the effect of `stamp(B)` with `Z = ∅`."  Both are
defined there.  (`Tri k A B C`; such an input exists for any three
transactions: `triDone`.) -/
theorem «app:cc-bases/bases-differ» {T K : Type} {A B C : T} {k : Inp T K}
    (h : Tri k A B C) :
    (∃ τ, (order A B).app (σ3 k) = some τ ∧ ∀ c, basisMVTO c → c.app (σ3 k) ≠ some τ) ∧
    (∃ τ, (stamp B (fun _ => False)).app (σ3 k) = some τ ∧
      ∀ c, basis2PL c → c.app (σ3 k) ≠ some τ) :=
  let ⟨τ, hτ, _⟩ := order_at h
  let ⟨τ', hτ', _⟩ := stamp_at h
  ⟨⟨τ, hτ, order_not_MVTO h hτ⟩, ⟨τ', hτ', stamp_not_2PL h hτ'⟩⟩

/-- "In every state that a run under either basis reaches, each row has a
complete refinement in the table at its input, and any output between two rows
of the table at one input is itself a row of the table."  (`Good`.) -/
theorem «app:cc-bases/run-states» {T K : Type} {af : Bool} {i : Inp T K}
    {es : List (SEvent (spec (T := T) (K := K) af))} {τ : State (spec af)}
    (h : SysExec basis2PL (canon _ i) es τ ∨ SysExec basisMVTO (canon _ i) es τ) :
    (∀ k x, τ.R k x → ∃ c, τ.R k c ∧ Decides af k c.o ∧ x ≼ c) ∧
    (∀ k x y c, τ.R k x → τ.R k c → x ≼ y → y ≼ c → τ.R k y) :=
  let hg : Good τ := h.elim good_run.1 good_run.2
  ⟨hg.2, hg.1⟩

/-- "So a read is reported by applying `read(A,k,v)` and then emitting the
result, which is then exposable."  Precisely: after `read(A,k,v)`, adding the
result to a row that every remaining row refines gives a row, and emitting it is
exposable.  (At any state with the two properties above.) -/
theorem «app:cc-bases/read-emit» {T K : Type} {af : Bool} {A : T} {n : Nat} {v : Option T}
    {σ σ' : State (spec (T := T) (K := K) af)} (hg : Good σ)
    (h : (read A n v).app σ = some σ') {u : Partial.ROut T K} {k : Inp T K} (hu : σ'.R k u)
    (hall : ∀ k w, σ'.R k w → u ≼ w) :
    σ'.R k (addRead u A n v) ∧ Exposable σ' (addRead u A n v) :=
  read_emit hg h hu hall

/-! ## 2PL -/

/-- "If `A` holds that lock in a conflicting mode, `B` waits, and the scheduler
applies `order(A,B)` in a commitment event, reporting nothing.  On complete rows
without aborts, `order(A,B)` keeps exactly those with `A` before `B` (Figure
`fig:cc-commitments`(h))." -/
theorem «app:cc-bases/fig-h» {T K : Type} {A B : T}
    {σ τ : State (spec (T := T) (K := K) false)} (h : (order A B).app σ = some τ)
    {k : Inp T K} {c : Partial.ROut T K} (hp : Decides false k c.o) (hX : ∀ t, ¬ c.o.X t)
    (hA : k.mem A) (hB : k.mem B) :
    τ.R k c ↔ σ.R k c ∧ c.o.lt A B :=
  fig_h h hp hX hA hB

/-- "At the canonical state of `{A,B,C}` it removes `[B,A,C]` and keeps
`[A,B,C]` and `[C,A,B]`, so it is a choice, and it is not the choice `c_o` of
any output `o`." -/
theorem «app:cc-bases/order-at-ABC» {T K : Type} {A B C : T} {k : Inp T K} (h : Tri k A B C) :
    ∃ τ, (order A B).app (σ3 k) = some τ ∧
      τ.R k (full (mk [A, B, C] fun _ => False)) ∧
      τ.R k (full (mk [C, A, B] fun _ => False)) ∧
      ¬ τ.R k (full (mk [B, A, C] fun _ => False)) ∧
      ∀ o, (choiceC o).app (σ3 k) ≠ some τ :=
  let ⟨τ, hτ, h1, h2, h3⟩ := order_at h
  ⟨τ, hτ, h1, h2, h3, (neither_is_choice h).1 τ hτ⟩

/-- "A deadlock between `A` and `B` arises when `B` waits for a lock that `A`
holds and an operation of `A` then waits for a lock that `B` holds: the
scheduler has applied `order(A,B)` and later `order(B,A)`.  Then no remaining
row, at any input, commits both `A` and `B`, so every remaining complete row
aborts one of them, and resolving the deadlock means aborting one."
"Remaining" is: in any table contained in the one after `order(B,A)`. -/
theorem «app:cc-bases/deadlock» {T K : Type} {A B : T}
    {σ σ1 σ1' σ2 : State (spec (T := T) (K := K) false)}
    (h1 : (order A B).app σ = some σ1) (hs : ∀ k u, σ1'.R k u → σ1.R k u)
    (h2 : (order B A).app σ1' = some σ2) {R : Inp T K → Partial.ROut T K → Prop}
    (hR : ∀ k u, R k u → σ2.R k u) :
    (∀ k w, R k w → ¬ (w.o.dom A ∧ w.o.dom B)) ∧
    (∀ k c, R k c → Decides false k c.o → k.mem A → k.mem B → c.o.X A ∨ c.o.X B) :=
  ⟨fun _ _ hw => deadlock h1 hs h2 hR hw,
   fun _ _ hc hp hA hB => deadlock_complete h1 hs h2 hR hc hp hA hB⟩

/-- "Once the scheduler applies `TxCommit(A)`, every remaining complete row
aborts `B`, and `TxCommit(B)` is never again defined." -/
theorem «app:cc-bases/deadlock-resolution» {T K : Type} {A B : T}
    {σ σ1 σ1' σ2 σ3 σ4 : State (spec (T := T) (K := K) false)}
    (h1 : (order A B).app σ = some σ1) (hs : ∀ k u, σ1'.R k u → σ1.R k u)
    (h2 : (order B A).app σ1' = some σ2) (hs' : ∀ k u, σ3.R k u → σ2.R k u)
    (h3 : (commit A).app σ3 = some σ4) (τ : State (spec false))
    (hτ : ∀ k u, τ.R k u → σ4.R k u) :
    (∀ k c, τ.R k c → Decides false k c.o → c.o.X B) ∧ (commit B).app τ = none :=
  deadlock_commit h1 hs h2 hs' h3 τ hτ

/-- "Under the abort-free specification, once both orderings have been applied,
no remaining row is at an input in which both `A` and `B` have requested
commit.  The system never accepts both requests, so at least one of `A` and
`B` waits forever."  The second part: no state that any later execution (under
any basis) reaches is at such an input. -/
theorem «app:cc-bases/abort-free-waits-forever» {T K : Type} {A B : T}
    {σ σ1 σ1' σ2 : State (spec (T := T) (K := K) true)}
    (h1 : (order A B).app σ = some σ1) (hs : ∀ k u, σ1'.R k u → σ1.R k u)
    (h2 : (order B A).app σ1' = some σ2) :
    (∀ (R : Inp T K → Partial.ROut T K → Prop), (∀ k u, R k u → σ2.R k u) →
      ∀ k w, R k w → ¬ (k.fin A ∧ k.fin B)) ∧
    ∀ (Bs : Basis (spec true)) es τ, SysExec Bs σ2 es τ → ¬ (τ.cur.fin A ∧ τ.cur.fin B) :=
  ⟨fun _ hR _ _ hw => abortFree_deadlock h1 hs h2 hR hw,
   fun Bs _ _ hx => abortFree_never_both h1 hs h2 Bs hx⟩

/-! ## MVTO -/

/-- "On complete rows without aborts, `stamp(B)` with `Z = ∅` keeps exactly
those with `B` first (Figure `fig:cc-commitments`(i))." -/
theorem «app:cc-bases/fig-i» {T K : Type} {B : T}
    {σ τ : State (spec (T := T) (K := K) false)} (h : (stamp B (fun _ => False)).app σ = some τ)
    {k : Inp T K} {c : Partial.ROut T K} (hp : Decides false k c.o) (hX : ∀ t, ¬ c.o.X t)
    (hB : k.mem B) :
    τ.R k c ↔ σ.R k c ∧ ∀ D, k.mem D → D ≠ B → c.o.lt B D :=
  fig_i h hp hX hB

/-- "… at the canonical state of `{A,B,C}` it is a choice, and it is not the
choice `c_o` of any output": it keeps `[B,A,C]` and `[B,C,A]` and removes
`[A,B,C]` and `[C,B,A]`. -/
theorem «app:cc-bases/stamp-at-ABC» {T K : Type} {A B C : T} {k : Inp T K} (h : Tri k A B C) :
    ∃ τ, (stamp B (fun _ => False)).app (σ3 k) = some τ ∧
      τ.R k (full (mk [B, A, C] fun _ => False)) ∧
      τ.R k (full (mk [B, C, A] fun _ => False)) ∧
      ¬ τ.R k (full (mk [A, B, C] fun _ => False)) ∧
      ¬ τ.R k (full (mk [C, B, A] fun _ => False)) ∧
      ∀ o, (choiceC o).app (σ3 k) ≠ some τ :=
  let ⟨τ, hτ, h1, h2, h3, h4⟩ := stamp_at h
  ⟨τ, hτ, h1, h2, h3, h4, (neither_is_choice h).2 τ hτ⟩

/-- *What a read is a commitment to*, the row argument: "At an input in which
`A` writes `x`, a complete row that satisfies both stamps and commits both `A`
and `B` places `A` between that version and `B`, so it does not permit the
read."  `Z_B ∋ A` is "`B` stamped after `A`"; the read is the `n`-th operation
of `B`; the version is the initial one or written by `W ∈ Z_A`, `W ≠ A`. -/
theorem «app:cc-bases/mvto-row» {T K : Type} {k : Inp T K} {c : Partial.ROut T K}
    (hc : Complete false k c) {A B : T} {ZA ZB : T → Prop} {x : K} {n : Nat}
    {v : Option T} (hsA : StampOK A ZA c.o) (hsB : StampOK B ZB c.o) (hAB : ZB A)
    (hBB : ¬ ZB B) (hwA : k.writes A x) (hop : k.op B n = some (.rd x))
    (hv : ∀ W, v = some W → ZA W ∧ W ≠ A) (hρ : c.ρ B n = some v) :
    ¬ (c.o.dom A ∧ c.o.dom B) :=
  fun ⟨hA, hB⟩ => stamps_row hc hsA hsB hAB hBB hwA hop hv hρ hA hB

/-- "Hence, after the two stamps, no row that reports the read and is at an
input in which `A` writes `x` commits both `A` and `B`.  Once `read` has been
applied, no remaining row at such an input commits both, whether it reports the
read or not.  Reporting the read is a commitment to this: if `A` writes `x`,
then `A` and `B` do not both commit."  The two stamps are
`TwoStamps A B Z_A Z_B σ σ2` (`stamp(A)`, anything, `stamp(B)` with
`A ∈ Z_B`); "remaining" is: in any table contained in the one after the stamps
(resp. after `read(B,n,v)`). -/
theorem «app:cc-bases/read-commits» {T K : Type} {af : Bool} {A B : T} {ZA ZB : T → Prop}
    {σ σ2 : State (spec (T := T) (K := K) af)} (H : TwoStamps A B ZA ZB σ σ2) {x : K}
    {n : Nat} {v : Option T} (hv : ∀ W, v = some W → ZA W) :
    (∀ (R : Inp T K → Partial.ROut T K → Prop), (∀ k u, R k u → σ2.R k u) →
      ∀ k w, k.writes A x → k.op B n = some (.rd x) → R k w → w.ρ B n = some v →
        ¬ (w.o.dom A ∧ w.o.dom B)) ∧
    (∀ σ3 σ4 : State (spec af), (∀ k u, σ3.R k u → σ2.R k u) →
      (read B n v).app σ3 = some σ4 →
      ∀ (R : Inp T K → Partial.ROut T K → Prop), (∀ k u, R k u → σ4.R k u) →
      ∀ k w, k.writes A x → k.op B n = some (.rd x) → R k w → ¬ (w.o.dom A ∧ w.o.dom B)) :=
  ⟨fun _ hR _ _ hwA hop hw hρ => H.no_both hv hR hwA hop hw hρ,
   fun _ _ hs3 h _ hR _ _ hwA hop hw => H.read_no_both hv hs3 h hR hwA hop hw⟩

/-- "The condition on the version is needed.  At an input of three
transactions `A`, `W`, `B`, stamped in that order, each having requested
commit, with `A` and `W` writing `x` and `B` only reading it, the complete row
that commits all three in stamp order and reports that `B` read `W`'s write is
permitted and satisfies every stamp."  ("Only reading it": the read is not
preceded by a write of `x` by `B`.) -/
theorem «app:cc-bases/writer-before-A» {T K : Type} {A W B : T} {k : Inp T K}
    (hk : Tri k A W B) {x : K} {n : Nat} (hwA : k.writes A x) (hwW : k.writes W x)
    (hop : k.op B n = some (.rd x)) (hown : ¬ OwnW k B n x) :
    let r : Partial.ROut T K := ⟨mk [A, W, B] fun _ => False, single B n (some W)⟩
    Complete false k r ∧ StampOK A (fun _ => False) r.o ∧
      StampOK W (· = A) r.o ∧ StampOK B (fun z => z = A ∨ z = W) r.o ∧
      k.writes A x ∧ r.ρ B n = some (some W) ∧ r.o.dom A :=
  writer_after_A hk hwA hwW hop hown

/-- *When the abort is entailed.*  "Suppose `A`'s write of `x` has arrived.  If
every remaining complete row commits `B`, for instance after `TxCommit(B)`,
then every remaining complete row aborts `A`.  Emitting `A`'s abort, added to a
row that reports the read and that every remaining row refines, is then
exposable: the specification entails the abort."  (Lean also shows that no
remaining row commits `A`.)  Stated at any state `τ` with the two properties of
`«app:cc-bases/run-states»` whose table is contained in the one after the two
stamps, at an input in which `A` writes `x`. -/
theorem «app:cc-bases/abort-entailed» {T K : Type} {A B : T} {ZA ZB : T → Prop}
    {σ σ2 : State (spec (T := T) (K := K) false)} (H : TwoStamps A B ZA ZB σ σ2) {x : K}
    {n : Nat} {v : Option T} (hv : ∀ W, v = some W → ZA W) {τ : State (spec false)}
    (hτ : ∀ k u, τ.R k u → σ2.R k u) (hg : Good τ) (hwA : τ.cur.writes A x)
    (hop : τ.cur.op B n = some (.rd x)) {u : Partial.ROut T K}
    (hall : ∀ k w, τ.R k w → u ≼ w) (hρ : u.ρ B n = some v)
    (hB : ∀ k c, τ.R k c → Decides false k c.o → c.o.dom B) :
    (∀ k w, τ.R k w → ¬ w.o.dom A) ∧
    (∀ k c, τ.R k c → Decides false k c.o → c.o.X A) ∧
    (τ.R τ.cur u → τ.R τ.cur (addAbort u A) ∧ Exposable τ (addAbort u A)) :=
  H.abort_entailed hv hτ hg hwA hop hall hρ hB

/-- "While `B` is undecided, it does not.  Consider a run in which `A`'s first
operation, a read of `x`, arrives, then `B`'s read of `x`, and then `A`'s write
of `x`, with further transactions free to arrive.  The scheduler applies
`stamp(A)` and `stamp(B)` in commitment events and reports that `B` read the
initial version of `x`.  Reporting the read is not exposable on its own, since
at an input in which `A` writes `x` the row that commits `A` and then `B`
cannot be completed with it; the output event that applies `read` and then
reports the read is legal under `B_MVTO`.  After `A`'s write arrives, two
completions remain at the input in which both then request commit: `B`
committed with `A` aborted, and `A` committed with `B` aborted.  Emitting
`A`'s abort is not exposable, and `abort(A)` and `abort(B)` are both defined
and keep different completions.  MVTO's write rule aborts `A` at once, with the
output event that applies `abort(A)` and reports the abort, which is legal
under `B_MVTO`.  That abort is the scheduler's choice between two outcomes the
specification still permits.  If instead the scheduler waits until `B`'s commit
request arrives and applies `TxCommit(B)`, `A`'s abort becomes exposable."

(`C` is the further transaction: `stamp(B)` is defined because `C` may still
arrive and be ordered before `B`.  `Ex.i1`–`Ex.i4` are the inputs after each
arrival, `Ex.j2` the input in which both have requested commit; `Ex.u B` is the
output reporting the read, `Ex.r1`/`Ex.r2` the two completions, `Ex.rAB` the
row `[A,B]`.) -/
theorem «app:cc-bases/abort-is-a-choice» {T K : Type} {A B C : T} (h : Distinct3 A B C)
    (x : K) :
    ∃ σ1 σ2 σ3 σ3r σ4 σ5 σ6 σ7 σ8 : State (spec (T := T) (K := K) false),
      SysStep basisMVTO (canon _ (Ex.i1 (A := A) x)) (.commit [stamp A (fun _ => False)]) σ1 ∧
      SysStep basisMVTO σ1 (.input (Ex.i2 h x)) σ2 ∧
      SysStep basisMVTO σ2 (.commit [stamp B (· = A)]) σ3 ∧
      σ3.R (Ex.j2 h x) (Ex.rAB A B) ∧ ¬ Exposable σ3 (Ex.u B) ∧
      (read B 0 none).app σ3 = some σ3r ∧ ¬ σ3r.R (Ex.j2 h x) (Ex.rAB A B) ∧
      SysStep basisMVTO σ3 (.output [read B 0 none] (Ex.u B)) σ4 ∧
      SysStep basisMVTO σ4 (.input (Ex.i3 h x)) σ5 ∧
      σ5.R (Ex.j2 h x) (Ex.r1 A B) ∧ σ5.R (Ex.j2 h x) (Ex.r2 A B) ∧
      ¬ Exposable σ5 (addAbort (Ex.u B) A) ∧
      (∃ τA, (abort A).app σ5 = some τA ∧
        τA.R (Ex.j2 h x) (Ex.r1 A B) ∧ ¬ τA.R (Ex.j2 h x) (Ex.r2 A B)) ∧
      (∃ τB, (abort B).app σ5 = some τB ∧
        τB.R (Ex.j2 h x) (Ex.r2 A B) ∧ ¬ τB.R (Ex.j2 h x) (Ex.r1 A B)) ∧
      (∃ τe, SysStep basisMVTO σ5 (.output [abort A] (addAbort (Ex.u B) A)) τe) ∧
      SysStep basisMVTO σ5 (.input (Ex.i4 h x)) σ6 ∧
      SysStep basisMVTO σ6 (.commit [commit B]) σ7 ∧
      Exposable σ7 (addAbort (Ex.u B) A) ∧
      SysStep basisMVTO σ7 (.output [] (addAbort (Ex.u B) A)) σ8 :=
  Ex.mvto_run h x

/-! ## Comparison -/

/-- "Under MVTO, a later transaction's read of an older version is a commitment
that, if the writer writes that key, the writer and the reader do not both
commit.  The write rule settles this by aborting the writer when its write
arrives, and the specification forces that abort only after the reader
commits."  The first part is `«app:cc-bases/read-commits»`; the second is
`«app:cc-bases/abort-entailed»` together with the run of
`«app:cc-bases/abort-is-a-choice»`, restated here: after the write arrives,
`A`'s abort is not exposable while `B` is undecided, the write rule's
`Out_[abort(A)]` is legal, and once `TxCommit(B)` has been applied the abort is
exposable. -/
theorem «app:cc-bases/comparison» {T K : Type} {A B C : T} (h : Distinct3 A B C) (x : K) :
    ∃ σ5 σ7 : State (spec (T := T) (K := K) false),
      ¬ Exposable σ5 (addAbort (Ex.u B) A) ∧
      (∃ τe, SysStep basisMVTO σ5 (.output [abort A] (addAbort (Ex.u B) A)) τe) ∧
      (∃ σ6, SysStep basisMVTO σ5 (.input (Ex.i4 h x)) σ6 ∧
        SysStep basisMVTO σ6 (.commit [commit B]) σ7) ∧
      Exposable σ7 (addAbort (Ex.u B) A) :=
  let ⟨_, _, _, _, _, σ5, σ6, σ7, _, _, _, _, _, _, _, _, _, _, _, _, hne, _, _, he, h6, h7,
    hex, _⟩ := Ex.mvto_run (K := K) h x
  ⟨σ5, σ7, hne, he, ⟨σ6, h6, h7⟩, hex⟩

end Paper
end CC
