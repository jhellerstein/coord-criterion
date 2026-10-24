import CoordCriterion.Appendix.TransactionBases.PaperSpec

/-!
# Paper, Appendix G: Commitment bases for 2PL and MVTO (`app:cc-bases`)

Source: `appendices/commitment-bases.tex` (the whole appendix).

How to read this file: it follows the appendix paragraph by paragraph
(Specification, Commitments, 2PL, MVTO, Comparison).  The appendix has no
numbered results; every claim it states or argues gets a declaration named
`«app:cc-bases/<slug>»` in namespace `CC.Paper`.  Each docstring quotes the
claim; the statement is written out in full in terms of library definitions,
and the proof points to the library.

Library correspondence:
* The specification with outputs `(L,X,ρ)` is `CC.Txn.Reads.readSpec rd wr`
  (`Appendix/TransactionBases/ReadSpec.lean`), where `rd a x` / `wr a x` say
  transaction `a` reads / writes key `x`.  An output is `r : ROut T K`, with
  `r.o : Outcome T` the pair `(L,X)` (`r.o.X` the abort set, `r.o.dom` = `dom L`,
  `r.o.lt` = `<_L`) and `r.ρ a x = some v` the reported read of `x` by `a`
  (`v = none`: the initial version; `v = some W`: the write by `W`).
* Inputs are `FinSet T` (finite sets, presented by a duplicate-free list),
  ordered by inclusion.
* The commitments are row filters (`CC.Txn.Reads.filterCS`); their conditions
  are `orderP`, `commitP`, `abortP`, `stampP` of `NoReads.lean`, read on `r.o`.
* The simpler specification without read results (`CC.Txn.txnSpec`,
  `NoReads.lean`) is what the figures show; see
  `«app:cc-bases/figures-without-reads»`.
-/

namespace CC
namespace Paper

open CC.Txn CC.Txn.Reads CC.Txn.Full

/-! ## Specification -/

/-- "An input is a finite set of transactions … inputs are ordered by
inclusion."  `FinSet T` with `a ≼ b ↔ ∀ x, a x → b x`. -/
abbrev «app:cc-bases/input» (T : Type) := FinSet T

/-- Inputs are ordered by inclusion. -/
theorem «app:cc-bases/input-order» {T : Type} (a b : FinSet T) :
    a ≼ b ↔ ∀ x, a.1 x → b.1 x := Iff.rfl

/-- "We write an output as `(L,X,ρ)`: `X` is the set of aborted transactions,
`L` is the serial order, a total order on the set `dom L` of committed ones, and
`ρ` is the set of reported read results." -/
abbrev «app:cc-bases/output» (T K : Type) := ROut T K

/-- "`(L,X,ρ) ⪯ (L',X',ρ') ⟺ X ⊆ X', dom L ⊆ dom L', L'|_{dom L} = L, ρ ⊆ ρ'`."
(The restriction `L'|_{dom L} = L` is: `L'` and `L` agree on pairs from
`dom L`; `ρ ⊆ ρ'` is: `ρ'` extends the partial map `ρ`.) -/
theorem «app:cc-bases/output-order» {T K : Type} (r r' : ROut T K) :
    r ≼ r' ↔
      (∀ t, r.o.X t → r'.o.X t) ∧ (∀ t, r.o.dom t → r'.o.dom t) ∧
      (∀ a b, r.o.dom a → r.o.dom b → (r'.o.lt a b ↔ r.o.lt a b)) ∧
      (∀ a x v, r.ρ a x = some v → r'.ρ a x = some v) :=
  ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩⟩

/-- "Each reported read of a key `x` by a transaction `T` returns the write of
`x` by the last transaction before `T` in the serial order that writes `x`, or
the initial version of `x` if no earlier transaction writes it."  This is
`LastWrite wr o a x v`. -/
theorem «app:cc-bases/last-write» {T K : Type} (wr : T → K → Prop) (o : Outcome T) (a : T)
    (x : K) :
    (LastWrite wr o a x none ↔ ∀ w, o.lt w a → ¬ wr w x) ∧
    ∀ W, LastWrite wr o a x (some W) ↔
      o.lt W a ∧ wr W x ∧ ∀ w', o.lt W w' → o.lt w' a → ¬ wr w' x :=
  ⟨Iff.rfl, fun _ => Iff.rfl⟩

/-- "A row is permitted when every transaction of the input is committed or
aborted, and not both, and each reported read … returns the [last] write …"
(a reported read is a read of a key the transaction reads, by a committed
transaction). -/
theorem «app:cc-bases/permitted» {T K : Type} (rd wr : T → K → Prop) (k : FinSet T)
    (r : ROut T K) :
    (readSpec rd wr).S k r ↔
      (∀ t, (k.1 t ↔ r.o.X t ∨ r.o.dom t) ∧ ¬ (r.o.X t ∧ r.o.dom t)) ∧
      ∀ a x v, r.ρ a x = some v → r.o.dom a ∧ rd a x ∧ LastWrite wr r.o a x v :=
  Iff.rfl

/-- The specification itself (total: abort everything, report nothing). -/
abbrev «app:cc-bases/spec» {T K : Type} (rd wr : T → K → Prop) := readSpec rd wr

/-- "The figures … show only the serial order, for transactions without
reads."  An output `(L,X,∅)` reporting no reads is permitted exactly when
`(L,X)` is a row of the specification without read results
(`CC.Txn.txnSpec`). -/
theorem «app:cc-bases/figures-without-reads» {T K : Type} (rd wr : T → K → Prop)
    (k : FinSet T) (o : Outcome T) :
    (readSpec rd wr).S k (noReads (K := K) o) ↔ (txnSpec T).S k o :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ _ _ h => by cases h⟩⟩

/-- "The rows `({A,B},([A,B],∅,∅))` and `({A,B},([B,A],∅,∅))`, corresponding
to Figure (f), have no common output [refinement], since it would order `A`
before `B` and `B` before `A`; so the specification is not monotone."  The
no-common-refinement claim is proved in all of `ROut T K`; non-monotonicity is
stated as failure of Directed Outputs and of Lifted Monotonicity. -/
theorem «app:cc-bases/ab-ba-not-monotone» {T K : Type} (rd wr : T → K → Prop) {A B : T}
    (h : A ≠ B) :
    (readSpec rd wr).S (pairSet A B h) (noReads (K := K) (ordPair A B h)) ∧
    (readSpec rd wr).S (pairSet A B h) (noReads (K := K) (ordPair B A (Ne.symm h))) ∧
    (¬ ∃ u : ROut T K, noReads (ordPair A B h) ≼ u ∧ noReads (ordPair B A (Ne.symm h)) ≼ u) ∧
    ¬ (readSpec (K := K) rd wr).DirectedOutputs ∧ ¬ (readSpec (K := K) rd wr).LiftedMono :=
  ⟨(full_ab_ba_rows rd wr h).1.1, (full_ab_ba_rows rd wr h).2.1, full_no_common_refinement h,
    full_not_liftedMono rd wr h⟩

/-- "The *abort-free* specification has the same rows with `X = ∅`." -/
abbrev «app:cc-bases/abort-free-spec» {T K : Type} (rd wr : T → K → Prop) :=
  abortFreeFull (T := T) (K := K) rd wr

/-- The abort-free rows are the permitted rows with `X = ∅`. -/
theorem «app:cc-bases/abort-free-rows» {T K : Type} (rd wr : T → K → Prop) (k : FinSet T)
    (r : ROut T K) :
    (abortFreeFull rd wr).S k r ↔ (readSpec rd wr).S k r ∧ ∀ t, ¬ r.o.X t :=
  Iff.rfl

/-- The same two rows show that the abort-free specification is not monotone
either (implicit in the appendix: both rows have `X = ∅`). -/
theorem «app:cc-bases/abort-free-not-monotone» {T K : Type} (rd wr : T → K → Prop) {A B : T}
    (h : A ≠ B) :
    ¬ (abortFreeFull (K := K) rd wr).DirectedOutputs ∧
      ¬ (abortFreeFull (K := K) rd wr).LiftedMono :=
  abortFreeFull_not_liftedMono rd wr h

/-! ## Commitments -/

/-- "`order(A,B)`, for distinct `A,B ∈ i`: `A ∈ X`, or `B ∈ X`, or `A <_L B`." -/
theorem «app:cc-bases/order-condition» {T : Type} (A B : T) (k : FinSet T) (o : Outcome T) :
    orderP A B k o ↔ o.X A ∨ o.X B ∨ o.lt A B := Iff.rfl

/-- "`commit(A)`, for `A ∈ i`: `A ∉ X`.  `abort(A)`, for `A ∈ i`: `A ∈ X`." -/
theorem «app:cc-bases/commit-abort-condition» {T : Type} (A : T) (k : FinSet T)
    (o : Outcome T) :
    (commitP A k o ↔ ¬ o.X A) ∧ (abortP A k o ↔ o.X A) := ⟨Iff.rfl, Iff.rfl⟩

/-- "`stamp(A)`, for `A ∈ i ∖ Z`, given `Z ⊆ i`, the transactions stamped
before `A`: at row `(k,(L,X,ρ))`, for every `z ∈ Z`, `z <_L A` or one of `z,A`
is in `X`; and for every `D ∈ k ∖ (Z ∪ {A})`, `A <_L D` or one of `A,D` is in
`X`." -/
theorem «app:cc-bases/stamp-condition» {T : Type} (A : T) (Z : T → Prop) (k : FinSet T)
    (o : Outcome T) :
    stampP A Z k o ↔
      (∀ z, Z z → o.lt z A ∨ o.X z ∨ o.X A) ∧
      (∀ D, k.1 D → ¬ Z D → D ≠ A → o.lt A D ∨ o.X A ∨ o.X D) := Iff.rfl

/-- The commitments `order(A,B)`, `commit(A)`, `abort(A)`, `stamp(A)` (given
`Z`) on the specification with reads. -/
noncomputable abbrev «app:cc-bases/order» {T K : Type} (rd wr : T → K → Prop) (A B : T) :
    Commitment (readSpec rd wr) := orderR rd wr A B
/-- `commit(A)` as a commitment. -/
noncomputable abbrev «app:cc-bases/commit» {T K : Type} (rd wr : T → K → Prop) (A : T) :
    Commitment (readSpec rd wr) := commitR rd wr A
/-- `abort(A)` as a commitment. -/
noncomputable abbrev «app:cc-bases/abort» {T K : Type} (rd wr : T → K → Prop) (A : T) :
    Commitment (readSpec rd wr) := abortR rd wr A
/-- `stamp(A)`, given `Z`, as a commitment. -/
noncomputable abbrev «app:cc-bases/stamp» {T K : Type} (rd wr : T → K → Prop) (A : T) (Z : T → Prop) :
    Commitment (readSpec rd wr) := stampR rd wr A Z

/-- "Applied at a state `(i,R)`, it retains the rows of `R` that satisfy the
condition, and is defined when some row of `R` at `i` satisfies it and some row
of `R` fails it" — for `order(A,B)`, with the guard "distinct `A,B ∈ i`" part of
definedness. -/
theorem «app:cc-bases/order-applied» {T K : Type} (rd wr : T → K → Prop) (A B : T)
    (σ τ : State (readSpec (K := K) rd wr)) :
    (orderR rd wr A B).app σ = some τ ↔
      ((A ≠ B ∧ σ.cur.1 A ∧ σ.cur.1 B) ∧ (∃ o, σ.R σ.cur o ∧ orderP A B σ.cur o.o) ∧
        ∃ k u, σ.R k u ∧ ¬ orderP A B k u.o) ∧
      τ.cur = σ.cur ∧ ∀ k u, τ.R k u ↔ σ.R k u ∧ orderP A B k u.o :=
  filterCS_app_iff

/-- … for `commit(A)` and `abort(A)`. -/
theorem «app:cc-bases/commit-abort-applied» {T K : Type} (rd wr : T → K → Prop) (A : T)
    (σ τ : State (readSpec (K := K) rd wr)) :
    ((commitR rd wr A).app σ = some τ ↔
      ((∃ o, σ.R σ.cur o ∧ commitP A σ.cur o.o) ∧ ∃ k u, σ.R k u ∧ ¬ commitP A k u.o) ∧
      τ.cur = σ.cur ∧ ∀ k u, τ.R k u ↔ σ.R k u ∧ commitP A k u.o) ∧
    ((abortR rd wr A).app σ = some τ ↔
      ((∃ o, σ.R σ.cur o ∧ abortP A σ.cur o.o) ∧ ∃ k u, σ.R k u ∧ ¬ abortP A k u.o) ∧
      τ.cur = σ.cur ∧ ∀ k u, τ.R k u ↔ σ.R k u ∧ abortP A k u.o) :=
  ⟨filterCS_app_iff.trans
      ⟨fun ⟨⟨_, a, b⟩, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨⟨trivial, a, b⟩, c⟩⟩,
   filterCS_app_iff.trans
      ⟨fun ⟨⟨_, a, b⟩, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨⟨trivial, a, b⟩, c⟩⟩⟩

/-- … for `stamp(A)`, with the guard "`Z ⊆ i`" part of definedness. -/
theorem «app:cc-bases/stamp-applied» {T K : Type} (rd wr : T → K → Prop) (A : T)
    (Z : T → Prop) (σ τ : State (readSpec (K := K) rd wr)) :
    (stampR rd wr A Z).app σ = some τ ↔
      ((∀ z, Z z → σ.cur.1 z) ∧ (∃ o, σ.R σ.cur o ∧ stampP A Z σ.cur o.o) ∧
        ∃ k u, σ.R k u ∧ ¬ stampP A Z k u.o) ∧
      τ.cur = σ.cur ∧ ∀ k u, τ.R k u ↔ σ.R k u ∧ stampP A Z k u.o :=
  filterCS_app_iff

/-- "Two permitted outputs at one input, one [refining] the other, have the same
serial order and abort set: … both pairs partition the input, so `X = X'` and
`dom L = dom L'`, hence `L = L'`."  (For both specifications.) -/
theorem «app:cc-bases/comparable-same-LX» {T K : Type} (rd wr : T → K → Prop) {k : FinSet T}
    {u w : ROut T K} :
    ((readSpec rd wr).S k u → (readSpec rd wr).S k w → u ≼ w → u.o = w.o) ∧
    ((abortFreeFull rd wr).S k u → (abortFreeFull rd wr).S k w → u ≼ w → u.o = w.o) :=
  ⟨full_comparable_same_LX rd wr, abortFreeFull_comparable_same_LX rd wr⟩

/-- "Each condition depends only on `L` and `X`, so it holds at both or at
neither."  Any condition `P` on `(k,(L,X))` agrees on comparable permitted rows
at one input. -/
theorem «app:cc-bases/condition-stable» {T K : Type} (rd wr : T → K → Prop)
    (P : FinSet T → Outcome T → Prop) :
    (∀ k (u w : ROut T K), (readSpec rd wr).S k u → (readSpec rd wr).S k w → u ≼ w →
      (P k u.o ↔ P k w.o)) ∧
    (∀ k (u w : ROut T K), (abortFreeFull rd wr).S k u → (abortFreeFull rd wr).S k w →
      u ≼ w → (P k u.o ↔ P k w.o)) :=
  ⟨stable_lift rd wr P, abortFreeFull_stable_lift rd wr P⟩

/-- "Each is a commitment (Definition `def:commitment`) … a removed row is
therefore not [refined] by a retained row at the same input, which is
Equation `eq:commitment-excludes`."  That they are commitments is their type
(`Commitment (readSpec rd wr)`, built by `filterCS` from
`«app:cc-bases/condition-stable»`); this states Eq. `commitment-excludes` for
each of them explicitly. -/
theorem «app:cc-bases/each-is-commitment» {T K : Type} (rd wr : T → K → Prop) :
    ∀ c : Commitment (readSpec (K := K) rd wr),
      ((∃ A B, c = orderR rd wr A B) ∨ (∃ A, c = commitR rd wr A) ∨
        (∃ A, c = abortR rd wr A) ∨ (∃ A Z, c = stampR rd wr A Z)) →
      ∀ σ τ, c.app σ = some τ → ∀ k u w, σ.R k u → ¬ τ.R k u → τ.R k w → ¬ (u ≼ w) :=
  fun c _ => c.excludes

/-- "The bases are `B_2PL = {order, commit, abort}` and
`B_MVTO = {stamp, commit, abort}`, ranging over all transactions." -/
abbrev «app:cc-bases/basis-2PL» {T K : Type} (rd wr : T → K → Prop) :
    Basis (readSpec (T := T) (K := K) rd wr) := basis2PL_R rd wr

/-- `B_MVTO = {stamp, commit, abort}`. -/
abbrev «app:cc-bases/basis-MVTO» {T K : Type} (rd wr : T → K → Prop) :
    Basis (readSpec (T := T) (K := K) rd wr) := basisMVTO_R rd wr

/-- `B_2PL` for the abort-free specification (its `order`, `commit`, `abort`
are the same conditions as filters on `abortFreeFull`). -/
abbrev «app:cc-bases/basis-2PL-abort-free» {T K : Type} (rd wr : T → K → Prop) :
    Basis (abortFreeFull (T := T) (K := K) rd wr) := basis2PL_AF rd wr

/-- Membership in the two bases. -/
theorem «app:cc-bases/basis-members» {T K : Type} (rd wr : T → K → Prop)
    (c : Commitment (readSpec (K := K) rd wr)) :
    (basis2PL_R rd wr c ↔
      (∃ A B, c = orderR rd wr A B) ∨ (∃ A, c = commitR rd wr A) ∨ (∃ A, c = abortR rd wr A)) ∧
    (basisMVTO_R rd wr c ↔
      (∃ A Z, c = stampR rd wr A Z) ∨ (∃ A, c = commitR rd wr A) ∨ (∃ A, c = abortR rd wr A)) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-! ## 2PL -/

/-- "When `B` waits for a lock that `A` holds …, the scheduler applies
`order(A,B)`; on rows without aborts it retains exactly those with `A` before
`B` (Figure `fig:cc-commitments`(h))." -/
theorem «app:cc-bases/fig-h» {T K : Type} (rd wr : T → K → Prop) {k : FinSet T}
    {r : ROut T K} (h : (readSpec rd wr).S k r) (hX : ∀ t, ¬ r.o.X t) (A B : T) :
    orderP A B k r.o ↔ r.o.lt A B :=
  orderP_noabort h hX A B

/-- "A deadlock between `A` and `B` means both `order(A,B)` and `order(B,A)`
have been applied; the rows left, at `i` and every larger input, are exactly
those with `A ∈ X` or `B ∈ X`, so every later output aborts `A` or `B`."  "Every
later output" is stated for the rows of every state reached afterwards (under
any basis); every later emitted output is such a row. -/
theorem «app:cc-bases/deadlock» {T K : Type} {rd wr : T → K → Prop} {A B : T}
    {σ σ1 σ2 : State (readSpec (K := K) rd wr)}
    (h1 : (orderR rd wr A B).app σ = some σ1) (h2 : (orderR rd wr B A).app σ1 = some σ2) :
    (σ2.cur = σ.cur ∧ ∀ k u, σ2.R k u ↔ σ.R k u ∧ (u.o.X A ∨ u.o.X B)) ∧
    ∀ (Bs : Basis (readSpec rd wr)) es τ, SysExec Bs σ2 es τ →
      ∀ k u, τ.R k u → u.o.X A ∨ u.o.X B :=
  ⟨deadlock_state_R h1 h2, fun _ _ τ hx => deadlock_forces_abort_R h1 h2 τ hx.sub⟩

/-- "Under the abort-free specification, once `order(A,B)` is applied no
remaining row satisfies `order(B,A)`, now or later, so it is never defined: `A`,
and hence `B`, waits forever."  Stated for every state with a smaller table,
and for every state any later execution (under any basis) reaches. -/
theorem «app:cc-bases/abort-free-waits-forever» {T K : Type} {rd wr : T → K → Prop} {A B : T}
    {σ σ1 : State (abortFreeFull (K := K) rd wr)}
    (h : (orderAFR rd wr A B).app σ = some σ1) :
    (∀ τ : State (abortFreeFull rd wr), (∀ k u, τ.R k u → σ1.R k u) →
      (orderAFR rd wr B A).app τ = none) ∧
    ∀ (Bs : Basis (abortFreeFull rd wr)) es τ, SysExec Bs σ1 es τ →
      (orderAFR rd wr B A).app τ = none :=
  ⟨abortFree_order_blocks_R h, fun Bs _ _ hx => abortFree_order_blocks_forever_R h Bs hx⟩

/-! ## MVTO -/

/-- "On rows without aborts, `stamp(B)` with `Z = ∅` retains exactly those with
`B` first (Figure `fig:cc-commitments`(i))." -/
theorem «app:cc-bases/fig-i» {T K : Type} (rd wr : T → K → Prop) {k : FinSet T}
    {r : ROut T K} (h : (readSpec rd wr).S k r) (hX : ∀ t, ¬ r.o.X t) (B : T) :
    stampP B (fun _ => False) k r.o ↔ ∀ D, k.1 D → D ≠ B → r.o.lt B D :=
  stampP_first_noabort h hX B

/-- The row-level argument for "the specification itself requires this abort":
"Suppose `A` writes `x`, `B` was stamped after `A`, and an output reports that
`B` read the initial version of `x`, or the write of `x` by a transaction `W`
stamped before `A`.  `B` is committed, since it has a reported read.  If `A`
were committed too, `stamp(B)` would put `A` before `B` in `L`, and `stamp(A)`
would put `W` before `A`; then `A` writes `x` after the version `B` read and
before `B`, so the reported read would not be permitted."  `Z_B ∋ A` is "`B`
stamped after `A`"; `v ∈ {initial} ∪ {write by W ∈ Z_A}`. -/
theorem «app:cc-bases/mvto-abort-row» {T K : Type} {rd wr : T → K → Prop} {k : FinSet T}
    {u : ROut T K} (hu : (readSpec rd wr).S k u) {A B : T} {ZA ZB : T → Prop} {x : K}
    {v : Option T} (hsA : stampP A ZA k u.o) (hsB : stampP B ZB k u.o) (hAB : ZB A)
    (hwA : wr A x) (hv : ∀ W, v = some W → ZA W) (hρ : u.ρ B x = some v) : u.o.X A :=
  forced_abort_row hu hsA hsB hAB hwA hv hρ

/-- "The specification itself requires this abort. … So any output reporting
`B`'s read aborts `A`, and so does every row left once it is emitted."  After
`stamp(A)` (given `Z_A`), anything, `stamp(B)` (given `Z_B ∋ A`), anything, a
legal output event `Out_γ(r)` with `ρ_r(B,x) = v` emits `A ∈ X` and leaves only
rows with `A ∈ X`. -/
theorem «app:cc-bases/mvto-abort-required» {T K : Type} {rd wr : T → K → Prop}
    {Bs : Basis (readSpec rd wr)} {A B : T} {ZA ZB : T → Prop} {x : K} {v : Option T}
    {σ σ1 σ1' σ2 τ0 τ : State (readSpec rd wr)} {es1 es2 : List (SEvent (readSpec rd wr))}
    {γ : List (Commitment (readSpec rd wr))} {r : ROut T K}
    (h1 : (stampR rd wr A ZA).app σ = some σ1) (hx1 : SysExec Bs σ1 es1 σ1')
    (h2 : (stampR rd wr B ZB).app σ1' = some σ2) (hx2 : SysExec Bs σ2 es2 τ0)
    (hout : SysStep Bs τ0 (.output γ r) τ)
    (hAB : ZB A) (hwA : wr A x) (hv : ∀ W, v = some W → ZA W) (hρ : r.ρ B x = some v) :
    r.o.X A ∧ ∀ k u, τ.R k u → u.o.X A :=
  mvto_forced_abort h1 hx1 h2 hx2 hout hAB hwA hv hρ

/-- Non-vacuity of `«app:cc-bases/mvto-abort-required»` (not stated in the
appendix): with `W = 0`, `A = 1`, `B = 2` stamped in that order at `{0,1,2}`,
`0` and `1` writing the single key and `2` reading it, the output event
`Out_γ(([0,2], {1}, ρ(2,x) = write by 0))` with
`γ = abort(1) commit(0) commit(2)` is legal under `B_MVTO`, and it and every
remaining row abort `1`. -/
theorem «app:cc-bases/mvto-abort-instance» :
    ∃ τ : State (readSpec Reads.Ex.rd Reads.Ex.wr),
      SysStep (basisMVTO_R Reads.Ex.rd Reads.Ex.wr) Reads.Ex.S3
        (.output [abortR Reads.Ex.rd Reads.Ex.wr 1, commitR Reads.Ex.rd Reads.Ex.wr 0,
          commitR Reads.Ex.rd Reads.Ex.wr 2] Reads.Ex.r02) τ ∧
      Reads.Ex.r02.o.X 1 ∧ ∀ k u, τ.R k u → u.o.X 1 :=
  Reads.Ex.read_event_legal

/-- "The writer must be stamped before `A`: at input `{A,W,B}` with `A`, `W`,
`B` stamped in that order and `A`, `W` writing `x`, the row that commits all
three in stamp order and reports that `B` read `W`'s write is permitted and
satisfies every stamp."  Instance `A = 0`, `W = 1`, `B = 2`, one key `x = ()`;
`Reads.Ex.wr t x ↔ t = 0 ∨ t = 1`, `Reads.Ex.rd t x ↔ t = 2`; the row is
`([0,1,2], ∅, ρ(2,x) = write by 1)`, and it keeps `A = 0` committed. -/
theorem «app:cc-bases/writer-before-A» :
    let r : ROut Nat Unit :=
      ⟨listOrder [0, 1, 2], fun a _ => if a = 2 then some (some 1) else none⟩
    (readSpec Reads.Ex.rd Reads.Ex.wr).S Reads.Ex.k0 r ∧
      stampP 0 (fun _ => False) Reads.Ex.k0 r.o ∧
      stampP 1 (fun z => z = 0) Reads.Ex.k0 r.o ∧
      stampP 2 (fun z => z = 0 ∨ z = 1) Reads.Ex.k0 r.o ∧
      Reads.Ex.wr 0 () ∧ Reads.Ex.wr 1 () ∧ r.ρ 2 () = some (some 1) ∧ ¬ r.o.X 0 :=
  let ⟨h1, h2, h3, h4, h5, h6, h7⟩ := Reads.Ex.writer_after_A
  ⟨h1, h2, h3, h4, h5, Or.inr rfl, h6, h7⟩

/-- "The requirement comes from the reported read: at input `{W,A,B}`, stamped
in that order, after the three stamps a row that commits `A` and reports no read
for `B` remains."  Instance `W = 0`, `A = 1`, `B = 2` at `Reads.Ex.k0 = {0,1,2}`:
from the canonical state, `stamp(0)` (`Z = ∅`), `stamp(1)` (`Z = {0}`),
`stamp(2)` (`Z = {0,1}`) are all defined and the row `([0,1,2], ∅, ∅)`
remains. -/
theorem «app:cc-bases/requirement-from-read» :
    ∃ σ1 σ2 σ3 : State (readSpec Reads.Ex.rd Reads.Ex.wr),
      (stampR Reads.Ex.rd Reads.Ex.wr 0 (fun _ => False)).app (canon _ Reads.Ex.k0) = some σ1 ∧
      (stampR Reads.Ex.rd Reads.Ex.wr 1 (fun z => z = 0)).app σ1 = some σ2 ∧
      (stampR Reads.Ex.rd Reads.Ex.wr 2 (fun z => z = 0 ∨ z = 1)).app σ2 = some σ3 ∧
      σ3.R Reads.Ex.k0 ⟨listOrder [0, 1, 2], fun _ _ => none⟩ ∧ ¬ (listOrder [0, 1, 2]).X 1 :=
  let ⟨h1, h2, h3, h4, h5, _⟩ := Reads.Ex.reads_rows
  ⟨_, _, _, h1, h2, h3, h4, h5⟩

/-! ## Comparison -/

/-- "Every output decides each transaction of its input, so fixing only `A`'s
status or its relative position is a commitment, never itself an output."
Formalized: every permitted output decides (commits or aborts, not both) each
transaction of its input; the commitments are `«app:cc-bases/order»` etc. -/
theorem «app:cc-bases/outputs-decide-all» {T K : Type} (rd wr : T → K → Prop) (k : FinSet T)
    (r : ROut T K) (h : (readSpec rd wr).S k r) :
    ∀ t, k.1 t → (r.o.X t ∨ r.o.dom t) ∧ ¬ (r.o.X t ∧ r.o.dom t) :=
  fun t ht => ⟨(h.1 t).1.1 ht, (h.1 t).2⟩

end Paper
end CC
