import CoordCriterion.Appendix.TransactionBases.Partial

/-!
# Paper, Appendix G: Commitment bases for 2PL and MVTO (`app:cc-bases`)

Source: `appendices/commitment-bases.tex` (the whole appendix).

How to read this file: it follows the appendix paragraph by paragraph
(Specification, Commitments, 2PL, MVTO, Comparison).  The appendix has no
numbered results; every claim it states or argues gets a declaration named
`«app:cc-bases/<slug>»` in namespace `CC.Paper`.  Each docstring quotes the
claim; the statement is written out in full in terms of library definitions,
and the proof points to the library.

Library correspondence (`Appendix/TransactionBases/Partial.lean`, namespace
`CC.Txn.Partial`):
* The specification is `spec rd wr false` (abort-free variant:
  `spec rd wr true`), where `rd a x` / `wr a x` say transaction `a` reads /
  writes key `x`.  An output is `r : ROut T K`, with `r.o : Outcome T` the pair
  `(L,X)` (`r.o.X` the abort set, `r.o.dom` = `dom L`, `r.o.lt` = `<_L`) and
  `r.ρ a x = some v` the reported read of `x` by `a` (`v = none`: the initial
  version; `v = some W`: the write by `W`).  A transaction in neither `X` nor
  `dom L` is undecided.
* Inputs are `FinSet T` (finite sets, presented by a duplicate-free list),
  ordered by inclusion.
* "Complete at `k`" is `Partitions k r.o`; a permitted complete output is
  `Complete rd wr k r` (with `Permitted` adding `X = ∅` in the abort-free case).
* The commitments are *closure commitments* `closeC G Q`: the guard `G` is the
  appendix's "for `A ∈ i`" etc., the condition `Q` is on complete outputs, and
  a row is kept when a remaining complete row refines it and satisfies `Q`
  (`Keep`).
* What the Lean does not model: the protocol steps (when a lock wait, a
  timestamp, a read, or a write rejection happens) are prose; the Lean proves
  what the corresponding commitments do.
-/

namespace CC
namespace Paper

open CC.Txn CC.Txn.Partial

/-! ## Specification -/

/-- "An input is a finite set of transactions … inputs are ordered by
inclusion."  `FinSet T` with `a ≼ b ↔ ∀ x, a x → b x`. -/
abbrev «app:cc-bases/input» (T : Type) := FinSet T

/-- Inputs are ordered by inclusion. -/
theorem «app:cc-bases/input-order» {T : Type} (a b : FinSet T) :
    a ≼ b ↔ ∀ x, a.1 x → b.1 x := Iff.rfl

/-- "An output has three parts: the committed transactions, in a serial order;
the aborted transactions; and the read results reported so far."  Written
`(L,X,ρ)`. -/
abbrev «app:cc-bases/output» (T K : Type) := Partial.ROut T K

/-- "One output refines another when it extends all three parts …"
`(L,X,ρ) ⪯ (L',X',ρ') ⟺ X ⊆ X', dom L ⊆ dom L', L'|_{dom L} = L, ρ ⊆ ρ'`. -/
theorem «app:cc-bases/output-order» {T K : Type} (r r' : Partial.ROut T K) :
    r ≼ r' ↔
      (∀ t, r.o.X t → r'.o.X t) ∧ (∀ t, r.o.dom t → r'.o.dom t) ∧
      (∀ a b, r.o.dom a → r.o.dom b → (r'.o.lt a b ↔ r.o.lt a b)) ∧
      (∀ a x v, r.ρ a x = some v → r'.ρ a x = some v) :=
  ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩⟩

/-- "… the last transaction before `T` in the serial order that writes `x`, or
the initial version if no earlier transaction writes it." -/
theorem «app:cc-bases/last-write» {T K : Type} (wr : T → K → Prop) (o : Outcome T) (a : T)
    (x : K) :
    (Partial.LastWrite wr o a x none ↔ ∀ w, o.lt w a → ¬ wr w x) ∧
    ∀ W, Partial.LastWrite wr o a x (some W) ↔
      o.lt W a ∧ wr W x ∧ ∀ w', o.lt W w' → o.lt w' a → ¬ wr w' x :=
  ⟨Iff.rfl, fun _ => Iff.rfl⟩

/-- "An output is complete at an input when it commits or aborts every
transaction of the input, and not both.  A complete output is permitted when
each reported read returns the initial version or a write by a transaction of
the input, and each reported read of a key `x` by a committed transaction `T`
returns the write of `x` by the last transaction before `T` … Reads by aborted
transactions are otherwise unconstrained."  (A reported read is a read of a
transaction of the input, of a key it reads.) -/
theorem «app:cc-bases/complete» {T K : Type} (rd wr : T → K → Prop) (k : FinSet T)
    (r : Partial.ROut T K) :
    Complete rd wr k r ↔
      (∀ t, (k.1 t ↔ r.o.X t ∨ r.o.dom t) ∧ ¬ (r.o.X t ∧ r.o.dom t)) ∧
      ∀ a x v, r.ρ a x = some v →
        k.1 a ∧ rd a x ∧ Valid wr k x v ∧ (r.o.dom a → Partial.LastWrite wr r.o a x v) :=
  Iff.rfl

/-- "Any output is permitted when some permitted complete output refines it,
that is, when it can still be completed." -/
theorem «app:cc-bases/permitted» {T K : Type} (rd wr : T → K → Prop) (k : FinSet T)
    (u : Partial.ROut T K) :
    (spec rd wr false).S k u ↔ ∃ c, Complete rd wr k c ∧ u ≼ c :=
  ⟨fun ⟨c, hc, h⟩ => ⟨c, hc.1, h⟩, fun ⟨c, hc, h⟩ => ⟨c, ⟨hc, fun h => by cases h⟩, h⟩⟩

/-- The specification. -/
abbrev «app:cc-bases/spec» {T K : Type} (rd wr : T → K → Prop) := spec (K := K) rd wr false

/-- "The figures … show only complete outputs without aborts or read results,
as serial orders": a serial order of the input, with nothing aborted and no
reads, is a row of both specifications. -/
theorem «app:cc-bases/figure-rows» {T K : Type} (rd wr : T → K → Prop) (af : Bool)
    (k : FinSet T) (o : Outcome T) (h : (abortFreeSpec T).S k o) :
    (spec (K := K) rd wr af).S k (full o) :=
  ⟨full o, ⟨full_complete rd wr h.1, fun _ => h.2⟩, PO.refl _⟩

/-- "Every input has a permitted row: the one that aborts every transaction and
reports nothing." -/
theorem «app:cc-bases/total» {T K : Type} (rd wr : T → K → Prop) (k : FinSet T) :
    (spec (K := K) rd wr false).S k (full (allAbort k)) :=
  ⟨_, ⟨full_complete rd wr (allAbort_part k), fun h => by cases h⟩, PO.refl _⟩

/-- "The rows `({A,B},([A,B],∅,∅))` and `({A,B},([B,A],∅,∅))` of Figure
ambiguity-frames(f) have no common refinement, which would order `A` both before
and after `B`, so the specification is not monotone."  Not monotone: no Directed Outputs, no Lifted
Monotonicity. -/
theorem «app:cc-bases/ab-ba-not-monotone» {T K : Type} (rd wr : T → K → Prop) {A B : T}
    (h : A ≠ B) :
    (spec (K := K) rd wr false).S (pairSet A B h) (full (ordPair A B h)) ∧
    (spec (K := K) rd wr false).S (pairSet A B h) (full (ordPair B A (Ne.symm h))) ∧
    (¬ ∃ u : Partial.ROut T K, full (ordPair A B h) ≼ u ∧ full (ordPair B A (Ne.symm h)) ≼ u) ∧
    ¬ (spec (K := K) rd wr false).DirectedOutputs ∧ ¬ (spec (K := K) rd wr false).LiftedMono :=
  ⟨(ab_ba_rows rd wr false h).1, (ab_ba_rows rd wr false h).2, ab_ba_no_common h,
    spec_not_liftedMono rd wr false h⟩

/-- "The *abort-free* specification permits a row when it can be completed with
`X = ∅`." -/
theorem «app:cc-bases/abort-free-spec» {T K : Type} (rd wr : T → K → Prop) (k : FinSet T)
    (u : Partial.ROut T K) :
    (spec rd wr true).S k u ↔ ∃ c, (Complete rd wr k c ∧ ∀ t, ¬ c.o.X t) ∧ u ≼ c :=
  ⟨fun ⟨c, hc, h⟩ => ⟨c, ⟨hc.1, hc.2 rfl⟩, h⟩, fun ⟨c, hc, h⟩ => ⟨c, ⟨hc.1, fun _ => hc.2⟩, h⟩⟩

/-- "… the same two rows show that it is not monotone either." -/
theorem «app:cc-bases/abort-free-not-monotone» {T K : Type} (rd wr : T → K → Prop) {A B : T}
    (h : A ≠ B) :
    ¬ (spec (K := K) rd wr true).DirectedOutputs ∧ ¬ (spec (K := K) rd wr true).LiftedMono :=
  spec_not_liftedMono rd wr true h

/-! ## Commitments -/

/-- "Applied at a state `(i,R)`, it keeps the rows of `R` that can still be
completed, within `R`, by a complete row meeting the condition, and removes the
rest.  It is defined when it keeps some row at `i` and removes some row."  (Guards such as "for `A ∈ i`" are part of definedness.) -/
theorem «app:cc-bases/applied» {T K : Type} {sp : Spec (FinSet T) (Partial.ROut T K)}
    (G : State sp → Prop) (Q : Partial.ROut T K → Prop) (σ τ : State sp) :
    (closeC G Q).app σ = some τ ↔
      (G σ ∧ (∃ u, Keep σ Q σ.cur u) ∧ ∃ k u, σ.R k u ∧ ¬ Keep σ Q k u) ∧
      τ.cur = σ.cur ∧
      ∀ k u, τ.R k u ↔ σ.R k u ∧ ∃ c, σ.R k c ∧ Partitions k c.o ∧ u ≼ c ∧ Q c :=
  closeC_app_iff

/-- The four conditions.  "`order(A,B)` …: `B` is not committed before `A`,
that is, not `B <_L A`.  `commit(A)`: `A ∉ X`.  `abort(A)`:
`A ∉ dom L`.  `stamp(A)` …: no committed transaction outside `Z ∪ {A}`
precedes `A` in `L`, and no committed transaction of `Z` follows `A`.
`read(A,x,v)`: the output reports that `A`'s read of `x` returned the version
`v`." -/
theorem «app:cc-bases/conditions» {T K : Type} (A B : T) (Z : T → Prop) (o : Outcome T)
    (r : Partial.ROut T K) (x : K) (v : Option T) :
    (OrderOK A B o ↔ ¬ o.lt B A) ∧ (CommitOK A o ↔ ¬ o.X A) ∧ (AbortOK A o ↔ ¬ o.dom A) ∧
    (StampOK A Z o ↔ (∀ D, ¬ Z D → D ≠ A → ¬ o.lt D A) ∧ ∀ z, Z z → ¬ o.lt A z) ∧
    ((fun c : Partial.ROut T K => c.ρ A x = some v) r ↔ r.ρ A x = some v) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- `order(A,B)`, for distinct `A,B ∈ i`. -/
noncomputable abbrev «app:cc-bases/order» {T K : Type} {sp : Spec (FinSet T) (Partial.ROut T K)}
    (A B : T) : Commitment sp := order A B
/-- `commit(A)`, for `A ∈ i`. -/
noncomputable abbrev «app:cc-bases/commit» {T K : Type} {sp : Spec (FinSet T) (Partial.ROut T K)}
    (A : T) : Commitment sp := commit A
/-- `abort(A)`, for `A ∈ i`. -/
noncomputable abbrev «app:cc-bases/abort» {T K : Type} {sp : Spec (FinSet T) (Partial.ROut T K)}
    (A : T) : Commitment sp := abort A
/-- `stamp(A)`, for `A ∈ i ∖ Z`, `Z ⊆ i`. -/
noncomputable abbrev «app:cc-bases/stamp» {T K : Type} {sp : Spec (FinSet T) (Partial.ROut T K)}
    (A : T) (Z : T → Prop) : Commitment sp := stamp A Z
/-- `read(A,x,v)`, for `A ∈ i`. -/
noncomputable abbrev «app:cc-bases/read» {T K : Type} {sp : Spec (FinSet T) (Partial.ROut T K)}
    (A : T) (x : K) (v : Option T) : Commitment sp := read A x v

/-- "Each is a commitment (Definition `def:commitment`).  If a kept row refines
another row at the same input, the complete row that keeps it also refines the
other, which is therefore kept; so no removed row is refined by a kept one, as
Equation `eq:commitment-excludes` requires."  Every closure commitment, for every
guard and condition, is a `Commitment` (`closeC`); this states
Eq. `commitment-excludes` for it. -/
theorem «app:cc-bases/each-is-commitment» {T K : Type} {sp : Spec (FinSet T) (Partial.ROut T K)}
    (G : State sp → Prop) (Q : Partial.ROut T K → Prop) (σ τ : State sp)
    (h : (closeC G Q).app σ = some τ) :
    ∀ k u w, σ.R k u → ¬ τ.R k u → τ.R k w → ¬ (u ≼ w) :=
  (closeC G Q).excludes σ τ h

/-- "… for them a complete row is kept exactly when it satisfies the condition,
since two permitted complete outputs at one input, one refining the other, have
the same serial order and abort set." -/
theorem «app:cc-bases/complete-kept-iff» {T K : Type} {sp : Spec (FinSet T) (Partial.ROut T K)}
    {σ : State sp} {P : Outcome T → Prop} {k : FinSet T} {c : Partial.ROut T K}
    (hp : Partitions k c.o) :
    Keep σ (fun c => P c.o) k c ↔ σ.R k c ∧ P c.o :=
  keep_complete hp

/-- "The bases are `B_2PL = {order, commit, abort, read}` and
`B_MVTO = {stamp, commit, abort, read}`, ranging over all transactions, keys,
and versions." -/
theorem «app:cc-bases/bases» {T K : Type} {sp : Spec (FinSet T) (Partial.ROut T K)}
    (c : Commitment sp) :
    (basis2PL c ↔ (∃ A B, c = order A B) ∨ (∃ A, c = commit A) ∨ (∃ A, c = abort A) ∨
      (∃ A x v, c = read A x v)) ∧
    (basisMVTO c ↔ (∃ A Z, c = stamp A Z) ∨ (∃ A, c = commit A) ∨ (∃ A, c = abort A) ∨
      (∃ A x v, c = read A x v)) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- "… and differ in how they order: at the canonical state of three
transactions `{A,B,C}`, no commitment of `B_MVTO` has the effect of
`order(A,B)`, and no commitment of `B_2PL` has the effect of `stamp(B)` with
`Z = ∅`."  Both are defined there; for any reads and writes. -/
theorem «app:cc-bases/bases-differ» {T K : Type} {rd wr : T → K → Prop} {A B C : T}
    (h : Distinct3 A B C) :
    (∃ τ, (order A B).app (σABC (K := K) rd wr h) = some τ ∧
      ∀ c, basisMVTO c → c.app (σABC rd wr h) ≠ some τ) ∧
    (∃ τ, (stamp B (fun _ => False)).app (σABC (K := K) rd wr h) = some τ ∧
      ∀ c, basis2PL c → c.app (σABC rd wr h) ≠ some τ) :=
  let ⟨τ, hτ, _⟩ := order_at (K := K) (rd := rd) (wr := wr) h
  let ⟨τ', hτ', _⟩ := stamp_at (K := K) (rd := rd) (wr := wr) h
  ⟨⟨τ, hτ, order_not_MVTO h hτ⟩, ⟨τ', hτ', stamp_not_2PL h hτ'⟩⟩

/-- "In every state that a run under either basis reaches, each row has a
complete refinement in the table at the same input, and each output between two
rows of the table at one input is itself a row of the table."  (`Good`.) -/
theorem «app:cc-bases/run-states» {T K : Type} {rd wr : T → K → Prop} {af : Bool}
    {i : FinSet T} {es : List (SEvent (spec (K := K) rd wr af))} {τ : State (spec rd wr af)}
    (h : SysExec basis2PL (canon _ i) es τ ∨ SysExec basisMVTO (canon _ i) es τ) :
    (∀ k x, τ.R k x → ∃ c, τ.R k c ∧ Partitions k c.o ∧ x ≼ c) ∧
    (∀ k x y c, τ.R k x → τ.R k c → x ≼ y → y ≼ c → τ.R k y) :=
  let hg : Good τ := h.elim good_run.1 good_run.2
  ⟨hg.2, hg.1⟩

/-- "So a read is reported by applying `read(A,x,v)` and then emitting the
result, which is then exposable."  Precisely: after `read(A,x,v)`, adding the
result to a row that every remaining row refines gives a row, and emitting it is
exposable.  (At any state with the
two properties above.) -/
theorem «app:cc-bases/read-emit» {T K : Type} {rd wr : T → K → Prop} {af : Bool} {A : T}
    {x : K} {v : Option T} {σ σ' : State (spec rd wr af)} (hg : Good σ)
    (h : (read A x v).app σ = some σ') {u : Partial.ROut T K} {k : FinSet T} (hu : σ'.R k u)
    (hall : ∀ k w, σ'.R k w → u ≼ w) :
    σ'.R k (addRead u A x v) ∧ Exposable σ' (addRead u A x v) :=
  read_emit hg h hu hall

/-! ## 2PL -/

/-- "… the scheduler applies `order(A,B)`.  On complete rows without aborts it
keeps exactly those with `A` before `B` (Figure `fig:cc-commitments`(h))." -/
theorem «app:cc-bases/fig-h» {T K : Type} {sp : Spec (FinSet T) (Partial.ROut T K)} {A B : T}
    {σ τ : State sp} (h : (order A B).app σ = some τ) {k : FinSet T} {c : Partial.ROut T K}
    (hp : Partitions k c.o) (hX : ∀ t, ¬ c.o.X t) (hA : k.1 A) (hB : k.1 B) :
    τ.R k c ↔ σ.R k c ∧ c.o.lt A B :=
  fig_h h hp hX hA hB

/-- "At the canonical state of `{A,B,C}` it removes `[B,A,C]` and keeps both
`[A,B,C]` and `[C,A,B]`, so it is a choice, and it is not the choice `c_o` of
any output `o`." -/
theorem «app:cc-bases/order-at-ABC» {T K : Type} {rd wr : T → K → Prop} {A B C : T}
    (h : Distinct3 A B C) :
    ∃ τ, (order A B).app (σABC (K := K) rd wr h) = some τ ∧
      τ.R (tri A B C h) (full (mk [A, B, C] fun _ => False)) ∧
      τ.R (tri A B C h) (full (mk [C, A, B] fun _ => False)) ∧
      ¬ τ.R (tri A B C h) (full (mk [B, A, C] fun _ => False)) ∧
      ∀ o, (choiceC o).app (σABC rd wr h) ≠ some τ :=
  let ⟨τ, hτ, h1, h2, h3⟩ := order_at (K := K) (rd := rd) (wr := wr) h
  ⟨τ, hτ, h1, h2, h3, (neither_is_choice h).1 τ hτ⟩

/-- "A deadlock between `A` and `B` means that `order(A,B)` and later
`order(B,A)` have both been applied.  Then no remaining row, at any input,
commits both `A` and `B`, so every remaining complete row aborts one of them,
and resolving the deadlock means aborting one."
"Remaining" is: in any table contained in the one after `order(B,A)`. -/
theorem «app:cc-bases/deadlock» {T K : Type} {sp : Spec (FinSet T) (Partial.ROut T K)}
    {A B : T} {σ σ1 σ1' σ2 : State sp}
    (h1 : (order A B).app σ = some σ1) (hs : ∀ k u, σ1'.R k u → σ1.R k u)
    (h2 : (order B A).app σ1' = some σ2) {R : FinSet T → Partial.ROut T K → Prop}
    (hR : ∀ k u, R k u → σ2.R k u) :
    (∀ k w, R k w → ¬ (w.o.dom A ∧ w.o.dom B)) ∧
    (∀ k c, R k c → Partitions k c.o → k.1 A → k.1 B → c.o.X A ∨ c.o.X B) :=
  ⟨fun _ _ hw => deadlock h1 hs h2 hR hw,
   fun _ _ hc hp hA hB => deadlock_complete h1 hs h2 hR hc hp hA hB⟩

/-- "Once the scheduler applies `commit(A)`, every remaining complete row aborts
`B`, and `commit(B)` is never again defined." -/
theorem «app:cc-bases/deadlock-resolution» {T K : Type}
    {sp : Spec (FinSet T) (Partial.ROut T K)} {A B : T} {σ σ1 σ1' σ2 σ3 σ4 : State sp}
    (h1 : (order A B).app σ = some σ1) (hs : ∀ k u, σ1'.R k u → σ1.R k u)
    (h2 : (order B A).app σ1' = some σ2) (hs' : ∀ k u, σ3.R k u → σ2.R k u)
    (h3 : (commit A).app σ3 = some σ4) (τ : State sp) (hτ : ∀ k u, τ.R k u → σ4.R k u) :
    (∀ k c, τ.R k c → Partitions k c.o → c.o.X B) ∧ (commit B).app τ = none :=
  deadlock_commit h1 hs h2 hs' h3 τ hτ

/-- "Under the abort-free specification, once `order(A,B)` is applied,
`order(B,A)` is undefined at every later state: `A`, and hence `B`, waits
forever."  Stated for every state with a smaller table, and for every state a
later execution (under any basis) reaches. -/
theorem «app:cc-bases/abort-free-waits-forever» {T K : Type} {rd wr : T → K → Prop} {A B : T}
    {σ σ1 : State (spec (K := K) rd wr true)} (h : (order A B).app σ = some σ1) :
    (∀ τ : State (spec rd wr true), (∀ k u, τ.R k u → σ1.R k u) →
      (order B A).app τ = none) ∧
    ∀ (Bs : Basis (spec rd wr true)) es τ, SysExec Bs σ1 es τ → (order B A).app τ = none :=
  ⟨abortFree_blocks h, fun Bs _ _ hx => abortFree_blocks_forever h Bs hx⟩

/-! ## MVTO -/

/-- "On complete rows without aborts, `stamp(B)` with `Z = ∅` keeps exactly
those with `B` first (Figure `fig:cc-commitments`(i))." -/
theorem «app:cc-bases/fig-i» {T K : Type} {sp : Spec (FinSet T) (Partial.ROut T K)} {B : T}
    {σ τ : State sp} (h : (stamp B (fun _ => False)).app σ = some τ) {k : FinSet T}
    {c : Partial.ROut T K} (hp : Partitions k c.o) (hX : ∀ t, ¬ c.o.X t) (hB : k.1 B) :
    τ.R k c ↔ σ.R k c ∧ ∀ D, k.1 D → D ≠ B → c.o.lt B D :=
  fig_i h hp hX hB

/-- "… at the canonical state of `{A,B,C}` it is a choice, and it is not the
choice `c_o` of any output": it keeps `[B,A,C]` and `[B,C,A]` and removes
`[A,B,C]` and `[C,B,A]`. -/
theorem «app:cc-bases/stamp-at-ABC» {T K : Type} {rd wr : T → K → Prop} {A B C : T}
    (h : Distinct3 A B C) :
    ∃ τ, (stamp B (fun _ => False)).app (σABC (K := K) rd wr h) = some τ ∧
      τ.R (tri A B C h) (full (mk [B, A, C] fun _ => False)) ∧
      τ.R (tri A B C h) (full (mk [B, C, A] fun _ => False)) ∧
      ¬ τ.R (tri A B C h) (full (mk [A, B, C] fun _ => False)) ∧
      ¬ τ.R (tri A B C h) (full (mk [C, B, A] fun _ => False)) ∧
      ∀ o, (choiceC o).app (σABC rd wr h) ≠ some τ :=
  let ⟨τ, hτ, h1, h2, h3, h4⟩ := stamp_at (K := K) (rd := rd) (wr := wr) h
  ⟨τ, hτ, h1, h2, h3, h4, (neither_is_choice h).2 τ hτ⟩

/-- *What a read commits to*, the row argument: "A complete row that satisfies
both stamps and commits both `A` and `B` places `A` between that version and
`B`, so it does not permit the read."  `Z_B ∋ A` is "`B` stamped after `A`"; the version is the
initial one or written by `W ∈ Z_A`, `W ≠ A`. -/
theorem «app:cc-bases/mvto-row» {T K : Type} {rd wr : T → K → Prop} {k : FinSet T}
    {c : Partial.ROut T K} (hc : Complete rd wr k c) {A B : T} {ZA ZB : T → Prop} {x : K}
    {v : Option T} (hsA : StampOK A ZA c.o) (hsB : StampOK B ZB c.o) (hAB : ZB A)
    (hBB : ¬ ZB B) (hwA : wr A x) (hv : ∀ W, v = some W → ZA W ∧ W ≠ A)
    (hρ : c.ρ B x = some v) : ¬ (c.o.dom A ∧ c.o.dom B) :=
  fun ⟨hA, hB⟩ => stamps_row hc hsA hsB hAB hBB hwA hv hρ hA hB

/-- "Hence, after the two stamps, no row reporting the read commits both `A`
and `B`, and once `read` has been applied, no remaining row commits both,
whether it reports the read or not.  Reporting the read commits to this: `A`
and `B` do not both commit."  The two stamps are
`TwoStamps A B Z_A Z_B σ σ2` (`stamp(A)`, anything, `stamp(B)` with `A ∈ Z_B`);
"remaining" is: in any table contained in the one after the stamps (resp.
after `read(B,x,v)`). -/
theorem «app:cc-bases/read-commits» {T K : Type} {rd wr : T → K → Prop} {af : Bool}
    {A B : T} {ZA ZB : T → Prop} {σ σ2 : State (spec (K := K) rd wr af)}
    (H : TwoStamps A B ZA ZB σ σ2) {x : K} {v : Option T} (hwA : wr A x)
    (hv : ∀ W, v = some W → ZA W) :
    (∀ (R : FinSet T → Partial.ROut T K → Prop), (∀ k u, R k u → σ2.R k u) →
      ∀ k w, R k w → w.ρ B x = some v → ¬ (w.o.dom A ∧ w.o.dom B)) ∧
    (∀ σ3 σ4 : State (spec rd wr af), (∀ k u, σ3.R k u → σ2.R k u) →
      (read B x v).app σ3 = some σ4 →
      ∀ (R : FinSet T → Partial.ROut T K → Prop), (∀ k u, R k u → σ4.R k u) →
      ∀ k w, R k w → ¬ (w.o.dom A ∧ w.o.dom B)) :=
  ⟨fun _ hR _ _ hw hρ => H.no_both hwA hv hR hw hρ,
   fun _ _ hs3 h _ hR _ _ hw => H.read_no_both hwA hv hs3 h hR hw⟩

/-- "The condition on the version is needed.  At input `{A,W,B}`, stamped in
that order, with `A` and `W` writing `x`, the complete row that commits all
three in stamp order and reports that `B` read `W`'s write is permitted and
satisfies every stamp." -/
theorem «app:cc-bases/writer-before-A» {T K : Type} {rd wr : T → K → Prop} {A W B : T}
    (h : Distinct3 A W B) {x : K} (hwA : wr A x) (hwW : wr W x) (hrB : rd B x) :
    let r : Partial.ROut T K := ⟨mk [A, W, B] fun _ => False, single B x (some W)⟩
    Complete rd wr (tri A W B h) r ∧ StampOK A (fun _ => False) r.o ∧
      StampOK W (· = A) r.o ∧ StampOK B (fun z => z = A ∨ z = W) r.o ∧
      wr A x ∧ r.ρ B x = some (some W) ∧ r.o.dom A :=
  writer_after_A h hwA hwW hrB

/-- *When the abort is entailed.*  "If every remaining complete row commits
`B`, for instance after `commit(B)`, then every remaining complete row aborts
`A`.  Emitting `A`'s abort, added to a row that reports the read and that every
remaining row refines, is then exposable: the specification entails the abort."
(Lean also shows that no remaining row commits `A`.)  Stated at any state `τ` with the two
properties of `«app:cc-bases/run-states»` whose table is contained in the one
after the two stamps. -/
theorem «app:cc-bases/abort-entailed» {T K : Type} {rd wr : T → K → Prop} {af : Bool}
    {A B : T} {ZA ZB : T → Prop} {σ σ2 : State (spec (K := K) rd wr af)}
    (H : TwoStamps A B ZA ZB σ σ2) {x : K} {v : Option T} (hwA : wr A x)
    (hv : ∀ W, v = some W → ZA W) {τ : State (spec rd wr af)}
    (hτ : ∀ k u, τ.R k u → σ2.R k u) (hg : Good τ) {u : Partial.ROut T K}
    (hall : ∀ k w, τ.R k w → u ≼ w) (hρ : u.ρ B x = some v)
    (hB : ∀ k c, τ.R k c → Partitions k c.o → c.o.dom B) :
    (∀ k w, τ.R k w → ¬ w.o.dom A) ∧
    (∀ k c, τ.R k c → Partitions k c.o → c.o.X A) ∧
    (τ.R τ.cur u → τ.R τ.cur (addAbort u A) ∧ Exposable τ (addAbort u A)) :=
  H.abort_entailed hwA hv hτ hg hall hρ hB

/-- "While `B` is undecided, it does not.  At input `{A,B}`, with `A` writing
`x`, `B` reading it, and further transactions free to arrive, apply `stamp(A)` and `stamp(B)`, and report that `B`
read the initial version of `x`.  Reporting the read is not exposable on its
own, since the row that commits `A` and then `B` cannot be completed with it;
the output event that applies `read` and then reports the read is legal under
`B_MVTO`.  Two completions remain: `B` committed with `A` aborted, and `A`
committed with `B` aborted.  Emitting `A`'s abort is not exposable, and
`abort(A)` and `abort(B)` are both defined and keep different completions.
After `commit(B)`, `A`'s abort becomes exposable."  (`C` is the further transaction: `stamp(B)` is defined because `C` may
still arrive and be ordered before `B`; `Ex.u B x` is the output reporting the read,
`Ex.r1`/`Ex.r2` the two completions.) -/
theorem «app:cc-bases/abort-is-a-choice» {T K : Type} {rd wr : T → K → Prop} {A B C : T}
    (h : Distinct3 A B C) {x : K} (hwA : wr A x) (hrB : rd B x) :
    ∃ σ1 σ2 σ3 τ : State (spec (K := K) rd wr false),
      (stamp A (fun _ => False)).app (canon _ (pairSet A B h.ab)) = some σ1 ∧
      (stamp B (· = A)).app σ1 = some σ2 ∧
      σ2.R (pairSet A B h.ab) (Ex.rAB A B) ∧ ¬ Exposable σ2 (Ex.u B x) ∧
      (read B x none).app σ2 = some σ3 ∧ ¬ σ3.R (pairSet A B h.ab) (Ex.rAB A B) ∧
      SysStep basisMVTO σ2 (.output [read B x none] (Ex.u B x)) τ ∧
      τ.R (pairSet A B h.ab) (Ex.r1 A B x) ∧ τ.R (pairSet A B h.ab) (Ex.r2 A B x) ∧
      ¬ Exposable τ (addAbort (Ex.u B x) A) ∧
      (∃ τA, (abort A).app τ = some τA ∧
        τA.R (pairSet A B h.ab) (Ex.r1 A B x) ∧ ¬ τA.R (pairSet A B h.ab) (Ex.r2 A B x)) ∧
      (∃ τB, (abort B).app τ = some τB ∧
        τB.R (pairSet A B h.ab) (Ex.r2 A B x) ∧ ¬ τB.R (pairSet A B h.ab) (Ex.r1 A B x)) ∧
      (∃ τC, (commit B).app τ = some τC ∧
        τC.R (pairSet A B h.ab) (addAbort (Ex.u B x) A) ∧
        Exposable τC (addAbort (Ex.u B x) A)) :=
  Ex.mvto_instance h hwA hrB

/-! ## Comparison -/

/-- "Under MVTO, a later transaction's read of an older version commits that
the writer and the reader do not both commit, and the write rule settles this
at once by aborting the writer; the specification forces that abort only after
the reader commits."  The first part is `«app:cc-bases/read-commits»`; the
second is `«app:cc-bases/abort-entailed»` together with the instance
`«app:cc-bases/abort-is-a-choice»`, restated here: after the read is reported,
`A`'s abort is not exposable while `B` is undecided, and is exposable once
`commit(B)` has been applied. -/
theorem «app:cc-bases/comparison» {T K : Type} {rd wr : T → K → Prop} {A B C : T}
    (h : Distinct3 A B C) {x : K} (hwA : wr A x) (hrB : rd B x) :
    ∃ τ : State (spec (K := K) rd wr false),
      ¬ Exposable τ (addAbort (Ex.u B x) A) ∧
      ∃ τC, (commit B).app τ = some τC ∧ Exposable τC (addAbort (Ex.u B x) A) :=
  let ⟨_, _, _, τ, _, _, _, _, _, _, _, _, _, hne, _, _, ⟨τC, hC, _, hex⟩⟩ :=
    Ex.mvto_instance (rd := rd) h hwA hrB
  ⟨τ, hne, τC, hC, hex⟩

end Paper
end CC
