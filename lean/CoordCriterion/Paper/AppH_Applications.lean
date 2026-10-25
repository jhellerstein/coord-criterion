import CoordCriterion.Appendix.Applications

/-!
# Paper, Appendix H: Additional applications (`app:additional-applications`)

Source: `appendices/additional-applications.tex` (the whole appendix: committed
authority, `k`-set agreement, tight renaming, snapshots).

How to read this file: one `/-! ## … -/` section per subsection of the
appendix, in paper order.  Labeled equations are named by their label
(`«eq:authority-refinement»`, `«eq:tight-renaming»`); every other claim is
named `«app:additional-applications/<slug>»`.  Each docstring quotes the claim;
statements are written out in terms of library definitions of
`Appendix/Applications.lean` (namespace `CC.Apps`), and proofs point there.

Common modeling choices (see `Appendix/Applications.lean`): output types
contain all partial maps / sets, and "no common refinement" is proved in the
whole output type (stronger than among permitted outputs); "not monotone" is
`¬ LiftedMono`; "the negative side of Complete CAP" is
`¬ ∃ Sys, CAP.Availability Sys ∧ CAP.PartitionConsistency Sys`, obtained from
`CC.CAP.complete_cap`, whose proof builds the partition separating the rows'
inputs.  The App. B version of `k`-set agreement (pairs suffice, with inputs
and outputs both partial maps on `Fin (k+1)`) is `CC.CALM.KSet` in
`CALM/Examples.lean`; this file uses the general version of App. H.
-/

namespace CC
namespace Paper

open CC.Txn CC.Apps

/-! ## Committed authority, then monotone evidence -/

/-- "An output is a triple `(E,V,D)`: a certified epoch chain `E`, a finite
sequence of epochs …; a set `V` of votes or certificates; and a set `D` of
decisions."  Certification is not modeled: `Auth Ep Vt Dc` contains every
triple; the protocol's specification decides which are permitted. -/
abbrev «app:additional-applications/authority-output» (Ep Vt Dc : Type) := Auth Ep Vt Dc

/-- Eq. `authority-refinement`:
"`(E,V,D) ⪯ (E',V',D') ⟺ E ⪯_pref E', V ⊆ V', D ⊆ D'`", where `E ⪯_pref E'`
means that `E` is a prefix of `E'`. -/
theorem «eq:authority-refinement» {Ep Vt Dc : Type} (a b : Auth Ep Vt Dc) :
    a ≼ b ↔ (∃ t, b.E = a.E ++ t) ∧ (∀ v, a.V v → b.V v) ∧ (∀ d, a.D d → b.D d) :=
  Iff.rfl

/-- "Protocol safety guarantees that every output permitted at the current or
any later input [refines] the certified evidence already emitted, so authority
changes and certified decisions are [exposable] and need no further
commitment."  Safety is the hypothesis that every remaining row refines `o`;
the conclusion is that `o` is exposable and the commitment-free output event
`Out_ε(o)` is legal (under any basis).  Generic in the specification. -/
theorem «app:additional-applications/safety-exposable» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} {σ : State sp} {o : O} (ho : σ.R σ.cur o)
    (hsafe : ∀ k x, σ.R k x → o ≼ x) (B : Basis sp) :
    Exposable σ o ∧ SysStep B σ (.output [] o) (outState σ o ho) :=
  safety_exposable ho hsafe B

/-- "Competing proposals for an undecided slot have incompatible extensions of
`D`, so certifying one is a commitment."  Two current outputs deciding
different values `d ≠ d'` for the same epoch and slot (`slot d = slot d'`), in
a specification whose permitted outputs decide at most one value per epoch and
slot (`SlotUnique`, the paper's "at most one value per epoch and slot"):
emitting one rejects the other, is not exposable, and every legal output event
emitting it applies a commitment (`γ ≠ []`). -/
theorem «app:additional-applications/slot-conflict» {I Ep Vt Dc κ : Type} [PO I]
    (slot : Dc → κ) {sp : Spec I (Auth Ep Vt Dc)}
    (hU : ∀ k u, sp.S k u → SlotUnique slot u.D)
    {σ : State sp} {o o' : Auth Ep Vt Dc} (ho : σ.R σ.cur o) (ho' : σ.R σ.cur o')
    {d d' : Dc} (hd : o.D d) (hd' : o'.D d') (hs : slot d = slot d') (hne : d ≠ d') :
    Rejected σ o σ.cur o' ∧ ¬ Exposable σ o ∧
      ∀ (B : Basis sp) γ τ, SysStep B σ (.output γ o) τ → γ ≠ [] :=
  slot_conflict slot hU ho ho' hd hd' hs hne

/-- "If the succession rule were not fixed, competing next epochs would require
one [a commitment] as well."  Two current outputs extending the chain `e` by
different next epochs `a ≠ b`. -/
theorem «app:additional-applications/epoch-conflict» {I Ep Vt Dc : Type} [PO I]
    {sp : Spec I (Auth Ep Vt Dc)} {σ : State sp}
    {o o' : Auth Ep Vt Dc} (ho : σ.R σ.cur o) (ho' : σ.R σ.cur o') {e : List Ep} {a b : Ep}
    (he : o.E = e ++ [a]) (he' : o'.E = e ++ [b]) (hne : a ≠ b) :
    Rejected σ o σ.cur o' ∧ ¬ Exposable σ o ∧
      ∀ (B : Basis sp) γ τ, SysStep B σ (.output γ o) τ → γ ≠ [] :=
  epoch_conflict ho ho' he he' hne

/-! ## `k`-set agreement: no `k`-wise test suffices -/

/-- "An input is a finite set of proposals `(p,v)`, at most one per
participant, ordered by inclusion." -/
abbrev «app:additional-applications/kset-input» (P Val : Type) := KInput P Val

/-- "Outputs are partial decision maps `m : P ⇀ Val` ordered by extension." -/
theorem «app:additional-applications/pmap-order» {P Val : Type} (m m' : PMap P Val) :
    m ≼ m' ↔ ∀ p a, m.f p = some a → m'.f p = some a := Iff.rfl

/-- "At input `I`, `m` is permitted when it decides only participants that
propose in `I`, every value in its range is proposed in `I` (validity), and its
range has at most `k` values."  (The range is covered by a list of length
`≤ k`.) -/
theorem «app:additional-applications/kset-permitted» {P Val : Type} (k : Nat)
    (I : KInput P Val) (m : PMap P Val) :
    (ksetSpec P Val k).S I m ↔
      (∀ p a, m.f p = some a → ∃ b, I.1.1 (p, b)) ∧
      (∀ p a, m.f p = some a → ∃ q, I.1.1 (q, a)) ∧
      ∃ l : List Val, l.length ≤ k ∧ ∀ p a, m.f p = some a → a ∈ l :=
  Iff.rfl

/-- "At `p_r`'s proposal input, `{p_r ↦ v_r}` is permitted" (`k ≥ 1`).
Participants and values are indexed by `r : Fin (k+1)`. -/
theorem «app:additional-applications/kset-proposal-row» {P Val : Type} [DecidableEq P]
    {k : Nat} {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val} (hk : 1 ≤ k) (r : Fin (k + 1)) :
    (ksetSpec P Val k).S (propIn p v r) (single p v r) :=
  kset_single_row hk r

/-- "… and the union of the proposal inputs is a common [expansion]" (an input
because the `p_r` are distinct). -/
theorem «app:additional-applications/kset-union» {P Val : Type} [DecidableEq P] {k : Nat}
    {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val} (hp : ∀ r r', p r = p r' → r = r')
    (r : Fin (k + 1)) :
    propIn p v r ≼ unionIn p v hp :=
  kset_union_upper hp r

/-- "Any `k` of these `k+1` rows have a common [refinement] there": for each
omitted index `r₀`, a permitted output at the union refines every
`{p_r ↦ v_r}`, `r ≠ r₀`. -/
theorem «app:additional-applications/kset-any-k» {P Val : Type} [DecidableEq P] {k : Nat}
    {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val} (hp : ∀ r r', p r = p r' → r = r')
    (r0 : Fin (k + 1)) :
    ∃ u, (ksetSpec P Val k).S (unionIn p v hp) u ∧ ∀ r, r ≠ r0 → single p v r ≼ u :=
  kset_any_k hp r0

/-- "… all `k+1` do not, since it would have `k+1` values." -/
theorem «app:additional-applications/kset-all-fail» {P Val : Type} [DecidableEq P] {k : Nat}
    {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val} (hp : ∀ r r', p r = p r' → r = r')
    (hv : ∀ r r', v r = v r' → r = r') :
    ¬ ∃ u, (ksetSpec P Val k).S (unionIn p v hp) u ∧ ∀ r, single p v r ≼ u :=
  kset_all_fail hp hv

/-- "So the common-[expansion] condition fails and the specification is not
monotone (Proposition `prop:common-expansion-form`); a partition separating the
`p_r` gives the negative side of Complete CAP." -/
theorem «app:additional-applications/kset-not-monotone» {P Val : Type} [DecidableEq P]
    {k : Nat} {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val}
    (hp : ∀ r r', p r = p r' → r = r') (hv : ∀ r r', v r = v r' → r = r') (hk : 1 ≤ k)
    (D : Type) :
    ¬ (ksetSpec P Val k).CommonExpansion ∧ ¬ (ksetSpec P Val k).LiftedMono ∧
      ¬ ∃ Sys : CAP.System (ksetSpec P Val k) D,
        CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  ⟨kset_not_commonExpansion hp hv hk, kset_not_liftedMono hp hv hk, kset_no_cap hp hv hk D⟩

/-- "Consensus is `k = 1`": two distinct participants proposing distinct
values. -/
theorem «app:additional-applications/consensus» {P Val : Type} [DecidableEq P]
    {p : Fin 2 → P} {v : Fin 2 → Val}
    (hp : ∀ r r', p r = p r' → r = r') (hv : ∀ r r', v r = v r' → r = r') (D : Type) :
    ¬ (ksetSpec P Val 1).LiftedMono ∧
      ¬ ∃ Sys : CAP.System (ksetSpec P Val 1) D,
        CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  ⟨kset_not_liftedMono hp hv (Nat.le_refl 1), kset_no_cap hp hv (Nat.le_refl 1) D⟩

/-! ## Tight renaming -/

/-- Eq. `tight-renaming`: "the outputs at `N` are the injective maps
`m : N → {1,…,|N|}`" (total on `N`, undefined outside `N`; `card N` is `|N|`). -/
theorem «eq:tight-renaming» {P : Type} [DecidableEq P] (N : FinSet P) (m : PMap P Nat) :
    (renSpec P).S N m ↔
      (∀ x, N.1 x ↔ ∃ n, m.f x = some n) ∧
      (∀ x y n, m.f x = some n → m.f y = some n → x = y) ∧
      ∀ x n, m.f x = some n → 1 ≤ n ∧ n ≤ card N :=
  Iff.rfl

/-- "At `{p}` the only output is `p ↦ 1`, and at `{q}` it is `q ↦ 1`." -/
theorem «app:additional-applications/renaming-singletons» {P : Type} [DecidableEq P]
    (p q : P) (m : PMap P Nat) :
    ((renSpec P).S (sing p) m ↔ m = name1 p) ∧ ((renSpec P).S (sing q) m ↔ m = name1 q) :=
  ⟨ren_singleton_iff p m, ren_singleton_iff q m⟩

/-- "Each has a [refinement] at `{p,q}`, so Relational Monotonicity does not
fail here, but no injective map extends both." -/
theorem «app:additional-applications/renaming-each-extends» {P : Type} [DecidableEq P]
    {p q : P} (h : p ≠ q) :
    (∃ u, (renSpec P).S (pairSet p q h) u ∧ name1 p ≼ u) ∧
    (∃ u, (renSpec P).S (pairSet p q h) u ∧ name1 q ≼ u) ∧
    ¬ ∃ u : PMap P Nat, Injective u ∧ name1 p ≼ u ∧ name1 q ≼ u :=
  ⟨(ren_each_extends h).1, (ren_each_extends h).2, ren_no_injective_extends_both h⟩

/-- "Directed Outputs also fails at `{p,q}`: `{p↦1,q↦2}` and `{p↦2,q↦1}` have
no common [refinement].  The specification therefore fails Lifted Monotonicity,
and by Theorem `thm:complete-cap` a partition separating `p` and `q` rules out
Availability with Partition Consistency." -/
theorem «app:additional-applications/renaming-not-monotone» {P : Type} [DecidableEq P]
    {p q : P} (h : p ≠ q) (D : Type) :
    (¬ ∃ u, name2 p q 1 2 ≼ u ∧ name2 p q 2 1 ≼ u) ∧
    ¬ (renSpec P).DirectedOutputs ∧ ¬ (renSpec P).LiftedMono ∧
    ¬ ∃ Sys : CAP.System (renSpec P) D, CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  ⟨(ren_not_directed h).1, (ren_not_directed h).2.1, (ren_not_directed h).2.2,
    ren_no_cap h D⟩

/-! ## Snapshots -/

/-- "Inputs are finite causal histories, that is, finite sets of events with a
causal partial order; `h ⊑ h'` when `h` is a downward-closed subset of `h'`
carrying the restricted order." -/
theorem «app:additional-applications/history-order» {Ev : Type} (h h' : Hist Ev) :
    h ≼ h' ↔
      (∀ x, h.s.1 x → h'.s.1 x) ∧ (∀ a b, h.s.1 b → h'.lt a b → h.s.1 a) ∧
      ∀ a b, h.s.1 a → h.s.1 b → (h.lt a b ↔ h'.lt a b) :=
  Iff.rfl

/-- "The *prefix* specification permits at `h` any downward-closed subset of
`h`, with outputs ordered by inclusion." -/
theorem «app:additional-applications/prefix-spec» {Ev : Type} (h : Hist Ev) (p : ESet Ev) :
    (prefixSpec Ev).S h p ↔ (∀ x, p.mem x → h.s.1 x) ∧ ∀ a b, p.mem b → h.lt a b → p.mem a :=
  Iff.rfl

/-- "Old prefixes stay legal as history grows, and finite unions of prefixes are
prefixes, so it satisfies Lifted Monotonicity." -/
theorem «app:additional-applications/prefix-monotone» {Ev : Type} :
    (∀ {h h' : Hist Ev} (p : ESet Ev), h ≼ h' → (prefixSpec Ev).S h p → (prefixSpec Ev).S h' p) ∧
    (∀ (j : Hist Ev) (ps : List (ESet Ev)), (∀ p ∈ ps, (prefixSpec Ev).S j p) →
      (prefixSpec Ev).S j ⟨fun x => ∃ p ∈ ps, p.mem x⟩) ∧
    (prefixSpec Ev).LiftedMono :=
  ⟨fun _ hle hp => prefix_mono hle hp, fun _ ps hps => prefix_union ps hps,
    prefixSpec_liftedMono⟩

/-- "… it guarantees neither freshness nor completeness": the empty prefix is
permitted at every history. -/
theorem «app:additional-applications/prefix-empty» {Ev : Type} (h : Hist Ev) :
    (prefixSpec Ev).S h ⟨fun _ => False⟩ :=
  prefix_empty h

/-- "A specification that requires the complete history, with output `h` at `h`
and outputs ordered by equality, is functional and not monotone: its required
output changes whenever an event arrives."  (Not monotone as soon as there is an
event `e`: `∅ ⊑ {e}`.) -/
theorem «app:additional-applications/complete-history» {Ev : Type} (e : Ev) :
    (∀ h o, (completeSpec Ev).S h o ↔ o = ⟨h⟩) ∧
    (completeSpec Ev).Functional ∧ ¬ (completeSpec Ev).MonotoneF ∧
      ¬ (completeSpec Ev).LiftedMono :=
  ⟨fun _ _ => Iff.rfl, completeSpec_functional, completeSpec_not_monotone e⟩

/-- "By Proposition `prop:functional-exposure-boundary`, some output can then be
exposed only after a commitment that seals larger inputs."  At some state
reachable without commitment, some current output rules out a sealed row and no
rejected row, and every legal output event emitting it applies a commitment. -/
theorem «app:additional-applications/complete-history-seal» {Ev : Type} (e : Ev) :
    ∃ (τ : State (completeSpec Ev)) (o : Eqd (Hist Ev)), ReachableCF τ ∧ τ.R τ.cur o ∧
      (∃ k x, Sealed τ o k x) ∧ (∀ k x, ¬ Rejected τ o k x) ∧
      ∀ (B : Basis (completeSpec Ev)) γ τ', SysStep B τ (.output γ o) τ' → γ ≠ [] :=
  completeSpec_seal_needed e

end Paper
end CC
