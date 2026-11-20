import CoordCriterion.Appendix.Classical

/-!
# Paper, Appendix G: Classical problems in distributed computing (`app:additional-applications`)

Source: `appendices/classical-problems.tex` (the whole appendix: three
patterns and the table of classical problems; consensus; `k`-set agreement;
renaming; snapshots; a causal FIFO queue).

How to read this file: one `/-! ## … -/` section per subsection of the
appendix, in paper order.  Lemmas, propositions, the table, and labeled
equations are named by their label (`«lem:accumulating»`,
`«prop:causal-fifo»`, `«tab:classical-problems/…»`, `«eq:tight-renaming»`);
every other claim is named `«app:additional-applications/<slug>»`.  Each
docstring quotes the claim; statements are written out in terms of library
definitions of `Appendix/Applications.lean` and `Appendix/Classical.lean`
(namespace `CC.Apps`), and proofs point there.

Common modeling choices: output types contain all partial maps / sets, and
"no common output extension" is proved in the whole output type when that is
stronger; "not monotone" is `¬ LiftedMono`; "the negative side of Complete
CAP" (Theorem `thm:complete-cap` with `E = P` and Corollary
`cor:complete-cap-any-system`) is
`¬ ∃ Sys, CAP.Availability Sys ∧ CAP.PartitionConsistency Sys`, obtained from
`CC.CAP.complete_cap`, whose proof builds the partition separating the rows'
inputs.  Classical results the appendix cites (Fischer–Lynch–Paterson,
wait-free impossibility of `k`-set agreement, the renaming hierarchy, the
equivalence of total-order broadcast and consensus, wait-free atomic
snapshots, liveness of reliable broadcast) are not proved here; the
docstrings that mention them say so.
-/

namespace CC
namespace Paper

open CC.Txn CC.Apps

/-! ## Three patterns -/

/-- **Lemma `lem:accumulating`** (Accumulating outputs).  "Suppose the outputs
of an I/O specification are sets of facts ordered by inclusion.  If every
output permitted at an input is still permitted at each input extension of
that input, and the union of two outputs permitted at one input is permitted
there, then the spec is monotone."  Proof: "Take `i ⊑ j` and a nonempty finite
`X ⊆ P(i)`.  Each member of `X` is permitted at `j`, so by induction on the
size of `X` their union is permitted at `j`, and it extends every member of
`X`."  Sets of facts are `ESet F`. -/
theorem «lem:accumulating» {I F : Type} [PO I] {sp : Spec I (ESet F)}
    (hgrow : ∀ i j o, i ≼ j → sp.P i o → sp.P j o)
    (hunion : ∀ j a b, sp.P j a → sp.P j b → sp.P j (ESet.union a b)) : sp.LiftedMono :=
  accumulating_monotone hgrow hunion

/-- "The proof uses only that each fiber contains, with any two outputs, a
common output extension of both.  The lemma therefore holds for any output
order and any binary operation with that property, such as the maximum of two
counter values under `≤`."  Lean assumes Relational Monotonicity in place of
"still permitted at each input extension", which is weaker; the counter case
is `«tab:classical-problems/counter»`. -/
theorem «app:additional-applications/accumulating-join» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} (join : O → O → O) (hl : ∀ a b, a ≼ join a b) (hr : ∀ a b, b ≼ join a b)
    (hc : ∀ j a b, sp.P j a → sp.P j b → sp.P j (join a b)) (hR : sp.RelMono) :
    sp.LiftedMono :=
  liftedMono_of_join join hl hr hc hR

/-- **Lemma `lem:order-commitment`** (Ordering concurrent events).  "Suppose
that each output `o` of an I/O specification determines, for each pair of
events `a` and `b`, whether `o` places `a` before `b`; that if `o ⪯ u` and `o`
places `a` before `b`, so does `u`; and that no output permitted at an input
`j` places two events in both orders.  If rows `(i₁,o₁)` and `(i₂,o₂)` have `j`
as a common input extension, `o₁` places `a` before `b`, and `o₂` places `b`
before `a`, then the spec is not monotone.  If `i₁ = i₂ = j`, the fiber at `j`
is not directed."  Proof: "A common output extension of `o₁` and `o₂` in
`P(j)` would place `a` before `b` and `b` before `a`.  So the common-extension
condition fails, and by Proposition `prop:common-expansion-form` so does Lifted
Monotonicity.  When `i₁ = i₂ = j`, the same argument shows that `o₁` and `o₂`
are incompatible in `P(j)`." -/
theorem «lem:order-commitment» {I O E : Type} [PO I] [PO O] {sp : Spec I O}
    (before : O → E → E → Prop) (hmono : ∀ o u a b, o ≼ u → before o a b → before u a b)
    {j : I} (hasym : ∀ u a b, sp.P j u → before u a b → ¬ before u b a)
    {i1 i2 : I} {o1 o2 : O} {a b : E} (h1 : sp.P i1 o1) (h2 : sp.P i2 o2)
    (hj1 : i1 ≼ j) (hj2 : i2 ≼ j) (hb1 : before o1 a b) (hb2 : before o2 b a) :
    (¬ ∃ u, sp.P j u ∧ o1 ≼ u ∧ o2 ≼ u) ∧ ¬ sp.CommonExpansion ∧ ¬ sp.LiftedMono ∧
      (i1 = j → i2 = j → ¬ sp.DirectedOutputs) :=
  ⟨order_no_common before hmono hasym hb1 hb2,
   (order_conflict before hmono hasym h1 h2 hj1 hj2 hb1 hb2).1,
   (order_conflict before hmono hasym h1 h2 hj1 hj2 hb1 hb2).2,
   fun e1 e2 => by
     subst e1; subst e2
     exact (order_conflict_fiber before hmono hasym h1 h2 hb1 hb2).1⟩

/-- **Lemma `lem:bounded-values`** (Bounded number of values).  "Suppose that
each output `o` of an I/O specification determines a set of values that `o`
decides; that if `o ⪯ u`, then `u` decides every value that `o` decides; and
that every output permitted at an input `j` decides at most `k` values.  If
`k+1` rows have `j` as a common input extension and decide `k+1` distinct
values, one per row, then the spec is not monotone."  Proof: "A common output
extension of the `k+1` outputs in `P(j)` would decide all `k+1` values.  So the
common-extension condition fails, and Proposition `prop:common-expansion-form`
applies."  "At most `k` values": covered by a list of length `≤ k`. -/
theorem «lem:bounded-values» {I O V : Type} [PO I] [PO O] {sp : Spec I O}
    (dec : O → V → Prop) (hmono : ∀ o u v, o ≼ u → dec o v → dec u v) {k : Nat} {j : I}
    (hbound : ∀ u, sp.P j u → ∃ l : List V, l.length ≤ k ∧ ∀ v, dec u v → v ∈ l)
    (i : Fin (k + 1) → I) (o : Fin (k + 1) → O) (v : Fin (k + 1) → V)
    (hv : ∀ r r', v r = v r' → r = r') (hrow : ∀ r, sp.P (i r) (o r)) (hj : ∀ r, i r ≼ j)
    (hd : ∀ r, dec (o r) (v r)) :
    (¬ ∃ u, sp.P j u ∧ ∀ r, o r ≼ u) ∧ ¬ sp.CommonExpansion ∧ ¬ sp.LiftedMono :=
  ⟨bounded_no_common dec hmono hbound o v hv hd,
   bounded_values dec hmono hbound i o v hv hrow hj hd⟩

/-- "When Lemma `lem:order-commitment` or Lemma `lem:bounded-values` applies,
Complete CALM (Theorem `thm:complete-calm`) says that the runs of the spec are
not consistent.  The No-commitment test (Proposition `prop:exposure-boundary`)
adds that some output, at some state reachable without commitment, is not
legal, so emitting it applies a commitment.  With `E = P`, Theorem
`thm:complete-cap` and Corollary `cor:complete-cap-any-system` add that no
system for the spec has Availability for `P` and Partition Consistency.  …
When Lemma `lem:accumulating` applies, the runs are consistent, and the
canonical system for `P` needs no commitment and escapes CAP for `P`."
First conjunct: from `¬ LiftedMono` (the conclusion of both lemmas); second:
from `LiftedMono`, with the canonical system the commitment-free system
`CAP.cfSystem`. -/
theorem «app:additional-applications/pattern-consequences» {I O : Type} [PO I] [PO O]
    (sp : Spec I O) (D : Type) :
    (¬ sp.LiftedMono →
      ¬ sp.Consistent ∧
      (∃ τ : State sp, ReachableCF τ ∧ ∃ o, τ.R τ.cur o ∧ ¬ Exposable τ o ∧
        ∀ (B : CommitmentBasis sp) τ', SysStep B τ (.output o) τ' → B (canonicalCommitment o)) ∧
      ¬ ∃ Sys : CAP.System sp D, CAP.Availability Sys ∧ CAP.PartitionConsistency Sys) ∧
    (sp.LiftedMono →
      sp.Consistent ∧ (∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o) ∧
      CAP.Availability (CAP.cfSystem sp D) ∧ CAP.PartitionConsistency (CAP.cfSystem sp D)) :=
  ⟨fun h => pattern_consequences_neg h D, fun h => pattern_consequences_pos h D⟩

/-! ### Table `tab:classical-problems` and the specs defined after it -/

/-- Table row "Reliable broadcast | broadcast messages (⊆) | delivered messages
(⊆) | Lemma `lem:accumulating` | yes", with the text: "In reliable broadcast,
an input is a finite set of broadcast messages, and an output is a set of
delivered messages.  An output is permitted when it contains only broadcast
messages, so Lemma `lem:accumulating` applies."  The liveness requirement of
reliable broadcast that the text mentions is cited, not modeled. -/
theorem «tab:classical-problems/reliable-broadcast» {M : Type} :
    (∀ i o, (bcastSpec M).P i o ↔ ∀ x, o.mem x → i.1 x) ∧ (bcastSpec M).LiftedMono :=
  ⟨fun _ _ => Iff.rfl, bcast_liftedMono⟩

/-- Table row "Causal broadcast, global snapshot | causal history |
downward-closed set of events (⊆) | Lemma `lem:accumulating` | yes": the prefix
spec of Section `app:snapshots`, monotone by Lemma `lem:accumulating`. -/
theorem «tab:classical-problems/causal-broadcast» {Ev : Type} : (prefixSpec Ev).LiftedMono :=
  prefix_liftedMono_accumulating

/-- Table row "Grow-only counter | increments (⊆) | count (≤) | Lemma
`lem:accumulating`, with maximum | yes", with the text: "A grow-only counter
takes as input a finite set of increments and outputs a count, ordered by `≤`.
A count is permitted when it is at most the number of increments.  A permitted
count stays permitted as increments arrive, and the larger of two permitted
counts is permitted, so the maximum form of Lemma `lem:accumulating` applies."
Counts are `Count` (a wrapper on `Nat`); `card i` is the number of
increments. -/
theorem «tab:classical-problems/counter» {Inc : Type} [DecidableEq Inc] :
    (∀ i c, (counterSpec Inc).P i c ↔ c.n ≤ card i) ∧ (counterSpec Inc).LiftedMono :=
  ⟨fun _ _ => Iff.rfl, counter_liftedMono⟩

/-- Table row "Total-order broadcast | broadcast messages (⊆) | delivery
sequence (prefix) | Lemma `lem:order-commitment` | no", with the text:
"Total-order broadcast has the inputs of reliable broadcast, but an output is
a delivery sequence of distinct broadcast messages, ordered by prefix.  Two
delivery sequences have a common output extension only when one is a prefix
of the other, which is the agreement that total-order broadcast requires.  A
sequence places `a` before `b` when it lists `a`, and lists `b`, if at all,
after `a`.  An extension of the sequence keeps this placement, and no sequence
places two messages in both orders.  The rows `({a},[a])` and `({b},[b])` have
the common input extension `{a,b}`, so by Lemma `lem:order-commitment` the spec
is not monotone."  The cited equivalence with consensus is not proved. -/
theorem «tab:classical-problems/total-order-broadcast» {M : Type} [DecidableEq M] {a b : M}
    (h : a ≠ b) (D : Type) :
    (∀ i s, (tobSpec M).P i s ↔ s.l.Nodup ∧ ∀ x ∈ s.l, i.1 x) ∧
    (∀ s t : Seq M, (∃ u, s ≼ u ∧ t ≼ u) ↔ s ≼ t ∨ t ≼ s) ∧
    (∀ (s u : Seq M) (x y : M), s ≼ u → PlacesBefore s x y → PlacesBefore u x y) ∧
    (∀ (s : Seq M) (x y : M), PlacesBefore s x y → ¬ PlacesBefore s y x) ∧
    ¬ (tobSpec M).LiftedMono ∧
    ¬ ∃ Sys : CAP.System (tobSpec M) D, CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  ⟨fun _ _ => Iff.rfl, seq_common_iff, fun _ _ _ _ h1 h2 => placesBefore_mono h1 h2,
   fun _ _ _ h1 h2 => placesBefore_asymm h1 h2, (tob_not_liftedMono h).2,
   no_cap_of_not_liftedMono (tob_not_liftedMono h).2 D⟩

/-- Table row "Causal FIFO queue | causal history of enqueues | dequeue
sequence (prefix) | Lemma `lem:order-commitment` | no; yes on chains": see
Proposition `prop:causal-fifo`. -/
theorem «tab:classical-problems/causal-fifo-queue» {Ev : Type} [DecidableEq Ev] {h : Hist Ev}
    {a b : Ev} (ha : h.s.1 a) (hb : h.s.1 b) (hab : a ≠ b) (h1 : ¬ h.lt a b) (h2 : ¬ h.lt b a) :
    ¬ (queueSpec Ev).LiftedMono ∧ (queueChainSpec Ev).LiftedMono :=
  ⟨(queue_not_directed ha hb hab h1 h2).2, queueChain_liftedMono⟩

/-- Table row "Atomic snapshot | updates and scans (⊆) | views of answered
scans (extension) | Lemma `lem:order-commitment` | no": see
`«app:additional-applications/atomic-snapshot»`. -/
theorem «tab:classical-problems/atomic-snapshot» {U S : Type} [DecidableEq S] {u1 u2 : U}
    {s1 s2 : S} (hu : u1 ≠ u2) (hs : s1 ≠ s2) : ¬ (snapSpec U S).LiftedMono :=
  (snap_not_liftedMono hu hs Unit).2.1

/-- Table row "Consensus | proposals (⊆) | decision map (extension) | Lemma
`lem:bounded-values`, `k = 1` | no": see
`«app:additional-applications/consensus»`. -/
theorem «tab:classical-problems/consensus» {P Val : Type} [DecidableEq P]
    {p : Fin 2 → P} {v : Fin 2 → Val}
    (hp : ∀ r r', p r = p r' → r = r') (hv : ∀ r r', v r = v r' → r = r') :
    ¬ (ksetSpec P Val 1).LiftedMono :=
  (kset_not_directed hp hv (Nat.le_refl 1)).2

/-- Table row "`k`-set agreement | proposals (⊆) | decision map (extension) |
Lemma `lem:bounded-values` | no": see Section `app:kset`. -/
theorem «tab:classical-problems/kset» {P Val : Type} [DecidableEq P] {k : Nat}
    {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val}
    (hp : ∀ r r', p r = p r' → r = r') (hv : ∀ r r', v r = v r' → r = r') (hk : 1 ≤ k) :
    ¬ (ksetSpec P Val k).LiftedMono :=
  (kset_not_directed hp hv hk).2

/-- Table row "Leader election | candidates (⊆) | choice of leader (extension)
| Lemma `lem:bounded-values`, `k = 1` | no", with the text: "In leader
election, an input is a finite set of candidates, and an output maps candidates
to the leader each has chosen, ordered by extension.  An output is permitted
when it names only candidates and names at most one leader.  This is consensus
in which each candidate proposes itself, so Lemma `lem:bounded-values` applies
with `k = 1`."  Lean models the spec exactly so: `ksetSpec P P 1`, with
candidate `p` entering as the proposal `(p, p)`; two candidates give the
witness. -/
theorem «tab:classical-problems/leader-election» {P : Type} [DecidableEq P] {p : Fin 2 → P}
    (hp : ∀ r r', p r = p r' → r = r') (D : Type) :
    ¬ (ksetSpec P P 1).LiftedMono ∧
      ¬ ∃ Sys : CAP.System (ksetSpec P P 1) D, CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  ⟨(kset_not_directed hp hp (Nat.le_refl 1)).2, (leader_not_liftedMono hp D).2⟩

/-- Table row "Renaming | participants (⊆) | names (extension) | Lemma
`lem:bounded-values`, `k = 1` | no": see `«app:additional-applications/renaming-bounded»`
and `«app:additional-applications/renaming-any-bound»`. -/
theorem «tab:classical-problems/renaming» {P : Type} [DecidableEq P] {p q : P} (h : p ≠ q) :
    ¬ (renSpec P).LiftedMono :=
  (ren_via_bounded h).2

/-! ## Consensus: committed authority, then monotone evidence -/

/-- "As a spec, consensus is `k`-set agreement with `k = 1` …  Two
participants that propose different values and each decide their own give two
rows with a common input extension, so by Lemma `lem:bounded-values` the spec
is not monotone."  Also, from Section `app:kset`: "Consensus is `k = 1`."  The
Fischer–Lynch–Paterson result the paragraph cites is not proved. -/
theorem «app:additional-applications/consensus» {P Val : Type} [DecidableEq P]
    {p : Fin 2 → P} {v : Fin 2 → Val}
    (hp : ∀ r r', p r = p r' → r = r') (hv : ∀ r r', v r = v r' → r = r') (D : Type) :
    ¬ (ksetSpec P Val 1).LiftedMono ∧
      ¬ ∃ Sys : CAP.System (ksetSpec P Val 1) D,
        CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  ⟨(kset_not_directed hp hv (Nat.le_refl 1)).2, kset_no_cap hp hv (Nat.le_refl 1) D⟩

/-- "An output is a triple `(E,V,D)`: a certified epoch chain `E`, which is a finite
sequence of epochs …; a set `V` of votes or certificates; and a set `D` of
decisions."  Certification is not modeled: `Auth Ep Vt Dc` contains every
triple; the specification decides which are permitted. -/
abbrev «app:additional-applications/authority-output» (Ep Vt Dc : Type) := Auth Ep Vt Dc

/-- Eq. `authority-refinement`:
"`(E,V,D) ⪯ (E',V',D') ⟺ E ⪯_pref E', V ⊆ V', D ⊆ D'`", where `E ⪯_pref E'`
means that `E` is a prefix of `E'`. -/
theorem «eq:authority-refinement» {Ep Vt Dc : Type} (a b : Auth Ep Vt Dc) :
    a ≼ b ↔ (∃ t, b.E = a.E ++ t) ∧ (∀ v, a.V v → b.V v) ∧ (∀ d, a.D d → b.D d) :=
  Iff.rfl

/-- "Write `c(i)` for the certified evidence at input `i` …  The evidence spec
permits at `i` exactly the outputs that `c(i)` extends."  Generic in the input
and output orders (in the paper, outputs are `Auth Ep Vt Dc` under
Eq. `authority-refinement`). -/
theorem «app:additional-applications/evidence-spec» {I O : Type} [PO I] [PO O] (c : I → O)
    (i : I) (o : O) : (evidenceSpec c).P i o ↔ o ≼ c i :=
  Iff.rfl

/-- **Prop. `prop:monotone-evidence`** (Monotone evidence).  "If `i ⊑ j`
implies `c(i) ⪯ c(j)`, the evidence spec is monotone, and every output at every
state reachable without commitment is legal."  Proof: "Take rows `(iᵣ,oᵣ)` with
a common input extension `j`.  Each `oᵣ ⪯ c(iᵣ) ⪯ c(j)`, and `c(j)` is
permitted at `j`.  So the common-extension condition holds, and Proposition
`prop:common-expansion-form` gives Lifted Monotonicity.  The second claim
follows by Proposition `prop:exposure-boundary`."  The hypothesis is the
paper's "protocol safety"; that Paxos provides it is cited, not proved. -/
theorem «prop:monotone-evidence» {I O : Type} [PO I] [PO O] (c : I → O)
    (hc : ∀ i j, i ≼ j → c i ≼ c j) :
    (evidenceSpec c).LiftedMono ∧
      ∀ τ : State (evidenceSpec c), ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  evidenceSpec_monotone c hc

/-- "The same reasoning applies at a single state.  If every row remaining at a
state extends an output `o` of the current input, emitting `o` removes no row,
so `o` is a legal output.  Under protocol safety, this is the case for an
authority change or a certified decision once it is part of the evidence, so
emitting it needs no further commitment."  The hypothesis `hsafe` is that every
remaining row extends `o`; the conclusion is that `o` is a legal output, so its
output event `output(o)` applies no commitment and is available under any
basis.  Generic in the specification. -/
theorem «app:additional-applications/safety-exposable» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} {σ : State sp} {o : O} (ho : σ.R σ.cur o)
    (hsafe : ∀ k x, σ.R k x → o ≼ x) (B : CommitmentBasis sp) :
    Exposable σ o ∧ SysStep B σ (.output o) (outState σ o ho) :=
  safety_exposable ho hsafe B

/-- "Competing proposals for an undecided slot have incompatible extensions of
`D`, since a permitted output decides at most one value per epoch and slot.  So
certifying one of them is a commitment."  Two current outputs deciding
different values `d ≠ d'` for the same epoch and slot (`slot d = slot d'`), in
a specification whose permitted outputs decide at most one value per epoch and
slot (`SlotUnique`): emitting one rejects the other, is not a legal output, and
its output event applies a commitment, the canonical commitment `x_o`, which
the basis must contain. -/
theorem «app:additional-applications/slot-conflict» {I Ep Vt Dc κ : Type} [PO I]
    (slot : Dc → κ) {sp : Spec I (Auth Ep Vt Dc)}
    (hU : ∀ k u, sp.P k u → SlotUnique slot u.D)
    {σ : State sp} {o o' : Auth Ep Vt Dc} (ho : σ.R σ.cur o) (ho' : σ.R σ.cur o')
    {d d' : Dc} (hd : o.D d) (hd' : o'.D d') (hs : slot d = slot d') (hne : d ≠ d') :
    Excluded σ o σ.cur o' ∧ ¬ Exposable σ o ∧
      ∀ (B : CommitmentBasis sp) τ, SysStep B σ (.output o) τ → B (canonicalCommitment o) :=
  slot_conflict slot hU ho ho' hd hd' hs hne

/-- "If the succession rule were not fixed, choosing among competing next epochs
would require a commitment as well."   Two current outputs extending the chain `e` by
different next epochs `a ≠ b`: as for slots, emitting one is not a legal
output, and its output event applies `x_o`, which the basis must contain.  The
paragraph's remarks on how Multi-Paxos, Raft, and Mencius place these
commitments describe the protocols and are not formalized. -/
theorem «app:additional-applications/epoch-conflict» {I Ep Vt Dc : Type} [PO I]
    {sp : Spec I (Auth Ep Vt Dc)} {σ : State sp}
    {o o' : Auth Ep Vt Dc} (ho : σ.R σ.cur o) (ho' : σ.R σ.cur o') {e : List Ep} {a b : Ep}
    (he : o.E = e ++ [a]) (he' : o'.E = e ++ [b]) (hne : a ≠ b) :
    Excluded σ o σ.cur o' ∧ ¬ Exposable σ o ∧
      ∀ (B : CommitmentBasis sp) τ, SysStep B σ (.output o) τ → B (canonicalCommitment o) :=
  epoch_conflict ho ho' he he' hne

/-! ## `k`-set agreement: no `k`-wise test suffices -/

/-- "An input is a finite set of proposals `(p,v)`, at most one per
participant, ordered by inclusion." -/
abbrev «app:additional-applications/kset-input» (P Val : Type) := KInput P Val

/-- "Outputs are partial decision maps `m : 𝒩 ⇀ Val` ordered by extension."
(The participant type is `P` here.) -/
theorem «app:additional-applications/pmap-order» {P Val : Type} (m m' : PMap P Val) :
    m ≼ m' ↔ ∀ p a, m.f p = some a → m'.f p = some a := Iff.rfl

/-- "At input `I`, `m` is permitted when three conditions hold: it decides only
participants that propose in `I`, every value in its range is proposed in `I` (validity), and its
range has at most `k` values."  (The range is covered by a list of length
`≤ k`.) -/
theorem «app:additional-applications/kset-permitted» {P Val : Type} (k : Nat)
    (I : KInput P Val) (m : PMap P Val) :
    (ksetSpec P Val k).P I m ↔
      (∀ p a, m.f p = some a → ∃ b, I.1.1 (p, b)) ∧
      (∀ p a, m.f p = some a → ∃ q, I.1.1 (q, a)) ∧
      ∃ l : List Val, l.length ≤ k ∧ ∀ p a, m.f p = some a → a ∈ l :=
  Iff.rfl

/-- "At `p_r`'s proposal input, `{p_r ↦ v_r}` is permitted" (`k ≥ 1`).
Participants and values are indexed by `r : Fin (k+1)`. -/
theorem «app:additional-applications/kset-proposal-row» {P Val : Type} [DecidableEq P]
    {k : Nat} {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val} (hk : 1 ≤ k) (r : Fin (k + 1)) :
    (ksetSpec P Val k).P (propIn p v r) (single p v r) :=
  kset_single_row hk r

/-- "… and the union of the proposal inputs is a common input extension" (an input
because the `p_r` are distinct). -/
theorem «app:additional-applications/kset-union» {P Val : Type} [DecidableEq P] {k : Nat}
    {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val} (hp : ∀ r r', p r = p r' → r = r')
    (r : Fin (k + 1)) :
    propIn p v r ≼ unionIn p v hp :=
  kset_union_upper hp r

/-- "Any `k` of these `k+1` rows have a common output extension there": for each
omitted index `r₀`, a permitted output at the union extends every
`{p_r ↦ v_r}`, `r ≠ r₀`.  This is also the sense of "no test that examines
`k` proposal rows at a time detects the failure". -/
theorem «app:additional-applications/kset-any-k» {P Val : Type} [DecidableEq P] {k : Nat}
    {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val} (hp : ∀ r r', p r = p r' → r = r')
    (r0 : Fin (k + 1)) :
    ∃ u, (ksetSpec P Val k).P (unionIn p v hp) u ∧ ∀ r, r ≠ r0 → single p v r ≼ u :=
  kset_any_k hp r0

/-- "All `k+1` do not, since such an output would have `k+1` values." -/
theorem «app:additional-applications/kset-all-fail» {P Val : Type} [DecidableEq P] {k : Nat}
    {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val} (hp : ∀ r r', p r = p r' → r = r')
    (hv : ∀ r r', v r = v r' → r = r') :
    ¬ ∃ u, (ksetSpec P Val k).P (unionIn p v hp) u ∧ ∀ r, single p v r ≼ u :=
  kset_all_fail hp hv

/-- "So the common-extension condition fails, and the spec is not
monotone (Proposition `prop:common-expansion-form`).  This is Lemma
`lem:bounded-values`, where a map decides the values in its range.  A
partition separating the `p_r` gives the negative side of Complete CAP."
The second conjunct is obtained through Lemma `lem:bounded-values`
(`kset_not_directed`), with `Decides`. -/
theorem «app:additional-applications/kset-not-monotone» {P Val : Type} [DecidableEq P]
    {k : Nat} {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val}
    (hp : ∀ r r', p r = p r' → r = r') (hv : ∀ r r', v r = v r' → r = r') (hk : 1 ≤ k)
    (D : Type) :
    ¬ (ksetSpec P Val k).CommonExpansion ∧ ¬ (ksetSpec P Val k).LiftedMono ∧
      ¬ ∃ Sys : CAP.System (ksetSpec P Val k) D,
        CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  ⟨kset_not_commonExpansion hp hv hk, (kset_not_directed hp hv hk).2, kset_no_cap hp hv hk D⟩

/-- "The failure lies within one fiber.  An output permitted at an input is
still permitted at each input extension of that input, so Relational
Monotonicity holds.  At the union of the proposal inputs, each `{p_r ↦ v_r}`
is permitted, but the `k+1` of them are not compatible in that fiber, so the
fiber is not directed."  The wait-free impossibility result cited after this is not
proved. -/
theorem «app:additional-applications/kset-within-fiber» {P Val : Type} [DecidableEq P]
    {k : Nat} {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val}
    (hp : ∀ r r', p r = p r' → r = r') (hv : ∀ r r', v r = v r' → r = r') (hk : 1 ≤ k) :
    (∀ (I J : KInput P Val) m, I ≼ J → (ksetSpec P Val k).P I m → (ksetSpec P Val k).P J m) ∧
    (ksetSpec P Val k).RelMono ∧
    (∀ r, (ksetSpec P Val k).P (unionIn p v hp) (single p v r)) ∧
    ¬ (ksetSpec P Val k).DirectedOutputs :=
  ⟨fun _ _ _ hIJ hm => kset_grow hIJ hm, kset_relMono, kset_union_row hp hk,
   (kset_not_directed hp hv hk).1⟩

/-! ## Renaming -/

/-- Eq. `tight-renaming`: "the outputs at `N` are the injective maps
`m : N → {1,…,|N|}`" (total on `N`, undefined outside `N`; `card N` is `|N|`). -/
theorem «eq:tight-renaming» {P : Type} [DecidableEq P] (N : FinSet P) (m : PMap P Nat) :
    (renSpec P).P N m ↔
      (∀ x, N.1 x ↔ ∃ n, m.f x = some n) ∧
      (∀ x y n, m.f x = some n → m.f y = some n → x = y) ∧
      ∀ x n, m.f x = some n → 1 ≤ n ∧ n ≤ card N :=
  Iff.rfl

/-- "Relational Monotonicity holds.  Given `N ⊆ N'` and an output `m` at `N`,
the participants of `N' ∖ N` can take the names `|N|+1,…,|N'|`, which gives an
output at `N'` that extends `m`." -/
theorem «app:additional-applications/renaming-relational» {P : Type} [DecidableEq P] :
    (renSpec P).RelMono :=
  ren_relMono

/-- "At `{p}` the only output is `p ↦ 1`, and at `{q}` it is `q ↦ 1`." -/
theorem «app:additional-applications/renaming-singletons» {P : Type} [DecidableEq P]
    (p q : P) (m : PMap P Nat) :
    ((renSpec P).P (sing p) m ↔ m = name1 p) ∧ ((renSpec P).P (sing q) m ↔ m = name1 q) :=
  ⟨ren_singleton_iff p m, ren_singleton_iff q m⟩

/-- "Each has an output extension at `{p,q}`, but no injective map extends
both." -/
theorem «app:additional-applications/renaming-each-extends» {P : Type} [DecidableEq P]
    {p q : P} (h : p ≠ q) :
    (∃ u, (renSpec P).P (pairSet p q h) u ∧ name1 p ≼ u) ∧
    (∃ u, (renSpec P).P (pairSet p q h) u ∧ name1 q ≼ u) ∧
    ¬ ∃ u : PMap P Nat, Injective u ∧ name1 p ≼ u ∧ name1 q ≼ u :=
  ⟨(ren_each_extends h).1, (ren_each_extends h).2, ren_no_injective_extends_both h⟩

/-- "This is Lemma `lem:bounded-values` with `k = 1`, where a map decides the
participants to which it gives the name `1`." -/
theorem «app:additional-applications/renaming-bounded» {P : Type} [DecidableEq P]
    {p q : P} (h : p ≠ q) :
    (∀ u : PMap P Nat, Injective u → ∃ l : List P, l.length ≤ 1 ∧ ∀ x, HoldsName1 u x → x ∈ l) ∧
    ¬ (renSpec P).CommonExpansion ∧ ¬ (renSpec P).LiftedMono :=
  ⟨fun _ hu => inj_bound hu, ren_via_bounded h⟩

/-- "The fiber at `{p,q}` is not directed either: `{p↦1,q↦2}` and `{p↦2,q↦1}`
have no common output extension.  The spec therefore fails Lifted
Monotonicity, and by Theorem `thm:complete-cap` with `E = P` and Corollary
`cor:complete-cap-any-system` a partition separating `p` and `q` rules out
Availability for `P` with Partition Consistency." -/
theorem «app:additional-applications/renaming-not-monotone» {P : Type} [DecidableEq P]
    {p q : P} (h : p ≠ q) (D : Type) :
    (¬ ∃ u, name2 p q 1 2 ≼ u ∧ name2 p q 2 1 ≼ u) ∧
    ¬ (renSpec P).DirectedOutputs ∧ ¬ (renSpec P).LiftedMono ∧
    ¬ ∃ Sys : CAP.System (renSpec P) D, CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  ⟨(ren_not_directed h).1, (ren_not_directed h).2.1, (ren_not_directed h).2.2,
    ren_no_cap h D⟩

/-- "The witness uses only the name `1` at single-participant inputs and the
injectivity of outputs at `{p,q}`.  It therefore applies to renaming with any
namespace `{1,…,f(|N|)}` such that `f(n) ≥ n` for all `n`, for example
`f(n) = 2n-1`."  The wait-free renaming hierarchy cited next is not proved. -/
theorem «app:additional-applications/renaming-any-bound» {P : Type} [DecidableEq P]
    {f : Nat → Nat} (hf : ∀ n, n ≤ f n) {p q : P} (h : p ≠ q) (D : Type) :
    ¬ (renSpecB P f hf).LiftedMono ∧
      ¬ ∃ Sys : CAP.System (renSpecB P f hf) D,
        CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  renB_not_liftedMono hf h D

/-! ## Snapshots -/

/-- "Inputs are finite causal histories, that is, finite sets of environment events with a
causal partial order; `h ⊑ h'` when `h` is a downward-closed subset of `h'`
carrying the restricted order." -/
theorem «app:additional-applications/history-order» {Ev : Type} (h h' : Hist Ev) :
    h ≼ h' ↔
      (∀ x, h.s.1 x → h'.s.1 x) ∧ (∀ a b, h.s.1 b → h'.lt a b → h.s.1 a) ∧
      ∀ a b, h.s.1 a → h.s.1 b → (h.lt a b ↔ h'.lt a b) :=
  Iff.rfl

/-- "The *prefix* spec permits at `h` any downward-closed subset of
`h`, with outputs ordered by inclusion." -/
theorem «app:additional-applications/prefix-spec» {Ev : Type} (h : Hist Ev) (p : ESet Ev) :
    (prefixSpec Ev).P h p ↔ (∀ x, p.mem x → h.s.1 x) ∧ ∀ a b, p.mem b → h.lt a b → p.mem a :=
  Iff.rfl

/-- "Old prefixes stay legal as history grows, and finite unions of prefixes are
prefixes, so it satisfies Lifted Monotonicity, by Lemma `lem:accumulating`."
The last conjunct goes through Lemma `lem:accumulating`
(`prefix_liftedMono_accumulating`). -/
theorem «app:additional-applications/prefix-monotone» {Ev : Type} :
    (∀ {h h' : Hist Ev} (p : ESet Ev), h ≼ h' → (prefixSpec Ev).P h p → (prefixSpec Ev).P h' p) ∧
    (∀ (j : Hist Ev) (ps : List (ESet Ev)), (∀ p ∈ ps, (prefixSpec Ev).P j p) →
      (prefixSpec Ev).P j ⟨fun x => ∃ p ∈ ps, p.mem x⟩) ∧
    (prefixSpec Ev).LiftedMono :=
  ⟨fun _ hle hp => prefix_mono hle hp, fun _ ps hps => prefix_union ps hps,
    prefix_liftedMono_accumulating⟩

/-- "It guarantees neither freshness nor completeness": the empty prefix is
permitted at every history.  (The following sentences on global snapshots and
causal broadcast describe those protocols' outputs as prefixes and are not
formalized beyond this spec.) -/
theorem «app:additional-applications/prefix-empty» {Ev : Type} (h : Hist Ev) :
    (prefixSpec Ev).P h ⟨fun _ => False⟩ :=
  prefix_empty h

/-- "A spec that requires the complete history, with output `h` at `h`
and outputs ordered by equality, is functional and not monotone: its required
output changes whenever an environment event arrives."  (Not monotone as soon as there is an
event `e`: `∅ ⊑ {e}`.) -/
theorem «app:additional-applications/complete-history» {Ev : Type} (e : Ev) :
    (∀ h o, (completeSpec Ev).P h o ↔ o = ⟨h⟩) ∧
    (completeSpec Ev).Functional ∧ ¬ (completeSpec Ev).MonotoneF ∧
      ¬ (completeSpec Ev).LiftedMono :=
  ⟨fun _ _ => Iff.rfl, completeSpec_functional, completeSpec_not_monotone e⟩

/-- "By Proposition `prop:functional-exposure-boundary`, some output can then be
emitted only after a commitment that rules out larger inputs."   At some state
reachable without commitment, some current output rules out an excluded row, and
the output event emitting it applies a commitment, `x_o`, which the basis must
contain. -/
theorem «app:additional-applications/complete-history-commitment» {Ev : Type} (e : Ev) :
    ∃ (τ : State (completeSpec Ev)) (o : Eqd (Hist Ev)), ReachableCF τ ∧ τ.R τ.cur o ∧
      (∃ k x, Excluded τ o k x) ∧
      ∀ (B : CommitmentBasis (completeSpec Ev)) τ', SysStep B τ (.output o) τ' →
        B (canonicalCommitment o) :=
  completeSpec_commitment_needed e

/-- "An input is a finite set of update and scan operations, ordered by
inclusion.  An output maps answered scans to views, each a set of updates of
the input, and is ordered by extension.  It is permitted when every answered
scan is in the input and any two of its views are comparable."  Only this
consequence of atomicity is modeled, as the paper says ("We model one
consequence of this requirement"). -/
theorem «app:additional-applications/atomic-snapshot-spec» {U S : Type}
    (i : FinSet (SOp U S)) (o : PMap S (ESet U)) :
    (snapSpec U S).P i o ↔
      (∀ s V, o.f s = some V → i.1 (.scan s) ∧ ∀ u, V.mem u → i.1 (.upd u)) ∧
      (∀ s s' V V', o.f s = some V → o.f s' = some V' → V ≼ V' ∨ V' ≼ V) :=
  Iff.rfl

/-- "An output places update `a` before update `b` when one of its views
contains `a` and not `b`.  Let an input contain updates `u₁,u₂` and scans
`s₁,s₂`.  The outputs `{s₁ ↦ {u₁}}` and `{s₂ ↦ {u₂}}` are both permitted there,
and they place `u₁` and `u₂` in opposite orders.  By Lemma
`lem:order-commitment`, the fiber is not directed and the spec is not
monotone."  (`Reflects o a b` is "places `a` before `b`".)  The wait-free
implementability from atomic registers that the paragraph cites is not
proved; the linearizable register is treated in Section `sec:complete-cap`. -/
theorem «app:additional-applications/atomic-snapshot» {U S : Type} [DecidableEq S]
    {u1 u2 : U} {s1 s2 : S} (hu : u1 ≠ u2) (hs : s1 ≠ s2) (D : Type) :
    (snapSpec U S).P (snapIn hu hs) (scanAns s1 u1) ∧
    (snapSpec U S).P (snapIn hu hs) (scanAns s2 u2) ∧
    Reflects (scanAns s1 u1) u1 u2 ∧ Reflects (scanAns s2 u2) u2 u1 ∧
    ¬ (snapSpec U S).DirectedOutputs ∧ ¬ (snapSpec U S).LiftedMono ∧
      ¬ ∃ Sys : CAP.System (snapSpec U S) D,
        CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  ⟨scanAns_row hu hs (Or.inl rfl) (Or.inl rfl), scanAns_row hu hs (Or.inr rfl) (Or.inr rfl),
   ⟨s1, ⟨fun x => x = u1⟩, by simp [scanAns], rfl, fun h => hu h.symm⟩,
   ⟨s2, ⟨fun x => x = u2⟩, by simp [scanAns], rfl, fun h => hu h⟩,
   snap_not_liftedMono hu hs D⟩

/-! ## A causal FIFO queue -/

/-- "An input is a finite causal history of enqueue events, ordered as in
Section `app:snapshots`.  Each event enqueues a distinct value, which we
identify with the event.  An output is a dequeue sequence, ordered by prefix.
A sequence is permitted at `h` when it lists distinct events of `h`, never
lists an event after one that is causally later, and skips no event: if it
lists an event, it lists every event causally before it." -/
theorem «app:additional-applications/queue-spec» {Ev : Type} (h : Hist Ev) (s : Seq Ev) :
    (queueSpec Ev).P h s ↔
      s.l.Nodup ∧ (∀ x ∈ s.l, h.s.1 x) ∧ (∀ a b, b ∈ s.l → h.lt a b → a ∈ s.l) ∧
        s.l.Pairwise (fun x y => ¬ h.lt y x) :=
  Iff.rfl

/-- **Prop. `prop:causal-fifo`** (Causal FIFO queue).  "The causal FIFO queue
satisfies Relational Monotonicity.  Its fiber at a history `h` is directed if
and only if any two events of `h` are causally ordered.  Hence the spec is not
monotone if two values can be enqueued concurrently, and its restriction to
histories whose events are causally totally ordered is monotone."  The proof's
steps are `queue_grow`, `below_seq` and `queue_concurrent` (with
`PlacesBefore`, Lemma `lem:order-commitment`), `qperm_pred`, `qperm_eq`,
`qperm_prefix`, and `directed_of_comparable`.  The restriction is
`queueChainSpec`, on `ChainHist`. -/
theorem «prop:causal-fifo» {Ev : Type} [DecidableEq Ev] :
    (queueSpec Ev).RelMono ∧
    (∀ h : Hist Ev, JointLift ((queueSpec Ev).P h) ((queueSpec Ev).P h) ↔ Chain h) ∧
    (∀ {h : Hist Ev} {a b : Ev}, h.s.1 a → h.s.1 b → a ≠ b → ¬ h.lt a b → ¬ h.lt b a →
      ¬ (queueSpec Ev).LiftedMono) ∧
    (queueChainSpec Ev).LiftedMono :=
  ⟨queue_relMono, queue_directed_iff, fun ha hb hab h1 h2 => (queue_not_directed ha hb hab h1 h2).2,
   queueChain_liftedMono⟩

/-- "At a history with concurrent enqueues `a` and `b`, consider the two
sequences built in the proof.  Emitting the one that lists `a` removes the row
of the one that lists `b`, and no remaining row at that input extends the
removed one.  So the output event applies a commitment." -/
theorem «app:additional-applications/queue-commitment» {Ev : Type} [DecidableEq Ev]
    {h : Hist Ev} {a b : Ev} (ha : h.s.1 a) (hb : h.s.1 b) (hab : a ≠ b)
    (h1 : ¬ h.lt a b) (h2 : ¬ h.lt b a) :
    ∃ σa σb : Seq Ev, PlacesBefore σa a b ∧ PlacesBefore σb b a ∧
      Excluded (canon (queueSpec Ev) h) σa h σb ∧ ¬ Exposable (canon (queueSpec Ev) h) σa ∧
      ∀ (B : CommitmentBasis (queueSpec Ev)) τ, SysStep B (canon (queueSpec Ev) h) (.output σa) τ →
        B (canonicalCommitment σa) :=
  queue_order_commitment ha hb hab h1 h2

/-- "A queue that reports only the set of dequeued events, which must be
downward closed, has the prefix spec of Section `app:snapshots`, which is
monotone." -/
theorem «app:additional-applications/queue-set-variant» {Ev : Type} :
    (prefixSpec Ev).LiftedMono :=
  prefix_liftedMono_accumulating

/-- "A queue without the no-skipping rule may dequeue an event and never
dequeue an event causally before it.  Its fiber at any history with two
distinct events `a` and `b` is not directed, even when `a` is causally before
`b`, since `[a]` and `[b]` are both permitted and place the two events in
opposite orders." -/
theorem «app:additional-applications/queue-skip-variant» {Ev : Type} [DecidableEq Ev]
    {h : Hist Ev} {a b : Ev} (ha : h.s.1 a) (hb : h.s.1 b) (hab : a ≠ b) :
    ((skipSpec Ev).P h ⟨[a]⟩ ∧ (skipSpec Ev).P h ⟨[b]⟩) ∧
    ¬ (skipSpec Ev).DirectedOutputs ∧ ¬ (skipSpec Ev).LiftedMono :=
  ⟨⟨⟨by simp, by simpa using ha, by simp [Sorted]⟩, ⟨by simp, by simpa using hb, by simp [Sorted]⟩⟩,
   skipSpec_not_directed ha hb hab⟩

end Paper
end CC
