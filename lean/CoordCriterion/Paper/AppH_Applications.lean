import CoordCriterion.Appendix.Classical
import CoordCriterion.Appendix.ClassicalFrontiers
import CoordCriterion.Appendix.BLink

/-!
# Paper, Appendix G: Classical problems in distributed computing (`app:additional-applications`)

Source: `appendices/classical-problems.tex` (the whole appendix: patterns
and the table of classical problems; broadcast; consensus, with
`k`-set agreement and the shared-memory remark; leader election; snapshots;
queues; search structures).

How to read this file: one `/-! ## … -/` section per subsection of the
appendix, in paper order.  Lemmas, propositions, the table, and labeled
equations are named by their label (`«lem:accumulating»`,
`«prop:causal-queue»`, `«tab:classical-problems/…»`,
`«eq:authority-refinement»`); every other claim is named
`«app:additional-applications/<slug>»`.  Each docstring quotes the claim;
statements are written out in terms of library definitions of
`Appendix/Applications.lean`, `Appendix/Classical.lean`,
`Appendix/ClassicalFrontiers.lean`, and `Appendix/Frontiers.lean`, and proofs
point there.

Common modeling choices: output types contain all partial maps / sets, and
"no common output extension" is proved in the whole output type when that is
stronger; "not monotone" is `¬ LiftedMono`; "no system has Availability for
`P` and Partition Consistency" (Theorem `thm:complete-cap` with `E = P` and
Corollary `cor:complete-cap-any-system`) is
`¬ ∃ Sys, CAP.Availability Sys ∧ CAP.PartitionConsistency Sys`, obtained from
`CC.CAP.complete_cap`, whose proof builds the partition separating the rows'
inputs.  Classical results the appendix cites (Fischer–Lynch–Paterson,
wait-free computability and Herlihy's hierarchy, the renaming bounds, the
equivalence of total-order broadcast and consensus, broadcast without
agreement, ring election algorithms, Angluin's anonymous-ring result, the
weakest failure detector `Ω`, wait-free atomic snapshots, liveness of reliable
broadcast, the Chandy–Lamport algorithm) are not proved here; the docstrings
that mention them say so.
-/

namespace CC
namespace Paper

open CC.Txn CC.Apps

/-! ## Patterns and problems (`app:classical-patterns`) -/

section ThreePatterns
open CC.Apps

/-- **Lemma `lem:accumulating`** (Growth in a semilattice).  "Suppose the
outputs of an I/O specification form a join semilattice under `⪯`.  If every
output permitted at an input is still permitted at each input extension of
that input, and the join of two outputs permitted at one input is permitted
there, then the spec is monotone."  Proof: "Take `i ⊑ j` and a nonempty finite
`X ⊆ P(i)`.  Each member of `X` is permitted at `j`, so by induction on the
size of `X` their join is permitted at `j`, and it extends every member of
`X`."  `join` is any binary operation giving an upper bound of its arguments
(`hl`, `hr`); leastness is not used. -/
theorem «lem:accumulating» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (join : O → O → O) (hl : ∀ a b, a ≼ join a b) (hr : ∀ a b, b ≼ join a b)
    (hgrow : ∀ i j o, i ≼ j → sp.P i o → sp.P j o)
    (hjoin : ∀ j a b, sp.P j a → sp.P j b → sp.P j (join a b)) : sp.LiftedMono :=
  liftedMono_of_join join hl hr hjoin (fun i j o hij ho => ⟨o, hgrow i j o hij ho, PO.refl o⟩)

/-- "The common case is sets of facts ordered by inclusion, with union as the
join; counters under `≤`, with the maximum as the join, are another."  The set
case: outputs `ESet F` under inclusion with `ESet.union`
(`accumulating_monotone`); the counter case is
`«tab:classical-problems/counter»`. -/
theorem «app:classical-patterns/accumulating-sets» {I F : Type} [PO I] {sp : Spec I (ESet F)}
    (hgrow : ∀ i j o, i ≼ j → sp.P i o → sp.P j o)
    (hunion : ∀ j a b, sp.P j a → sp.P j b → sp.P j (ESet.union a b)) : sp.LiftedMono :=
  accumulating_monotone hgrow hunion

/-- "The proof uses only that each fiber contains, with any two outputs, a
common output extension of both, so the join need not be least."  Lean
assumes Relational Monotonicity in place of "still permitted at each input
extension", which is weaker. -/
theorem «app:classical-patterns/accumulating-join» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} (join : O → O → O) (hl : ∀ a b, a ≼ join a b) (hr : ∀ a b, b ≼ join a b)
    (hc : ∀ j a b, sp.P j a → sp.P j b → sp.P j (join a b)) (hR : sp.RelMono) :
    sp.LiftedMono :=
  liftedMono_of_join join hl hr hc hR

/-- **Lemma `lem:order-commitment`** (Ordering concurrent events).  "Fix an
input `j`.  Suppose that each output `o` of an I/O specification has a
relation `<_o` on events, the pairs that `o` places in order, such that (1)
`o ⪯ u` implies `<_o ⊆ <_u`, and (2) no `u ∈ P(j)` has both `a <_u b` and
`b <_u a`.  If rows `(i₁,o₁)` and `(i₂,o₂)` with `i₁ ⊑ j` and `i₂ ⊑ j` have
`a <_{o₁} b` and `b <_{o₂} a`, then the spec is not monotone.  If
`i₁ = i₂ = j`, the fiber at `j` is not directed."  Proof: "A common output
extension `u` of `o₁` and `o₂` in `P(j)` would have `a <_u b` and `b <_u a` by
(1), which contradicts (2).  So the common-extension condition fails, and by
Proposition `prop:common-expansion-form` so does Lifted Monotonicity.  When
`i₁ = i₂ = j`, the same argument shows that `o₁` and `o₂` are incompatible in
`P(j)`."  `<_o` is `before o`. -/
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

/-- **Lemma `lem:bounded-values`** (Bounded number of values).  "Fix an input
`j` and a number `k`.  Suppose that each output `o` of an I/O specification has
a set `D(o)` of values it decides, such that (1) `o ⪯ u` implies
`D(o) ⊆ D(u)`, and (2) every `u ∈ P(j)` has at most `k` values in `D(u)`.  If
`k+1` rows `(i_r,o_r)` with `i_r ⊑ j` each decide a different value
`v_r ∈ D(o_r)`, then they cannot all grow to one output at `j`, so the spec is
not monotone."  Proof: "A common output extension `u` of the `k+1` outputs in
`P(j)` would have all `k+1` values in `D(u)` by (1), which contradicts (2).  So
the common-extension condition fails, and Proposition
`prop:common-expansion-form` applies."  `D(o)` is `dec o`; "at most `k`
values": covered by a list of length `≤ k`. -/
theorem «lem:bounded-values» {I O V : Type} [PO I] [PO O] {sp : Spec I O}
    (dec : O → V → Prop) (hmono : ∀ o u v, o ≼ u → dec o v → dec u v) {k : Nat} {j : I}
    (hbound : ∀ u, sp.P j u → ∃ l : List V, l.length ≤ k ∧ ∀ v, dec u v → v ∈ l)
    (i : Fin (k + 1) → I) (o : Fin (k + 1) → O) (v : Fin (k + 1) → V)
    (hv : ∀ r r', v r = v r' → r = r') (hrow : ∀ r, sp.P (i r) (o r)) (hj : ∀ r, i r ≼ j)
    (hd : ∀ r, dec (o r) (v r)) :
    (¬ ∃ u, sp.P j u ∧ ∀ r, o r ≼ u) ∧ ¬ sp.CommonExpansion ∧ ¬ sp.LiftedMono :=
  ⟨bounded_no_common dec hmono hbound o v hv hd,
   bounded_values dec hmono hbound i o v hv hrow hj hd⟩

/-- **Lemma `lem:blocking`** (Blocking before arrival).  "Suppose the inputs
of an I/O specification are sets ordered by `⊆`, and its outputs are pairs
`(A,B)` of disjoint sets, the accepted and the blocked facts, ordered
componentwise by `⊆`.  If rows `(i,(A,B))` and `(j,(A',B'))` with `i ⊆ j` have
a fact `f ∈ B ∩ A'`, the spec is not monotone."  Proof: "A common output
extension `(A'',B'')` of the two outputs in `P(j)` has `f ∈ B ⊆ B''` and
`f ∈ A' ⊆ A''`, but `A''` and `B''` are disjoint.  So the common-extension
condition fails, and Proposition `prop:common-expansion-form` applies."
Generic in the input order and in the output type: `acc o` and `blk o` are the
accepted and blocked facts, each growing with `⪯` (as componentwise `⊆`
does), and disjointness is needed only in the fiber at `j`.  The election
example that follows (the rows at `ab·` and `aba`, closing the polls, and the
fixed list of voters) is prose and is not formalized. -/
theorem «lem:blocking» {I O F : Type} [PO I] [PO O] {sp : Spec I O}
    (acc blk : O → F → Prop)
    (hacc : ∀ o u f, o ≼ u → acc o f → acc u f)
    (hblk : ∀ o u f, o ≼ u → blk o f → blk u f) {j : I}
    (hdisj : ∀ u f, sp.P j u → acc u f → ¬ blk u f)
    {i : I} {o o' : O} {f : F} (h1 : sp.P i o) (h2 : sp.P j o') (hij : i ≼ j)
    (hb : blk o f) (ha : acc o' f) :
    (¬ ∃ u, sp.P j u ∧ o ≼ u ∧ o' ≼ u) ∧ ¬ sp.CommonExpansion ∧ ¬ sp.LiftedMono :=
  blocking acc blk hacc hblk hdisj h1 h2 hij hb ha

end ThreePatterns


/-- "When one of the last three [Lemmas `lem:order-commitment`,
`lem:bounded-values`, `lem:blocking`] applies, Complete CALM (Theorem
`thm:complete-calm`) says that the runs of the spec are not consistent.  The
No-commitment test (Proposition `prop:exposure-boundary`) adds that some
output, at some state reachable without commitment, is not legal, so emitting
it applies a commitment.  With `E = P`, Theorem
`thm:complete-cap` and Corollary `cor:complete-cap-any-system` add that no
system for the spec has Availability for `P` and Partition Consistency.  …
When Lemma `lem:accumulating` applies, the runs are consistent, and the
canonical system for `P` needs no commitment and escapes CAP for `P`."
First conjunct: from `¬ LiftedMono` (the conclusion of each of the three lemmas); second:
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


/-! ### Table `tab:classical-problems` -/

/-- Table row "Reliable broadcast | delivered messages (⊆) | yes"; see
`«app:additional-applications/reliable-broadcast»`. -/
theorem «tab:classical-problems/reliable-broadcast» {M : Type} : (bcastSpec M).LiftedMono :=
  bcast_liftedMono

/-- Table row "Causal broadcast | causally closed set of delivered messages
(⊆) | yes"; see `«app:additional-applications/causal-broadcast»`. -/
theorem «tab:classical-problems/causal-broadcast» {Ev : Type} : (prefixSpec Ev).LiftedMono :=
  prefix_liftedMono_accumulating

/-- Table row "Grow-only counter | count (≤) | yes"; see
`«app:additional-applications/counter»`. -/
theorem «tab:classical-problems/counter» {Inc : Type} [DecidableEq Inc] :
    (counterSpec Inc).LiftedMono :=
  counter_liftedMono

/-- Table row "Total-order broadcast | delivery sequence (prefix) | no"; see
`«app:additional-applications/total-order-broadcast»`. -/
theorem «tab:classical-problems/total-order-broadcast» {M : Type} [DecidableEq M] {a b : M}
    (h : a ≠ b) : ¬ (tobSpec M).LiftedMono :=
  (tob_not_liftedMono h).2

/-- Table row "Consensus, `k`-set agreement | decision map (extension) | no";
see `«app:additional-applications/consensus»` and
`«app:additional-applications/kset»`. -/
theorem «tab:classical-problems/consensus-kset» {P Val : Type} [DecidableEq P] {k : Nat}
    {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val}
    (hp : ∀ r r', p r = p r' → r = r') (hv : ∀ r r', v r = v r' → r = r') (hk : 1 ≤ k) :
    ¬ (ksetSpec P Val k).LiftedMono :=
  (kset_not_directed hp hv hk).2

/-- Table row "Leader election, participants listed | leader or `⊥` (`⊥`
lowest) | yes"; see `«app:additional-applications/leader-listed»`. -/
theorem «tab:classical-problems/leader-listed» (All : List Nat) :
    (leaderAllSpec All).LiftedMono :=
  (leaderAll_consistent All).2

/-- Table row "Leader election, participants unlisted | leader or `⊥` (`⊥`
lowest) | no"; see `«app:additional-applications/leader-unlisted»`. -/
theorem «tab:classical-problems/leader-unlisted» : ¬ leaderSpec.LiftedMono :=
  (leader_not_monotone Unit).1

/-- Table row "Global snapshot | a cut per scan (extension) | yes*", with the
caption: "*Monotone across partitions when each process answers its own
scans."  See Proposition `prop:snapshots`(1). -/
theorem «tab:classical-problems/global-snapshot» {Ev : Type} {n : Nat} (proc : Ev → Fin n)
    (scan : Ev → Prop) : Deploy.MonoAcrossPartitions (Deploy.ownerD (clSpec proc scan)) :=
  cl_monoAcross proc scan

/-- Table row "Atomic snapshot | a view per scan (extension) | no*"; see
Proposition `prop:snapshots`(2). -/
theorem «tab:classical-problems/atomic-snapshot» {Ev : Type} {proc : Ev → Fin 2}
    {scan : Ev → Prop} (w : Four proc scan) :
    ¬ Deploy.MonoAcrossPartitions (Deploy.ownerD (atSpec proc scan)) :=
  atomic_not_monoAcross w

/-- Table row "Causal queue | dequeue history (prefix) | yes"; see
Proposition `prop:causal-queue`(1). -/
theorem «tab:classical-problems/causal-queue» {Ev : Type} : (cqSpec Ev).LiftedMono :=
  cqSpec_liftedMono

/-- Table row "Forward-reachability lookup | valid claims (⊆) | yes": the spec
bounded by the valid claims satisfies Lifted Monotonicity
(Propositions `prop:persistent-forwarding` and `prop:remembered-claims`(1)). -/
theorem «tab:classical-problems/forward-lookup» {K P : Type} (Rs : Front.Restructuring K P) :
    (boundSpec (fwdV Rs)).LiftedMono :=
  (boundSpec_liftedMono_iff _).2 (fwdV_grows Rs)

/-! ## Broadcast -/

/-- "In reliable broadcast, an input is a finite set of broadcast messages,
and an output is a set of delivered messages.  An output is permitted when it
contains only broadcast messages, so Lemma `lem:accumulating` applies."  The
liveness requirement of reliable broadcast that the text mentions is cited,
not modeled. -/
theorem «app:additional-applications/reliable-broadcast» {M : Type} :
    (∀ i o, (bcastSpec M).P i o ↔ ∀ x, o.mem x → i.1 x) ∧ (bcastSpec M).LiftedMono :=
  ⟨fun _ _ => Iff.rfl, bcast_liftedMono⟩

/-- "An input is a finite causal history of broadcasts: a finite set of events
with a strict partial order of causal precedence.  A history `h'` extends `h`,
`h ⊑ h'`, when the events of `h` form a causally closed subset of `h'` that
carries the restricted order, so an input extension never adds an event to
the causal past of an old one." -/
theorem «app:additional-applications/history-order» {Ev : Type} (h h' : Hist Ev) :
    h ≼ h' ↔
      (∀ x, h.s.1 x → h'.s.1 x) ∧ (∀ a b, h.s.1 b → h'.lt a b → h.s.1 a) ∧
      ∀ a b, h.s.1 a → h.s.1 b → (h.lt a b ↔ h'.lt a b) :=
  Iff.rfl

/-- "An output is a set of delivered messages, permitted when it is causally
closed in the input.  Such a set stays causally closed as the history grows,
and a union of causally closed sets is causally closed, so Lemma
`lem:accumulating` applies."  Delivered messages are identified with their
broadcast events; the spec is `prefixSpec`, and the last conjunct goes
through Lemma `lem:accumulating` (`prefix_liftedMono_accumulating`). -/
theorem «app:additional-applications/causal-broadcast» {Ev : Type} :
    (∀ (h : Hist Ev) p, (prefixSpec Ev).P h p ↔
      (∀ x, p.mem x → h.s.1 x) ∧ ∀ a b, p.mem b → h.lt a b → p.mem a) ∧
    (∀ {h h' : Hist Ev} (p : ESet Ev), h ≼ h' → (prefixSpec Ev).P h p → (prefixSpec Ev).P h' p) ∧
    (∀ (j : Hist Ev) (ps : List (ESet Ev)), (∀ p ∈ ps, (prefixSpec Ev).P j p) →
      (prefixSpec Ev).P j ⟨fun x => ∃ p ∈ ps, p.mem x⟩) ∧
    (prefixSpec Ev).LiftedMono :=
  ⟨fun _ _ => Iff.rfl, fun _ hle hp => prefix_mono hle hp, fun _ ps hps => prefix_union ps hps,
    prefix_liftedMono_accumulating⟩

/-- "A grow-only counter takes as input a finite set of increments and outputs
a count, ordered by `≤`.  A count is permitted when it is at most the number
of increments.  A permitted count stays permitted as increments arrive, and
the larger of two permitted counts is permitted, so the maximum form of Lemma
`lem:accumulating` applies."  Counts are `Count` (a wrapper on `Nat`);
`card i` is the number of increments. -/
theorem «app:additional-applications/counter» {Inc : Type} [DecidableEq Inc] :
    (∀ i c, (counterSpec Inc).P i c ↔ c.n ≤ card i) ∧ (counterSpec Inc).LiftedMono :=
  ⟨fun _ _ => Iff.rfl, counter_liftedMono⟩

/-- "Total-order broadcast has the inputs of reliable broadcast, but an output
is a delivery sequence of distinct broadcast messages, ordered by prefix.  Two
delivery sequences have a common output extension only when one is a prefix
of the other, which is the agreement that total-order broadcast requires.  A
sequence places `a` before `b` when it lists `a`, and lists `b`, if at all,
after `a`.  An extension of the sequence keeps this placement, and no sequence
places two messages in both orders.  The rows `({a},[a])` and `({b},[b])` have
the common input extension `{a,b}`, so by Lemma `lem:order-commitment` the
spec is not monotone."  Also: "Total-order broadcast needs a commitment"
(the last conjunct, and by the No-commitment test).  The cited classical
results (broadcast without agreement; the equivalence with consensus) are not
proved. -/
theorem «app:additional-applications/total-order-broadcast» {M : Type} [DecidableEq M]
    {a b : M} (h : a ≠ b) (D : Type) :
    (∀ i s, (tobSpec M).P i s ↔ s.l.Nodup ∧ ∀ x ∈ s.l, i.1 x) ∧
    (∀ s t : Seq M, (∃ u, s ≼ u ∧ t ≼ u) ↔ s ≼ t ∨ t ≼ s) ∧
    (∀ (s u : Seq M) (x y : M), s ≼ u → PlacesBefore s x y → PlacesBefore u x y) ∧
    (∀ (s : Seq M) (x y : M), PlacesBefore s x y → ¬ PlacesBefore s y x) ∧
    ¬ (tobSpec M).LiftedMono ∧
    ¬ ∃ Sys : CAP.System (tobSpec M) D, CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  ⟨fun _ _ => Iff.rfl, seq_common_iff, fun _ _ _ _ h1 h2 => placesBefore_mono h1 h2,
   fun _ _ _ h1 h2 => placesBefore_asymm h1 h2, (tob_not_liftedMono h).2,
   no_cap_of_not_liftedMono (tob_not_liftedMono h).2 D⟩

/-! ## Consensus: committed authority, then monotone evidence -/

/-- "In consensus, inputs are finite sets of proposals, at most one per
participant, ordered by inclusion.  Outputs are partial decision maps from
participants to values, ordered by extension, and every permitted output
decides at most one value, which some participant proposed.  Two participants
that propose different values and each decide their own give two rows with a
common input extension, so by Lemma `lem:bounded-values` with `k = 1` the spec
is not monotone."  Consensus is `ksetSpec P Val 1`; the second conjunct goes
through Lemma `lem:bounded-values` (`kset_not_directed`).  The
Fischer–Lynch–Paterson result the paragraph cites is not proved. -/
theorem «app:additional-applications/consensus» {P Val : Type} [DecidableEq P]
    {p : Fin 2 → P} {v : Fin 2 → Val}
    (hp : ∀ r r', p r = p r' → r = r') (hv : ∀ r r', v r = v r' → r = r') (D : Type) :
    (∀ I m, (ksetSpec P Val 1).P I m ↔
      (∀ p a, m.f p = some a → ∃ b, I.1.1 (p, b)) ∧
      (∀ p a, m.f p = some a → ∃ q, I.1.1 (q, a)) ∧
      ∃ l : List Val, l.length ≤ 1 ∧ ∀ p a, m.f p = some a → a ∈ l) ∧
    ¬ (ksetSpec P Val 1).LiftedMono ∧
      ¬ ∃ Sys : CAP.System (ksetSpec P Val 1) D,
        CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  ⟨fun _ _ => Iff.rfl, (kset_not_directed hp hv (Nat.le_refl 1)).2,
    kset_no_cap hp hv (Nat.le_refl 1) D⟩

/-- "The same holds for `k`-set agreement, which allows up to `k` decided
values: `k+1` participants that each decide their own proposal give the
witness of Lemma `lem:bounded-values`."  `ksetSpec P Val k`; the witness rows
are `(propIn p v r, single p v r)` at the common input extension
`unionIn p v hp`. -/
theorem «app:additional-applications/kset» {P Val : Type} [DecidableEq P]
    {k : Nat} {p : Fin (k + 1) → P} {v : Fin (k + 1) → Val}
    (hp : ∀ r r', p r = p r' → r = r') (hv : ∀ r r', v r = v r' → r = r') (hk : 1 ≤ k)
    (D : Type) :
    (∀ r, (ksetSpec P Val k).P (propIn p v r) (single p v r) ∧ propIn p v r ≼ unionIn p v hp) ∧
    (¬ ∃ u, (ksetSpec P Val k).P (unionIn p v hp) u ∧ ∀ r, single p v r ≼ u) ∧
    ¬ (ksetSpec P Val k).LiftedMono ∧
      ¬ ∃ Sys : CAP.System (ksetSpec P Val k) D,
        CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  ⟨fun r => ⟨kset_single_row hk r, kset_union_upper hp r⟩, kset_all_fail hp hv,
    (kset_not_directed hp hv hk).2, kset_no_cap hp hv hk D⟩

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
choosing the value for a slot is a commitment, and every slot needs one."  Two current outputs deciding
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
paragraph's remarks that a fixed authority makes each per-slot commitment
locally, like a voter's ballot, and on how Multi-Paxos, Raft, and Mencius place
the per-slot commitments, describe the protocols and are not formalized. -/
theorem «app:additional-applications/epoch-conflict» {I Ep Vt Dc : Type} [PO I]
    {sp : Spec I (Auth Ep Vt Dc)} {σ : State sp}
    {o o' : Auth Ep Vt Dc} (ho : σ.R σ.cur o) (ho' : σ.R σ.cur o') {e : List Ep} {a b : Ep}
    (he : o.E = e ++ [a]) (he' : o'.E = e ++ [b]) (hne : a ≠ b) :
    Excluded σ o σ.cur o' ∧ ¬ Exposable σ o ∧
      ∀ (B : CommitmentBasis sp) τ, SysStep B σ (.output o) τ → B (canonicalCommitment o) :=
  epoch_conflict ho ho' he he' hne


/-- Paragraph "Shared memory": "The queue orders concurrent requests.  From
sets of requests to request sequences, it is the total-order broadcast spec of
Section `app:broadcast`, so ordering them is a commitment, and the object
makes it locally, as the authority of an epoch does above."  And, for the
register algorithm: "That decision stage is also monotone, so it needs no
commitment and never decides two values …"  First conjunct: the queue, as a spec
from sets of requests to request sequences, is `tobSpec`, which is not
monotone, so some output needs a commitment (`pattern_consequences_neg`).
Second: `sp` is any upstream stage (for example the memory, whose outputs are
its responses); `d` is the processes' decisions as a monotone function of
those outputs (Proposition `prop:guard-test` via
`monotone_stage_proper`).  The modeling of shared memory as a single
participant, wait-freedom, crashes, and the cited results (Herlihy's
hierarchy and valency argument, the renaming bounds) are prose and citations,
not formalized. -/
theorem «app:additional-applications/shared-memory» {R : Type} [DecidableEq R] {a b : R}
    (hab : a ≠ b) {I M O : Type} [PO I] [PO M] [PO O]
    (sp : Spec I M) (d : M → O) (hd : ∀ m m', m ≼ m' → d m ≼ d m') :
    (¬ (tobSpec R).LiftedMono ∧
      ∃ τ : State (tobSpec R), ReachableCF τ ∧ ∃ o, τ.R τ.cur o ∧ ¬ Exposable τ o) ∧
    Guard.Proper sp (funSpec d) := by
  refine ⟨⟨(tob_not_liftedMono hab).2, ?_⟩, monotone_stage_proper sp d hd⟩
  obtain ⟨τ, hτ, o, ho, hne, _⟩ := (pattern_consequences_neg (tob_not_liftedMono hab).2 Unit).2.1
  exact ⟨τ, hτ, o, ho, hne⟩

/-- "With compare-and-swap, each process applies compare-and-swap with its
proposal to a location that starts empty, and its response names the value of
the first compare-and-swap, the same value in every response.  Each process
decides the value in its response.  That decision stage is a monotone function
of the object's responses, so it needs no commitment on them (Proposition
`prop:guard-test`), and the object's ordering is the only commitment the
pipeline needs (Theorem `thm:sufficient-guards`)."  The object is any upstream stage `sp` whose
outputs are response maps (a partial map from processes to the value named in
their response, ordered by extension) in which all responses name the same
value; the decision stage is the identity on response maps.  Conclusions: the
decision stage needs no commitment (`Guard.Proper`), and no two processes decide different values.  Wait-free
termination and the test-and-set algorithm are prose, not formalized. -/
theorem «app:additional-applications/cas-positive» {I P V : Type} [PO I]
    (sp : Spec I (PMap P V))
    (hagree : ∀ i m, sp.P i m → ∀ p q a b, m.f p = some a → m.f q = some b → a = b) :
    Guard.Proper sp (funSpec (fun m : PMap P V => m)) ∧
      ∀ i m, sp.P i m → ∀ p q a b,
        (funSpec (fun m : PMap P V => m)).P m m → m.f p = some a → m.f q = some b → a = b :=
  ⟨monotone_stage_proper sp _ (fun _ _ h => h), fun i m hm p q a b _ => hagree i m hm p q a b⟩

/-! ## Leader election -/

/-- "Its input is the set of candidates heard so far, ordered by inclusion,
and an output is `⊥`, for no leader yet, or a candidate heard, ordered with `⊥`
below every leader and leaders incomparable."  The output order. -/
theorem «app:additional-applications/leader-order» (x y : Flat Nat) :
    x ≼ y ↔ x.v = none ∨ x = y :=
  Iff.rfl

/-- "The spec one would write first gives the expected answer.  …  Two
candidates, each elected at the input where only it has been heard, have no
common output extension at the input where both have been heard.  So the spec
is not monotone, and by Theorem `thm:complete-cap` no system has Availability
for `P` and Partition Consistency."  The two candidates are `1` and `2`. -/
theorem «app:additional-applications/leader-unlisted» (D : Type) :
    (∀ S o, leaderSpec.P S o ↔ o.v = none ∨ ∃ l, o.v = some l ∧ S.1 l) ∧
    ¬ leaderSpec.LiftedMono ∧
      ¬ ∃ Sys : CAP.System leaderSpec D, CAP.Availability Sys ∧ CAP.PartitionConsistency Sys :=
  ⟨fun _ _ => Iff.rfl, leader_not_monotone D⟩

/-- "Including the list of all participants in the input, the `All` relation
of Ameloot et al. (Section `sec:systems`), changes the answer.  The input then
also records, for some of the listed participants, whether each is a
candidate, and inputs are ordered by extension of these records.  The spec is
functional.  Its output is the largest candidate once every listed
participant has reported, or `⊥` if there is none, and `⊥` before that.  The
spec is monotone, since more input never changes a report already received,
so once every participant has reported the output is fixed.  By Functional
CALM (Theorem `thm:functional-calm`), its runs are consistent, and electing
the largest candidate needs no commitment."  The list `All` is a parameter of
the spec, so it is the same in every row; participants are identified by
natural numbers, and a record is a partial map to `Bool` (candidate or not).
The remarks on waiting for evidence, the ring algorithms, availability, Raft,
and the comparison with Ameloot et al. and with Baccaert and Ketsman's results
(their Prop. 37, Ex. 6, Thm. 1) are prose and citations, not formalized. -/
theorem «app:additional-applications/leader-listed» (All : List Nat) :
    (∀ x o, (leaderAllSpec All).P x o ↔ o = maxLeader All x) ∧
    (leaderAllSpec All).Functional ∧ (leaderAllSpec All).MonotoneF ∧
    (leaderAllSpec All).Consistent ∧ (leaderAllSpec All).LiftedMono :=
  ⟨fun _ _ => Iff.rfl, leaderAllSpec_functional All, leaderAll_mono All,
    leaderAll_consistent All⟩

/-! ## Snapshots -/

/-- "For a scan `s` of a history `h`, a cut for `s` is a set `C` of updates of
`h` that is causally closed among updates, contains every update causally
before `s`, and contains no update causally after `s`."  Events are labeled
by participant (`proc`) and kind (`scan`); updates are the events that are
not scans. -/
theorem «app:additional-applications/cut» {Ev : Type} (scan : Ev → Prop) (h : Hist Ev)
    (s : Ev) (C : ESet Ev) :
    ClCut scan h s C ↔
      (∀ u, C.mem u → h.s.1 u ∧ ¬ scan u) ∧
      (∀ u w, C.mem w → ¬ scan u → h.lt u w → C.mem u) ∧
      (∀ u, ¬ scan u → h.lt u s → C.mem u) ∧
      (∀ u, C.mem u → ¬ h.lt s u) :=
  Iff.rfl

/-- "A view of participant `p` at `h` assigns a cut to each scan of `p` in `h`,
and views are ordered by extension.  The global-snapshot spec is the product
interface of these views (Appendix `app:rtc`): its outputs are partial tuples
with one view per participant." -/
theorem «app:additional-applications/global-snapshot-spec» {Ev : Type} {n : Nat}
    (proc : Ev → Fin n) (scan : Ev → Prop) :
    (∀ (p : Fin n) h (v : PMap Ev (ESet Ev)), ClView proc scan p h v ↔
      (∀ s, v.f s ≠ none ↔ ScanOf proc scan h p s) ∧ ∀ s C, v.f s = some C → ClCut scan h s C) ∧
    (clSpec proc scan).P = Deploy.prodTable (fun p h v => ClView proc scan p h v) :=
  ⟨fun _ _ _ => Iff.rfl, rfl⟩

/-- **Prop. `prop:snapshots`** (Global and atomic snapshots).  "(1) The
global-snapshot spec is monotone across partitions under the owner
deployment.  (2) The atomic snapshot is the strengthening of the
global-snapshot spec that selects the tuples of views explained by one strict
total order `L` of all events of the input that extends causal precedence: the
view of each scan is the set of updates before it in `L`.  With two
participants that can each perform an update and then a scan, it is not
monotone across partitions under the owner deployment."  Proof of (1): "The views of a participant at one input are
defined on the same scans, so they form an antichain, and the updates
causally before a scan form a cut for it, so views exist.  By Theorem
`thm:product-frontier`(1), it suffices that views continue.  An input
extension adds nothing to the causal past of an old event, so the cut of an
old scan is still a cut for it.  A new scan can take as its cut the updates
causally before it."  Proof of (2): "The updates before a scan in such an `L`
form a cut for it, since `L` extends causal precedence, so the selected tuples
are tuples of views.  Let participant `p` perform update `u_p` and then scan
`s_p`, and let `q` perform `u_q` and then `s_q`, with no messages between
them.  The answer `{u_p}` to `s_p` is explained by the order
`u_p s_p u_q s_q`, and the answer `{u_q}` to `s_q` by `u_q s_q u_p s_p`.  An
order explaining both would place `u_p` before `s_p`, `s_p` before `u_q`,
`u_q` before `s_q`, and `s_q` before `u_p`.  So the two answers, emitted by
`p` and `q` on two sides of a partition, have no common output extension."
Part (2) holds for every event universe with two participants that contains
such four events (`Four`); the atomic snapshot is `atSpec`, whose rows are the
restrictions of the tuples `atomicStr` selects. -/
theorem «prop:snapshots» {Ev : Type} :
    (∀ {n : Nat} (proc : Ev → Fin n) (scan : Ev → Prop),
      Deploy.Antichain (W := fun _ : Fin n => PMap Ev (ESet Ev))
        (fun p h v => ClView proc scan p h v) ∧
      (∀ p h, ∃ v, ClView proc scan p h v) ∧
      Deploy.Continue (W := fun _ : Fin n => PMap Ev (ESet Ev))
        (fun p h v => ClView proc scan p h v) ∧
      Deploy.MonoAcrossPartitions (Deploy.ownerD (clSpec proc scan))) ∧
    (∀ {n : Nat} (proc : Ev → Fin n) (scan : Ev → Prop) (h : Hist Ev) L (p : Fin n),
      LinExt h L → ClView proc scan p h (atomicView proc scan h L p)) ∧
    (∀ (proc : Ev → Fin 2) (scan : Ev → Prop), Four proc scan →
      ¬ Deploy.MonoAcrossPartitions (Deploy.ownerD (atSpec proc scan))) :=
  ⟨fun proc scan => ⟨cl_antichain proc scan, cl_nonempty proc scan, cl_continue proc scan,
      cl_monoAcross proc scan⟩,
   fun proc scan h L p hL => atomicView_cl proc scan h L hL p,
   fun _ _ w => atomic_not_monoAcross w⟩

/-- "By Proposition `prop:deployment-complete-cap`, the owner deployment's
canonical system for the global-snapshot spec has Deployment Availability and
Partition Consistency, and no system for the atomic snapshot has both.  The
global-snapshot spec permits the two answers of the proof together."  The
first conjunct needs at least two participants.  The cited wait-free
implementations of atomic snapshots, and the remark that the memory makes the
commitments, are not formalized. -/
theorem «app:additional-applications/snapshot-cap» {Ev : Type} (D : Type) :
    (∀ {n : Nat} (proc : Ev → Fin n) (scan : Ev → Prop), 2 ≤ n →
      ∃ Sys : CAP.System (clSpec proc scan) D,
        Deploy.DeploymentAvailability Sys (Deploy.ownerD (clSpec proc scan)) ∧
        Deploy.PartitionConsistencyAt Sys n) ∧
    (∀ {proc : Ev → Fin 2} {scan : Ev → Prop} (w : Four proc scan),
      (¬ ∃ Sys : CAP.System (atSpec proc scan) D,
        Deploy.DeploymentAvailability Sys (Deploy.ownerD (atSpec proc scan)) ∧
        Deploy.PartitionConsistencyAt Sys 2) ∧
      (clSpec proc scan).P w.hist ⟨fun p => some (w.y p)⟩) :=
  ⟨fun proc scan hn => cl_cap proc scan hn D, fun w => ⟨atomic_no_cap w D, w.cl_row⟩⟩

/-! ## Queues -/

/-- "An output is a dequeue history `(D,<)`, a partially ordered
history of dequeue events: a set `D` of the enqueued items dequeued so far,
with a strict order `<` on `D` that the queue guarantees among them.  Dequeue
histories are ordered by prefix: `(D,<) ⪯ (D',<')` when `D ⊆ D'`, the order `<'` agrees
with `<` on `D`, and no item of `D' ∖ D` comes before an item of `D` under
`<'`.  On totally ordered histories this is the usual prefix order."  (Strictness is a hypothesis where it is used.) -/
theorem «app:additional-applications/dequeue-report» {Ev : Type} (x y : DReport Ev) :
    x ≼ y ↔ (∀ a, x.D a → y.D a) ∧ (∀ a b, x.D a → x.D b → (x.lt a b ↔ y.lt a b)) ∧
      ∀ a b, x.D b → y.lt a b → x.D a :=
  Iff.rfl

/-- "The causal queue permits at `h` the dequeue histories `(D,→)` in which `D` is a
causally closed set of items of `h` and `→` is causal precedence restricted to
`D`." -/
theorem «app:additional-applications/causal-queue-spec» {Ev : Type} (h : Hist Ev)
    (x : DReport Ev) :
    (cqSpec Ev).P h x ↔ (∀ a, x.D a → h.s.1 a) ∧ (∀ a b, x.D b → h.lt a b → x.D a) ∧
      ∀ a b, x.lt a b ↔ (x.D a ∧ x.D b ∧ h.lt a b) :=
  Iff.rfl

/-- **Prop. `prop:causal-queue`** (Causal queue).  "(1) The causal queue
satisfies Lifted Monotonicity.  (2) Consider any spec with these inputs and
outputs whose fiber at `h` is directed, and which permits at `h`, for each
item `b` of `h`, a dequeue history whose set consists of `b` and the items causally
before it.  Every order that a dequeue history it permits at `h` guarantees between
two distinct items of `h` is causal precedence.  (3) Consider a spec that satisfies Lifted
Monotonicity.  Suppose that its dequeue histories list only items of the input, contain
every item causally before a listed one, order every causally ordered pair of
listed items causally, and never place an item before itself, and that every
causally closed set of items is the set of some dequeue history it permits.  Then it
permits exactly the dequeue histories of the causal queue."  Proof: "(1) We check the
common-extension condition.  Given rows `(h_r,(D_r,→))` with a common input
extension `j`, the union `D` of the `D_r` is causally closed in `j`, and
`(D,→)` extends each `(D_r,→)`: causal precedence on `D_r` is the same in
`h_r` and `j`, and an item causally before an item of `D_r` lies in `D_r`.
(2) Suppose a permitted dequeue history `(D,<)` has `a<b` with `a ≠ b`, and `a` is not
causally before `b`.  Let `(D_b,<_b)` be a permitted dequeue history whose set consists
of `b` and the items causally before it, so `a ∉ D_b`.  A common output
extension `(D'',<'')` in the fiber has `a <'' b` with `b ∈ D_b`, so `a` comes
before an item of `D_b`, and the prefix order forces `a ∈ D_b`, a
contradiction.  (3) A spec that satisfies Lifted Monotonicity has directed
fibers, and the set consisting of an item and the items causally before it is
causally closed.  So by (2) and the remaining hypotheses, each permitted
dequeue history orders exactly the causally ordered pairs of its causally closed set,
and is a dequeue history of the causal queue.  Conversely, a dequeue history `(D,→)` of the
causal queue has the same set as some permitted dequeue history, which by the same
argument is `(D,→)`."  In (2), `below h b` is `b` with its causal past. -/
theorem «prop:causal-queue» {Ev : Type} :
    (cqSpec Ev).LiftedMono ∧
    (∀ (T : Spec (Hist Ev) (DReport Ev)) (h : Hist Ev),
      JointLift (T.P h) (T.P h) → (∀ b, h.s.1 b → ∃ x, T.P h x ∧ x.D = below h b) →
      ∀ {x : DReport Ev} {a b : Ev}, T.P h x → x.lt a b → a ≠ b → h.s.1 b → h.lt a b) ∧
    (∀ T : Spec (Hist Ev) (DReport Ev), T.LiftedMono →
      (∀ h x, T.P h x → ∀ a, x.D a → h.s.1 a) →
      (∀ h x, T.P h x → ∀ a b, x.D b → h.lt a b → x.D a) →
      (∀ h x, T.P h x → ∀ a b, x.D a → x.D b → h.lt a b → x.lt a b) →
      (∀ h x, T.P h x → ∀ a, ¬ x.lt a a) →
      (∀ h (D : Ev → Prop), (∀ a, D a → h.s.1 a) → (∀ a b, D b → h.lt a b → D a) →
        ∃ x, T.P h x ∧ x.D = D) →
      ∀ h x, T.P h x ↔ (cqSpec Ev).P h x) :=
  ⟨cqSpec_liftedMono, fun T h hdir hdown _ _ _ hx hab hne hb =>
      directed_orders_causal T h hdir hdown hx hab hne hb,
   fun T hT hs hc hf hi ha => cq_unique T hT hs hc hf hi ha⟩

/-- "Under it, a spec that guarantees any order between two concurrent items
has a fiber that is not directed, so it is not monotone.  A queue that guarantees
a total dequeue order is one example." -/
theorem «app:additional-applications/queue-total» {Ev : Type} (T : Spec (Hist Ev) (DReport Ev))
    (h : Hist Ev) (hdown : ∀ b, h.s.1 b → ∃ x, T.P h x ∧ x.D = below h b)
    {a b : Ev} (ha : h.s.1 a) (hb : h.s.1 b) (hne : a ≠ b)
    (hca : ¬ h.lt a b) (hcb : ¬ h.lt b a)
    {x : DReport Ev} (hx : T.P h x) (hord : x.lt a b ∨ x.lt b a) :
    ¬ JointLift (T.P h) (T.P h) ∧ ¬ T.LiftedMono :=
  total_report_not_directed T h hdown ha hb hne hca hcb hx hord

/-! ## Search structures -/

/-- **Prop. `prop:persistent-forwarding`** (Persistent forwarding).  "Under
(1)–(3), every claim valid at `h` is valid at every input extension of `h`."
Proof: "By induction on the history it suffices to treat one step.  We show,
by induction on `n`, that if the search for `k` from `π` reaches an occurrence
of `k` after `n` edges before the step, then after the step it reaches a
current occurrence of `k`.  If `n = 0`, `π` held `k`, and (3) applies.
Otherwise let `π → π'` be the first edge.  By (2), the search from `π` after
the step reaches a position `ρ` that the search from `π'` reached before it.
Before the step, each position had at most one search edge for `k` and the
search stopped at the occurrence, so `ρ` lies on the path from `π'` to the
occurrence, fewer than `n` edges from it.  By induction, the search from `ρ`
after the step reaches a current occurrence, and so does the search from
`π`."  The structure is modeled as in `Appendix/Frontiers.lean`
(`Front.Restructuring`): key-indexed search edges and occurrences, with
obligation (1) built into the fixed position type.  `Front.Obligations`
records the two setup assumptions (`det`: at most one search edge per key;
`stop`: an occurrence has no search edge for its key) with (2) (`edges`) and
(3) (`occs`); the induction on `n` is `Front.claims_step`.  The child/link
distinction is needed only for exact claims, which are an arbitrary table of
valid claims below. -/
theorem «prop:persistent-forwarding» {K P : Type} (Rs : Front.Restructuring K P)
    {h h' : Rs.Hist} (hle : h ≼ h') : ∀ k p, Rs.R h k p → Rs.R h' k p :=
  Front.persistent_forwarding Rs hle

/-- "Condition (2) does not ask that the search from `π` still reach `π'`.
Posting a new node's separator into its parent changes the parent's search
edge for some keys from the old child to the new node, which lies to the right
of the old child, so the search no longer reaches the old child."  A posting
step of the B-link model (`BLink.post_breaks_strong`, on the reachable tree
`BLink.s3`) after which the search for key `4` from node `2` no longer reaches
`0`, its search edge before the step.  "It reaches the new node, which the old
search reached through the old child's right link" holds because the step
satisfies the obligations (`BLink.oblig_step`). -/
theorem «app:additional-applications/posting-weak» :
    BLink.Star BLink.BStep BLink.St.init BLink.s3 ∧ BLink.BStep BLink.s3 (BLink.s3.addPost 3) ∧
      (BLink.St.snap BLink.s3).edge 4 2 0 ∧
      ¬ Front.Path (BLink.St.snap (BLink.s3.addPost 3)) 4 2 0 :=
  BLink.post_breaks_strong

/-- "For a map `V` that gives a set `V(h)` of claims at each input, the spec
bounded by `V` permits at `h` every set of claims contained in `V(h)`, ordered
by inclusion." -/
theorem «app:additional-applications/bounded-spec» {I C : Type} [PO I] (V : I → C → Prop)
    (h : I) (S : ESet C) : (boundSpec V).P h S ↔ ∀ c, S.mem c → V h c :=
  Iff.rfl

/-- **Prop. `prop:remembered-claims`** (Remembered claims).  "(1) The spec
bounded by `V` satisfies Lifted Monotonicity if and only if `h ⊑ h'` implies
`V(h) ⊆ V(h')`.  (2) Let `X̂(h)` be the set of claims exact at some input below
`h`.  The spec bounded by `X̂` satisfies Lifted Monotonicity, and every map
`V ⊇ X` for which the spec bounded by `V` does has `X̂ ⊆ V`.  (3) Let `X̃(h)` be
the set of claims exact at some input below an input whose current structure
is that of `h`.  The spec bounded by `X̃` satisfies Lifted Monotonicity, and
every map `V ⊇ X` that depends only on the current structure, and for which
the spec bounded by `V` satisfies Lifted Monotonicity, has `X̃ ⊆ V`.  (4)
Valid claims contain `X̃`, and they equal `X̃` at every input if and only if
every valid claim at every input is in `X̃`."  Proof: "(1) First assume
Lifted Monotonicity.  A claim `c ∈ V(h)` gives the row `(h,{c})`, which has an
output extension at `h'`, so `c ∈ V(h')`.  Now assume that `V` grows.  The
union of finitely many sets permitted at inputs below `h'` is contained in
`V(h')`.  (2) `X̂` grows by construction.  A claim exact at `h₀ ⊑ h` lies in
`V(h₀)`, and so in `V(h)` by (1).  (3) Whether a history can be continued by
a step depends only on its current structure.  So if `h₀` lies below an input
`h'` with the structure of `h`, and `h` grows to `k`, then `h'` grows to an
input with the structure of `k`, and `h₀` lies below it.  Hence `X̃` grows.
For `V` as in (3), a claim exact at `h₀ ⊑ h'` lies in `V(h')` by (1), and
`V(h') = V(h)`.  (4) The valid claims depend only on the current structure,
contain `X`, and grow by Proposition `prop:persistent-forwarding`, so (3)
applies."  (2) and (3) are stated for any input order; (3) assumes, as the
proof says, that continuations depend only on the current structure
(`StateDet`), which holds for restructuring histories (`restr_stateDet`).  A
map that "depends only on the current structure" is `F (g h)`.  In (4), `X`
is any table of valid claims (exact claims are valid). -/
theorem «prop:remembered-claims» :
    (∀ {I C : Type} [PO I] (V : I → C → Prop), (boundSpec V).LiftedMono ↔ Grows V) ∧
    (∀ {I C : Type} [PO I] (X : I → C → Prop),
      (boundSpec (remembered X)).LiftedMono ∧
      ∀ V : I → C → Prop, (∀ i c, X i c → V i c) → (boundSpec V).LiftedMono →
        ∀ i c, remembered X i c → V i c) ∧
    (∀ {I C S : Type} [PO I] (g : I → S), StateDet g → ∀ X : I → C → Prop,
      (boundSpec (stateRemembered g X)).LiftedMono ∧
      ∀ F : S → C → Prop, (∀ i c, X i c → F (g i) c) →
        (boundSpec (fun i => F (g i))).LiftedMono →
        ∀ i c, stateRemembered g X i c → F (g i) c) ∧
    (∀ {K P : Type} (Rs : Front.Restructuring K P) (X : Rs.Hist → K × P → Prop),
      (∀ h c, X h c → fwdV Rs h c) →
      (∀ h c, stateRemembered (curSnap Rs) X h c → fwdV Rs h c) ∧
      ((∀ h c, fwdV Rs h c ↔ stateRemembered (curSnap Rs) X h c) ↔
        (∀ h c, fwdV Rs h c → stateRemembered (curSnap Rs) X h c))) :=
  ⟨fun V => boundSpec_liftedMono_iff V,
   fun X => ⟨(boundSpec_liftedMono_iff _).2 (remembered_grows X),
     fun V hXV hV => remembered_least X V hXV ((boundSpec_liftedMono_iff V).1 hV)⟩,
   fun g hdet X => ⟨(boundSpec_liftedMono_iff _).2 (stateRemembered_grows g hdet X),
     fun F hX hF => stateRemembered_least g X F hX ((boundSpec_liftedMono_iff _).1 hF)⟩,
   fun Rs X hX => ⟨fwd_contains_stateRemembered Rs X hX, fwd_eq_iff Rs X hX⟩⟩

/-- "By (4), forward-reachability lookup is the strongest lookup that depends
only on the structure and satisfies Lifted Monotonicity exactly when every
valid claim was exact at some earlier point of some history that reaches the
same structure."  Restated: the valid claims equal the least state-determined
growing map containing the exact claims (Prop. `prop:remembered-claims`(3))
exactly under that condition. -/
theorem «app:additional-applications/forwarding-frontier» {K P : Type}
    (Rs : Front.Restructuring K P) (X : Rs.Hist → K × P → Prop)
    (hX : ∀ h c, X h c → fwdV Rs h c) :
    (boundSpec (fwdV Rs)).LiftedMono ∧
    ((∀ h c, fwdV Rs h c ↔ stateRemembered (curSnap Rs) X h c) ↔
      (∀ h c, fwdV Rs h c → stateRemembered (curSnap Rs) X h c)) :=
  ⟨(boundSpec_liftedMono_iff _).2 (fwdV_grows Rs), fwd_eq_iff Rs X hX⟩

/-- "Each step satisfies (1)–(3), and searches stop at leaves."  The model
`BLink.St`, `BLink.BStep` (insert, half-split, post, grow), on well-formed
trees (`BLink.WF`, preserved by steps). -/
theorem «app:additional-applications/blink-steps» {s s' : BLink.St} (hs : BLink.WF s)
    (h : BLink.BStep s s') : Front.Obligations (BLink.St.snap s) (BLink.St.snap s') :=
  BLink.oblig_step hs h

/-- **Prop. `prop:blink`** (B-link trees).  "In the B-link tree model, every
claim valid at `h` lies in `X̃(h)`.  So the valid claims equal `X̃`, and
forward-reachability lookup is the strongest lookup that depends only on the
current structure and satisfies Lifted Monotonicity."  Proof sketch as in the
paper: `BLink.valid_facts`, `BLink.cut` (with `cut_wf`, `cut_sub`,
`cut_exact`), `BLink.complete`, giving `BLink.blink_H`; histories are
sequences of trees (`BLink.SRestr`), since exact claims need the child/link
distinction.  Lean states the first two sentences; the third is
Prop. `prop:remembered-claims`(3). -/
theorem «prop:blink» :
    (∀ h c, BLink.blink.fwdV h c → stateRemembered BLink.blink.cur BLink.exactX h c) ∧
    (∀ h c, BLink.blink.fwdV h c ↔ stateRemembered BLink.blink.cur BLink.exactX h c) :=
  ⟨BLink.blink_H, BLink.blink_fwd_eq⟩

end Paper
end CC
