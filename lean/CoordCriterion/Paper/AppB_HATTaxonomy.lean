import CoordCriterion.Instances.HATAppB
import CoordCriterion.Instances.HATWriteSkew

/-!
# Paper App. F, subsection "The HAT taxonomy" (`appendices/instances.tex`, `app:hat-taxonomy`)

Statement layer for subsection `app:hat-taxonomy` of
`appendices/instances.tex`.  Read it side by side with the `.tex`:
entries follow the paper's paragraphs in order; each quotes the claim it
formalizes.  Unlabeled claims are named `«app:hat-taxonomy/<slug>»`.

Library: `Instances/HATTaxonomy.lean` (model, phenomena, specifications),
`Instances/HATTaxonomyRules.lean` (reveal rules, positive results),
`Instances/HATTaxonomyWitness.lean` (negative results), `Instances/HATAppB.lean`
(the algorithm for monotonic atomic view), `Instances/HATWriteSkew.lean`, all
in namespace `CC.HATTax` (Write Skew in `CC.HATSpec.WS`).  The parameter
`reps : Nat → List Nat` gives each item's replicas; `lam = true` imposes the
timestamp condition of Theorem `thm:hat-levels`.
-/

namespace CC
namespace Paper

open CC.HATTax

set_option linter.unusedSectionVars false

/-! ## Introduction and inputs -/

/-- Opening paragraph: "Bailis et al. classify transactional guarantees by what a system can
provide while every client that can reach a replica keeps getting answers.  The
extended paper defines each guarantee by the anomaly it rules out and gives
algorithms for the guarantees that can be provided.  We use those definitions
and algorithms as written, except that where a definition disagrees with its
own example, we follow the example."

Paragraph "Inputs and outputs": "The inputs extend the histories of Definition
`def:hat-spec`.  Each item has a fixed set of replicas, and a read is served by
a replica of its item.  A *predicate read* reads a fixed range of items at once
and returns a version of each.  A transaction's reads are ordered.  A client
runs one transaction at a time.  Its transactions form its *session*, and its
commit timestamps increase along the session.  Outputs are sets of read
answers, as before."

Lean: an input is a `HATSpec` history with the conditions `HATTax.Sess reps`
(fields `rd_rep`, `prd_rep`: reads at replicas of their items; `prd_before`:
predicate reads precede their commit; `txn_order`: a transaction's reads are
ordered; `seq`: one transaction at a time; `sess_ts`: increasing commit
timestamps along a session).  A predicate read is the event `.prd c n ks r`
over the fixed item list `ks`. -/
abbrev «app:hat-taxonomy/inputs» (reps : Nat → List Nat) (lam : Bool) : Type :=
  HATTax.SInp reps lam

/-- Paragraph "Guarantees": "Each guarantee rules out one anomaly of the
extended paper: a pattern in a graph whose nodes are transactions.  The edges
are the write-, read-, and anti-dependencies of Adya on each item, and session
edges from each transaction to its client's later ones.  For example, read your
writes rules out a transaction that reads a version of `x` older than one that
an earlier transaction of the same client wrote.  The extended paper gives no
formal definition of recency.  We take it to require that a read return a
version at least as new as every write by another transaction whose commit
happens before the read.  Because a replica can return only versions it
holds, the *visibility store* permits an answer only if its version is the
initial one or arrived at the reading replica before the read."

Lean: the edges are `HATSpec.wwI`, `HATTax.wr2`, `HATTax.rw2` and `HATTax.sess`;
each guarantee's anomaly is `HATTax.Phen g`; read your writes is `HATTax.MYR`,
recency `HATTax.Recency`; the visibility store is `HATTax.vstore`, whose
condition is `HATTax.Vis`. -/
theorem «app:hat-taxonomy/guarantees» {reps : Nat → List Nat} {lam : Bool}
    (j : SInp reps lam) (o : IConf.St Fact2) :
    (vstore (reps := reps) (lam := lam)).P j o ↔
      ∀ e k v, o (.rv e k v) → ∃ c n r, Acc j.1 e c n k r ∧
        (v = HATRC.tsInit ∨ ∃ d c' n' f ks, j.1.lab d = some (.dl c' n' k r) ∧ j.1.lt d e ∧
          j.1.lab f = some (.cm c' n' v ks)) :=
  Iff.rfl

/-- **Definition `def:hat-availability`** (Guarantee spec, high availability,
sticky read, sticky availability).  "For a guarantee `G`, the table of `𝒮_G`
contains an output at an input when the visibility store permits the output and
the input extends to a complete history that includes the output and has no
anomaly that `G` rules out.  The guarantee `G` is *highly available* when some
explicit relation `E ⊆ P_G` answers every read and some system for `𝒮_G` has
Availability for `E` and Partition Consistency.  A read is *sticky* when its
replica has received every write of the client's earlier transactions to the
items that replica holds.  The guarantee `G` is *sticky available* when the
same holds for an `E` that answers every sticky read."

Lean: `𝒮_G` is `HATTax.tax G`, the intersection of `HATTax.vstore` with
`HATTax.gspec G`; high availability is `HATTax.HighlyAvailable`, a sticky read
is `HATTax.Reflects`, and sticky availability is `HATTax.StickyAvailable`. -/
theorem «def:hat-availability» {reps : Nat → List Nat} {lam : Bool} (g : Guar) (D : Type) :
    (∀ j o, (tax (reps := reps) (lam := lam) g).P j o ↔
      (vstore (reps := reps)).P j o ∧ ∃ H : CH2 j, o ≼ H.facts ∧ ¬ Phen g j H) ∧
    (HighlyAvailable (reps := reps) (lam := lam) (tax g) D ↔
      ∃ E : Table (SInp reps lam) (IConf.St Fact2), (∀ i o, E i o → (tax g).P i o) ∧
        (∀ i, ∃ o, E i o) ∧ (∀ i o, E i o → AnswersAll i o) ∧
        ∃ Sys : CAP.System (tax g) D, CAP.AvailabilityFor E Sys ∧ CAP.PartitionConsistencyAtEnd Sys) ∧
    (StickyAvailable (reps := reps) (lam := lam) (tax g) D ↔
      ∃ E : Table (SInp reps lam) (IConf.St Fact2), (∀ i o, E i o → (tax g).P i o) ∧
        (∀ i, ∃ o, E i o) ∧ (∀ i o, E i o → AnswersSticky i o) ∧
        ∃ Sys : CAP.System (tax g) D, CAP.AvailabilityFor E Sys ∧ CAP.PartitionConsistencyAtEnd Sys) :=
  ⟨fun _ _ => Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- "Sticky availability follows Bailis et al.: a client gets answers whenever
its transaction runs against a copy of the database that reflects all of its
earlier operations.  By Theorem `thm:complete-cap` and Corollary
`cor:complete-cap-any-system`, `G` is highly available exactly when `𝒮_G`
satisfies Lifted Monotonicity for some `E ⊆ P_G` that answers every read, and
likewise for sticky availability."  Lean: `HATTax.highlyAvailable_iff` and
`HATTax.stickyAvailable_iff`, through `CAP.complete_cap_for`. -/
theorem «app:hat-taxonomy/complete-cap» {reps : Nat → List Nat} {lam : Bool}
    (sp : Spec (SInp reps lam) (IConf.St Fact2)) (D : Type) :
    (HighlyAvailable sp D ↔
      ∃ E : Table (SInp reps lam) (IConf.St Fact2), (∀ i o, E i o → sp.P i o) ∧ (∀ i, ∃ o, E i o) ∧
        (∀ i o, E i o → AnswersAll i o) ∧ CAP.ConsistentOn sp E) ∧
    (StickyAvailable sp D ↔
      ∃ E : Table (SInp reps lam) (IConf.St Fact2), (∀ i o, E i o → sp.P i o) ∧ (∀ i, ∃ o, E i o) ∧
        (∀ i o, E i o → AnswersSticky i o) ∧ CAP.ConsistentOn sp E) :=
  ⟨highlyAvailable_iff sp D, stickyAvailable_iff sp D⟩

/-! ## Reveal rules -/

/-- Paragraph "Reveal rules": "A transaction is *pending stable* before a read
when every replica of every item it wrote has received its write before the
read. … The *reveal rule* combines the three.  A write is revealed at a read
once its transaction and every transaction whose commit happens before its
commit are pending stable.  A transaction reads, for each item, the highest
version revealed at every one of its reads so far.  The *sticky reveal rule*
answers only sticky reads, and it also reveals the client's own earlier writes,
which a sticky read's replica holds."  (The elided sentences quote Bailis et
al.'s algorithms.)

Lean: pending stable is `HATTax.Stable`; the revealing condition is
`HATTax.DepStable` inside `HATTax.Rev s` (`s = true` adds the client's own
writes); the candidates are `HATTax.SnapC`; the rule's output is
`HATTax.outR s` (with `s = true` it answers only reads satisfying
`HATTax.Reflects`).  Both rules answer only with versions the replica holds,
answer every read (resp. every sticky read), and are monotone. -/
theorem «app:hat-taxonomy/reveal-rules» {reps : Nat → List Nat} {lam : Bool} (s : Bool) :
    (∀ j : SInp reps lam, (vstore (reps := reps) (lam := lam)).P j (outR s j)) ∧
    (∀ j : SInp reps lam, AnswersAll j (outR false j)) ∧
    (∀ j : SInp reps lam, AnswersSticky j (outR true j)) ∧
    (∀ i j : SInp reps lam, i ≼ j → outR s i ≼ outR s j) :=
  ⟨fun _ => outR_vis, outR_answers, outR_answersSticky, fun _ _ h => outR_mono h⟩

/-! ## Theorem `thm:hat-taxonomy` -/

/-- **Theorem `thm:hat-taxonomy`** (HAT taxonomy).  "(1) Under the timestamp
condition of Theorem `thm:hat-levels`, read committed and monotonic atomic
view are highly available.  Item cut isolation, predicate cut isolation,
monotonic reads, monotonic writes, and writes follow reads are highly
available.  (2) Read your writes, PRAM, and causal consistency are sticky
available and not highly available.  Given at least two participants and any
assignment of clients to them, consider the deployment that lets each client's
participant give the sticky reveal rule's answers to that client's reads.  Some
system has Deployment Availability and Partition Consistency for it.
(3) Recency is neither highly available nor sticky available.  For any level
that rules out Lost Update or Write Skew, no system has Availability for an
explicit relation that answers every read and Partition Consistency."

Lean: `«sec:hat-instance/session-guarantees»` collects the same results; here
they are stated item by item.  `lam = true` is the timestamp condition
(`HATTax.HAGuar lam` includes RC and MAV only then); the assignment of clients
is `srv`, the deployment `HATTax.stickyD`.  The negative results assume only
that item `0` has replica `0`.  Lost Update is `«thm:hat-levels»`; Write Skew
is `HATSpec.WS.writeSkew_unavailable`, for repeatable read and
serializability. -/
theorem «thm:hat-taxonomy» (reps : Nat → List Nat) (lam : Bool) (D : Type) :
    (∀ g, HAGuar lam g → HighlyAvailable (reps := reps) (lam := lam) (tax g) D) ∧
    (∀ g, (g = .RYW ∨ g = .PRAM ∨ g = .Causal) →
      StickyAvailable (reps := reps) (lam := lam) (tax g) D ∧
      (0 ∈ reps 0 → ¬ HighlyAvailable (reps := reps) (lam := lam) (tax g) D)) ∧
    (∀ g (hg : StickyGuar g) (n : Nat) (srv : Nat → Fin n), 2 ≤ n →
      ∃ Sys : CAP.System (tax (reps := reps) (lam := lam) g) D,
        Deploy.DeploymentAvailability Sys (stickyD hg srv) ∧ Deploy.PartitionConsistencyAt Sys n) ∧
    (0 ∈ reps 0 →
      ¬ HighlyAvailable (reps := reps) (lam := lam) (tax .Rec) D ∧
      ¬ StickyAvailable (reps := reps) (lam := lam) (tax .Rec) D) ∧
    (∀ (L : HATSpec.Level), (L = .RR ∨ L = .SER) →
      ∀ A : Table (HATSpec.Inp lam) (IConf.St HATSpec.Fact), (∀ i o, A i o → (HATSpec.spec L).P i o) →
        (∀ i, ∃ o, A i o) → (∀ i o e, A i o → HATSpec.IsRd i e → ∃ v, o (.read e v)) →
        ¬ ∃ Sys : CAP.System (HATSpec.spec L) D,
          CAP.AvailabilityFor A Sys ∧ CAP.PartitionConsistencyAtEnd Sys) :=
  ⟨fun _ hg => ha_of_rule hg D,
   fun g hg => ⟨sticky_of_rule (by
      rcases hg with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))) D,
     fun h0 => ryw_not_ha h0 hg D⟩,
   fun _ hg _ srv hn => stickyD_available hg hn srv D,
   fun h0 => ⟨recency_not_ha h0 D, recency_not_sticky h0 D⟩,
   fun L hL A hAS ht ha => (HATSpec.WS.writeSkew_unavailable L hL D A hAS ht ha).2⟩

/-- Proof of Theorem `thm:hat-taxonomy`, item (1): "The reveal rule answers every
read.  Each answer depends only on the read's past, so later input never changes
it, and the rule is monotone.  A monotone relation inside the spec satisfies
Lifted Monotonicity for itself: rows below `j` have the relation's own answer at
`j` as a common output extension.  The rule returns only versions the replica
holds, and its answers have none of the anomalies these guarantees rule out.
Consider monotonic reads.  If an earlier transaction of a client read a
version of `x`, that version was revealed.  It had then reached every replica
of `x`, so it stays revealed at every later read.  The client's later
transaction reads after the earlier one commits, so it reads that version of
`x` or a newer one.  For read committed and monotonic atomic view, the
timestamp condition rules out G1c, as in Theorem `thm:hat-levels`."

Lean: the rule's complete history `HATTax.ruleHist` has none of the anomalies
(`HATTax.rule_clean_ha`; monotonic reads is `HATTax.rule_NMR`); the rule is
inside each spec (`HATTax.outR_tax`) and consistent on its rows
(`HATTax.ruleE_consistent`). -/
theorem «thm:hat-taxonomy/proof-ha» {reps : Nat → List Nat} {lam : Bool} {g : Guar}
    (hg : HAGuar lam g) :
    (∀ j : SInp reps lam, ¬ Phen g j (ruleHist false j)) ∧
    (∀ j : SInp reps lam, (tax g).P j (outR false j)) ∧
    CAP.ConsistentOn (tax (reps := reps) (lam := lam) g) (ruleE false) :=
  ⟨rule_clean_ha hg, outR_tax (rule_clean_ha hg),
   ruleE_consistent _ (outR_tax (rule_clean_ha hg))⟩

/-- Proof of Theorem `thm:hat-taxonomy`, item (2): "The sticky reveal rule does
the same for every sticky read.  The deployment authorizes only answers of this
one monotone relation inside the spec, so it is monotone across partitions, and
Proposition `prop:deployment-complete-cap` gives the system.  Without
stickiness, consider a client that writes `x` at one replica and then reads `x`
at another replica that has not received the write.  That replica holds only
the initial version of `x`, which read your writes rules out.  No explicit
relation inside the spec answers the read.  PRAM and causal consistency include
read your writes."

Lean: `HATTax.rule_clean_sticky`, `HATTax.stickyD_monoAcross`; the input is
`HATTax.w1`, whose read is not sticky (`HATTax.w1_not_sticky`) and has no
permitted answer (`HATTax.ryw_no_answer`). -/
theorem «thm:hat-taxonomy/proof-sticky» {reps : Nat → List Nat} {lam : Bool} {g : Guar}
    (hg : StickyGuar g) (h0 : 0 ∈ reps 0) :
    (∀ j : SInp reps lam, ¬ Phen g j (ruleHist true j)) ∧
    (∀ {n : Nat} (srv : Nat → Fin n), Deploy.MonoAcrossPartitions (stickyD (reps := reps) (lam := lam) hg srv)) ∧
    ¬ Reflects (reps := reps) (w1 (lam := lam) h0).1 1 1 0 ∧
    (∀ o, (tax (reps := reps) (lam := lam) .RYW).P (w1 h0) o → ∀ v, ¬ o (.rv 1 0 v)) :=
  ⟨rule_clean_sticky hg, fun srv => stickyD_monoAcross hg srv, w1_not_sticky h0,
   fun _ ho v => ryw_no_answer h0 ho v⟩

/-- Proof of Theorem `thm:hat-taxonomy`, item (3): "For recency, another
client's write of `x` commits before a read but never reaches the reading
replica, which again holds only the initial version.  The read is sticky, so
stickiness does not help.  For Write Skew, two transactions at partitioned
replicas each read the item the other writes.  Each replica can return only the
initial version, and together the answers form the cycle that Write Skew names,
as for Lost Update in Theorem `thm:hat-levels`."

Lean: the input `HATTax.w2` (`HATTax.recency_no_answer`); for Write Skew,
each side's only visible answer is the initial version (`HATSpec.WS.wi1_ver`,
`HATSpec.WS.wi2_ver`) and the joined answers form the cycle
(`HATSpec.WS.ws_cycle`). -/
theorem «thm:hat-taxonomy/proof-unavailable» {reps : Nat → List Nat} {lam : Bool} (h0 : 0 ∈ reps 0) :
    (∀ o, (tax (reps := reps) (lam := lam) .Rec).P (w2 h0) o → ∀ v, ¬ o (.rv 1 0 v)) ∧
    (∀ v, HATSpec.Ver (HATSpec.WS.wi1 (lam := lam)) 1 1 1 v → v = HATRC.tsInit) ∧
    (∀ v, HATSpec.Ver (HATSpec.WS.wi2 (lam := lam)) 2 1 0 v → v = HATRC.tsInit) :=
  ⟨fun _ ho v => recency_no_answer h0 ho v, fun _ h => HATSpec.WS.wi1_ver h,
   fun _ h => HATSpec.WS.wi2_ver h⟩

/-! ## The algorithm for monotonic atomic view -/

/-- Paragraph "The algorithm for monotonic atomic view": "A replica keeps a
write in a *pending* set until it has received acknowledgments from every
replica of the items its transaction wrote, and then moves it to a *good* set.
A read of `x` may carry a required timestamp.  Without one, the replica returns
its highest good version of `x`.  With one, it returns a good version at least
as new, or else the pending write with exactly that timestamp.  After each
read, the client raises the required timestamp of every item that the returned
write's transaction also wrote, and it clears these timestamps when the
transaction ends.  The input does not fix which acknowledgments a replica has
received, so each replica's good set may be any set of pending stable
transactions that depends only on the read's past.  The pending case returns
only a write whose transaction an earlier read of the same transaction found
good, so every answer is a version the replica holds."

Lean: the good sets are `K : HATTax.AckK reps` (fields `sound`: pending
stable; `loc`: depends only on the read's past); the answers are
`HATTax.bAns K` and the output `HATTax.outB K`.  Every non-initial answer is
pending stable (`HATTax.bAns_stable`), so the output is in the visibility store
(`HATTax.outB_vis`). -/
theorem «app:hat-taxonomy/mav-algorithm» {reps : Nat → List Nat} {lam : Bool} (K : AckK reps) :
    (∀ j : SInp reps lam, (vstore (reps := reps) (lam := lam)).P j (outB K j)) ∧
    (∀ j : SInp reps lam, AnswersAll j (outB K j)) :=
  ⟨outB_vis K, outB_answers K⟩

/-- **Proposition `prop:hat-mav-algorithm`** (The algorithm provides monotonic
atomic view).  "For every choice of the replicas' good sets, and under the
timestamp condition of Theorem `thm:hat-levels`, the answers of the algorithm
for monotonic atomic view form an explicit relation inside `P_MAV` that answers
every read and is monotone.  So monotonic atomic view is highly available."

Proof sketch: "Each answer depends only on the read's past, so the relation is
monotone, and it answers every read.  The timestamp condition rules out G1c, as
for read committed.  For the anomaly of monotonic atomic view, suppose a
transaction reads `x` from `T_j` and later reads `y`, which `T_j` also wrote.
The first read raised the required timestamp of `y` to `T_j`'s, so the second
read returns `T_j`'s version of `y` or a newer one.  Theorem `thm:complete-cap`
gives the system."  Lean: `HATTax.outB_tax_MAV` (through `HATTax.bHist_G1c`
and `HATTax.bHist_OTV`), `HATTax.outB_answers`, `HATTax.outB_mono`,
`HATTax.mav_appB`. -/
theorem «prop:hat-mav-algorithm» {reps : Nat → List Nat} (K : AckK reps) (D : Type) :
    (∀ j : SInp reps true, (tax (reps := reps) .MAV).P j (outB K j)) ∧
    (∀ j : SInp reps true, AnswersAll j (outB K j)) ∧
    (∀ i j : SInp reps true, i ≼ j → outB K i ≼ outB K j) ∧
    HighlyAvailable (reps := reps) (lam := true) (tax .MAV) D :=
  ⟨outB_tax_MAV K, outB_answers K, fun _ _ h => outB_mono K h, mav_appB K D⟩

/-! ## Differences in form -/

/-- Paragraph "Differences in form": "Our classification matches theirs and
differs in form in three ways.  First, our framework separates two reasons a
guarantee can be unavailable.  The unavailable isolation levels fail Lifted
Monotonicity: answers that the two sides give have no common extension.  Read
your writes without stickiness, and recency in every case, fail earlier.  Some
read has no permitted answer at all (items (2) and (3) of the proof of Theorem
`thm:hat-taxonomy`), so the question of Lifted Monotonicity never arises.
Second, monotonic writes needs the version order to follow each session's
order.  Bailis et al. obtain this from client timestamps, and our inputs assume
it.  Third, we model a predicate as a fixed range of items, and general
predicates, whose items depend on the data, are not modeled.  Bailis et al.
also list several recency guarantees without formal definitions, among them
bounds on staleness and safe, regular, and linearizable register semantics.  We
model only the recency guarantee defined above."
(The statements about Bailis et al.'s paper are prose-only.)

Lean: (1) on `HATTax.w1`, client 1's read of `x` is not sticky
(`HATTax.w1_not_sticky`) and no output that the read-your-writes spec permits
answers it (`HATTax.ryw_no_answer`); on `HATTax.w2`, the same holds for recency
although the read is sticky (`HATTax.recency_no_answer`); the isolation levels'
failure is the answer pair of `«thm:hat-levels/lost-update-pair»` and
`HATSpec.WS.ws_cycle`; (2) every taxonomy input has increasing commit
timestamps along each client's session (field `sess_ts` of `HATTax.Sess`);
(3) a predicate read `.prd c n ks r` names a fixed list of items `ks`, and
recency is the single phenomenon `HATTax.Recency`. -/
theorem «app:hat-taxonomy/form-choices» (reps : Nat → List Nat) (lam : Bool) (h0 : 0 ∈ reps 0) :
    (¬ HATTax.Reflects (reps := reps) (HATTax.w1 (lam := lam) h0).1 1 1 0 ∧
      ∀ o, (HATTax.tax (reps := reps) (lam := lam) .RYW).P (HATTax.w1 h0) o →
        ∀ v, ¬ o (.rv 1 0 v)) ∧
    (∀ o, (HATTax.tax (reps := reps) (lam := lam) .Rec).P (HATTax.w2 h0) o →
        ∀ v, ¬ o (.rv 1 0 v)) ∧
    (∀ (j : HATTax.SInp reps lam) {f f' c n n' t t' ks ks'},
      j.1.lab f = some (.cm c n t ks) → j.1.lab f' = some (.cm c n' t' ks') → j.1.lt f f' →
        HATRC.tsLt t t') :=
  ⟨⟨HATTax.w1_not_sticky h0, fun _ ho v => HATTax.ryw_no_answer h0 ho v⟩,
    fun _ ho v => HATTax.recency_no_answer h0 ho v,
    fun j => j.2.2.sess_ts⟩

/-! ## Differences from the extended paper's text

Not in the paper: this paragraph was removed from Appendix `app:hat-taxonomy`.
The entries below record the differences, which Lean still checks. -/

/-- Predicate cut isolation, read "for some": "Def. 24 (predicate cut isolation) says that a history has the
anomaly if, *for all* pairs of overlapping predicate reads in a transaction,
the transactions that change their matches differ.  That holds trivially for a
transaction with no such pair.  We read 'for some pair.'"  Lean: `HATTax.PMP`
is existential over the pair of predicate reads. -/
theorem «app:hat-taxonomy/pmp-for-some» {reps : Nat → List Nat} {lam : Bool} {j : SInp reps lam}
    (H : CH2 j) :
    PMP H ↔ ∃ e₁ e₂ c n r₁ r₂ ks₁ ks₂ t, j.1.lab e₁ = some (.prd c n ks₁ r₁) ∧
      j.1.lab e₂ = some (.prd c n ks₂ r₂) ∧ HATSpec.CTs j.inp c n t ∧
      ¬ ∀ u, (Chg H e₁ (ks₁.filter (· ∈ ks₂)) u ↔ Chg H e₂ (ks₁.filter (· ∈ ks₂)) u) :=
  Iff.rfl

/-- Monotonic atomic view, read literally: "Def. 26 (monotonic atomic view) asks for a read-dependency on `x`
and 'a set of edges by `y` containing at least one anti-dependency.'  Read
literally, this allows any path of edges on `y`, and the extended paper's own
algorithm produces such a path.  In one history, `T_j` writes `x` and `y`.  A
transaction `T_k` reads `y` before `T_j`'s writes are pending stable, so it gets
the initial version, and then writes `y` with a higher timestamp than `T_j`'s.
Then `T_i` reads `x` and `y`, both from `T_j`.  The read-dependency from `T_j`
to `T_i` on `x` and the anti-dependencies from `T_i` to `T_k` and from `T_k` to
`T_j` on `y` form a cycle of the literal shape, although `T_i` saw all of
`T_j`'s writes.  The definition also says that '`T_j`'s read from `y` precedes
its read from `x`,' while its example (Fig. 9) has `T_i` read `x` before `y`.
We follow the example: `T_i` reads `x` from `T_j` and later reads a version of
`y` older than `T_j`'s."

Lean: the literal reading is `HATTax.OTVlit`, which `HATTax.OTV` (the
example's form) implies (`HATTax.otv_lit`); on the input `HATTax.w5`, under the
timestamp condition, the algorithm's answers are in `P_MAV` and every complete
history with them exhibits `OTVlit` (`HATTax.appB_OTVlit`). -/
theorem «app:hat-taxonomy/otv-literal» :
    (∀ {reps : Nat → List Nat} {lam : Bool} {j : SInp reps lam} (H : CH2 j), OTV H → OTVlit H) ∧
    (tax (reps := r0) (lam := true) .MAV).P w5 (outB (stableK (reps := r0)) w5) ∧
    ∀ H : CH2 w5, outB (stableK (reps := r0)) w5 ≼ H.facts → OTVlit H :=
  ⟨fun H h => otv_lit H h, appB_OTVlit⟩

/-- Monotonic reads across intermediate versions: "Def. 28 (monotonic reads) describes a cycle of exactly a session
edge, an anti-dependency, and a read-dependency.  That misses a transaction
that reads a version two or more versions older than one its client read
earlier.  We allow write-dependencies between the anti-dependency and the
read-dependency."  Lean: `HATTax.NMR`, with `HATTax.RwWw` (an anti-dependency
followed by write-dependencies). -/
theorem «app:hat-taxonomy/nmr-intermediate» {reps : Nat → List Nat} {lam : Bool} {j : SInp reps lam}
    (H : CH2 j) :
    NMR H ↔ ∃ ti tj tl x e c n r, Relation.TransGen (sess (j := j)) ti tj ∧
      j.1.lab e = some (.rd c n x r) ∧ HATSpec.CTs j.inp c n tj ∧
      (∃ u, HATSpec.Next j.inp x (H.val e x) u ∧ (u = tl ∨ Relation.TransGen (HATSpec.wwI j.inp x) u tl)) ∧
      wr2 H x tl ti :=
  Iff.rfl

/-- Monotonic writes and its example: "Def. 30 (monotonic writes) requires a write-dependency edge, but
its example (Figs. 13 and 14) has none.  We also rule out the example's
anomaly."  Lean: `HATTax.NMW` is the definition as written (`HATTax.NMWlit`)
or the example's anomaly. -/
theorem «app:hat-taxonomy/nmw-example» {reps : Nat → List Nat} {lam : Bool} {j : SInp reps lam}
    (H : CH2 j) :
    NMW H ↔ NMWlit (j := j) ∨
      ∃ ti tj tk x y e c n r, Relation.TransGen (sess (j := j)) ti tj ∧ wr2 H y tj tk ∧
        j.1.lab e = some (.rd c n x r) ∧ HATSpec.CTs j.inp c n tk ∧ tk ≠ ti ∧ RwWw H x e ti :=
  Iff.rfl

/-- Writes follow reads, as we read it: "Def. 32 (writes follow reads) states the condition for the
anomaly's absence ('`T_3` does not directly anti-depend on `T_1`'), says
'write-depends' where its example has read-dependencies, and names the anomaly
MRWD, while Defs. 33 and 37 call it MWRD.  We read: `T_2` reads `x` from `T_1`,
`T_3` reads `y` from `T_2`, and `T_3` reads the version of `x` that `T_1`
overwrote."  Lean: `HATTax.MRWD`. -/
theorem «app:hat-taxonomy/mrwd-reading» {reps : Nat → List Nat} {lam : Bool} {j : SInp reps lam}
    (H : CH2 j) :
    MRWD H ↔ ∃ t₁ t₂ t₃ x y e c n r, wr2 H x t₁ t₂ ∧ wr2 H y t₂ t₃ ∧
      j.1.lab e = some (.rd c n x r) ∧ HATSpec.CTs j.inp c n t₃ ∧ t₃ ≠ t₁ ∧
      HATSpec.Next j.inp x (H.val e x) t₁ :=
  Iff.rfl

end Paper
end CC
