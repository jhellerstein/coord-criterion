I read the attached main.tex directly. For a tomorrow PODS deadline, I would not try to rethink the paper anymore. The core story is now coherent, and the running example is much improved. My last-minute advice is mostly about removing reviewer tripwires and avoiding claims that are stronger than you need.

I also checked the LaTeX source mechanically for duplicate labels and missing \refs: I found no duplicate labels and no missing internal refs. Older uploaded files in the conversation have expired, so this review is based only on the current attached file.

Executive judgment

The paper is now in a submit-able shape if you do a small cleanup pass. The key conceptual arc is clear:

1. specifications are histories → outcomes + refinement order;
2. monotonicity is the exact semantic coordination-free criterion;
3. the operational theorem ties this back to I/O automata;
4. distributed-monotonicity gives a CAP-style theorem;
5. known DB results become instances;
6. proper coordination/residual interfaces explain why coordinated layers can produce coordination-free downstream outputs.

That is a strong paper.

The biggest remaining risks are not fatal, but they are reviewer-facing:

* “linearizability” is defined using happens-before, which is stronger than standard Herlihy–Wing linearizability unless carefully phrased;
* the frontier appendix still makes maximality claims that are stronger than their proofs;
* a few proof sketches claim more than they establish, especially the operational theorem and separation from CALM;
* one appendix reference in the HAT proof appears misleading.

Below is the last-minute punchlist by priority.

⸻

P0 — Fix before submission

1. Clarify the linearizability definition in the running example

The new two-write/two-read example is good. It avoids the old pending-read problem. In fact, it is the right witness:

* r_p = 2 forces w_p < w_q;
* r_q = 1 forces w_q < w_p;
* contradiction.

However, the text says:

Under linearizability, outcomes are total orders on completed operations
consistent with happens-before...

Standard Herlihy–Wing linearizability requires consistency with real-time order of operation intervals, not arbitrary internal message happens-before. Your example actually works under standard real-time order because both writes complete before both reads begin, given the histories you wrote. You do not need the stronger “all happens-before” phrasing.

Recommended low-cost edit:

Under linearizability~\cite{herlihy1990linearizability}, outcomes are
total orders on completed operations consistent with real-time order
between operation intervals; in our histories this real-time order is
represented by the happens-before relation between invocation and
response events.

Then avoid implying internal propagation messages are themselves object-level ordering constraints. This will prevent the strongest possible distributed-systems objection.

Also revise this later phrase:

the only linearization consistent with happens-before

to:

the only linearization consistent with the completed operation
responses in this history

or:

the only linearization consistent with the operation-interval order
in this history

2. Fix the HAT proof reference

The proof heading says:

\begin{proof}[Proof (read committed; others in Appendix~\ref{app:hierarchy})]

But Appendix app:hierarchy is the CALM hierarchy appendix, not a proof of read uncommitted / monotonic reads / read-your-writes. I did not see those HAT proofs there.

This is an easy reviewer catch. Either add the missing proof text to the appendix or change the proof heading to:

\begin{proof}[Proof sketch]

and keep the existing “other levels are prefix-stable” prose.

Given the deadline, I’d do the latter.

3. Tone down the frontier maximality claims

The main body still says:

minimal monotone enlargements ...

That formal definition is fine. But the appendix frontier results still claim too much, especially:

no weaker monotone order suffices

for queues and search structures.

The monotonicity parts are solid and interesting. The maximality parts are more fragile: there may be intermediate weakenings between strict FIFO and causal FIFO, or between exact lookup and forward-reachability, unless you formalize the allowed class of refinements very tightly.

Since this is appendix material, I would not rewrite it deeply. I would change proposition titles/statements to “natural frontier point” language.

For queue:

\begin{proposition}[Queue frontier point]
  Causal FIFO is a natural monotone relaxation of replicated FIFO:
  it preserves causal ordering among enqueues while relaxing the
  global total-order requirement.
\end{proposition}

Then in the proof, replace:

Hence no order smaller than causal FIFO is monotone.

with:

Thus any strengthening that attempts to preserve a fixed order among
concurrent enqueues creates a non-monotonicity witness.

For search:

\begin{proposition}[Search frontier point]
  Under the link invariant, forward-reachability is a monotone
  relaxation of exact-location lookup.
\end{proposition}

Replace:

no weaker order suffices

with:

any semantics that invalidates a lookup solely because the key has
moved along a maintained forwarding path is non-monotone.

This preserves the insight without inviting an unnecessary minimality fight.

⸻

P1 — Strongly recommended cleanup

4. The semantic Complete CALM proof is almost too terse

The proof of Theorem 1 says:

Condition (i) follows: if every outcome at every history survives
all futures, no future need be suppressed.

This is intuitively right, but “realizable” was introduced in the implementation definition, not as a property of a specification. A reviewer may see this as a definitional slip.

Low-cost fix: change the theorem proof to avoid “Condition (i) follows” and instead say:

Monotonicity is exactly condition (ii). Since condition (ii) ensures
that no future can invalidate any admitted outcome, no history
suppression is needed for correctness; the specification-level notion
of coordination-freedom is therefore satisfied.

That makes clear you are defining semantic coordination-freedom, not constructing an implementation yet. The operational construction comes next.

5. The operational sufficiency proof needs one extra assumption stated

The causal-view protocol says each process:

picks any o \in \Obs(H_i)

But this presumes \Obs(H_i) is nonempty and effectively selectable. Since the paper is semantic, this is okay, but make it explicit:

For histories with \Obs(H_i)=\emptyset, the specification admits no
correct response; for admitted histories, choose any outcome
(non-constructively—the theorem is semantic, not a decidability result).

This is a small caveat that will reduce objections about computability/enumerability.

6. The separation theorem overstates “relational-transducer CALM cannot”

The theorem currently says:

Relational-transducer CALM cannot, in general, verify proper coordination.

The proof argues syntactic CALM sees negation and says no. But CALM as a theorem is semantic over monotone queries; “presence of negation” is a syntactic sufficient check, not the theorem itself. Also, a transducer program consuming an already-decided append-only log can be monotone.

Safer theorem title/statement:

Program-level CALM does not directly verify proper coordination.

or:

Relational-transducer CALM, applied monolithically to program text,
does not in general certify that an upstream coordination mechanism has
produced a monotone residual interface.

Then the proof becomes less exposed.

I would also soften/remove this paragraph:

no precise syntactic analysis can exist...
determining whether an arbitrary PTIME function is monotone is undecidable...

That claim is not needed and is a possible theory-reviewer rabbit hole. For a tomorrow deadline, cut it or replace with:

For sufficiently expressive languages, semantic monotonicity is not
captured by simple syntactic criteria; the specification-level test
makes the relevant boundary explicit.

7. The Complete CAP sufficiency proof is still a sketch; mark it as semantic

You already do this in the main text:

Complete CAP is a semantic characterization...

Good. I would move or repeat that sentence inside/just after the theorem proof. The sufficiency direction says “compose causal-view protocol with same-side resolution layer.” That is plausible, but not a fully formal protocol for arbitrary same-side non-monotonicity. Calling it semantic avoids overburdening the proof sketch.

Recommended sentence:

The sufficiency direction should be read semantically: same-side
non-monotonicities may require coordination, but only within a
connected component, so they do not create a partition-availability
obstruction.

⸻

P2 — Medium priority polish

8. Use “atomic/linearizable register” in the CAP-related discussion

In related work:

Gilbert--Lynch proof show linearizability cannot coexist...

That is fine, but in the running example and Complete CAP context, I’d use “atomic/linearizable read-write register” once. It anchors the CAP connection.

9. Tighten the snapshot isolation paragraph

The SI paragraph says:

To keep the invariant, SI ensures \Obs_{SI}(H_2)=\emptyset

That is not quite right: SI itself does not ensure the invariant; the application invariant plus SI execution yields an invalid state. You probably mean the specification combining SI with invariant preservation has empty observations.

Low-cost edit:

For the specification that requires SI execution while preserving the
invariant, \Obs(H_2)=\emptyset...

This avoids the impression that SI enforces the invariant.

10. The “one round of coordination suffices” remark is rhetorically risky

This remark says:

Membership establishment need only happen once...
after the initial bootstrap, the entire chain of authority transitions is monotone.

This is a nice thesis, but it is debatable: reconfiguration and leader election still use consensus/quorums; calling them monotone votes under current authority may sound like a sleight of hand.

Since it is not necessary for the paper, consider softening:

In many systems, an initial membership authority can turn subsequent
authority changes into decisions under an already-established authority.

This avoids a Paxos reviewer getting distracted.

11. “bakes in replica consistency” is a bit sharp

Current:

the transducer model's definition of coordination-freedom bakes in
replica consistency...

I’d soften to:

the transducer model studies coordination-free computation of a common
output set, so replica agreement is built into that formulation...

Same idea, less provocative.

⸻

P3 — Cosmetic / easy wins

12. Remove duplicated phrase in appendix

In the frontier appendix:

original guarantee.
original guarantee.

This duplicated line should be removed.

13. Watch “future” notation consistency

Most of the paper uses H_1 \hext H_2. In the CAP section you write:

A future H_2 \sqsupseteq H_1

I would use the macro consistently:

A future H_1 \hext H_2

Not a big issue, but easy polish.

14. Consider changing “Full proof” to “Proof details” in a few places

Several appendices are proof sketches or partial formalizations. If you say “full proof,” a reviewer may expect all omitted cases to be covered. Safer:

Proof details in Appendix...

especially for the frontier and CAP sections.

⸻

What I would not change now

I would not radically restructure. I would not remove Complete CAP. The distributed-monotone version is the right scoped theorem and is now defensible. I would not remove the frontier section either; just soften maximality language where it is most vulnerable.

I would also not spend time trying to fully formalize every application. The paper’s core is the framework and theorem; the applications are meant to show breadth. Just avoid saying “full proof” where you have a sketch.

⸻

Minimal last-minute punchlist

If you only have a few hours, do these:

1. Replace “linearizability consistent with happens-before” with “consistent with real-time operation order; in this example the relevant order is induced by happens-before among invocation/response events.”
2. Change the HAT proof heading to “Proof sketch” or add the missing appendix proof.
3. Soften queue/search frontier maximality claims.
4. Cut or soften the “no precise syntactic analysis can exist / PTIME monotonicity undecidable” paragraph.
5. Fix the duplicated “original guarantee.”
6. Clarify SI paragraph: invariant-preserving SI spec, not SI alone.
7. Add one sentence that operational/CAP sufficiency is semantic, not algorithmic.

Do those, and I think the paper is in good last-minute submission shape.