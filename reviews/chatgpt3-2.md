I read the attached main.tex carefully against the “candidate submission” standard: internal consistency, obvious reviewer tripwires, and small last-minute edits only. I also did a quick mechanical check: the file compiles with pdflatex on its own, and I did not find duplicate labels or missing internal refs. The undefined citations are just because there is no .bib/.bbl in the sandbox, not necessarily a paper problem.

Overall: this is much cleaner and close to submission-ready. I would not restructure. I would do a small targeted cleanup pass.

Must-fix / very low-cost correctness polish

1. Replace “consistent with happens-before” in the linearizability definition

The running example is now a good two-write/two-read witness. But this sentence is still reviewer bait:

“Under linearizability, outcomes are total orders on completed operations consistent with happens-before…”

Standard linearizability is consistent with real-time order between operation intervals, not full Lamport happens-before including internal messages. Your witness does not need the stronger claim.

Suggested edit:

Under linearizability, outcomes are total orders on completed operations consistent with real-time order between operation intervals; in our histories, the relevant operation-interval order is represented by happens-before among invocation and response events.

Also replace:

“the only linearization consistent with happens-before”

with:

“the only linearization consistent with the completed operation intervals”

This is the one edit I’d most strongly recommend.

2. Fix/soften the HAT proof heading

You currently have:

Proof (read committed; others in Appendix~\ref{app:hierarchy})

But app:hierarchy is the CALM hierarchy appendix, not the other HAT cases. Unless those cases are actually there under that label, this will look like a bad ref.

Fastest fix:

\begin{proof}[Proof sketch]

and leave the surrounding prose as-is.

3. Remove or soften “no weaker monotone order suffices” in queue/search

You softened the surrounding framing, but these two appendix propositions still contain strong maximality phrases:

“no weaker monotone order suffices”
“no order smaller than causal FIFO is monotone”
“no weaker order suffices” for search

For tomorrow, I would not reprove anything. Just soften.

For queue, change the proposition ending to:

“…relaxing the global total-order requirement.”

and in the proof replace the final sentence with:

Thus any strengthening that attempts to preserve a fixed order among concurrent enqueues creates a non-monotonicity witness.

For search, change:

“it is monotone, and no weaker order suffices.”

to:

“it is monotone and captures a natural coordination-free lookup guarantee under the link invariant.”

and replace the final “Hence no order smaller…” sentence with the more local claim that exact-location-style invalidation after movement is non-monotone.

This avoids a reviewer trying to find intermediate relaxations.

Strongly recommended small polish

4. The frontier appendix has a duplicated phrase

There is a duplicated line/phrase around the frontier discussion:

original guarantee.
original guarantee.

Remove one.

5. Soften “bakes in replica consistency”

Current:

“the transducer model’s definition of coordination-freedom bakes in replica consistency…”

Suggested:

“the transducer model studies coordination-free computation of a common output set, so replica agreement is built into that formulation…”

Same point, less provocative for CALM reviewers.

6. Tone down “no weaker condition suffices” in the discussion

Current:

“any specification with even one future-inconsistent outcome requires coordination (no weaker condition suffices)…”

Given the theorem is intentionally definitional at the semantic level, I’d qualify:

“within this no-history-suppression/no-outcome-suppression model, any specification with even one future-inconsistent outcome requires coordination…”

This prevents the “tautology” objection from feeling like a gotcha.

7. Snapshot isolation wording

Where you discuss SI/write skew, make sure the text says the invariant-preserving SI specification has empty observations, not that SI alone prevents the bad state. If the current paragraph says or implies “SI ensures Obs(H)=∅,” change to:

For the specification that combines SI execution with invariant preservation, Obs(H_2)=∅.

Things I would not change now

I would keep the title, abstract, Complete CAP, distributed-monotone formulation, and overall structure. The CAP theorem is now scoped much better than earlier drafts. I would also keep the frontier material, just soften maximality language in the appendix.

Final minimal punchlist

1. Linearizability: replace “happens-before” with “real-time order between operation intervals.”
2. HAT proof heading: change to “Proof sketch.”
3. Queue/search frontier: soften “no weaker/no smaller order” claims.
4. Remove duplicated “original guarantee.”
5. Soften “bakes in replica consistency.”
6. Add “within this model” before “no weaker condition suffices.”
7. Check SI sentence for “invariant-preserving SI spec,” not SI alone.

Do those and I’d stop. The draft is in credible submission shape.