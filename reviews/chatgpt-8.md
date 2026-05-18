I reviewed the latest main.tex. The draft is cleaner in several ways: the title is better, empty Obs is now allowed, the old duplicate-label/orphan-proof issues appear fixed, and the CALM instantiation is much more defensible. But I see two pressing correctness blockers that I would address before worrying about polish.

P0 — Must fix before submission

1. The current Poss-preservation definition makes Complete CALM false

The new definition is elegant, but as written it does not encode the refinement/irretractability condition needed for the theorem.

You define:

\Poss_{H_{\mathit{in}}}(H)
=
\bigcup_{H' \in \mathcal{A}(H_{\mathit{in}}),\, H \hext H'}
\Obs(H')

and

\Poss^I_{H_{\mathit{in}}}(H)
=
\bigcup_{H' \in \mathcal{R}_I(H_{\mathit{in}}),\, H \hext H'}
\Expose_I(H')

Then coordination-free means:

\Poss^I_{H_{\mathit{in}}}(H) = \Poss_{H_{\mathit{in}}}(H)

But if an implementation realizes all admissible histories and sets

\Expose_I(H)=\Obs(H)

then this equality holds for any specification, monotone or not. The definition only says “the same outcomes appear somewhere in some future.” It does not say that an outcome exposed at a prefix must have a compatible refinement in every future.

So the sufficiency direction no longer needs monotonicity, and the necessity direction does not go through.

The core theorem needs a condition over commitment/refinement, not just possibility-set equality. A minimal repair is to define possibility relative to a prior exposed outcome:

\Poss(H,o)
=
\{ H' \mid H \hext H' \text{ and } \exists o' \in \Obs(H') : o \Ord o' \}.

Then coordination-freedom says something like:

for every admissible H, every o ∈ Obs(H), and every admissible future H', the commitment o remains possible/refinable at H'.

That is exactly monotonicity. Or, more simply, return to:

I is coordination-free iff
(i) it realizes all admissible histories, and
(ii) every outcome in Obs(H) is future-consistent.

Then say explicitly that condition (ii) is the semantic no-outcome-suppression requirement. Right now Poss-preservation sounds operational, but it has lost the \Ord structure.

2. The running example currently makes causal consistency non-monotone

This is the most important example-level issue.

At H_1, under causal consistency you admit both response commitments for the pending read:

{(w(1), bot), (r -> 0, bot)}

and

{(w(1), r -> 1)}

Then H_2 is a future that contains the actual response:

r -> 1

The draft says:

At H_2, the outcome {(w(1), r -> 1)} refines both.

But it does not refine the outcome containing r -> 0 if read return values are part of the outcome. A commitment to r -> 0 is not refined by a later history in which the same read returns 1.

So, under the current semantics, causal consistency is not monotone either. The problem is not causal consistency; it is the modeling of pending-response commitments.

You have a few possible fixes:

1. Do not include pending response commitments in Obs(H). Let Obs(H) contain only completed/externally committed operations. Then causal consistency is easier to make monotone, but you need a different witness for SC.
2. Model exposure as adding an event to the history. If the implementation exposes r -> 0 at H_1, then the future should be an extension of H_1 + resp(r,0), not a future where resp(r,1) occurs. This is probably the most operationally faithful version.
3. Split “possible immediate responses” from “observable committed outcomes.” For example, use MayRespond(H) for availability choices and Obs(H) for already committed observations. Then the theorem applies to Obs; availability analysis separately asks when MayRespond can be safely committed.

Right now the paper is mixing “possible response choices” and “irretractable observations.” That is exactly what causes the causal-consistency witness to fail.

⸻

P1 — Important reviewer-risk issues

3. “Complete CAP” is still broader than the formal proof supports

The main theorem says:

a specification admits a consistent, available, partition-tolerant implementation iff it is monotone

The appendix introduces cross-partition witnesses, which is the right concept, but the main theorem still quantifies over all non-monotone specs. Not every non-monotonicity witness is cross-partition. Some are local, thread-level, or same-partition.

The formal corollary should be scoped like this:

If a specification has a cross-partition future-inconsistent outcome under partition pattern P, then no implementation can be both correct and maximally available under P. If the specification is monotone, no such CAP-style witness exists.

That still gives you a memorable “Complete CAP” story, but it avoids an overclaim.

Also, the proof of the appendix corollary begins with a cross-partition witness, but the statement does not assume one. That mismatch is a reviewer trap.

4. The frontier definition is improved, but the examples still overclaim “frontier”

The abstract and contributions now say:

“minimal monotone enlargements of the declared order characterize the strongest coordination-free guarantees.”

This is fine as a definition, but the examples do not quite match it.

In the register section, the frontier definition fixes (E, Obs, Ord) and varies Ord. But the register result switches to:

\Obs_{\mathit{causal}}

which is not the same observation function as SC. So the proposition:

\Ord^* = \Ord_{\mathit{causal}}

does not really follow from the stated frontier definition. It is about a weaker interface, not merely a larger order.

You do acknowledge this in prose:

“More generally, a coordination-free weakening may change the observation function, the refinement order, or both…”

Good. But then the formal propositions should not use \Ord^* as if only the order is changing. Safer:

Causal consistency is a coordination-free weakening of sequential consistency and lies on the interface frontier under the comparison relation ...

If you want it as a theorem, define the interface preorder explicitly:

(E,Obs_1,Ord_1) \sqsubseteq (E,Obs_2,Ord_2)

meaning something like “the second admits no observations that the first would forbid, modulo abstraction.” Without that, “strongest interface below SC” is intuitive but not formal.

5. The frontier maximality proofs are still too hand-wavy

For the register, queue, and search structure appendices, the monotonicity halves are useful. The maximality halves are much less solid.

Examples:

* Register maximality says you can force o_2 as the unique extension of o_1. That needs a realizability lemma.
* Queue maximality still uses informal “any smaller order must declare one pair incompatible” reasoning. A smaller order might remove some refinement edges without imposing a global preference between all concurrent enqueues.
* Search maximality is especially broad: “any order smaller than forward-reachability requires exact location” is not generally true. There may be intermediate weakenings.

I would make these appendix results less brittle:

“Forward-reachability is a natural monotone weakening…”

rather than:

“Forward-reachability is on the frontier…”

unless you formalize the ordering over weakenings and prove minimality rigorously.

6. Proper coordination is good, but “fewer histories” is not reflected in the definition

Definition:

Spec' = (E, Obs', Ord)

with

Obs'(H) \subseteq Obs(H)

This captures outcome restriction, but not really future/history restriction unless you encode forbidden histories as Obs'(H)=∅.

The prose says:

fewer admissible outcomes, fewer admissible histories, or both

That is fine if empty Obs is now the representation of excluded histories. Say that explicitly:

We represent history restriction by setting Obs'(H)=∅.

That will make the definition cleaner.

⸻

P2 — Presentation / polish

7. The CALM separation language is still a little too sharp

This line in the Paxos example is risky:

“This is correct for the internal specification but incorrect for the output specification. Complete CALM distinguishes these; CALM conflates them.”

I would soften to:

“Classic CALM, applied monolithically to the program text, reports the coordination used internally. Complete CALM additionally lets us certify the monotone residual output interface.”

That is harder to object to. CALM can analyze append-only log consumers if they are modeled that way; your real advantage is semantic boundary selection.

8. The prefix-extension Datalog proposition is plausible but overstated

The proof says encoding prefix extension as position facts requires negation to enforce uniqueness. That is intuitively right for the obvious encoding, but “any encoding” is strong. A theory reviewer may ask about alternative encodings, built-in keys, functional dependencies, or type-level uniqueness.

Safer title:

“Set-inclusion encodings of prefix extension require non-monotone uniqueness constraints”

or:

“The standard position-fact encoding requires negation.”

If you keep “any encoding,” you need a more model-theoretic argument.

9. The abstract is exciting but exposes every risky claim

The abstract currently advertises:

* strongest frontier for any specification;
* new characterizations for registers, queues, and search structures;
* complete CAP.

These are the least buttoned-down parts. If this is going to PODS, I would either harden those sections or soften the abstract:

“suggests a frontier construction…”
“illustrated on registers, queues, and search structures…”
“yields a CAP-style corollary…”

The core Complete CALM result is strong enough; do not let the most speculative appendix material dominate the abstract.

10. Hydro citation in the main theorem section may feel abrupt

The Hydro sentence is interesting, but it appears immediately after a deep semantic theorem:

“Hydro uses such checks…”

That may feel like a systems advertisement unless the related-work/application section explains it. I would either move it to related work or add one sentence saying it is an example of conservative syntactic checking for a semantic criterion.

⸻

Things that are much better now

The following changes are clear improvements:

* The title, “Complete CALM: Coordination Analysis for Specifications,” is much better.
* Allowing Obs(H)=∅ fixes the I-confluence direction.
* The CALM instantiation now abstracts away transducer internals and correctly uses semantic query output.
* Proper coordination is now an explicit section and is a real contribution.
* The CAP material is more operationally grounded than before, even though the theorem statement still needs narrowing.
* The old duplicate labels and orphan proof issue appear fixed.

⸻

My recommended priority order

If you only have time for a focused revision, I would do this:

1. Fix the Poss/coordination-free definition so Complete CALM is true.
2. Fix the pending-response problem in the running example, especially causal consistency.
3. Scope Complete CAP to cross-partition future-inconsistency.
4. Clarify that register/queue/search are interface-frontier examples, not merely order-frontier examples.
5. Soften or formalize the frontier maximality proofs.
6. Tone down “CALM conflates” and “any encoding” language.

The first two are blockers. The rest are about reducing reviewer attack surface.

Bottom line

The paper’s core idea remains strong and publishable:

coordination-freedom is future-monotonicity of observable commitments under a declared refinement order.

But the current revision’s new Poss machinery and pending-response example accidentally undercut that core. Fix those, and the draft will be much more stable.