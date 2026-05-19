This draft is clearer than the previous one, and the overall story is now easier to follow. The operational section has a much better “spine”: semantic criterion → demonic/interface-contract interpretation → I/O automata → sufficiency/necessity → Complete CALM. That is the right shape.

But I think the simplification still leaves two important concerns:

1. The necessity proof still relies on response observability / faithful exposure, but that condition is no longer formal enough.
2. The paper’s statements still overgeneralize from the response-oriented operational theorem to “any concurrent system / any refinement order.”

The good news: these are fixable with small, targeted edits. I would not undo the simplification.

⸻

What looks good now

The demonic exposure issue is much better handled. This paragraph is doing the right work:

“A system that systematically exposes only a subset of Obs(H) implements a restricted specification Spec' — not Spec itself. Coordination-freedom is therefore a property of the specification, not of any angelic selection strategy.”

That should stay. It is the right conceptual move.

The joint-consistency remark is now solid and understandable. The key idea that response compositionality is enforced by evaluating Obs on the full response history is clear.

The sufficiency proof is also now quite clean. The causal-view protocol chooses an admissible response from the local view; monotonicity lifts it to the global history; consistency with recorded responses makes the outcome explain the whole response trace. That is good.

The CAP section is better than before because it now talks about same-side resolution within connected components, not merely same-process local coordination. That fixes an important conceptual slippage.

⸻

Main remaining issue: necessity still needs response observability

The necessity proof currently says:

“Since Obs captures all observable behavior, any monotonicity violation manifests at the interface: we may assume without loss of generality that H_1 contains a pending invocation e …”

This is exactly the point that needs to be a formal condition, not an informal “WLOG.”

Your current well-formedness conditions are, in prose:

1. outcomes agree with recorded facts;
2. refinement preserves committed responses;
3. every admissible outcome at a response point commits to a response;
4. adding a recorded response only restricts admissibility.

Those are useful, but none of them implies:

every monotonicity violation has a response-point witness.

You are relying on faithful modeling: if the violation matters, it is externally observable. That is a reasonable stance, but it should be named and stated as part of the theorem’s hypothesis.

A compact fix:

We call a specification response-faithful if every future-inconsistent
outcome is exposable at the interface: whenever
o \in Obs(H_1) has no refinement in some future H_2, there is a
history H_r \sqsubseteq H_1, a pending invocation e at some process p,
and an outcome o_r \in Obs(H_r) prescribing a response to e such that
exposing that response commits to o.

That version may be more detailed than you want. A simpler paper-friendly version:

Faithful exposure. Every outcome in Obs(H) represents an externally
observable commitment. In particular, every monotonicity violation has
a response-point witness: some pending or recorded response whose
outcome has no compatible refinement in the violating future.

Then change the operational theorem to:

A well-formed, response-faithful specification admits …

This is not pedantry. It is exactly what justifies the phrase “we may assume without loss of generality.”

⸻

The post-response step is good, but use it explicitly

The necessity proof now includes:

H_2 \cup \{\mathsf{resp}(e,v)\}

and uses the response-restriction property:

Obs(H_2 \cup {resp(e,v)}) ⊆ Obs(H_2)

Good. That was needed.

I would make this a little cleaner by naming the response-extended history:

Let H_2^r = H_2 \cup \{\mathsf{resp}(e,v)\}.
By refinement coherence, Obs(H_2^r) ⊆ Obs(H_2).
Since no outcome in Obs(H_2) refines o, no outcome in Obs(H_2^r)
refines o either.

This makes the proof easier to check and avoids hiding the actual history where correctness is evaluated.

⸻

“Well-formed” is doing too much under that name

Right now “well-formed” includes semantic/interface obligations, not just structural sanity conditions. That is okay, but the name may understate its role.

Maybe rename or frame it as:

response-faithful well-formedness

or:

well-formed response interface

For example:

A specification is a well-formed response interface if it satisfies:
...

That tells readers these conditions are not generic to all semantic triples; they are the interface discipline needed for the operational theorem.

This matters because the abstract says:

“The proof needs only a specification mapping execution histories to outcome sets under a declared refinement order.”

That is true of the semantic criterion, but not the operational theorem. The operational theorem also needs the response-interface discipline. I would adjust the abstract slightly:

“The semantic criterion needs only histories, outcomes, and refinement. For well-formed response interfaces, we prove an operational I/O-automaton theorem…”

That avoids overclaiming.

⸻

The abstract still overgeneralizes

The abstract currently says:

“any concurrent system, any refinement order”

For the semantic framework, yes. For the operational theorem, no: the theorem is for well-formed response interfaces under demonic exposure semantics.

I would revise the relevant abstract paragraph along these lines:

“The semantic criterion applies to arbitrary history/outcome specifications. For faithful response-oriented interfaces, we prove an operational I/O-automaton characterization: coordination-free implementation exists iff the specification is monotone.”

That is still strong, and it anticipates the natural reviewer objection.

⸻

The separation theorem regressed a bit

The latest separation proof appears to have lost the useful direct/indirect caution you added earlier. It now says:

“Encoding the linearization as position-value facts requires a uniqueness constraint…”

This is vulnerable unless you say “when the program constructs or validates the linearization.” Reading an already-valid log is monotone, which you later discuss, but the direct-encoding sentence should be precise.

Suggested edit:

“If the program is responsible for constructing or validating the linearization from unordered/concurrent events, encoding the linearization as position-value facts requires enforcing uniqueness and completeness…”

This prevents a reviewer from saying, “But pos(i,v) facts can be consumed monotonically if validity is guaranteed externally.”

Also, the theorem title is still broad:

Separation from relational-transducer CALM

I would prefer:

Interface separation from relational-transducer CALM

The current proof is about the absence of a specification-level/interface judgment in relational CALM, not a broad expressiveness separation. The stronger title invites unnecessary argument.

⸻

Complete CAP is better but still bold

The CAP theorem is now more plausible because the proof says same-side non-monotonicities are discharged by coordination within the connected component. That is the right story.

But the theorem remains the boldest claim in the paper. Two issues remain:

First, the main theorem and appendix restatement are slightly inconsistent in flavor. The main proof talks about local/same-side resolution plus causal-view protocol. The appendix restatement says:

“Since every outcome survives all such futures, p can expose any admissible outcome immediately…”

That latter statement sounds like no same-side resolution is needed. But if distributed-monotonicity is weaker than full monotonicity, same-side conflicts may still exist. The appendix sufficiency proof should include the same same-side resolution layer, or it overstates sufficiency.

Second, distributed-monotonicity should inherit the same demonic/response-faithful exposure convention. If “exposed at p” is a response commitment, say so explicitly and tie it back to the operational well-formedness assumptions.

A small fix in the appendix proof:

Under a partition, cross-side futures are exactly the P-constrained futures. Same-side futures may still contain non-monotonicity, but they are resolved by coordination within the connected component. Availability in CAP forbids waiting across the partition, not coordination within a connected component.

That aligns the appendix with the main text.

⸻

The Admissible histories paragraph still says implementation choices are not included

This paragraph says admissible histories:

“represent the environment’s nondeterminism … rather than implementation choices.”

But the interface projection includes responses, which are implementation outputs. You’ve handled this conceptually elsewhere with interface-contract semantics, but this sentence is now misleading.

A safer version:

“They represent causally coherent interface continuations under asynchrony. Invocations and message deliveries are supplied by the environment; response events are permitted interface exposures under the specification’s contract.”

This aligns the admissible-history definition with the demonic exposure view.

⸻

Minor concrete fixes

A few more small things I noticed:

* In the sufficiency proof: “each local view satisfies H_i \hext H” is backwards in ordinary English. You use H_1 \hext H_2 to mean H_2 is a future/extension of H_1, so the intended statement is correct if \hext means “is a prefix of.” But visually it may confuse readers. Consider writing “H is a future of H_i” in prose.
* In the main CAP theorem, “same-side resolution layer” should mention connected components under the current partition, not merely “same-side” if partitions can have multiple components.
* The phrase “All specifications in this paper are well-formed” may be too strong if frontier examples are abstract and not response-oriented. Consider “All specifications to which the operational theorem is applied are well-formed response interfaces.”
* The abstract says CAP follows as a “companion theorem”; the appendix labels it “restated.” That is okay, but make sure cross-references call it theorem consistently.

⸻

Bottom line

The draft is clearer and closer. The demonic exposure story is now present enough that I understand the intended theorem. But to make it reviewer-proof, I would add back one compact formal hypothesis:

response-faithfulness / response observability: every monotonicity violation is externally exposable.

Then align the abstract and theorem statement with that scope.

My top edits:

1. Add “response-faithful” as a named condition and include it in the operational theorem.
2. Keep the explicit H_2^r post-response proof step.
3. Fix the admissible-histories prose so response futures are not described as environment choices.
4. Reinsert the “constructing/validating the log” qualifier in the separation proof.
5. Make the appendix CAP sufficiency proof mention same-component resolution, not just immediate exposure.

With those, I think the formal story is much more robust while preserving the simpler presentation.