Below is a fresh review of this version as a PODS submission, treating the draft on its own terms.

Overall assessment

This version is much more coherent than the previous formulation implied by the prose. The paper now has a clearer identity:

CALM does not fundamentally depend on Datalog, transducers, or set inclusion. It depends on histories, observations, and refinement. Once stated at that level, the same monotonicity criterion can be applied to specifications and to residual interfaces produced by coordination mechanisms.

That is a good and potentially valuable PODS paper.

The best parts are:

1. The conceptual lift is clean. The “minimal axiomatic basis” story is now much more persuasive.
2. The proof is appropriately framed as short because the contribution is abstraction.
3. The residual/well-coordination angle is genuinely interesting. It is probably the most distinctive part of the paper.
4. The paper now has a plausible PODS audience: database theory, distributed semantics, transaction theory, CALM/HAT/I-confluence/CRDT connections.

But I still see several high-risk issues that could lead to rejection if not addressed. The most important are:

* the main theorem still risks looking definitional;
* the register/linearizability example remains shaky;
* the “strictly less conservative than CALM” theorem overclaims;
* the use of empty observation sets in I-confluence contradicts the core spec definition;
* arbitrary outcome orders still need a stronger “faithfulness” discipline;
* some applications are presented as recovered boundaries but are only sketches.

My recommendation: this is close to a compelling paper, but I would revise to make the claims slightly narrower, the examples bulletproof, and the model discipline sharper.

⸻

1. Main contribution: strong, but needs careful framing

The abstract now says:

“We show that CALM’s proof needs far less: only Lamport histories, an outcome set at each history, and a declared refinement order.”

This is a good framing. It turns the short proof from a liability into a feature.

However, the paper still occasionally oversells:

* “Complete CALM”
* “Universal Criterion”
* “strictly less conservative”
* “recovers the HAT/non-HAT boundary”
* “every module boundary can be tested independently”
* “no strictly weaker condition suffices”

These are strong claims. Some are defensible, but only under the paper’s exact definitions. PODS reviewers will test the edges.

I would make the central pitch:

We identify a semantic CALM theorem: future-monotonicity of observable commitments exactly characterizes coordination-free exposure in an asynchronous history model. This generalizes CALM’s proof principle and enables reasoning about residual interfaces after coordination.

That is strong enough. You do not need to claim universality quite so loudly.

⸻

2. The main theorem is still close to definitional

The theorem is:

A spec admits a coordination-free implementation iff it is monotone.

Given the definitions, this follows almost immediately:

* coordination-free means Expose_I(H) = Obs(H);
* implementations must be irretractable;
* irretractability over Expose_I = Obs is exactly monotonicity.

You now explicitly say the proof is short because it is a lifting. Good. But the paper should go one step further and preempt the obvious objection:

“Is this just monotonicity renamed as coordination-freedom?”

A reviewer may say yes unless you clearly justify the semantic definition of coordination-free independently.

The new “Why universal exposure” remark helps, but it is not yet fully convincing. In particular:

“A partitioned node has no basis for this distinction: it cannot know which futures will materialize.”

This invokes local knowledge, but the formal model has no local views, processes, or knowledge relation. The framework is global-history based. So this paragraph depends on an intuition that is not formalized.

Possible fix: add a short formal or semi-formal bridge:

* Define view_p(H) or at least state that the current theorem is a global safety criterion, not a full epistemic model of local implementability.
* Or weaken the prose: “The universal exposure condition abstracts the absence of coordination: the implementation is not allowed to use additional information to filter the spec’s allowed outcomes.”

I would avoid saying “unique formulation” unless you prove it.

Suggested replacement:

The universal condition is intentionally strong: it abstracts a setting in which the implementation does not perform any additional filtering beyond the specification itself. We use it as the semantic analogue of CALM’s “locally derivable outputs are safe to emit” condition. Weaker existential notions are possible, but they require an additional mechanism for selecting safe outcomes; in this paper, such mechanisms are treated as coordination and analyzed via residualization.

That is more defensible.

⸻

3. The largest technical risk: the running linearizability example

The running example is still the highest-risk part of the draft.

You define outcomes as:

“sequences of completed operations annotated with return values”

But then at H_1, the read has been invoked but not responded, and you include:

\langle w(1), r \mapsto 0 \rangle,\quad
\langle w(1), r \mapsto 1 \rangle

as outcomes. You patch this by saying:

“This includes outcomes for operations whose invocation is present in H but whose response is not: the implementation may commit to a return value before the response event occurs.”

That is a coherent modeling choice, but it is surprising and needs to be made more prominent. It changes “outcomes are completed operations” into “outcomes may include commitments to pending operations.” That is not standard linearizability history semantics.

I would rename the outcome domain in this example:

* not “sequences of completed operations,” but
* “sequences of operation commitments,” or
* “sequences of completed-or-committed operations.”

Otherwise the reader sees an inconsistency.

More importantly, the specific witness still seems suspect.

At H_2, the read response is resp(r,1). You say:

“Every linearization consistent with this return value must place w before r.”

True, given register semantics.

But the stranded outcome is:

\langle w(1), r \mapsto 0 \rangle

That outcome is stranded because the actual response event later says 1. This shows that committing early to a return value before the response event occurs can be invalidated by the future. It does not by itself show that linearizability requires coordination in the usual sense. It shows that speculative exposure of a pending read result is unsafe.

A critic may ask:

Why must a coordination-free implementation expose an outcome for a read before the response event exists?

Your definition says it must expose all Obs(H), but this is exactly where the modeling choice does the work. In an ordinary implementation, the read response is the exposure. Before the response, there is no client-visible commitment. If you include possible pending responses in Obs(H), then non-monotonicity is easy to obtain, but it may not correspond to the ordinary coordination need.

A cleaner running example might avoid pending responses entirely. Use a specification where a completed observation can be invalidated by a concurrent future event added later. For example:

* deterministic choice / leader election / first-writer-wins under concurrent proposals;
* uniqueness allocation;
* “choose the minimum proposal among all proposals seen so far,” where a future can add a concurrent lower proposal.

Because your future relation allows adding concurrent events, this can be made clean without relying on pending operation commitments.

Then use linearizability later as an application, carefully explained as requiring a particular observation model.

If you keep the register example, I suggest explicitly naming the nonstandard feature:

“We use speculative outcomes: Obs(H) contains return commitments that an implementation could make for pending operations. A conventional implementation that waits until response events are fixed is precisely suppressing outcomes in our sense.”

That makes the point clearer, but it may still be controversial.

⸻

4. Obs is doing too much

The paper now says:

Obs(H) is the set of outcomes the specification permits at H—not what has already been exposed, but what an implementation may expose.

That is much better.

But in different sections, Obs still means slightly different things:

1. possible speculative commitments for pending operations;
2. semantic query answer on current input;
3. exposed log prefixes after Paxos;
4. converged state if invariant holds, empty otherwise;
5. reachable CRDT states.

These are all plausible, but the paper needs a unifying statement:

Obs is an interface contract. It is not necessarily “the full mathematical behavior of the object”; it is the set of client-visible commitments the interface allows at a history.

That would make residualization and varying orders less ad hoc.

I also think the paper would benefit from reintroducing a Poss/Obs split. You already have \Poss defined but unused. This distinction would help enormously:

* Poss(H): outcomes consistent with the history / possible completions;
* Obs(H): outcomes allowed to be exposed now.

Then the register example becomes:

* at H_1, both read returns are possible;
* whether both are observable is a design/spec choice;
* Complete CALM applies to Obs, not Poss.

This would make “withholding a pending read response” formally visible as choosing Obs(H) smaller than Poss(H), i.e. as outcome suppression/coordination/latency.

Without this split, “admissible,” “possible,” “permitted,” and “observable” blur together.

⸻

5. Outcome order needs a stronger faithfulness condition

The remark on choosing Ord is useful, but not enough for a theory paper.

The obvious objection remains:

If the analyst declares a coarse enough order, any spec becomes monotone.

You say changing the order changes the specification. True. But a reviewer may still ask what prevents gaming the theorem.

I would add a formal “faithful refinement” condition, even if lightweight.

For example:

A refinement order is faithful if o1 ⪯ o2 implies every client-visible fact/commitment entailed by o1 is also entailed by o2.

Or:

Incompatible outcomes—outcomes that cannot both be prefixes/approximations of a single client-visible execution—must have no common refinement.

Then the theorem can be stated over specifications with declared faithful outcome orders. This does not need to be heavy, but it will make the arbitrary-order generalization feel disciplined rather than permissive.

This also helps with the “top element” problem. A top element refining everything is disallowed if it claims compatibility between client-visible contradictions.

⸻

6. The CALM subsumption section is improved, but still overstates equivalence

The revised transducer instantiation now uses:

\[
\Obs(H)=\{Q(I_H)\}
\]

rather than already-emitted output. Good. That fixes the earlier triviality.

However, there is still a subtle issue:

“Histories are prefixes of fair runs of the transducer network.”

If Hist depends on a particular transducer network computing Q, then the specification is no longer purely about Q; it is tied to an implementation. But the theorem is supposed to say monotonicity of Spec_Q iff monotonicity of Q.

You can simplify this section:

* Let histories be input-growth histories, not transducer run prefixes.
* Internal events are irrelevant for the query-level instantiation.
* Then I_H is just the set of input facts in the history.

After proving Spec_Q monotone iff Q monotone, cite Ameloot et al. for Q monotone iff coordination-free transducer evaluation.

That would avoid the awkward claim:

“Ameloot et al.’s operational definition … is equivalent to our semantic definition…”

You have not really proved equivalence of definitions; you prove equivalence through the common middle term “monotone query.” That is enough, but the text should say that.

Suggested wording:

The instantiation recovers CALM extensionally: both criteria accept exactly the monotone queries. We do not need to identify the operational notions definition-by-definition; the common characterization by query monotonicity gives the formal subsumption.

This is safer.

Also check this line:

“The connection is: in the transducer model, ‘output depends only on local input’ … is equivalent to ‘no outcome is suppressed’…”

This may still be too hand-wavy. I would cut or soften it.

⸻

7. “Strictly less conservative than CALM” theorem is risky

The separation theorem is a good idea, but as currently written it is likely to draw fire.

Item (2) witness: double negation in Datalog

You give:

in_R(x) <- R(x), not not_in_R(x)
not_in_R(x) <- not R(x)

This is not a clean Datalog witness.

Problems:

1. This is stratification/circularity-sensitive. not_in_R depends negatively on R, and in_R depends negatively on not_in_R. Depending on the domain of x, safety/range restriction, stratification, and closed-world assumptions, this may not be a legal or well-defined Datalog program.
2. Classic CALM is about semantic monotonicity of queries, not merely syntactic occurrence of negation. A program with double negation may be syntactically non-monotone in a naive checker, but CALM as a theorem does not “classify by syntax”; it classifies by monotonicity of the query.
3. If you say “relational-transducer CALM classifies this as non-monotone (it uses negation),” a knowledgeable reviewer may object that the theorem does not classify by the presence of negation. Positive Datalog is a sufficient syntactic fragment, not the theorem’s complete semantic test.

So item (2) is better framed as:

syntax-directed monotonicity analyses can be conservative; the semantic criterion can see through equivalent rewritings.

But do not attribute that conservatism to “relational-transducer CALM” itself.

Possible replacement:

There exist non-monotone-looking programs rejected by common syntactic monotonicity checkers whose induced query/specification is monotone.

Or remove item (2) and focus on item (3), which is stronger and more original.

Item (3): Paxos composition

This is compelling as architecture, but the proof says:

“CALM, applied to the combined program text, identifies these non-monotone operators and classifies the system as requiring coordination.”

Again, CALM is not just a syntactic operator checker. Also, if the output is an append-only log prefix, a Datalog program that consumes the decided log can be monotone. The issue is not that CALM cannot ever recognize the monotone output; it is that classic CALM lacks a native residualization/interface theorem for “coordination has already happened upstream.”

I would retitle this theorem:

Semantic residualization is less conservative than monolithic program analysis.

And phrase the claim:

A monolithic analysis of C · P reports that coordination is used/required internally; Complete CALM can additionally certify that the residual output interface is coordination-free for downstream consumers.

That is true and valuable.

Avoid:

“Complete CALM remains correct while CALM does not.”
“CALM conflates them.”

These sound combative and technically contestable.

⸻

8. The “well-coordination” concept is a major strength

This is probably the part I would emphasize more.

The paper’s strongest new contribution may be:

A coordination mechanism can be judged by the monotonicity of the residual interface it exposes.

That is a clean systems-theory idea. It connects well to logs, CDC, stream processors, stratification barriers, consensus, etc.

I would consider moving “well-coordination” earlier, perhaps immediately after the main theorem, before the CALM subsumption/separation. Then the structure becomes:

1. Framework.
2. Complete CALM.
3. Residualization and well-coordination.
4. CALM as an instance and limitation.
5. Applications.

Right now “Strict Generalization of CALM” contains three different ideas: subsumption, beyond set inclusion, and separation. The section title makes the paper feel like it is primarily arguing with CALM. I think the paper is stronger if framed positively as a semantic theory.

⸻

9. I-confluence section currently violates the spec definition

Core spec definition requires:

\[
\Obs(H) \neq \emptyset
\]

But I-confluence defines:

\[
\Obs_I(H)=\emptyset
\]

when the invariant is violated.

This is an internal inconsistency. You need to fix it before submission.

Options:

Option A: Allow partial/safety specifications in the core model

Modify Definition 3:

Obs(H) may be empty; empty means the history is forbidden/unsafe.

Then adjust Complete CALM:

* If Obs(H_2)=∅, monotonicity fails for any prior observable o.
* Coordination-free implementability is only possible if no admissible future reaches empty observations after a nonempty observation.

This is probably the cleanest.

Option B: Keep nonempty specs and encode violations as a distinguished bad outcome

Let Obs(H) = {bad} for invariant-violating histories, and make bad incompatible with valid states. But then every valid outcome may or may not refine to bad depending on the order. This is less clean.

Option C: Move I-confluence to “sketch only”

Say the instantiation requires the standard extension to safety specs with empty observations, and do not claim it as a formal proposition in the main paper.

I recommend Option A. Empty observations are natural for safety properties. The main theorem can handle them with small edits.

Also fix the proof direction labels. The proposition is:

\[
\Spec_I \text{ monotone} \iff T \text{ is } I\text{-confluent}.
\]

But the proof says:

(\Rightarrow): If T is I-confluent...

That direction label is backwards relative to the stated order. Use words instead:

* “I-confluence implies monotonicity.”
* “Failure of I-confluence implies failure of monotonicity.”

⸻

10. HAT/isolation section: good intuition, but needs precision

The HAT section is readable and mostly plausible as a sketch, but still not formal enough to support “we recover the boundary.”

Issues:

Read committed / monotonic reads details

For read committed:

“Extending a history can add committed transactions but cannot uncommit.”

True, but it can add a commit event for a transaction whose write causally/temporally precedes a read that already returned another value. Whether that invalidates the previous read depends on the exact RC definition. Many definitions allow stale reads of any committed version, so it is fine, but you should state that version.

For monotonic reads:

“non-decreasing values with respect to commit order”

This assumes a total commit order. Under weak availability models, global commit order may itself require coordination or may not be part of the guarantee. Better to say “with respect to the session’s observed version order” or whatever model you intend.

Serializability witness needs stronger Obs_L(H) definition

You say:

“Any o2 ⊇ o1 in Obs_ser(H2) must include both reads…”

That only follows if Obs_ser(H) is required to include all committed transactions and their read facts present in H.

The spec sketch should say:

Each outcome in Obs_L(H) must include all committed transactions and read/write facts whose commit/response events appear in H; it may additionally include commitments for pending transactions if the interface allows them.

Without this, the witness can be avoided by choosing an outcome that simply omits T2.

“Partial-order / total-order boundary” is too sweeping

This sentence:

“The HAT/non-HAT boundary is precisely the partial-order/total-order boundary.”

Nice slogan, but perhaps too broad. Some non-HAT guarantees are not simply total-order commitments; some HAT guarantees may involve session order plus causality. I would soften:

“A recurring source of the HAT/non-HAT boundary is the transition from partial-order-stable observations to observations that require resolving concurrency into a globally consistent order.”

That is still insightful but less brittle.

⸻

11. CRDT section is the cleanest application

This section works well. It could be made slightly more precise:

Current proof:

“every state reachable at H’ is at least as large as some state reachable at H. In particular, there exists o’…”

The quantifier you need is:

\[
\forall o \in \Obs(H), \exists o' \in \Obs(H') : o \sqsubseteq o'.
\]

Say:

Take a derivation/execution witnessing o ∈ Obs(H). Extend that derivation with the updates and merges added in H'. Since each added step is inflationary, the resulting state o' is reachable at H' and satisfies o ⊑ o'.

Also, reset-capable CRDTs:

“reset-capable CRDTs require additional protocol machinery”

This is true in spirit, but some reset/remove-like operations are implemented by enriching the lattice with causal context, epochs, tombstones, etc. Your theory explains this elegantly:

reset is non-monotone in the plain counter lattice; coordination-free designs must change the state space/order so that reset becomes represented as inflationary metadata growth.

I would say that explicitly. It strengthens your point.

⸻

12. Universal construction: useful, but overclaims

The appendix says:

“for any specification, establishing membership and ordering yields a monotone residual specification.”

Then the proof says:

“this defines a new residual output interface … not the original specification’s outcome domain.”

That is honest, but it means the theorem is not quite about the original specification. It is about exposing a log/prefix interface from which deterministic evaluation can proceed.

That is fine, but then avoid saying:

“for any specification … the resolved specification Spec|I_ord is monotone”

because earlier Spec|I was defined as same outcome order/domain with restricted histories and exposed outcomes. Here you change the outcome domain/order. This is not the same residualization operation.

You need two notions:

1. Restriction residual: same outcome domain/order, fewer histories/outcomes.
2. Interface residual: new output interface produced by a mechanism, e.g. log prefixes.

The universal construction is an interface residual, not a restriction residual.

Also this line remains problematic:

“The universal construction resolves all distributed coordination … in one round (membership).”

But ordering service is ongoing coordination. You say that earlier, so this remark contradicts the theorem text. I would delete or rewrite:

“The construction separates two forms of coordination: ongoing distributed agreement to produce the ordered log, and downstream local commitments after the log boundary. The latter require no additional distributed coordination once membership and log delivery are provided.”

That is accurate.

⸻

13. Related work: mostly good, but watch “strictly more general” claims

The Attiya/Enea/Román-Calvo paragraph says:

“their arbitration-freedom is a special case of our monotonicity: every arbitration-free specification is monotone under the appropriate instantiation.”

This may be true, but unless you prove it, it is risky. I would phrase as:

“Their arbitration-free condition appears as a close analogue/specialization of our monotonicity condition when the relevant suppression mechanism is total-order arbitration.”

Similarly:

“Li and Lee … syntactic”

Make sure that is accurate. If their work is semantic over replicated objects, calling it syntactic may be unfair. Safer:

“Their model is architecture-specific, assuming replicated-object merge semantics as primitives; ours abstracts over the history and outcome order.”

⸻

14. Presentation and structure

The paper is dense but readable. The main structural issue is that the section “Strict Generalization of CALM” is doing too much and is rhetorically adversarial.

Suggested structure:

1. Introduction
2. Running example
3. Framework
4. Complete CALM
5. Residualization and well-coordination
6. CALM as an instance
7. Expressiveness of outcome orders
8. Applications
9. Related work

This would put your actual new conceptual machinery before the comparison fight.

Also consider renaming:

* “Strict Generalization of CALM” → “From CALM to Semantic Specifications”
* “The Separation” → “Residual Interfaces and Well-Coordination”

⸻

15. Concrete textual changes I would make

Abstract

Current:

“ordered properties such as sequential consistency fall under the CALM umbrella”

Safer:

“resolved ordered interfaces, such as agreed log prefixes used to implement sequential consistency, fall under the CALM umbrella via prefix refinement.”

Current:

“recover the HAT/non-HAT boundary…”

Safer:

“recover representative HAT/non-HAT separations…”

unless you fully prove the whole Bailis table.

Contribution 2

Current:

“linearizability are directly analyzable”

Safer:

“resolved linearizable logs are directly analyzable”

or distinguish unresolved linearizability as non-monotone.

Beyond set inclusion

Current:

“the specification is coordination-free under prefix extension”

This is ambiguous. Replace with:

“the resolved log-prefix interface is coordination-free under prefix extension.”

Separation theorem

Current:

“Complete CALM is a strictly less conservative diagnostic than relational-transducer CALM”

Replace with:

“Complete CALM distinguishes semantic output monotonicity from syntactic/program-internal non-monotonicity.”

Then state a theorem about residual interfaces, not about CALM being wrong.

I-confluence

Add before the instantiation:

“For safety specifications, we allow Obs(H)=∅, meaning that no correct implementation may realize H. The main theorem extends directly: a coordination-free implementation exists only if no admissible future of an observable history reaches an empty observation set.”

Or revise the core definition.

⸻

16. Submission-risk assessment

Strengths reviewers will like

* Elegant abstraction.
* Unification of CALM with order-theoretic specifications.
* Good connection to CRDTs and logs.
* Well-coordination/residualization is a real conceptual contribution.
* Clear writing and strong motivation.

Weaknesses reviewers may attack

* The theorem is immediate from definitions.
* Coordination-free is too strong / not operationally grounded.
* Local information is invoked but not modeled.
* Linearizability example is nonstandard because it exposes pending responses.
* HAT/I-confluence claims are sketches but stated as recovery.
* Arbitrary outcome orders risk vacuity.
* “CALM cannot recognize” claims are rhetorically overstated.

Likely review summary if submitted unchanged

A sympathetic reviewer might say:

“Interesting semantic generalization of CALM, but the formal model and applications need tightening.”

A skeptical reviewer might say:

“The main theorem is definitional, and the examples/applications do not fully support the claimed universality.”

The revision goal should be to make the skeptical review harder to write.

⸻

Bottom line

This is a materially stronger draft. The central idea is now visible and worth pursuing:

CALM is really about future-monotone observable commitments, not about Datalog.

The most important repairs are:

1. Make Obs and speculative exposure precise, especially in the register example.
2. Add a faithfulness condition for outcome orders.
3. Allow or handle empty observations consistently before using I-confluence.
4. Reframe the separation from CALM as residual-interface certification, not as CALM being “incorrect.”
5. Soften “universal/complete/strictly less conservative” rhetoric unless each claim is formally nailed down.
6. Clarify that ordered/log interfaces are monotone after coordination chooses the order, while the original ordering spec may be non-monotone.

With those changes, I think the paper could become a strong PODS submission: not because the main proof is hard, but because the abstraction is clean and the residualization perspective is genuinely useful.