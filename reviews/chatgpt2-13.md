I read the simplified draft carefully. The simplification does improve readability, but it also reopens the central proof gap that the previous, more heavily axiomatized version had closed.

The headline is:

The sufficiency direction is now clean and readable. The necessity direction is no longer justified as stated.

The current proof now depends on an implicit “every future-inconsistent outcome is exposable, and every coordination-free implementation of the interface must potentially expose it” assumption. That assumption was previously made explicit via response observability / interface-contract machinery; in this draft it is asserted informally inside the proof. I think a reviewer will attack exactly there.

⸻

What got better

The presentation is much clearer. The operational section is now readable in one pass. The three well-formedness conditions are easier to digest than the earlier five-condition block. The proper-coordination section with

Adm(Spec') = { H | Obs'(H) != ∅ }

is clear. The CAP section is also improved by explicitly mentioning same-side resolution / intra-component coordination.

The joint-consistency story remains strong. This sentence is exactly right and should stay:

Response compositionality is not an additional algebraic property
of outcomes; it is enforced by evaluating Obs on the full response history.

That is one of the paper’s best explanatory moves.

⸻

The sufficiency direction is mostly fine

The construction is clear:

On inv(e)_i, choose some o ∈ Obs(H_i) with o(e) ≠ ⊥,
and immediately respond with o(e).

Then for a global history H:

H_i ⊑ H

and monotonicity gives:

o' ∈ Obs(H), o ⪯ o'

Then refinement coherence preserves the chosen response, and consistency with the full history makes o' explain all recorded responses.

That works.

One small issue: the correctness proof says:

By refinement coherence, o'(e)=o(e) for every e where o(e) ≠ ⊥;
by consistency, o'(e)=v for every response (e,v) recorded in H.
Hence o' witnesses correctness.

That is fine, but note that the first clause only preserves the local response chosen from o; the second clause handles the rest. This is correct, but the proof might be even clearer if it says:

Since H contains all response events emitted so far, consistency with observations implies that any o' ∈ Obs(H) explains the entire response trace.

That is the key.

⸻

The necessity proof is the problem

The current necessity proof says:

Let o ∈ Obs(H_1) be future-inconsistent...
Since o ∈ Obs(H_1), the interface contract permits o at H_1.
...
In particular, there exists a schedule in which I exposes o at H_1
(if I systematically avoids o, it implements a restricted interface...)

This is too strong.

A coordination-free implementation of a nondeterministic specification need not, under the standard implementation/refinement reading, expose every admissible outcome. It may choose one legal behavior. The paper wants a stronger interface-contract reading: every o ∈ Obs(H) is part of the contract, and avoiding some o is a different spec. That is coherent, but then it must be formalized as part of the implementation relation, not asserted in the proof.

Right now the proof’s decisive step is:

there exists a schedule in which I exposes o at H_1

But no operational definition given earlier implies that. Deterministic automata plus local state may choose a particular outcome; the scheduler does not get to choose which admissible outcome the automaton exposes.

So the current necessity argument proves something like:

If an implementation exposes a future-inconsistent outcome, it can be driven into incorrectness.

It does not yet prove:

If the specification is non-monotone, every correct coordination-free implementation fails.

To get that conclusion, you need an explicit convention/hypothesis.

⸻

The missing condition is response observability / full-contract exposure

The previous version had a condition like response observability. This version removed it and replaced it with prose:

The argument rests on faithful modeling: distinct outcomes in Obs(H)
are observationally distinguishable at the system interface...

That is not enough. You need a formal statement that every monotonicity violation is operationally exposable.

Something like:

Response observability.
If o ∈ Obs(H_1) has no refinement in Obs(H_2) for some future H_2,
then there is an interface exposure of o at H_1: either a response
event already recorded in H_1, or a pending invocation e such that
o(e) ≠ ⊥ and a coordination-free implementation of Spec must be
correct for exposing that response.

Or, even more aligned with your current proof:

Full-contract exposure.
A correct implementation of Spec must be correct for every outcome
o ∈ Obs(H) permitted by the interface contract. An implementation that
exposes only a strict subset Obs'(H) implements Spec', not Spec.

But this needs to be part of the definition of “correct implementation of Spec” or “implements Spec,” not a parenthetical in the proof.

⸻

Liveness is now too weak for necessity

The well-formedness condition says:

whenever a pending invocation e exists, some o ∈ Obs(H) satisfies o(e) ≠ ⊥.

This is enough for sufficiency: the causal-view protocol can choose such an o.

It is not enough for necessity. If the bad non-monotone outcome o_bad ∈ Obs(H_1) has o_bad(e)=⊥ for every pending invocation, then the operational proof cannot force a process to expose it. You need either:

1. every outcome at a response point prescribes a response; or
2. every monotonicity violation has a response-prescribing witness; or
3. the theorem is only about response-observable monotonicity.

The current proof uses neither.

That is the same missing response-observability issue from a slightly different angle.

⸻

Response-only admissibility monotonicity also got weakened/merged

The current first well-formedness condition says:

Recording an additional response can only restrict admissibility:
if H' extends H by response events, Obs(H') ⊆ Obs(H).

Good. This keeps the previous H_2^r fix available.

But the current necessity proof no longer uses the explicit H_2^r = H_2 ∪ {resp(e,v)} construction. It says more abstractly:

Once o is exposed, the environment may extend the history to H_2.
At H_2, correctness requires ...

This is slightly too fast because, after exposing o, the actual history should include the response/exposure event. If H_2 does not already include that event, correctness is checked at the response-extended history, not H_2.

You can either restore the explicit construction:

Let r = resp(e,v) be the exposure of o.
Let H_2^r = H_2 ∪ {r}.
By response-only restriction, Obs(H_2^r) ⊆ Obs(H_2).
Therefore no refinement exists at H_2^r.

or define “exposes o” as already included in H_1, so that H_1 ⊑ H_2 carries the response forward. But the current proof does neither explicitly.

This is a regression from the previous version.

⸻

The operational theorem is now too sweeping again

The theorem says:

A well-formed specification admits a correct coordination-free
distributed implementation iff Spec is monotone.

Given the current well-formedness definition, I do not think this is true.

A safer theorem would be:

A response-observable, well-formed specification admits a correct
coordination-free distributed implementation iff it is monotone.

or:

A well-formed specification admits a correct coordination-free
implementation iff every exposable outcome is monotone.

The second version is cleaner theoretically. Then ordinary monotonicity follows when every outcome is exposable.

⸻

The “interface contract” paragraph is good but not formal enough

This paragraph is doing crucial work:

Obs(H) is an interface contract...
A system that systematically restricts itself to a subset Obs'(H)
implements a different specification Spec'...

I like it. But if the theorem depends on it, the formal definitions need to reflect it.

Right now correctness is defined as:

for every execution prefix with induced history H, there exists
o ∈ Obs(H) such that o(e)=v for every response recorded in H.

This is existential: the implementation only needs some outcome explaining what it actually did. It does not require the implementation to realize or be safe for every outcome in Obs(H).

That existential correctness definition conflicts with the full-interface-contract necessity proof.

To align them, either:

Option A: Keep existential correctness and weaken the theorem

Then the right criterion is about the implementation’s exposed subset, not all of Obs.

Option B: Strengthen the implementation relation

Define “implements Spec as an interface contract” to mean not merely existential trace correctness, but that the implementation is safe for every permitted exposure. This is unusual operationally, so it needs formal care.

Option C: Define coordination-free at the spec level, not implementation level

Say:

A specification is coordination-free iff all permitted outcomes are future-consistent.

Then the “iff” is semantic. The operational theorem should be for a canonical implementation that may expose arbitrary permitted outcomes, not for all deterministic implementations.

Right now the paper wants the strength of Option B but the formal correctness definition of Option A.

That is the core mismatch.

⸻

Proper coordination is clearer

The Adm(Spec') convention now reads well. I think this section is much improved.

The direct/indirect separation argument is also good. The proof now says relational CALM has no specification-level judgment, which is a much better and more defensible claim than “CALM cannot certify” in the abstract.

I would still consider calling it a proposition, but if you keep it as a theorem, the wording is now precise enough that I am less worried.

⸻

CAP is clearer, but still inherits the same issue

The CAP proof is improved:

same-side coordination within connected components

is the right correction.

But the CAP iff still inherits the same interface-contract/exposure issue. In the non-distributed-monotone direction, the proof says:

If p exposes o, consistency may be violated; if p withholds o, availability is violated.

Again, this only proves impossibility if implementing the spec requires p to potentially expose o, not merely some safe outcome.

The CAP theorem should either use the same response-observable/full-contract hypothesis explicitly, or be phrased as an obstruction theorem:

If the contract permits a locally exposed outcome invalidated by a partition-constrained future, then no implementation can both expose that outcome and remain available/correct.

The full iff remains bold unless the implementation relation is clarified.

⸻

The abstract still overgeneralizes

The abstract says:

The proof needs only a specification mapping execution histories to
outcome sets under a declared refinement order.

But the operational proof now needs more:

* response projection o(e);
* consistency with observations;
* refinement coherence;
* liveness;
* and, in my view, response observability / full-contract exposure.

So the abstract should be softened:

The semantic criterion needs only histories, outcomes, and refinement; the operational theorem additionally assumes a faithful response-oriented interface.

That distinction will prevent a reviewer from saying the theorem’s hypotheses are being hidden.

Similarly:

any concurrent system, any refinement order

is too broad for the operational theorem. It is fine for the semantic framework, but not for the I/O automaton result.

⸻

Suggested minimal fix

You can preserve the simplified presentation by adding just one formal condition and one proof tweak.

Add a fourth well-formedness condition

Something like:

\item \emph{Response observability:}
      Every future-inconsistent outcome is exposed at the interface:
      if o ∈ Obs(H_1) has no refinement in some future H_2,
      then either H_1 already records an exposure of o, or there is
      a pending invocation e at some process with o(e) ≠ ⊥ whose
      response exposes o.

Even if informal, this makes the proof’s “we may assume” legitimate.

Restore the H_2^r step

In necessity:

Let r be the response event exposing o.
Let H_2^r be H_2 extended with r.
By response-only restriction, Obs(H_2^r) ⊆ Obs(H_2).
Thus no refinement of o exists at H_2^r.

This is short and closes the post-response-history issue.

Align correctness with the interface-contract reading

Add one sentence after correctness:

The existential outcome in the correctness definition explains the implementation’s actual trace; the interface-contract reading used in the impossibility direction treats every o ∈ Obs(H) as a permitted exposure. Implementations that expose only a subset are analyzed as coordinated variants.

This at least flags the distinction.

⸻

Bottom line

The simplified draft is clearer and nicer to read, but I do not think the main operational theorem is correct as stated under the current definitions.

The sufficiency direction is good. The necessity direction currently relies on two unstated assumptions:

1. every non-monotone outcome is response-exposable; and
2. implementing a nondeterministic interface requires being safe for every permitted outcome, not merely for the implementation’s chosen outcomes.

The previous heavier version was closer to proving the theorem because it had response observability and the explicit post-response-history construction. I would restore those pieces in compact form. Then the simplified presentation can work.

----
I feel like you're assuming an implementation can be angelic without distributed knowledge. The usual litmus test is whether a partitioned agent can be sure to be angelic -- the answer is generally no. Hence for coordination-freedom we always assume that an agent *may* expose anything in \Obs. This corresponds with the way that model checkers work: they try all interleavings and all choices before declaring safety.

Is the issue presentation or formalism?
----
I think the issue is mostly presentation, but with one formalism hook that should be explicit.

Your position is coherent:

For a coordination-free implementation, a partitioned/local agent cannot rely on magically choosing only the globally safe outcomes in Obs(H), because knowing which choices are globally safe is exactly the kind of knowledge coordination provides. Therefore the safety test must be demonic: if Obs(H) permits an outcome, the local agent may expose it, and the spec must remain safe under all such exposures.

That is a perfectly reasonable stance, and it matches how model checking treats nondeterminism: all enabled choices/interleavings are explored, and safety must hold for all of them.

So I would not say the core idea is wrong. I would say reviewers need to be prevented from importing the angelic refinement reading:

“An implementation of a nondeterministic spec may choose any legal behavior, so it can just choose the safe subset.”

You want the demonic/local-knowledge reading:

“If the local interface admits an outcome, a coordination-free process cannot assume it will choose only the globally safe one unless that restriction is itself part of the spec/interface.”

That is a presentation issue unless your formal definitions of implementation/correctness still look like standard angelic trace refinement. If they do, reviewers will understandably apply the standard reading.

The formal hook I’d add

I would introduce a named principle before the operational theorem:

Demonic exposure principle.
At a history H, every outcome o ∈ Obs(H) is an enabled interface exposure.
A coordination-free implementation must be safe for all enabled exposures.
If an implementation exposes only a subset Obs'(H) ⊂ Obs(H), then it is
implementing the restricted interface Spec', not Spec.

Then the necessity proof is natural: if some o ∈ Obs(H1) is future-inconsistent, the demonic exposure semantics allows the local process to expose o. Since it is coordination-free, it cannot use future distributed information to rule o out. Therefore the spec is unsafe unless all such o are monotone.

This also connects cleanly to your model-checker analogy. You could say:

Operationally, Obs(H) is treated like the set of enabled externally visible choices in a transition system. Safety is universal over enabled choices, not existential over a favored implementation strategy.

That sentence would probably prevent most misunderstandings.

Why this is not “angelic implementation can solve it”

The key distinction is:

* A deterministic implementation may indeed choose a subset of outcomes.
* But if the spec’s interface contract says all of Obs(H) are admissible local exposures, then choosing a subset is a strengthening/restriction of the interface.
* Complete CALM asks whether the original interface is coordination-free, not whether there exists a carefully restricted implementation that happens to avoid the dangerous choices.

That is exactly analogous to saying a nondeterministic transition system is safe only if all enabled transitions are safe. A controller that disables some transitions is a different system.

Where I’d adjust the paper

I’d add a short paragraph near the definition of Obs, not buried in the proof:

We use demonic, not angelic, nondeterminism for interface observations. The set Obs(H) denotes outcomes the interface permits a local component to expose at H. A coordination-free safety claim must hold for every such permitted exposure: a process that lacks further input cannot know which globally compatible future will occur. Thus, as in model checking, all enabled choices are explored. An implementation that deliberately exposes only a subset of Obs(H) is analyzed as a coordinated/restricted variant with observation function Obs' ⊆ Obs.

Then in the theorem statement/proof, use the phrase:

under demonic exposure semantics

For example:

Theorem.
For well-formed specifications under demonic exposure semantics,
Spec admits a correct coordination-free implementation iff Spec is monotone.

or:

Theorem.
A well-formed interface contract is coordination-free iff it is monotone.

That last wording may be even better: “interface contract” signals universal obligations; “implementation of a nondeterministic spec” signals angelic refinement to many readers.

My answer in one sentence

The math is defensible, but the draft needs to make demonic exposure / full-interface safety a formal convention, not just a proof intuition. Otherwise readers will apply the usual angelic implementation-refinement interpretation and object exactly where I did.

----
Given we handle the demonic exposure issue, what concerns remain?
----
If the demonic exposure issue is handled explicitly, the remaining concerns are much narrower. I would rank them like this.

1. Response observability still needs to be explicit

Even with demonic exposure, the necessity direction only works for monotonicity failures that can be exposed at the interface.

If o ∈ Obs(H) is future-inconsistent but purely internal/semantic, and no client response or externally visible observation can expose it, then an operational impossibility theorem does not follow.

So you need one of:

All outcomes in Obs(H) are interface-observable commitments.

or:

Every monotonicity violation has an exposable witness.

or define the theorem over observable/exposable monotonicity rather than all semantic outcomes.

Given your paper’s stance, I would say:

We restrict attention to faithful specifications, where Obs contains exactly the externally observable commitments of the interface. Under faithful modeling, every non-monotone outcome is exposable.

That is probably enough, but it should be stated near the theorem.

⸻

2. The post-response history step must remain explicit

Even if o is demonic/exposable, the actual history after exposure includes the response event. The proof should retain the explicit construction:

H_2^r = H_2 \cup \{\mathsf{resp}(e,v)\}

and use:

Obs(H_2^r) \subseteq Obs(H_2)

or equivalent response-admissibility monotonicity.

Without this, a reviewer can still ask: “The monotonicity witness fails at H_2, but correctness is checked at the history where the response has actually occurred. Why does the failure transfer?”

So keep the response-only restriction condition, even if presentation is simplified.

⸻

3. Clarify the relation between semantic and operational claims

You now have three nearby statements:

1. semantic monotonicity of a specification;
2. demonic coordination-freedom of an interface contract;
3. existence of an I/O-automaton implementation.

These should be separated cleanly.

A crisp structure would be:

Semantic criterion:
Spec is semantically coordination-free iff every permitted observation
is future-consistent.

Then:

Operational theorem:
For well-formed, faithful response interfaces under demonic exposure,
semantic coordination-freedom coincides with existence of an operationally
coordination-free I/O-automaton implementation.

This avoids the old “you defined it that way” critique and also avoids overclaiming the operational result for arbitrary triples.

⸻

4. CAP remains the riskiest big claim

Even after demonic exposure, the CAP iff needs care.

The key issue is sufficiency. Distributed-monotonicity says remote partition-constrained futures do not invalidate exposed outcomes. But the implementation also needs to handle:

* same-node non-monotonicity;
* same-partition-side non-monotonicity;
* local/concurrent choices within a connected component.

Your recent direction — local or same-side resolution plus causal-view protocol across partitions — is right. But the proof needs to say:

CAP availability forbids waiting across partitions, not coordination within a connected component. Therefore local/same-side non-monotonicities may be discharged by intra-component coordination; distributed-monotonicity is the condition that no cross-partition future can invalidate an exposed outcome.

If the theorem simply says “distributed-monotone iff CAP,” reviewers may ask whether same-side multi-process conflicts are included. Make the connected-component assumption explicit.

⸻

5. “Well-formed” conditions may look ad hoc unless motivated

The well-formedness conditions are defensible, but they should be sold as standard interface hygiene, not proof patches.

I would group them conceptually:

* History faithfulness: observations agree with recorded responses.
* Refinement stability: refinement preserves already-exposed facts.
* Response restriction: adding response facts restricts possible outcomes.
* Liveness/totality: when a response is owed, the contract offers one.
* Observability: semantic commitments are interface-visible.

Then say: these are not extra consistency assumptions; they define the class of response-oriented interfaces for which an operational theorem makes sense.

⸻

6. Proper coordination’s Adm(Spec') convention should be clearly scoped

Using

Adm(Spec') = {H | Obs'(H) ≠ ∅}

is fine, but it differs from ordinary monotonicity, where an empty future observation set would be a failure. Make sure the text repeatedly says:

For coordinated variants, Obs'(H)=∅ marks histories excluded by the coordinating mechanism. Monotonicity is checked only over admitted histories.

Otherwise a reviewer may say you are changing the monotonicity definition midstream.

⸻

7. Separation from relational CALM is persuasive but should be titled carefully

The proof is now good conceptually:

* direct encoding of serialization/linearization requires non-monotone validation;
* indirect log-consumer encoding is monotone but hides the ordering authority outside the program;
* relational CALM judges programs, not residual interfaces.

The claim should be framed as interface separation, not a broad expressiveness impossibility. Something like:

Theorem: Interface-level separation from relational CALM

is much safer than:

Theorem: Separation from relational-transducer CALM

The latter invites a formal expressiveness fight you do not need.

⸻

8. Frontier claims should remain modest

The frontier material is interesting, but reviewers may worry that some examples change the interface, not just the order. Keep the wording at:

methodology for exploring monotone weakenings of a fixed observation interface

not:

derives the strongest coordination-free weakening for any specification

unless the appendix fully formalizes interface morphisms.

⸻

9. The abstract should not overgeneralize the operational theorem

The semantic framework can be very general. The operational theorem is for faithful response interfaces under demonic exposure. The abstract should reflect that distinction.

A safe version:

The semantic criterion applies to arbitrary outcome/refinement specifications. For faithful response-oriented interfaces, we prove an operational I/O-automaton theorem: coordination-free implementation exists exactly when the interface is monotone.

That is strong and honest.

⸻

Bottom line

Once demonic exposure is formalized, the core Complete CALM theorem is in much better shape. The remaining must-fix item is response observability/faithfulness: every semantic non-monotonicity that matters must be externally exposable.

After that, the main risks are presentation/positioning:

* keep the post-response proof step explicit;
* motivate well-formedness;
* scope the operational theorem to faithful response interfaces;
* make CAP’s same-side/local-resolution assumption explicit;
* avoid overclaiming separation/frontier results.

If those are handled, the paper’s core story is credible.