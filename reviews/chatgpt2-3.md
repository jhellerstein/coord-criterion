This revision is meaningfully better, especially in the operational framing. You have addressed several of the most important previous objections: enabled-response rather than “the scheduler must not interleave input,” explicit fairness, deterministic automata, a correctness definition via response explanation, and an explicit acknowledgment of silent/remote futures in the necessity proof.

But I still think the paper is not yet internally aligned enough for the main iff theorem as currently stated. The new material improves the story, but it also exposes a central tension:

The semantic theorem quantifies over all outcomes and all futures, while the operational proof only constrains locally exposed responses under silent/remote futures, and the sufficiency proof still assumes joint response consistency that does not follow from pointwise monotonicity.

That is the core issue to fix.

Below is a structured review.

⸻

High-level assessment

The paper is now much closer to a credible “Complete CALM” submission. The I/O-automaton section is no longer just decorative; it is trying to prove the right operational theorem. The presentation is also clearer, and the running example is better integrated.

However, the paper still makes claims at three different levels and treats them as equivalent:

1. Semantic future-monotonicity: every o ∈ Obs(H) refines into every future.
2. Operational immediate response: each process can respond without waiting for further local input.
3. Distributed availability under partitions: each side can continue responding during a network partition.

These are related, but they are not identical. The current theorem statements collapse them too aggressively.

I would now describe the state of the paper as:

The conceptual thesis is strong and the operational model is promising, but the main theorem still needs either a narrower statement or stronger assumptions.

⸻

Biggest remaining problem: the operational theorem still does not prove the stated iff

The theorem says:

A specification Spec admits a correct coordination-free distributed
implementation iff Spec is monotone.

But the necessity proof itself now says:

The proof requires that H_2 be realizable as a p-silent future...
This holds whenever the non-monotonicity witness involves activity
at processes other than p...
For purely process-local non-monotonicity... such non-monotonicity
does not prevent coordination-free implementation.

That caveat is important, but it contradicts the theorem as stated.

Ordinary monotonicity quantifies over all futures, including process-local futures. Your operational impossibility argument only works for futures that the responding process cannot observe before responding. That is exactly the distinction you later use for Complete CAP via distributed-monotonicity.

So the current theorem should not say:

coordination-free iff monotone

unless your operational notion of coordination-free disallows even process-local waiting/serialization and every non-monotonicity witness is response-exposable at some process before the dangerous local future.

Right now the paper says both:

* Complete CALM: all non-monotonicity prevents coordination-free implementation.
* Complete CAP: process-local non-monotonicity does not prevent CAP-style availability.

That distinction is good, but the Complete CALM theorem must explicitly adopt the stronger local-immediacy model.

A defensible version would be:

A specification admits a correct strongly immediate implementation, in which every invocation can be answered from the post-invocation local state without waiting for any further local or remote input, iff every exposed outcome is monotone under all futures.

Or alternatively:

A specification admits a correct communication-free/distributed-available implementation iff it is monotone with respect to futures invisible to the responding process.

Those are different theorems. The current draft slides between them.

⸻

The most serious proof gap: pointwise monotonicity does not imply joint consistency

The sufficiency proof still contains the weakest sentence in the paper:

Since each local view H_i is a prefix of H, and Obs(H) contains all
outcomes admissible at the global history, the existence of a jointly
consistent o^* follows from the specification's definition of
admissibility at H.

I do not think this follows.

Monotonicity says:

for each local chosen o_i ∈ Obs(H_i),
there exists some o_i' ∈ Obs(H) with o_i ⪯ o_i'.

But correctness requires:

there exists one o^* ∈ Obs(H)
that explains all responses emitted by all processes.

Those are different. Each local response can be separately explainable while the set of responses is jointly inconsistent.

This is the classic issue: pointwise extendability is not finite compatibility.

You need an additional property, something like:

Finite exposure compatibility:
For any global history H and any finite set of outcomes
o_1 ∈ Obs(H_1), ..., o_k ∈ Obs(H_k), where each H_j ⊑ H,
if the corresponding responses are all emitted in H, then there exists
o^* ∈ Obs(H) refining all o_j.

Or more cleanly:

Response-compositionality:
If each emitted response fact is individually explainable at H, then
the set of emitted response facts is jointly explainable by some
o ∈ Obs(H).

Without such an assumption, the causal-view protocol can let two replicas independently choose outcomes that are each future-consistent but mutually incompatible.

This is not a minor technicality. It is exactly the gap between semantic “every chosen thing can survive” and distributed “independently chosen things can coexist.”

Possible fixes:

1. Restrict the theorem to response-fact specifications, where outcomes are sets of response facts ordered by inclusion and Obs(H) is closed under union of compatible facts.
2. Add finite-join/compatibility monotonicity as part of the criterion.
3. Make the implementation choose from a canonical deterministic selection function that is stable under refinement and guaranteed to compose across processes.
4. Weaken correctness to per-response explainability rather than joint explainability — but I would not recommend that, because it weakens the model too much.

For PODS, I think you need to confront this explicitly.

⸻

Histories still conflate inputs and outputs

You improved the I/O-automaton model, but the base history model still says:

E_in contains client-facing interface events:
both invocations and responses.

Then later:

Input projection In(H) restricts H to its input events:
E ∩ E_in

This is confusing because responses are not input actions in the I/O-automaton model. They are output actions.

The text tries to reconcile this:

In the I/O automaton model, invocations are input actions and
responses are output actions; the history records both as interface
events regardless of which party initiates them.

But then In(H) is no longer an input projection. It is an interface projection. And A(H_in) treats response events as if they were part of the environment’s input prefix.

That creates a real modeling problem: if responses are in the “input history,” then admissible histories include client response values as part of the environment-controlled projection. But operationally the implementation chooses responses.

I would rename and separate:

E_req      client invocations
E_resp     client responses
E_send
E_recv
E_int

Then define:

Input(H) = H restricted to E_req ∪ E_recv
Interface(H) = H restricted to E_req ∪ E_resp
Output(H) = H restricted to E_resp ∪ E_send

Then the implementation’s realizable histories are constrained by input schedules, but correctness is judged over interface histories.

This would clean up a lot of later confusion.

At minimum, do not call E_in “input” if it includes responses. Call it E_iface.

⸻

The operational definition and introduction are slightly inconsistent

The improved operational definition says:

the response is enabled immediately: there exists an execution fragment
from p_i's post-invocation state consisting only of internal and output
actions at p_i that produces resp(e,v)_i

Good. This fixes the scheduler-preemption problem.

But the intro still says:

coordination-freedom means that no input action ... intervenes between
an invocation and its response.

That is the older, too-strong phrasing. Under the new definition, input actions may intervene in a particular adversarial schedule; what matters is that the response does not require them.

Rewrite the intro sentence as:

coordination-freedom means that after an invocation, the responding process has a local execution fragment to a response using only internal/output actions, without requiring any further input.

That distinction matters.

⸻

The theorem is still partly semantic and partly operational

You now have two definitions of coordination-free:

1. semantic coordination-free implementation:

R_I(H_in) = A(H_in)
every o ∈ Obs(H) is future-consistent

2. operational coordination-free:

response enabled immediately from local post-invocation state

The semantic definition is still essentially monotonicity by definition. The operational theorem is meant to justify it, but the relationship is not fully clean.

In particular, the semantic definition still requires:

every o ∈ Obs(H) is future-consistent

This is not a property of implementation I; it is a property of Spec. So the phrase “coordination-free implementation” remains odd in the semantic section. It might be better to say:

A specification is semantically coordination-free if ...

and reserve “implementation is coordination-free” for the I/O-automaton property.

Then Complete CALM can be structured as:

1. Semantic lemma:

Spec is semantically coordination-free iff Spec is monotone.

    This is definitional and okay.
2. Operational theorem:

Under assumptions A, B, C, semantic coordination-freedom coincides
with existence of an operationally coordination-free implementation.

That would prevent reviewers from feeling that two different notions are being silently identified.

⸻

Obs(H_i) = ∅ handling is not quite right

The sufficiency proof says:

If Obs(H_i) = empty ... this case does not arise for monotone
specifications at reachable histories, since monotonicity propagates
nonemptiness forward.

Monotonicity does not by itself guarantee nonemptiness. It says outcomes at earlier histories have refinements at later histories. If Obs(H_0) is empty, monotonicity is vacuous forever. If a particular invocation history has no admissible outcome, monotonicity does not create one.

You need a separate totality/availability condition:

Response-totality:
For every reachable local view containing an invocation requiring a
response, Obs(H) contains at least one outcome prescribing such a
response.

Or treat abort/error as an explicit admissible response outcome and require it to be present.

This matters for invariant enforcement: you often use Obs(H)=∅ to mark unrealizable histories. But an available implementation cannot just say “empty” unless it has an explicit abort/error response in the outcome space.

⸻

“Outcome exposed at p” is still informal

Complete CAP defines:

An outcome is exposed at p if p is the process that would communicate
it to a client---formally, if o determines a response to an invocation
event at p.

That is closer, but still not formal enough for a theorem. The operational correctness definition also relies on:

outcome o prescribes response v to invocation e

This should be a first-class relation, e.g.:

Prescribes(o, e, v)

or

Expose_p(o) ⊆ E_resp

Then correctness becomes:

Resp(H) ⊆ Expose(o)

and distributed-monotonicity can quantify over response facts rather than vague “outcomes exposed at p.”

This also helps fix the necessity theorem. Non-monotonicity of a purely internal semantic outcome should not necessarily imply an operational impossibility unless that outcome can be exposed through a response.

A more precise theorem might quantify over exposable outcomes:

For every H, every response fact r that a process may emit at H,
and every relevant future H', there exists o' ∈ Obs(H') explaining r.

⸻

Proper coordination is still formally underdefined

The definition remains:

Spec' = (E, Obs', Ord)
Obs'(H) ⊆ Obs(H)
Spec' is monotone

But the prose says:

fewer admissible outcomes, fewer admissible histories, or both

The definition still cannot express “fewer admissible histories” except by setting Obs'(H)=∅, which generally breaks monotonicity for prefixes that had nonempty observations.

The separation theorem uses:

Define the variant Spec' by restricting to histories in which
→ totally orders E_in.

That is not represented by Obs'(H) ⊆ Obs(H) unless the future relation or admissible history space is part of the spec.

You should change the base specification to include admissible histories/futures:

Spec = (A, Obs, Ord)

where A ⊆ Hist is prefix-closed, or:

Spec = (Hist, ⊑_Spec, Obs, Ord)

Then a coordinated variant can restrict:

A' ⊆ A
Obs'(H) ⊆ Obs(H)
Ord' maybe same or mapped

This is necessary for total-order broadcast, locks, barriers, leader election, and “future restriction” in Table 1.

Right now Table 1’s “future restriction” category is conceptually right but not expressible in the formal definition.

⸻

The separation theorem is overstated

The theorem says:

There exist non-monotone specifications with properly coordinated
variants that Complete CALM can verify but relational-transducer CALM
has no mechanism to certify...

This is plausible, but the proof sketch is not currently rigorous enough.

Issues:

1. The coordinated variant restricts histories, but the formal definition does not support history restriction.
2. It says standard Datalog encodings of linearizability require non-monotone uniqueness constraints. True-ish, but the point is not fully established.
3. The claim “relational-transducer CALM has no mechanism” is a meta-theoretic claim about a framework, not a theorem unless formalized.

I would downgrade this from theorem to proposition/observation unless you want to prove a formal separation from a specified transducer language.

A safer phrasing:

This illustrates a separation in emphasis: relational CALM analyzes whether a program is coordination-free, while Complete CALM can analyze whether the residual interface produced by a coordinated component is monotone.

That is strong enough and less attackable.

⸻

Complete CAP is better but still too strong as an iff theorem

The distributed-monotone idea is good. The distinction between process-local and partition-spanning non-monotonicity is valuable and should stay.

But the theorem:

a specification admits a consistent, available, partition-tolerant
implementation iff it is distributed-monotone

still has the same problems as Complete CALM:

* it relies on informal exposure;
* it does not handle joint consistency of independently emitted responses;
* its sufficiency says “every process can safely expose any admissible outcome,” but outcome selection may not compose;
* its proof is a sketch, not an I/O-automaton theorem;
* availability is not given a precise formal definition in the main section.

I would either:

1. make Complete CAP a corollary of a formally proved local-exposure theorem; or
2. present it as a “semantic CAP principle” rather than a full theorem.

The phrase “Complete CAP” is rhetorically powerful but risky. CAP reviewers are unforgiving. If the theorem is not watertight, the label will attract fire.

⸻

The “universal construction” and frontier claims still overreach

The abstract and contribution list still claim:

a coordination-free frontier construction that derives natural
coordination-free weakenings for any specification

and:

yields new results for queues and search structures

This is exciting, but I would be careful. From the parts I inspected, the frontier machinery still appears to mix:

* weakening the order,
* changing the outcome interface,
* restricting futures,
* and residualizing through a log/order authority.

These are related but not the same. The abstract/contributions should not imply a fully general, mechanically justified construction unless the appendix proves it cleanly.

A safer contribution bullet:

We propose a frontier method for exploring monotone weakenings of a specification and illustrate it on registers, queues, and search structures.

That still sounds interesting and avoids claiming “derives” too strongly.

⸻

What is now genuinely strong

Despite the issues above, several parts are in much better shape.

1. The paper now has a real operational story

The I/O automaton model, fair local scheduling, enabled-response formulation, and indistinguishability proof sketch are the right ingredients. This is a major improvement.

2. The register example is now clearer

The linearizability witness using opposite read observations is a good teaching example. It grounds the whole paper.

3. The distinction between monotonicity and distributed-monotonicity is valuable

This is one of the most interesting conceptual points in the paper:

Some non-monotonicity is local; CAP impossibility comes from non-monotonicity that spans a partition.

That is a nice contribution and worth highlighting.

4. The “proper coordination” idea remains excellent

Even though the formal definition needs work, the idea is very strong:

Coordination can be used internally to discharge non-monotonicity, after which the residual interface can be monotone.

This may be the paper’s most distinctive value beyond “CALM but abstract.”

⸻

Concrete revision plan

If I were revising this version for submission, I would do the following.

1. Split the main result into two results

Use:

Theorem 1: Semantic Complete CALM.
Spec is future-monotone iff every admissible outcome is future-consistent.

Be honest that this is immediate but conceptually clarifying.

Then:

Theorem 2: Operational Complete CALM.
For response-compositional, response-total specifications whose exposed
outcomes are exactly response facts ordered by refinement, operational
coordination-freedom coincides with semantic monotonicity.

Or whatever class of specs you can prove.

This prevents the operational theorem from pretending to cover arbitrary abstract outcome domains.

2. Add explicit assumptions

Something like:

Definition: A response specification is well-formed if:
(i) response-totality,
(ii) response preservation under refinement,
(iii) response-compositionality,
(iv) every semantic outcome relevant to monotonicity is exposable.

Then prove the I/O theorem for well-formed response specifications.

3. Fix the event taxonomy

Replace E_in with:

E_inv, E_resp, E_send, E_recv, E_int

or at least rename current E_in to E_iface.

Define input projection using only actual I/O automaton inputs.

4. Make admissible histories part of the spec

Change:

Spec = (E, Obs, Ord)

to:

Spec = (A, Obs, Ord)

where A is the admissible history/future structure.

Then proper coordination and future restriction become formal instead of rhetorical.

5. Formalize exposure

Add:

Prescribes(o,e,v)

or:

Expose(o)

Then rewrite correctness, distributed-monotonicity, and the necessity proof using that relation.

6. Downgrade the strongest appendix claims

Change “derives new results” to “illustrates a method” unless the frontier proofs are fully formalized.

⸻

Suggested theorem wording

Here is a theorem shape that would be much harder to attack:

Theorem (Operational Complete CALM for response-compositional specs).
Let Spec be a response-total, response-compositional specification
whose outcomes preserve response facts under refinement. Then Spec
admits a correct locally-immediate implementation in the I/O-automaton
model iff every exposable outcome is monotone under admissible futures.

Then you can add:

For specifications whose outcomes are precisely accumulated response
facts ordered by inclusion/prefix/lattice refinement, this condition
coincides with Definition X's monotonicity.

This preserves the main story while making the theorem technically defensible.

For CAP:

Corollary (Semantic CAP).
Under the same response-compositional assumptions, a partition-available
implementation exists iff every locally exposable response survives
every partition-constrained future invisible to the responding process.

That is cleaner than the current universal “consistent, available, partition-tolerant iff distributed-monotone.”

⸻

Final verdict

This revision is a strong step forward. The paper now has the right bones: histories, outcomes, refinement, I/O automata, local enabled response, indistinguishability, and partition-constrained futures.

But the main iff theorem is still ahead of the proof. The remaining gap is not presentation polish; it is a precise mathematical mismatch:

Pointwise monotonicity of abstract outcomes does not automatically yield a distributed implementation whose independently emitted responses are jointly explainable.

Fix that with explicit response-compositionality/exposure machinery, and the paper becomes much more credible.

I would now focus less on adding examples and more on tightening the formal spine. The conceptual narrative is already compelling; the next win is making the theorem exactly as strong as the proof can support.