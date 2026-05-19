I read the new version carefully. This draft is substantially better and the targeted fixes mostly landed. The paper now has a much more defensible formal core than the earlier versions.

The biggest improvement is that the response-events-in-history move is now explicit through well-formedness. That repairs the earlier “joint consistency” concern. I think the sufficiency direction is now basically on the right track.

However, the necessity proof still has a real gap, and it is now the main remaining theorem-level vulnerability. The new “schedule the dangerous future after the response” idea is the right instinct, but the proof does not yet show that the violation persists at the actual post-response history where correctness is checked.

Below is the careful review.

⸻

Executive assessment

The new draft fixes several previously serious issues:

1. E_iface is much clearer than the old E_in.
2. Response soundness, preservation, and totality are now formalized.
3. The operational theorem is now explicitly for well-formed specs.
4. The sufficiency proof now invokes response soundness/preservation correctly.
5. The proper-coordination section now clearly distinguishes excluded residual histories from ordinary Obs(H)=∅ failures.
6. The separation result is now a proposition rather than an overclaimed theorem.
7. The frontier language is softened in the abstract.

Those are real repairs.

The main remaining issues are:

1. Necessity still assumes more than non-monotonicity provides.
2. Response totality is not quite strong enough for the causal-view protocol as written.
3. The proper-coordination convention is workable but still formally second-class compared with an explicit admitted-history set.
4. Complete CAP remains more theorem-heavy than the formal development supports.
5. The frontier/contribution language is softened in the abstract but still fairly strong in the contribution list.

⸻

1. Joint consistency is now basically fixed

The response-soundness condition is the key repair:

if H contains resp(e,v), then every o ∈ Obs(H) prescribes response v for e.

Together with response preservation, this makes the sufficiency proof credible.

The crucial argument is now:

o_p ∈ Obs(H_p)
H_p ⊑ H
monotonicity gives o' ∈ Obs(H) with o_p ⪯ o'

Then:

* by response preservation, o' preserves the response produced from o_p;
* by response soundness, o' agrees with all response events already recorded in H.

So o' explains the whole response trace, not just the one local response.

That is a good move. I would keep it. I no longer think you need a separate response-compositionality axiom, provided the model remains “histories include responses, and outcomes at a history must respect all recorded responses.”

One small suggested wording improvement in the remark:

Response compositionality is not an additional algebraic property of outcomes; it is enforced by evaluating Obs on the full response history.

That sentence would make the modeling trick even clearer.

⸻

2. Sufficiency is now close, but response-totality should be slightly strengthened

The current response-totality condition says:

at every reachable history containing an invocation requiring a response,
Obs(H) ≠ ∅ and some outcome prescribes an allowed response.

But the protocol says:

computes Obs(H_i), chooses o ∈ Obs(H_i), and immediately responds
with v where v is o's prescription for e.

There is a small mismatch: response totality guarantees some outcome prescribes a response, not that every outcome does. The protocol should either:

1. choose an o ∈ Obs(H_i) that prescribes a response to e, or
2. well-formedness should require that every outcome in Obs(H) prescribes a response for every pending invocation requiring a response.

The simplest patch is in the protocol:

On inv(e)_i, the process chooses an outcome o ∈ Obs(H_i) that
prescribes an allowed response v for e, whose existence is guaranteed
by response totality.

Then the proof is fine.

Also, the line:

No input action intervenes.

still sounds like the old scheduler-sensitive property. Since the formal definition is enabled-response, I would change this to:

This response is enabled without requiring any further input action.

That is a small but important consistency fix.

⸻

3. The necessity proof is still not quite sound

This is the main remaining issue.

The new necessity argument says:

Let o ∈ Obs(H1) be future-inconsistent, witnessed by H1 ⊑ H2,
with o prescribing response v to invocation e at process p.
...
The additional events in H2 \ H1 can be scheduled after p's response.
...
Execution beta: p responds with v; then H2 \ H1 occurs, reaching
global history H2 extended with p's response.
...
In beta, the global history is H2 and no o' ∈ Obs(H2) refines o.
Correctness is violated.

There are two related problems.

3.1 The actual final history is not H2

If H1 did not already contain resp(e,v), then after p responds, the final beta history is not H2. It is something like:

H2^r = H2 ∪ {resp(e,v)}

with the response event inserted after the invocation and before or concurrent with some later events.

Correctness is checked at H2^r, not at H2.

The monotonicity witness gives:

no o' ∈ Obs(H2) with o ⪯ o'

But the proof needs:

no o' ∈ Obs(H2^r) with o ⪯ o'

That does not follow automatically. Adding a response event changes the history at which Obs is evaluated. Since Obs is arbitrary apart from well-formedness, it is possible in principle that Obs(H2) has no refinement of o, but Obs(H2^r) does.

In normal specs, adding a response event should constrain Obs, not create new refinements. But that is another well-formedness/monotonicity-of-admissibility condition, and it is not currently stated.

You need either:

Option A: choose the monotonicity witness so H2 already contains the response

Require the witness to be:

H1 ⊑ H1^r ⊑ H2

where H1^r includes resp(e,v), and no refinement of o exists in Obs(H2).

But ordinary non-monotonicity does not guarantee such a witness.

Option B: add a “response extension cannot restore validity” condition

Something like:

Response restriction:
If H ⊑ H^r adds only response events consistent with o, then
any o' ∈ Obs(H^r) refining o implies there exists some
\bar{o} ∈ Obs(H) refining o.

Equivalently, adding a response event may restrict admissible outcomes, but may not make a previously impossible refinement possible.

This is a natural condition, but it needs to be stated.

Option C: prove necessity using histories where the response is already present

You might define operationally relevant monotonicity failures over histories that include the response event being exposed. That would align semantic and operational checking more cleanly, but it changes the theorem statement.

Right now the proof jumps from failure at H2 to failure at H2 + response. A reviewer will likely catch that.

3.2 Response totality does not guarantee the bad outcome prescribes a response

The proof says:

with o prescribing response v to invocation e at process p
(response totality guarantees such an outcome exists)

Response totality guarantees that at a reachable history with a pending invocation, some outcome prescribes a response. It does not guarantee that the particular non-refinable o in the monotonicity violation prescribes a response.

A non-monotonicity failure could involve an outcome that has no immediate client-visible response prescription. Then the operational impossibility argument does not apply.

You can fix this one of three ways:

1. Require every outcome in Obs(H) at a response-required history to prescribe a response.
2. Define monotonicity only over exposable outcomes.
3. Strengthen the theorem’s condition to “exposable monotonicity” rather than full monotonicity.

Given your current direction, the easiest is probably:

Response totality/prescription completeness:
At every reachable history containing an invocation requiring a response,
every outcome in Obs(H) prescribes an allowed response for that invocation.

But that may be too strong for specs with partial outcomes. A more surgical fix is:

The operational theorem applies to response-complete specifications,
where every admissible outcome at a response point is exposable.

Then your theorem is clean.

⸻

4. The necessity proof’s “schedule after response” idea is promising but needs formal support

The insight is good:

Under strong local-immediacy, p must respond before knowing which future will materialize; the dangerous future can occur after the response.

That is the right way to avoid the earlier p-silent/pre-response indistinguishability issue.

But to make it fully rigorous, the proof needs to show:

1. p can emit the response after H1;
2. the future events H2 \ H1 can still be scheduled after that response without violating causal closure;
3. the resulting history is a valid future;
4. the resulting history has no admissible outcome explaining the response.

Point 4 is the currently missing part.

A possible rewrite of the necessity proof could be:

Let H1 ⊑ H2 and o ∈ Obs(H1) witness non-monotonicity.
Because the spec is response-complete, choose an invocation e at p
whose response v is prescribed by o. Let r = resp(e,v), and let
H1^r be H1 extended with r. Coordination-freedom requires r to be
enabled from p's post-invocation state. Schedule r, then schedule the
events of H2 \ H1, obtaining H2^r. By response-restriction
(or by choosing the witness to include r), no outcome in Obs(H2^r)
can explain r while refining o. Therefore correctness fails.

But this needs the missing response-restriction lemma/condition.

⸻

5. Semantic vs operational Complete CALM is better, but still a bit conflated

The draft now says the operational theorem yields the semantic criterion. That helps. But you still have a semantic definition of coordination-free implementation whose condition (ii) is spec-level:

every o ∈ Obs(H) is future-consistent

You acknowledge this, but it remains rhetorically delicate. I would slightly rephrase:

We call a specification semantically coordination-free when every admissible outcome is future-consistent. An implementation is semantically coordination-free when it realizes all admissible input histories and exposes only such outcomes.

This keeps “implementation” from bearing a condition that is not really implementation-dependent.

Not a blocker, but a reviewer who is sensitive to definitional theorems may still poke here.

⸻

6. Proper coordination is now acceptable, but the convention should be named

The updated proper-coordination clarification is good. It now explicitly says that Obs'(H)=∅ marks histories excluded by the coordination mechanism, and monotonicity is checked only over the admitted subspace.

That is workable.

However, this is a different use of Obs=∅ from the main theorem, where Obs(H)=∅ at a future is a monotonicity failure. The draft now says that distinction explicitly, which is good.

I would give the admitted subspace a name:

Adm(\Spec') = { H | Obs'(H) ≠ ∅ }.

Then define:

Spec' is monotone over Adm(Spec') if for all H1,H2 ∈ Adm(Spec')
with H1 ⊑ H2, ...

This would make the definition more readable and less ad hoc. It also gives reviewers a crisp handle.

Longer term, I still think the mathematically cleaner route is:

Spec = (A, Obs, Ord)

where A is an explicit admitted-history space. But your current convention is probably acceptable if named clearly.

⸻

7. Complete CAP is still the boldest overclaim

The Complete CAP theorem remains the section I would be most nervous about after the operational necessity proof.

The theorem says:

a specification admits a consistent, available, partition-tolerant
implementation iff it is distributed-monotone.

The proof is still more of a semantic sketch than an operational theorem. In particular:

* “exposed at p” is still informal;
* availability is not formalized in the main theorem;
* distributed-monotonicity is weaker than full monotonicity, so the causal-view protocol from Complete CALM does not automatically provide a correct implementation outside partition-constrained futures;
* local non-monotonicity is said to be resolvable locally, but no implementation model for that local coordination is given;
* the same “post-response history” issue from the necessity proof applies here too.

I like the conceptual section. I would be cautious about the iff theorem. A safer statement would be:

Distributed-monotonicity characterizes the CAP obstruction: if it fails,
then some locally exposed outcome can be invalidated by a partition-
constrained future, forcing a choice between availability and correctness.

Then perhaps:

Under the same well-formedness and local-resolution assumptions as
Theorem X, distributed-monotonicity is sufficient.

Right now the theorem wording is stronger than the proof.

Also, the abstract still says:

“a complete version of the CAP theorem follows as a corollary”

That is rhetorically powerful, but CAP claims attract scrutiny. If you keep it, the formal proof needs to be much tighter.

⸻

8. The contribution list still overstates the frontier slightly

The abstract softened the frontier claim nicely:

methodology for exploring the strongest monotone weakenings of a fixed observation interface

But the contribution list still says:

minimal monotone enlargements of the declared order characterize the strongest coordination-free guarantees.

That is stronger. It may be okay in the appendix, but earlier reviews suggested that examples sometimes change the interface, not just enlarge the order. The next sentence partially handles this:

More generally, weakening the interface itself yields coordination-free alternatives.

I would soften the first sentence slightly:

for a fixed observation interface, minimal monotone enlargements of the declared order provide a way to characterize strongest coordination-free guarantees.

“Provide a way to characterize” is less absolute than “characterize.”

Also, “yields new results for queues and search structures” is still a bit bold. It may be fine, but make sure the appendix proofs are rigorous enough.

⸻

9. A subtle issue: reachable history in response totality is undefined

The well-formedness condition says:

at every reachable history containing an invocation requiring a response...

Reachable under what?

* reachable in the semantic history space Hist?
* reachable by some implementation?
* reachable by the causal-view protocol?
* reachable and admitted, i.e. Obs(H) ≠ ∅?
* reachable from the empty history by future extension?

Because this is a condition on specifications, not a particular implementation, “reachable” should be defined semantically.

Maybe:

A history is reachable if it is well-formed and belongs to the intended
admissible history space of the specification.

But since the spec is still (E, Obs, Ord) without an explicit admitted-history set, you might instead say:

at every well-formed history H with Obs(H) intended nonempty and
containing an invocation requiring a response...

This is awkward. Another reason an explicit admitted-history set would clean things up.

A simple local patch:

Response totality: for every well-formed history H at which an invocation
e is pending and the specification requires an available response, there
exists o ∈ Obs(H) prescribing an allowed response for e.

Avoid “reachable” unless defined.

⸻

10. Some small textual fixes

A few local edits I’d make:

In the sufficiency proof

Replace:

No input action intervenes.
(Response totality guarantees Obs(H_i) ≠ empty ...)

with:

By response totality, choose such an o that prescribes an allowed
response to e. The response is enabled without requiring any further
input action.

In the necessity proof

Replace:

response totality guarantees such an outcome exists

with something more accurate, or add a stronger well-formedness condition.

For example:

For response-complete specifications, every outcome at a response point
prescribes a response; let v be the response prescribed by o.

In the CAP proof

Replace:

The causal-view protocol of Theorem 1 provides the implementation

with something more qualified, unless distributed-monotonicity plus local resolution has been proved to support that protocol.

In the abstract

Maybe weaken:

a complete version of the CAP theorem follows as a corollary

to:

we obtain a CAP-style distributed monotonicity criterion...

unless you are ready to defend the full iff.

⸻

Revised verdict

This is the best draft so far. The sufficiency side is now quite plausible, and the “response events are part of history” move is formalized enough to answer the joint-consistency objection.

But the necessity proof still needs one more careful turn. The current proof shows the right intuition, but it does not yet prove that a monotonicity failure at H2 remains a correctness failure at the actual history where p has responded and the future has materialized.

The fix is probably one of:

1. strengthen well-formedness with response-completeness and response-restriction;
2. define operational monotonicity over histories that already include the response event;
3. narrow the theorem to exposable monotonicity;
4. or add a lemma proving that every semantic monotonicity failure can be transformed into a post-response monotonicity failure.

If you solve that, the core theorem becomes much harder to attack.

My current confidence:

* Sufficiency: high, after minor wording fixes.
* Necessity: medium-low; promising but still has a real formal gap.
* Proper coordination: acceptable with named admitted-history convention.
* Complete CAP: conceptually strong, theorem still too strong.
* PODS viability: substantially improved; remaining risk is concentrated in the necessity theorem and CAP overclaiming.