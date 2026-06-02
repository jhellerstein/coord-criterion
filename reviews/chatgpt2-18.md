Here’s my appendix-focused review, setting aside the body except where the appendices must align with it.

Overall appendix assessment

The appendices are useful and mostly in the right order. They now serve three roles:

1. Proof support for operational adequacy and CAP.
2. Extended examples/constructions: frontier, universal ordering authority, CALM hierarchy.
3. Positioning material: classical coordination requirements.

That is the right split. The appendices do not need to be as polished as the body, but they do need to avoid reopening formal objections that the body has worked hard to defuse.

The main appendix risks are:

* the operational appendix still sounds like ordinary existential implementation correctness in places, while the body relies on demonic exposure;
* the CAP appendix still has a relatively sketchy sufficiency direction;
* the frontier appendix makes strong minimality claims that need more careful assumptions;
* the universal construction appendix is good, but occasionally drifts toward “all downstream computation is coordination-free” in ways that should be explicitly tied to the residual interface.

⸻

Appendix A: Operational Adequacy

What works

The sufficiency proof is clear. The causal-view protocol is easy to understand:

On inv(e)_i, process adds e to H_i, computes Obs(H_i), picks o ∈ Obs(H_i), responds with o(e).

The joint-consistency argument is also good. It is now one of the cleanest formal explanations of why independent local responses compose:

because Obs(H) is evaluated on the full history including all response events.

That should stay.

Main issue: necessity should match demonic exposure more explicitly

The necessity proof still says:

no correct coordination-free implementation of Spec exists

then uses:

an adversary may hold the implementation to o as the operative interpretation

This is fine under the demonic interface-contract reading, but the appendix should repeat that convention explicitly before the proof. Otherwise a reader who skipped or forgot the body will read “implementation” in the ordinary trace-refinement sense and object.

Suggested insertion before the proof:

In the necessity direction, correctness is understood in the demonic
interface-contract sense of Section~X: every outcome in Obs(H) is a
permitted exposure of the interface. An implementation that avoids some
permitted outcomes is implementing the restricted interface Obs' ⊂ Obs,
not Spec itself.

That one paragraph would align the appendix with the body.

Potential issue: post-response history

The proof still jumps from exposure at H_1 to correctness at H_2. If the exposure of o is a response event not already in H_2, the actual history after the exposure and future continuation is something like:

H_2^r = H_2 ∪ {resp(e,v)}

You can avoid the issue in either of two ways:

1. Define the witness so that H_1 already includes the exposure/response event.
2. Or explicitly add the response-extension step and use the “response events only restrict admissibility” condition.

I would add the explicit step in the appendix because it is cheap and robust:

Let r = resp(e,v) be the response exposing o, and let H_2^r be the
history obtained by adding r to H_2. Since adding response events can
only restrict Obs, Obs(H_2^r) ⊆ Obs(H_2). Thus no outcome in
Obs(H_2^r) refines o either.

This closes a nitpick before it appears.

Small wording issue

This sentence:

The environment may schedule the continuation producing H_2.

should be changed to:

The interface contract admits a continuation to H_2.

or:

An admissible continuation reaches H_2.

Since histories include responses, “environment schedules” can sound wrong.

⸻

Appendix B: Complete CAP

What works

The appendix now correctly frames availability as semantic availability and admits that stronger fairness-based versions exist. That is helpful.

The proof also now says same-side non-monotonicities can be resolved by coordination within the connected component. That is the right CAP distinction: CAP forbids relying on communication across the partition, not coordination within a connected component.

Main issue: sufficiency is still too compressed

The sufficiency proof currently says, in effect:

distributed-monotonicity rules out cross-partition non-monotonicities; same-side non-monotonicities are handled by intra-component coordination; therefore correctness and availability hold.

That is the right idea, but for a “formal treatment” appendix it needs a little more construction.

I would add a short implementation sketch:

Under a partition, each connected component runs an internal resolver
for non-monotonic choices whose witnesses lie wholly inside the component
(e.g., serialization, locking, or any coordinated implementation of the
component-local residual spec). Across components, processes expose
outcomes using the causal-view protocol. Distributed-monotonicity ensures
that no future consisting only of activity outside the component can
invalidate such an exposure.

Then conclude:

Because no step waits for messages across components, partition availability is preserved.

That would make the sufficiency direction much less hand-wavy.

Necessity should inherit demonic exposure

The necessity direction says:

If p exposes o...
If p withholds o...

Given the body’s convention, this is right, but the appendix should explicitly say:

As in Theorem X, exposure is demonic: if o ∈ Obs(H) is permitted at p, a CAP-available implementation of the full interface must be safe for exposing it.

Otherwise the same angelic-subset objection can return.

Availability definition is weaker than standard CAP

You call it semantic availability, which helps. I would keep that language everywhere. Avoid saying simply “available” in the appendix proof when you mean “maximally available under this semantic definition.”

Maybe add:

This theorem identifies the semantic CAP obstruction. Standard liveness
formulations can be layered on by requiring fair local progress of the
chosen implementation.

That avoids CAP-theorem purist objections.

⸻

Appendix C: Coordination-Free Frontier

This appendix is interesting, but it is the one most likely to draw technical scrutiny if the claims are too strong.

Register frontier

The monotonicity proof is mostly fine, but I see a subtle issue in this line:

past(r, H_2) ⊇ past(r, H_1)

Given your future definition says old events’ pasts are not changed by new events, for reads already in H_1 this should probably be equality, not just superset:

past(r, H_2) = past(r, H_1)

If the model allows adding causal predecessors to old events, then the future definition would be odd. Earlier you used downward-closedness to prevent that. I’d write:

no new event in H_2 enters the causal past of an event already in H_1.

Then equality follows for old reads. It’s okay if you leave superset, but equality is cleaner and prevents causal-order confusion.

Register maximality proof may still overclaim

The proof says any missing causal-prefix edge can be forced as the unique causally consistent extension by adding a read whose only causal-past write is w(v).

That works only if the removed edge corresponds to appending exactly such a read operation. But an arbitrary edge in the causal-prefix order may correspond to appending a write, or multiple operations, or an operation whose result is not uniquely forced.

You may need to weaken or refine the proposition:

* either prove maximality only for single-read extension edges, then extend by induction;
* or state the interface/order is generated by these primitive read-extension refinements;
* or soften “maximality” to “causal consistency lies on the frontier under the primitive read-extension comparison.”

This is worth tightening, because “frontier” claims invite reviewers to test edge cases.

Queue/search structures

The queue and search subsections are useful, but the minimality arguments need the same discipline:

For each, explicitly state:

1. What is fixed: E, Obs, or interface?
2. What is being weakened: order only, or Obs too?
3. What are the primitive refinement edges?
4. Why removing any such primitive edge creates a monotonicity failure?

If any example changes the observation interface, say so directly and avoid presenting it as merely an order enlargement.

Suggested appendix wording

For the whole frontier appendix, I’d add one cautionary framing sentence:

The maximality arguments below are relative to the stated interface and
primitive refinement generators. They should be read as frontier results
for those interface choices, not as uniqueness theorems over all possible
weakenings.

That protects you from over-broad interpretation.

⸻

Appendix D: Universal Construction

This appendix is conceptually important and mostly well-framed.

What works

You now explicitly say:

The ordering service is itself ongoing coordination.

Good. That prevents the dangerous misread that consensus somehow becomes coordination-free.

You also correctly frame the construction as creating a new residual output interface, not preserving the original interface. That is essential.

Main thing to watch

The final paragraphs still sometimes say things like:

process all subsequent computation coordination-free

or:

all remaining computation is monotone local accumulation

These are right downstream of the ordering authority, but I would keep repeating that boundary:

downstream consumers are coordination-free relative to the ordered-prefix interface.

You do say this several times; just make sure every strong sentence has that qualifier nearby.

Membership-change argument

Your argument that authority i+1 is appointed during the reign of authority i via a monotone vote is good. I would make that explicit in the appendix:

The initial seed authority is the only open-world authority commitment.
After that, authority changes are entries authorized by the current
authority; observing another certified transition extends the authority
chain rather than invalidating it.

This is a crisp version of the point and avoids the “but reconfiguration is coordination!” objection.

Stratified Datalog remark

This is useful, but be careful with:

zero additional rounds of distributed coordination

I know what you mean: no additional non-monotone distributed authority choices beyond membership/order. But waiting for end-of-data signals from all participants is distributed communication. To avoid nitpicks, say:

zero additional rounds of distributed coordination in the sense of resolving incompatible futures; the barriers are monotone waits over known participants.

That is precise.

⸻

Appendix E: CALM hierarchy

This appendix is short and useful.

Main issue: \mathcal{A} appears but main spec may not define it

You write:

with \mathcal{A} restricted to histories...

If the main framework no longer explicitly has an admissible-history component \mathcal{A}, this may confuse readers. Either:

* define \mathcal{A} locally as “the admitted history space induced by Obs(H)≠∅,” or
* rewrite as “restricting the history space to histories…”

Suggested:

Under the transducer instantiation, restrict the admitted history space
to histories in which every node's system relation contains...

Avoid introducing \mathcal{A} unless it is defined.

Domain-independence paragraph is good

The discussion that queries using All are coordination-free given membership knowledge but not monotone under input growth is helpful. It connects to your semantic treatment nicely.

⸻

Appendix F: Classical coordination requirements

This appendix is probably fine as long as it remains illustrative.

The table format is useful. Just make sure every row’s “non-monotonicity pattern” matches the body’s terminology:

* outcome invalidated by future;
* authority closure;
* quorum/knowledge closure;
* invariant violation;
* partition-constrained future.

I would avoid strong claims in this table unless they have proof elsewhere. Treat it as explanatory synthesis.

⸻

Appendix-wide polish priorities

If time is limited, I’d prioritize in this order:

1. Operational appendix: align necessity with demonic exposure and add the H_2^r response-extension step or define exposure as already in H_1.
2. CAP appendix: strengthen sufficiency construction with same-component resolver + causal-view protocol.
3. Frontier appendix: clarify assumptions and narrow maximality claims to stated interfaces/generators.
4. Universal construction: qualify downstream coordination-freedom and state authority-chain monotonicity crisply.
5. CALM hierarchy: remove/define \mathcal{A}.

The appendices do not need to be beautiful, but they must not undercut the body’s carefully tuned semantics. The main risk is not style; it is appendix proofs accidentally reverting to older phrasings like “environment schedules responses,” “ordinary correct implementation,” or unqualified “everything downstream is coordination-free.”