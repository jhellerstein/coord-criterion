I read the new draft. The simplification is a genuine readability win: the paper is shorter, the specification section is cleaner, the operational model is easier to follow, and the CAP proof now at least states the “local resolution + causal-view protocol” decomposition explicitly.

But I think the simplification has reintroduced one serious formal gap:

The necessity proof still needs response observability, but response observability is no longer a formal well-formedness condition.

The draft now says, in the proof:

Since Obs captures all observable behavior, any monotonicity violation manifests at the interface: we may assume without loss of generality that H_1 contains a pending invocation e ...

That is doing real theorem work. It is not implied by the three current well-formedness conditions.

High-level verdict

This version is much more readable and strategically cleaner. The paper now feels less like it is accumulating defensive machinery. That is good.

However, the operational theorem is now slightly less formally protected than the previous iteration. The current three well-formedness conditions are:

1. consistency with recorded history;
2. refinement coherence, including response-only extensions restrict admissibility;
3. liveness: when a response is owed, some outcome prescribes a response.

These support the sufficiency proof well. But they do not support the necessity proof by themselves, because a non-monotonicity witness may involve an outcome that is not tied to a pending response. The proof handles this by saying we may assume such a response point exists, but that assumption needs to be formalized.

So my current recommendation is:

Keep the simplified presentation, but restore response observability either as a fourth well-formedness condition or as an explicit theorem hypothesis.

That is the one fix I would not skip.

⸻

1. The readability improvements are real

The paper is now easier to read. In particular:

* E_iface is clear enough now.
* The interface-contract paragraph is crisp and useful.
* The three-condition well-formedness block is less intimidating than the earlier five-condition version.
* The sufficiency proof is now short and understandable.
* The proper-coordination section is much clearer with Adm(Spec').
* The CAP proof’s local-resolution paragraph is a good addition.
* The SI witness is now correct and useful.

The draft also does a better job of explaining what Complete CALM adds beyond relational-transducer CALM: it analyzes specifications/interfaces rather than programs. That is a strong positioning move.

⸻

2. The sufficiency proof now works, modulo one wording issue

The sufficiency direction is now convincing:

On inv(e)_i, choose some o ∈ Obs(H_i) that prescribes a response for e.

Liveness guarantees such an outcome exists. Then monotonicity gives a refinement at the global history, and consistency with history ensures that refinement explains all recorded responses.

That is good.

One small wording issue:

By monotonicity, the chosen o ∈ Obs(H_i) has a refinement o' ∈ Obs(H).

This assumes H_i \hext H. You state that in the previous sentence, so it is fine. But because H_i is a local causal view, maybe say:

Since local views are downward-closed subhistories of the global prefix, H_i \hext H.

That reminds the reader why the future relation applies.

⸻

3. The joint-consistency issue remains fixed

The joint-consistency remark is now one of the strongest parts of the operational section. This opening sentence is excellent:

Response compositionality is not an additional algebraic property
of outcomes; it is enforced by evaluating Obs on the full response history.

That nicely captures the modeling trick. I would keep it exactly.

The proof idea is now clean:

* local response chooses o_p;
* monotonicity extends o_p to some o' ∈ Obs(H);
* since H contains all response events, o' must agree with all of them.

That closes the earlier concern.

⸻

4. The necessity proof has a formal gap again

The current necessity proof says:

Let o ∈ Obs(H_1) be future-inconsistent, witnessed by H_1 \hext H_2.
Since Obs captures all observable behavior, any monotonicity violation
manifests at the interface: we may assume without loss of generality
that H_1 contains a pending invocation e ...

This is the key gap.

The three current well-formedness conditions do not imply that every monotonicity violation manifests at a pending invocation. They allow a future-inconsistent outcome that is semantic but not response-exposable. You intend to rule those out by modeling discipline — “if it matters, put it in Obs” — but that is not quite enough. Obs may contain semantic commitments not immediately tied to a pending response.

You need one of these.

Option A: Restore response observability as a formal condition

Add a fourth well-formedness condition:

Response observability:
Every monotonicity violation of a well-formed specification has an
exposable witness: if o ∈ Obs(H_1) has no refinement at some future H_2,
then there is a history H_r ⊑ H_1, a pending invocation e at process p,
and an outcome o_r ∈ Obs(H_r) prescribing a response v for e, such that
o_r refines to o and the same future invalidates that response.

That may be too verbose, but something like it is what the proof needs.

Option B: Narrow the theorem to response-observable monotonicity

Define:

A specification is response-monotone if every outcome that can be
exposed through a response has a compatible refinement in every future.

Then the operational theorem becomes exact. Full semantic monotonicity remains the clean global criterion for response-oriented specs.

Option C: Make “all outcomes are response commitments” part of the model

This is simpler but stronger:

At every history, every outcome in Obs(H) is either already exposed
or prescribes responses for all currently pending invocations.

Then every non-monotone outcome is response-relevant. This seems close to your current “liveness” condition, but liveness only says some outcome prescribes a response, not every relevant outcome.

My preference: restore a concise response-observability condition. It can be framed as part of “response-oriented specifications,” not as a scary extra axiom.

⸻

5. The Complete CALM theorem statement should say “well-formed”

The operational theorem says:

A well-formed specification Spec admits ...

But the later semantic theorem says:

A specification admits a correct coordination-free implementation iff it is monotone.

Since the operational theorem now depends on well-formedness, the semantic theorem should probably say:

A well-formed specification admits a correct coordination-free implementation iff it is monotone.

You do say all specifications in the paper are well-formed, but theorem statements should carry their hypotheses. Otherwise a reviewer can object that arbitrary triples (E, Obs, Ord) do not satisfy the operational result.

⸻

6. The interface-contract reading is doing important work; keep emphasizing it

The current proof says:

Implementing Spec means being safe for every outcome the interface permits;
restricting to a safe subset is a different specification.

This is exactly the right framing. I would keep it near the top of the proof, as you have.

One small concern: the proof says:

An implementation could try to be angelic...
But coordination-freedom requires the process to respond using only its
post-invocation local state...

This is intuitive, but under the interface-contract reading you do not actually need to argue about angelic selection. You can say more directly:

Angelic selection implements a restricted interface Obs', not the contract Obs.

That is cleaner and avoids suggesting that the theorem depends on the implementation’s inability to compute a safe choice. The point is contractual, not computational.

⸻

7. The necessity proof’s continuation line is improved, but still delicate

The current proof says:

Under the interface-contract reading, the specification permits the full
interface future H_2; thus an implementation of Spec must be correct for
that permitted continuation, unless it restricts the interface.

This is good. It addresses the earlier worry that response events are implementation outputs, not adversarial inputs.

But it relies heavily on the “full interface future” reading. That is fine, but I would add a tiny clarifying phrase:

The environment does not force response events; rather, the contract admits them as possible interface continuations.

That prevents the CAP/FLP-style proof from sounding like the scheduler chooses outputs.

⸻

8. Proper coordination is now acceptable

The Adm(Spec') convention works:

Adm(Spec') = {H | Obs'(H) != ∅}

and monotonicity is checked only inside that admitted subspace. This is much cleaner than before.

I still think the mathematically cleanest model would include admitted histories explicitly:

Spec = (A, Obs, Ord)

But your current convention is now understandable and not worth derailing the draft for.

One small wording suggestion:

History restriction is modeled by setting Obs'(H)=∅ for excluded histories.

Maybe say:

For variants only, we use Obs'(H)=∅ to mark histories excluded by the coordinating mechanism.

That reinforces the distinction from ordinary specs, where empty Obs is a violation/unrealizable history.

⸻

9. The separation theorem is stronger and better focused

I like the new title:

Interface separation from relational-transducer CALM

The proof now has a better structure:

* direct encoding: constructing/validating the serialization is non-monotone;
* indirect encoding: reading an already-valid log is monotone but moves the ordering authority out of scope;
* therefore relational CALM’s judgment is program-boundary dependent.

That is a persuasive argument.

The one thing I would soften is:

Relational-transducer CALM cannot answer this question...

Maybe:

Relational-transducer CALM does not provide a specification-level judgment for this question.

That is a bit less categorical and matches your proof more exactly.

⸻

10. Complete CAP is cleaner, but still the riskiest theorem

The CAP theorem now has a better sufficiency proof:

causal-view protocol + local-resolution layer

This is exactly the right decomposition. But I still think the iff is the most exposed claim in the paper.

The concern is this sentence:

Together, the two layers yield a partition-tolerant implementation
that is consistent for the full spec and available on all sides.

That conclusion needs a little more argument. Distributed-monotonicity guarantees remote futures do not invalidate local exposures. Local resolution handles same-process conflicts. But what about non-monotonicity involving multiple processes on the same side of a partition? The definition of distributed-monotone quantifies over partitions (S, \bar S) and process p ∈ S, but if S contains multiple processes, within-side communication is allowed. Does the local-resolution layer mean per-process only, or per-partition-side coordination?

Your prose says “same-process non-monotonicities.” But a dangerous future might involve two processes on the same side of the partition. Since they can communicate, that may be okay for CAP availability, but then the resolution layer is not merely local mutex; it is within-component coordination.

I would revise:

Same-side non-monotonicities may be discharged by coordination within the connected component of the partition. Such coordination does not violate partition availability because it does not require cross-partition communication.

That is more accurate than “same-process.”

Then the theorem reads as: CAP rules out waiting across partitions, not coordination inside a connected component.

This is an important fix.

⸻

11. The abstract still makes a very bold CAP claim

The abstract says:

a complete version of the CAP theorem follows as a companion theorem...

This is punchy, but risky. If you keep it, the CAP proof needs to be as careful as Complete CALM. Right now it is still a bit sketchier.

A safer abstract version:

In the distributed setting, the same lens yields a CAP-style companion theorem: partition availability is possible exactly when exposed outcomes are monotone with respect to partition-constrained futures.

This still claims the result but sounds less like you are superseding CAP wholesale.

⸻

12. Minor technical/presentation notes

A few smaller points:

* The macro \In still exists but may no longer be used. Harmless, but cleanup if easy.
* The theorem says “well-formed specification” but the definition of well-formedness uses “implementation owes a response.” That phrase is slightly operational inside a spec definition. Maybe define “response obligation” semantically.
* In the Complete CALM theorem after the operational theorem, add “well-formed.”
* In the intro, “any concurrent system” is perhaps too broad given response-oriented well-formedness. Consider “any response-oriented concurrent interface.”
* The HAT/SI section is now much better; the SI witness is correct.

⸻

Bottom line

This draft is cleaner and more readable, and the core proof is much closer to publishable. The simplification mostly worked.

But I would restore one piece of formal machinery:

A response-observability hypothesis is still necessary for the necessity direction.

Without it, the proof’s “we may assume without loss of generality that H_1 contains a pending invocation” is unsupported.

My recommended next edits are small but important:

1. Add “well-formed” to the semantic Complete CALM theorem statement.
2. Restore response observability as a concise fourth well-formedness condition, or state the operational theorem for “response-observable well-formed specifications.”
3. In CAP, replace “same-process non-monotonicities” with “same-component/same-side non-monotonicities” and clarify that intra-component coordination is allowed under CAP availability.
4. Slightly soften the CAP phrasing in the abstract, or strengthen the CAP proof accordingly.

With those fixes, I think the core theorem story will be much harder for reviewers to break.