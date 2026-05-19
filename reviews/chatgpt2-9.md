I read the attached draft carefully. This time the patch did land: I see the four well-formedness conditions, the revised sufficiency proof, the H_2^r construction in necessity, the strengthened joint-consistency remark, the \mathsf{Adm}(\Spec') convention, and the separation result downgraded to a proposition.

This is a real improvement. The sufficiency direction is now much more defensible. But the new necessity proof has exposed a deeper modeling issue: the theorem still quantifies over futures that include implementation-controlled response events, and an implementation should not be required to realize arbitrary future response histories. That is now the main remaining risk.

What is now strong

The joint-consistency story is now convincing under your model. The key sentence is right:

“Response compositionality is not an additional algebraic property of outcomes; it is enforced by evaluating Obs on the full response history.”

Given response soundness and preservation, the sufficiency proof works much better:

o \in Obs(H_i), \quad H_i \hext H

monotonicity gives:

o' \in Obs(H), \quad o \Ord o'

and because H contains all emitted responses, response soundness makes o' explain the whole response trace. That is now a clean argument.

The new proper-coordination definition is also much clearer:

Adm(Spec') = { H | Obs'(H) != empty }

and checking monotonicity only over Adm(Spec') is a reasonable way to model “the coordination layer excludes the other histories.” I still think an explicit admitted-history component would be cleaner, but the current convention is now understandable.

The new necessity proof fixes one gap but reveals another

You fixed the previous problem by constructing:

H_2^r = H_2 \cup { resp(e,v) }

and adding response monotonicity:

Obs(H_2^r) \subseteq Obs(H_2)

So if no outcome in Obs(H_2) refines o, then no outcome in Obs(H_2^r) refines o. That part is good.

But the proof now relies on this step:

Since the spec is well-formed, H_1 contains some pending invocation e
at process p (otherwise Obs(H_1) would be invariant under all
extensions and monotonicity would hold)

That claim is not true as stated. A monotonicity failure can occur at a history with no pending invocation. For example, an already-exposed response/outcome can be invalidated by a later remote event. Operationally, the interesting response happened earlier, not at H_1.

So the necessity proof still needs to connect an arbitrary future-inconsistent outcome to a response point. Full monotonicity says every outcome at every history must refine into every future. Operational coordination-freedom only forces processes to respond at invocation points. These are not automatically the same.

A safer proof would need to show:

Every monotonicity violation can be pulled back to the history at which some response exposing the bad outcome was enabled.

That may be true for your intended response-centric specs, but it is not proved by the current well-formedness conditions.

The deeper issue: futures include response events

This is the bigger concern.

Your history model includes responses as interface events. That was crucial for sufficiency and joint consistency. But then monotonicity quantifies over all future histories:

H_1 \hext H_2

including futures where other processes emit response events.

Those response events are not environment events. They are implementation outputs. So in the necessity proof, if the bad future H_2 contains response events, a particular implementation may simply not produce those responses. That is not “suppressing a history” in the same sense as suppressing a message delivery or input; it is just choosing a different output policy.

This matters because the theorem currently says:

If there exists any future response history that makes o unrefinable, no coordination-free implementation exists.

But an implementation is not required to realize every possible future response history. It only needs to respond according to its own deterministic policy.

This is the price of the elegant response-in-history move: it repairs sufficiency, but it makes necessity delicate. The future relation now mixes:

1. environment/input futures, which the implementation cannot prevent;
2. message-delivery/scheduling futures, which the implementation cannot prevent;
3. response/output futures, which the implementation chooses.

For necessity, the dangerous future must be one the implementation cannot avoid after making the response. If the danger comes only from alternative future responses that the implementation would not emit, that is not an impossibility.

Concrete example shape of the remaining problem

Suppose at H_1, process p can respond either 0 or 1, and the implementation deterministically always responds 0. A future H_2 containing a later response 1 elsewhere may invalidate the outcome corresponding to 0. But if the implementation never emits that later 1, then H_2 is not an unavoidable future for that implementation.

Your current monotonicity criterion treats H_2 as a future merely because it is a well-formed history. The operational proof needs it to be a future that can arise under the same implementation after p responds.

This is exactly where the older distinction between environment histories and implementation/output histories matters.

How I would fix the theorem

I see three possible routes.

Option A: Quantify monotonicity over input/adversary futures only

Define a future relation that extends histories only by events outside the implementation’s choice, e.g.:

H_1 \hext_{\mathit{env}} H_2

where the extension may add invocations, message deliveries, failures, internal forced events, etc., but not arbitrary response events.

Then response events still appear in histories for correctness, but monotonicity/necessity quantifies over adversarial futures rather than all full histories.

The sufficiency proof can still evaluate Obs(H) on full response histories. The necessity proof then becomes cleaner: the dangerous future is one the implementation cannot rule out.

Option B: Keep full histories, but restrict monotonicity to implementation-closed futures

For a given implementation I, define the futures that can actually occur after H_1 under I. Then a specification is coordination-free if there is an implementation whose actual response policy makes all exposed outcomes monotone over its realizable futures.

But this weakens the clean spec-only criterion, because monotonicity becomes implementation-relative. You probably do not want this.

Option C: Treat Obs as an interface contract where every admissible response history must be realizable

This preserves the theorem, but it is very strong. It says a coordination-free implementation must preserve all admissible response possibilities, not merely all environment futures. In other words, if the spec admits two possible future responses, the implementation must be prepared for either to occur.

That may be your semantic stance, but it is not the usual operational stance. If you choose it, the paper needs to say explicitly:

We analyze specifications as nondeterministic interface contracts: all response histories admitted by the specification are considered possible exposures unless the implementation narrows the interface. A deterministic implementation that commits to one response policy is already an outcome restriction.

This would make the theorem more defensible, but also more clearly about preserving all specified nondeterminism, not just avoiding communication.

The new well-formedness conditions are useful but strong

The strengthened response totality now says:

at every well-formed history H containing a pending invocation e,
every o in Obs(H) prescribes an allowed response for e

This is strong. It means outcomes at a history with a pending invocation already commit to a response before the response event is in the history. That is consistent with the causal-view protocol, but it is not a harmless assumption. It makes Obs(H) a set of possible next-response commitments, not merely possible completed observations.

That is okay, but I would rename or explain it more explicitly:

At a response point, outcomes are not just descriptions of completed behavior; they are candidate commitments for the pending invocation.

Otherwise readers may wonder why an outcome must prescribe a response that has not happened yet.

Also, if multiple invocations are pending, the current wording implies every outcome prescribes responses for all of them. Maybe that is intended, but if not, say “for every invocation whose owner is required to respond at H” or “for every pending invocation considered by the availability obligation.”

Response monotonicity needs a slight wording tweak

The condition says:

if H' extends H by adding only response events consistent with outcomes
in Obs(H), then Obs(H') subseteq Obs(H)

“consistent with outcomes in Obs(H)” is ambiguous. Does the added response have to be consistent with every outcome in Obs(H), or at least one?

If it means every outcome, the condition may rarely apply, because different admissible outcomes may prescribe different responses.

If it means at least one outcome, then Obs(H') ⊆ Obs(H) is plausible, but you should say:

adding response events consistent with at least one outcome in Obs(H)

or better:

for any response-only extension H' of H, Obs(H') ⊆ Obs(H).

That last version is simpler and seems to be what you need. Response soundness will make Obs(H') empty if the response contradicts all prior possibilities.

The necessity proof’s alpha/beta construction still needs tightening

Current proof:

Construct two executions: alpha where the system halts at H1 plus p's
response, and beta where the system reaches H2^r.
Since p's state is identical at the moment of response...

This is fine if H_2 \setminus H_1 contains only events scheduled after the response and not implementation-controlled responses that depend on different local states. But if H_2 contains response events at other processes, then beta requires those processes to emit them under the same implementation. That needs justification.

So I would change the proof to either:

* require H_2 \setminus H_1 to be an input/adversary extension, with responses generated by the implementation; or
* state that the contradiction applies only to monotonicity witnesses whose future extension is realizable under the implementation after the response.

Right now it implicitly assumes all well-formed futures are realizable regardless of response policy, which is the questionable part.

Complete CAP still overclaims

The CAP section is conceptually good, but the theorem still says:

a specification admits a consistent, available, partition-tolerant
implementation iff it is distributed-monotone

Given the above issue, CAP has the same problem: partition-constrained futures should probably quantify over input/message-delivery futures, not arbitrary future response histories.

The CAP direction I would trust is:

if a locally exposed response can be invalidated by a partition-constrained adversary future, availability and correctness conflict.

That is strong and clean. The iff remains risky unless you formalize exactly which futures are adversarial and which are implementation outputs.

Smaller edits

The proposition label still says:

\label{thm:separation}

Even though it is now a proposition. Rename to prop:separation.

The abstract still says:

“a complete version of the CAP theorem follows as a corollary”

I would soften this unless the CAP proof gets the same operational care as Complete CALM. Maybe:

“we obtain a CAP-style distributed monotonicity criterion…”

The contribution list still says:

“minimal monotone enlargements … characterize the strongest coordination-free guarantees.”

That is okay if limited to fixed observation interfaces, but I would insert “for a fixed observation interface” directly into that sentence.

Bottom line

This version is significantly improved. The sufficiency proof now works much better, and the response-in-history design has been made explicit enough to carry the joint-consistency argument.

But the necessity proof still has a conceptual gap: not every future history is an adversarial future once histories include implementation-controlled response events. The new H_2^r proof fixes the “post-response” problem only if the dangerous future is otherwise unavoidable or realizable under the same implementation.

So the remaining question is:

Does monotonicity quantify over all well-formed full histories, including arbitrary future responses, or only over futures the environment can force after the implementation exposes an outcome?

If it is all full histories, the theorem is about preserving all nondeterministic interface possibilities, not ordinary operational coordination-freedom. If it is environment-forceable futures, the formal future relation needs to distinguish invocations/deliveries from responses.

I think that is now the core issue to resolve.