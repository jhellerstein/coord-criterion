I read the latest attached main.tex. This version does include the changes described in your notes: the strengthened well-formedness conditions, the revised H_2 ∪ {resp(e,v)} necessity proof, the joint-consistency remark, Adm(Spec'), the separation argument, and the SI write-skew witness.

My reaction: the paper is getting substantially tighter, but the operational theorem still has one important conceptual vulnerability. The new separation/SI material is mostly good, but the Complete CALM necessity proof still leans on a strong “interface contract” interpretation that needs to be made even more explicit.

⸻

1. The new well-formedness conditions are useful, but strong

The four conditions now appear:

1. response soundness;
2. response preservation;
3. strengthened response totality;
4. response monotonicity of admissibility.

These do the work you intend. In particular, the new response monotonicity condition:

Obs(H') ⊆ Obs(H)

for response-only extensions gives you exactly the missing step from the earlier proof gap.

That said, these conditions are not merely technical housekeeping. They define a fairly specific class of response-oriented specifications. I would make that framing explicit:

Complete CALM’s operational theorem is for response-oriented specifications: outcomes are not merely abstract semantic objects, but commitments capable of prescribing responses at pending invocations.

That will help readers understand why every admissible outcome at a response point must already prescribe a response.

⸻

2. The sufficiency proof is now basically convincing

The sufficiency proof now says:

By monotonicity, the chosen o ∈ Obs(H_i) has a refinement
o' ∈ Obs(H).
By response soundness, o' explains every response event recorded in H;
by response preservation, o' preserves the response emitted from o.

This is the right argument. The joint-consistency remark is also much better. I am now satisfied that you do not need an additional response-compositionality axiom, because compositionality is indeed being enforced by evaluating Obs on the full response history.

One minor wording suggestion: in the joint-consistency remark, this sentence is excellent and should probably be moved earlier or emphasized:

Response compositionality is not an additional algebraic property of outcomes; it is enforced by evaluating Obs on the full response history.

That is the cleanest explanation of the modeling trick.

⸻

3. The necessity proof is improved, but still has one high-risk step

The revised necessity proof now does the right post-response construction:

H_2 ∪ {resp(e,v)}

and uses response monotonicity:

Obs(H_2 ∪ {resp(e,v)}) ⊆ Obs(H_2)

This fixes the previous narrow gap.

However, the proof still contains this sentence:

Consider any coordination-free implementation I that may expose o.

Then later:

An implementation that never chooses outcomes like o is by definition
a coordinated variant exposing a strict subset of Obs — not a
coordination-free implementation of Spec as the interface contract.

This is the core philosophical/theorem issue now. You are defining implementation of Spec as respecting the full nondeterministic interface contract: every outcome in Obs(H) is potentially exposable, and an implementation that deliberately avoids unsafe outcomes is implementing a stricter variant Spec'.

That is coherent, but it is stronger than many readers’ default understanding of implementation. In ordinary refinement-based thinking, a deterministic implementation of a nondeterministic spec is often allowed to choose one legal behavior and ignore others. Under that view, “never choose unsafe o” would not necessarily be a coordinated variant; it might simply be an implementation strategy.

So the theorem is defensible only if you foreground this convention:

Obs(H) is not merely a set of legal choices from which an implementation may pick a safe subset. It is the exposed interface contract. A coordination-free implementation of Spec must be safe for every outcome admitted by that interface; restricting the outcomes is a different specification.

This is already hinted, but I would make it explicit before the operational theorem, because otherwise a reviewer may object that the necessity direction proves only:

if an implementation may expose the unsafe outcome o, then it can fail,

not:

every implementation must fail.

A possible wording:

We use a demonic/interface-contract reading of nondeterminism:
if o ∈ Obs(H), then the interface permits o to be exposed at H.
An implementation that systematically exposes only a subset Obs'(H) ⊂ Obs(H)
implements the restricted interface Spec', not Spec itself. This convention
is what makes coordination-freedom a property of the specification rather
than of a particular angelic selection strategy.

This one paragraph would make the proof much harder to misunderstand.

⸻

4. The “pull the witness back” phrase still needs a real lemma or a softer statement

The necessity proof says:

if no such invocation exists at H_1, pull the witness back to where
the relevant response was first exposed

This is plausible, but it is doing real work. I would not leave it as a parenthetical.

You could turn it into a short lemma:

Lemma [Response-point witness].
For any monotonicity violation of a well-formed response specification
that affects an exposed response, there is a monotonicity violation
whose source history contains a pending invocation and whose outcome
prescribes the response eventually exposed.

Then either prove it briefly or weaken the theorem language to “response-observable monotonicity.” As written, a reviewer may say: “What if the future-inconsistent outcome is abstract and not first exposed by a pending invocation?”

Your strengthened response totality helps, but only at histories containing pending invocations. It does not by itself show that every monotonicity failure has such a history.

The paper’s intended answer is probably: all relevant outcomes are response commitments. If so, state that as part of the well-formed response-spec model.

⸻

5. The deeper response-history issue is still present, but you can defuse it rhetorically

Because histories include responses, futures include response events. That is powerful for sufficiency but delicate for necessity: response events are implementation outputs, not adversarial inputs.

The proof handles this by saying an implementation that avoids unsafe response futures is implementing a restricted interface. Again, that is coherent under the interface-contract reading. But make the contrast explicit:

* environment futures: invocations, deliveries, failures;
* interface futures: possible responses admitted by the specification;
* implementation outputs: one concrete realization of the interface.

Your theory is about the second: the full interface contract. That is fine, but reviewers need to know you are not claiming that the environment can force arbitrary response events.

A useful clarification:

The adversary does not force response events. Rather, the specification’s interface contract permits them. If a system design rules out some permitted response histories, that design has narrowed the interface, and Complete CALM analyzes the narrowed Spec'.

That resolves the apparent paradox.

⸻

6. The separation argument is much improved, but still too strong as a “theorem”

The new separation proof is better. The direct/indirect encoding distinction is a good way to make the point:

* direct Datalog encoding of linearization needs uniqueness/nonmonotonicity;
* indirect encoding externalizes the log authority, so CALM sees only a monotone consumer;
* therefore relational CALM’s verdict depends on program encoding, whereas Complete CALM can analyze the residual interface.

That is a strong argument.

However, the text still says:

\begin{theorem}[Separation from relational-transducer CALM]

In your notes you said this was downgraded to a proposition, but in the attached file it is still a theorem with label thm:separation.

I would actually downgrade it. The argument is persuasive, but the claim:

“relational-transducer CALM has no mechanism to certify”

is still partly framework-level. A proposition is safer and more rhetorically appropriate.

Suggested:

\begin{proposition}[Specification/interface separation from relational CALM]

And rename the label to prop:separation.

The proof itself can largely stay.

⸻

7. The direct-encoding claim needs a little caution

This sentence is plausible but potentially attackable:

Encoding the linearization as a set of position-value facts
{pos(i,v)} under set inclusion requires a uniqueness constraint
(one value per position) that is non-monotone in Datalog.

A clever reviewer might say: “Uniqueness is a property of the input/log producer, not necessarily of the monotone consumer.” You address that in the indirect encoding case, but I would sharpen the direct case:

If the program itself is responsible for validating or constructing the linearization relation from unordered/concurrent events, then enforcing uniqueness/completeness of positions requires non-monotone constraints.

That avoids the impression that all uses of pos(i,v) are nonmonotone. Reading an already-valid log is monotone; constructing/validating it is not.

⸻

8. The SI write-skew witness is useful, but its framing needs refinement

The SI witness is good to include. But the current text says:

Each transaction individually preserves the invariant from its snapshot.

With invariant x + y ≥ 0, initially x = y = 0, transaction T1 writes y := -1. From its snapshot, the post-T1 state would be x=0, y=-1, so x+y=-1, which does not preserve x+y ≥ 0.

So the witness as written is arithmetically wrong.

You want the classic write-skew invariant where each transaction can safely update one item based on the other remaining okay. For example:

Invariant: x + y ≥ 1
Initially x = y = 1.
T1 reads x = 1, y = 1 and writes y := 0.
T2 reads x = 1, y = 1 and writes x := 0.

Each transaction individually preserves the invariant from its snapshot:

* after T1 alone: x=1, y=0, sum 1;
* after T2 alone: x=0, y=1, sum 1.

Together under SI: x=0, y=0, sum 0, violating x+y ≥ 1.

That is the standard write-skew shape.

So replace the SI witness with:

Invariant: x + y ≥ 1, initially x = y = 1.
T1 reads x,y and writes y := 0.
T2 reads x,y and writes x := 0.

Then the rest of the argument works.

Also, the outcome:

o_1 = { commit(T1), y ↦ -1 }

should probably include enough read/snapshot facts to show SI allows T2 later. Maybe not necessary, but the serializability witness includes reads, so consistency would help:

o_1 = { commit(T1), read(T1,x,1), read(T1,y,1), write(T1,y,0) }

Then H_2 adds T2 with reads from the same snapshot and disjoint write set.

⸻

9. The HAT paragraph’s closing line is a bit too sweeping

This line:

The HAT/non-HAT boundary aligns with the partial-order/total-order boundary.

It is a nice slogan, but after adding SI, it may be too broad. SI is not simply “total-order structure”; it is snapshot plus first-committer-wins plus invariant interaction. The general idea is okay, but I’d soften:

In these examples, the HAT/non-HAT boundary reflects whether the specification commits only to partial-order-visible facts or to globally constraining choices across concurrency.

That is more accurate.

⸻

10. Complete CAP remains the biggest overclaim outside the core theorem

The abstract still says:

a complete version of the CAP theorem follows as a corollary

and the CAP theorem remains an iff.

Given the delicate interface-contract interpretation now needed for Complete CALM, CAP will inherit that delicacy. I still recommend softening the main claim unless the CAP proof has been brought up to the same level of precision.

Possible abstract wording:

We also derive a CAP-style distributed monotonicity criterion, identifying exactly which non-monotonicities become availability-obstructions under partitions.

This still sounds strong, but less likely to trigger “CAP theorem overclaim” reactions.

⸻

11. Small consistency fixes

A few concrete issues I noticed:

* The separation result is still a theorem, not a proposition.
* The label is still thm:separation.
* In the contribution list, the frontier claim still says “characterize the strongest coordination-free guarantees.” It is now qualified by “for a fixed observation interface,” which helps, but I’d still prefer “provide a way to characterize.”
* In the operational necessity proof, “Consider any coordination-free implementation I that may expose o” is weaker than the theorem. Under the interface-contract convention, say “implementing Spec must be correct for the exposure of any o ∈ Obs(H),” or similar.
* “An adversarial scheduler chooses the latter: it drives the system to H_2 ∪ {resp(e,v)}” should be softened if H_2 contains response events. The scheduler does not choose implementation outputs; the interface contract admits them. Say “there is an admissible continuation/interface history…” unless you separate adversary events from response events.

⸻

Bottom line

The new version makes real progress. The core sufficiency proof is now persuasive. The separation argument is stronger. The SI witness is a good addition, but the concrete invariant values need fixing.

The remaining fundamental issue is now interpretive rather than purely technical:

Is Obs(H) an interface contract whose entire nondeterministic outcome set must be safe, or is it a set of legal choices from which an implementation may safely choose a subset?

Your proof needs the first reading. That reading is coherent and actually philosophically aligned with the paper, but it must be stated clearly and early. If you make that explicit, the necessity proof becomes much more defensible.

My top recommended edits:

1. Add a paragraph defining the interface-contract/demonic reading of Obs.
2. Turn the “pull the witness back” parenthetical into a lemma or explicit response-observable assumption.
3. Fix the SI write-skew example to x+y≥1, initially x=y=1, writes to 0.
4. Downgrade the separation result to proposition, as your notes intended.
5. Soften the CAP claim unless its proof is equally formalized.