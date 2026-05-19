I read the attached draft. It is cleaner and more coherent than the prior versions, especially in the flow from semantic coordination-freedom to the operational theorem. The demonic exposure paragraph is now doing the right conceptual work, and the CAP section is more careful about same-side/intra-component coordination.

That said, I do not think the formal story has fully converged yet. The remaining issue is now quite specific:

The proof of necessity uses demonic exposure, but the formal definition of operational correctness is still existential over actual response traces.

So the paper now explains the intended demonic/interface-contract reading, but the I/O-automaton theorem has not quite internalized it formally.

⸻

What is strong now

The presentation is much improved. The “interface contract: demonic exposure” paragraph is exactly the right conceptual move:

Obs(H) is an interface contract ...
We treat these outcomes demonically, as in model checking ...
An implementation that systematically excludes some Obs'(H) ⊂ Obs(H)
is implementing a coordinated variant, not Spec.

This is clear, and it directly addresses the angelic-selection objection.

The joint-consistency remark remains strong. The statement that response compositionality is enforced by evaluating Obs on the full response history is a very nice piece of the theory.

The proper-coordination section is now readable and well-motivated. The Adm(Spec') convention is clear enough.

The separation theorem is also much better: the “program-boundary” framing is the right way to distinguish Complete CALM from relational-transducer CALM.

⸻

Main remaining concern: operational correctness does not mention demonic nomination

The operational correctness definition says:

An implementation is correct for Spec if for every execution prefix
with induced history H, there exists o ∈ Obs(H) such that o(e)=v
for every response (e,v) recorded in H.

This is existential. It says the implementation’s actual trace must be explainable by some outcome in Obs(H).

But the necessity proof says:

By demonic exposure, a correct implementation must be safe under
every admissible interpretation; in particular, an adversary may
hold the implementation to o as the operative interpretation at H1.

That universal/demonic obligation is not present in the formal correctness definition.

So a reviewer can still say:

Your operational implementation only has to produce actual responses that are explained by some admissible outcome. It does not have to be correct relative to every o ∈ Obs(H) unless that is part of the implementation relation.

This is not a conceptual objection anymore; the paper’s prose explains your intention. It is a formal alignment issue.

Minimal fix

Define correctness under demonic exposure explicitly. For example:

An implementation is demonically correct for Spec if for every execution
prefix with history H, every nominated outcome o ∈ Obs(H) compatible
with the responses recorded in H, and every admissible continuation H'
of H, there exists o' ∈ Obs(H') with o ⪯ o' and o' explains the
responses recorded in H'.

That is perhaps too strong/wordy, but something like it needs to appear.

A lighter version:

Under demonic exposure, correctness is universal over permitted
outcomes: an implementation of Spec must be safe for every
o ∈ Obs(H) that the interface permits at H. The existential
definition above checks only trace explanation; the demonic
interface contract additionally requires every such explanation
to be future-consistent.

Then the theorem can say:

A well-formed specification admits a demonically correct
coordination-free implementation iff it is monotone.

Or:

A well-formed interface contract is operationally coordination-free
under demonic exposure iff it is monotone.

That would align the proof with the definitions.

⸻

The necessity proof still feels partly semantic, not operational

The necessity proof says:

Let o ∈ Obs(H1) be future-inconsistent...
an adversary may hold the implementation to o as the operative
interpretation at H1.

This is a semantic/model-checking argument, not quite an I/O-automaton indistinguishability argument. That is fine if you frame it correctly.

Right now the theorem says:

A well-formed specification admits a correct coordination-free
distributed implementation iff Spec is monotone.

But the necessity proof is really proving:

Under demonic exposure semantics, if the interface contract permits a future-inconsistent outcome, then the interface is not safely coordination-free.

That is slightly different from standard “there exists no deterministic I/O automaton implementation whose actual traces are correct.”

I would adjust the theorem title or statement:

Theorem [Complete CALM, operational interface form].
A well-formed interface contract admits a demonically safe
coordination-free implementation iff it is monotone.

This would avoid the impression that ordinary angelic refinement semantics are being used.

⸻

Response totality / NULL response still needs a small clarification

The current well-formedness condition says:

for every invocation e in H and every o ∈ Obs(H), o(e) is defined
(possibly as a designated NULL response).

Then the protocol says:

picks any o ∈ Obs(H_i), and immediately performs resp(e, o(e)).

If o(e) may be NULL, does the implementation literally respond with NULL? Is NULL an allowed user-visible response? Or does NULL mean “this outcome does not constrain e”?

If NULL means “not constrained,” then the protocol cannot respond with it unless NULL is an actual allowed response value. If NULL is an actual allowed response, say so.

Suggested wording:

NULL is treated as an ordinary distinguished response value when the specification intentionally leaves an invocation unconstrained.

Or, if that is not intended:

At a response point, every o ∈ Obs(H) must assign a non-NULL response to the pending invocation.

This matters because the sufficiency protocol chooses arbitrary o.

⸻

The abstract still slightly overstates the operational theorem

The abstract now says:

The semantic criterion needs only a specification mapping execution
histories to outcome sets under a declared refinement order.
...
For faithful response-oriented interfaces, we prove an operational
I/O-automaton theorem...

This is much better. But a few lines later:

Complete CALM: a specification admits coordination-free implementation
iff its outcomes are monotone

That omits the “faithful response-oriented / demonic exposure” caveat.

I would change that sentence to:

This yields Complete CALM: semantically, a specification is coordination-free iff its outcomes are monotone; for faithful response-oriented interfaces, this semantic criterion exactly matches operational coordination-free implementation.

That separates the two claims cleanly.

⸻

CAP remains bold, but now more defensible

The CAP section is improved. This is the right structure:

* non-monotonicity confined to one side can be handled by same-side coordination;
* only cross-partition invalidation creates the CAP dilemma;
* distributed-monotonicity is monotonicity with respect to partition-constrained futures.

The sufficiency proof is still a bit compressed, but the “same-side resolution layer” paragraph helps.

One thing I would adjust:

Complete CAP is a semantic characterization: it identifies when no
coordination is required for safety, not how a process algorithmically
selects an outcome.

This says “no coordination,” but the preceding paragraph explicitly allows same-side coordination. Maybe:

Complete CAP is a semantic characterization of when no cross-partition coordination is required for safety…

That is more accurate.

Also, CAP should inherit the demonic exposure convention explicitly:

As in Complete CALM, outcomes exposed at p are interpreted demonically as permitted interface exposures at p.

That would make the necessity direction clearer.

⸻

The separation theorem is now in good shape

I like the current statement:

relational-transducer CALM has no specification-level judgment:
its verdict is necessarily attached to a chosen program boundary,
not to the output specification of the variant.

This is precise and defensible. The direct/indirect encoding proof is now much better than the earlier version.

One possible small edit:

“Complete CALM certifies Spec' directly.”

Maybe say:

“Complete CALM certifies the residual interface Spec' directly.”

That reinforces the interface/program distinction.

⸻

Proper coordination is clear, but the Obs'=∅ convention is still worth flagging once more

The text now says excluded histories are never reached and that this differs from the main theorem. Good.

I would only add a sentence:

Thus proper coordination changes the admitted history space; it is not an application of ordinary monotonicity to the original unrestricted future relation.

This prevents a reader from thinking you are toggling the meaning of empty Obs.

⸻

Frontier claim is acceptable but still watch the word “characterizes”

The abstract says:

for a fixed observation interface, characterizes the strongest
coordination-free weakenings

This is fine if the appendix is rigorous. If you want to be safer:

provides a way to characterize

But this is lower priority than the operational correctness alignment.

⸻

Bottom line

You have converged conceptually. The paper now has a clear stance:

Obs is a demonic interface contract. Coordination-freedom means every permitted local exposure must remain safe under all futures. Restricting the permitted outcomes is itself coordination/proper variant construction.

That is coherent and strong.

The remaining fix is to make the formal definitions match that stance. Right now the correctness definition is existential over actual traces, while the necessity proof uses universal/demonic exposure over all Obs(H). I would add a formal “demonic correctness” or “interface-contract correctness” definition and state the operational theorem using it.

Once that is done, the core theorem will be much harder to attack.