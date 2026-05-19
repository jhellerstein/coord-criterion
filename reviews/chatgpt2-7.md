I read the latest main.tex carefully. This is a substantial improvement over the previous draft. The biggest change is that the paper now explicitly states response soundness and response preservation, uses E_iface rather than the misleading old “input” terminology, and defines operational coordination-freedom in the enabled-response style. Those changes directly address several serious objections.

Most importantly: I am now convinced that my earlier “joint consistency” objection is not valid against the intended model, provided the response-soundness convention is taken as part of the formal model. The draft now says this explicitly enough that the sufficiency proof is much more plausible.

That said, I still see a few high-risk issues. The two largest are:

1. The necessity direction of the operational Complete CALM theorem still appears stronger than the proof supports.
2. Proper coordination now has a pragmatic “admitted histories” fix, but it is not fully integrated with the main definition of specification/monotonicity.

Below is the detailed review.

⸻

Top-level verdict

The latest draft is now much closer to a credible PODS submission. The formal spine is clearer, and the paper has a better answer to the “this is definitional” critique:

* operational coordination-freedom is now enabled-response based;
* correctness is defined over emitted responses;
* response soundness and preservation are explicit;
* monotonicity now genuinely does work in the sufficiency proof;
* proper coordination is framed as verification of a residual interface;
* Complete CAP is conceptually connected to distributed-monotonicity rather than naïve monotonicity.

But I would still not quite trust the main theorem as stated:

A specification admits a correct coordination-free distributed implementation iff Spec is monotone.

The sufficiency direction is now much better. The necessity direction is still under-specified, because an arbitrary monotonicity failure need not be realizable as the kind of indistinguishable execution pair used in the proof.

So my recommendation is:

Keep the main conceptual claim, but sharpen the theorem statement or add a lemma identifying exactly which monotonicity failures are operationally observable by an invocation/response event.

⸻

1. The joint-consistency issue is largely fixed

This is the biggest improvement.

The paper now states:

Response soundness: if H contains resp(e,v), then every o ∈ Obs(H)
prescribes response v for invocation e.

and:

Response preservation: if o Ord o' and o prescribes response v for e,
then o' also prescribes v for e.

With those assumptions, the joint-consistency remark is basically right.

The earlier worry was:

o_p ∈ Obs(H_p)
o_q ∈ Obs(H_q)
monotonicity gives:
o_p ⪯ o'_p ∈ Obs(H)
o_q ⪯ o'_q ∈ Obs(H)
but maybe no single o* explains both responses.

Your answer is now:

Since H contains both response events, any o' ∈ Obs(H) explains both responses by response soundness.

That works. In fact, one response’s monotone refinement is enough:

o_p ∈ Obs(H_p)
H_p ⊑ H
monotonicity gives o' ∈ Obs(H) with o_p ⪯ o'

Then:

* o' preserves p’s response by response preservation;
* o' explains every other response in H by response soundness.

So no separate response-compositionality assumption is needed for this history-includes-responses model. The paper should maybe state this even more crisply:

Because response events are part of the history, response compositionality is pushed into the admissibility judgment Obs(H): if two responses cannot be jointly explained, then no outcome explaining either response can refine into the full response history.

That is a good idea and a clean theoretical move.

⸻

2. The sufficiency proof is now plausible, but it needs one small cleanup

The sufficiency proof says:

At any prefix with global history H, each local view satisfies H_i \hext H.
By monotonicity, the chosen o ∈ Obs(H_i) has a refinement o' ∈ Obs(H).
Since refinement preserves earlier responses, the emitted response is
consistent with o'.

Given the new response-soundness condition, the last sentence should be strengthened:

Since H contains all response events emitted so far, response soundness
implies that any o' ∈ Obs(H) explains all of Resp(H). Since o ⪯ o',
response preservation ensures that o' also preserves the response
chosen at H_i.

That makes the proof directly match the joint-consistency remark.

Also, the phrase:

No input action intervenes.

is slightly misleading under the enabled-response definition. The protocol guarantees that a response is locally enabled without requiring further input; an adversarial execution might still schedule another input first. I would replace it with:

The response is enabled without requiring any further input action.

This avoids sliding back into the older scheduler-sensitive formulation.

⸻

3. The necessity direction still looks too broad

This is now the main theorem-level concern.

The proof says:

Let o ∈ Obs(H_1) be future-inconsistent, witnessed by H_1 \hext H_2,
with o prescribing response v to invocation e at process p.

But monotonicity failure gives only:

o ∈ Obs(H_1)
H_1 \hext H_2
no o' ∈ Obs(H_2) with o \Ord o'

It does not automatically give:

1. that o prescribes a response to some invocation;
2. that the invocation is at a particular process p;
3. that the response must be emitted from a local state indistinguishable between two executions;
4. that the additional events in H_2 \setminus H_1 can occur without input actions at p before the response.

The proof tries to handle this with:

the additional events in H_2 \setminus H_1 occur without input actions
at p—either at other processes, or as consequences of prior events at p
that have already been processed

But that is an extra condition on the witness, not a consequence of non-monotonicity as defined.

There are monotonicity failures whose dangerous future contains new local input at p. Under your operational definition, the response must be enabled immediately after the invocation, so perhaps local future inputs should indeed count. But the indistinguishability proof needs to be phrased differently for those cases: the future local input can occur after the response, not before it. If the dangerous future requires new input at p before the response, the proof as written does not apply.

I think the theorem needs one of these fixes.

Option A: Add a “response-exposable monotonicity” lemma

State a lemma before the theorem:

For response-total, response-sound specifications, any monotonicity
failure relevant to operational correctness can be witnessed by an
outcome prescribing a response to a pending invocation, and by a future
that can be scheduled after that response without changing the
pre-response local state.

Then prove it. If you can’t prove that lemma, the theorem should be narrowed.

Option B: Narrow the theorem to “exposable monotonicity”

Define:

A specification is exposure-monotone if every outcome that prescribes
a response to an invocation remains refineable in every admissible
future that can occur after that response is locally enabled.

Then the operational theorem becomes exact. Ordinary monotonicity can remain the simpler, stronger semantic condition used in applications.

Option C: Make the necessity proof explicitly case-split

For a monotonicity failure H1 ⊑ H2:

* if the dangerous added events are remote/silent to p, use indistinguishability;
* if they are local but occur after the response, schedule the response first and then add the local future;
* if they must occur before the response, explain why such a witness is not relevant to a response prescribed at H1, or adjust the history chosen for the witness.

Right now the proof gestures at this but does not establish it.

This is the most important thing I would fix before submission.

⸻

4. E_iface is a big improvement, but A(H_iface) still feels awkward

Renaming E_in to E_iface is good. The text now correctly says interface events include invocations and responses, while I/O automaton inputs are only invocations and receives.

However, the admissible-history definition still uses an interface prefix:

A(H_iface) = {H ∈ Hist | H_iface \hext In(H)}

where In(H) is really the interface projection.

This is semantically okay, but there is still a conceptual wrinkle: if H_iface includes responses, then it includes implementation output choices. So A(H_iface) is not the set of histories possible under a given environment input schedule; it is the set of histories extending a given client-observed trace.

That is fine if intentional, but the surrounding prose says:

They represent the environment's nondeterminism ... rather than implementation choices.

That is not quite right once responses are in the prefix. Responses are implementation choices, even though they are client-interface events.

I would revise the prose:

These are the causally coherent histories compatible with a given client-visible interface prefix. The prefix may include both invocations supplied by the environment and responses emitted by the implementation; admissibility describes causal possibility, not who chose the event.

This small wording change would avoid the lingering input/output confusion.

⸻

5. Response totality should be promoted from a parenthetical to an assumption

The proof currently says:

We assume response totality...

inside the sufficiency proof.

This is important enough to put near response soundness/preservation in the specification section. The operational theorem should state:

For response-sound, response-preserving, response-total specifications...

or the paper should say all specifications considered are response-total.

As written, the theorem statement omits response totality:

A specification Spec admits ... iff Spec is monotone.

But monotonicity alone does not imply response totality. A spec with Obs(H)=∅ at every invocation history is monotone but has no available implementation.

You partially handle this by allowing error/abort, but that must be formal:

* either error/abort is an admissible response prescribed by some outcome, or
* the implementation is not correct for histories where Obs(H)=∅.

I would add a “well-formed response specification” definition:

A response specification is well formed if it satisfies response
soundness, response preservation, and response totality.

Then state the operational theorem for well-formed response specifications. This is a harmless narrowing and makes the theorem robust.

⸻

6. Proper coordination is improved but still semantically nonstandard

The new definition says a properly coordinated variant is monotone only over histories where Obs' is nonempty:

for all H_1 \hext H_2 with Obs'(H_1) ≠ ∅ and Obs'(H_2) ≠ ∅

This is a pragmatic way to model admitted histories without adding an explicit admissible-history set. It fixes the earlier problem where excluded futures made monotonicity fail immediately.

But it also means that “monotone” for coordinated variants is not the same monotone as Definition 8 / Complete CALM. It is monotonicity over an induced admitted-history subspace.

That is okay, but the paper should be more explicit:

In this section, Obs'(H)=∅ is used not merely to indicate a safety violation but to mark histories outside the residual interface. Monotonicity is therefore checked relative to the subspace of admitted histories.

This convention differs from the main Complete CALM theorem, where a future with Obs(H')=∅ is exactly a monotonicity failure. Here, a future with Obs'(H')=∅ is ignored because the coordination mechanism is assumed to exclude it.

That is a reasonable modeling move for proper coordination, but I would not hide it.

The cleanest fix remains to define specifications as:

Spec = (A, Obs, Ord)

where A is the admitted history space, and monotonicity quantifies over H1,H2 ∈ A. But if you do not want to restructure the paper, the current induced-admitted-history convention can work if clearly flagged.

⸻

7. The separation theorem is still overclaimed

The “Separation from relational-transducer CALM” theorem is rhetorically useful, but I would soften it.

The theorem says:

There exist non-monotone specifications with properly coordinated
variants that Complete CALM can verify but relational-transducer CALM
has no mechanism to certify...

The proof sketch argues:

* linearizability is non-monotone;
* restrict to histories where interface operations are totally ordered;
* the residual prefix interface is monotone;
* relational CALM cannot certify this because Datalog encodings of linearizability need non-monotone uniqueness constraints.

The underlying point is good, but as a formal theorem it is vulnerable. “Relational-transducer CALM has no mechanism” is a claim about the scope of a framework, not a formally defined impossibility result.

I would rename this:

Observation / Example / Proposition

and phrase it as:

This illustrates a separation in what the frameworks analyze: relational CALM classifies programs, while Complete CALM can classify residual output interfaces produced by coordinated components.

That is strong, true, and less likely to trigger a reviewer demanding a formal separation proof.

⸻

8. Complete CAP is conceptually strong but still too theorem-heavy

I like the distributed-monotonicity section. The key distinction is valuable:

Full monotonicity captures no coordination at all; distributed-monotonicity captures no communication-dependent coordination under partitions.

That is a nice conceptual contribution.

But the theorem:

a specification admits a consistent, available, partition-tolerant implementation
iff it is distributed-monotone

still needs more scaffolding if it is going to remain an iff theorem.

Issues:

* “exposed at p” is still informal: “if o determines a response to an invocation event at p.”
* availability is not formally defined in the main body.
* the sufficiency proof invokes the causal-view protocol, but distributed-monotonicity is weaker than full monotonicity; the protocol’s correctness under non-partition futures is not addressed.
* the theorem says “partition-tolerant implementation,” but the proof only reasons about a fixed partition-constrained future.
* process-local non-monotonicity can be resolved by local mechanisms, but the implementation model for that is not given.

I would either:

1. move the full formal burden to the appendix and make the main statement a corollary under the same well-formedness assumptions as Complete CALM; or
2. soften the main theorem to an obstruction/characterization principle.

A safer main-text theorem:

If distributed-monotonicity fails, then no implementation can be both
available under the corresponding partition and correct for the exposed
outcome. Conversely, for response-total specifications whose only
non-monotonicity is process-local and locally resolved, distributed-
monotonicity suffices for partition availability.

That is less punchy, but more defensible. If you keep “Complete CAP,” I would make the availability definition and exposure relation fully formal in the main section.

⸻

9. The intro overstates the theorem relative to the proof

The intro says:

a specification admits a correct coordination-free implementation—one
in which every process responds to every invocation without waiting for
any remote information—iff it is monotone.

But the operational definition is stronger than “without waiting for remote information”: it says without requiring any further input action at that process, including local invocations/messages.

Later you use this distinction to explain process-local non-monotonicity and CAP. I would revise the intro to avoid a mismatch:

one in which every process can respond to an invocation using only its post-invocation local state and local computation, without requiring any further input action.

Then distinguish:

A weaker distributed notion, where local coordination is allowed but remote coordination is unavailable under partitions, yields Complete CAP and distributed-monotonicity.

That makes the CALM/CAP relationship cleaner.

⸻

10. The abstract and contribution list still overclaim the frontier

The abstract says the frontier construction:

derives natural coordination-free weakenings for any specification

and the contribution says:

minimal monotone enlargements ... characterize the strongest
coordination-free guarantees

I still think this is too strong relative to the appendix. The frontier examples are interesting, but many involve changing the interface, not merely enlarging the order. The paper does acknowledge this, but the abstract/contributions sound more definitive than the formal development supports.

Suggested softer wording:

a frontier methodology for exploring strongest monotone weakenings of a fixed observation interface, illustrated on registers, queues, and search structures.

That still sounds good and avoids overpromising.

⸻

11. Some smaller technical/prose points

CRDT proof

The proof says:

every state reachable at H' is at least as large as some state reachable at H

The needed statement is:

for every o ∈ Obs(H), there exists o' ∈ Obs(H') with o ≤ o'

You then say “in particular,” but I would rewrite directly from the chosen o. It is cleaner and avoids a quantifier mismatch.

HAT proposition

“HAT levels are monotone” is a broad statement. Read committed is fine. Session guarantees need careful outcome modeling because the relevant order is per-session and includes client history constraints. If you keep the broad proposition, make sure the appendix really proves those cases.

Snapshot isolation aside

You still say SI requires coordination but omit the witness. I would either include a one-sentence witness or remove the parenthetical. Reviewers will notice unsupported claims about SI.

Stratified Datalog example

This still relies on the proper-coordination convention that Obs'=∅ marks histories outside the admitted residual interface. That is fine, but it should be described as changing the admitted history space, not merely as monotonicity of the original spec.

⸻

Suggested minimal edits before submission

If you do not want to restructure deeply, I would make these targeted edits.

1. Define “well-formed response specification”

After response soundness/preservation:

We call a specification response-well-formed if it satisfies response
soundness, response preservation, and response totality: whenever a
reachable history contains an invocation requiring a response, some
outcome in Obs(H) prescribes an allowed response.

Then change the operational theorem:

A response-well-formed specification admits a correct coordination-free
distributed implementation iff it is monotone.

This avoids the empty-Obs objection.

2. Strengthen the sufficiency proof conclusion

Replace the current correctness paragraph with:

At any execution prefix with global history H, choose any response
emitted by the protocol, and let o be the outcome chosen at the local
view H_i that produced it. Since H_i \hext H, monotonicity gives
o' ∈ Obs(H) with o \Ord o'. By response soundness, o' explains every
response event recorded in H; by response preservation, it preserves
the response emitted from o. Hence Resp(H) is explained by o', so the
prefix is correct.

This directly encodes the repaired joint-consistency argument.

3. Fix the necessity proof’s witness condition

Add either a lemma or a caveat:

The contrapositive uses a monotonicity witness whose unsafe outcome is
exposable by a response and whose invalidating future can be scheduled
without changing the responder's pre-response state. For the
response-well-formed specifications considered here, every violation
of monotonicity has such a witness...

Then prove that last sentence, or weaken the theorem to exposable monotonicity.

This is the one edit that may require real thought.

4. Clarify admitted histories in proper coordination

Add:

For coordinated variants, Obs'(H)=∅ is used to mark histories outside
the residual interface. Thus condition (ii) checks monotonicity relative
to the admitted subspace {H | Obs'(H) ≠ ∅}, not monotonicity over all
well-formed futures. Operationally, the coordination mechanism is
responsible for ensuring excluded histories are unreachable.

This makes the changed convention explicit.

5. Downgrade “Separation theorem”

Call it an observation/proposition unless you formalize relational-transducer non-certifiability.

⸻

Final assessment

This is the best draft so far. The latest version has genuinely repaired the previous joint-consistency concern by making histories include responses and requiring response soundness. That is a strong move and should stay.

The remaining danger is not the sufficiency proof anymore; it is the scope of the necessity theorem. The current proof still assumes more about the non-monotonicity witness than the definition of monotonicity provides. If you can close that gap—or narrow the theorem to response-exposable/prescription-relevant monotonicity—the paper becomes much more robust.

My current confidence levels:

* Core idea: high.
* Sufficiency direction: mostly convincing after a small proof rewrite.
* Necessity direction: still needs tightening.
* Proper coordination: conceptually strong, formally acceptable if you explicitly define admitted-history monotonicity.
* Complete CAP: promising but still overclaimed unless formalized more.
* PODS viability: plausible, but reviewers will likely attack theorem scope and overclaiming unless those are tightened.