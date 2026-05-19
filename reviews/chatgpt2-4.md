I read the new main.tex. My reaction is mixed but clear:

The paper’s conceptual arc is stronger, but the formal spine is still not where the introduction claims it is. In particular, the revision still does not appear to have incorporated the key fixes around response compositionality, explicit exposure, admissible history spaces, and the operational/semantic theorem split. The text now talks more confidently about the I/O-automaton grounding, but the proof of the central theorem remains essentially the same shape as before, and the same technical gaps remain.

The most important issue is still this:

The paper proves, at best, that each locally chosen response can be individually justified by some future outcome. It does not prove that all independently emitted responses are jointly explainable by one outcome.

That is the gap I would expect a careful PODS reviewer to attack.

⸻

1. The main theorem is still too strong

The central theorem remains:

A specification admits a correct coordination-free distributed implementation iff it is monotone.

But the proof still relies on the causal-view protocol:

On inv(e)_i, the process adds e to H_i, computes Obs(H_i),
chooses o ∈ Obs(H_i), and immediately responds with v prescribed by o.

Then correctness says:

At any prefix with global history H, each local view satisfies H_i ⊑ H.
By monotonicity, the chosen o ∈ Obs(H_i) has a refinement o' ∈ Obs(H).
Since refinement preserves earlier responses, the emitted response is
consistent with o'.

This is individual-response correctness, not global correctness.

If process p chooses outcome o_p and process q concurrently chooses outcome o_q, monotonicity gives:

o_p refines to some o_p' ∈ Obs(H)
o_q refines to some o_q' ∈ Obs(H)

But correctness requires:

there exists one o* ∈ Obs(H) explaining both responses.

Nothing in the current theorem gives this. You still need a condition like:

Finite response compatibility:
If a finite set of responses are each individually explainable at histories
that embed into H, then they are jointly explainable by some o ∈ Obs(H).

or:

Response-compositionality:
If r_1, ..., r_k are response facts emitted in H and each is compatible
with Obs(H), then there exists o ∈ Obs(H) that prescribes all of them.

Without this, the sufficiency proof does not go through.

This is not pedantry. It is exactly the distributed coordination problem: independently safe local choices may be globally incompatible.

⸻

2. The operational model still conflicts with the history model

The I/O automaton section says:

Input actions: client invocations and message arrivals.
Output actions: client responses and message sends.

But the history model still defines:

E_in = external inputs

and examples still put responses in E_in:

inv(w_p), resp(w_p) ∈ E_in
inv(r_p), resp(r_p, 2) ∈ E_in

This remains a serious inconsistency. In the I/O automaton model, responses are not input events. They are implementation outputs.

This also contaminates the definition:

In(H) = H restricted to E_in

If E_in includes responses, then the “input projection” includes values chosen by the implementation. Then admissible histories are not really environment-input histories; they already include output choices.

I would fix this decisively. Use something like:

E_inv    client invocation events
E_resp   client response events
E_send   message send events
E_recv   message receive events
E_int    internal computation events

Then:

Input(H)     = H restricted to E_inv ∪ E_recv
Output(H)    = H restricted to E_resp ∪ E_send
Interface(H) = H restricted to E_inv ∪ E_resp

The implementation is constrained by Input(H), but correctness is judged over Interface(H) or Resp(H).

Right now the paper says the right thing operationally, but the formal history definitions still encode the older mixed model.

⸻

3. “Coordination-free operational” regressed to the scheduler-sensitive version

The current operational definition says:

for every client invocation inv(e)_i, the corresponding response occurs
with no intervening input action at p_i

This is the earlier too-strong scheduler-sensitive definition. Under ordinary I/O automata, input actions are always enabled and controlled by the environment. The scheduler can always deliver another local client invocation or message before the automaton is scheduled to output the response.

The prose then says:

“if the network goes silent and no other client requests arrive after the invocation, the process can still respond.”

That is weaker and more reasonable. But the formal definition says the response actually occurs with no intervening input action in every execution, which is stronger.

I think the right definition is enabled/local-fragment based:

After inv(e)_i, there exists a local execution fragment from p_i's
post-invocation state, using only internal and output actions at p_i,
that emits resp(e,v)_i.

or fairness-based:

If no further input occurs at p_i and local actions are fairly scheduled,
then p_i eventually emits resp(e,v)_i.

As written, the definition can be falsified by an adversarial environment that immediately delivers another input before scheduling the response.

⸻

4. Correctness still lacks a formal exposure relation

Correctness is currently:

the emitted responses are consistent with some o ∈ Obs(H)

But “consistent with” is not formalized.

You need a first-class relation, for example:

Prescribes(o, e, v)

or:

Expose(o) ⊆ E_resp

Then define:

Resp(H) = set of response facts emitted in H

and correctness as:

∃o ∈ Obs(H). Resp(H) ⊆ Expose(o)

or whatever the intended relation is.

This would also let you define “outcome exposed at process p” cleanly. Right now distributed-monotonicity says:

An outcome is exposed at p if p is the process that would communicate it
to a client---formally, if o determines a response to an invocation event at p.

But “determines a response” is doing all the work. Make it formal.

Without this relation, the necessity proof is also too broad: non-monotonicity of some semantic outcome matters operationally only if that outcome can be exposed by some response.

⸻

5. Necessity still proves only a local/silent-future result, not full monotonicity

The necessity proof says:

Let o ∈ Obs(H_1) be future-inconsistent, witnessed by H_1 ⊑ H_2,
with o prescribing response v to invocation e at process p.

But non-monotonicity alone does not imply:

1. o prescribes a response;
2. the response is at a particular process p;
3. H_2 can be realized without changing p’s local state before response;
4. the distinguishing future is invisible to p.

The proof then constructs executions where other processes advance to produce H_2 while messages to p are delayed. That only works for p-silent or remote-only futures.

So the theorem should be about one of the following:

Option A: Strong immediate local coordination-freedom

Then non-monotonicity under any future matters, including local futures. But the model must say the process may not wait for even local inputs/concurrency, and every future-inconsistent outcome must be locally exposable.

Option B: Distributed availability / CAP-style freedom

Then the condition is not full monotonicity. It is distributed-monotonicity or p-silent monotonicity.

Right now the paper wants both. It says Complete CALM is full monotonicity, but its operational proof uses an indistinguishability argument that only works for invisible futures.

This is fixable, but the theorem statement must match the proof.

⸻

6. Obs(H)=∅ remains problematic for availability

The paper says:

Obs(H) = ∅ signals that H is unrealizable.

Then the sufficiency protocol says each process computes Obs(H_i), chooses o ∈ Obs(H_i), and responds.

But a monotone specification may have empty observations at reachable histories. Monotonicity does not imply nonemptiness. If Obs(H_i)=∅, the protocol cannot choose an outcome.

You need a separate response-totality condition:

For every reachable local view containing an invocation requiring a response,
there exists o ∈ Obs(H) prescribing an allowed response.

Or make abort/error an explicit response outcome.

This matters especially for I-confluence and invariant examples, where Obs(H)=∅ is used to mark invariant violation. An available implementation cannot simply have no outcome unless it can return abort or error.

⸻

7. Proper coordination is still not formal enough

The paper still defines a properly coordinated variant as:

Spec' = (E, Obs', Ord)
Obs'(H) ⊆ Obs(H)
Spec' is monotone

But then the prose says proper coordination can involve:

fewer admissible outcomes, fewer admissible histories, or both.

The definition still only supports fewer outcomes. It does not support fewer histories or restricted futures.

This matters for examples like:

* total-order broadcast,
* locking,
* barriers,
* Paxos logs,
* stratified Datalog,
* future restriction in Table 1.

For future restriction, the spec must include an admissible history space or admissible future relation. I would change the base spec to:

Spec = (A, Obs, Ord)

where A ⊆ Hist is the admissible history/future structure, or:

Spec = (Hist, ⊑_Spec, Obs, Ord)

Then a coordinated variant can be:

A' ⊆ A
Obs'(H) ⊆ Obs(H)
Ord' maybe inherited or transformed

Without this, the “future restriction” side of the theory is still informal.

⸻

8. Complete CAP is still overclaimed

The distributed-monotonicity idea is good. The paper’s distinction is valuable:

Full monotonicity captures coordination-freedom under all futures; distributed-monotonicity captures availability under remote-only/partition futures.

That should be a major contribution.

But the theorem still says:

a specification admits a consistent, available, partition-tolerant implementation
iff it is distributed-monotone

The proof still has the same issues:

* “exposed at p” is informal;
* availability is existential rather than universal;
* sufficiency again assumes arbitrary local outcomes compose globally;
* correctness still lacks a formal response/outcome exposure relation;
* the proof is a sketch, not a full I/O-automaton construction.

The appendix’s “maximal availability” definition says:

if some partition extension completes an invocation and admits nonempty Obs,
there exists an execution of I in which e completes.

That is much weaker than standard availability. It is existential over executions, not “every request to a nonfailed node eventually receives a response under fair scheduling.” You say stronger versions only strengthen impossibility, but the iff also needs sufficiency under the chosen definition.

I would rename this section away from “Complete CAP” unless you strengthen it. A safer framing:

Distributed-monotonicity gives the semantic CAP obstruction: if an exposed outcome can be invalidated by a partition-constrained future, then availability and correctness conflict.

Then present the iff only under explicit well-formed response-compositional assumptions.

⸻

9. The frontier section is still too ambitious

The abstract says:

a coordination-free frontier construction that derives natural coordination-free weakenings for any specification

That is too strong relative to the appendix.

The frontier formalism is:

minimal monotone enlargements of Ord

But the examples often change more than Ord:

* causal consistency changes from single global total-order outcomes to per-process/causal views;
* the universal construction creates a new residual interface;
* search structure examples change what is being observed;
* proper coordination restricts histories/futures.

So the frontier is not merely “minimal monotone enlargement of the order.” It is a broader design pattern over interface transformations. That is interesting, but not yet formalized.

Also, the maximality proofs are still hand-wavy. For example, the register proof says one can choose H_2 such that o_2 is the only causally consistent extension. That is doing too much work and is not generally obvious.

I would weaken the contribution claim:

We propose a frontier methodology for exploring coordination-free weakenings, illustrated by registers, queues, and search structures.

Avoid saying it “derives” them for any specification unless you formalize interface morphisms.

⸻

10. Some application claims are still too breezy

A few examples:

HAT levels

The read-committed proof is plausible, but “HAT levels are monotone” is broad. Session guarantees and monotonic reads need careful treatment because the outcome order and session histories matter.

Snapshot isolation

You say SI requires coordination but omit the witness. At this stage, either include the witness or remove the parenthetical. Reviewers will notice.

I-confluence

The instantiation says:

conv(H) = the state the system will inevitably reach once gossip completes

But your model earlier imposes no fairness or delivery guarantee. Better:

conv(H) is the join/merge closure of the states represented in H

Do not use “inevitably” unless eventual delivery is part of the model.

CRDT proof

This sentence remains suspicious:

every state reachable at H' is at least as large as some state reachable at H

What you need is:

for every o ∈ Obs(H), there exists o' ∈ Obs(H') with o ≤ o'

The current sentence is weaker/different. Easy fix: start from chosen o, apply the additional updates/merges in H' \ H, obtain o'.

⸻

The biggest structural recommendation

I would split the paper’s core into three explicitly different levels:

Level 1: Semantic Complete CALM

This is the clean definitional result:

Spec is monotone iff every admissible outcome is future-consistent.

Be honest that this is immediate but conceptually clarifying.

Level 2: Operational Complete CALM for well-formed response specs

State a theorem with explicit assumptions:

For response-total, response-compositional specifications with
response-preserving refinement and explicit exposure relation,
monotonicity is equivalent to existence of a correct locally-immediate
implementation.

This is the theorem you can actually prove.

Level 3: Distributed/CAP variant

Then state:

For the same class of response specs, distributed-monotonicity is the
partition-availability analogue: exposed responses survive all
partition-constrained invisible futures.

This would make the paper much more defensible.

⸻

Suggested revised core definitions

I would add something like this.

A response specification is a tuple
Spec = (A, Obs, Ord, Expose)
where A is a prefix-closed set of admissible histories,
Obs(H) is a set of outcomes,
Ord is refinement, and
Expose(o) is the set of response facts entailed by outcome o.

Then:

Correctness:
An execution prefix with history H is correct iff
there exists o ∈ Obs(H) such that Resp(H) ⊆ Expose(o).

Response preservation:

If o Ord o', then Expose(o) ⊆ Expose(o').

Response totality:

Every invocation that must receive a response has at least one
admissible response fact entailed by some o ∈ Obs(H).

Response compositionality:

If r_1, ..., r_k are response facts emitted at compatible local views
and each is explainable at H, then there exists o ∈ Obs(H)
such that {r_1, ..., r_k} ⊆ Expose(o).

Then the sufficiency proof has something to stand on.

⸻

What is genuinely strong now

Even with the issues, the paper’s intellectual contribution is still strong.

The strongest parts are:

1. The semantic abstraction: histories → outcome sets under refinement.
2. The running register example: linearizability vs causal consistency is compelling.
3. The distinction between monotonicity and distributed-monotonicity: very valuable.
4. Proper coordination / residual interfaces: likely the most distinctive payoff.
5. CALM subsumption: this remains one of the cleanest formal sections.
6. The architectural framing: coordination layers discharge non-monotonicity and expose monotone residual streams.

The paper should lean into those, but with theorem claims narrowed to match the formal support.

⸻

My overall verdict

This draft reads more polished and more confident, but I do not think the deeper formal concerns are resolved yet. In fact, the I/O-automaton theorem is still the most vulnerable part of the paper.

The core claim still needs one of two moves:

1. Narrow the theorem to a well-formed class of response-compositional specifications; or
2. Strengthen the formalism so arbitrary outcomes, arbitrary local choices, and arbitrary concurrent responses compose into a single globally valid outcome.

I strongly recommend the first route. It will make the result less grandiose but much more credible.

A safer headline theorem would be:

For response-total, response-compositional specifications with response-preserving refinement, operational coordination-freedom coincides with monotonicity of exposable outcomes.

That theorem would still be broad, still subsume CALM/CRDT/I-confluence/HAT-style cases, and would be far less attackable.