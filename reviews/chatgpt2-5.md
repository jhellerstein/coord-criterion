I read this main.tex fresh. This is definitely not identical in spirit to the stale version: it now has an enabled-response operational definition, a fairness assumption, a correctness definition over emitted responses, and an explicit “joint consistency” remark. Those are all improvements.

But my main reaction is:

This version has moved the right objections into the text, but it has not yet solved them. In a few places it now asserts away exactly the gap a reviewer will press on.

The paper is getting closer, but the formal center still needs surgery.

⸻

The biggest issue: the joint-consistency remark is not correct

The new Remark [Joint consistency of independent responses] is clearly aimed at the previous critique. Unfortunately I do not think the argument works.

It says, roughly:

If two concurrent responses are jointly inconsistent, then the global history containing both responses has Obs(H)=∅. But then the earlier outcome at H_p has no refinement at H, so monotonicity fails. Therefore monotonicity guarantees joint consistency.

The problem is the first step. Joint inconsistency of two emitted responses does not necessarily mean Obs(H)=∅. It means:

no outcome in Obs(H) explains both emitted responses.

But there may still be outcomes in Obs(H) explaining different responses, or explaining one but not the other. So the issue is not emptiness of Obs(H), but lack of a common explaining refinement.

More formally, the protocol chooses:

o_p ∈ Obs(H_p)
o_q ∈ Obs(H_q)

Monotonicity gives:

∃o'_p ∈ Obs(H). o_p ⪯ o'_p
∃o'_q ∈ Obs(H). o_q ⪯ o'_q

But correctness needs:

∃o* ∈ Obs(H). o_p ⪯ o* and o_q ⪯ o*

or at least one o* explaining both response facts. Pointwise refinement does not imply common refinement.

This is the core mathematical gap. The new remark tries to close it, but it only closes the special case where conflicting responses make Obs(H) empty. Many specs can have nonempty Obs(H) while two independently chosen outcomes are mutually incompatible.

A simple abstract counter-shape:

Obs(H_p) = {a}
Obs(H_q) = {b}
Obs(H)   = {a', b'}
a ⪯ a'
b ⪯ b'

with no outcome refining both a and b. This is monotone in the pointwise sense but does not support independent local choice of a and b.

You need one of these:

1. Response-compositionality / finite compatibility as an explicit assumption.
2. A stronger monotonicity criterion requiring common refinements for compatible concurrent local observations.
3. A restricted outcome model where outcomes are response-fact sets ordered by inclusion and Obs(H) is closed under unions of independently emitted facts.
4. A canonical selection function whose choices are guaranteed to compose.

Without one of those, the sufficiency proof of the operational theorem is still not valid.

⸻

The operational theorem still proves less than it states

The theorem states:

A specification Spec admits a correct coordination-free distributed
implementation iff Spec is monotone.

But the necessity proof still contains the caveat:

The proof requires that H_2 be realizable as a p-silent future...
This holds whenever the non-monotonicity witness involves activity
at processes other than p...
For purely process-local non-monotonicity ... such non-monotonicity
does not prevent coordination-free implementation.

That caveat contradicts the theorem as stated.

Full monotonicity quantifies over all futures. The operational indistinguishability proof only applies to futures invisible to the responding process. So the theorem is not “iff monotone” unless your operational definition disallows even local waiting/serialization and every monotonicity failure is tied to an exposable response before the dangerous future.

You have two coherent choices:

Option A: Strong local-immediacy theorem

Say explicitly:

This theorem is about a very strong notion of coordination-freedom: after an invocation, the process must be able to respond before any further input, including local input. Therefore process-local non-monotonicity also violates this strong property.

Then remove or rephrase the caveat saying process-local non-monotonicity does not prevent coordination-free implementation.

Option B: Distributed-availability theorem

Say:

The operational theorem characterizes distributed coordination-freedom, so the relevant property is not global monotonicity but p-silent/distributed monotonicity.

Then the theorem should not be “iff monotone”; it should be “iff local-exposure/distributed monotone.”

Right now the paper tries to use full monotonicity for Complete CALM and distributed-monotonicity for CAP, but the operational proof for Complete CALM already relies on the distributed/silent-future distinction.

⸻

Histories still conflate interface events with automaton inputs

The event universe still defines:

E_in (client interface: invocations and responses)

and then defines:

In(H) = H restricted to E_in

But in the I/O automaton section, invocations are input actions and responses are output actions. The paper acknowledges this in prose:

“the history records both as interface events regardless of which party initiates them.”

That is fine, but then E_in should not be called input, and In(H) should not be the input projection. It is the interface projection.

This matters because admissible histories are defined as:

A(H_in) = { H | H_in ⊑ In(H) }

If H_in includes responses, then the environment-controlled input prefix already includes implementation output choices. That breaks the operational interpretation.

I would change the event taxonomy to:

E_inv    client invocations
E_resp   client responses
E_int    internal computation
E_send   message sends
E_recv   message receives

Then define:

Input(H)     = H restricted to E_inv ∪ E_recv
Output(H)    = H restricted to E_resp ∪ E_send
Interface(H) = H restricted to E_inv ∪ E_resp

This would cleanly separate:

* what the adversary supplies,
* what the implementation emits,
* and what the client observes.

Right now the terminology is doing damage. A reviewer will notice.

⸻

The semantic definition of coordination-free remains partly tautological

You still define semantic coordination-free implementation as:

(i) R_I(H_in) = A(H_in)
(ii) every o ∈ Obs(H) is future-consistent

Condition (ii) is purely a property of the specification, not of the implementation. You acknowledge this:

“Condition (ii) is deliberately specification-level…”

That helps, but then the phrase “implementation is coordination-free” is still misleading. It would be cleaner to split:

A specification is semantically coordination-free iff every admissible
outcome is future-consistent.

and:

An implementation is operationally coordination-free iff responses are
enabled locally without further input.

Then state a bridge theorem under assumptions. Right now the paper moves between these notions too quickly.

⸻

The Obs(H_i)=∅ issue is still not fixed

The sufficiency proof says:

If Obs(H_i) = ∅ ... this case does not arise for monotone specifications
at reachable histories, since monotonicity propagates nonemptiness forward.

This is false as stated. Monotonicity preserves nonemptiness from a nonempty prefix. It does not create nonemptiness from nothing. A monotone spec can have empty observations at all histories, or at some reachable invocation histories, and still be monotone.

You need a separate condition:

Response-totality:
At every reachable local view where a response is required, there is
at least one admissible outcome prescribing an allowed response.

Or make abort/error an explicit admissible outcome and prove it is always present.

This is not a corner case. You use Obs(H)=∅ to model invariant violations and excluded histories. An available implementation needs a response story for those cases.

⸻

Proper coordination still cannot correctly express future restriction

This version still says:

A properly coordinated variant Spec' = (E, Obs', Ord) satisfies
Obs'(H) ⊆ Obs(H)

and then:

“History restriction is modeled by setting Obs’(H)=∅ for excluded histories: monotonicity is then vacuous at those histories.”

This is not right.

Monotonicity is vacuous from excluded histories, but not into excluded histories. If H1 is included with nonempty Obs'(H1) and H2 is a future that the coordinated system excludes by setting Obs'(H2)=∅, then monotonicity from H1 to H2 fails.

So setting Obs'(H)=∅ does not model future restriction unless the future relation itself is also restricted.

This directly affects:

* total-order broadcast;
* locks;
* barriers;
* leader election;
* stratified Datalog sealing;
* the proper coordination table;
* the separation theorem.

You need the spec to include admissible histories or an admissible future relation:

Spec = (A, Obs, Ord)

where A is a prefix-closed admissible history space, and monotonicity quantifies only over H1 ⊑ H2 within A.

Then a coordinated variant can restrict A:

A' ⊆ A
Obs'(H) ⊆ Obs(H)

Without this, “future restriction” is not formal.

This is, in my view, the second biggest remaining formal issue after joint consistency.

⸻

The separation theorem is still too strong

The theorem claims:

There exist non-monotone specifications with properly coordinated variants that Complete CALM can verify but relational-transducer CALM has no mechanism to certify.

The intuition is good, but the theorem as written is vulnerable.

First, the proposed variant “restricting to histories in which → totally orders E_in” is a history/future restriction, but the formal definition of coordinated variant only restricts Obs.

Second, the claim about relational-transducer CALM having “no mechanism” is a meta-claim about a framework, not a formal separation theorem unless you define the class of encodings and what it means to certify the output specification.

I would downgrade this to an “Observation” or “Example” unless you want to formalize the separation.

A safer version:

Complete CALM can analyze the monotonicity of the residual interface exposed by a coordinated component, whereas relational CALM classically analyzes the monotonicity of the program that produces that interface.

That is persuasive and less attackable.

⸻

Complete CAP is conceptually good, but the theorem is not yet solid

The distributed-monotonicity idea is one of the best parts of the paper. The distinction between process-local and partition-spanning non-monotonicity is valuable.

But the theorem:

a specification admits a consistent, available, partition-tolerant
implementation iff it is distributed-monotone

has the same unresolved problems:

* “exposed at p” is still informal;
* availability is not fully formalized in the main theorem;
* sufficiency again assumes arbitrary local outcomes compose globally;
* correctness depends on an implicit “explains responses” relation;
* p-silent indistinguishability is gestured at but not fully formalized;
* the theorem should probably inherit response-totality and response-compositionality assumptions.

I would present Complete CAP as a semantic obstruction theorem unless you fully formalize the operational model. For example:

If distributed-monotonicity fails, then any implementation must either withhold a locally exposable outcome during the partition or risk inconsistency.

That direction is powerful and easier to defend. The iff needs much more scaffolding.

⸻

The register example is strong, but watch “input” terminology

The replicated-register example remains a good running example. The linearizability-vs-causal-consistency separation is intuitive and useful.

But since E_in contains responses, statements like “totally orders input operations” or “restricting E_in” are confusing. A response is not an operation input. This will become much clearer once you split invocations and responses.

Also, your linearizability model is still Lamport-history linearizability: the order must respect message-induced happens-before, not just real-time operation precedence. That is okay, but the paper should keep reminding the reader that this is the history-based linearizability appropriate to your model.

⸻

The operational definition is much better now

The enabled-response formulation is exactly the right fix:

there exists an execution fragment from p_i's post-invocation state
consisting only of internal and output actions at p_i that produces resp(e,v)_i

This avoids the scheduler-preemption problem. Good.

But the proof text still says:

No input action intervenes.

That phrase sounds like the older scheduler-sensitive definition. Better:

The response is enabled without requiring further input.

That is the property you actually want.

⸻

“Every outcome must be future-consistent” is still too strong operationally

The semantic definition requires every outcome in Obs(H) to be future-consistent. The operational protocol chooses an arbitrary o ∈ Obs(H_i). This motivates the universal quantifier.

But real implementations rarely expose arbitrary admissible outcomes. They expose outcomes chosen by a policy. If some admissible outcome is unsafe but the implementation never chooses it, the spec as written is non-monotone, but the implementation might still be coordination-free with a restricted exposure policy.

You partly handle this through “coordinated variants,” but that requires modeling the implementation’s exposure policy as Obs'. That is okay, but then your central theorem is about interfaces that allow arbitrary exposure, not all possible implementations of the original spec.

I would make this explicit:

We treat Obs(H) as the interface contract: any outcome in Obs(H) may be exposed. If an implementation commits to exposing only a subset, that is a different, restricted interface Obs'.

This framing is defensible, but needs to be stated early and repeatedly.

⸻

Frontier/universal construction still overclaim in the intro

The contribution list says the frontier “derives natural coordination-free weakenings for any specification.” The appendix examples are interesting, but the formal framework does not yet support “any specification” in a robust way because many weakenings involve:

* changing the outcome domain,
* changing the future relation,
* residualizing through logs,
* or restricting histories.

I would soften:

We propose a frontier methodology for exploring monotone weakenings and illustrate it on registers, queues, and search structures.

That still sounds valuable and avoids an overbroad claim.

⸻

What I would do next

I think the paper needs one more focused formal revision, not more examples.

1. Add admissible histories to specifications

Change:

Spec = (E, Obs, Ord)

to:

Spec = (A, Obs, Ord)

where A is the admissible history/future structure.

Then monotonicity quantifies only over futures inside A.

This fixes proper coordination, future restriction, barriers, total-order broadcast, and many examples.

2. Split invocations and responses

Replace E_in with E_inv and E_resp.

Use E_iface if you want a combined client-visible set.

This fixes the operational/semantic mismatch.

3. Make exposure formal

Add:

Expose(o) ⊆ ResponseFacts

or:

Prescribes(o,e,v)

Then correctness is:

∃o ∈ Obs(H). Resp(H) ⊆ Expose(o)

4. Add a well-formed response-spec class

Define assumptions such as:

response preservation:
o ⪯ o' implies Expose(o) ⊆ Expose(o')
response totality:
every required invocation has some admissible response
finite response compatibility:
individually explainable local response choices in a common history
have a common explaining outcome

Then state the operational theorem for this class.

5. Separate semantic Complete CALM from operational Complete CALM

Something like:

Theorem 1: Semantic Complete CALM.
Spec is future-monotone iff every admissible outcome is future-consistent.

Then:

Theorem 2: Operational Complete CALM.
For well-formed response-compositional specs, future-monotonicity
coincides with existence of a correct locally immediate implementation.

This will look much more careful and much less tautological.

⸻

Bottom line

This is a stronger copy than the stale one in that it directly addresses enabled responses, fairness, deterministic automata, and joint consistency. But the joint-consistency fix is not mathematically valid, and the paper still lacks two formal ingredients it really needs:

1. common-refinement / response-compositionality, and
2. admissible history/future spaces inside the spec.

Until those are added, I would not trust the main iff theorem in front of PODS reviewers.

The good news is that the conceptual paper is very much alive. The right theorem is probably only slightly narrower:

For response-total, response-preserving, response-compositional specifications over an explicit admissible future space, operational coordination-freedom coincides with monotonicity of exposable outcomes.

That is still a big and useful result, and it would make the rest of the paper much easier to defend.