I read the revised main.tex carefully. The new I/O-automaton section is a real improvement: it directly addresses the previous concern that Complete CALM was just definitional. But I do not yet think the operational theorem is sound as stated. The paper is much closer, but the current proof has several important gaps, mostly around the relationship between local responses, global outcomes, input/output histories, and arbitrary monotonicity witnesses.

My bottom-line view:

The new direction is right. The I/O-automaton model should stay. But the theorem currently needs either a narrower statement or stronger hypotheses. As written, “spec admits a correct coordination-free distributed implementation iff spec is monotone” is still too broad.

The most important changes I would make are:

1. define histories consistently with I/O automata, separating invocations from responses;
2. define an explicit exposure relation from outcomes to response events;
3. restrict the necessity theorem to monotonicity failures that are observable by some process response;
4. fix the sufficiency proof so it produces a globally coherent sequence of exposed outcomes, not just individually valid responses;
5. weaken the operational definition of coordination-freedom so an adversarial scheduler cannot falsify it merely by delivering another input before the process is scheduled to output.

⸻

What improved substantially

The paper now has a much better answer to the “tautology” objection. The addition of:

\subsection{Operational Characterization}

is exactly the right move. The paper now says:

* processes are I/O automata;
* client invocations and message arrivals are inputs;
* responses and sends are outputs;
* coordination-freedom means responding without intervening local input;
* sufficiency uses a causal-view protocol;
* necessity uses indistinguishability.

That is the right shape for the theorem.

The intro also now makes the operational claim explicit:

“This operational grounding distinguishes Complete CALM from a purely definitional equivalence…”

That is good. It signals to reviewers that you understand the issue and are solving it head-on.

The proof style is also directionally right: a constructive protocol for sufficiency, and a GL/FLP-style indistinguishability argument for necessity. This is the right rhetorical and technical package.

But the theorem currently overstates what this proof establishes.

⸻

Main technical issue 1: histories still conflate invocations and responses

The new I/O-automaton model says:

Input actions: client invocations and message arrivals.
Output actions: client responses and message sends.

But the earlier history model still says:

E_in contains client read/write invocations

and then the register examples include responses in E_in:

inv(w_p), resp(w_p) \in E_in
inv(r_p), resp(r_p, 2) \in E_in

This is now inconsistent.

In the I/O-automaton model, resp is not an external input. It is an implementation output. This matters because your admissible histories are defined via input projection:

A(H_in) = { H | H_in \hext In(H) }

If responses are in E_in, then admissibility treats response values as environment-given, which breaks the operational reading. If responses are not in E_in, then the register examples and the definition of Obs(H) need revision.

This is not cosmetic. It affects the core theorem.

You need something like:

E = E_inv \uplus E_resp \uplus E_send \uplus E_recv \uplus E_int

with:

* E_inv and E_recv = input actions;
* E_resp and E_send = output actions;
* E_int = internal actions.

Then define input projection using only invocations and receives, not responses.

Alternatively, if you want histories to include completed operation records as semantic facts, then you should not simultaneously claim they are I/O-automaton input histories. But I think the better fix is to align the history model with the automaton model.

⸻

Main technical issue 2: operational coordination-freedom is too scheduler-sensitive

You define:

A distributed implementation is coordination-free if in every execution,
for every client invocation inv(e)_i, the corresponding response occurs
with no intervening input action at p_i.

In standard I/O automata, the environment/scheduler controls when input actions occur, and input actions are always enabled. So after an invocation at p_i, the environment could immediately deliver another message or client invocation at p_i before the automaton is scheduled to perform its response output. Then your implementation violates coordination-freedom, even if it had the response enabled immediately.

This makes the definition too strong and partly hostage to scheduler interleavings.

You probably want one of these instead:

Option A: Enabled-response formulation

After inv(e)_i, before any further input at p_i, there exists an execution fragment consisting only of internal/output actions at p_i that emits resp(e,v)_i.

This captures “does not need remote input” without requiring the adversary to schedule the response before any other input.

Option B: Quiescent availability formulation

For every execution prefix ending in inv(e)_i, if no further input action occurs at p_i, then p_i eventually produces resp(e,v)_i using only local/internal/output actions.

This is closer to Gilbert-Lynch availability: if the network is silent, the node can still respond.

Option C: Urgent-output model

You can impose a model where enabled response outputs are urgent and cannot be preempted by later inputs. But that is less standard and should be explicit.

As written, the definition says “no intervening input action,” but the proof uses the weaker idea “the process need not wait for input.” Those are not the same under adversarial scheduling.

⸻

Main technical issue 3: correctness over “some outcome” is under-specified

The current correctness definition is:

An implementation is correct for Spec if for every execution prefix whose
induced history is H, the emitted responses are consistent with some
o ∈ Obs(H).

This is a good start, but “consistent with” is doing a lot of hidden work.

You need an explicit exposure/interpretation relation, for example:

Expose(H, o) = set of response events entailed by outcome o at history H

or:

Resp(H) \sqsubseteq o

where Resp(H) is the actual response trace emitted so far.

Then correctness becomes:

for every execution prefix with history H,
there exists o ∈ Obs(H) such that Resp(H) is explained by o.

Without this, the proof cannot precisely connect:

* an outcome chosen by the process,
* the response value emitted,
* the global history after the response,
* and the later refinement relation.

This is especially important because outcomes are abstract. Some outcomes may not “prescribe” a response to a particular invocation at all. The theorem assumes they do.

⸻

Main technical issue 4: sufficiency currently proves only per-response correctness, not global correctness

The sufficiency proof says:

On inv(e)_i, process computes Obs(H_i), chooses o ∈ Obs(H_i),
and responds with v prescribed by o.

Then:

At any global prefix H, local view H_i ⊑ H.
By monotonicity, chosen o has a refinement o' ∈ Obs(H).
Since refinement preserves earlier responses, the emitted response is
consistent with o'.

This shows, at best, that each individual response can be justified by some outcome at the later global history. But operational correctness requires all emitted responses in the prefix to be jointly consistent with one outcome.

Those are different.

Suppose two processes concurrently choose two different admissible outcomes from their local views. Monotonicity says each outcome can be refined into some later outcome. It does not automatically say there is a single later outcome that refines both choices.

You need one of the following additional conditions.

Fix 1: Require exposed outcomes to form a refinement chain

The implementation should maintain a current exposed outcome and only expose refinements of it. But in a distributed setting, two processes may expose concurrently without seeing each other’s previous exposure.

Fix 2: Strengthen monotonicity to finite-join / compatibility monotonicity

For concurrent local exposures, you may need:

For any finite set of outcomes exposed at causally compatible histories, there exists a common refinement at any joint future.

This is stronger than the current pointwise monotonicity condition.

Something like:

If H_1, ..., H_k all embed into a common future H,
and o_j ∈ Obs(H_j),
then there exists o ∈ Obs(H) such that o_j ⪯ o for all j.

This would make the causal-view protocol plausible.

Fix 3: Restrict outcomes so each response is an independent fact

If outcomes are sets of response facts ordered by inclusion, then independently emitted responses compose naturally. But this is a restriction on the outcome model, not arbitrary Ord.

The current theorem claims arbitrary specifications and arbitrary partial orders. For that level of generality, pointwise monotonicity is not enough to guarantee a distributed protocol whose independently chosen local outputs compose into a valid global outcome.

⸻

Main technical issue 5: necessity only works for exposed, local monotonicity failures

The necessity proof says:

Let o ∈ Obs(H_1) be future-inconsistent, witnessed by H_1 ⊑ H_2,
with o prescribing response v to invocation e at process p.

But ordinary non-monotonicity only gives:

o ∈ Obs(H_1)
H_1 ⊑ H_2
no o' ∈ Obs(H_2) with o ⪯ o'

It does not give:

* an invocation e,
* a process p,
* a response value v,
* or that o is externally exposed at p.

So the proof establishes necessity only for monotonicity failures that are locally observable as a response. That is likely the right theorem, but the statement needs to say so.

You could define:

observable monotonicity

or:

exposure-monotonicity

where every outcome that may be exposed by a process must survive futures indistinguishable to that process.

Then Complete CALM becomes:

A specification admits a correct immediate-exposure implementation iff it is exposure-monotone.

If you want the theorem to remain about all outcomes in Obs(H), you need a premise saying every outcome is potentially exposable by some process action.

Right now the theorem quantifies over semantic outcomes, but the operational model only constrains client responses. There is a mismatch.

⸻

Main technical issue 6: the indistinguishability proof assumes too much about the witness future

The necessity proof constructs:

alpha: global history H1; after e arrives at p, no further input at p.
beta: same local state at p when e arrives, but other processes advance to produce H2.

This only works if the H_1 ⊑ H_2 witness can be realized while keeping p’s local state unchanged until response.

But a general future H_2 of H_1 may add:

* receives at p,
* invocations at p,
* local events at p,
* or other events that affect p’s state before the relevant response.

Then p need not be indistinguishable between H_1 and H_2.

For CAP, you correctly introduce partition-constrained futures. For the full Complete CALM theorem, you need an analogous notion: dangerous futures must be invisible to the responding process until it responds.

Otherwise the theorem proves more than the indistinguishability argument supports.

A possible fix:

Define p-silent or p-indistinguishable future:

H_1 ⊑_p H_2

meaning H_2 extends H_1 without adding any input action at p before the relevant response.

Then the operational theorem is about monotonicity with respect to p-silent futures, not all futures.

This is philosophically okay. It says:

Coordination is needed when a locally exposed outcome can be invalidated by a future the process cannot distinguish before responding.

That is arguably the right operational criterion.

⸻

Main technical issue 7: nondeterminism is not handled

The necessity proof says:

Since p's state is identical and the automaton is deterministic ...

But the process definition uses a transition relation, not a deterministic transition function. I/O automata are often nondeterministic.

You can fix this in several ways:

* explicitly restrict to deterministic automata;
* quantify over the same internal nondeterministic choices in both executions;
* treat random bits as local input/internal events included in the local state;
* or phrase the impossibility as “there exists a schedule/adversary resolving nondeterminism so that…”

The simplest is probably:

We restrict to deterministic automata without loss of generality for safety/availability; nondeterministic choices can be represented as internal events, and the indistinguishability argument couples executions with the same local choices.

But you should say it.

⸻

Main technical issue 8: Obs(H_i) may be empty

In the sufficiency protocol, the process computes Obs(H_i) and chooses o ∈ Obs(H_i). But monotonicity does not imply nonemptiness. A monotone spec can have Obs(H)=∅ at some histories.

You need a realizability/input-enabledness condition, e.g.:

For every input history at which a response is required, Obs(H) contains at least one outcome prescribing a response.

Or correctness should allow rejecting/blocking when Obs is empty. But that would conflict with coordination-freedom/availability.

This is especially relevant because elsewhere you use Obs(H)=∅ to model unrealizable histories/invariant violations. If a client invokes a transaction that would violate an invariant, what is the required response? Commit? Abort? If abort is allowed, it should be an outcome. If no outcome is allowed, an available implementation cannot respond correctly.

⸻

Proper coordination: still underdefined relative to prose

The definition remains:

Spec' = (E, Obs', Ord)
Obs'(H) ⊆ Obs(H)
Spec' is monotone

But the prose says:

“fewer admissible outcomes, fewer admissible histories, or both”

The definition only restricts outcomes. It does not restrict the history/future relation except by setting Obs'(H)=∅.

That still does not properly model future restriction. If H_1 is admitted and H_2 is a future that the coordinated implementation would exclude, setting Obs'(H_2)=∅ makes monotonicity fail from H_1 to H_2.

You need the spec to include admissible histories or an admissible-future relation:

Spec = (A, Obs, Ord)

where A ⊆ Hist is prefix-closed, or:

Spec = (Hist, ⊑_Spec, Obs, Ord)

Then a coordinated variant can restrict A or ⊑.

This matters immediately in your separation theorem:

Define the variant Spec' by restricting to histories in which → totally orders E_in.

That is not expressible by your formal definition unless history admissibility is part of the spec.

You have now added an operational model, which makes this even more important: total-order broadcast restricts output histories/futures, not merely Obs.

⸻

Complete CAP: improved framing, but still not theorem-ready

The distributed-monotonicity refinement is a good idea:

non-monotonicity that is process-local does not create CAP impossibility; only partition-spanning non-monotonicity does.

That is useful and should stay.

But the theorem:

A specification admits a consistent, available, partition-tolerant
implementation iff it is distributed-monotone.

still feels too strong as stated.

The proof remains informal. In particular:

* “consistent” is not formally tied to the earlier operational correctness definition;
* “available” is not formally defined in this section;
* “partition-tolerant” is modeled by partition-constrained futures, but not by an execution model;
* “exposed at p” is still informal;
* sufficiency says “every process can safely expose any admissible outcome,” but again does not solve outcome selection or joint consistency;
* necessity again needs an indistinguishability construction, not just “p cannot observe.”

I would either downgrade this to a corollary/sketch, or give a full formal subsection analogous to the I/O-automaton theorem.

A more defensible title might be:

CAP as Distributed Exposure-Monotonicity

rather than “Complete CAP,” unless the proof is made fully operational.

⸻

CALM subsumption is now one of the cleanest parts

The transducer instantiation section is much better grounded. The theorem:

Spec_Q monotone iff Q monotone iff coordination-free transducer

is clean and credible.

This is probably the strongest formal section after the framework. It demonstrates that the abstraction is faithful without overreaching.

One caution: the statement

“The transducer model’s definition of coordination-freedom bakes in replica consistency”

is rhetorically useful but should be phrased carefully. Ameloot et al.’s model includes distributed transducers and output convergence/quiescence assumptions; saying “bakes in replica consistency” is plausible, but a reviewer who knows the model may want precision. Maybe say:

“In the standard CALM formulation, coordination-freedom is tied to eventual production of a common query output, whereas our specification model separates the safety of local exposure from convergence of replicas.”

That is safer.

⸻

The stratified Datalog example is rhetorically good but technically risky

This example says:

“after sealing, the output of stratum 2 is fixed and grows monotonically under set inclusion as the sealed computation completes.”

I think the intuition is right, but this sentence is easy to attack. Once stratum 1 is sealed, stratum 2 may derive negative facts based on absence. The output grows monotonically relative to the sealed snapshot, but the sealing barrier is exactly the coordinated event that changes the admissible future relation.

So this example strongly depends on adding admissible histories/futures to the spec. Under the current (E, Obs, Ord) definition, it is not cleanly expressible.

Suggested phrasing:

“The barrier changes the residual interface: downstream of the barrier, the sealed stratum-1 output is an input constant, and the stratum-2 computation is monotone relative to that fixed input.”

That is more precise.

⸻

The frontier appendix still feels too ambitious

The frontier section remains interesting, but I would not put too much weight on it in the main contribution list unless the formalism is tightened.

The phrase:

“minimal monotone enlargements of the declared order characterize the strongest coordination-free guarantees”

is attractive but heavy. It requires a precise comparison space of specifications/interfaces. Some examples seem to change not only the order but the observable outcome domain.

For example, causal consistency for registers is not simply a monotone enlargement of the prefix order on linearization sequences; it changes from a single global total order to per-process causal views. That is an interface transformation, not just an order weakening.

You do acknowledge this later, but the contribution bullet still sounds stronger than the formal machinery supports.

For this PODS version, I would demote the frontier to:

“A design pattern for deriving coordination-free weakenings”

unless you have space to formalize interface morphisms.

⸻

What I would change in the theorem statement

The current theorem says:

A specification Spec admits a correct coordination-free distributed
implementation iff Spec is monotone.

I would consider replacing it with a theorem along these lines:

A response specification is operationally coordination-free iff it is
locally exposure-monotone: every response outcome that may be exposed by
a process at a local view has a compatible refinement in every global
future indistinguishable to that process until the response.

Then define ordinary monotonicity as a stronger, simpler sufficient condition:

Global monotonicity implies local exposure-monotonicity.
For specifications whose outcomes are exactly accumulated response facts
ordered by refinement, the two coincide.

This would be technically safer.

If you want to preserve the clean “iff monotone” statement, add explicit assumptions:

1. Response-totality: every admissible outcome prescribes responses for pending invocations.
2. Exposure-compositionality: independently exposed responses have common refinements.
3. Prefix-closed admissibility: every local causal view is a prefix of the global history.
4. Observable outcomes: every outcome in Obs(H) is potentially exposable at some process.
5. Scheduler fairness/urgency: enabled local responses cannot be indefinitely preempted by unrelated inputs, or coordination-freedom is stated existentially over local fragments.
6. Determinism or coupled nondeterminism.

With those assumptions, the theorem may be salvageable as stated.

⸻

A possible revised proof architecture

Here is a proof structure I think would withstand review better.

Definitions

Define:

Histories include inv, resp, send, recv, int events.
Input actions are inv and recv.
Output actions are resp and send.

Define actual emitted response facts:

Resp(H)

Define outcome explanation:

Resp(H) ⊨ o

or:

Resp(H) ⊆ Expose(o)

Define local view:

View_p(H)

Define local indistinguishability:

H_1 ≡_p H_2

or silent futures:

H_1 ⊑_p H_2

Semantic property

Define:

Spec is locally exposure-monotone iff
for every p, local view V, outcome o exposable by p at V,
and every global future H compatible with V and silent at p,
there exists o' ∈ Obs(H) refining o.

Sufficiency

Protocol:

* process maintains local view;
* on invocation, chooses a response fact r;
* emits it immediately;
* correctness follows because local exposure-monotonicity ensures a global refining outcome exists for every global future compatible with the local view.

But to handle multiple processes, either:

* responses are accumulated facts under set inclusion; or
* require finite compatibility of concurrent local exposures.

Necessity

If local exposure-monotonicity fails, construct two executions with same local view at p through invocation/response. If p responds, one execution violates correctness; if it waits for an input, it violates coordination-freedom.

Then ordinary monotonicity can be presented as a clean corollary for global specifications where all outcomes are observable and compositional.

⸻

Smaller comments and edits

1. “no input action” should not include another client invocation?

You currently say no message arrival or new invocation may intervene. That means a local process cannot wait for another local invocation either. This is stronger than “no distributed coordination.” It rules out local batching, local serial scheduling, and local locks.

That may be intended, but then Complete CALM is about immediate local response, not merely distributed coordination-freedom. You later say process-local non-monotonicity can be resolved by a local mutex for CAP. That conflicts somewhat with the Complete CALM definition, which treats local waiting as coordination.

You should distinguish:

* coordination-free in the strong local-immediate sense;
* communication-free / partition-available in the CAP sense;
* local serialization allowed vs disallowed.

This is actually a nice conceptual distinction, but it needs explicit naming.

2. “chooses any o ∈ Obs(H_i)” is too strong

Even if the theorem is otherwise fixed, the protocol should not choose arbitrary outcomes. It should choose according to a deterministic selection function that is compatible with refinement, if such a function exists.

If every admissible outcome is safe, arbitrary local choice may be safe individually, but not necessarily jointly.

3. The phrase “implementation determines scheduling” is odd

Earlier you say:

“An implementation is active: it determines which histories are realized (by choosing how to schedule events and deliver messages).”

But in the I/O-automaton model, the adversarial environment controls input scheduling and delivery. The implementation controls internal and output actions. You should revise this paragraph.

4. R_I(H_in) remains somewhat disconnected from the I/O model

You now have both:

* abstract implementation as sets of realizable histories;
* operational implementation as I/O automata.

That is fine, but the bridge should be explicit. For an I/O automaton composition A, define R_A(H_in) as the set of histories induced by executions whose input projection extends H_in.

Otherwise the two implementation notions coexist without fully connecting.

5. “all adversarial schedules” needs fairness nuance

If adversarial scheduling can indefinitely suppress output actions, no implementation can guarantee response. Standard availability properties usually assume fair scheduling of enabled local actions or phrase liveness conditionally. Add the fairness assumption.

⸻

Strategic advice for the paper

The revised paper is much closer to having a publishable core. But right now it is still trying to prove too much at once.

For a PODS submission, I would make the center of gravity:

1. formal model;
2. operational exposure theorem;
3. CALM subsumption;
4. examples: linearizability vs causal consistency, I-confluence, CRDTs;
5. proper coordination as residual monotonicity.

I would soften:

* Complete CAP,
* frontier maximality,
* universal construction,
* strong claims about queues/search structures,
* and “new results” phrasing.

Those can remain, but as applications/discussion unless formalized to the same standard as the I/O theorem.

⸻

Final assessment

The revision meaningfully improves the paper. The I/O-automaton model is the right response to the earlier critique. But the current theorem still has a gap between:

pointwise semantic monotonicity of abstract outcomes

and

existence of a distributed implementation whose independently emitted local responses are globally correct under adversarial scheduling.

That gap is fixable, but it needs explicit machinery: response exposure, local views, indistinguishable futures, compositionality of exposed outcomes, and scheduler/fairness assumptions.

I would not submit the theorem in its current form as an iff over arbitrary (E, Obs, Ord) specifications. I would either narrow the theorem or strengthen the model assumptions. The conceptual story is strong enough that a slightly narrower, precise theorem will be more convincing than a grand theorem reviewers can break.