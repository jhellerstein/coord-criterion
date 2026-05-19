I read main.tex in full, including the appendices, as a fresh PODS-style review. My top-level reaction is: the paper has a strong and appealing conceptual center, but in its current form I think it is at serious risk because the main theorem looks definitional, the implementation model conflates environment behavior with implementation behavior, and several later “new result” claims outrun the formal machinery. The best version of this paper is likely much tighter, more modest in theorem claims, and much more precise about what is actually being characterized.

Executive summary

The core idea is good:

Coordination is required exactly when an observation made now can be invalidated by an admissible causal future.

That is a powerful unifying slogan. It plausibly explains CALM, CAP, HATs, I-confluence, CRDTs, causal consistency, and log-based residualization.

But the current draft makes this into an iff theorem by defining “coordination-free” to require precisely that every admissible outcome be future-consistent. That makes Complete CALM read as:

A spec is coordination-free iff every outcome is future-consistent iff the spec is monotone.

This is elegant, but reviewers may see it as tautological unless you provide a substantially more operational implementation model and prove that your semantic condition exactly corresponds to nonblocking distributed/local implementations in that model.

The paper also currently overclaims. “Complete CAP,” the frontier construction, “proper coordination,” and several application results are interesting, but not yet formal enough to carry theorem/proposition labels at PODS standards.

My advice: make the main paper about the semantic criterion and one or two carefully worked instantiations. Move or soften the frontier/universal construction/CAP iff claims unless you fully formalize them.

⸻

Major strengths

1. The paper has a compelling unifying thesis

The intro frames the problem well: CALM, CRDTs, I-confluence, and HATs feel like siblings but lack a single semantic account. The history/outcome/order abstraction is clean, and the intuition that coordination is needed when exposed observations can be invalidated by future extensions is the right conceptual primitive.

This is the paper’s strongest contribution. I would foreground it even more:

The important move is not “we prove another CALM theorem.”
The important move is “we identify the semantic object that all these CALM-like theorems were secretly about: future-stability of observable outcomes under a declared refinement order.”

That is a real contribution if presented carefully.

2. The running example is mostly excellent

The replicated register example cleanly separates causal consistency from linearizability. The witness with two concurrent writes and opposite later reads is intuitive and useful. This should remain central.

However, it needs to be made definitionally consistent with the later formal model. More on that below.

3. The “proper coordination” framing is valuable

The observation that coordination can be internal, producing a monotone residual interface downstream, is very good. It captures a common architecture: consensus/log/transaction layer resolves non-monotonicity, while consumers see a monotone prefix stream.

This is probably one of the paper’s genuinely distinctive angles beyond prior CALM work.

But the current definition of “properly coordinated variant” does not yet support the examples you use.

4. The paper has broad intellectual reach

The connections to CALM, HATs, I-confluence, CRDTs, CAP, log architectures, prefix orders, and frontier weakenings are ambitious and mostly natural. A PODS audience will appreciate the ambition. The danger is that the breadth makes the draft feel under-formalized in too many places.

⸻

The biggest issue: Complete CALM is currently almost definitional

The key definitions are:

An outcome o ∈ Obs(H) is future-consistent at H if for every future H'
of H, there exists o' ∈ Obs(H') with o ⪯ o'.

Then:

An implementation I is coordination-free if:
(i) R_I(H_in) = A(H_in)
(ii) every o ∈ Obs(H) is future-consistent at every H ∈ A(H_in).

Then monotonicity is:

for all H1 ⊑ H2 and all o ∈ Obs(H1), there exists o' ∈ Obs(H2)
with o ⪯ o'.

So the theorem:

A specification admits a coordination-free implementation iff it is monotone.

is proved essentially by unpacking definitions. This is not necessarily fatal, but the paper must be honest about what is being achieved. Right now the draft calls this “Complete CALM” and “the main result,” but the proof is intentionally trivial. A reviewer may respond: “You defined coordination-free to mean monotone, then proved equivalence.”

You can rescue this in one of two ways.

Option A: Reframe as a semantic definition, not a deep theorem

Make the contribution:

We propose future-monotonicity as the semantic definition of coordination-freedom for specifications, and show that it specializes exactly to known model-specific notions.

Then the main theorem can be presented as a sanity check or representation theorem, not the source of technical weight.

In this framing, the real work becomes the instantiations:

* CALM exact subsumption.
* HAT/I-confluence/CRDT recovery.
* Linearizability vs causal consistency.
* Properly coordinated residual interfaces.

Option B: Strengthen the operational model

If you want “Complete CALM” to be an actual iff theorem, you need an implementation model where:

* processes have local views,
* outputs/exposures are actions,
* coordination is modeled operationally as waiting for remote information, suppressing futures, requiring communication, blocking, aborting, or excluding schedules,
* availability/nonblocking is stated as a liveness property,
* correctness is stated over traces with exposed outputs,
* and then you prove equivalence to future-monotonicity.

That is much harder, but would make the theorem nontrivial.

As written, the implementation does not expose outcomes; it only chooses realizable histories. Condition (ii) is independent of the implementation. That makes “admits an implementation” feel vacuous: if the spec is monotone, set R_I = A; if it is not, no implementation can satisfy a condition that is not actually about I.

My recommendation for this submission: choose Option A. It is cleaner and safer. Sell the result as a semantic completion and unification of CALM, not as a new operational impossibility theorem for all systems.

⸻

Critical modeling problem: histories conflate environment, protocol, and output

This is the most important technical issue to fix.

The paper defines histories with external inputs, internal computation, sends, and receives. It then defines admissible histories as those that “could arise under asynchrony and causality alone,” and an implementation as selecting a subset of those histories.

But sends, internal events, responses, commits, and exposed outputs are not all environment nondeterminism. Many are implementation choices. For example:

* whether to send a message is a protocol choice;
* whether to respond to a read is an implementation choice;
* whether to commit or abort a transaction is an implementation choice;
* whether to expose an outcome is exactly what coordination is supposed to control.

The register examples treat read responses as part of the history, e.g. resp(r_p, 2). But then the history already contains the output whose safety we are trying to analyze. If a correct implementation would avoid returning 1 at q, is that “history suppression,” “outcome suppression,” or just choosing not to emit an invalid response? The current model blurs these.

You likely need to separate at least three layers:

1. Environment/input history: invocations, crashes, message delays, partitions, external transaction requests.
2. Implementation/action history: sends, receives, local steps, commit/abort choices, response emissions.
3. Observation/outcome: the semantic artifact exposed to clients/downstream consumers.

Right now E_in includes both invocations and responses in examples. That creates trouble because “no history suppression” then appears to require the implementation to allow arbitrary response histories, including incorrect ones.

A cleaner model might use:

* E_req: environment requests/invocations.
* E_net: message delivery events controlled by adversarial scheduler, subject to sends.
* E_act: implementation actions.
* E_exp: exposure/response events.

Then a spec maps prefixes of request/delivery/exposure histories to allowed semantic outcomes, and an implementation decides when exposure events occur. Coordination-freedom should say something like:

If a local process has enough local information to expose an outcome allowed by the spec, it need not wait for future remote events to avoid invalidation.

Or, if staying abstract:

The semantic interface is coordination-free when every exposure allowed at a history is stable under admissible environment extensions.

But then call it a property of the interface, not an implementation theorem.

⸻

“Proper coordination” definition does not support its examples

The paper defines a properly coordinated variant as:

Spec' = (E, Obs', Ord)
Obs'(H) ⊆ Obs(H)
Spec' is monotone

But the prose says it can restrict “fewer admissible outcomes, fewer admissible histories, or both.” The definition only restricts outcomes. It does not restrict the history space except indirectly by making Obs'(H)=∅.

That indirect approach is insufficient. Suppose H1 is a serialized history with a nonempty outcome, and H2 is a future that adds a concurrent or otherwise nonserialized event. If Obs'(H2)=∅, then monotonicity fails: the outcome at H1 has no refinement at H2.

This directly affects the proof sketch of the separation theorem:

“Define the variant by restricting to histories in which → totally orders E_in.”

That is not expressible by your definition unless the future relation/histories are also restricted. If you merely set Obs'=∅ outside serialized histories, monotonicity will often fail.

You need to generalize specifications from (E, Obs, Ord) to something like:

Spec = (Hist_adm, Obs, Ord)

or:

Spec = (E, A, Obs, Ord)

where A is the admissible history/future relation for the interface. Then a coordinated variant can restrict either:

* the history space/futures, representing locks, serialization, barriers, leaders, total-order broadcast; or
* the outcomes, representing aborts, quorum reads, validation, withheld exposure.

That change would also help CAP and universal residualization.

⸻

The paper needs a sharper distinction between “restriction” and “residual interface”

You already notice this in Appendix G:

The universal construction produces a new output interface, not a restriction of the original specification’s outcome domain.

That distinction should move much earlier. It is central.

There are at least three transformations currently grouped together:

1. Outcome restriction: fewer allowed outputs at the same histories.
2. History/future restriction: fewer executions/futures are admissible.
3. Interface residualization: expose a different semantic object, e.g. log prefixes rather than the original object’s abstract state.

These are all legitimate ways coordination can “discharge” non-monotonicity, but they are not the same mathematically.

The paper should define them separately. For example:

A coordinated restriction of Spec restricts Hist and/or Obs while preserving Ord.
A residualization of Spec maps histories/outcomes through an interface function φ into a new outcome domain O_res with order Ord_res.
A proper residual is one whose resulting specification is monotone.

Then the Paxos/log example becomes clean: Paxos is not merely a coordinated variant of linearizability; it is a residualization exposing a monotone log-prefix interface.

⸻

Complete CAP is promising but too loose as stated

The CAP section has the right intuition:

CAP obstruction occurs when a locally exposed outcome can be invalidated by a partition-constrained remote future.

But the theorem as written is not yet formal enough for an iff claim.

Problems:

1. Availability is existential, not universal

The appendix defines maximal availability as:

if some partition extension completes a client invocation and admits nonempty Obs, there exists an execution of I in which e completes.

CAP availability is usually universal/fairness-style: every request to a nonfailed node eventually receives a response. Your existential version seems too weak. An implementation that sometimes responds and sometimes blocks might satisfy the existential condition but not availability.

You note that stronger universal availability “only strengthens the impossibility direction,” but for an iff theorem the sufficiency direction depends on the exact definition.

2. The proof needs indistinguishability, not just “cannot observe”

The impossibility direction says process p cannot observe remote activity under the partition. But to prove CAP-style impossibility, you need two executions with the same local view at p up to the response point and different global futures. The current proof gestures at this but does not build the indistinguishable executions.

3. “Consistent” is not formally defined

The theorem says “consistent, available, partition-tolerant implementation” but correctness/consistency is just “correct on all well-formed histories” in the appendix. You need to align the terms.

4. Distributed-monotone quantifies over outcomes “exposed at p”

The phrase “exposed at p” is only informally defined:

if o determines a response to an invocation event at p.

That is too informal for the theorem doing so much work. You need a projection or exposure relation:

Expose_p(H, o, e, v)

or a local observation map.

My recommendation: either downgrade Complete CAP to a proposition/interpretation, or give it a formal model with local views, partitions, availability, and indistinguishability.

⸻

The causal consistency treatment is internally inconsistent

The running example defines causal consistency using per-process causal views that may order concurrent writes differently. Good.

But the appendix later defines causal consistency for the register as outcomes ordered by prefix extension, and says:

Obs_causal(H) = { o | every read r in o returns some v with w(v) in past(r,H) ... }

This is not the same object. It is also not a standard full causal consistency spec for registers. It allows reads to return “some” causally prior write, which is too weak unless you intend a very permissive multi-value/last-writer-less register. It also says initial value is allowed only when no write is in the causal past, which may conflict with common read semantics depending on how local writes and concurrent writes are handled.

More importantly, the proof says:

past(r,H2) ⊇ past(r,H1)

But by your future definition, no new predecessor of an old event can be added. So for reads already in H1, the past should be equal, not merely superset. The point is good — old reads remain valid — but the formal statement should be tightened.

You need one consistent causal-register specification throughout the paper. Possible choices:

1. Per-process view model: outcomes are maps from process/read events to causally closed partial orders or sequences. Refinement adds events/views without changing prior read explanations.
2. Causal past return model: outcomes are read-return facts, ordered by set inclusion, where each read’s return is justified by its fixed causal past.
3. Causal memory model: outcomes are operation histories with per-process serialization orders satisfying causal constraints.

I think option 1 best matches your running example.

⸻

The linearizability example needs careful wording

The example says linearizability requires a single total order consistent with happens-before, “i.e., if operation A completes before operation B begins, then A precedes B.”

That parenthetical is the usual real-time order, but your histories are Lamport partial orders. In the example you then rely on message-delivery causality from a write to a later read, not just operation completion-before-invocation. This is okay if your spec is not vanilla Herlihy-Wing linearizability but “linearizability respecting execution-order happens-before” or “Lamport-history linearizability.”

You should name that explicitly. Otherwise a reviewer may object that linearizability only orders non-overlapping operations by real-time order, and message propagation events are not usually part of the object history unless they affect invocation/response order.

Suggested wording:

We use a Lamport-history version of linearizability: the linearization order must extend the happens-before order induced by process order and message delivery among operation events. This is stronger than pure object-history linearizability when internal communication creates causal dependencies, and it is the appropriate order for our history-based specification model.

Or, if you want standard linearizability, make the witness use invocation/response real-time order only.

⸻

There is at least one stale/inconsistent witness

In the Complete CALM section, the draft says:

The register witness ... is exactly such a failure:
o_{H_1} = { (r ↦ 0, w(1)) } has no prefix-extension at H_2.

This does not match the running example, which uses:

⟨ w_p(1), w_q(2), r_p ↦ 2 ⟩

This is likely leftover text. It should be fixed; it will be noticed.

⸻

The “frontier” construction is attractive but currently under-proved

The coordination-free frontier is a nice idea, but the appendix proofs are too hand-wavy for theorem/proposition status.

Register frontier

The maximality proof says: take any smaller order than causal prefix; choose H2 such that o2 is the only causally consistent extension. This is not generally justified. The space of causal outcomes usually has many valid extensions. You need strong assumptions to make uniqueness hold.

Also, the frontier is defined as minimal monotone enlargements of a fixed order over a fixed Obs, but the register proposition says causal consistency “weakens total-order outcomes to causal-prefix outcomes.” That changes the outcome structure, not just the order. You acknowledge this in prose, but then the proposition still leans on the frontier definition.

Queue frontier

The causal FIFO maximality argument is not tight. It uses examples of concurrent enqueues and says any smaller order must declare one pair incompatible, but “smaller order” over prefix sequences is not the same as adding a global order between concurrent values. The proof needs a precise lattice/order-theoretic statement.

Search frontier

The forward-reachability example is evocative and potentially very nice, but the maximality claim is not proved. “Any order smaller than forward-reachability must declare some pair invalid” confuses the observation predicate with the refinement order. Also, exact-location semantics and forward-reachability semantics have different Obs, not merely different orders.

My recommendation: keep the frontier as a discussion/conjectural design pattern unless you want to invest several pages formalizing interface morphisms and maximal monotone weakenings.

For PODS, unsupported maximality claims are dangerous.

⸻

The universal construction currently overstates “coordination-free downstream”

The universal construction says an ordering authority plus membership makes any spec residual monotone. That is true if the residual output is “prefix-indexed evaluation over an ordered log,” but then the theorem is almost independent of the original spec: any append-only log is monotone under prefix order.

That may still be useful, but the current prose makes some stronger architectural claims that should be softened.

In particular:

“establish membership once, then process all subsequent computation coordination-free”

But the theorem also requires an ongoing ordering service, which is itself coordination. Later you acknowledge that, but the architectural paragraph still risks sounding like membership alone suffices.

Also, the stratified Datalog remark says stratum sealing requires waiting for all participants but “no distributed coordination is needed beyond knowing who the participants are.” This is rhetorically risky. Waiting for end-of-data signals from all participants is communication and a barrier. You want to distinguish monotone waiting from non-monotone choice/coordination, but many reviewers will still call a barrier coordination.

I would avoid saying “zero additional rounds of distributed coordination” unless you define coordination narrowly as resolving incompatible futures, not waiting/communication. Say instead:

The subsequent barriers are monotone joins over known participants: they require communication and waiting, but not semantic coordination in the sense of choosing among incompatible futures.

That is a better distinction.

⸻

Application sections: mostly plausible, but theorem labels are too strong

HATs / isolation

The read committed monotonicity proof is fine as an intuition. The serializability witness is also good.

But the claim “HAT levels are monotone” needs more careful coverage if stated as a proposition. HATs include several guarantees with subtle definitions. Either restrict the proposition to the specific ones you prove, or make it a lemma schema and move details to appendix.

The line:

“Snapshot isolation similarly requires coordination… but we omit it here”

is a missed opportunity. PODS reviewers will either want the witness or want the claim removed. If you mention SI, give the witness.

I-confluence

This is one of the best application matches, but the instantiation needs care.

You define Obs_I(H) using the converged state conv(H), “the state the system will inevitably reach once gossip completes.” But earlier the model imposes no fairness/progress assumptions and messages may be lost indefinitely. “Inevitable” therefore needs to be semantic closure, not actual future inevitability.

You can define:

conv(H) = join of all updates present in H

or:

conv(H) = closure of H under eventual delivery/merge

But do not rely on inevitability unless the model includes eventual delivery.

CRDTs

The CRDT monotonicity proposition is intuitively right, but the proof has a quantifier gap. It says every state reachable at H' is at least as large as some state reachable at H; what you need is: for every o ∈ Obs(H), there exists o' ∈ Obs(H') with o ≤ o'.

This is easy to fix if Obs(H) is the set of states reachable by applying some subset/order of events in H; then from a chosen o, apply the additional updates/merges in H'\H to get o'. But state that.

Also, “reset-capable CRDTs require additional protocol machinery” is true in spirit but too quick. Some reset designs use epochs/dots/tombstones; the semantic order changes so reset becomes inflationary in a richer lattice. That actually supports your thesis: the coordination story depends on the declared outcome order/interface. Mentioning that nuance would strengthen the paper.

⸻

Related work risk: some claims need toning down

The related work section sometimes says “X is a special case of ours” where the formal subsumption has not really been shown. That will provoke reviewers familiar with the cited work.

Examples:

* Attiya et al. arbitration-free consistency: “Their criterion is a special case of ours” is plausible but not proved here. Say “closely related” unless you give a formal embedding.
* Baccaert and Ketsman 2026: since this is presumably very recent/possibly unpublished relative to reviewers, be precise and avoid leaning on it unless the citation is solid.
* Mahajan et al.: saying your frontier derivation “recovers” their result is too strong unless your causal consistency and maximality proof are made rigorous.

⸻

Presentation and structure

The paper is currently trying to be too many papers:

1. Semantic Complete CALM.
2. Complete CAP.
3. Proper coordination/residualization.
4. CALM hierarchy subsumption.
5. HAT/I-confluence/CRDT applications.
6. Coordination-free frontier for registers/queues/search structures.
7. Universal ordering construction.
8. Speculation about stratification/boundedness/query containment.

For PODS, I would focus.

A stronger structure:

1. Introduction.
2. Running example: linearizability vs causal consistency.
3. Semantic framework: histories, outcomes, refinement.
4. Future-monotonicity criterion.
5. Exact CALM instantiation.
6. Proper coordination/residualization, with one clean log/linearizability example.
7. Applications: I-confluence and CRDTs, maybe HATs if space.
8. CAP as a corollary/discussion, not full theorem unless formalized.
9. Related work and conclusion.

Move frontier and universal construction to “discussion/future work” or a shorter appendix.

⸻

Suggested revised thesis

I would avoid saying:

“Complete CALM: a specification admits coordination-free implementation iff it is monotone.”

Instead, try:

“We identify future-monotonicity as the semantic core of coordination-freedom. A specification is coordination-free exactly when every outcome it permits at a history remains refineable in every admissible future. This condition specializes to monotone queries in relational CALM, to merge-closure in I-confluence, and to inflationary lattice evolution in CRDTs. Because the criterion is stated over specifications rather than programs, it can also verify residual interfaces produced by coordination layers, such as log-prefix outputs from consensus.”

This is less grandiose but more defensible.

⸻

Concrete fixes I would make before submission

Must fix

1. Separate environment histories from implementation/output histories, or explicitly narrow the paper to semantic interfaces rather than operational implementations.
2. Revise the Complete CALM theorem framing so it does not look tautological.
3. Change the spec definition to include admissible history space/future relation, not just (E, Obs, Ord). You need this for proper coordination.
4. Fix properly coordinated variants to allow:
    * outcome restriction,
    * history/future restriction,
    * and residual interface maps.
5. Unify the causal consistency model between the running example and appendix.
6. Fix the stale register witness using r ↦ 0, w(1).
7. Downgrade or fully formalize Complete CAP.
8. Downgrade frontier maximality claims unless you can make the interface comparison formal.

Should fix

9. Give a precise definition of “exposed at process p.”
10. Clarify whether linearizability extends real-time order only or full happens-before.
11. Avoid saying barriers are not distributed coordination unless you define coordination narrowly.
12. Add a short “what is not claimed” paragraph:
    * monotonicity is semantic, not a decidable algorithm in general;
    * coordination-free does not mean no communication;
    * monotone residualization can change the interface;
    * replica convergence is separate from coordination-freedom.
13. Tighten all theorem/proposition labels. Some should become examples or observations.

⸻

Possible rewritten core definitions

Here is the direction I’d consider.

Define a semantic interface as:

A specification is (A, Obs, ⪯), where A is a prefix-closed set of admissible histories equipped with a future relation ⊑, Obs(H) is the set of outcomes permitted at H, and ⪯ is refinement.

Then:

Spec is future-monotone iff
for all H ⊑ H' in A and o ∈ Obs(H),
there exists o' ∈ Obs(H') such that o ⪯ o'.

Then define:

An interface is semantically coordination-free iff every permitted exposure is future-stable under admissible futures.

Then the theorem becomes:

Future-monotonicity is equivalent to semantic coordination-freedom.

This is intentionally definitional, but useful.

For operational claims, say:

Any operational model in which coordination is precisely the exclusion of admissible futures or withholding of future-unstable outcomes soundly maps to this criterion.

Then show CALM is one such model.

⸻

My bottom-line recommendation

This is a promising PODS paper, but the current draft is not yet ready as a theory paper because the formal core and the big claims are misaligned.

The strongest path is:

* Reduce the theorem ambition.
* Increase definitional precision.
* Make the paper about the semantic abstraction and its instantiations.
* Use “proper coordination” as the distinctive payoff.
* Move frontier/CAP/universal construction into a lighter-weight section unless fully formalized.

The conceptual contribution is real. The paper will be much more credible if it openly says: “The main equivalence is simple because we have isolated the right semantic object,” and then spends its rigor budget proving that the object faithfully explains existing coordination boundaries.