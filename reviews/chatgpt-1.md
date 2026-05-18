Overall assessment

This is an ambitious and potentially important paper. The pitch is attractive for PODS: CALM, but lifted from programs to specifications and observable outcomes. That is exactly the kind of conceptual unification PODS can like, especially because the examples touch transactional isolation, invariant confluence, CRDTs, and the CALM lineage.

But in its current form, I think the paper is not yet reviewer-safe. The main issue is not exposition; it is that several core definitions and proofs are currently too loose, and one key running-example extension appears to violate the paper’s own definition of history extension. A skeptical PODS reviewer will likely pounce on this. The paper has a strong idea, but it needs a tighter formal core before the surrounding claims about “universal,” “complete,” “strict generalization,” and “one round suffices” will be accepted.

My headline recommendation: narrow and harden the theorem before broadening the applications. The paper should make one precise semantic criterion incontrovertible, then present the applications as carefully scoped corollaries or evidence, not as fully settled universal recoveries unless you can formalize them at the same level.

I reviewed the attached draft, Complete CALM: A Universal Criterion for Coordination-Freedom  ￼.

⸻

Likely PODS reviewer reaction

A friendly reviewer will see the promise:

“This paper proposes a specification-level version of CALM, replacing program monotonicity with monotonicity of observable outcomes over Lamport histories. This is a natural and potentially valuable abstraction that unifies several known coordination-avoidance results.”

A skeptical reviewer will say:

“The central definitions do not yet support the claimed iff theorem. The implementation model, exposure semantics, and possibility preservation condition appear insufficiently formalized. Several examples seem inconsistent with the history model. The universal construction appears to change the specification or outcome order rather than implement the original specification.”

That second review is the one to defend against.

⸻

Major issue 1: the running register witness appears invalid under your future definition

This is the most urgent correctness issue.

You define a future H1 ⊑h H2 so that E1 is downward-closed under →2: if e ∈ E1 and e' →2 e, then e' ∈ E1. That means a future cannot add a new causal predecessor of an existing event.

But in the running example, H1 contains the read event r, and H2 adds a receive event rs with rs → r, thereby adding a new predecessor of an event already present in H1. The draft even says this does not introduce a predecessor of an existing event, but it does: r is existing, rs is new, and rs → r.

This is not a small typo. It breaks the core witness separating eventual consistency and linearizability.

You need to repair the model. Possible fixes:

1. Split operation events into invocation and response.
    Let H1 contain a write invocation and a read invocation, but not the read response. Then H2 can add the message receive before the read response, without adding a predecessor of an existing response event.
2. Use partial histories with open events.
    If r in H1 is only a pending operation, not a fixed event whose causal past is closed, then the future can complete it after newly delivered information. But then the history model must distinguish pending invocations from completed observations.
3. Change the witness.
    Keep downward-closed futures, but make the non-monotonicity arise from an outcome exposed at H1 whose incompatibility appears when future events are appended, not by retroactively inserting causal predecessors of an existing read.

I would choose option 1. It is standard, clean, and aligns well with linearizability: histories contain invocation and response events, and completed operations are those with both.

A revised witness would say:

* H1 contains completed write w(1) at p, a read invocation inv(r) at q, and an in-flight propagation message.
* At H1, an implementation may still expose a response resp(r,0)? Careful: if the response is not yet in the history, is it admissible in Obs(H1)? You need to decide whether Obs(H) includes possible future outputs or only outputs already exposed at H.
* Alternatively, let H1 contain the read response returning 0, and let H2 later contain some event that makes that response incompatible without being causally before it. For linearizability, that may require a real-time edge, not a causal-past edge.

This leads directly to the next issue.

⸻

Major issue 2: Obs(H) ambiguously mixes “currently exposed” and “possible under extensions”

The paper’s core theorem depends on a very sharp distinction among:

1. What has already happened in the history.
2. What may happen in future extensions.
3. What the specification permits.
4. What the implementation actually exposes to clients.
5. What an external observer is committed to never retracting.

Right now, Obs(H) is asked to do too many jobs. Sometimes it means outcomes already observable at H. Sometimes it means outcomes admissible under completions of H. Sometimes it seems to include possible return values for reads that have not yet completed. This ambiguity appears in the register example and then again in the theorem proof.

I think you need two semantic maps, not one:

* May(H): outcomes that are still possible in some admissible completion/extension of H.
* Obs(H): outcomes actually permitted to be exposed at H.

Then the monotonicity criterion should probably be about exposed commitments:

If an outcome may be exposed at H1, then for every admissible future H2, there must be an outcome exposable at H2 that refines it.

That is close to what you intend, but the current formalism lets Obs(H) float between may- and must-/now-observability.

A PODS reviewer will ask: “Is Obs(H) an angelic set of possible outcomes, a demonic set of allowed commitments, or the actual output behavior of an implementation?” The answer needs to be unambiguous.

⸻

Major issue 3: the implementation definition does not quite support the iff theorem

Definition 8 defines coordination-freedom using equality of two possibility sets:

Poss_I(H) = Poss(H).

But this equality is not obviously the right semantic substitute for “no coordination,” and the proof does not consistently use it.

Sufficiency problem

In the proof, you say:

If Spec is monotone, set R_I(Hin) = A(Hin) and let Expose_I(H) ⊆ Obs(H) be any nondeterministic choice.

But if Expose_I(H) is an arbitrary subset of Obs(H), then Poss_I need not equal Poss. It may omit outcomes the specification permits. To make the equality true, you likely need something like:

* Expose_I(H) = Obs(H) for all realized H, or
* a nondeterministic implementation whose possible executions cover every outcome in Obs(H), or
* a liveness/fairness assumption ensuring every spec-permitted outcome remains reachable.

As written, “any nondeterministic choice” is too weak.

Necessity problem

The necessity proof says that if o1 ∈ Poss, then the implementation “may expose o1,” and if exposing it causes trouble, the implementation must suppress either o1 or H2.

But an implementation can be correct by simply not exposing o1 at H1 while still preserving it as a possible outcome along some other branch. Whether that counts as coordination depends on your definition. If Poss equality requires every spec-permitted outcome to remain reachable, then you need to show that o1 is reachable only by exposing it before the incompatible extension. If not, the argument does not go through.

This is especially delicate because Poss is a union over extensions. An outcome in Obs(H1) can appear in Poss(H1), but the implementation might expose it at a different extension or under a different scheduling branch. The proof needs to track histories, branches, and exposure times more carefully.

Suggested fix

I would define implementation behavior as a prefix-closed set of traces with output events, and correctness as a safety condition on every trace prefix. Then coordination-freedom can be stated as an input-enabledness / future-preservation property:

For every implementation prefix compatible with history H, and every admissible causal extension H' of H, the implementation has a continuation realizing H' without retracting prior outputs.

Then the theorem becomes much more natural:

* Monotonicity gives you a continuation-preserving implementation.
* Non-monotonicity gives you an output that cannot be preserved under some admissible future, so any implementation that exposes it must either block/suppress that future or avoid exposing the output.

This is closer to standard safety/liveness reasoning and will be easier for theory readers to trust.

⸻

Major issue 4: “well-coordinated” is not yet formal enough

The abstract and introduction make a strong distinction:

* coordination-free: no coordination has been applied;
* well-coordinated: coordination already applied suffices, no more is needed.

This is a compelling conceptual contribution. But formally, the paper mostly proves a theorem about coordination-free implementations of a specification. Then Section 4 introduces “resolved specifications” by restricting histories through a coordination mechanism.

That move needs to be made first-class.

Right now, the paper risks equivocation:

* For the original specification, coordination is required.
* After a coordination mechanism restricts histories, the residual/resolved specification is monotone.
* Therefore the system is “well-coordinated.”

That is a good idea, but it is not the same theorem as “a specification admits a coordination-free implementation iff monotone.” It is a theorem about residual coordination-freedom after quotienting/restricting the history space by a prior mechanism.

I would explicitly introduce:

A coordination mechanism C transforms Spec into a residual specification Spec/C.
C is complete for Spec if Spec/C is monotone.
A system is well-coordinated iff its residual specification after its internal coordination mechanisms is monotone.

Then “Complete CALM” can be presented as the test for both:

* ordinary coordination-freedom: Spec is monotone;
* residual coordination-freedom: Spec/C is monotone.

That would cleanly support your separation from CALM.

⸻

Major issue 5: Theorem 3, “membership universally suffices,” is overclaimed

This theorem will draw scrutiny. As written, it says that for any specification, establishing membership makes the resolved specification monotone. The proof then changes the behavior to:

* wait until all inputs arrive;
* deterministically evaluate the specification over complete input;
* use an order with ⊥ ⪯ o.

This feels too close to “make any computation monotone by hiding all output until the end.” That may be true in a vacuous sense, but it risks undermining the paper’s central claim. Reviewers may say: if every specification can be made monotone by adding ⊥ and delaying output, then what exactly is the criterion measuring?

Specific concerns:

1. It changes the observation discipline.
    The original specification may allow or require incremental observations. The construction replaces them with “undefined until all inputs arrive.”
2. It assumes finite, known, complete input.
    Many distributed/database specs are online or open-ended. “Once a node has received input from every member of All” only works for a closed batch, not an ongoing service.
3. It collapses nondeterminism.
    “Evaluates the specification deterministically” chooses one result from a relation. That may be an extra commitment not accounted for by membership.
4. Membership is not the only commitment.
    For many specs, knowing participants does not determine a total order, winner, arbitration choice, serialization order, etc. The construction obtains determinacy by waiting for all relevant inputs and then computing centrally/locally, but that may be a much stronger closure assumption than mere membership.
5. The theorem may be true only under a closed-world/batch interpretation.
    If so, state that. It could still be useful, but the current “universal coordination primitive” language is too strong.

I would either move Theorem 3 to a discussion section and soften it, or restate it as:

For closed finite computations, once the input domain and termination condition are established, any specification can be evaluated by monotone accumulation followed by local deterministic evaluation.

That is safer and still useful. But I would not put it forward as a central contribution unless fully formalized.

⸻

Major issue 6: Some application claims are currently too sketchy for PODS

The applications are promising, but several are asserted at a level that PODS reviewers may find hand-wavy.

Transaction isolation

The serializability witness is plausible in spirit, but the modeling needs tightening.

You define outcomes as sets of facts ordered by inclusion. But serializability is not just about facts accumulating; it is about existence of a serialization order. If an outcome fact-set includes commit(T1) and read(T1,x,0), future additions may make the set unserializable. That supports non-monotonicity.

But for HAT levels, the statement “extending a history may add committed transactions but cannot invalidate previously exposed commit or read facts” is too broad. Some session guarantees, read-your-writes, monotonic reads, causal consistency, etc., depend on client/session order and visibility choices. You need a precise class of histories and outcomes.

Also, the claim that snapshot isolation is non-monotone by write skew is fine, but write skew is not exactly the same as serializability violation unless the invariant or serialization target is stated. Snapshot isolation itself permits write skew; it is not “non-monotone” in the same way serializability is unless your outcome spec includes constraints that future transactions invalidate.

Invariant confluence

This section is currently the shakiest application.

You write that outcomes are “sets of database states reachable under causally admissible extensions, ordered by set inclusion (refinement = ruling out states).” But if refinement is ruling out states, the order should likely be reverse inclusion, not inclusion. If o2 rules out states relative to o1, then o2 ⊆ o1, so o1 ⪯ o2 would correspond to superset-to-subset ordering.

This matters because the monotonicity proof depends on the direction of the order. As written, “extending a history can only enlarge the reachable-state set” conflicts with “refinement = ruling out states.”

Also, I-confluence is about whether independently reachable invariant-satisfying states can be merged while preserving the invariant. To recover it, you probably need outcomes to encode accepted/visible states and merge closure more carefully.

CRDTs

This is the cleanest application. The proposition that inflationary updates and joins induce monotone observable states is straightforward. But the “necessary” language should be softened. Complete CALM says monotone observable semantics are necessary for coordination-free behavior under the chosen outcome order; it does not say the semilattice discipline is necessary. You already say it is “one way,” but elsewhere the rhetoric leans stronger.

⸻

Major issue 7: The title and “Complete CALM” framing may overpromise

“Complete CALM” is catchy, but it raises expectations:

* Complete with respect to what model?
* Complete relative to which notion of coordination?
* Complete despite arbitrary choice of outcome order?
* Complete despite hiding output until finalization?

The title says “A Universal Criterion for Coordination-Freedom,” while much of the paper’s real novelty is about residual coordination-freedom after coordination has discharged non-monotonicity. That is more subtle and more interesting than the current slogan.

Possible title variants:

* Complete CALM: Coordination-Freedom as Monotone Observability
* Beyond CALM: A Semantic Criterion for Residual Coordination-Freedom
* Well-Coordinated Systems: A Semantic Generalization of CALM
* Observable Monotonicity and the Boundary of Coordination

I like “Complete CALM” as a term, but the subtitle should probably signal the exact semantic move.

⸻

What I would prioritize before submission

Priority 1: Fix the formal core

Before polishing prose, I would rewrite Sections 2–3 around a tighter distinction among:

* histories;
* futures;
* admissible completions;
* observable commitments;
* implementation traces;
* residual specifications after a coordination mechanism.

The current theorem can probably be salvaged, but the proof must be rebuilt around an implementation model that explicitly preserves prior observations across futures.

Priority 2: Fix the running example

The register example is doing too much work to be even slightly wrong. It should be a perfectly crisp witness.

I would rewrite it with invocation/response events and completed operations. Make clear whether the problematic outcome is:

* a response already exposed at H1, or
* a possible response in a completion of H1.

If it is the latter, then the monotonicity condition should be about possible completions, not current observations.

Priority 3: Soften or move Theorem 3

The membership theorem currently threatens to make the paper look either trivial or false. A reviewer could say: “Of course if you wait until all inputs arrive and expose only a final answer under a specially chosen order, everything is monotone.”

I would either:

* restate it as a closed-world/batch corollary;
* move it after the main applications;
* or replace it with a more modest architectural proposition about log/sequencer patterns.

Priority 4: Make the Section 4 separation the centerpiece

The most compelling contribution is not merely “CALM generalized to arbitrary specs.” It is:

Program-level non-monotonicity is not the right diagnostic once coordination has already occurred. The right diagnostic is monotonicity of the residual observable output.

That is a strong systems/theory insight. I would foreground it more and prove it carefully.

A possible restructuring:

1. Original CALM diagnoses uncoordinated programs.
2. But real systems compose coordination layers with downstream consumers.
3. A layer may be internally non-monotone but externally monotone.
4. Therefore the right object is not the program but the residual observable specification.
5. Complete CALM characterizes when that residual needs no further coordination.

That story is sharper than “universal criterion” alone.

⸻

Smaller technical and presentation issues

There are several textual and LaTeX issues that should be cleaned up:

* “propertie” → “properties.”
* “Specec” is awkward; maybe Spec_ec or Spec_EC.
* Section reference typo: Section efsec:universal-construction.
* “Connection to CAP..” has a double period.
* Missing references: Hellerstein determination paper, Immerman–Vardi, Kafka, Burckhardt, Attiya/Enea/Román-Calvo, extended version.
* The proof of Proposition 5 has a likely direction typo: “for every admissible extension H2 ⊑h H1” should presumably be H1 ⊑h H2.
* Appendix B’s induced order proof is not convincing as stated; it derives an order from one implementation’s exposed behavior, but then claims Spec is monotone, although Spec’s Obs may contain outcomes never exposed by that implementation.
* The paper alternates among “Coordination Criterion,” “Complete CALM,” and “Coordination-freedom” terminology. Pick one primary formal name and use others as explanatory aliases.
* Avoid saying prior work “cannot” do something unless the claim is carefully delimited. For example, CALM can reason about some stratified programs if you model stage boundaries as inputs/epochs. Your stronger point is that the program syntax alone does not express residual coordination status.

⸻

A possible revised theorem statement

Something like this might be more defensible:

Theorem. Let Spec = (H, Obs, ⪯) be a specification where Obs(H) denotes the set of outcomes that may be irrevocably exposed at history H, and where implementations must preserve exposed outcomes under causal extension. Then Spec admits an input-enabled, non-suppressing implementation iff for all H ⊑ H' and all o ∈ Obs(H), there exists o' ∈ Obs(H') with o ⪯ o'.

Then separately:

Residual corollary. Given a coordination mechanism C that restricts histories to H_C, no further coordination is required downstream iff the residual specification Spec|C is monotone over H_C.

This gives you a clean place to put Paxos/logs, stratified Datalog after sealing, serializable schedulers, etc.

⸻

Bottom line

The paper has a very good conceptual core, and I think the “residual monotonicity after coordination” story is genuinely worth pursuing for PODS. But I would not submit this version as-is. The current draft’s strongest claims rest on definitions that are not yet tight enough, and the invalid future-extension in the running example is a serious red flag.

The best path is to reduce the scope of what must be proved, make observable commitments precise, and turn the coordination-layer separation into the central formal contribution. If that core becomes airtight, the paper can land as a strong conceptual unification of CALM, HAT/I-confluence, CRDTs, and log-based architectures.