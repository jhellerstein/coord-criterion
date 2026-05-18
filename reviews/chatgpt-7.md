I reviewed the revised main.tex. This is definitely moving in the right direction: the paper now has a clearer title, a less grandiose opening frame, a better “proper coordination” section, and a more explicit attempt to connect the semantic theorem to operational CAP. But several high-risk issues remain. Some are conceptual, and some are concrete fix-before-submit problems.

One note: the current uploaded file is available and I reviewed that. Some older uploaded files in the conversation have expired, so I can only compare against what is in this current main.tex and the text visible in the chat history.

Overall assessment

The draft’s strongest contribution is now very clear:

CALM is not fundamentally about Datalog or set inclusion. It is about whether outcomes admitted at a history remain refinable along all causal futures.

That is a strong idea. The paper is also better at saying why this matters: it separates coordination-freedom from replica convergence, supports prefix/lattice/causal orders, and lets you analyze properly coordinated variants.

The main danger is that the paper still tries to carry too many ambitious corollaries at once: Complete CALM, Complete CAP, coordination-free ceiling, register/queue/search ceilings, CALM hierarchy, HAT, I-confluence, CRDTs, proper coordination, replica consistency. Several of those are currently only sketches, and a PODS reviewer will likely attack the weakest one.

My recommendation: keep the paper’s core theorem and proper-coordination story, but either harden or demote the CAP and ceiling claims. They are interesting, but currently they are the highest-risk parts.

⸻

Biggest remaining issues

1. The implementation model is still not quite coherent

The current Implementation definition introduces:

\Expose_I : \Hist \to O

and

\Expose_I^*(H) = \{\Expose_I(H') : H' \hext H,\; H' \in \mathcal{R}_I\}.

But \mathcal{R}_I is indexed by input history:

\mathcal{R}_I(H_{\mathit{in}})

So H' \in \mathcal{R}_I is ill-defined in multiple places. Same issue appears in downward closure:

if H \in \mathcal{R}_I and H' \hext H then H' \in \mathcal{R}_I

You need to either make R_I global or carry the input-history index everywhere.

More importantly, Expose_I^* only grows by set inclusion because it is defined as all prior exposures. That makes irretractability automatic for any Expose_I, independent of semantic refinement. The actual semantic non-retraction condition is not merely:

\Expose_I^*(H_1) \subseteq \Expose_I^*(H_2)

but something like:

every previously exposed outcome must remain compatible with the current/future exposed outcome.

Right now, the theorem’s proof relies on future-consistency, but the implementation definition’s irretractability condition does not encode compatibility under \Ord; it only says old exposures remain in the accumulated set. That means the “physical growth” and “semantic refinement” story is in the prose, not in the implementation definition.

A cleaner model would be:

For all realizable H1 \hext H2 and all o1 in Expose_I(H1),
there exists o2 in Expose_I(H2) such that o1 \Ord o2.

or, if Expose_I is a single outcome:

\Expose_I(H1) \Ord \Expose_I(H2).

If you want accumulated observations, define validity of an accumulated exposure set:

S is compatible with H iff for every o in S, there exists o' in Obs(H)
with o \Ord o'.

Then irretractability plus correctness can be stated meaningfully.

As written, the implementation machinery feels more complicated than the theorem needs, and it gives reviewers a target.

2. Coordination-free implementation is still mostly a property of the spec

The definition says I is coordination-free if:

1. it realizes all admissible histories; and
2. every o ∈ Obs(H) is future-consistent.

Condition (ii) no longer depends on I at all. That makes the theorem close to definitional:

A spec admits a coordination-free implementation iff every outcome is future-consistent iff the spec is monotone.

This is not fatal; you now frame it as an axiomatic lift. But I would be explicit:

The implementation object is used only to express history suppression. Outcome suppression is a property of the specification/interface: if any admitted outcome is future-inconsistent, an implementation must refine the interface by withholding it.

That would make the theorem feel intentional rather than accidentally tautological.

Alternatively, rename the main theorem as a characterization of coordination-free specifications/interfaces, not implementations. Then define implementations as witnesses later.

3. The running register witness is improved but still fragile

The causal consistency vs sequential consistency example is much better than the earlier linearizability version. But there is still a modeling issue.

At H_1, the read is pending. Under SC you admit the outcome:

{(r -> 0, w(1))}

That means Obs(H) includes return values for operations whose response has not yet happened. You do say this in the specification section:

including return values for operations whose invocation is present but whose response is not yet.

Good. But the running example should say this directly, because it is nonstandard and central to the witness.

Otherwise a reviewer will say:

If the read has not returned at H_1, why is r -> 0 an observable outcome at H_1?

The answer is: because Obs(H) represents outcomes the implementation may commit to now, including available responses to pending invocations. That is a good answer, but it needs to be front-and-center in the example.

Suggested edit near the witness:

At H_1, the read invocation is pending. Since Obs(H) records response commitments that an implementation may make at H, SC admits the commitment r -> 0 ordered before the concurrent write.

That will prevent confusion.

4. There is a concrete inconsistency in Example: Extending H1 to H2

In the running example and Example~\ref{ex:h1-formal}, H_1 already contains send(w) in flight.

But Example~\ref{ex:h2-formal} says:

Extend H_1 by adding a send event \mathit{send}(w) ...

That is wrong. H_2 should add the matching receive and response, not the send. Fix this.

5. The SC witness notation has a mismatch

In the running example, H_2 adds:

r -> 1

But the SC non-monotonicity paragraph then says:

H_2 is a future of H_1 whose happens-before includes (w(1), r -> 0).

That should presumably be (w(1), r -> 1), unless you are considering the future where the implementation exposed r -> 0 but the history later forces r -> 1. The current wording mixes the actual response in H_2 with the earlier exposed commitment.

The intended argument is probably:

* o_{H1} commits to r -> 0 before w;
* in future H2, the read is causally after the write and returns/should return 1;
* any SC outcome at H2 must order w before r;
* no prefix extension of r -> 0 < w can satisfy that.

But the text should avoid saying the future’s happens-before includes w -> r0 if the event in H2 is r -> 1.

One way to clean this up is to separate the operation identity from the return commitment:

r[0] and r[1] are alternative response commitments for the same read invocation r.

Then say H_2 contains the commitment/response r[1], not r[0].

6. The CAP corollary is still too strong

The main text still states:

A specification admits a consistent, available, partition-tolerant
distributed implementation iff it is monotone.

This remains too sweeping.

Your appendix formalization introduces cross-partition witnesses, which is exactly the right move. But the corollary still says iff monotone, while the proof begins:

Let o ∈ Obs(H1) be cross-partition under P…

That proves a CAP-style impossibility only for specs with a cross-partition future-inconsistent witness. Non-monotonicity alone does not imply such a witness. Some non-monotonicity is local, same-partition, or caused by thread interleavings rather than network separation.

So the main corollary should be weakened to something like:

A distributed specification with a cross-partition future-inconsistent outcome cannot have an implementation that is both correct and maximally available under that partition pattern. Monotone specifications have no such witnesses and therefore avoid this CAP-style dilemma.

This is still strong and much more defensible.

The title “Complete CAP” is risky unless the theorem is exactly scoped. Maybe call it:

* “A CAP corollary”
* “CAP as cross-partition non-monotonicity”
* “CAP-style unavailability from future-inconsistency”

If you keep “Complete CAP,” reviewers will expect a very careful formal comparison to Gilbert–Lynch availability/atomicity. Right now it is not that.

Also, there is still a duplicate label:

\label{cor:cap}

appears twice.

7. There is still an orphan proof block after the CAP corollary

After the main-text CAP discussion, there is a standalone:

\begin{proof}
  We exhibit a concrete witness for item~(2).
  ...
\end{proof}

This is not attached to any theorem and refers to “item~(2)” with no local referent. It is clearly leftover from an older separation proof.

Delete it or move it under the relevant theorem. This is a must-fix.

8. I-confluence still conflicts with the nonempty Obs definition

Definition of specification says:

Obs : Hist -> P(O) maps each history to a nonempty set

But I-confluence says:

Obs_I(H) = emptyset otherwise

This is still inconsistent.

You should revise the core definition to allow empty observation sets:

Obs(H) may be empty; empty means no correct outcome is admitted at H.

Then state:

A specification is total if Obs(H) is nonempty for all H; safety specs may be partial.

Complete CALM still works with minor changes. In fact, the empty-set case is natural: a future from nonempty Obs(H1) to empty Obs(H2) is a monotonicity failure.

Also, the proof direction labels in I-confluence remain reversed:

(\Rightarrow): If T is I-confluent ...
(\Leftarrow): If T is not I-confluent ...

Given the proposition is Spec_I is monotone iff T is I-confluent, this is confusing. Use prose labels:

I-confluence => monotonicity.
Failure of I-confluence => failure of monotonicity.

9. The coordination-free ceiling proposition still has a serious order-theoretic problem

This section is exciting, but the proposition is not correct as written.

You define:

o1 rightsquigarrow o2 iff there exist H1 \hext H2
with o1 in Obs(H1) and o2 in Obs(H2).

Then claim:

If (E, Obs, Ord') is monotone, then for every o1 rightsquigarrow o2,
monotonicity gives o1 Ord' o2.

That does not follow.

Monotonicity says:

for every o1 ∈ Obs(H1), there exists some o2' ∈ Obs(H2) such that o1 Ord' o2'.

It does not say o1 Ord' o2 for every o2 ∈ Obs(H2).

Your rightsquigarrow relation includes all pairs of prefix/future outcomes, but monotonicity only requires at least one refining future outcome. So Ord^* as defined is too large/coarse, and the minimality proof fails.

This is the most important technical issue in the ceiling section.

To fix it, you need a more careful construction. There are two possible paths:

Path A: Universal future compatibility

If you want “every possible future outcome must be compatible,” then define monotonicity universally:

\[
\forall H_1 \hext H_2,\ \forall o_1 \in Obs(H_1),\ \forall o_2 \in Obs(H_2): o_1 \preceq o_2
\]

But that is stronger than your main theorem and likely too strong.

Path B: Choice-based closure

If you keep existential monotonicity, the “least monotone enlargement” is not simply all possible transitions. It is more like a hitting/choice problem:

For each obligation (H1,H2,o1), choose at least one o2 ∈ Obs(H2) to add as a refinement. The minimal monotone preorder may not be unique.

This means the claim of a unique coordination-free ceiling is not automatic. You may need to define the ceiling as the intersection or union of all monotone orders and check whether that preserves monotonicity. In general, intersections of monotone orders may fail monotonicity because existential witnesses may differ across orders.

That is a major complication.

Given this, I would not present the ceiling construction as a proven main contribution unless you fix the math. For this submission, I would demote it to a conjectural/illustrative appendix or restrict it to deterministic/singleton Obs(H) settings where the construction works.

In singleton-output specs, the construction is much simpler:

Obs(H) = {o_H}

Then monotonicity requires o_H1 <= o_H2, and the forced order is clear. But for nondeterministic/multiple-outcome specs, the existential witness issue matters.

10. The “coarsest order = strongest guarantee” language is confusing

The ceiling section says:

“the strongest guarantee achievable without coordination”
“the coarsest order under which the specification is monotone”

Usually a coarser order is a weaker guarantee, because it treats more outcome transitions as compatible. A finer order is stronger.

You later say:

pairs in Ord^* but not in Ord represent transitions the client considers incompatible but that the system cannot prevent without coordination.

This suggests Ord^* is a weakening/enlargement of the desired order. So it is the weakest relaxation or least weakening needed for coordination-freedom, not straightforwardly the “strongest guarantee” unless you carefully order guarantees by reverse inclusion.

I would rewrite this section with explicit terminology:

If Ord_1 \subseteq Ord_2, then Ord_1 is stricter/finer/stronger.
A monotone relaxation of Ord is any Ord' \supseteq Ord that is monotone.
The coordination-free frontier is a minimal such relaxation, if it exists.

Then avoid “coarsest” unless you define exactly what you mean.

11. Register/queue/search ceilings currently depend on the flawed ceiling proposition

The examples are compelling, but because the general ceiling theorem is shaky, these examples inherit risk.

Register ceiling

The proposition says:

Ord^* = Ord_causal

But in the register subsection, Obs_causal changes the observation function, not just the order. The ceiling proposition was stated for fixed (E, Obs) and varying Ord. Here you appear to change from SC observations to causal observations.

That is a mismatch. Decide whether the ceiling varies:

1. only the outcome order, holding Obs fixed; or
2. both Obs and Ord, deriving a weaker spec.

The text currently does both.

Also, Obs_causal says a read returns a value with w(v) in past(r,H). What about the initial value? Model it as an initial write in every read’s causal past or explicitly allow v=0.

Queue ceiling

The causal FIFO result is interesting but underproved. The “maximality” proof assumes any finer order imposes a global preference between concurrent enqueues. That is not generally true. A finer order might distinguish some histories/outcomes without imposing a universal a before b.

This needs either a much more formal lattice/order argument or should be presented as an illustrative conjecture.

Search ceiling

This is the most speculative. It is a good systems insight, but the formal proposition is not yet PODS-ready. The proof assumes structural modifications only add forwarding reachability; real search structures also delete links, merge nodes, reclaim memory, etc. If the link invariant is strong enough, state it as a monotonicity lemma, not as a full “ceiling” theorem.

I would keep search structures as a motivating example, not a theorem, unless you formalize the structure graph transition system carefully.

12. The separation from relational-transducer CALM still overstates

The theorem says:

relational-transducer CALM cannot certify

The proof sketch says any Datalog encoding of SC requires a non-monotone uniqueness constraint. But later the proposition only says prefix extension requires negation in a Datalog encoding. That supports the point, but “cannot certify” is still broad.

Classic CALM can certify monotone consumers of an already serialized log if the log is modeled as append-only input facts. What it lacks is your semantic ability to identify the properly coordinated variant directly at the specification boundary.

So I would rephrase:

Relational-transducer CALM cannot certify this at the same semantic boundary without encoding the coordination mechanism and output interface as a Datalog program; such encodings obscure the monotone residual interface.

Less punchy, but safer.

13. The replica consistency section is good, but the join claim is too quick

This is a nice section and worth keeping. But:

“if Ord admits joins, monotonicity implies convergence”

Existence of joins alone does not imply convergence. You also need the implementation to exchange outcomes and merge by join, and you need fairness/eventual delivery if you want eventual convergence.

Better:

If Ord admits joins and replicas exchange and merge observations by join under eventual delivery, then monotonicity supports convergence. Without joins, monotonicity gives safe independent observations but not necessarily replica agreement.

That aligns with CRDTs and avoids overclaiming.

14. The HAT section should be scoped more carefully

This section is mostly fine as a proof sketch, but the paper still says it “recovers the HAT/non-HAT boundary.” You only prove representative cases: RU, RC, session guarantees, and serializability. Snapshot isolation is mentioned but omitted.

I would write:

We recover representative HAT/non-HAT separations.

or:

We show how the HAT boundary can be recovered; full enumeration follows the same pattern.

If you claim the full boundary, include the full table.

Also, the serializability witness relies on the assumption that outcomes at H_2 must include all committed transactions and observed reads. State this explicitly in the spec sketch.

⸻

Concrete fix-before-submit checklist

These are the things I would definitely fix before sending to reviewers.

1. Fix duplicate label: cor:cap appears twice.
2. Delete or move the orphan proof block after the main CAP corollary.
3. Fix R_I indexing throughout Implementation and Expose_I^*.
4. Fix H_2 example adding send(w) twice.
5. Clarify pending-response commitments in the running example.
6. Fix r -> 0 vs r -> 1 mismatch in the SC witness.
7. Allow empty Obs or change I-confluence encoding.
8. Fix I-confluence proof direction labels.
9. Weaken Complete CAP to cross-partition non-monotonicity.
10. Either repair or demote the ceiling theorem, because the current proof of minimality is not valid under existential monotonicity.
11. Clarify whether the frontier varies only Ord or also Obs.
12. Soften claims that relational-transducer CALM “cannot” certify residual interfaces.
13. Qualify replica convergence with join-merge plus eventual delivery.

⸻

Suggested strategic restructuring

I would consider moving the ceiling section out of the main contribution list unless fixed. Right now it creates the largest technical vulnerability.

A stronger, lower-risk PODS structure would be:

1. Complete CALM theorem over histories/outcomes/orders.
2. Proper coordination as monotone restriction/residualization.
3. CALM as an instance.
4. Applications: CRDTs, I-confluence, HAT/sequential consistency.
5. CAP-style corollary for cross-partition witnesses.
6. Appendix: exploratory coordination-free frontier, with register as the main example and queue/search as sketches.

This version would still be ambitious but less brittle.

⸻

Bottom line

This revision improves the paper’s positioning and narrative, but it has not yet eliminated the main technical risks. The biggest unresolved issue is now the coordination-free ceiling: as written, the proposition is not correct under the paper’s existential monotonicity definition. The second-biggest issue is Complete CAP, which still needs to be scoped to cross-partition witnesses rather than all non-monotone specifications.

The core Complete CALM idea is strong and worth protecting. I would not let the ceiling/CAP material overexpose the submission unless you can formalize it cleanly.I reviewed the revised main.tex. This is definitely moving in the right direction: the paper now has a clearer title, a less grandiose opening frame, a better “proper coordination” section, and a more explicit attempt to connect the semantic theorem to operational CAP. But several high-risk issues remain. Some are conceptual, and some are concrete fix-before-submit problems.

One note: the current uploaded file is available and I reviewed that. Some older uploaded files in the conversation have expired, so I can only compare against what is in this current main.tex and the text visible in the chat history.

Overall assessment

The draft’s strongest contribution is now very clear:

CALM is not fundamentally about Datalog or set inclusion. It is about whether outcomes admitted at a history remain refinable along all causal futures.

That is a strong idea. The paper is also better at saying why this matters: it separates coordination-freedom from replica convergence, supports prefix/lattice/causal orders, and lets you analyze properly coordinated variants.

The main danger is that the paper still tries to carry too many ambitious corollaries at once: Complete CALM, Complete CAP, coordination-free ceiling, register/queue/search ceilings, CALM hierarchy, HAT, I-confluence, CRDTs, proper coordination, replica consistency. Several of those are currently only sketches, and a PODS reviewer will likely attack the weakest one.

My recommendation: keep the paper’s core theorem and proper-coordination story, but either harden or demote the CAP and ceiling claims. They are interesting, but currently they are the highest-risk parts.

⸻

Biggest remaining issues

1. The implementation model is still not quite coherent

The current Implementation definition introduces:

\Expose_I : \Hist \to O

and

\Expose_I^*(H) = \{\Expose_I(H') : H' \hext H,\; H' \in \mathcal{R}_I\}.

But \mathcal{R}_I is indexed by input history:

\mathcal{R}_I(H_{\mathit{in}})

So H' \in \mathcal{R}_I is ill-defined in multiple places. Same issue appears in downward closure:

if H \in \mathcal{R}_I and H' \hext H then H' \in \mathcal{R}_I

You need to either make R_I global or carry the input-history index everywhere.

More importantly, Expose_I^* only grows by set inclusion because it is defined as all prior exposures. That makes irretractability automatic for any Expose_I, independent of semantic refinement. The actual semantic non-retraction condition is not merely:

\Expose_I^*(H_1) \subseteq \Expose_I^*(H_2)

but something like:

every previously exposed outcome must remain compatible with the current/future exposed outcome.

Right now, the theorem’s proof relies on future-consistency, but the implementation definition’s irretractability condition does not encode compatibility under \Ord; it only says old exposures remain in the accumulated set. That means the “physical growth” and “semantic refinement” story is in the prose, not in the implementation definition.

A cleaner model would be:

For all realizable H1 \hext H2 and all o1 in Expose_I(H1),
there exists o2 in Expose_I(H2) such that o1 \Ord o2.

or, if Expose_I is a single outcome:

\Expose_I(H1) \Ord \Expose_I(H2).

If you want accumulated observations, define validity of an accumulated exposure set:

S is compatible with H iff for every o in S, there exists o' in Obs(H)
with o \Ord o'.

Then irretractability plus correctness can be stated meaningfully.

As written, the implementation machinery feels more complicated than the theorem needs, and it gives reviewers a target.

2. Coordination-free implementation is still mostly a property of the spec

The definition says I is coordination-free if:

1. it realizes all admissible histories; and
2. every o ∈ Obs(H) is future-consistent.

Condition (ii) no longer depends on I at all. That makes the theorem close to definitional:

A spec admits a coordination-free implementation iff every outcome is future-consistent iff the spec is monotone.

This is not fatal; you now frame it as an axiomatic lift. But I would be explicit:

The implementation object is used only to express history suppression. Outcome suppression is a property of the specification/interface: if any admitted outcome is future-inconsistent, an implementation must refine the interface by withholding it.

That would make the theorem feel intentional rather than accidentally tautological.

Alternatively, rename the main theorem as a characterization of coordination-free specifications/interfaces, not implementations. Then define implementations as witnesses later.

3. The running register witness is improved but still fragile

The causal consistency vs sequential consistency example is much better than the earlier linearizability version. But there is still a modeling issue.

At H_1, the read is pending. Under SC you admit the outcome:

{(r -> 0, w(1))}

That means Obs(H) includes return values for operations whose response has not yet happened. You do say this in the specification section:

including return values for operations whose invocation is present but whose response is not yet.

Good. But the running example should say this directly, because it is nonstandard and central to the witness.

Otherwise a reviewer will say:

If the read has not returned at H_1, why is r -> 0 an observable outcome at H_1?

The answer is: because Obs(H) represents outcomes the implementation may commit to now, including available responses to pending invocations. That is a good answer, but it needs to be front-and-center in the example.

Suggested edit near the witness:

At H_1, the read invocation is pending. Since Obs(H) records response commitments that an implementation may make at H, SC admits the commitment r -> 0 ordered before the concurrent write.

That will prevent confusion.

4. There is a concrete inconsistency in Example: Extending H1 to H2

In the running example and Example~\ref{ex:h1-formal}, H_1 already contains send(w) in flight.

But Example~\ref{ex:h2-formal} says:

Extend H_1 by adding a send event \mathit{send}(w) ...

That is wrong. H_2 should add the matching receive and response, not the send. Fix this.

5. The SC witness notation has a mismatch

In the running example, H_2 adds:

r -> 1

But the SC non-monotonicity paragraph then says:

H_2 is a future of H_1 whose happens-before includes (w(1), r -> 0).

That should presumably be (w(1), r -> 1), unless you are considering the future where the implementation exposed r -> 0 but the history later forces r -> 1. The current wording mixes the actual response in H_2 with the earlier exposed commitment.

The intended argument is probably:

* o_{H1} commits to r -> 0 before w;
* in future H2, the read is causally after the write and returns/should return 1;
* any SC outcome at H2 must order w before r;
* no prefix extension of r -> 0 < w can satisfy that.

But the text should avoid saying the future’s happens-before includes w -> r0 if the event in H2 is r -> 1.

One way to clean this up is to separate the operation identity from the return commitment:

r[0] and r[1] are alternative response commitments for the same read invocation r.

Then say H_2 contains the commitment/response r[1], not r[0].

6. The CAP corollary is still too strong

The main text still states:

A specification admits a consistent, available, partition-tolerant
distributed implementation iff it is monotone.

This remains too sweeping.

Your appendix formalization introduces cross-partition witnesses, which is exactly the right move. But the corollary still says iff monotone, while the proof begins:

Let o ∈ Obs(H1) be cross-partition under P…

That proves a CAP-style impossibility only for specs with a cross-partition future-inconsistent witness. Non-monotonicity alone does not imply such a witness. Some non-monotonicity is local, same-partition, or caused by thread interleavings rather than network separation.

So the main corollary should be weakened to something like:

A distributed specification with a cross-partition future-inconsistent outcome cannot have an implementation that is both correct and maximally available under that partition pattern. Monotone specifications have no such witnesses and therefore avoid this CAP-style dilemma.

This is still strong and much more defensible.

The title “Complete CAP” is risky unless the theorem is exactly scoped. Maybe call it:

* “A CAP corollary”
* “CAP as cross-partition non-monotonicity”
* “CAP-style unavailability from future-inconsistency”

If you keep “Complete CAP,” reviewers will expect a very careful formal comparison to Gilbert–Lynch availability/atomicity. Right now it is not that.

Also, there is still a duplicate label:

\label{cor:cap}

appears twice.

7. There is still an orphan proof block after the CAP corollary

After the main-text CAP discussion, there is a standalone:

\begin{proof}
  We exhibit a concrete witness for item~(2).
  ...
\end{proof}

This is not attached to any theorem and refers to “item~(2)” with no local referent. It is clearly leftover from an older separation proof.

Delete it or move it under the relevant theorem. This is a must-fix.

8. I-confluence still conflicts with the nonempty Obs definition

Definition of specification says:

Obs : Hist -> P(O) maps each history to a nonempty set

But I-confluence says:

Obs_I(H) = emptyset otherwise

This is still inconsistent.

You should revise the core definition to allow empty observation sets:

Obs(H) may be empty; empty means no correct outcome is admitted at H.

Then state:

A specification is total if Obs(H) is nonempty for all H; safety specs may be partial.

Complete CALM still works with minor changes. In fact, the empty-set case is natural: a future from nonempty Obs(H1) to empty Obs(H2) is a monotonicity failure.

Also, the proof direction labels in I-confluence remain reversed:

(\Rightarrow): If T is I-confluent ...
(\Leftarrow): If T is not I-confluent ...

Given the proposition is Spec_I is monotone iff T is I-confluent, this is confusing. Use prose labels:

I-confluence => monotonicity.
Failure of I-confluence => failure of monotonicity.

9. The coordination-free ceiling proposition still has a serious order-theoretic problem

This section is exciting, but the proposition is not correct as written.

You define:

o1 rightsquigarrow o2 iff there exist H1 \hext H2
with o1 in Obs(H1) and o2 in Obs(H2).

Then claim:

If (E, Obs, Ord') is monotone, then for every o1 rightsquigarrow o2,
monotonicity gives o1 Ord' o2.

That does not follow.

Monotonicity says:

for every o1 ∈ Obs(H1), there exists some o2' ∈ Obs(H2) such that o1 Ord' o2'.

It does not say o1 Ord' o2 for every o2 ∈ Obs(H2).

Your rightsquigarrow relation includes all pairs of prefix/future outcomes, but monotonicity only requires at least one refining future outcome. So Ord^* as defined is too large/coarse, and the minimality proof fails.

This is the most important technical issue in the ceiling section.

To fix it, you need a more careful construction. There are two possible paths:

Path A: Universal future compatibility

If you want “every possible future outcome must be compatible,” then define monotonicity universally:

\[
\forall H_1 \hext H_2,\ \forall o_1 \in Obs(H_1),\ \forall o_2 \in Obs(H_2): o_1 \preceq o_2
\]

But that is stronger than your main theorem and likely too strong.

Path B: Choice-based closure

If you keep existential monotonicity, the “least monotone enlargement” is not simply all possible transitions. It is more like a hitting/choice problem:

For each obligation (H1,H2,o1), choose at least one o2 ∈ Obs(H2) to add as a refinement. The minimal monotone preorder may not be unique.

This means the claim of a unique coordination-free ceiling is not automatic. You may need to define the ceiling as the intersection or union of all monotone orders and check whether that preserves monotonicity. In general, intersections of monotone orders may fail monotonicity because existential witnesses may differ across orders.

That is a major complication.

Given this, I would not present the ceiling construction as a proven main contribution unless you fix the math. For this submission, I would demote it to a conjectural/illustrative appendix or restrict it to deterministic/singleton Obs(H) settings where the construction works.

In singleton-output specs, the construction is much simpler:

Obs(H) = {o_H}

Then monotonicity requires o_H1 <= o_H2, and the forced order is clear. But for nondeterministic/multiple-outcome specs, the existential witness issue matters.

10. The “coarsest order = strongest guarantee” language is confusing

The ceiling section says:

“the strongest guarantee achievable without coordination”
“the coarsest order under which the specification is monotone”

Usually a coarser order is a weaker guarantee, because it treats more outcome transitions as compatible. A finer order is stronger.

You later say:

pairs in Ord^* but not in Ord represent transitions the client considers incompatible but that the system cannot prevent without coordination.

This suggests Ord^* is a weakening/enlargement of the desired order. So it is the weakest relaxation or least weakening needed for coordination-freedom, not straightforwardly the “strongest guarantee” unless you carefully order guarantees by reverse inclusion.

I would rewrite this section with explicit terminology:

If Ord_1 \subseteq Ord_2, then Ord_1 is stricter/finer/stronger.
A monotone relaxation of Ord is any Ord' \supseteq Ord that is monotone.
The coordination-free frontier is a minimal such relaxation, if it exists.

Then avoid “coarsest” unless you define exactly what you mean.

11. Register/queue/search ceilings currently depend on the flawed ceiling proposition

The examples are compelling, but because the general ceiling theorem is shaky, these examples inherit risk.

Register ceiling

The proposition says:

Ord^* = Ord_causal

But in the register subsection, Obs_causal changes the observation function, not just the order. The ceiling proposition was stated for fixed (E, Obs) and varying Ord. Here you appear to change from SC observations to causal observations.

That is a mismatch. Decide whether the ceiling varies:

1. only the outcome order, holding Obs fixed; or
2. both Obs and Ord, deriving a weaker spec.

The text currently does both.

Also, Obs_causal says a read returns a value with w(v) in past(r,H). What about the initial value? Model it as an initial write in every read’s causal past or explicitly allow v=0.

Queue ceiling

The causal FIFO result is interesting but underproved. The “maximality” proof assumes any finer order imposes a global preference between concurrent enqueues. That is not generally true. A finer order might distinguish some histories/outcomes without imposing a universal a before b.

This needs either a much more formal lattice/order argument or should be presented as an illustrative conjecture.

Search ceiling

This is the most speculative. It is a good systems insight, but the formal proposition is not yet PODS-ready. The proof assumes structural modifications only add forwarding reachability; real search structures also delete links, merge nodes, reclaim memory, etc. If the link invariant is strong enough, state it as a monotonicity lemma, not as a full “ceiling” theorem.

I would keep search structures as a motivating example, not a theorem, unless you formalize the structure graph transition system carefully.

12. The separation from relational-transducer CALM still overstates

The theorem says:

relational-transducer CALM cannot certify

The proof sketch says any Datalog encoding of SC requires a non-monotone uniqueness constraint. But later the proposition only says prefix extension requires negation in a Datalog encoding. That supports the point, but “cannot certify” is still broad.

Classic CALM can certify monotone consumers of an already serialized log if the log is modeled as append-only input facts. What it lacks is your semantic ability to identify the properly coordinated variant directly at the specification boundary.

So I would rephrase:

Relational-transducer CALM cannot certify this at the same semantic boundary without encoding the coordination mechanism and output interface as a Datalog program; such encodings obscure the monotone residual interface.

Less punchy, but safer.

13. The replica consistency section is good, but the join claim is too quick

This is a nice section and worth keeping. But:

“if Ord admits joins, monotonicity implies convergence”

Existence of joins alone does not imply convergence. You also need the implementation to exchange outcomes and merge by join, and you need fairness/eventual delivery if you want eventual convergence.

Better:

If Ord admits joins and replicas exchange and merge observations by join under eventual delivery, then monotonicity supports convergence. Without joins, monotonicity gives safe independent observations but not necessarily replica agreement.

That aligns with CRDTs and avoids overclaiming.

14. The HAT section should be scoped more carefully

This section is mostly fine as a proof sketch, but the paper still says it “recovers the HAT/non-HAT boundary.” You only prove representative cases: RU, RC, session guarantees, and serializability. Snapshot isolation is mentioned but omitted.

I would write:

We recover representative HAT/non-HAT separations.

or:

We show how the HAT boundary can be recovered; full enumeration follows the same pattern.

If you claim the full boundary, include the full table.

Also, the serializability witness relies on the assumption that outcomes at H_2 must include all committed transactions and observed reads. State this explicitly in the spec sketch.

⸻

Concrete fix-before-submit checklist

These are the things I would definitely fix before sending to reviewers.

1. Fix duplicate label: cor:cap appears twice.
2. Delete or move the orphan proof block after the main CAP corollary.
3. Fix R_I indexing throughout Implementation and Expose_I^*.
4. Fix H_2 example adding send(w) twice.
5. Clarify pending-response commitments in the running example.
6. Fix r -> 0 vs r -> 1 mismatch in the SC witness.
7. Allow empty Obs or change I-confluence encoding.
8. Fix I-confluence proof direction labels.
9. Weaken Complete CAP to cross-partition non-monotonicity.
10. Either repair or demote the ceiling theorem, because the current proof of minimality is not valid under existential monotonicity.
11. Clarify whether the frontier varies only Ord or also Obs.
12. Soften claims that relational-transducer CALM “cannot” certify residual interfaces.
13. Qualify replica convergence with join-merge plus eventual delivery.

⸻

Suggested strategic restructuring

I would consider moving the ceiling section out of the main contribution list unless fixed. Right now it creates the largest technical vulnerability.

A stronger, lower-risk PODS structure would be:

1. Complete CALM theorem over histories/outcomes/orders.
2. Proper coordination as monotone restriction/residualization.
3. CALM as an instance.
4. Applications: CRDTs, I-confluence, HAT/sequential consistency.
5. CAP-style corollary for cross-partition witnesses.
6. Appendix: exploratory coordination-free frontier, with register as the main example and queue/search as sketches.

This version would still be ambitious but less brittle.

⸻

Bottom line

This revision improves the paper’s positioning and narrative, but it has not yet eliminated the main technical risks. The biggest unresolved issue is now the coordination-free ceiling: as written, the proposition is not correct under the paper’s existential monotonicity definition. The second-biggest issue is Complete CAP, which still needs to be scoped to cross-partition witnesses rather than all non-monotone specifications.

The core Complete CALM idea is strong and worth protecting. I would not let the ceiling/CAP material overexpose the submission unless you can formalize it cleanly.