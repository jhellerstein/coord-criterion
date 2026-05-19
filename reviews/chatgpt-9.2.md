I read the attached main.tex directly and checked the specific areas you flagged. You are right on two important meta-points: the old “orphan proof block” is not present in this file, and the CAP discussion has indeed been substantially revised rather than left in the earlier state. I also checked for duplicate labels and undefined \refs; I did not find duplicate labels or undefined refs in the LaTeX source.

My judgment: the strategy mostly worked for the core paper, but I would not yet consider the strengthened Complete CAP proof fully safe. The issue is narrower now, but still real.

P0 / P1 — Most pressing

1. Complete CAP: the proof now states the missing step, but the step is too strong

The current CAP proof explicitly argues:

In the asynchronous model with \geq 2 processes, the specification
does not constrain which process generates these events: any event
may occur at any process.

This is the crucial move. It is what lets you preserve the memorable iff:

consistent + available + partition-tolerant iff monotone

But I do not think this assumption is justified by the framework as currently defined.

Earlier, the framework says a specification fixes an event universe. In examples, events are often already process-labeled: reads at node q, writes at node p, sends from p to q, receives at q, transaction invocations at replicas, etc. For such specifications, it is not generally true that “any event may occur at any process.” The location of an event may be semantically meaningful.

So the strengthened proof closes the gap only under an additional symmetry/relocatability assumption:

non-monotonicity witnesses can be realized with the deciding/exposing process separated by a partition from the events needed to rule out the dangerous future.

That is plausible for many distributed objects, but it is not true for every specification in the current model.

A safer way to keep the strong CAP result is to make the assumption explicit. For example:

Call a distributed specification process-parametric if every
non-monotonicity witness can be realized under an isomorphic assignment
of the distinguishing events to a remote process. For process-parametric
asynchronous specifications with at least two processes, CAP vulnerability
coincides with non-monotonicity.

Then the corollary can remain strong in that class:

For process-parametric asynchronous specifications, consistent,
maximally available, partition-tolerant implementation exists iff the
specification is monotone.

If you want the unqualified “Complete CAP” statement, you need to bake process-parametricity into the model earlier. Otherwise, a reviewer can object with a local/single-shard/same-process non-monotonicity witness.

2. The CAP availability definition is existential and may be weaker than reviewers expect

The appendix defines maximal availability as:

whenever some H in Ext_P(H_i) both completes a client invocation e
and admits nonempty Obs(H), there exists an execution H^* ... in which e
completes.

This is an existential availability condition: some implementation execution completes the operation. CAP-style availability is usually closer to “every request to a non-failing node eventually receives a response,” i.e. universal over executions/fair schedules, not merely existence of one completing execution.

This may be fine for your semantic framework, but you should say it is a “may-complete” or “maximal availability” abstraction. Otherwise a reviewer may say the CAP corollary is not about CAP availability as usually stated.

Suggested patch:

Our availability notion is semantic and permissive: if any partition-respecting extension admits a valid response, an available implementation must have a partition-respecting execution that produces one. Stronger universal/fairness-based availability notions only strengthen the impossibility direction.

That would defuse the mismatch.

3. Running example: the CC fix is present, but the “decision time” model still needs one formal sentence

You did add the key sentence:

a response commitment is evaluated against the causal past at decision time

That addresses my previous concern in spirit. But the formal objects still make r ambiguous: sometimes r is an invocation, sometimes a pending read operation, sometimes a response commitment.

In the running example, this matters because H_2 has recv(w) before any future response at q, yet the old commitment r -> 0 remains valid because it was made at decision time before the receive.

I would add a short formal convention:

For pending operations, an outcome containing r ↦ v represents a
decision event d_r at the current history, ordered after the invocation
and before any later events. Future response events merely communicate
that already-made decision.

This would make the CC argument crisp: recv(w) in H_2 is after the decision point for the committed r -> 0, so it cannot retroactively enter that decision’s causal past.

Without this, the example is readable but still open to “what exactly is the read event whose causal past is being measured?”

⸻

P1 — Important but not fatal

4. The frontier section is improved, but the abstract/contributions still oversell it

The appendix now clearly defines the formal frontier for fixed E, fixed Obs, and varying Ord. It also says that interface weakenings may change Obs or Ord. That is a good improvement.

But the abstract and contribution list still say things like:

a coordination-free frontier construction that derives natural
coordination-free weakenings for any specification

and

minimal monotone enlargements ... characterize the strongest
coordination-free guarantees

This is true for the fixed-Obs order-frontier definition, but the register example is an interface frontier, not just an order-frontier. The current wording blurs the two.

I would split the claim:

For fixed observation interfaces, minimal monotone enlargements of the refinement order define a coordination-free frontier. More generally, one may weaken the full interface; our register, queue, and search examples illustrate this broader use.

That is enough to keep the idea without making the examples bear a formal burden they do not yet fully discharge.

5. Register frontier statement is much safer now, but the maximality proof still has a “forcing unique extension” leap

You renamed the proposition to “Register interface frontier” and removed the problematic Ord^* = Ord_causal. Good.

The remaining weak spot is this proof sentence:

with causal structure forcing o2 as the unique extension of o1 at H2

That is a nontrivial realizability/uniqueness claim. It might be true under your chosen interface comparison, but it is not established.

If you want to keep maximality, add a lemma or soften:

This shows that causal consistency is a natural frontier point: any
attempt to preserve more of the total-order commitment must rule out
some admissible concurrent extension.

That is less exact but much safer.

6. Queue/search maximality remains the least rigorous part

You softened the propositions somewhat, but the proofs still say things like:

Any order smaller than causal FIFO must declare one of these pairs
incompatible...

and:

Any order smaller than forward-reachability must declare some pair
(k,p) invalid...

Those are still broad claims. There may be intermediate weakenings that remove some refinement edges without imposing the specific incompatibilities you describe.

My advice: keep these as “worked instances” or “natural frontier points,” but avoid claiming full minimality/maximality unless you formalize the interface preorder and prove no intermediate guarantee exists.

For example:

Under the stated assumptions, causal FIFO is a natural monotone weakening on the coordination-free frontier.

is safer than:

no weaker order suffices.

⸻

P2 — Rhetoric / reviewer-risk polish

7. Intro still says “transducer model underlying CALM conflates coordination-freedom with replica consistency”

This line appears in the introduction:

the transducer model underlying CALM conflates coordination-freedom
with replica consistency, leaving causal consistency ... outside its scope.

That is punchy, but possibly too aggressive. A CALM expert may object that the transducer theorem is about query outputs, not replica consistency per se.

Safer:

The transducer formulation ties coordination-freedom to monotone growth of a common output relation; it does not directly express coordination-free but non-convergent interfaces such as causal consistency.

Same idea, less inflammatory.

8. The Datalog prefix proposition is now appropriately softened

I verified this now says:

Standard encodings of prefix extension ...

That is much better than “any encoding.” I would keep it as-is, though I might remove “Full proof in Appendix~\ref{app:hierarchy}” unless the appendix actually contains a full proof of this proposition. In the current file, Appendix app:hierarchy is about the CALM hierarchy, not a full proof of prefix encoding impossibility. If there is no full proof there, that line should be removed or changed to “Discussion appears…”

9. “Complete CAP” can stay, but qualify the theorem title or model

I understand the desire to keep the memorable name. I think it can stay if the theorem statement says:

In the process-parametric asynchronous message-passing model...

or:

For distributed specifications whose witnesses are relocatable across partitions...

That one phrase protects the claim.

⸻

Things that are clearly fixed

I verified these directly in the attached file:

* \Poss macro is gone.
* \rightsquigarrow is gone.
* The orphan proof block I mentioned previously is not present.
* Duplicate labels are not present.
* Empty Obs is now allowed in the definition of specification.
* The CALM instantiation abstracts internal transducer events and uses semantic query output.
* The Hydro sentence has been moved to related work.
* The SC witness is now expressed mostly in ordering language rather than contradictory tuple language.
* The “CALM conflates them” sentence has been replaced in the Paxos example with a more nuanced boundary claim.

Did the new strategy work?

Mostly yes. The core paper is now much more stable. The main theorem and CALM instantiation are in much better shape. The old Poss issue is gone. The paper now reads like a coherent semantic generalization rather than a pile of related claims.

The remaining strategic risk is that you preserved the strongest “Complete CAP iff monotone” statement by adding a relocation argument. That can work, but only if the model explicitly supports relocation of witness events across processes. Right now the paper says it does; the earlier framework does not fully justify it.

So the main remaining revision I would make is small but important:

Add a named assumption for the CAP theorem: process-parametric / location-renamable / partition-relocatable specifications.

Then the CAP result becomes much harder to attack.

Priority summary

Priority	Item	Recommendation
P0	CAP proof assumes events can be reassigned to remote processes	Add explicit process-parametric/relocatable-witness assumption or weaken theorem
P0/P1	Pending read decision time	Add formal convention that outcome commitment introduces a decision point
P1	Frontier examples still overstate maximality	Keep as natural frontier points unless full interface preorder is formalized
P1	Prefix proposition references full proof in wrong appendix	Remove or fix reference
P2	“CALM conflates coordination-freedom with replica consistency”	Soften wording
P2	CAP availability is existential	Note this is a semantic/maximal availability abstraction

Bottom line: the revision worked for the core. I would now focus almost entirely on protecting the CAP theorem and frontier appendix from overclaim objections.