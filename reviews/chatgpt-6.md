I read the uploaded main.tex all the way through. This is a much more ambitious and interesting draft than the pasted version: it now has a stronger “coordination-free ceiling” story, the causal-consistency/register example is more central, and the abstract is sharper. But it also introduces several new high-risk claims and a few concrete technical/LaTeX inconsistencies that I would fix before submitting.

Overall assessment

The strongest version of the paper is now:

Complete CALM lifts CALM from program/query monotonicity to specification-level monotonicity over histories and outcome-refinement orders. This unifies CALM, CRDTs, I-confluence, HAT-style availability, and gives a semantic way to compute or reason about the strongest coordination-free weakening of a specification.

That is a plausible PODS paper.

However, this draft currently overreaches. The new “coordination-free ceiling,” “Complete CAP,” and “new characterizations for registers, queues, and search structures” are exciting, but they make the submission much easier to attack. In its current form, I think a skeptical PODS reviewer could reject it on technical grounds, especially around:

1. the definition/proof of Complete CALM becoming partly tautological;
2. the running SC witness still relying on pending-operation outcomes in a way that needs more care;
3. the “ceiling” construction appearing order-theoretically backward or at least unclearly stated;
4. empty observation sets in I-confluence conflicting with the specification definition;
5. “Complete CAP” being much too strong as stated;
6. several appendix claims that are more suggestive than proved;
7. some concrete LaTeX/proof-structure errors.

The paper is conceptually strong, but I would narrow and harden the claims.

⸻

Major technical issues

1. The implementation model and theorem no longer line up cleanly

The current Implementation definition has an exposure function:

\Expose_I : \Hist \to O

and accumulated exposure:

\Expose_I^*(H) = \{\Expose_I(H') : H' \hext H,\; H' \in \mathcal{R}_I\}

Then Coordination-free implementation says:

(i) R_I(H_in) = A(H_in)
(ii) Every o in Obs(H) is future-consistent at every H

Notice that condition (ii) no longer mentions I or Expose_I. So “coordination-free implementation” is mostly a property of the specification, not the implementation. This makes Theorem 1 nearly definitional:

* monotone iff every outcome is future-consistent;
* coordination-free iff every outcome is future-consistent plus all histories realized.

That may be acceptable if framed as an axiomatization, but the current implementation machinery becomes confusing. The proof even says:

“For any choice Expose_I(H)=o ∈ Obs(H) … setting Expose_I(H')=o' maintains correctness.”

But Expose_I is a single global function. If a history H' is reachable from many different prefixes with different prior exposures, you cannot independently “set” Expose_I(H') to satisfy all branches unless a coherent choice exists. Monotonicity gives an extension for each prior outcome, but not necessarily one single Expose_I(H') refining all previously exposed outcomes.

This is a serious issue.

A simple example: suppose at H1, two outcomes a,b ∈ Obs(H1) are both future-consistent individually, and at H2, a refines to a', b refines to b', but there is no single outcome at H2 refining both. Your definition of coordination-free says every individual outcome is future-consistent, but an implementation exposing different outcomes along different prefixes may need a consistent branch choice. Because Expose_I^* accumulates all exposures, you may need compatibility of the set of accumulated exposures, not just each exposure individually.

You need to decide which model you want:

Option A: Keep exposure as “safe choices,” not actual execution output

Then remove Expose_I : Hist -> O and accumulated exposure from the implementation model. Define coordination-freedom directly as:

no history suppression, and all admissible outcomes are future-consistent.

Then Theorem 1 is an order-theoretic characterization of safe observability, not of concrete implementations.

Option B: Model concrete implementations

Then Expose_I should probably be path-dependent or execution-dependent, not just Hist -> O, and irretractability should require:

\[
\Expose_I(H_1) \preceq \Expose_I(H_2)
\]

for H1 ⊑ H2, not merely set inclusion of accumulated unrelated outcomes. Coordination-free might require that for every allowed choice at H1, there exists some allowed implementation branch that preserves it. That is more complex.

Right now the draft is between these two models.

2. Expose_I^* uses R_I without the input-history index

In the definition:

\Expose_I^*(H) = \{\Expose_I(H') : H' \hext H,\;
H' \in \mathcal{R}_I\}

But R_I is defined as R_I(H_in). The expression omits H_in. Same issue appears in downward-closure:

if H \in R_I and H' \hext H then H' \in R_I

This is syntactically and semantically ambiguous. Either make R_I global or carry the index everywhere.

3. The running SC witness still has a modeling problem

The running example is clearer than before, but the SC non-monotonicity witness still depends on including a pending read’s possible return in Obs(H1).

At H1, the read is pending. You admit the outcome:

{(r -> 0, w(1))}

Then at H2, the read response is 1, and the outcome is stranded.

This works only because Obs(H) includes return commitments for operations whose response is not yet in the history. You state that later, but the example should make this front-and-center. Otherwise a reviewer will object:

If the read has not returned at H1, why must an implementation expose r -> 0 at H1? Why not wait until the response event?

In ordinary SC/linearizability semantics, the client-visible event is the response. Before the response, there is no observation to retract. Your framework treats “possible response commitments” as observable outcomes. That is legitimate, but then the theorem is about safe early exposure or available completion, not merely about the consistency condition.

The operational line:

“to implement SC correctly, a system must not respond r -> 0 until it can rule out the future H2”

is good. But then Obs(H1) should be described as “responses an available implementation might choose now for the pending read,” not simply as completed-operation outcomes.

I would rename in the example:

* “completed operations” → “committed operation responses”
* “admissible outcomes” → “available response commitments”

That one change would prevent many objections.

4. The causal-consistency side of the running example is underspecified

For causal consistency you define outcomes as DAGs of completed operations, but at H1 the read is pending, and unlike SC you do not include pending-read outcomes. Then the contrast is asymmetric:

* SC Obs(H1) includes a pending read response.
* CC Obs(H1) only contains the completed write.

If both specs are supposed to model availability, CC should probably also admit r -> 0 and/or r -> 1 at H1, depending on the local view. The monotonicity claim should show those possible read responses remain valid under future extension.

As written, CC appears monotone partly because it withholds the pending read outcome that SC is forced to include. That weakens the example.

Suggested fix:

At H1, for CC include:

{(w(1), bot), (r -> 0, bot)}

or perhaps a DAG with concurrent write/read nodes, showing that stale read remains compatible even if the propagation later arrives. Then contrast with SC where the same r -> 0 commits to a total-order position incompatible with the future.

5. The “Coordination-free ceiling” construction seems backwards or at least confusing

This is the biggest new conceptual addition, and it needs much more care.

You write:

“For any specification (E, Obs), define o1 ↝ o2 iff there exist histories H1 ⊑ H2 with o1 ∈ Obs(H1) and o2 ∈ Obs(H2). Let Ord* be the reflexive-transitive closure … Then (E, Obs, Ord*) is monotone. Ord* is the coarsest such order.”

There are several problems.

a. The proof of monotonicity is wrong as written

To prove monotonicity, for every specific pair H1 ⊑ H2 and every o1 ∈ Obs(H1), you need some o2 ∈ Obs(H2) such that o1 Ord* o2.

But your relation ↝ is existential over histories:

o1 ↝ o2 iff there exist histories H1 ⊑ H2 ...

For a given H2, this does not guarantee there is any o2 ∈ Obs(H2) related to o1; it only guarantees some future somewhere has some related outcome.

You can fix this by defining a family of required constraints:

R = \{(o_1,o_2) \mid \exists H_1 \sqsubseteq H_2,\ o_1\in Obs(H_1),\ o_2\in Obs(H_2)\}

But that still does not guarantee that for each (H1,H2,o1) at least one o2 ∈ Obs(H2) is chosen. You are adding all possible pairs, which is enough if Obs(H2) is nonempty: for every o2 ∈ Obs(H2), the pair exists. In fact this makes the order extremely coarse: any outcome at a prefix is below every outcome at every future.

If that is intentional, then yes, it makes the spec monotone, but it may collapse distinctions aggressively.

b. “Strongest guarantee” vs “coarsest order” is semantically delicate

You say:

“The strongest guarantee achievable without coordination is the coarsest order under which the specification is monotone.”

Usually a finer order is a stronger client guarantee, because fewer transitions count as compatible. A coarser order is a weaker guarantee, because more outcomes are considered compatible. So the “strongest coordination-free guarantee” should be the finest order that remains monotone, not the coarsest.

But then your proposition says Ord* is coarsest. That sounds like the weakest guarantee, not strongest.

Maybe you are ordering orders by inclusion and using “coarsest” differently, but the prose will confuse readers. You need a precise statement:

* If Ord1 ⊆ Ord2, then Ord1 is stricter/finer/stronger.
* Monotonicity becomes easier as Ord grows.
* Therefore the strongest coordination-free weakening is the least enlargement of the declared order that makes monotonicity hold, not simply the coarsest monotone order over all possible orders.

I suspect what you really want is:

Given an original desired order Ord, construct the least preorder/order Ord^+ containing Ord plus all forced future-refinement pairs needed for monotonicity. If Ord^+ collapses contradictions, that tells you the ceiling/weakening.

That would be much more meaningful than defining Ord* from (E,Obs) alone.

c. The register ceiling proof does not follow from the general construction

You claim:

Ord* = Ord_causal: causal consistency is the coordination-free ceiling of the replicated register.

But your Ord* is constructed over outcomes from a fixed Obs. Which Obs? The text switches between sequential consistency outcomes and causal consistency observations. If Obs already is Obs_causal, then the result is circular. If Obs is SC outcomes, it is not obvious the ceiling is causal consistency.

In the register section, Obs_causal(H) is defined as:

every read r in o returns some v with w(v) in past(r,H)

This excludes the initial value unless you model the initial write as in every read’s causal past. It also seems to require returning a causally prior write, whereas causal consistency typically allows a read to return a value from a causally consistent local prefix, including stale values not necessarily including all causally visible writes unless read-your-writes/session guarantees are specified. This needs precision.

The maximality proof is also too hand-wavy:

“Since o1 Ord_causal o2, there exist histories H1 ⊑ H2…”

That does not follow automatically from the order relation; it requires a realizability lemma.

d. Queue and search ceilings are interesting but underproved

The queue “causal FIFO” result is intuitively nice, but the maximality proof is not rigorous. It talks about any finer order requiring one concurrent enqueue to precede another, but a finer order could restrict other pairs without imposing a global order on every concurrent pair. You need a general argument.

The search-structure ceiling is even more speculative. It relies on internal structure-graph evolution and a “link invariant,” which is not part of the main model. The result is interesting, but as a PODS theorem it needs much more formal setup. It may be too much for this paper.

Recommendation: make the ceiling construction a main result only if you can formalize it cleanly. Otherwise move the queue/search examples to “illustrative sketches” or cut them. The core paper is already strong without them.

6. I-confluence still conflicts with Obs(H) ≠ ∅

The spec definition says:

Obs : Hist -> P(O) maps each history to a nonempty set

But I-confluence defines:

Obs_I(H) = emptyset otherwise

This is a direct inconsistency.

You either need to allow partial/safety specs in the core definition or avoid empty observations. Since safety properties naturally want empty observations, I recommend changing Definition 3 to allow Obs(H)=∅ and then state that monotonicity is vacuous at empty-prefix histories but fails when a nonempty observable history extends to an empty one.

Also the I-confluence proof labels are reversed:

(\Rightarrow): If T is I-confluent ...
(\Leftarrow): If T is not I-confluent ...

Given the proposition says Spec_I is monotone iff T is I-confluent, the first paragraph is the T I-confluent => Spec monotone direction, not => as written unless you have stated the equivalence in the opposite orientation.

7. “Complete CAP” is much too strong as stated

The corollary says:

A specification admits a consistent, available, partition-tolerant distributed implementation iff it is monotone.

This is an extremely strong claim. It risks attracting objections from anyone familiar with CAP variants.

Problems:

1. Availability is redefined as “maximal availability under partitions,” not standard Gilbert-Lynch availability. That is okay, but then the corollary should not be called simply “Complete CAP” without heavy qualification.
2. The proof assumes every non-monotone spec has a cross-partition witness. That is not true in general. Non-monotonicity may be local to one process/thread, or require events within the same partition. Your appendix says CAP applies to specs admitting a cross-partition witness, but the corollary states iff monotone.
3. The main-text proof says “By Complete CALM, the specification requires coordination. By Lemma, coordination requires communication.” But coordination need not require cross-partition communication for every spec; it may be local, preconfigured, or inside one partition.
4. “Consistent” is overloaded: in CAP it usually means linearizability or a consistency model; in your paper correctness means Expose ∈ Obs.

I would change the result to:

For distributed specifications whose non-monotonicity witnesses can straddle partitions, future-inconsistency yields a CAP-style availability/consistency tradeoff.

That is still useful and much more defensible.

Also note a concrete LaTeX issue: \label{cor:cap} appears twice, once in the main text and once in the appendix.

8. There is an orphaned proof block in the middle of Section 4

After the Complete CAP corollary, there is:

\begin{proof}
  We exhibit a concrete witness for item~(2).
  ...
\end{proof}

This appears to be leftover from an older separation theorem. It is not attached to any theorem, and “item~(2)” has no local referent. It should be removed or moved under the proper coordination theorem.

This is the sort of thing reviewers notice and interpret as draft immaturity.

9. The separation from relational-transducer CALM still overclaims

Theorem:

“There exist non-monotone specifications with properly coordinated variants that Complete CALM can verify but relational-transducer CALM cannot certify.”

This is plausible, but the proof says any Datalog encoding of SC requires non-monotone uniqueness constraints. That is not fully proven in the text, and the referenced appendix does not actually contain a full proof of prop:prefix-negation; it only contains the N3 hierarchy proof. So the paper currently promises a full proof that is absent.

Also, the phrase “relational-transducer CALM cannot certify” is delicate. CALM can certify monotone consumers of an already-decided log if modeled as input facts growing by append. The distinction is that CALM does not provide a semantic residualization theorem for a coordinated variant. I would state that rather than claiming impossibility too broadly.

10. The HAT/isolation section is still too sweeping

The claim:

“The HAT/non-HAT boundary is precisely the partial-order/total-order boundary.”

This is a nice slogan, but I would soften it. HAT’s classifications depend on specific availability models, sticky availability, transactional availability, and exact definitions of isolation. “Precisely” is too strong unless you prove the full table.

The serializability witness is the classic write-skew cycle and is good in spirit, but the spec sketch needs to say that outcomes at H2 must include all committed transactions and their reads. Otherwise an extension could omit T2 from the outcome set.

The read-committed proof says:

o' = o ∪ {newly committed facts} ∈ Obs_L(H')

This assumes adding newly committed facts cannot introduce constraints that invalidate old reads. That is true for a permissive version of RC, but should be stated explicitly.

Snapshot isolation is mentioned but omitted. That is okay, but then do not say “recovers the HAT/non-HAT boundary” unless SI is handled somewhere.

11. Replica consistency vs coordination-freedom: good idea, but the join claim is too quick

This section says:

“if Ord admits joins, monotonicity implies convergence”

Not by itself. A join-semilattice outcome order is not enough; replicas must also exchange states, merge by join, and the implementation must choose the join as its reconciliation operation. Monotonicity plus existence of joins gives a possible convergence discipline, not automatic convergence.

Suggested wording:

“If Ord is equipped with a join operation and the implementation exposes/merges outcomes by join, then monotone independent observations can be reconciled.”

That is the CRDT story. As written, “admits joins” alone is too weak.

12. Universal construction still changes the output interface

The appendix is honest:

“this defines a new residual output interface … not the original specification’s outcome domain.”

But the theorem states:

Spec|_{I_ord} is monotone.

Earlier “properly coordinated variant” is defined as Obs'(H) ⊆ Obs(H) with the same Ord. The universal construction changes the outcome domain and order. That is not the same kind of variant.

You need two notions:

1. restriction variant: same interface, fewer outcomes/histories;
2. interface residual: new interface, e.g., ordered-prefix logs.

The universal construction is the second. Do not present it as the first.

Also, this sentence remains contradictory:

“The universal construction resolves all distributed coordination … in one round (membership).”

But the ordering service requires ongoing consensus per entry/batch. Delete or rewrite this. It directly conflicts with the earlier, correct statement that the ordering service is ongoing coordination.

⸻

Concrete LaTeX / consistency issues

These should be fixed regardless of deeper theory.

1. Duplicate label: \label{cor:cap} appears twice.
2. Missing or misleading appendix reference: prop:prefix-negation says “Full proof in Appendix~\ref{app:hierarchy},” but no full proof appears there.
3. Orphan proof block after Complete CAP: starts “We exhibit a concrete witness for item~(2).”
4. app:cap-formal is a subsection, not appendix section; that is fine, but it is referenced as if it contains full formalization. It is not very formal yet.
5. R_I index omitted in multiple places.
6. Expose_I^* definition direction is hard to read. Since H' \hext H means H is a future of H', it is correct for prefixes, but many readers will stumble. Consider writing “H' is a prefix of H” explicitly.
7. Specification nonemptiness conflict with I-confluence.
8. The “Classical distributed specifications” paragraph is empty immediately followed by another paragraph heading. Delete one.
9. Bibliography risk: citations like hydro, baccaert2026spectrum, power2025freetermination, hellerstein2020keeping need to be in the .bib; I could not verify from main.tex.

⸻

Rhetorical / positioning advice

Tone down “Complete” and “universal” where possible

The current title is better than “Universal Criterion,” but the abstract still says:

“Complete CAP”
“strongest coordination-free guarantee for any specification”
“new characterizations for registers, queues, and search structures”

That is a lot of surface area. PODS reviewers are conservative about sweeping claims. I would make the paper’s core claims maximally defensible and mark the ceiling examples as “illustrations” unless fully proved.

Lead with the cleanest contribution

The main paper should emphasize:

1. semantic CALM theorem;
2. proper coordination/residualization;
3. CALM/CRDT/I-confluence/HAT as instances.

The ceiling construction may deserve its own paper or a shorter “bonus” section. Right now it competes with the main theorem and introduces avoidable risk.

Be careful saying “CALM cannot”

Several places say relational-transducer CALM cannot express/certify things. Often the more precise statement is:

CALM can only analyze what is encoded as a monotone query over growing fact sets; Complete CALM lets us choose the semantic outcome order directly and analyze residual interfaces.

That is strong and less attackable.

⸻

Suggested revision plan

If I were preparing this for PODS, I would do the following.

Must-fix before submission

1. Repair the formal model of exposure. Either make it purely a safe-choice/spec property, or make concrete exposure path-dependent and coherent.
2. Allow empty Obs or remove empty Obs from I-confluence.
3. Fix the SC/CC running example asymmetry.
4. Remove or weaken Complete CAP. State a CAP-style corollary only for cross-partition non-monotonicity witnesses.
5. Fix the ceiling construction. Clarify strongest/finer/coarser and prove the order construction correctly, or downgrade to an illustrative appendix.
6. Delete the orphan proof block and duplicate labels.

Strongly recommended

1. Add a formal or semi-formal faithfulness condition for refinement orders, to avoid “choose a top order and everything is monotone.”
2. Make Poss vs Obs explicit. You already define \Poss; use it. It would clarify pending responses, safety specs, and coordinated variants.
3. Rewrite “proper coordination” around two cases:
    * same-interface restriction variants;
    * new-interface residuals/logs.
4. Downgrade queue/search ceiling claims unless fully formalized.

⸻

What I like most

The “coordination-free ceiling” idea is genuinely interesting, even if the current formalization needs work. If made precise, it could be a very attractive PODS contribution:

Given a desired object spec, derive the strongest weakening that can be implemented without coordination.

That is a great bridge between database theory and systems design. The register → causal consistency story is especially compelling. The queue/search examples are provocative and memorable, though currently underproved.

The paper’s broader conceptual thesis is also strong:

CALM is not about Datalog. It is about monotone growth of observable commitments.

That is a clean message and worth publishing.

⸻

Bottom line

This draft is more ambitious and more interesting, but also riskier. I would not submit it unchanged. The main theorem and unification story are promising; the new CAP and ceiling claims need significant tightening.

My recommended target for a strong PODS version:

Core paper: Complete CALM over histories/outcomes/orders; faithful recovery of CALM; proper coordination via monotone residual interfaces; CRDT/I-confluence/HAT as carefully scoped examples.
Appendix/sketch: coordination-free ceiling, with register fully proved and queue/search as conjectural or illustrative unless formalized.

That version would be much harder to reject.