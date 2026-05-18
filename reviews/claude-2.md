## Review: "Complete CALM: A Universal Criterion for Coordination-Freedom" (Revised)

This revision has made meaningful progress on the major concerns raised previously. The formal subsumption of CALM (Theorem 4.1) is the most important addition — it was previously missing — and the proof of Proposition 4.5 (HAT levels) has been substantially developed. The outcome order concern is now addressed with practical guidance in Remark 3.2. The paper is in considerably better shape. Here is a detailed assessment of what works, what remains problematic, and what is new.

---

### What Has Improved

**Theorem 4.1 (Subsumption of CALM) is the right move and mostly works.** Showing the three-way equivalence between Ameloot et al.'s operational definition, Complete CALM's semantic definition, and monotone queries gives the paper its needed formal grounding. The argument that CALM is not merely analogous to but a formal instance of Complete CALM now has teeth. The appeal to Ameloot et al.'s Corollary 13 for the $(1)\Leftrightarrow(3)$ direction is correct and appropriately attributed.

**Proposition 4.5 (HAT levels are monotone) now has a real proof.** Going through read uncommitted, read committed, monotonic reads, and read-your-writes individually is exactly what was needed. The key structural observation — "constraints are prefix-stable: they restrict which read values are admissible at a given history, but never retroactively invalidate a previously admissible read" — is precise and the per-level arguments follow cleanly.

**The outcome order is now handled better.** Remark 3.2 gives practical guidance ("too-coarse makes everything trivially monotone; too-fine introduces spurious non-monotonicity; the order is part of the semantic contract, not chosen freely by the analyst") and closes the concern that the theorem is vacuous by choosing Ord freely. The statement that "changing the order changes the specification" is exactly right.

**The sufficiency proof is cleaner.** Setting $\Expose_I(H) = \Obs(H)$ throughout (rather than "any nondeterministic choice") makes the coordination-freedom verification immediate and eliminates the previous ambiguity about whether safety holds.

---

### Remaining Major Issues

**1. The universal construction overstates "one round."**

This is the most significant remaining error. The proof of Theorem A.1 says the construction "places all input events into a total order consistent with causality and delivers this order identically to every replica." That is total-order broadcast (TOB) — a protocol that requires one round of consensus *per batch of events*, not one round of coordination total. TOB is the primary coordination mechanism in systems like Paxos, Raft, and ZAB; calling it "one round of membership establishment" conflates two very different things.

The claim "the distributed coordination depth is therefore just one round: establishing membership" (Remark in the body, and the section header "One Round of Coordination Universally Suffices") is incorrect if the construction relies on TOB. What is true is that you need a sequencer *authority* — establishing that a sequencer exists requires one coordination act (choosing the leader/sequencer). But the sequencer then runs continuously, producing one decision per entry, which is ongoing distributed coordination. The paper conflates the one-time authority establishment with the ongoing consensus protocol.

The fix is either: (a) acknowledge that the ordering mechanism requires ongoing coordination and that "one round" refers to establishing the authority role (not its operation), or (b) use a different construction — for example, if all inputs arrive before any evaluation begins (the batch model), one round of membership plus sorting genuinely suffices. Be explicit about which model you mean.

**2. The subsumption theorem proof has a gap in the $(2) \Rightarrow (3)$ direction.**

The proof says: "Let $H_I$ be a complete run on input $I$ (reaching quiescence with output $Q(I)$) and let $H_J$ extend $H_I$ by adding the facts $J \setminus I$ as additional input events." The inference $O_{H_I} \subseteq O_{H_J}$ then follows from monotonicity of $\Spec_Q$.

The argument is correct *given* that the natural completion of $H_I$ to a run on $J$ is a valid future in the sense of Definition 2.2. This requires that adding new input events to a quiescent run does not introduce new predecessors of existing events — which holds in the transducer model (new input facts arrive causally after quiescence) but is not a consequence of the history framework alone. The proof should state explicitly: "In the transducer model, adding new input facts to a quiescent run is always a valid future (new facts arrive causally after the quiescence point)." Without this, the step from model-specific quiescence to the general history framework is left implicit.

**3. The minimality proposition (Appendix B) is still weaker than its conclusion claims.**

The proof shows: if a coordination-free implementation $I$ exists, then the specification is monotone under $\Ord^*$ — an order *derived from $I$'s observable behavior*. The conclusion says "monotonicity is therefore the weakest semantic structure that coordination-free behavior can exhibit." 

This conflates two things. The necessity direction of the main theorem establishes that if the specification is *not monotone under the declared $\Ord$*, then no coordination-free implementation exists. That is the sharp result. Proposition B.1 proves only that some order (possibly different from $\Ord$) makes the behavior monotone — which is trivially true of any deterministic system. The proposition adds nothing to the main theorem and the "weakest semantic structure" language should be revised or the proposition removed. If you want to keep it, the correct framing is: "the coordination-free implementations of a specification inhabit exactly the monotone specifications under their induced behavior order, confirming that the main theorem's characterization cannot be weakened."

**4. The I-confluence specification encoding uses a counterintuitive outcome order.**

In Section 4.2, outcomes are "sets of database states reachable under causally admissible extensions" ordered by set *inclusion* as refinement — that is, refinement means *more* states are possible. This is the opposite of the natural intuition (refinement usually means narrowing down, not expanding). The parenthetical "(Here refinement means enlarging the known-reachable set—learning that more states are possible—not ruling states out)" acknowledges this but doesn't explain why this choice is appropriate.

The issue is that the outcome domain and order have been chosen post-hoc to make I-confluence come out as a monotonicity condition, rather than being derived from the semantics of the specification in the way the register example does. For the register, prefix extension is natural: a longer sequence of observed operations genuinely refines a shorter one. For I-confluence, the choice of "sets of reachable states" with upward-closure ordering is a technical device, not a natural semantic commitment.

The cleanest fix is to reformulate I-confluence outcomes as individual invariant-preserving states (not sets of states) with some natural order, and show that I-confluence is the condition that makes merges produce an extension rather than a contradiction. This would make the encoding parallel the register example's structure.

---

### Moderate Issues

**5. The separation theorem statement is still informal about CALM's scope.**

Theorem 4.2 says "CALM, applied syntactically to any program implementing $I$, classifies it as non-monotone." But CALM requires a relational transducer encoding; not every program can be analyzed by CALM, and the theorem should say "any relational transducer program implementing $I$." More importantly, the proof's claim — "CALM, applied to the combined program text, identifies these non-monotone operators and classifies the system as requiring coordination. This is correct for the internal specification (linearizability does require coordination), but incorrect for the output specification" — is still comparing CALM applied to the internal program with Complete CALM applied to the output specification. CALM was never designed to analyze composed output specifications, so calling this a "failure" of CALM needs more precise framing. The claim should be: CALM *cannot ask* this question; it is not that CALM gives the wrong answer to the same question.

**6. The HAT proof still omits causal consistency.**

Proposition 4.5 covers read uncommitted, read committed, monotonic reads, and read-your-writes, but not causal consistency — one of the most important HAT levels in Bailis et al.'s taxonomy. Since causal consistency is the strongest HAT level and requires a separate argument (the outcome order must respect causal order, and extending a causally consistent history cannot invalidate prior causal reads), it should either be addressed or the scope of the proposition should be explicit about which HAT levels are covered.

---

### Minor Issues

**Typo at line 132:** "monotonicity propertie" should be "monotonicity properties."

**Missing open-quote at line 1263:** `requires coordination'' by CALM` has an asymmetric quotation mark — should be `''requires coordination'' by CALM` or equivalently using proper LaTeX quotation.

**The "Coordination Criterion" vs. "Complete CALM" naming** appears to have been resolved — the paper now consistently uses "Complete CALM." Good.

**The "Additional Applications" appendix (Section at line 1770)** defers to "an extended version" for the full formalization of consensus decomposition. Since this paper is the extended version, this reference should either be removed or the formalization included.

---

### Overall Assessment

The paper has advanced to a point where acceptance is realistic with targeted revisions. The main theorem is sound, the subsumption proof works, the HAT applications are properly proved, and the outcome order concern is adequately handled. The core theoretical contribution — that specification-level monotonicity is the exact semantic characterization of the coordination boundary — is correct and more general than anything in the prior literature.

The "one round" claim in the universal construction is the most pressing issue: if left as is, a reviewer will correctly identify it as wrong and it will create unnecessary controversy around an otherwise clean result. The fix is straightforward: clarify that "one round" establishes the authority role and that the authority's ongoing operation is the mechanism through which coordination continues; the novelty is that downstream consumption of the resulting monotone output stream requires no additional coordination. This is both true and interesting — it just needs to be stated correctly.