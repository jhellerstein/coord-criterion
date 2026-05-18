## Review: "Complete CALM: A Universal Criterion for Coordination-Freedom"

**Reviewer:** Wim Martens (simulated), University of Bayreuth  
**Venue:** PODS 2026

---

### Summary

The paper proposes "Complete CALM," a generalization of the CALM theorem from relational transducers to arbitrary specifications over Lamport histories. The main result states that a specification (mapping histories to sets of admissible outcomes under a declared refinement order) admits a coordination-free implementation if and only if it is monotone—i.e., every outcome admitted at a history has a refinement admitted at every future history. The paper claims to subsume the original CALM theorem, enable compositional verification of coordination protocols, and recover known coordination boundaries (HATs, I-confluence, CRDTs) as instances.

---

### Strengths

- **Clean conceptual contribution.** The shift from program-level analysis to specification-level analysis is well-motivated and genuinely useful. The observation that CALM conflates "the system uses non-monotone operators" with "the system's *output* requires coordination" is sharp and important. The separation theorem (Section 4.2) captures a real architectural pattern (consensus + log tailing) that practitioners use daily but that lacked formal justification.

- **Elegant framework design.** The three-component specification (event universe, observability function, outcome order) is parsimonious. The running example of a replicated register with two specifications over the same histories is pedagogically effective and carries through the paper well.

- **Formal subsumption of CALM is convincing.** Theorem 2 (Section 4.1) provides a clean formal argument that the transducer instantiation recovers CALM exactly, not merely by analogy. The proof via the three-way equivalence (coordination-free transducers ↔ monotone specification ↔ monotone query) is well-structured.

- **Broad applicability demonstrated.** The applications to HATs, I-confluence, and CRDTs show that the framework is not vacuous—it can express and recover known results. The uniform explanation ("commitment to structure that a future can invalidate") is satisfying.

- **Honest about limitations.** The paper correctly notes that checking monotonicity of an arbitrary specification is undecidable (Rice's theorem analogy), and positions the criterion as an analytic tool rather than a compiler-checkable condition.

---

### Weaknesses

1. **The main theorem is essentially a tautology given the definitions, raising concerns about circularity.**

   The definition of coordination-freedom (Definition 6) requires *both* (i) no history suppression and (ii) Expose_I(H) = Obs(H) for all admissible H. The definition of monotonicity (Definition 7) says: for all H₁ ⊑ H₂ and o ∈ Obs(H₁), there exists o' ∈ Obs(H₂) with o ≤ o'. The proof of necessity simply observes that if you set Expose = Obs (condition ii) and realize all histories (condition i), then irretractability *is* monotonicity. The proof of sufficiency constructs the implementation by *defining* Expose = Obs.

   This is logically correct but raises the question: is the theorem doing real work, or is the intellectual content entirely in the *definitions*? The paper acknowledges this ("The proof is short by design. The contribution is not a difficult proof but a change of domain") but I think the issue runs deeper. The definition of coordination-freedom is *engineered* so that monotonicity is equivalent to it. A skeptic could argue that the "no outcome suppression" condition (Expose = Obs) is unreasonably strong—it requires that *every* permitted outcome be safely exposable, not just that *some* correct outcome exists. This is a modeling choice that makes the theorem true, not a theorem that validates a pre-existing definition.

2. **The interpretation of Expose_I(H) = Obs(H) as a "capability set" is incoherent with irretractability.**

   The paper states: "A concrete execution exposes at most one outcome per history; the condition requires that *whichever* outcome the implementation chooses, it can do so safely. This is the sense in which Expose_I(H) = Obs(H): the set records all outcomes available for safe exposure, not a claim that all are simultaneously communicated to clients."

   But irretractability is stated as: for all realized H₁ ⊑ H₂, if o ∈ Expose_I(H₁) then there exists o' ∈ Expose_I(H₂) with o ≤ o'. If Expose_I(H) is a "capability set" (what *could* be exposed), then irretractability says: for every outcome that *could* be exposed at H₁, some refinement *could* be exposed at H₂. But this is much stronger than what irretractability should mean operationally. Operationally, irretractability should say: for the outcome that *was actually* exposed at H₁, some refinement is available at H₂. The paper's formulation quantifies over all *possible* exposures, not just actual ones. This conflation between "could expose" and "did expose" is the mechanism by which the theorem becomes trivial—but it also makes the definition of coordination-freedom arguably too strong.

   A more natural definition would be: there exists a *selection function* σ : H → O (choosing one outcome per history) such that σ is irretractable and σ(H) ∈ Obs(H) for all H. Under this definition, coordination-freedom would mean: for *every* admissible history and *every* selection function, irretractability holds. This is strictly weaker than the paper's definition and would require a non-trivial proof.

3. **The applications are sketches, not proofs.**

   - Proposition 1 (HAT levels are monotone): The proof handles read uncommitted, read committed, monotonic reads, and read-your-writes individually, but each case is argued informally ("extending a history can add writes but never removes them"). There is no formal definition of what Obs_L(H) actually is for any of these levels. Without a precise definition of the outcome set, the claim "take o' = o plus any newly committed facts" is hand-waving—one must verify that this o' actually satisfies the isolation level's constraints, which is non-trivial for session guarantees.

   - Proposition 3 (I-confluence ↔ monotonicity): The proof sketch is two sentences in each direction. The forward direction says "extending a history can only enlarge the reachable-state set, and merging invariant-preserving states preserves the invariant." But this *is* I-confluence—the proof is circular. The claim should be: I-confluence (as defined by Bailis et al.) is equivalent to monotonicity (as defined here) under the specific instantiation. This requires showing that the instantiation faithfully captures Bailis et al.'s model, which is not done.

   - Proposition 4 (CRDTs are monotone): This is the cleanest of the three, but still assumes without proof that "every state reachable at H' is at least as large as some state reachable at H." This requires showing that the history extension relation preserves the lattice ordering of reachable states, which depends on the specific CRDT merge semantics.

4. **Hidden quantifier issue in Definition 7 (Monotonicity).**

   The definition quantifies over *all* histories H₁, H₂ ∈ ℋ with H₁ ⊑_h H₂. But ℋ is the set of *all well-formed histories* over the event universe—an enormous (typically uncountable) space. The definition does not relativize to any particular input history or to admissible histories. This means monotonicity must hold even for histories that no implementation would ever produce. Is this intentional? If so, it should be discussed. If the definition were relativized to admissible histories (given some input), the theorem might not hold as stated—the necessity direction uses the fact that *both* H₁ and H₂ are admissible, but sufficiency constructs an implementation over *all* admissible histories.

   More precisely: the paper defines A(H_in) as the admissible histories given input H_in, but monotonicity is defined over all of ℋ without reference to any H_in. The proof of necessity only uses histories that are admissible (given some input), so monotonicity restricted to admissible histories would suffice for necessity. But sufficiency requires monotonicity over all admissible histories for all inputs—which is the same as all of ℋ if every history is admissible for some input. Is this always the case? The paper does not address this.

5. **The "resolved specification" (Definition 9) has Obs_I(H) = ∅ for unrealized histories, violating the non-emptiness requirement of Definition 4.**

   Definition 4 requires Obs(H) ≠ ∅ for all H. The resolved specification sets Obs_I(H) = ∅ for H ∉ R_I. Either the non-emptiness requirement should be dropped, or the resolved specification should be defined only over realized histories (restricting the domain of ℋ). The paper's Definition 10 (well-coordination) does restrict to realized histories, but the resolved specification as an object does not satisfy the specification axioms. This is a minor formal inconsistency but should be addressed.

---

### Minor Issues

- The abstract has a typo: "declative" → "declarative."
- The paper references [hellerstein2026complexity] and [hellerstein2026coordinationcriterion] which appear to be unpublished companion papers. The self-referential nature of the research program is fine, but the paper should be self-contained—currently, determination depth is invoked but not defined.
- The "Minimality" result (Appendix B, Proposition 5) constructs ≤* as the reflexive-transitive closure of the reachability relation, "quotiented by mutual reachability." This quotient may collapse distinct outcomes into equivalence classes, making ≤* a preorder on equivalence classes rather than a partial order on O. The claim that this is a partial order needs justification.
- The universal construction (Appendix C) changes the outcome domain and order from the original specification. The claim "for any specification, an ordering authority yields a monotone residual" is true only because the construction *redefines* what outcomes are. This should be stated more carefully—it is not that the original specification becomes monotone, but that a *different* specification (over log prefixes) is monotone.
- Example 3 (stratified Datalog) is well-chosen but the claim "the exposed output is monotone under set inclusion (it can only grow as the sealed computation completes)" conflates two things: the output is *fixed* after sealing (it doesn't grow), and the *knowledge* of the output grows monotonically. Which is the outcome here?

---

### Questions for Authors

1. **On the strength of the coordination-freedom definition:** Why require Expose_I(H) = Obs(H) rather than the weaker condition "there exists a selection function σ with σ(H) ∈ Obs(H) for all H, such that σ is irretractable along all admissible futures"? The weaker condition captures "the implementation can always find *some* safe outcome to expose" without requiring that *every* outcome be safe. Under the weaker definition, is the characterization still monotonicity, or something else?

2. **On the quantifier structure of monotonicity:** Is there a natural example where monotonicity holds over all admissible histories (for all inputs) but fails over some well-formed history that is not admissible for any input? If not, can you prove that every well-formed history is admissible for some input, making the distinction moot?

3. **On the applications:** For Proposition 3 (I-confluence ↔ monotonicity), can you provide a formal instantiation that maps Bailis et al.'s definitions to yours bijectively, rather than arguing by informal analogy? Specifically, what is the event universe, what are the histories, and what is Obs_I(H) precisely?

---

### Overall Assessment

The paper presents a clean and potentially important conceptual contribution: lifting CALM from programs to specifications. The framework is well-designed, the running example is effective, and the separation from CALM (Section 4.2) is the paper's strongest result. However, the main theorem is uncomfortably close to a tautology given the definitions—the intellectual content is in the modeling choices, not in the proof. The "capability set" interpretation of Expose creates a tension with irretractability that the paper does not fully resolve. The applications are sketched rather than proved, and several formal issues (non-emptiness violation in resolved specs, quantifier scope of monotonicity, minimality construction) need attention.

The paper is above average in ambition and conceptual clarity, but below the PODS standard for formal rigor in its current form. The definitions need tightening, the applications need full proofs, and the relationship between the definition of coordination-freedom and the theorem needs a more honest discussion of the degree to which the theorem is "built into" the definitions.

---

### Recommendation: **Weak Reject**

The conceptual contribution is real and the framework is promising, but the formal execution does not yet meet the standard for a top theory venue. The main theorem's near-tautological character, the unresolved tension in the Expose interpretation, and the sketched applications are each individually addressable but collectively suggest the paper needs another revision. I would encourage resubmission with: (a) a frank discussion of the definitional engineering that makes the theorem hold, (b) full proofs for at least one application (I-confluence is the most natural candidate), and (c) resolution of the Expose_I = Obs capability-set issue, ideally by showing that the weaker "selection function" definition yields the same characterization (which would make the theorem genuinely non-trivial).
