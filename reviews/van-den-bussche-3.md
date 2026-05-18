## PODS 2026 Review — "Complete CALM: A Universal Criterion for Coordination-Freedom"

**Reviewer:** Jan van den Bussche (simulated)  
**Expertise:** Expert (co-author of Ameloot et al. 2013)  
**Overall recommendation:** Weak Accept

---

### Summary

The paper proposes "Complete CALM," a generalization of the CALM theorem from relational transducers to arbitrary specifications over Lamport histories. The main result states that a specification (mapping histories to outcome sets under a declared refinement order) admits a coordination-free implementation if and only if it is monotone: every admitted outcome at a history has a refinement at every future history. The paper claims to subsume the original CALM theorem, the Ameloot-Ketsman-Neven-Zinn hierarchy, I-confluence, HAT isolation levels, and CRDTs as instances.

---

### Strengths

- **Clean conceptual contribution.** The shift from programs to specifications is well-motivated and genuinely useful. The observation that CALM conflates "the system uses non-monotone operators" with "the output requires coordination" is sharp, and the separation theorem (Section 5.2) captures a real architectural pattern (consensus + log tailing) that practitioners understand intuitively but that lacked formal grounding.

- **Unifying framework.** Recovering HAT/non-HAT, I-confluence, and CRDT coordination-freedom as instances of a single monotonicity test is elegant. The paper demonstrates that these independently-developed criteria share a common semantic core.

- **Well-written exposition.** The running example (replicated register) is effective. The paper is clearly structured and the definitions build logically. The distinction between "history suppression" and "outcome suppression" as the two faces of coordination is crisp.

- **Honest about limitations.** The paper acknowledges that checking monotonicity is undecidable in general (Rice's theorem analogy), and that the criterion is an analytic tool rather than a compiler-checkable condition.

---

### Weaknesses

- **The main theorem is essentially trivial given the definitions.** The proof of Complete CALM is a three-line argument in each direction. The paper acknowledges this but the definitions may be too tightly coupled. Definition 5 essentially defines coordination-freedom as "the specification is monotone" by requiring Expose_I(H) = Obs(H). The theorem then becomes a tautology dressed in notation.

- **The CALM subsumption (Theorem 2) has a gap in the (2)⇒(3) direction.** The proof constructs H_J by delivering facts J\I "after quiescence on I." The proof asserts downward-closure but does not formally verify condition (iii) of Definition 3 for the internal events that the transducer generates in response to the new inputs.

- **The N3 Proposition (Proposition 2) is imprecise.** Theorem 20 in Ameloot et al. 2015 characterizes N3-coordination-free queries as those computable by a domain-independent monotone query—not simply "monotone queries." The paper's claim that "monotone spec ⟺ monotone query" under N3 elides the domain-independence distinction.

- **The I-confluence proof (Proposition 4) is incomplete and self-contradictory.** The (⇐) direction refutes itself: it constructs a witness, observes that monotonicity is NOT violated, then introduces a "closure requirement" not part of the original definition. Either the specification must be defined with the closure requirement from the start, or the equivalence does not hold as stated.

- **The definition of coordination-freedom is very strong and may not match operational intuitions.** Condition (ii) requires every permitted outcome to be safely exposable. A system that can always produce *a* correct answer without coordination, but cannot produce *every* correct answer, would fail this definition.

---

### Minor Issues

1. References to "Hellerstein 2026" and "Baccaert and Ketsman 2026" as published results—status should be clarified.
2. Computability requirement on implementations is stated but never used.
3. Non-emptiness of Expose_I at the initial history is not guaranteed by irretractability alone.
4. HAT proof is informal—should verify extended outcomes satisfy isolation constraints.
5. Abstract claims sequential consistency is "under the CALM umbrella" but the body shows it requires coordination (only the resolved output is monotone).

---

### Questions for Authors

1. Why require Expose_I(H) = Obs(H) rather than the weaker condition that for every H, Expose_I(H) ≠ ∅ and irretractability holds?
2. How do you reconcile the N3 claim with the fact that N3-coordination-free queries include domain-dependent queries not monotone in the input?
3. Can you provide a clean I-confluence proof without the mid-proof closure amendment?

---

### Overall Recommendation: **Weak Accept**

The conceptual contribution is strong enough for PODS. The separation theorem and unifying perspective are valuable. But the N3 claim appears incorrect as stated, the I-confluence proof has a genuine gap, and the main theorem is uncomfortably close to a tautology. With targeted fixes, this could be a solid accept.
