## PODS 2026 Review — "Complete CALM: A Universal Criterion for Coordination-Freedom"

**Reviewer:** Paraschos Koutris (University of Wisconsin-Madison)  
**Expertise:** Parallel and distributed query processing; CALM theorem literature  
**Overall recommendation:** Weak Accept

---

### Summary

This paper proposes "Complete CALM," a generalization of the CALM theorem from relational transducers to arbitrary specifications over Lamport histories. The main result states that a specification admits a coordination-free implementation if and only if its observable outcomes are monotone with respect to a declared refinement order on outcomes. The paper claims to subsume the original CALM theorem, the N1/N2/N3 hierarchy, and Baccaert-Ketsman's coordination spectrum, and applies the criterion to recover known coordination boundaries for transactional isolation levels, invariant confluence, and CRDTs.

---

### Strengths

- **Clean conceptual contribution.** The shift from program-level monotonicity to specification-level monotonicity is well-motivated. The outcome order as a first-class modeling choice genuinely expands the scope of what can be analyzed.

- **The separation theorem (Theorem 4) is the paper's strongest result.** The observation that CALM conflates internal non-monotonicity with output non-monotonicity is sharp and practically relevant. The stratified Datalog example is particularly effective.

- **Excellent exposition and running example.** The replicated register is carried through the entire paper effectively. The writing is unusually clear for a theory paper.

- **Breadth of applications.** Recovering HAT/non-HAT, I-confluence, and CRDT coordination-freedom as instances of a single test demonstrates unifying power.

- **Honest about limitations.** The paper acknowledges undecidability and positions the criterion as an analytic tool.

---

### Weaknesses

- **The main theorem is technically shallow.** The proof is a one-step unfolding of definitions. The paper acknowledges this but for PODS the technical bar is high. The theorem is more of a well-chosen definition than a deep result.

- **The N3 subsumption (Proposition 3) is not rigorous.** The proof says "the proof of Theorem [subsumption] applies unchanged" but does not carry out the actual work of showing the semantic definition coincides with the operational definition under the restricted history space. The N1/N2 cases and Baccaert-Ketsman are dismissed in a single sentence.

- **The definition of coordination-freedom is very strong and may be too restrictive.** Many systems we consider "coordination-free" (e.g., CRDTs with garbage collection) do suppress some admissible histories without requiring inter-node coordination. The equivalence between "no suppression" and "no need for remote consultation" is asserted but not proved.

- **The I-confluence proof (Proposition 5) has a gap.** The reverse direction discovers that the naive construction does NOT violate monotonicity and must retreat to a "closure requirement" not part of the original definition.

- **No complexity or decidability results.** Characterizing the complexity of checking monotonicity for natural specification languages would significantly strengthen the contribution.

---

### Minor Issues

1. References to unpublished companion papers as established results.
2. Theorem 2 relies on Ameloot et al.'s Corollary 13 for (1)⟺(3)—the new content is only (2)⟺(3).
3. Universal construction's "monotone extension of the authority chain" for membership change is informal.
4. "Well-coordination" conflicts with existing distributed computing terminology.
5. Write-skew witness for serializability should note distinction from strict serializability.

---

### Questions for Authors

1. Can you prove that a weaker definition of coordination-freedom (e.g., "never needs to consult remote state") yields the same characterization?
2. Under the original Bailis et al. definition of I-confluence (without closure requirement), does the equivalence with monotonicity still hold?
3. Can you provide a complete proof for the N3 proposition showing the operational→semantic direction?

---

### Overall Recommendation: **Weak Accept**

The paper makes a genuine conceptual contribution. The separation theorem and breadth of applications tip it toward acceptance. However, the main theorem is technically shallow, the subsumption claims are not fully proved, and the I-confluence application has a gap. The paper is a well-written definitional contribution with a clean unifying perspective, but the technical depth is below the typical PODS bar. The separation theorem and applications are strong enough for acceptance, but I am not fully confident.

**Confidence:** 4/5
