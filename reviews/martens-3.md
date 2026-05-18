## Review: "Complete CALM: A Universal Criterion for Coordination-Freedom"

**Reviewer:** Wim Martens (simulated), University of Bayreuth  
**Venue:** PODS 2026  
**Overall recommendation:** Weak Accept

---

### Summary

The paper proposes "Complete CALM," a generalization of the CALM theorem from relational transducers to arbitrary specifications over Lamport histories. The main claim is that a specification admits a coordination-free implementation if and only if its observable outcomes are monotone with respect to a declared refinement order on outcomes. The paper instantiates this criterion on transactional isolation levels, invariant confluence, and CRDTs, and proves a "separation" from syntactic CALM.

---

### Strengths

- **Clean conceptual contribution.** The shift from programs to specifications is well-motivated. The idea that coordination-freedom is a semantic property of the specification rather than a syntactic property of the program is compelling and unifying.

- **The main theorem is elegantly simple.** The proof is short and correct. The simplicity shows the definitions are well-chosen.

- **Good subsumption argument.** The formal subsumption of relational-transducer CALM (Theorem 2) is carefully done. The three-way equivalence is convincing.

- **The separation theorem captures real architectural practice.** The Paxos + log tailing example and the stratified Datalog example are both effective.

- **Broad instantiation.** The applications demonstrate the framework's breadth.

---

### Weaknesses

- **The "capability set" interpretation of Expose_I is incoherent under scrutiny.** If Expose_I(H) is what *could* be safely exposed, then irretractability quantifies over all possible exposures, not just actual ones. This conflation makes the theorem trivial but the operational semantics murky. A cleaner formulation would define an implementation as a strategy (function from histories to a single chosen outcome) and quantify over all strategies.

- **The I-confluence proof (Proposition 5) is not rigorous.** The (⇐) direction explicitly acknowledges that the initial construction does not yield a monotonicity violation, then introduces a "closure requirement" not part of the original definition. This is a serious gap.

- **The resolved specification definition (Definition 8) has a well-formedness issue.** Non-emptiness of Expose_I at all realized histories is asserted but not proved from the axioms.

- **The paper lacks formal precision in several definitions.** The event universe is informal; the admissible histories definition's quantifier direction is confusing; the computability requirement is unused.

- **The paper's novelty claim is overstated relative to proof difficulty.** The main theorem is a definitional tautology. The real contribution is the definitions and instantiations, but the paper frames the theorem as the main result.

---

### Minor Issues

1. References to unpublished companion papers as established results.
2. Proposition 3 references a theorem label that may be dangling.
3. Notation inconsistency between ⊑_h and ⪯.
4. Universal construction changes outcome domain without sufficient discussion.
5. Missing decidability discussion.

---

### Questions for Authors

1. Can you give a formal operational semantics for what it means to "expose" an outcome?
2. Can you fix the I-confluence proof without the mid-proof closure amendment?
3. In what precise sense does Complete CALM "recover" CAP rather than merely being consistent with it?

---

### Overall Recommendation: **Weak Accept**

The paper presents a clean conceptual framework that genuinely unifies several known results. The separation theorem and applications are the strongest parts. However, the I-confluence proof has a genuine gap, the Expose_I semantics are muddled, and the main theorem is more of a well-chosen definition than a deep result. The paper is above the acceptance threshold but the formal foundations need tightening.
