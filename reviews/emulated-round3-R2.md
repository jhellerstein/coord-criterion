# Emulated PODS Review — Round 3, Reviewer 2

**Reviewer perspective: Jan Van den Bussche — logic, database theory, formal methods**

## Summary

This paper generalizes the CALM theorem from relational transducers to arbitrary specifications over Lamport histories. The central claim is that a specification admits a correct coordination-free implementation (in the I/O automaton model with adversarial scheduling) iff it is "monotone" — every admissible outcome refines along every future. The paper proves this via a protocol construction (sufficiency) and an indistinguishability argument (necessity), then applies the criterion to isolation levels, I-confluence, CRDTs, and CAP.

## Evaluation

The paper addresses an important question with a clean answer. The I/O automaton operational model is the right choice, and the proof structure (construction + impossibility) is standard and appropriate for the claim.

### What works well

**The operational theorem (Theorem 1) is the paper's strongest formal contribution.** The causal-view protocol is a concrete construction, and the indistinguishability argument for necessity follows the standard distributed computing pattern. The response-soundness and response-preservation conditions are well-chosen well-formedness requirements. The joint-consistency remark (Remark 1) is a nice observation that closes what initially appears to be a gap.

**The CALM subsumption (Theorem 3) is precise and correct.** The three-way equivalence (coordination-free transducer ⟺ monotone spec ⟺ monotone query) is clean and the proof is straightforward once the instantiation is set up.

**The running example is well-constructed.** The two-write/two-read linearizability witness is standard and effective. The contrast with causal consistency (per-process views can disagree on concurrent write order) is immediate.

**The distinction between monotonicity and distributed-monotonicity is conceptually valuable.** This is a genuine insight: CAP is about non-monotonicity that spans a partition, not all non-monotonicity. The partition-constrained future definition makes this precise.

### Concerns

**1. The necessity proof's scope.** The proof says coordination-freedom means "the response is enabled without any further input action." This is a very strong condition — it means the process cannot wait for *any* external event, including a new local client invocation. This is stronger than what most distributed systems papers mean by "coordination-free" (which usually means "no waiting for remote communication"). The paper acknowledges this implicitly by having a separate, weaker CAP theorem using distributed-monotonicity. But the relationship should be stated more explicitly: Complete CALM uses a *strong* local-immediacy notion; Complete CAP uses the standard *distributed* availability notion. The two are different theorems about different operational properties.

**2. The properly coordinated variant definition is unusual.** Checking monotonicity "only over admitted histories (those with non-empty Obs')" is a non-standard restriction. In standard definitions, monotonicity is a universal property over all futures. The paper's variant effectively restricts the future space — which is fine, but it means "monotone" in the variant sense is weaker than "monotone" in the standard sense. This should be flagged clearly, perhaps by using a different term ("monotone within its admitted space" or "A-monotone").

**3. Response totality is assumed but not formally defined.** The sufficiency proof parenthetically assumes "response totality: at every reachable history containing an invocation requiring a response, Obs(H) ≠ ∅." This is a precondition of the theorem that should be stated in the theorem statement or as a numbered definition. As written, the theorem says "iff monotone" but the proof requires "monotone + response-total."

**4. The paper is over the page limit.** The body appears to be ~17 pages. For PODS, the limit is typically 15 pages (excluding references and appendix). The operational model section is essential and should stay; I would suggest compressing the applications section (Section 6) by removing one of the three subsections (I-confluence or CRDTs — both make the same structural point).

### Specific Technical Comments

- Definition 4 (Specification): The response-soundness and response-preservation conditions are stated as "well-formedness conditions" but not given definition numbers. They should be a numbered definition for easy reference.
- The proof of Theorem 1 (sufficiency) says "chooses o ∈ Obs(H_i)" — this requires Obs(H_i) ≠ ∅, which is the response-totality condition. The parenthetical handling is insufficient; make it a precondition.
- Theorem 2 (Complete CALM) says "Immediate from Theorem 1" — this is fine but the reader may want to see the semantic equivalence (monotone ⟺ every outcome future-consistent) stated as a lemma for clarity.
- The frontier appendix maximality proofs are improved but the register case still asserts "no other write in r's causal past" without arguing this is always achievable.

## Overall Assessment

The paper makes a genuine contribution: identifying monotonicity as the semantic core of coordination-freedom across disparate models, and proving this via a concrete operational characterization. The I/O automaton theorem is non-trivial and the applications are convincing. The main weaknesses are length and a few formal loose ends (response totality, variant monotonicity terminology). I recommend acceptance with minor revisions.

**Score: Accept (weak)**
