## PODS 2026 Review — "Complete CALM: A Universal Criterion for Coordination-Freedom"

**Reviewer:** Paraschos Koutris (University of Wisconsin-Madison)  
**Expertise:** Parallel and distributed query processing; CALM theorem literature

---

### Summary

This paper proposes "Complete CALM," a generalization of the CALM theorem from relational transducers to arbitrary specifications over Lamport histories. The main result states that a specification (mapping histories to outcome sets under a declared refinement order) admits a coordination-free implementation if and only if it is monotone—i.e., every admissible outcome at a history has a refinement at every future history. The paper claims to subsume Ameloot et al. (2013), Ameloot-Ketsman-Neven-Zinn (2015), and Baccaert-Ketsman (2026), and demonstrates applications to transactional isolation levels, invariant confluence, and CRDTs.

---

### Strengths

- **Clean conceptual contribution.** The shift from programs to specifications, and from set-inclusion to arbitrary partial orders on outcomes, is genuinely clarifying. The framework cleanly separates the *semantic need* for coordination (a property of the specification) from the *operational mechanism* (consensus, locking, etc.). This is a useful conceptual advance over the original CALM formulation.

- **The compositional separation (Theorem 4) is the paper's strongest result.** The observation that CALM cannot distinguish "before coordination" from "after coordination" is well-articulated and practically important. The stratified Datalog example (Example 4) is particularly effective—it shows a real limitation of syntactic monotonicity analysis in CALM's own native setting.

- **Uniform recovery of known boundaries.** The applications to HAT isolation levels, I-confluence, and CRDTs are well-chosen and demonstrate that the framework is not vacuous. The structural explanation (partial-order vs. total-order commitment) is satisfying.

- **Good exposition.** The running example (replicated register) is well-constructed and carries through the paper effectively. The paper is clearly written and well-organized for its length.

- **The universal construction (Appendix C) is interesting.** The observation that membership + ordering isolates all coordination into a reusable layer, with downstream consumption being coordination-free, is a clean architectural insight with formal backing.

---

### Weaknesses

- **The main theorem (Complete CALM) is technically shallow.** The proof is essentially a one-step unfolding of definitions: sufficiency constructs the trivial implementation (realize everything, expose everything), and necessity is a direct contradiction from the definitions. The paper acknowledges this ("The proof is short by design") but the claim that the contribution is a "change of domain" rather than a difficult proof is not fully convincing for a venue like PODS. The definitions are set up so that the theorem is nearly tautological—coordination-freedom *means* no suppression, and monotonicity *means* no outcome gets stranded. The intellectual content is in the definitions, not the theorem, and the paper does not sufficiently justify why these particular definitions are the "right" ones beyond appeal to intuition and examples.

- **The CALM subsumption (Theorem 2) has a gap in the (2)⇒(3) direction.** The proof assumes that for inputs I ⊆ J, one can construct a history H_J that extends H_I by "adding the facts J \ I as additional input events." But in the transducer model, a "complete run on input I" (reaching quiescence) is a *terminal* history—it includes heartbeat transitions signaling end-of-input. Extending such a history with new input facts is not straightforward; it requires re-opening the computation. The paper glosses over whether H_I ⊑_h H_J actually holds under the formal definition of futures (Definition 3), given that quiescence events in H_I may not be downward-closed predecessors of the new input events in H_J. This needs more careful treatment to claim formal equivalence with Ameloot et al.'s Corollary 13.

- **The subsumption of Ameloot-Ketsman-Neven-Zinn and Baccaert-Ketsman is hand-wavy.** The paper claims these are "likewise subsumed" in a single paragraph with no formal instantiation. For AKNZ, the paper says "each model restricts the admissible history space" but does not formally define the instantiation for models N₁, N₂, N₃ or verify that the equivalence holds. For Baccaert-Ketsman, the claim that "C-monotonicity coincides with monotonicity of the specification whose admissible histories are those consistent with C" is stated without proof. Given that these subsumption claims are a headline contribution, this is insufficient for a PODS paper. At minimum, one of these should be worked out in detail.

- **The definition of coordination-freedom (Definition 5) is very strong—arguably too strong.** Requiring Expose_I(H) = Obs(H) (every permitted outcome is safely exposable) is stronger than the standard operational notion of coordination-freedom in the distributed computing literature. In practice, a coordination-free implementation might choose to expose only a *subset* of permitted outcomes at each history (e.g., based on local state) without this constituting "coordination." The paper's definition conflates "the implementation has the *freedom* to expose any outcome" with "the implementation *must* expose all outcomes." The irretractability requirement then forces the strong form. This definitional choice makes the theorem true but potentially limits its applicability—real coordination-free systems (e.g., CRDTs) typically expose a *single* deterministic outcome at each state, not the full admissible set.

- **The outcome order is doing too much work without sufficient justification.** The paper acknowledges that the outcome order is a "modeling choice" and that a "too-coarse order makes all specifications trivially monotone" while a "too-fine order introduces spurious non-monotonicity." But there is no formal criterion for when an order is "correct"—the paper says it is "determined by what the specification means." This is circular: the theorem says coordination-freedom ↔ monotonicity, but monotonicity depends on the choice of order, and the choice of order is supposed to reflect whether the specification "needs" coordination. Without an independent criterion for the correctness of the outcome order, the theorem risks being unfalsifiable.

---

### Minor Issues

1. Abstract: "declative" → "declarative" (typo).
2. The paper references "Hellerstein [2026]" for determination depth multiple times, but this is an unpublished companion paper. The mutual dependence between two unpublished papers weakens both—neither can be evaluated independently.
3. The "Additional Applications" appendix (consensus, snapshots, agreement tasks) is too sketchy to add value. These are one-paragraph summaries without formal statements or proofs. Either develop them or remove them.
4. The paper does not discuss decidability of checking monotonicity for specific specification formalisms beyond a brief paragraph. For PODS, a concrete decidability result (even for a restricted class) would significantly strengthen the contribution.
5. Definition 4 (Implementation): the requirement that R_I and Expose_I be "computable" is stated but never used in any proof. Is it needed for the main theorem? If not, why include it?
6. The comparison with Attiya-Enea-Román-Calvo (2023) is too brief to be useful. How exactly does "arbitration-free" map to "coordination-free" in this framework?

---

### Questions for Authors

1. **On the outcome order:** Can you give a formal criterion (not just examples) for when an outcome order is "appropriate" for a specification? Without this, how do you respond to the concern that the theorem is trivially true for any specification if one chooses the "right" order (e.g., the discrete order makes everything monotone)?

2. **On the CALM subsumption:** In the (2)⇒(3) direction of Theorem 2, how exactly do you handle the extension of a quiescent history H_I to H_J? In Ameloot et al.'s model, quiescence involves specific heartbeat transitions that signal end-of-input. Does your future relation (Definition 3) permit adding new input events after quiescence?

3. **On the separation theorem:** Theorem 4 claims CALM "cannot" verify well-coordination. But couldn't one define a syntactic extension of CALM that tracks stratification boundaries and recognizes post-coordination monotonicity? Is the separation inherent to *any* syntactic analysis, or specific to the particular formalism of relational transducers? If the latter, the separation is less fundamental than claimed.

---

### Overall Recommendation: **Weak Accept**

The paper makes a genuine conceptual contribution by lifting CALM from programs to specifications and introducing the compositional separation (well-coordination). The framework is clean, the exposition is good, and the applications are well-chosen. However, the main theorem is technically shallow (nearly tautological given the definitions), the CALM subsumption claims are not fully rigorous (particularly for AKNZ and Baccaert-Ketsman), and the definitional choices (especially the outcome order and the strong form of coordination-freedom) need more justification. The paper reads more as a well-executed position/framework paper than a deep technical contribution. For PODS, I would like to see either (a) a non-trivial decidability result for checking monotonicity in a concrete specification language, or (b) a fully rigorous subsumption of at least one of the AKNZ/Baccaert-Ketsman results with a detailed instantiation proof. As submitted, the paper is above the acceptance threshold but not comfortably so.

**Confidence:** 4/5 (I am familiar with the CALM literature and the distributed computing models involved, though I have not verified every detail of the Baccaert-Ketsman comparison.)
