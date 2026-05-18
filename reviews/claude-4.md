## Review: "Complete CALM: A Universal Criterion for Coordination-Freedom"

**Venue:** PODS (Principles of Database Systems)
**Recommendation:** Major Revision

---

### Summary

The paper proposes "Complete CALM," a generalization of the CALM theorem from relational transducers and Datalog to arbitrary input/output specifications over Lamport histories with user-defined refinement orders. The central claim is: a specification admits a coordination-free implementation iff its observable outcomes are monotone under the declared order. The authors additionally claim formal subsumption of relational-transducer CALM, expressivity beyond set inclusion, compositional well-coordination, and uniform recovery of HAT/non-HAT boundaries, I-confluence, and CRDTs.

---

### Strengths

1. **Genuine conceptual contribution.** Lifting CALM from program syntax to semantic specifications is the right move, and the framework is cleanly formulated. The separation of *whether* coordination is needed (a property of the specification) from *how* authority mechanisms fail (CAP, operational concerns) is articulated more crisply here than anywhere else in the literature.

2. **The separation theorem is the strongest result.** Theorem 4 (and Example 6, the stratified Datalog case) correctly identifies something CALM cannot do: certify that a coordination mechanism *correctly discharges* non-monotonicity, leaving a monotone residual. This is genuinely useful and not adequately captured by prior work.

3. **Uniform recovery of known boundaries.** Section 5 is effective. Showing HAT levels, I-confluence, and CRDTs as instances of one semantic test is a good scholarly contribution, even if each individual recovery is not surprising.

4. **Writing quality.** The paper is unusually well-written for a theory submission. The running example is pedagogically strong and the proof sketches are honest about what they are.

---

### Weaknesses and Required Revisions

#### W1 — The Main Theorem is Essentially Trivial Given the Definitions (Major)

The proof of Theorem 1 (Complete CALM) is acknowledged to be short "by design," but the paper undersells the problem this creates: the theorem is close to a tautology given how coordination-freedom and monotonicity are defined.

- **Coordination-freedom** is defined as: no history suppression AND no outcome suppression AND irretractability.
- **Monotonicity** is defined as: every outcome at H₁ has a refinement at every future H₂.

Given these definitions, the sufficiency direction is a one-liner (set R_I = A and Expose_I = Obs; irretractability holds by monotonicity), and necessity is a two-line contradiction. The definitions are essentially *designed* so that the theorem holds. This is not a criticism of the result's importance—but PODS reviewers will ask: **what is the non-trivial content?**

The authors should either (a) demonstrate that alternative, operationally natural definitions of coordination-freedom do *not* collapse in this way (i.e., show the definitions are the *only* reasonable ones leading to the equivalence), or (b) acknowledge more forthrightly that the contribution lies in identifying the *right definitions* rather than in the theorem's proof.

The analogy the authors draw to Rice's theorem is apt and should be developed earlier and more prominently—it sets appropriate expectations.

#### W2 — Subsumption Proof Has a Gap (Major)

Theorem 2 (Subsumption of CALM) claims equivalence of three conditions. The direction (1) ↔ (3) is delegated to Ameloot et al.'s Corollary 13, which is fine. The directions (3) → (2) and (2) → (3) are proved in the paper.

The (2) → (3) direction has a subtle issue. The construction of H_J from H_I assumes that after quiescence on input I, the additional facts J \ I "arrive as new input events, causally after all events in H_I." But in the transducer model, nodes receive input facts at potentially different times and in different orders—there is no global quiescence signal. The paper needs to argue more carefully that the constructed H_J is a valid history in the transducer model's sense, particularly that downward-closure is satisfied. As stated, the construction seems to assume a sequential delivery model that may not match Ameloot et al.'s asynchronous transducer semantics.

#### W3 — The "Well-Coordination" Concept Needs Sharper Treatment (Moderate)

Definition 7 (well-coordination) is the key new concept enabling the separation theorem, but it receives insufficient development. Specifically:

- **Compositionality claims are informal.** The introduction promises "compositional verification" but the paper never states a compositionality theorem. The separation result shows well-coordination can be *checked*, not that it *composes*. If a system consists of a coordination layer feeding a downstream processor, is the composition well-coordinated? Under what conditions? This seems tractable to state formally.

- **The definition depends on R_I being a valid restriction.** Not every candidate I satisfying Definition 6 (coordination mechanism) will produce a useful resolved specification—the restriction might be so severe that Obs_I is trivially monotone. The paper should discuss what makes a coordination mechanism "appropriate" or "tight."

#### W4 — Comparison with Baccaert-Ketsman is Incomplete (Moderate)

The paper claims Baccaert and Ketsman's generalized CALM is subsumed (Section 4.1 and Related Work), but the argument is a sketch ("their C-monotonicity coincides with monotonicity of the specification whose admissible histories are those consistent with C"). This claim needs a proof or at minimum a precise statement. The Baccaert-Ketsman framework involves *behaviors* (not just queries) and non-deterministic transducers—the mapping to the present framework's history spaces is not obvious. Similarly for the N₁/N₂/N₃ hierarchy; Proposition 1 (N₃) is stated but its proof sketch delegates the main step to Ameloot et al. Theorem 20, and the domain-independence condition is introduced without sufficient justification of why it cannot be absorbed into the history-space restriction.

#### W5 — Undecidability Discussion is Underdeveloped (Minor)

The paper notes that checking monotonicity of an arbitrary specification is not decidable "analogous to Rice's theorem." This is stated informally and without proof. For a PODS submission, this deserves at minimum a precise statement: what is the input representation? Over what class of specifications? A brief but formal argument (or citation to where such an argument would apply) would strengthen the paper.

#### W6 — The Universal Construction (Appendix C) Smuggles In a New Outcome Domain (Minor)

Theorem 5 (Universal sufficiency of ordering authority) is important but the proof notes that the construction "does not preserve arbitrary original observation interfaces; it constructs a monotone interface exposing the deterministic evaluation of each log prefix." This is a significant qualification: the resolved specification has a *different* outcome domain than the original. The theorem therefore does not show that every specification can be made coordination-free at its *own* level of abstraction—it shows that every specification can be *compiled* into a different, coordination-free specification. This distinction should be stated explicitly in the theorem statement, not buried in the proof.

---

### Specific Technical Comments

- **Definition 3 (Implementation):** The computability requirement ("there exists an effective procedure") is invoked nowhere in the proofs. If it is load-bearing, its role should be demonstrated; if not, it should be dropped or moved to a remark.

- **Definition 5 (Coordination-free):** Condition (ii) requires Expose_I(H) = Obs(H) for all H ∈ A(H_in). This is a strong requirement—it demands that *every* permitted outcome be safely exposable, not merely that *some* be. The paper argues this is the right definition (any outcome must be safe regardless of which future materializes), but an alternative definition requiring ∃o ∈ Obs(H) that is safely exposable might also be defensible and would lead to a different (potentially weaker) theorem. The authors should acknowledge this design choice.

- **Example 5 (Coordination in the register):** This example concludes that "no coordination-free implementation of Spec_lin can satisfy irretractability." But the argument assumes Expose_I(H₁) must include ⟨w(1), r ↦ 0⟩ because condition (ii) requires Expose_I = Obs. A referee could ask: why can't a coordination-free implementation simply choose not to expose ⟨w(1), r ↦ 0⟩ at H₁? The answer is condition (ii)—but this circularity makes the example feel like it is just restating the definitions rather than illuminating them.

- **Proposition 2 (HAT levels are monotone):** The proof for monotonic reads states that a read value "consistent with monotonic-reads at H remains so at H'." This needs more care. The monotonic-reads constraint is a *session* property (successive reads by the same session are non-decreasing). Extending the history adds new reads. The paper needs to argue that no new read added in H' can retroactively violate the ordering constraint for reads already in H. As stated, the proof is incomplete.

- **Remark (Local depth, Appendix C):** The claim that "the distributed coordination depth is therefore just one round: establishing membership" is interesting but unproven. It implicitly assumes that stratum sealing reduces to monotone accumulation of signals from known participants—but this seems to require that no stratum produces facts that are *inputs* to a prior stratum (i.e., stratification must be strictly forward). Please state this assumption explicitly.

---

### Presentation

- The paper describes itself as proving a result "for the distributed systems or programming-language settings where the insight could have the most impact," but Section 5 (Applications) is entirely about *database* settings (isolation levels, I-confluence, CRDTs). The distributed computing applications are relegated to Appendix D, and even there, the consensus example refers to an "extended version" that does not appear in the submission. This is a tension the paper should address: either broaden Section 5 or adjust the framing.

- Proposition 1 in Section 4.1 (Subsumption of N₃) is labeled as referring to "thm:calm-subsumption" in the proof, but the theorem numbering calls it Theorem 2 in the main text. The LaTeX label is inconsistent.

- The Related Work section mentions Li and Lee [2025] and Baccaert and Ketsman [2026]—one of these citations is to a work that postdates typical PODS submission windows. Please verify these are accessible (published or available as preprints) and clarify their status.

---

### Summary of Required Changes

| Priority | Issue |
|----------|-------|
| Major | Clarify the non-trivial content of Theorem 1 given the definitions |
| Major | Fix the gap in the (2) → (3) direction of Theorem 2 |
| Moderate | State and prove a compositionality theorem, or retract the claim |
| Moderate | Complete the Baccaert-Ketsman subsumption argument |
| Minor | Fix the monotonic-reads proof in Proposition 2 |
| Minor | State Theorem 5 correctly (new outcome domain) |
| Minor | Drop or motivate the computability requirement in Definition 3 |

---

### Overall Assessment

This is a well-motivated paper with a genuine contribution—the separation theorem and the framework for well-coordination are new and useful. However, the main theorem is weaker than advertised (nearly definitional), several claimed subsumptions are insufficiently proved, and the compositionality promise in the introduction is not delivered. A major revision addressing W1–W4 would yield a solid PODS paper.