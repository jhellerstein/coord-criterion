## PODS 2026 Review — "Complete CALM: A Universal Criterion for Coordination-Freedom"

**Reviewer:** Jan van den Bussche (simulated)  
**Expertise:** Expert (co-author of Ameloot et al. 2013, the formal proof of the CALM theorem for relational transducers)

---

### Summary

This paper proposes "Complete CALM," a characterization of coordination-freedom for arbitrary specifications over Lamport histories: a specification admits a coordination-free implementation iff its observable outcomes are monotone under a declared refinement order. The paper claims to strictly generalize the relational-transducer CALM theorem, to handle outcome orders beyond set inclusion (e.g., prefix extension), and to enable compositional verification that coordination correctly "discharges" non-monotonicity. Applications to transactional isolation levels, I-confluence, and CRDTs are presented as instances.

---

### Strengths

- **Clean conceptual contribution.** The shift from program-level analysis to specification-level analysis is well-motivated and clearly articulated. The paper correctly identifies that CALM operates on program syntax while the underlying phenomenon is semantic. The framework (histories, specifications, outcome orders) is elegant and minimal.

- **The running example is effective.** The replicated register example with eventual consistency vs. linearizability is pedagogically excellent. It makes the monotonicity criterion concrete before the formal machinery is introduced, and the "future-inconsistent outcome" concept is immediately intuitive.

- **Uniform recovery of known results.** The applications section (HATs, I-confluence, CRDTs) demonstrates genuine unifying power. Recovering the HAT/non-HAT boundary as a monotonicity boundary, and explaining I-confluence as a special case, is satisfying. The structural explanation (partial-order vs. total-order commitment) is insightful.

- **The separation theorem captures real architectural practice.** The observation that Paxos + downstream log consumption separates coordination-requiring internals from coordination-free output is practically important and, to my knowledge, has not been formalized this cleanly before. The stratified Datalog example (Example 4.1) is particularly apt—it shows the separation in CALM's own native setting.

- **Well-written.** The paper is clearly structured, the proof sketches are readable, and the related work is thorough and fair to prior contributions.

---

### Weaknesses

- **The subsumption claim (Theorem 4.1) has a gap in the (2)⇒(3) direction.** The proof argues: if Spec_Q is monotone, consider inputs I ⊆ J; let H_I be a "complete run on input I (reaching quiescence with output Q(I))" and let H_J "extend H_I by adding the facts J \ I as additional input events." But this conflates two things. In the transducer model, a "complete run" H_I includes all internal events (rule firings, messages, heartbeats) up to quiescence. The history H_J that extends H_I by adding new input facts is *not* simply H_I with extra input events appended—it is a different run that may interleave new derivations with old ones. The paper needs H_I ⊑_h H_J (H_J is a future of H_I), which requires that H_I is downward-closed in H_J. This is true only if the new input facts arrive *after* quiescence on I—i.e., in a "batch-then-extend" execution model. But the transducer model allows continuous, interleaved input arrival. The proof implicitly assumes a specific execution strategy (complete I first, then add J\I) that need not correspond to the general transducer semantics. This is fixable (one can argue that such an execution *exists* and monotonicity of Q is a property of the query, not of a specific run), but as stated the argument is not rigorous.

- **The definition of coordination-freedom (Definition 3.5) is arguably too strong, making the theorem easier but less useful.** Requiring *both* no history suppression *and* no outcome suppression simultaneously is a very demanding condition. In the transducer model, coordination-freedom means there exists *some* correct distributed implementation that doesn't use coordination—not that *every* outcome at *every* history must be simultaneously exposable. The paper's definition says: an implementation is coordination-free iff it realizes all admissible histories AND exposes all admissible outcomes. But a real coordination-free system might realize all histories while being selective about which outcomes it exposes (choosing one valid response among many), without this selectivity constituting "coordination." The paper acknowledges this ("a concrete execution exposes at most one outcome per history") but then requires Expose_I(H) = Obs(H) as a *set*. This conflates "any outcome is safe to choose" with "all outcomes must be simultaneously available," which are different operational requirements. The equivalence between these is precisely what monotonicity guarantees—so the theorem becomes closer to a tautology than a deep characterization.

- **The "expressivity beyond set inclusion" claim overstates the limitation of the transducer model.** The paper argues that prefix extension cannot be expressed in the transducer model without non-monotone encoding constraints (functional dependencies). But this mischaracterizes what CALM actually proves. CALM characterizes which *queries* (input→output mappings) are coordination-free, not which *output orders* are expressible. A system that maintains a growing log (a sequence) can be modeled as a transducer that outputs position-value facts {pos(i,v)}, and the *query* "output the log" is monotone (facts only accumulate). The functional dependency (each position has one value) is not a constraint the *query* must enforce—it is a property of the *input* (the ordering authority guarantees it). CALM would correctly classify the downstream log-reading query as monotone. The paper's argument confuses the specification of the *coordination layer* (non-monotone) with the specification of the *consumption layer* (monotone)—but CALM, applied to the consumption layer alone, gives the same answer as Complete CALM. The separation is real but more subtle than presented.

- **The paper does not adequately address decidability or algorithmic content.** The paper acknowledges (briefly, in one paragraph) that checking monotonicity of an arbitrary specification is undecidable, analogous to Rice's theorem. But this significantly weakens the practical contribution relative to CALM, where monotonicity of Datalog programs *is* decidable (it's a syntactic property). If the criterion cannot be checked, what is its algorithmic value? The applications all require manual proofs. The paper should discuss more carefully when and how the criterion can be mechanized, and compare this to the syntactic decidability of CALM.

- **The relationship to Ameloot-Ketsman-Neven-Zinn and Baccaert-Ketsman is asserted but not proved.** The paper claims (end of Section 4.1) that the hierarchy of models N1, N2, N3 and Baccaert-Ketsman's C-monotonicity are "likewise subsumed" and that "the instantiation is mechanical." But no formal instantiation is given—only a one-sentence sketch. Given that these results involve subtle distinctions about node knowledge, network topology, and non-deterministic behaviors, the claim of mechanical subsumption deserves at least a proposition with proof sketch, not a hand-wave. As a co-author of the N1/N2/N3 hierarchy, I would want to see the actual instantiation verified.

---

### Minor Issues

1. The abstract contains a typo: "declative" → "declarative."
2. The paper references "Hellerstein 2026" (determination complexity) as if it were a published result, but it appears to be unpublished/concurrent work. The paper should clarify the status of this reference.
3. The universal construction (Appendix C) changes the outcome domain from the original specification's outcomes to "prefix-indexed evaluation results." This is a significant semantic shift that should be flagged more prominently—the construction does not show that the *original* specification becomes monotone, but that a *different* specification (over a different outcome domain) is monotone.
4. Proposition A.1 (semantic minimality) constructs an order Ord* from observable behavior, but the proof's quotient construction is not fully rigorous—mutual reachability under ⇝ need not yield antisymmetry without additional argument.
5. The paper should cite Zinn's thesis (2015) which contains important technical details about the transducer model that are relevant to the subsumption claim.

---

### Questions for Authors

1. **On Definition 3.5:** Can you exhibit a specification that is *not* monotone but where there exists a correct implementation that realizes all admissible histories (no history suppression) while being selective about outcomes—i.e., where outcome suppression alone suffices for correctness without constituting "coordination" in any operational sense? If so, your definition of coordination-freedom may be too strong. If not, can you prove that outcome suppression always requires inter-node communication?

2. **On the (2)⇒(3) direction of Theorem 4.1:** The proof constructs H_J as an extension of H_I by "adding the facts J\I as additional input events." Can you clarify why H_I ⊑_h H_J holds in the general transducer model, where input facts may arrive at any time during a run (not only after quiescence)? Does the argument require restricting to a specific class of executions?

3. **On the Baccaert-Ketsman subsumption:** You claim their C-monotonicity "coincides with monotonicity of the specification whose admissible histories are those consistent with C." Can you provide the formal instantiation? In particular, their framework handles non-deterministic behaviors (multiple valid outputs for the same input)—how does your single-valued Obs function (which maps histories to *sets* of outcomes) capture their notion of behavioral non-determinism?

---

### Overall Assessment

The paper presents a clean and well-motivated generalization of CALM from programs to specifications. The conceptual contribution is genuine: the shift to specification-level analysis and the compositional well-coordination concept are valuable. However, the technical execution has gaps. The subsumption proof has a non-trivial issue in the (2)⇒(3) direction. The definition of coordination-freedom is arguably too strong, making the main theorem closer to a definitional equivalence than a deep characterization. The claims about subsuming the Ameloot-Ketsman-Neven-Zinn hierarchy and Baccaert-Ketsman are not substantiated with formal proofs. The "expressivity beyond set inclusion" argument, while containing a kernel of truth, overstates the limitation of the transducer model.

The paper is well-written and the applications are convincing demonstrations of unifying power. But for a venue like PODS, where the original CALM theorem was proved with full formal rigor in the transducer model, I expect the same level of rigor in a paper claiming to strictly generalize it. The current version reads more like a compelling research program than a fully rigorous technical contribution.

**Recommendation: Weak Reject**

The ideas are strong and the paper is close to acceptable, but the technical gaps—particularly in the subsumption proof and the justification of the coordination-freedom definition—need to be addressed before publication at a top theory venue. A revision that (a) fixes the (2)⇒(3) argument, (b) provides formal instantiations for the hierarchy subsumption claims, and (c) more carefully discusses the strength of the coordination-freedom definition relative to the transducer model's operational definition would likely be acceptable.
