# Review: Complete CALM: A Universal Criterion for Coordination-Freedom

**Reviewer:** Jan van den Bussche (simulated)  
**Expertise:** Expert (co-author of Ameloot et al. 2013, the paper that proved CALM)  
**Overall recommendation:** Weak Accept

## Summary

This paper proves "Complete CALM": a specification over Lamport histories admits a coordination-free implementation iff its observable outcomes are future-monotone. The paper shows this strictly generalizes the original CALM theorem (which I co-authored), exhibits a separation, proves a universal construction (one round of total-order broadcast suffices for any specification), and instantiates the criterion on isolation levels, I-confluence, and CRDTs.

## Strengths

**S1.** The main theorem is clean and the dichotomy is genuine. The formulation in terms of observable outcomes rather than program syntax is a meaningful conceptual advance. The original CALM result is indeed model-specific, and this paper correctly identifies the semantic core.

**S2.** The separation theorem (Theorem 4.2) is the paper's most interesting contribution. The observation that a correctly-coordinated system produces future-monotone output—and that syntactic analysis cannot see this—is a real insight. The stratified Datalog example makes this vivid in CALM's own setting.

**S3.** The universal construction (Theorem 4.3) is a nice structural result. The comparison with our non-obliviousness result is fair: the construction here is indeed more general (works for non-monotone specs, not just monotone ones) and does not require syntactic recognition of system relations.

**S4.** The paper is well-written and well-structured. The running example threads through effectively, and the definitions are illustrated with concrete instances.

## Weaknesses

**W1.** The main theorem (Complete CALM dichotomy) is not technically deep. The proof is short—sufficiency is a trivial construction (realize everything, expose anything), and necessity is a two-step contradiction. The intellectual content is in the *definitions* (particularly the definition of coordination-freedom as possibility preservation), not in the proof. This is not necessarily a problem for PODS, but the paper should be more upfront about where the difficulty lies.

**W2.** The definition of coordination-freedom (Definition 3.5) deserves more scrutiny. Possibility preservation ($\Poss^I = \Poss$) is a strong condition—it says the implementation never rules out *any* outcome that the specification permits along *any* admissible future. This is stronger than what most distributed systems papers mean by "coordination-free." In the transducer model, coordination-freedom means that nodes can produce output based only on local information; here it means something different (no suppression of admissible futures). The paper should discuss this gap more carefully. Is there a formal relationship between the two definitions? Does one imply the other?

**W3.** The universal construction (Theorem 4.3) has a subtle issue. The theorem says one round of total-order broadcast suffices to make the *resolved specification* future-monotone. But the resolved specification $\Spec|_I$ is defined with outcomes as *log prefixes*, not as outcomes of the original specification $\Spec$. The "Correctness" paragraph claims that any deterministic function of a prefix-monotone input inherits future-monotonicity, but this is not quite right without additional conditions on the downstream function. If the downstream function is not itself monotone in the log prefix (e.g., it computes a non-monotone aggregate), the output may not be future-monotone in the *downstream* outcome order. The paper needs to be more precise about what "downstream coordination-freedom" means here.

**W4.** The comparison with our work (Ameloot et al.) is mostly fair but slightly overstated in one respect. The claim of "robustness to membership change" is about the *mechanism* (total-order broadcast can survive view changes), not about the *theorem*. Our theorem assumes a fixed set of nodes because that is the model; the paper's theorem also assumes a fixed event universe $E$. If nodes join or leave, the event universe changes, and the theorem would need to be re-applied to the new specification. The view-change discussion is about implementation, not about the formal result.

## Minor Issues

- The paper uses "the Coordination Criterion" and "Complete CALM" interchangeably. Pick one and be consistent.
- Definition 3.4 (Implementation): the prefix-closure condition says "if $H \in \mathcal{R}_I$ and $H' \hext H$, then $H' \in \mathcal{R}_I$." This is *upward* closure, not prefix-closure. Prefix-closure would be the reverse direction. Please clarify.
- The running example uses "sequences of completed operations" as outcomes, but the formal definition of $\Obs$ is never given precisely for this example. What exactly is in $\Obs_{\mathit{lin}}(H_1)$? The empty sequence? All single-operation sequences consistent with some linearization? This matters for the witness argument.
- Theorem 4.2 (Separation) is stated existentially ("there exist specifications...") but the proof exhibits a specific witness. Consider stating it as a proposition about the specific witness and then noting the existential consequence.

## Questions for Authors

1. What is the formal relationship between your definition of coordination-freedom (possibility preservation) and the transducer-model definition (output depends only on local input)? Is one strictly stronger?
2. In the universal construction, does the downstream function need to be monotone in the log prefix for the conclusion to hold? If I compute `COUNT(*)` over the log (which is monotone) vs. `EXISTS x: NOT IN log` (which is not), do both inherit coordination-freedom?
3. The paper claims the dichotomy has "no intermediate regime." But in the transducer model, there is a spectrum based on what system relations are available (Baccaert-Ketsman). How do you reconcile this? Is the spectrum an artifact of the transducer model, or does it correspond to something in your framework?

## Verdict

The paper makes a genuine conceptual contribution: the separation from CALM is real and the universal construction is a nice structural result. The main theorem itself is not deep, but the framework and its consequences are interesting. The paper is well-written and appropriate for PODS. I recommend weak accept, contingent on addressing W2 (the relationship between the two definitions of coordination-freedom) and W3 (precision about downstream functions in the universal construction).
