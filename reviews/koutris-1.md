# Review: Complete CALM: A Universal Criterion for Coordination-Freedom

**Reviewer:** Paraschos Koutris (simulated)  
**Expertise:** Knowledgeable (parallel/distributed query processing, knows CALM literature)  
**Overall recommendation:** Accept

## Summary

The paper proves a dichotomy theorem ("Complete CALM") characterizing when a distributed specification admits a coordination-free implementation: iff its observable outcomes are future-monotone. The paper shows this strictly generalizes the CALM theorem, proves a universal construction showing one round of total-order broadcast always suffices, and instantiates the criterion on transactional isolation levels, invariant confluence, and CRDTs.

## Strengths

**S1. Clean, general result.** The dichotomy is stated at the right level of abstraction—over specifications rather than programs—and the proof is elegant. The framework is minimal (histories, observability, outcome order) yet powerful enough to capture diverse settings.

**S2. The separation is the real contribution.** The insight that coordination *discharges* non-monotonicity, producing monotone output that CALM cannot recognize, is genuinely new. The stratified Datalog example is particularly compelling because it shows the separation in CALM's own native setting. This is not just a re-notation of known results.

**S3. The universal construction is strong.** Theorem 4.3 gives a constructive upper bound that improves on Ameloot et al.'s non-obliviousness result in concrete ways (no syntactic special-casing, membership-robust). The view-change discussion makes the membership robustness concrete and convincing.

**S4. The applications are well-chosen for PODS.** Recovering the HAT/non-HAT boundary, I-confluence, and CRDT monotonicity as instances of a single test is satisfying. The write-skew witness for snapshot isolation is a nice touch.

**S5. Well-written.** The paper is readable, the running example is effective, and the definitions are motivated before they are stated. A significant improvement over the typical theory paper that front-loads definitions without intuition.

## Weaknesses

**W1. The proof of the main theorem is short.** The sufficiency direction is essentially "realize everything"—a non-constructive existence proof that doesn't say anything about how to *build* a coordination-free implementation. The necessity direction is a clean contradiction argument but not technically challenging. The paper's depth comes from the separation and universal construction, not from the dichotomy proof itself.

**W2. The applications section recovers known results.** Each application (HATs, I-confluence, CRDTs) is a known coordination boundary re-derived in the new framework. The paper does not discover any *new* coordination boundary. This is acknowledged implicitly but should be stated explicitly: the contribution is unification, not discovery.

**W3. The relationship to the "determination depth" paper (Hellerstein 2026) is unclear.** The paper cites this as providing the quantitative theory beyond the boundary, and the universal construction seems to say "depth 1 always suffices." But the cited paper apparently proves exponential depth-width separations for depth > 1. How do these reconcile? If one round always suffices (Theorem 4.3), what does depth > 1 mean? I suspect the answer is that the universal construction changes the specification (from the original to the log-based one), while determination depth measures the cost of resolving the *original* specification. But this should be made explicit.

**W4. The definition of "resolved specification" (Definition 4.1) is somewhat informal.** It says $\Spec|_I$ has "histories realized by $I$" and "$\Obs$ restricted to those histories." But $\Obs$ is defined on all of $\Hist$, not just on realized histories. Is the restriction just the domain restriction of $\Obs$? And is the event universe of $\Spec|_I$ the same as that of $\Spec$, or is it restricted? This matters for applying Complete CALM to $\Spec|_I$.

## Minor Issues

- The paper should add the universal construction to the contributions list in the introduction. Currently only three contributions are listed; the universal construction is arguably the strongest technical result.
- In the proof of Theorem 4.3, the "Correctness" paragraph is hand-wavy. "Any deterministic function of the log prefix produces an output that can only refine" needs qualification—this is true only if the function is monotone in the log prefix under the downstream outcome order.
- The CAP paragraph is interesting but feels slightly out of place in the Framework section. Consider moving it to Related Work or making it a standalone remark.
- Reference [Hellerstein 2026] for determination depth—is this published or a preprint? If it's on arxiv, say so.

## Questions for Authors

1. Does the universal construction (Theorem 4.3) contradict the determination depth hierarchy? If one round always suffices, what is the operational meaning of depth > 1?
2. Can you give an example of a specification that is *not* future-monotone but whose non-monotonicity cannot be witnessed by a finite history? Or is the witness always finite?
3. The paper focuses on safety properties. Is there a natural extension to liveness (e.g., "eventually every admitted outcome is exposed")?

## Verdict

This is a solid theory paper with a clean main result, a genuinely new separation theorem, and a strong universal construction. The applications are unifying rather than novel, but the unification is valuable. The paper is well-written and appropriate for PODS. I recommend accept.
