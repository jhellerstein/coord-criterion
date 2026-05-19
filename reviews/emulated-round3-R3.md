# Emulated PODS Review — Round 3, Reviewer 3

**Reviewer perspective: Wim Martens (University of Bayreuth) — formal languages, logic, complexity**

## Summary

The paper proposes a general semantic framework for characterizing when coordination is necessary in concurrent/distributed systems. The main theorem states that a specification (mapping histories to outcome sets under a refinement order) admits a correct coordination-free implementation iff it is monotone. The proof uses the I/O automaton model: sufficiency constructs a "causal-view protocol," necessity uses an indistinguishability argument. Applications to CALM, isolation levels, I-confluence, CRDTs, and CAP are developed.

## Strengths

1. **Clean abstraction.** The triple (histories, outcomes, refinement order) is minimal and the definitions are clear. The event universe with interface/internal/send/receive events is well-structured.

2. **The operational theorem has real content.** Unlike earlier versions of this work (which I understand were more definitional), the current version constructs a protocol and proves an impossibility. The I/O automaton model is standard and the proof follows established distributed computing techniques.

3. **Good unification story.** Showing that CALM, CRDTs, I-confluence, and HATs are all instances of one condition is valuable for the PODS community.

4. **The running example is effective.** The linearizability witness with two concurrent writes and opposite reads is intuitive and correct.

5. **The response-soundness/preservation conditions and the joint-consistency remark are well-thought-out.** The observation that monotonicity implies joint consistency (because responses are history events) is non-obvious and important for the soundness of the sufficiency proof.

## Weaknesses

1. **No complexity results.** The paper mentions that checking monotonicity is undecidable in general but does not identify any decidable fragments or give complexity bounds for specific representations. For a theory venue like PODS, I would expect at least one computational result — e.g., the complexity of checking monotonicity for finite-state sequential objects, or for specifications given in some logical formalism. The paper gestures at this ("conservative checks based on type-level monotonicity annotations are practical") but doesn't formalize it.

2. **The paper is over length.** The body is ~17 pages against a 15-page limit. The appendix material (frontier, universal construction, CALM hierarchy) is interesting but the body needs compression.

3. **The "properly coordinated variant" definition is ad hoc.** Checking monotonicity "only over admitted histories" is a reasonable workaround for the lack of an explicit admissible-future relation in the specification model. But it means the paper's notion of "monotone variant" is non-standard and potentially confusing. A cleaner model would include admissible histories as part of the specification tuple. The current approach works but feels like a patch.

4. **The frontier results are the most novel but least rigorous.** The causal-FIFO result for queues and the forward-reachability result for search structures appear to be new. The maximality proofs are improved (explicit constructions) but still rely on assertions about "the only causally-consistent extension" that are not fully proved. If these are the paper's novel technical contributions beyond the main theorem, they need full proofs.

5. **The distinction between Complete CALM and Complete CAP is somewhat confusing.** Complete CALM uses a strong local-immediacy notion (no further input of any kind). Complete CAP uses distributed-monotonicity (only partition-constrained futures matter). The paper presents both as "Complete X" results but they use different operational notions of coordination-freedom. The relationship is stated but could be clearer — perhaps a diagram or a formal proposition relating the two.

## Minor Issues

- The abstract says "distributed-monotone—monotone with respect to remote-only futures" but the actual definition uses "partition-constrained futures" (no cross-partition message delivery), which is more specific than "remote-only."
- The paper cites Lynch 1996 for I/O automata but doesn't cite the original Lynch-Tuttle 1987 paper where the model was introduced.
- The `\In` macro (for interface projection) has a confusing name — it looks like "input" not "interface."
- Response totality should be a numbered definition, not a parenthetical in the proof.

## Questions for Authors

1. What is the complexity of checking monotonicity for specifications given as finite-state transducers (mapping input sequences to output sequences)?
2. Is there a natural specification that is distributed-monotone but not monotone? The paper claims the gap exists (process-local non-monotonicity) but doesn't give a concrete worked example.
3. The causal-view protocol propagates full local histories via gossip. What is the message complexity? Is there a more efficient coordination-free protocol for monotone specifications?

## Overall Assessment

The paper makes a solid conceptual contribution (unifying CALM/CRDTs/I-confluence/HATs under monotonicity) and now has genuine technical content (the I/O automaton theorem with construction + impossibility). The proper-coordination framing and the Complete CAP distinction are valuable. The main weaknesses are: no complexity results, over-length, and the frontier proofs being less rigorous than the main theorem. I lean toward acceptance but would like to see the page count addressed and at least one computational result (even a simple decidability observation) added.

**Score: Weak Accept (borderline)**
