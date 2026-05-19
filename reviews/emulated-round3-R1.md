# Emulated PODS Review — Round 3, Reviewer 1

**Reviewer perspective: Paraschos Koutris (University of Wisconsin-Madison) — distributed database theory, CALM**

## Summary

The paper proposes "Complete CALM": a semantic characterization of coordination-freedom for arbitrary concurrent specifications. The main result states that a specification admits a correct coordination-free implementation (in the I/O automaton model) iff it is monotone — every admissible outcome at every history has a compatible refinement at every future. The paper also introduces "distributed-monotonicity" for a CAP characterization, subsumes relational-transducer CALM as a formal instance, and applies the criterion to isolation levels, I-confluence, and CRDTs.

## Strengths

1. **The operational theorem is now genuinely non-trivial.** The paper constructs a concrete protocol (the causal-view protocol) for sufficiency and uses an indistinguishability argument for necessity. This is a real distributed computing result, not a definitional equivalence. The I/O automaton grounding and the explicit response-soundness/preservation conditions make the formal story credible.

2. **The unifying thesis remains compelling.** Showing that CALM, CRDTs, I-confluence, and HATs are all instances of one condition (future-stability of outcomes under refinement) is a genuine insight. The framework is clean.

3. **The running example is excellent.** The linearizability witness (two concurrent writes, cross-delivery, opposite reads) is intuitive, correct under standard linearizability, and cleanly separates from causal consistency. This is one of the best running examples I've seen in a PODS paper.

4. **The "proper coordination" framing is distinctive.** The ability to verify that a coordinated variant's residual output interface is monotone — something the transducer model cannot do — is practically relevant. The Paxos-log and stratified-Datalog examples are well-chosen.

5. **Complete CAP with distributed-monotonicity is a nice formalization.** The distinction between process-local non-monotonicity (resolvable without communication) and partition-spanning non-monotonicity (creating the CAP dilemma) is well-motivated and the partition-constrained future definition is clean.

6. **The joint-consistency remark (Remark 1) is a clever argument.** The observation that response-compositionality follows from monotonicity (because responses are history events that constrain future admissibility) is non-obvious and resolves what initially appears to be a gap in the sufficiency proof.

## Weaknesses

1. **The necessity proof still has a subtle scope issue.** The proof constructs execution β where "the additional events in H₂ \ H₁ occur without input actions at p — either at other processes, or as consequences of prior events at p that have already been processed." The second clause ("consequences of prior events at p") is vague. What exactly are "consequences" that occur without new input? Internal actions triggered by prior state? If so, those are already determined by p's local state and don't create indistinguishability — p would produce the same internal actions in both executions. The proof should either drop this clause or make it precise.

2. **The paper is over length.** At 27 pages (body ~17, appendix ~10), the body exceeds the typical PODS 15-page limit. The operational model section (Section 3.4) adds ~1.5 pages that are essential, but something else needs to be compressed. The applications section (Section 6) could be tightened — the I-confluence and CRDT subsections are somewhat formulaic once the pattern is established.

3. **The "properly coordinated variant" definition is non-standard.** Checking monotonicity "only over admitted histories (those with non-empty Obs')" is a reasonable modeling choice, but it means the variant's monotonicity is relative to a restricted future space. This should be stated more prominently — a reader might expect monotonicity to be checked over all futures and be confused when the separation theorem's variant fails that stronger check.

4. **The frontier maximality proofs, while improved, still have a gap in the register case.** The proof constructs a history where "the only causally-consistent return value is v" by ensuring "no other write in r's causal past writes a different value." But it doesn't argue that for every removed edge in the causal order, such a forcing history exists. The argument works because all edges in the causal-prefix order correspond to appending a read, but this structural fact should be stated explicitly.

## Minor Issues

- The `\In` macro is used for "interface projection" but the macro name suggests "input." Consider renaming to `\Iface`.
- The response-totality assumption is introduced parenthetically in the proof rather than as a formal condition. It should be promoted to a numbered condition alongside response soundness and response preservation.
- The Immerman-Vardi analogy in the universal construction appendix is slightly loose — the theorem is about capturing PTIME on ordered structures, not primarily about "bounded quantification over a known domain."

## Questions for Authors

1. The operational theorem requires the specification to satisfy response soundness, response preservation, and response totality. Are there natural specifications that fail these conditions? If so, what does the framework say about them?
2. Can you give a concrete example of a specification that is distributed-monotone but not monotone — i.e., one where the Complete CALM / Complete CAP distinction is strict?

## Overall Assessment

The paper has reached a level where PODS acceptance is realistic. The operational theorem with its protocol construction and indistinguishability argument provides genuine technical content. The unification story is compelling, the running example is strong, and the proper-coordination framing is distinctive. The main concerns are length and a few remaining proof-tightness issues. I lean toward acceptance.

**Score: Accept (weak)**
