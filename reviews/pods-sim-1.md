# PODS Review Simulation

## Reviewer 1 (Theory / Formal Methods)

**Overall assessment: Weak Accept**

The paper presents a clean generalization of the CALM theorem from relational transducers to arbitrary specifications over histories with declared refinement orders. The semantic criterion (monotonicity iff coordination-free) is elegant and the framework is well-designed. The applications to isolation levels, I-confluence, and CRDTs are convincing instantiations.

**Strengths:**

1. The framework is genuinely minimal: histories, Obs, Ord. The monotonicity definition is natural and the semantic equivalence is immediate from the definitions. This is a sign of good design.

2. The proper-coordination section (§4) is the most novel contribution for PODS. The ability to verify that coordination *correctly discharges* a non-monotone specification — not just detect non-monotonicity — is a real advance over CALM.

3. The interface-separation theorem (Theorem 3) is well-argued and makes a precise claim about what Complete CALM can do that relational-transducer CALM cannot.

4. The applications section is well-chosen for the PODS audience. The SI write-skew witness is concrete and the I-confluence recovery is clean.

**Weaknesses:**

1. The main theorem (Complete CALM, Theorem 1) is definitional. The paper acknowledges this ("The equivalence is definitional") but then spends significant space on the operational adequacy theorem to compensate. The question is whether the *definitions* are the right ones — and that's harder to evaluate from the theorem alone. The running example helps, but a skeptic might say: you defined coordination-freedom to mean monotonicity, then proved they're the same.

2. The operational section (§3.5) is compressed to a sketch. The demonic exposure paragraph does important work but the formal alignment between the existential correctness definition and the demonic necessity argument is still slightly uncomfortable. The paper says "angelic selection is itself a coordination strategy" — this is the key insight but it's asserted rather than proved. A formal-methods reviewer might want a lemma showing that any deterministic implementation that avoids some o ∈ Obs(H) necessarily implements a restricted interface.

3. The paper claims generality ("any concurrent setting — distributed or local") but the I/O automaton model in §3.5 is inherently multi-process. For single-threaded concurrency (e.g., coroutines, async/await), the "process responds from local state" framing doesn't directly apply. The semantic criterion still works, but the operational grounding is distribution-flavored.

4. The undecidability remark at the end of §3.6 is important but underdeveloped. If checking monotonicity is undecidable, what is the practical methodology? The paper mentions "type-level monotonicity annotations" but doesn't develop this. For PODS, where decidability/complexity is a core concern, this deserves more attention.

**Questions for the authors:**

- Can you give an example of a specification that is monotone under one choice of Ord but not another, where the "wrong" choice leads to a false positive (declares coordination-free when it shouldn't be)?
- The frontier construction (Appendix) seems like it could be a main contribution. Why is it in the appendix?
- How does the framework handle specifications with infinite outcome sets? Is there a finiteness assumption anywhere?

**Minor issues:**

- Definition 6 (Coordination-free, semantic) uses "semantically coordination-free" but the theorem just says "coordination-free." Clarify whether these are the same or different.
- The "Discussion" subsection (§3.6) feels like it belongs after the semantic theorem, not after the operational one. It discusses dividends of the semantic criterion.
- The label `sec:histories` is referenced but I don't see it defined (the subsection is "Histories and Futures" with no explicit label matching that name).

---

## Reviewer 2 (Database Systems / CALM community)

**Overall assessment: Accept**

This paper delivers on a long-standing promise: a model-free characterization of coordination-freedom that subsumes CALM, I-confluence, HATs, and CRDTs. The framework is simple (three ingredients), the main theorem is clean, and the applications are directly relevant to the PODS community. The proper-coordination contribution is genuinely new and practically important.

**Strengths:**

1. The paper solves a real problem. The CALM theorem is tied to Datalog and set inclusion; practitioners working with ordered logs, lattice-based CRDTs, or transactional isolation levels cannot directly apply it. Complete CALM provides a uniform test.

2. The proper-coordination section is the killer feature. Being able to verify that a Paxos-based log produces a monotone output interface — and that downstream consumers need no additional coordination — is exactly the kind of analysis modern data infrastructure needs.

3. The SI write-skew witness is excellent. It's concrete, well-known to the PODS audience, and demonstrates the framework's power on a real specification.

4. The Complete CAP theorem is a nice bonus. Lifting CAP from a one-directional impossibility to a bidirectional characterization is elegant, and the same-side/cross-partition distinction is technically correct.

5. The paper is well-written and well-structured. The running example carries through the entire paper effectively.

**Weaknesses:**

1. The paper is at the page limit and some sections feel compressed. The operational section is a sketch; the CALM subsumption proof is one paragraph; the CAP proof is a sketch. This is fine for a conference paper but the appendix carries a lot of weight.

2. The "demonic exposure" framing is important but may confuse readers unfamiliar with model-checking terminology. The epistemic justification ("a coordination-free process lacks the information...") is the right argument but it's buried in a paragraph rather than elevated to a principle. Consider making it a named assumption or a displayed quote.

3. The connection to Attiya et al.'s arbitration-free consistency [2023] deserves more than two sentences in related work. Their result is the closest prior work in spirit (a bidirectional characterization of available implementations). The paper should explain precisely how Complete CALM generalizes or differs from their criterion.

4. The frontier is in the appendix but referenced prominently in the abstract and contributions. This creates an expectation mismatch. Either bring a condensed version into the body or reduce its prominence in the framing.

**Questions:**

- For the transactional isolation application: does the framework handle *dynamic* isolation levels (e.g., a system that switches between SI and serializability based on workload)? Or is the specification fixed?
- The paper says "conservative (sufficient) checks based on type-level monotonicity annotations are practical and effective." Can you cite a system that does this? Hydro is mentioned in related work but not connected to this claim.

**Minor:**

- "The same analysis applies to concurrent threads on a single machine" (end of §2) — this is an important claim that deserves a brief example (e.g., two threads with a shared counter under different consistency models).

---

## Reviewer 3 (Distributed Computing / PODC-adjacent)

**Overall assessment: Weak Accept**

The paper presents a semantic characterization of coordination-freedom that generalizes CALM. The framework is clean and the semantic theorem is correct (indeed, definitional). The operational adequacy theorem is the part that connects to distributed computing, and it's now compressed to a sketch with full proof in the appendix.

**Strengths:**

1. The framework is genuinely model-free. The separation of semantic criterion from operational model is well-executed.

2. The demonic exposure principle is correctly motivated by epistemic necessity. This is the right way to think about coordination-freedom: without coordination, a process cannot be angelic.

3. The CAP generalization is interesting and the same-side/cross-partition distinction is technically sound.

4. The paper correctly identifies that the semantic theorem is the primary contribution and the operational theorem is an adequacy check. This is honest and well-framed.

**Weaknesses:**

1. The operational theorem (Theorem 2) is stated as an iff but the proof sketch is asymmetric. Sufficiency is a concrete protocol (causal-view); necessity is an informal argument about demonic exposure and indistinguishability. The full proof in the appendix should be checked carefully — the "adversary may hold the implementation to o" step is doing heavy lifting and relies on the demonic convention being accepted as the correct semantics for coordination-freedom.

2. The paper does not discuss the relationship to Fischer-Lynch-Paterson (FLP). The impossibility of consensus is a coordination requirement; does Complete CALM recover it? If so, how? If not, why not? This is a natural question for a distributed-computing reviewer.

3. The causal-view protocol assumes gossip propagation of local histories. In practice, this is expensive (state grows without bound). The paper should acknowledge that the protocol is a theoretical witness, not a practical implementation strategy. Practical implementations would use more efficient state representations (vector clocks, Bloom filters, etc.).

4. The "well-formed for the I/O model" conditions (consistency with observations, refinement coherence, response totality) are stated in §3.5 but used in the proof. Since the semantic theorem (Theorem 1) does not require them, it's unclear whether they are hypotheses of Theorem 2 only, or whether all specifications in the paper are assumed to satisfy them. The text says "All specifications in this paper are well-formed" but this should be more prominent.

5. The paper conflates "coordination" with "waiting for input." The operational definition says coordination-freedom means the response is enabled without further input. But some forms of coordination don't involve waiting (e.g., randomized protocols, speculative execution with rollback). The paper should clarify that its notion of coordination-freedom is specifically about *blocking* coordination, not all forms of inter-process communication.

**Questions:**

- Does the framework handle liveness properties (e.g., "every request eventually receives a response")? Or is it purely about safety?
- The paper mentions "fair local scheduling" in the appendix. Is this assumption necessary for the theorem, or just for the protocol's progress guarantee?
- Can you state precisely what "exposed at p" means in Definition 9 (distributed-monotone)? The current definition says "if o determines a response to an invocation event at p" — but outcomes are abstract objects, not response maps, in the semantic layer.

**Minor:**

- The paper uses both "coordination-free" and "semantically coordination-free." After the reordering, Definition 6 says "semantically coordination-free" but Theorem 1 says just "coordination-free." Pick one.
- The appendix operational proof references "by liveness" but the body renamed this to "response totality." Check consistency.
