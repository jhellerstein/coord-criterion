# Simulated PODS 2027 Reviews — Round 2

Three reviewers selected: Jan van den Bussche (database theory, query languages, descriptive complexity), Dan Suciu (probabilistic databases, provenance, information theory), Andreas Pieris (knowledge representation, ontologies, tuple-generating dependencies).

---

## Review 1: Jan van den Bussche (Universiteit Hasselt)

**Expertise:** High (query languages, descriptive complexity, CALM-adjacent)

**Summary:**
The paper proves that a specification (histories → outcome sets under a refinement order) admits coordination-free implementation iff it is monotone. This "Complete CALM" generalizes the relational-transducer CALM theorem from set-inclusion on Datalog outputs to arbitrary refinement orders. The paper also proves a Complete CAP companion, subsumes I-confluence and CRDTs, and introduces a "coordination-free frontier" construction.

**Strengths:**

1. The generalization from CALM is clean and well-motivated. The three-component specification (E, Obs, Ord) is minimal and expressive. The paper correctly identifies that CALM's restriction to set-inclusion growth is unnecessary — the real content is future-consistency of outcomes under any declared order.

2. The operational adequacy theorem (Theorem 2) is the paper's most technically substantive contribution. The semantic theorem (Theorem 1) is essentially definitional, and the paper is honest about this. The operational theorem shows the semantic notion matches the standard I/O-automaton notion, which is non-trivial.

3. The applications section is effective. Recovering the HAT/non-HAT boundary, I-confluence, and CRDT monotonicity as instances of one test is satisfying. The serializability and SI witnesses are concrete and correct.

4. The frontier construction (Section 8) is novel and interesting. Recovering Mahajan et al.'s result from a purely semantic construction is a nice contribution.

**Weaknesses:**

1. The semantic theorem (Complete CALM, Theorem 1) is definitional. The paper acknowledges this ("Given our framework, this result is definitional") but still presents it as a theorem. This is a presentation choice, not a flaw, but it means the paper's novelty rests on (a) the framework itself, (b) the operational adequacy, and (c) the applications. The framework is simple — arguably too simple to be a "theorem." The real question is whether the framework is the *right* one, and the applications argue that it is.

2. The separation theorem (Theorem 3) is the weakest formal result. The proof argues that syntactic CALM cannot verify proper coordination because semantic monotonicity of Datalog^neg programs is undecidable. The Rice-style argument is correct in spirit but stated loosely — "PTIME functions" is not a standard domain for Rice's theorem (which applies to r.e. index sets). The intended meaning is clear (no algorithm decides monotonicity for all programs in an expressive class), but the formalization could be tighter. The program-boundary argument in the final paragraph is actually stronger and more novel than the undecidability point.

3. The properly-coordinated-variant definition (Definition 6) introduces a local convention (monotonicity over admitted histories) that differs from the global monotonicity definition (Definition 5, over all Hist). This is handled correctly in the text, but the asymmetry may confuse readers on first pass. A brief remark after Definition 5 noting that the global quantifier is intentional (empty-Obs futures witness coordination requirements) would help.

4. The frontier minimality proofs in the appendix are somewhat informal. The "remove any edge" argument for causal consistency works for primitive prefix-extension edges but the relationship between edge-set inclusion on a partial order and removing individual edges from a transitive closure is not fully formalized. The paper's caveat ("relative to stated interface and primitive refinement generators") is appropriate but could be more prominent.

**Minor issues:**
- The paper cites `anonymous2025coord` as a preliminary version. For blind review, ensure this does not leak authorship.
- The `\jmh` comment macro should be removed or hidden before submission.

**Questions for authors:**
- Is there a natural notion of "distance" between a non-monotone spec and its frontier element? Could this quantify "how much coordination is needed"?
- The universal construction (Theorem 4) shows ordering authority always suffices. Is there a lower bound — a spec where ordering authority is *necessary* (no weaker coordination suffices)?

**Overall assessment:** Accept with minor revisions. The paper makes a genuine contribution to database theory by providing a uniform semantic framework that subsumes several important prior results. The operational adequacy theorem and the frontier construction are the strongest technical contributions. The semantic theorem is simple but the framework is well-chosen and the applications demonstrate its reach.

**Score: 7/10 (accept)**

---

## Review 2: Dan Suciu (University of Washington)

**Expertise:** High (provenance, probabilistic databases, query evaluation)

**Summary:**
This paper generalizes the CALM theorem to arbitrary specifications over Lamport histories. The main result: a specification is coordination-free iff monotone (outcomes survive all futures under the declared refinement order). Applications recover known boundaries for transactions, I-confluence, and CRDTs.

**Strengths:**

1. The paper identifies the right abstraction. The triple (E, Obs, Ord) cleanly separates the three modeling choices, and the monotonicity condition is the natural generalization. The paper is well-written and the running example is effective.

2. The Complete CAP theorem (Theorem 5) is a nice result. The distinction between monotonicity (all futures) and distributed-monotonicity (partition-constrained futures) is clean and captures the CAP tradeoff precisely.

3. The joint-consistency remark (Remark 3) is a non-obvious insight. That independently chosen responses are jointly consistent without agreement — as a free consequence of monotonicity — is surprising and well-explained.

4. The structural lemmas in Appendix F are a good addition. They make the classical results fall out cleanly from the framework.

**Weaknesses:**

1. The paper's main theorem is essentially a definition dressed as a theorem. The real content is in the *choice* of definitions (what is a specification, what is coordination-freedom, what is monotonicity) and in showing these choices are operationally adequate. This is fine for a foundations paper, but the paper should be more explicit that the contribution is the framework + adequacy, not the semantic theorem per se.

2. The demonic exposure assumption deserves more discussion. The paper says it is "an epistemic necessity" — a coordination-free process cannot know which futures will materialize, so it cannot angelically select safe outcomes. This is convincing, but it is also a modeling choice that determines the theorem's strength. Under angelic semantics (implementation chooses which outcome to expose), the criterion would be weaker. The paper should acknowledge this more explicitly — perhaps noting that angelic implementations correspond to coordinated variants.

3. The I-confluence instantiation (Proposition 3) uses $\Obs_I(H) = \emptyset$ for invariant-violating histories. Under the global monotonicity definition, this means the spec is non-monotone whenever a future can violate the invariant — which is the desired conclusion. But the paper should verify that the "admitted histories" convention from Definition 6 does not accidentally apply here (it should not — this is the original spec, not a coordinated variant).

4. The CALM subsumption (Theorem 6) is immediate from the instantiation. The paper correctly notes this. But the claim "subsumes CALM" is slightly misleading — it subsumes the *characterization* but not the *algorithmic* content of CALM (decidability of monotonicity for specific query languages). The paper should be clearer that Complete CALM is a semantic characterization, not a decision procedure.

**Minor issues:**
- The abstract says "subsumes CALM, CRDTs, I-confluence, and HATs as instances." This is accurate but could be read as claiming to subsume the full technical content of those papers. Clarify: "recovers the coordination boundaries of..."
- Definition 4 (Implementation) defines realizable futures but is never used again in the body. It could be cut or merged into Definition 5.

**Questions for authors:**
- How does the framework handle liveness? Monotonicity is a safety property. Can you characterize when coordination is needed for progress (e.g., free termination)?
- The frontier construction assumes a fixed Obs. What happens if you allow Obs to change (weaker observations)?

**Overall assessment:** The paper is well-executed and makes a clear contribution. The framework is simple but well-chosen, and the applications demonstrate its value. The main risk is that reviewers may find the semantic theorem too simple. The operational adequacy and the applications are what make this a PODS paper rather than a workshop note.

**Score: 6.5/10 (weak accept)**

---

## Review 3: Andreas Pieris (University of Edinburgh)

**Expertise:** Medium-high (formal foundations, logic-based approaches, less familiar with distributed systems specifics)

**Summary:**
The paper proposes a semantic framework for characterizing when coordination is required in concurrent systems. The main result equates coordination-freedom with monotonicity of a specification's outcomes under a declared refinement order. The paper subsumes the CALM theorem and applies the criterion to transactions, CRDTs, and replicated data structures.

**Strengths:**

1. The paper is clearly written and well-structured. The running example effectively illustrates the key concepts before the formal development. The progression from semantic to operational to applications is logical.

2. The framework is minimal and general. The specification triple (E, Obs, Ord) is a clean abstraction that accommodates diverse computational models. The paper demonstrates this generality convincingly through the applications.

3. The operational adequacy theorem (Theorem 2) provides the necessary bridge between the semantic criterion and the standard distributed computing model. The proof sketch is clear, and the full proof in the appendix is detailed.

4. The Universal Sufficiency theorem (Theorem 4) is a nice structural result showing that coordination can always be factored into a generic ordering layer plus coordination-free evaluation.

**Weaknesses:**

1. The paper's relationship to descriptive complexity could be explored further. The separation theorem invokes Rice's theorem for PTIME functions, and the universal construction draws an analogy to the Immerman-Vardi theorem. These connections suggest deeper relationships between coordination complexity and descriptive complexity that the paper only gestures at. For a PODS audience, making these connections more precise would strengthen the contribution.

2. The frontier construction is interesting but the minimality proofs are somewhat informal. For the register case, the proof argues that removing any edge from the causal-prefix order allows constructing a forcing history. This is plausible but the argument about "primitive refinement generators" versus edges in a transitive closure could be made more precise. The paper's caveat is appropriate but the proofs would benefit from a cleaner formalization of what "removing an edge" means for a partial order.

3. The paper does not discuss decidability of monotonicity for specific specification languages beyond the brief mention in the Discussion section. For a database theory audience, concrete decidability/complexity results for natural specification languages (e.g., specifications defined by conjunctive queries, Datalog, first-order logic) would significantly strengthen the paper.

4. Some definitions could be tightened. Definition 4 (Implementation) introduces realizable futures but this concept is not used in the subsequent development — the paper works directly with the coordination-freedom definition. Either use it or remove it.

**Minor issues:**
- The paper uses both $\hext$ and $\sqsupseteq$ for the future relation in different places. Standardize.
- Theorem 5 (Complete CAP) uses "consistent, available, partition-tolerant" without defining these terms in the body. The appendix defines availability; consistency and partition-tolerance should at least be glossed in the body.

**Questions for authors:**
- Is monotonicity decidable for specifications defined by unions of conjunctive queries with set-inclusion order? This would be a natural PODS-style complexity result.
- Can the framework express temporal properties (e.g., "eventually consistent")? Or is it purely safety-oriented?

**Overall assessment:** A solid paper with a clean framework and good applications. The main theorem is simple but the framework is well-chosen and the paper demonstrates its value through diverse instantiations. The paper would be stronger with concrete decidability results for natural specification languages, but this is a direction for future work rather than a flaw. The operational adequacy and the applications make this suitable for PODS.

**Score: 6.5/10 (weak accept)**

---

## Summary

| Reviewer | Score | Verdict |
|----------|-------|---------|
| van den Bussche | 7/10 | Accept |
| Suciu | 6.5/10 | Weak accept |
| Pieris | 6.5/10 | Weak accept |

**Likely outcome:** Borderline accept. The paper would benefit from (a) being more explicit that the contribution is the framework + adequacy + applications rather than the semantic theorem alone, and (b) concrete decidability results for natural specification languages. The operational adequacy, the applications, and the frontier construction are the strongest selling points. The main risk is the "too simple" objection to the semantic theorem, which the paper partially addresses but could address more forcefully.
