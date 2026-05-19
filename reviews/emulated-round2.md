# Emulated PODS Reviews — Round 2

Three reviews emulating perspectives from the PODS 2026 PC.

---

## Review 1 (Reviewer perspective: Paraschos Koutris — distributed database theory)

### Summary
The paper proposes a semantic framework for characterizing coordination-freedom in concurrent systems. The main result ("Complete CALM") states that a specification admits a coordination-free implementation iff it is monotone — where monotonicity means every admissible outcome at every history has a compatible refinement at every future. The paper also introduces "distributed-monotonicity" for a CAP characterization, subsumes relational-transducer CALM, and applies the criterion to isolation levels, I-confluence, and CRDTs.

### Strengths
1. The unifying thesis is compelling. The observation that CALM, CRDTs, I-confluence, and HATs all test the same semantic property (future-stability of outcomes under refinement) is a genuine insight. The framework is clean and the running example with linearizability vs. causal consistency is well-chosen.

2. The CALM subsumption (Theorem 5.1) is precise and the proof is correct. The paper clearly shows that relational-transducer CALM is one instantiation of the general framework.

3. The "proper coordination" framing (Section 4) is the paper's most distinctive contribution beyond prior CALM work. The ability to verify that a coordinated variant's output interface is monotone — something the transducer model cannot do — is practically relevant and theoretically clean.

4. The Complete CAP result using distributed-monotonicity and partition-constrained futures is a nice formalization. The distinction between process-local non-monotonicity (resolvable without communication) and partition-spanning non-monotonicity (creating the CAP dilemma) is well-motivated.

5. The coordination-free frontier construction in the appendix is an appealing idea, and the three worked instances (register, queue, search) are suggestive of a general technique.

### Weaknesses

1. **The main theorem is essentially definitional.** The proof is two sentences: sufficiency sets R_I = A; necessity observes that condition (ii) of coordination-freedom IS monotonicity. The paper acknowledges this ("the equivalence is simple by design") but I am not fully convinced that the contribution justifies a theorem label at PODS. The real work is in the definitions and instantiations, not in the theorem itself. I would prefer the paper to frame this as: "We propose future-monotonicity as the semantic definition of coordination-freedom" and then prove representation theorems showing it captures known notions.

2. **The linearizability definition needs more care.** The paper says linearizability requires a total order "consistent with happens-before (i.e., if operation A's response causally precedes operation B's invocation, then A precedes B)." Standard Herlihy-Wing linearizability uses real-time precedence between operation intervals, not Lamport happens-before. The paper claims these coincide in the async model and cites Gilbert-Lynch, but Gilbert-Lynch's model is about atomic registers with specific client-server interaction, not about arbitrary happens-before from internal propagation messages. The witness relies on message delivery creating happens-before between writes and reads at different nodes — this is correct for the paper's model but should be stated more carefully as "linearizability in the Lamport-history model" or similar.

3. **The frontier maximality proofs are incomplete.** The register maximality proof asserts that one can construct H₂ "with causal structure such that o₂ is the only causally-consistent extension." This is a nontrivial realizability claim that is not proved. The queue maximality proof claims "any order smaller than causal FIFO must declare one of these pairs incompatible" — but a smaller order could remove refinement edges without imposing a global incompatibility. These should be either fully proved or downgraded to conjectures/observations.

4. **"Exposed at p" is too informal for the CAP theorem.** The distributed-monotone definition quantifies over outcomes "exposed at p" but this is defined only as "if o determines a response to an invocation event at p." For compound outcomes (transaction fact sets, log prefixes, CRDT states), this is ambiguous. A formal projection or local-observation function would strengthen the result.

### Minor Issues
- The "bakes in replica consistency" language about the transducer model (Section 5.1) may provoke CALM experts. Consider "studies coordination-free computation of a common output relation, so coordination-freedom and convergence are analyzed together."
- The universal construction (Appendix C) claims "zero additional rounds of distributed coordination" for stratified evaluation after membership, but stratum sealing requires waiting for all participants — many would call that coordination. The parenthetical clarification helps but the claim is still rhetorically strong.

### Questions for Authors
1. Can you give a concrete example of a specification that is distributed-monotone but not monotone? The sharded-program example is mentioned in prose but not formalized.
2. Is there a decidable fragment of specifications for which monotonicity can be checked?

### Overall Assessment
The paper has a strong conceptual contribution: identifying future-monotonicity as the semantic core of coordination-freedom across disparate models. The proper coordination framing and the CAP generalization are genuine advances. However, the main theorem's near-definitional nature and the incomplete frontier proofs weaken the technical contribution. I lean toward acceptance if the authors can (a) reframe the main theorem more honestly as a semantic definition with representation properties, and (b) either complete or soften the frontier maximality claims.

**Score: Weak Accept (borderline)**

---

## Review 2 (Reviewer perspective: Jan Van den Bussche — logic/database theory)

### Summary
This paper generalizes the CALM theorem from relational transducers to arbitrary specifications over Lamport histories. The central claim is that a specification admits coordination-free implementation iff it is "monotone" — meaning every admissible outcome at every history refines along every future. Applications to isolation levels, I-confluence, CRDTs, and CAP are developed.

### Evaluation

The paper addresses an important question: what is the semantic essence of coordination-freedom, independent of any particular computational model? The answer — future-monotonicity of outcomes under a declared refinement order — is elegant and plausible.

However, I have significant concerns about the formal content.

**The main theorem is trivial by construction.** Definition 3.6 defines coordination-free implementation as: (i) all admissible histories realized, and (ii) every outcome future-consistent. Definition 3.7 defines monotonicity as: every outcome future-consistent. The theorem says: admits coordination-free implementation iff monotone. This is (i is always satisfiable) + (ii = monotonicity). The proof is two lines. I do not object to framework papers per se, but this theorem should not be presented as a deep result. It should be presented as: "We define coordination-freedom and monotonicity so that they coincide by design. The contribution is showing this definition is the right one."

**The CALM subsumption is the strongest formal result.** Theorem 5.1 genuinely shows that the framework specializes correctly to the relational-transducer setting. The proof uses the structure of the transducer model and is not trivial. This should be more prominently featured.

**The Complete CAP theorem (Theorem 4.1) has a gap.** The impossibility direction says: if not distributed-monotone, there exists a partition and an outcome with no refinement under that partition. Then "p cannot observe the activity in S̄." But the proof does not construct indistinguishable executions — it merely asserts that p cannot observe. For a formal impossibility result, you need two executions that are locally indistinguishable at p up to the decision point, one where the dangerous future materializes and one where it does not. This is standard in distributed computing proofs (cf. Fischer-Lynch-Paterson, Gilbert-Lynch). Without it, the proof is an argument sketch, not a proof.

**The I-confluence instantiation has a modeling issue.** The paper defines conv(H) as "the state the system will inevitably reach once gossip completes." But the model explicitly says "we impose no fairness or progress assumptions" and "messages may be lost." If messages can be lost, gossip may never complete, and conv(H) is not well-defined as an inevitable state. It should be defined as a semantic closure (join of all updates in H) rather than an operational inevitability.

**The frontier construction is interesting but the maximality proofs are not rigorous.** I would accept the monotonicity halves as propositions but the maximality halves need either full proofs or honest labeling as conjectures. The register maximality in particular asserts a uniqueness property ("o₂ is the only causally-consistent extension") that requires a lemma.

### Specific Comments
- Definition 3.2 (History): the matching function μ should be partial (not all sends have matching receives, as stated in the prose). Clarify.
- The paper uses ⊑_h for the future relation but also uses ⊑ for the outcome order in some places. Ensure notation is consistent.
- Theorem 5.1 proof: the step (3)⟺(1) cites "Ameloot et al.'s Corollary 13" — please verify this is the correct corollary number in the published version.

### Overall Assessment
The paper has a good conceptual contribution but oversells its formal content. The main theorem is definitional; the CAP proof is a sketch; the frontier maximality is incomplete. The CALM subsumption and the proper-coordination framing are the strongest formal contributions. I would accept a version that (a) honestly frames the main result as a semantic definition, (b) completes the CAP proof with indistinguishability, and (c) either proves or softens the frontier claims.

**Score: Borderline (between Weak Accept and Weak Reject)**

---

## Review 3 (Reviewer perspective: Xiao Hu — algorithms/theory)

### Summary
The paper proposes a general semantic framework for reasoning about when coordination is necessary in concurrent/distributed systems. The main claim is an equivalence between "coordination-free implementation" and "monotonicity" of a specification. Several applications are developed.

### Strengths
1. Clean abstraction. The triple (histories, outcomes, refinement order) is minimal and the definitions are clear.
2. Good unification story. Showing that CALM, CRDTs, I-confluence, and HATs are all instances of one condition is valuable.
3. The running example is well-constructed. The linearizability witness with two concurrent writes and opposite reads is intuitive and correct.
4. The paper is well-written and the structure is logical.

### Weaknesses

1. **Lack of computational content.** The main theorem has a two-line proof. There is no algorithm, no complexity result, no lower bound, no construction beyond "set R_I = A." For PODS, I expect at least one technically substantial theorem. The CALM subsumption (Theorem 5.1) comes closest but is also straightforward once the instantiation is set up. The paper reads more as a position paper or survey with a unifying framework than as a technical contribution.

2. **No decidability or complexity results.** The paper mentions that checking monotonicity is undecidable in general (Rice's theorem) but does not identify any decidable fragments. For a theory venue, this is a missed opportunity. Can monotonicity be decided for finite-state specifications? For specifications given as formulas in some logic? What is the complexity of checking monotonicity for the specific instantiations (HATs, I-confluence)?

3. **The CAP result is informal.** The proof says "p cannot observe" without constructing indistinguishable executions. The availability definition is existential rather than universal. The "exposed at p" notion is informal. This is not at the level of rigor I expect for a theorem at PODS.

4. **The frontier results are the most novel but least proved.** The causal FIFO result for queues and the forward-reachability result for search structures appear to be new. But the maximality proofs are hand-wavy. If these are the paper's novel technical contributions, they need full proofs.

### Questions
1. What is the complexity of checking monotonicity for specifications given as finite automata over histories?
2. Can you give a non-trivial example where distributed-monotonicity strictly separates from monotonicity (i.e., a spec that is distributed-monotone but not monotone, with a concrete coordination mechanism that resolves the local non-monotonicity)?

### Overall Assessment
The paper has a clean conceptual contribution but insufficient technical depth for PODS. The main theorem is definitional, the CAP proof is informal, and the frontier results are incomplete. I would encourage the authors to either (a) add computational/complexity content (decidable fragments, algorithms for checking monotonicity in specific models) or (b) fully formalize the frontier results with complete proofs. As submitted, the paper is below the technical bar for PODS.

**Score: Weak Reject**

---

## Meta-Review Summary

The three reviews agree on:
- The conceptual contribution (unifying CALM/CRDTs/I-confluence/HATs under future-monotonicity) is strong and valuable.
- The main theorem is near-definitional and should be reframed.
- The frontier maximality proofs need strengthening or softening.
- The CAP proof needs more rigor (indistinguishable executions).
- The proper coordination framing is the paper's most distinctive contribution.

Split on:
- Whether the conceptual contribution alone justifies PODS acceptance (R1: yes with revisions; R2: borderline; R3: no without more technical content).
- Whether the linearizability definition is standard enough (R1 flags it; R2/R3 accept it).

Consensus recommendation: **Borderline.** The paper would benefit from (1) honest framing of the main theorem as definitional, (2) either completing or honestly softening the frontier proofs, and (3) adding one technically substantial result — either a decidability/complexity result for a fragment, or a complete proof of the CAP theorem with indistinguishable executions.
