## Review: "Complete CALM: A Universal Criterion for Coordination-Freedom"

This paper argues for moving coordination analysis from the program level (CALM) to the specification level, proving that a specification admits a coordination-free implementation if and only if its observable outcomes are monotone. The framing is clean, the running example is well-chosen, and the recovery of HATs, I-confluence, and CRDTs as instances of one test is satisfying. Nevertheless, several issues require attention before this is ready for PODS.

---

### The Central Technical Gap: The Outcome Order Is a Free Parameter

This is the most important issue in the paper. The outcome order $\Ord$ is declared as "part of the specification" and monotonicity is defined relative to it. But Remark 3.1 acknowledges that if $\Ord$ is too coarse, "genuine conflicts disappear and no specification requires coordination." This observation is allowed to pass without resolution.

The consequence is that Complete CALM, as stated, is nearly vacuous: for any specification $(E, \Obs, \Ord)$ that fails to be monotone, one can choose a coarser $\Ord$ (e.g., a top element refining every outcome) and declare the specification monotone. Conversely, the minimality result in Appendix B constructs a tautological order from the implementation's observable behavior and concludes "the specification is monotone under $\Ord^*$" — but $\Ord^*$ is defined to make this true. This circular construction does not show that the *declared* $\Ord$ is necessary, only that some order always exists.

The paper needs a formal theory of when an outcome order is *faithful* to the specification's intent. Without this, the theorem has no bite: every specification is "monotone under some order" and every specification "fails to be monotone under some other order." A PODS reviewer will ask: for a given specification, what selects the canonical $\Ord$, and is the theorem nontrivial with respect to it? The register example handles this gracefully (prefix extension is natural), but the general answer is missing.

---

### The Definition of Coordination-Freedom Is Potentially Too Strong

Definition 3.6 requires $\Poss^I_{H_{in}}(H) = \Poss_{H_{in}}(H)$: every outcome reachable under *any* admissible extension must remain reachable under the implementation. The admissible histories include those with arbitrary message losses, indefinite delays, and Byzantine interleaving.

This requirement means an implementation that resends dropped messages, applies timeouts, or restricts message reordering is potentially "coordinating" — it has suppressed some admissible histories (those where messages are lost forever or arrive out-of-order). Yet none of these mechanisms are what the CALM literature means by coordination. The definition conflates *suppression of admissible futures* (what the paper calls coordination) with *blocking* (making one thread wait for another, the operational cost CALM cares about). These are different: a single-node serializable database using locking blocks but may not suppress admissible futures if the specification permits only serializable outcomes to begin with.

This needs either a more careful operational definition of "admissible histories" (perhaps restricting to fair executions, or to those respecting some reliability model) or an explicit argument that the conflation is intentional and harmless for the claims being made.

---

### The Main Theorem Is Too Easy for PODS

Once the definitions are in place, the proof of sufficiency is a single sentence: realize all admissible histories and expose any admissible outcome; monotonicity guarantees no stranding. The necessity direction is two cases of contradiction. For a PODS theory submission, reviewers will ask: where is the hard part?

The technical difficulty should appear somewhere — either in the definitions (formalizing the right notion of specification and coordination-freedom), in the applications (proving that HAT levels are monotone requires going through each level carefully), or in the separation theorem (showing CALM genuinely cannot answer the question Complete CALM answers, not just that they're applied to different objects). Currently none of these are developed to PODS depth.

The paper reads more like a *framework paper* (organizing known results under one umbrella) than a *theorem paper* (proving something technically difficult). Framework papers can be excellent PODS contributions, but they need either very tight formalization or more substantial technical content in the applications.

---

### The Separation Theorem Compares Apples to Oranges

Theorem 4.2 says Complete CALM "correctly identifies coordination-free behavior that CALM cannot recognize." The proof exhibits a Paxos-based system where Complete CALM finds the *output specification* monotone while CALM finds the *program text* non-monotone. But these are different objects: of course they give different answers — they're being applied to different things.

The claim should be sharpened: it's not that CALM *fails* on the same question; it's that CALM *cannot even ask* the question Complete CALM answers. The right framing is: the question "is the output of this coordinated system monotone?" is not expressible in CALM's framework, and Complete CALM provides the machinery to ask and answer it. As written, a reviewer might respond: "CALM was never designed to analyze composed output specifications, so this isn't a failure of CALM." The contribution is real but needs to be characterized more precisely.

Similarly, the stratified Datalog example (Example 4.4) is good but the claim "CALM cannot distinguish... before sealing and... after sealing" would be stronger with a formal statement about what CALM can and cannot express.

---

### The Universal Construction Has an Acknowledged Tension It Doesn't Resolve

Theorem 4.3 shows that membership establishment makes all remaining computation "coordination-free" because inputs from known participants can be accumulated monotonically. But this construction requires every node to *wait* for inputs from all members of $\mathsf{All}$ before evaluating. Waiting for all participants is a barrier synchronization — operationally expensive and availability-limiting in the same way as other coordination protocols.

Remark 3.7 acknowledges this: "each stratum seal is a local commitment triggered by monotone accumulation of signals from known participants." The remark calls this "zero additional rounds of distributed coordination" but it is not zero cost — it is one rendezvous per stratum. The distinction between "distributed coordination" and "barrier synchronization" is doing a lot of work here and needs formal grounding, or the claim needs to be weakened.

---

### Proposition 4.5 (HAT Levels Are Monotone) Is Unproved

This is one of the paper's key instantiation results and it is stated as a proposition with only a restatement as proof. Session guarantees (monotonic reads, read your writes, writes follow reads) are particularly non-trivial: whether each is monotone depends on how outcomes are defined, what counts as "invalidating" a previously exposed fact, and how session state is represented in histories. A PODS reviewer will expect a proof that actually engages with each level. The current "proof" — "extending a history may add committed transactions but cannot invalidate" — asserts the conclusion.

---

### Moderate Issues

**The relationship to CALM is stated but not fully demonstrated.** Section 4.1 says "CALM is an instance of Complete CALM under a natural modeling choice" and lists the choices. But showing CALM is an *instance* requires showing that CALM's notion of coordination-freedom (nodes can reach consistent answers using only local information) implies and is implied by Complete CALM's notion (possibility preservation). The derivation is sketched but the equivalence is not proved. In particular, CALM requires that *each individual node* can compute its answer locally — Complete CALM allows implementation-dependent coordination among nodes. These are genuinely different requirements.

**The broken LaTeX reference** in Section 3.3: "The universal construction (Section~`ef{sec:universal-construction}`)" should be `\ref{sec:universal-construction}`.

**"Coordination Criterion" vs. "Complete CALM."** The paper uses both names for the same result. Section 4.1 refers to "the Coordination Criterion" in several places while the theorem is called "Complete CALM." Pick one name and use it consistently.

**The minimality proof in Appendix B** constructs $\Ord^*$ from the implementation's observable behavior and concludes the specification is monotone under $\Ord^*$. This says nothing about whether the specification is monotone under its *declared* $\Ord$ — which is the order that matters for whether the system is actually well-coordinated. The proposition as stated shows "if a coordination-free implementation exists, then *some* order makes the specification monotone" — but this is not the same as "monotonicity of the declared order is necessary." Fix the claim or fix the proof.

---

### Minor Issues

**The Paxos universal construction example conflates coordination rounds.** Paxos requires two phases (prepare and accept), so using it as an example of "one round" of membership establishment is at best imprecise. The "one round" claim refers to a simpler membership-authority protocol, not Paxos.

**The applications section would benefit from a negative example within each domain** — not just showing monotone cases are coordination-free, but showing a specific non-monotone specification and explaining which future-inconsistent outcome witnesses it. The serializability witness (Section 4.5 Proposition 4.6) is good; similar witnesses for I-confluence failure and CRDT reset should appear.

**The CAP discussion** at the end of Section 3.4 is well-written but would be strengthened by a formal claim. Currently it is descriptive: "CAP's operational content is that authority mechanisms have failure modes under partitions." A one-sentence formal consequence would help: e.g., "if the required authority mechanism becomes unavailable, the implementation must choose between violating possibility preservation and blocking."

---

### Overall Assessment

The paper has genuine conceptual value: identifying that CALM's limitation is program-level analysis rather than specification-level analysis, and providing a framework that correctly handles the post-coordination regime. The separation theorem and the recovery of HATs/I-confluence/CRDTs under one umbrella are appealing. The writing is clear and the running example is effective.

For PODS acceptance, the paper needs: (1) a formal treatment of the outcome order selection problem — without this, the main theorem is not well-defined; (2) a proper proof of Proposition 4.5 (HAT levels); (3) either a strengthened minimality result or a retraction of the minimality claim; and (4) more careful treatment of the separation theorem's claim about CALM's limitations. The definition of coordination-freedom also deserves scrutiny: as stated it may be too strong to capture the intended notion.