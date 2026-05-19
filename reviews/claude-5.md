## Review: "Complete CALM: Coordination Analysis for Specifications"

This is a significantly richer paper than previous versions. Three genuine additions make it substantially stronger: Complete CAP (Section 4), the coordination-free frontier construction with three worked instances (Appendix B), and the replacement of the running example with causal consistency vs. linearizability. The paper is now technically substantive enough for PODS. Below is a detailed assessment.

---

### What Is Genuinely New and Good

**Complete CAP is the most technically interesting new result.** The bidirectional characterization — a specification admits a consistent, available, partition-tolerant implementation iff it is distributed-monotone — fills a real gap. The original CAP theorem proves only one direction (linearizability fails CAP), and Gilbert-Lynch proves impossibility for a fixed consistency model. Lifting this to a full iff over arbitrary specifications, via the clean restriction to partition-constrained futures, is the right generalization. The proof in the appendix is careful and the availability definition (Definition A.1) is precise.

**The coordination-free frontier construction is the paper's deepest technical contribution.** Asking "for a non-monotone specification, what are the strongest coordination-free weakenings?" and answering it by taking minimal monotone enlargements of the outcome order is a clean, original idea. The three worked instances are well chosen:
- The register instance recovers Mahajan et al. semantically rather than operationally — a genuine new proof technique.
- The queue instance (causal FIFO) appears to be a new result.
- The search structure instance gives the first formal explanation of the B-link tree's forward-reachability property.

All three proofs use the same structure (monotonicity + maximality), which validates the technique's generality.

**The running example upgrade from eventual consistency to causal consistency is important.** The previous witness ($r \mapsto 0$ at $H_1$ becoming stranded at $H_2$) was correct but used a trivial consistency model. The new witness — two concurrent writes at two nodes producing contradictory linearizations — directly engages with the happens-before structure and makes the non-monotonicity technically meaningful. The contrast with CC (where per-process views can differ without contradiction) is precisely what the paper needs.

**The coordination-free definition is cleaner.** Splitting into two conditions — no history suppression (i) and no outcome suppression (ii) — and making condition (ii) specification-level clarifies the architecture. The remark explaining why every outcome must be future-consistent (not just some) is essential and well-placed.

---

### Major Issues

**1. The main theorem is near-definitional, and the paper should acknowledge this explicitly.**

Definition 3.6 says an implementation is coordination-free iff (i) all admissible histories are realized and (ii) every outcome in Obs(H) is future-consistent. But condition (ii) is exactly monotonicity (Definition 3.7): a specification is monotone iff every outcome is future-consistent. So the theorem "admits a coordination-free implementation iff monotone" reduces to "there exists an I satisfying conditions (i) and (ii) iff condition (ii) holds." Condition (i) is always satisfiable by setting $\mathcal{R}_I = \mathcal{A}$, so the theorem is definitionally equivalent to "condition (ii) holds iff monotone." The proof sketch — two sentences — confirms this.

This is not fatal. Framework papers can contribute by identifying the right definitions. But a PODS reviewer who notices this will want to see it acknowledged, with the content redistributed: the contribution lies in the definition (that this correctly captures coordination-freedom), in the applications (that it characterizes known boundaries), and in the Complete CAP and frontier results (which are non-trivial). The paper currently presents the main theorem as a deep result with a proof sketching over the definitional nature. Reframe it: "The proof reduces to definitions by design — the payoff is expressive power."

**2. The frontier maximality proofs are incomplete as stated.**

The register maximality argument (Proposition B.1) constructs $H_2$ "with causal structure such that $o_2$ is the only causally-consistent extension of $o_1$ at $H_2$." This is the critical step, and it is currently asserted rather than constructed. For this to be a PODS-quality proof, you need to show explicitly how to choose the causal structure. Concretely: for two outcomes $o_1, o_2$ with $o_1 \Ord_{\mathit{causal}} o_2$ but $o_1 \not\Ord' o_2$, construct $H_2$ such that the ONLY causal-prefix extension of $o_1$ adds the specific read from $o_2 \setminus o_1$, and no other read value is causally valid at $H_2$.

The queue maximality argument has a similar gap. The proof claims "any order smaller than causal FIFO must declare one of these pairs incompatible" but this is asserted, not derived from the structure of smaller orders. Smaller orders are any partial order $\Ord' \subsetneq \Ord_{\mathit{causal-FIFO}}$, which could omit arbitrary edges. The proof should argue: for any removed edge, there exists a concrete $H_1, H_2$ pair that witnesses non-monotonicity.

The search structure maximality (Proposition B.4) is the cleanest of the three but still asserts that "any order smaller than forward-reachability must require the lookup to arrive at the exact current position." This follows from the construction, but the argument that no intermediate order exists between exact-location and forward-reachability should be made explicit.

**3. The Complete CAP proof uses undefined terminology.**

The theorem statement and the appendix proof say "correct on all causally consistent histories." But "causally consistent" is undefined in this context — it is also the name of the consistency model from the running example ($\Spec_{\mathit{cc}}$). A reviewer reading the CAP theorem will reasonably ask: "correct under the causal consistency specification?" The intended meaning is "correct under all well-formed histories" (all $H \in \mathcal{H}$). Replace "causally consistent histories" with "all well-formed histories" or "all $H \in \mathcal{H}$" throughout the CAP section and appendix.

**4. The "one round" claim in Appendix C remains imprecise.**

The remark at the end of Appendix C says "the distributed coordination depth is therefore just one round: establishing membership. After that, each stratum seal is a local commitment triggered by monotone accumulation." But the ordering service described in Theorem C.1 — "placing all input events into a total order and delivering this order identically to every replica" — is total-order broadcast, which requires ongoing consensus (one round per batch, not one round total). The paper now correctly says "The ordering service is itself ongoing coordination—it requires consensus per batch or entry," which is better. But the remark then says "the distributed coordination depth is just one round" — this contradicts the acknowledgment that the ordering service requires ongoing consensus. The remark should either be removed or scoped to: "one round is sufficient to *identify* the ordering authority; the authority's ongoing operation is the coordination."

---

### Moderate Issues

**5. The separation theorem proof is still comparing different objects.**

Theorem 4.1 says CALM "has no mechanism to certify" proper coordination. The proof shows CALM sees non-monotone Datalog operations in Paxos and reports "requires coordination." But CALM is being applied to the Paxos *program*, while Complete CALM is applied to the *output specification*. This is comparing different objects. The cleaner framing: CALM *cannot be applied* to the question Complete CALM answers (whether the output interface is coordination-free), because CALM only analyzes program text within the transducer model. The current proof correctly identifies the gap but frames it as CALM giving a wrong answer when it's actually giving an answer to a different question. One additional sentence in the proof making this explicit would help.

**6. The replica consistency section (Section 4.4) makes a claim without proof.**

The claim "if $\Ord$ admits joins and the implementation merges divergent outcomes by join, monotonicity implies convergence" is an interesting observation but is stated as fact without proof. For PODS this should either be a proposition with a proof or clearly labeled as a remark. The two-part test ("is monotone? does $\Ord$ admit joins?") is useful but its soundness should be demonstrated.

**7. The properly coordinated variant definition should state the outcome order explicitly.**

Definition 4.1 says $\Obs'(H) \subseteq \Obs(H)$ — the variant restricts outcomes but uses the same $\Ord$. This is implicit. Since $\Ord$ is a free parameter in the framework and changing $\Ord$ changes the specification, the definition should explicitly say "with the same $\Ord$" to distinguish from the frontier construction (which changes $\Ord$). The two mechanisms — restricting outcomes vs. enlarging the order — are complementary, and making this explicit would help readers understand the coordination-free frontier as the dual of properly coordinated variants.

**8. Causal consistency monotonicity proof uses a subtlety that needs to be stated.**

The proof of Proposition B.1 (monotonicity) says "no new event in $H_2$ enters the causal past of any event in $H_1$" and concludes that read values valid at $H_1$ remain valid at $H_2$. This is correct but relies on a specific implication of Definition 3.3 condition (iii): for any $r \in H_1$, the causal past of $r$ in $H_2$ equals its causal past in $H_1$ (not just that no predecessor is added — it is exactly preserved). This follows from condition (iii) together with the restriction of $\rightarrow_1$ to $E_1 \times E_1$, but the deduction is non-obvious and should be stated explicitly in the proof.

---

### Minor Issues

**Typo at line 132 of the previous version** ("monotonicity propertie") may persist in references/bib — worth checking.

**The claim that "the proof is a lifting of Ameloot et al.'s argument"** (paragraph after the proof sketch) is potentially misleading since the proof is two sentences while Ameloot et al.'s proof is technically complex. What is meant is that the *structure* of the characterization (semantic constraint = operational guarantee) is the same. Reword to: "This result recovers the structure of Ameloot et al.'s characterization in a minimalist setting."

**Table 1 (coordination mechanisms)** is a nice organizational contribution but the "strategy" column labels ("future restriction" vs. "outcome restriction") are not formally connected to the definitions. A sentence pointing back to Definition 4.1's two conditions (Obs' ⊆ Obs vs. excluding histories) would close this loop.

**The claim in Section 2 that causal consistency "is a natural frontier point—any attempt to preserve more of the total-order commitment must rule out some admissible concurrent extension"** appears in the running example section (before the frontier is defined). Either forward-reference the frontier or move this observation to Appendix B.

---

### Overall Assessment

The paper has reached a threshold where PODS acceptance is realistic. The main theorem is well-motivated even if near-definitional, and the applications validate the framework. Complete CAP is a genuine contribution that should interest both the distributed computing and database theory communities. The coordination-free frontier with its three applications — particularly the queue and search structure results — is novel and interesting.

The two most important fixes before submission: (1) shore up the frontier maximality proofs to PODS standards, and (2) resolve the CAP theorem's terminology issue ("causally consistent histories"). The near-definitional nature of the main theorem should be acknowledged rather than obscured. The remark about "one round" needs correction or removal. Everything else is presentation.