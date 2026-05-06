# Review: Complete CALM: A Universal Criterion for Coordination-Freedom

**Reviewer:** Andreas Pieris (simulated)  
**Expertise:** Knowledgeable (database theory, Datalog, ontological reasoning)  
**Overall recommendation:** Weak Accept

## Summary

The paper introduces "Complete CALM," a dichotomy theorem stating that a specification admits a coordination-free implementation iff it is future-monotone. The framework uses Lamport histories with an arbitrary refinement order on outcomes. The paper shows CALM is an instance, proves a strict separation, gives a universal construction (one round of total-order broadcast suffices), and applies the criterion to isolation levels, I-confluence, and CRDTs.

## Strengths

**S1. The dichotomy is clean and general.** The formulation abstracts away from specific computational models and captures the essence of coordination in a model-independent way. The theorem statement is simple and memorable.

**S2. The separation from CALM is convincing.** The stratified Datalog example (Example 4.1) is the strongest argument in the paper: it shows the separation in CALM's own language, making it impossible to dismiss as "different model, different result." The observation that sealing a stratum produces monotone output is simple but was not previously formalized.

**S3. The universal construction improves on Ameloot et al.** The two concrete advantages (no syntactic special-casing, membership robustness) are genuine. The view-change argument is well-explained.

**S4. Good use of running example.** The replicated register with EC vs. linearizability is simple enough to follow but rich enough to illustrate all definitions.

## Weaknesses

**W1. The formal framework lacks some precision that a PODS paper should have.**

Several points where the definitions are not fully rigorous:

(a) Definition 3.2 (History): The paper says "for every receive $r \in E$ there exists a unique send $s \in E$ with $s \rightarrow r$." But $\rightarrow$ is defined as a strict partial order on *all* of $E$, not just on send-receive pairs. The condition should say that $s$ is the *unique* send such that $s \rightarrow r$ *and* $s$ is matched to $r$ (via some matching function). As stated, any send that happens-before $r$ would satisfy the condition.

(b) Definition 3.3 (Specification): $\Obs$ maps histories to *nonempty* sets of outcomes. But what about histories where no outcome is admissible (e.g., an inconsistent history that violates the specification)? Should $\Obs(H) = \emptyset$ be allowed? The non-emptiness assumption is used implicitly in the proof but never justified.

(c) Definition 3.5 (Coordination-free): The condition $\Poss^I = \Poss$ quantifies over all $H \in \mathcal{R}_I(H_{\mathit{in}})$. But what if $\mathcal{R}_I(H_{\mathit{in}}) = \mathcal{A}(H_{\mathit{in}})$? Then the condition is trivially satisfied (both sides are the same union). The sufficiency proof exploits exactly this: set $\mathcal{R}_I = \mathcal{A}$ and you're done. This makes the sufficiency direction feel tautological—the "implementation" that witnesses coordination-freedom is one that does nothing (realizes everything). Is this really an implementation?

**W2. The proof of the main theorem has a gap in the necessity direction.**

The argument says: "Any coordination-free implementation must realize both $H_1$ and $H_2$." But this is not immediate from the definition. Coordination-freedom says $\Poss^I = \Poss$ for all $H \in \mathcal{R}_I$. It does *not* say $\mathcal{R}_I = \mathcal{A}$. A coordination-free implementation could in principle have $\mathcal{R}_I \subsetneq \mathcal{A}$ as long as $\Poss^I = \Poss$ at every realized history. The proof needs to argue that if $H_2 \notin \mathcal{R}_I$, then $\Poss^I(H_1) \subsetneq \Poss(H_1)$ (because outcomes arising only along $H_2$ would be missing). This argument is present in the PODC version but compressed out here. Please restore it.

**W3. The "dichotomy" framing is somewhat misleading.**

A dichotomy theorem in the PODS sense (e.g., Bulatov-Zhuk for CSP, Dalvi-Suciu for probabilistic queries) classifies a *parameterized family* of problems: for each parameter value, the problem is either tractable or hard. Here, the "parameter" is the specification, and the "classification" is coordination-free vs. coordination-requiring. But unlike CSP dichotomy, there is no complexity-theoretic content—the classification is a semantic property (future-monotonicity), not a computational one. Calling it a "dichotomy" is technically correct (it's a complete binary classification) but may set expectations that the paper doesn't meet. I'd suggest either (a) explaining how this differs from complexity-theoretic dichotomies, or (b) using "characterization" instead.

**W4. The applications do not yield new results.**

Each application (Propositions 5.1–5.4) recovers a known boundary. The paper's value here is unification, not discovery. This is fine, but the paper should be explicit about it. A stronger version would identify at least one *new* coordination boundary that was not previously known—a specification where the coordination requirement was unclear and Complete CALM resolves it.

## Minor Issues

- The paper uses $\hext$ (with subscript $h$) for the future relation but also uses $\sqsupseteq_h$ in one place (line 833). Be consistent.
- Example 3.1 says "a send event $s$ at $p$ propagating the write (in $E_{\mathit{send}}$), with $w \rightarrow s$." But $w$ is an input event (client write invocation) and $s$ is a send event. Is $w \rightarrow s$ part of the happens-before relation because of program order at $p$? This should be stated.
- The I-confluence application (Section 5.2) defines outcomes as "sets of database states" ordered by set inclusion. But set inclusion on *sets of states* means "refinement = ruling out states" (fewer states = more refined). This is the *reverse* of the usual intuition (more information = more refined). A sentence acknowledging this would help.
- Theorem 4.3 (universal construction): the proof says "all input events are submitted to a sequencer." But in the framework, input events are *external*—they are not under the implementation's control. How does the implementation "submit" them? This conflates the implementation's internal mechanism with the specification's event structure.

## Questions for Authors

1. In the necessity proof, can you make explicit why $H_2 \notin \mathcal{R}_I$ implies $\Poss^I(H_1) \subsetneq \Poss(H_1)$?
2. Is there a specification whose coordination status was previously unknown that Complete CALM resolves?
3. The sufficiency construction realizes all admissible histories. Is there a *non-trivial* coordination-free implementation for any future-monotone specification—one that doesn't simply "do nothing"?

## Verdict

The paper presents a clean characterization theorem with a genuine separation from CALM and a useful universal construction. The framework is elegant and the paper is well-written. However, some formal details need tightening (W1, W2), and the "dichotomy" framing slightly oversells the result (W3). I recommend weak accept, contingent on fixing the proof gap in W2 and clarifying the formal issues in W1.
