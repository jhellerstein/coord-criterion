I read the current main.tex beginning to end, including the appendices, setting aside prior versions. This draft is much cleaner and closer to final. The body now has a coherent story, and several earlier problems are no longer present. In particular, the properly coordinated variant definition now explicitly says monotone “over its admitted histories,” so the Adm(Spec') issue is resolved in the text as written.

Below is my review, split into body and appendices, followed by a prioritized punchlist.

Body feedback

Overall assessment

The body now mostly works. The main story is clear:

1. histories and futures;
2. outcomes and refinement;
3. monotonicity as future-consistency;
4. operational adequacy via I/O automata and demonic exposure;
5. proper coordination as residual monotonicity;
6. CAP/distributed-monotonicity;
7. CALM subsumption and applications;
8. frontier.

This is a much better paper than the earlier versions. The center of gravity is now the semantic result, with the operational section functioning as an adequacy bridge rather than as a second paper. That is the right balance for PODS.

The biggest remaining issues are not about the core idea. They are about a few theorem statements/proofs that are still either slightly too strong or slightly underqualified.

⸻

1. Proper coordination is now formally acceptable

The current definition says:

Spec' is monotone over its admitted histories: for all H1 ⊑ H2
with Obs'(H1) ≠ ∅ and Obs'(H2) ≠ ∅, ...

This solves the earlier concern. You do not need a separate Adm(Spec') notation unless you want it for readability. The current formulation is explicit enough.

The prose after the definition is also clear:

The coordination mechanism renders certain histories causally unreachable… the variant’s Obs' reflects this by assigning Obs'(H)=∅.

That works because the definition itself restricts monotonicity to admitted histories.

I would not reintroduce Adm unless you want a compact notation. The current text is fine.

⸻

2. The operational section is much better, but the theorem statement should mention demonic exposure

The operational section now reads well. The bridge from I/O automata to Obs is clear, and the demonic exposure paragraph is strong.

However, the theorem statement still says:

A well-formed specification Spec admits a correct coordination-free
implementation iff Spec is monotone.

Given the proof, I would add “under demonic exposure semantics” directly into the theorem statement or the preceding sentence. Otherwise the phrase “correct implementation” still sounds like ordinary existential trace refinement, while the necessity proof relies on universal/demonic exposure.

Suggested theorem wording:

Under demonic exposure semantics, a well-formed specification Spec
admits a correct coordination-free implementation of the full interface
contract iff Spec is monotone.

This is a small edit, but it prevents the most likely nitpick.

The definition of operational correctness is existential:

there exists o ∈ Obs(H) explaining the recorded responses

That is fine for trace-respect, but the necessity proof is about the full interface contract. So adding “full interface contract” to the theorem statement helps align the definition, the prose, and the proof.

⸻

3. The necessity proof sketch should avoid “implementation” ambiguity

The necessity sketch currently says:

“If o ∈ Obs(H1) is future-inconsistent … by demonic exposure the implementation must be safe when o is the operative interpretation.”

This is conceptually right. But I would add one phrase:

“of the full interface contract”

For example:

By demonic exposure, an implementation of the full interface contract
must be safe when o is the operative interpretation at H1.

That makes clear why “just avoid o” is not an implementation of the same spec.

⸻

4. The “environment may schedule” problem is mostly fixed

In the body proof sketch you now say:

An admissible continuation reaches H2

Good. That avoids implying the environment schedules response events. The appendix still has a few places where this distinction matters, discussed below.

⸻

5. Response totality and NULL

The operational bridge says:

for every invocation e in H and every o ∈ Obs(H), o(e) is defined.

This is clean, but it also means every outcome assigns a response to every invocation in the history. That is strong, but acceptable if outcomes are response interpretations.

Just make sure o(e) is always an actual response value. If there is any lingering notion of NULL, avoid it in the final text unless NULL is explicitly an ordinary distinguished response. In this draft, I did not see the earlier problematic NULL wording in the body, so this is mostly resolved.

⸻

6. Separation theorem: conceptually good, proof still invites side debate

The separation theorem currently argues:

1. a Datalog program implementing a non-monotone spec must contain negation;
2. adding coordination rules leaves negation in place;
3. syntactic CALM rejects;
4. no precise syntactic analysis can exist because semantic monotonicity of arbitrary PTIME functions is undecidable by a Rice-style argument;
5. Complete CALM bypasses this by checking the output spec.

The high-level point is good. But the proof is vulnerable in two ways:

First, the sentence

Datalog without negation cannot express non-monotone functions.

is fine, but “a non-monotone specification implemented by Datalog program P must contain negation” depends on the representation language and output encoding. It is okay in the intended Datalog setting, but reviewers may be picky.

Second, the Rice/PTIME sentence is a side fight:

determining whether an arbitrary PTIME function is monotone is undecidable
(by Rice's theorem applied to the class of PTIME-computable functions)

This needs precision. It is true in the intended “sufficiently expressive program language” sense, but “PTIME functions” plus “Rice” can trigger objections about what the program representation is, whether the time bound is syntactic, finite structures, ordered structures, etc.

My recommendation: keep the theorem, but make the proof’s center the program-boundary/interface argument, and demote the Rice point to a supporting sentence.

Something like:

Even replacing syntactic CALM by semantic program analysis would not
remove the boundary dependence: if the ordering authority is inside the
program, the program includes non-monotone validation/choice machinery;
if the authority is outside, the program is merely a monotone consumer.
For expressive Datalog^\neg transducer languages, complete semantic
monotonicity checking is undecidable in general, so there is no general
program-level repair. Complete CALM instead checks the residual
specification directly.

That preserves your point but avoids making the whole theorem rest on a Rice formulation.

⸻

7. “One round of coordination suffices” is bold but defensible

I now think your claim is correct as stated in the intended sense:

initial authority establishment is the non-monotone bootstrap; subsequent authority transitions are authorized by the current authority and can be represented as monotone extensions of the authority chain.

The remark is provocative but good. I would tweak only one sentence:

membership is configured once; everything downstream is coordination-free.

Maybe:

membership is bootstrapped once; downstream of the authority chain,
computation proceeds over a monotone ordered-prefix interface.

This keeps the strong idea while avoiding a reader misreading it as “Paxos stops coordinating after configuration.”

But this is a wording issue, not a correctness issue.

⸻

8. CAP theorem is clear in the body, but still bold

The CAP section is much improved. The distinction between same-side non-monotonicity and partition-spanning non-monotonicity is clear and important.

The proof sketch is acceptable for the body:

* distributed-monotone ⇒ causal-view plus same-side resolution;
* not distributed-monotone ⇒ expose/withhold dilemma.

I would only add the same “full interface contract / demonic exposure” phrase to the necessity direction:

Under demonic exposure of the full interface contract, if p exposes o...

The theorem is bold, but the body now explains the scope well enough.

⸻

9. CRDT proof is fixed

The CRDT proof now starts from a chosen o ∈ Obs(H) and constructs o' by applying additional updates/merges. That fixes the quantifier issue. Good.

⸻

10. Frontier body claim is acceptable, but the proof sketch is very strong

The body’s register frontier proof sketch says removing any edge from Ord_causal allows constructing a history where that removed refinement is the only valid extension. This is a strong claim, and the full proof in the appendix needs to carry it.

The body caveat says the appendix develops analogous frontier results and the proof is a sketch, so this is acceptable. If page pressure exists, the frontier section remains a candidate for compression, but it is not broken.

⸻

Appendix feedback

Appendix A: Operational adequacy

The sufficiency proof is good and aligns with the body.

The joint-consistency subsection is clear and useful.

The necessity proof is mostly aligned with the demonic-interface reading. This sentence is good:

Correctness here is the full demonic interface contract...

That solves the biggest earlier concern.

Two things to tighten:

A.1 Clarify existence of the exposing response

The proof says:

Let r = resp(e,v) be the response event exposing o at H1

This assumes every future-inconsistent outcome has a response exposure. That is consistent with the body’s “modeling discipline” and response-oriented bridge, but it is not independently formalized here.

I think this is acceptable given the paper’s stance, but if you want a one-sentence safeguard:

Because the operational theorem applies to well-formed response interfaces,
future-inconsistent outcomes are interface exposures; let r be the
response event exposing o.

This would close the last formal gap in the appendix proof.

A.2 H_2^r construction is now present

Good. The proof explicitly constructs H_2^r and uses:

Obs(H_2^r) ⊆ Obs(H_2)

That fixes the previous post-response-history issue.

⸻

Appendix B: CAP formal proof

The CAP proof is serviceable but still the least formal of the major appendices.

B.1 Availability definition is semantic/existential

The definition says:

if some P-extension contains invocation+response and Obs(H) ≠ ∅,
there exists an execution of I in which a response is emitted.

You correctly call this “semantic availability.” Good.

But the theorem statement says:

correct on all well-formed histories and maximally available under all partitions

This is okay, but readers may compare it to standard CAP availability. Keep the explanatory paragraph. I might add:

This is the weakest availability condition needed for the semantic
characterization; stronger fair-execution formulations imply it.

B.2 Sufficiency still slightly hand-wavy

The proof says same-side non-monotonicities are resolved by intra-component coordination. This is right, but it could use one more sentence:

Within each connected component of the partition, the implementation may
run any coordinated resolver for the component-local residual spec; CAP
availability forbids waiting across components, not coordination within one.

That would make the construction clearer.

B.3 Necessity should use response extension if necessary

The CAP necessity proof says if p exposes o, then in β the system reaches H_2 where no outcome refines o. As in Appendix A, if the exposure response is not already in H_2, the actual history is H_2^r.

You can either rely on Appendix A’s argument by reference or add a parenthetical:

As in Appendix A, if exposing o adds a response event r, evaluate the
future at H_2^r; response events only restrict Obs.

This would avoid a repeated nitpick.

⸻

Appendix C: Frontier

This appendix is interesting but technically the shakiest part after CAP.

C.1 General caveat is excellent

You added:

The maximality arguments are relative to the stated interface and
primitive refinement generators...

This is very helpful. It makes the frontier results read as calibrated examples rather than universal uniqueness theorems.

C.2 Register maximality proof still has a weak point

The proof says:

Since o2 extends o1 by appending at least one operation—call it r ↦ v
(a read returning v).

But an arbitrary missing edge in a prefix-extension order may append a write, or a block of operations, not necessarily a read. The parenthetical says writes are always appendable and the critical case is a forced read, but the proof should be phrased in terms of primitive generator edges.

Given your caveat, a safer version:

It suffices to consider primitive generator edges that append a single
read response, since write-only extensions do not constrain observations
and composite edges factor through primitive ones.

Then the construction works.

C.3 Queue maximality proof has a similar generator issue

The proof assumes every removed edge corresponds to appending one element. If Ord' removes a composite prefix edge but retains all one-step append edges, transitive closure may still recover the composite relation depending on whether Ord' is a partial order and transitive. Since Ord' must be a partial order, edge-set inclusion is a little tricky: “removing an edge” from a transitive relation may force removing many implied edges or violate transitivity.

This is not fatal, but it means the appendix should talk about “primitive refinement generators” rather than arbitrary edges in a transitive closure. Your caveat gestures at this; I would make it explicit in the proof.

C.4 Search frontier proof is the least rigorous

The search proof says:

Let Ord' be any order smaller than set inclusion...
there exist outcomes o1 ⊂ o2 with (k,p) ∈ o2 \ o1 but o1 not Ord' o2.

Then it constructs a lookup adding (k,p).

This is okay as intuition, but “no weaker order suffices” is very broad. If the frontier proof is not central, the caveat may suffice. If you want it robust, explicitly limit to the primitive set-inclusion generator that adds one lookup fact.

Suggested global appendix phrasing:

For frontier minimality, we compare orders by their primitive refinement
generators; the partial order is the reflexive-transitive closure of
these generators. Minimality below means no primitive generator used by
the stated frontier can be removed while preserving monotonicity.

That would make the three proofs cleaner.

⸻

Appendix D: Universal construction

This appendix is good and now carefully qualified.

What works:

* It says the ordering service is ongoing coordination.
* It distinguishes residual interface from restriction variant.
* It explains membership/authority.
* It acknowledges the ordering service requires consensus.

The strongest paragraph is the membership-change discussion:

current authority uses its decision-making power to admit new members or appoint successors.

That supports your “one bootstrap” claim well.

One wording tweak:

No distributed coordination is needed beyond knowing who the participants are (membership).

In the stratified Datalog remark, this is okay because you immediately clarify monotone waits over known participants. But a reviewer might still object that waiting for end-of-data signals is distributed synchronization. You already say “zero additional rounds … in the sense of resolving incompatible futures.” Good. I would leave it.

⸻

Appendix E: CALM hierarchy

This appendix is useful and short.

The phrase:

with the admitted history space restricted...

is now consistent with the proper-coordination convention. Good.

No major concerns.

⸻

Appendix F: Classical coordination requirements

This appendix is a nice synthesis, but the lemmas are somewhat schematic.

F.1 Total-order commitment lemma may be too broad

The lemma says if outcomes are total orders and the event universe admits two concurrent events, then the spec is not monotone. That is true only if future histories can force the opposite order through observations. The proof adds an e3 “only consistent with e2 < e1,” but not every total-order spec necessarily has such a forcing event.

To be precise, the lemma needs a condition:

and the specification admits a future observation that can force either
ordering of concurrent events.

Or call the lemma:

Total-order commitment with order-revealing futures is non-monotone

This is appendix-only, but worth fixing if you want the table to be defensible.

F.2 Bounded-cardinality lemma likewise needs “requiring distinct value”

The proof assumes the new candidate requires a distinct value. The statement says “event universe admits more than k distinguishable candidates,” which may be enough, but I would phrase it as:

admits a future that introduces a (k+1)-st candidate that must be assigned
a value distinct from all previous candidates.

This makes the lemma match the proof.

F.3 Table is useful

The table is good as explanatory synthesis. I would not overinvest unless the appendix becomes a focus of review.

⸻

Punchlist

High priority

1. Add “under demonic exposure / full interface contract” to Theorem 3.4’s statement.
    The theorem currently says “admits a correct coordination-free implementation iff monotone.” Add the semantic qualifier directly to prevent angelic-refinement readings.
2. Tighten the separation theorem proof.
    Keep the Rice/undecidability point, but scope it carefully to expressive Datalog^\neg transducer languages and foreground the program-boundary/interface argument. The current PTIME/Rice sentence is the most likely body-level proof nitpick.
3. In Appendix A, add one sentence justifying the response exposure r = resp(e,v) for arbitrary future-inconsistent o.
    This aligns the necessity proof with the response-interface scope.
4. In Appendix B, make CAP sufficiency more explicit.
    Add the connected-component resolver construction and clarify that CAP forbids cross-partition waiting, not intra-component coordination.
5. Fix Appendix F lemmas to include their needed forcing assumptions.
    The current total-order and bounded-cardinality lemmas are too broad as stated.

Medium priority

6. Adjust the operational theorem proof sketch wording in the body.
    Add “full interface contract” to the necessity paragraph and avoid any possible existential-correctness reading.
7. Qualify “membership is configured once; everything downstream is coordination-free.”
    Preserve the strong authority-chain point, but phrase it as downstream of the authority/order interface.
8. Refine frontier minimality proofs around primitive refinement generators.
    The current “remove any edge” language is risky for transitive partial orders. State minimality relative to primitive generators.
9. Add H_2^r parenthetical to CAP necessity proof.
    Appendix A has it; CAP should either reference it or repeat it briefly.
10. Check all uses of “environment schedules” versus “interface admits continuation.”
    The current body is mostly good; appendices should match.

Low priority

11. Consider softening “new results for queues and search structures.”
    The frontier claims are interesting but partly illustrative; avoid sounding too sweeping.
12. Clean theorem/proposition labels if any changed during edits.
    thm:separation is fine if it remains a theorem; otherwise rename.
13. Check page-breaking/orphan/widow layout after final cuts.
14. Review bibliography exactness for newer references.
    Especially Baccaert/Ketsman 2026 and Li/Lee 2025, make sure titles/venues/arXiv metadata are correct.
15. Do one final grep for stale terminology.
    E_in, “adversary schedules response,” “angelic,” “Adm,” old labels, etc.

Bottom line

The body is close. The most important body-level correction is theorem/proof wording around demonic exposure and a more careful separation proof. The appendices are useful but need a defensive polish pass, especially CAP, frontier minimality, and the structural lemmas.