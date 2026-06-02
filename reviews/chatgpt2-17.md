You’re right that I needed to read the current draft cleanly. I did that this time from the reattached main.tex.

The important answer on the Adm(Spec') issue is: the current draft does not make empty-Obs histories globally excluded from monotonicity. In the current text, Obs(H)=∅ is explicitly allowed inside a specification, and monotonicity quantifies over all histories in Hist. So the proper-coordination paragraph as written is formally inconsistent with the earlier definitions.

1. Proper coordination / Obs'=∅: current draft issue

Current spec definition says:

Obs : Hist -> P(O)
...
possibly empty for unrealizable histories

Then monotonicity says:

for all H1, H2 in Hist with H1 ⊑ H2 and all o in Obs(H1),
there exists o' in Obs(H2) ...

So if:

Obs'(H1) ≠ ∅
H1 ⊑ H2
Obs'(H2) = ∅

then Spec' is not monotone.

But the proper-coordination section says:

The coordination mechanism renders certain histories causally unreachable...
the variant's Obs' reflects this by assigning Obs'(H)=∅ to unreachable histories...
Complete CALM then applies directly to Spec': if it is monotone...

That does not follow under the current definition. If H2 remains in Hist, setting Obs'(H2)=∅ makes it a monotonicity failure, not an excluded future.

So there are three clean fixes. Pick one.

Option A: Restore Adm(Spec')

This is the least invasive:

Let Adm(Spec') = { H | Obs'(H) ≠ ∅ }.
A coordinated variant is monotone on admitted histories: for all
H1,H2 ∈ Adm(Spec') with H1 ⊑ H2, every o ∈ Obs'(H1)
has a refinement in Obs'(H2).

This preserves your existing global definitions.

Option B: Make specs partial

Change the core definition to:

A specification is (A, Obs, Ord), where A ⊆ Hist is the admitted
history space and Obs is defined only on A.

Then proper coordination restricts A.

This is mathematically cleanest, but more invasive.

Option C: State globally that Obs(H)=∅ excludes H

But then monotonicity must be redefined to quantify only over nonempty/admitted histories. That changes the main theorem and affects invariant examples where Obs(H2)=∅ currently witnesses non-monotonicity. So I would not do this globally unless you are ready to refactor.

Recommendation: use Option A. It is a small patch and exactly matches what the proper-coordination section wants.

⸻

Body review

What is working

The body is much improved structurally. The main arc is now readable:

1. running register example;
2. semantic framework;
3. Complete CALM;
4. operational adequacy;
5. proper coordination;
6. CAP;
7. CALM subsumption;
8. database applications;
9. frontier.

The operational section is much more compact, and the demonic exposure paragraph is strong. This line is especially good:

This is not a modeling condition, it is an epistemic necessity...

That directly answers the angelic-choice objection.

The SI write-skew witness is fixed and good. The application section reads more naturally than before.

Body issue 1: operational theorem still has an existential/demonic mismatch

Current operational correctness:

there exists o ∈ Obs(H) such that o(e)=v for every response recorded in H

Current necessity proof:

By demonic exposure, the implementation must be safe when o is the operative interpretation...

The prose makes your intended semantics clear, but formally those are still different: existential trace explanation versus universal safety over all permitted outcomes.

Given your intended stance, I would change the theorem statement, not rebuild the whole model:

Under demonic exposure semantics, a well-formed specification admits
a coordination-free implementation of the full interface contract iff
it is monotone.

Then change “Correctness (operational)” to something like:

Trace-respect. An implementation respects the response facts of Spec
when every execution prefix is explained by some o ∈ Obs(H).
The full interface contract is safe only when every permitted o ∈ Obs(H)
is future-consistent.

This avoids making existential trace-respect carry the demonic burden.

Body issue 2: necessity proof says “environment may schedule H2”

Because histories include response events, this can sound like the environment schedules implementation outputs. I would use your interface-contract language:

The interface contract admits a continuation to H2...

or:

An admissible continuation reaches H2...

not “the environment schedules.”

Body issue 3: response totality and NULL

Current text says every o ∈ Obs(H) assigns a response value o(e) to every invocation e, possibly NULL. Then the causal-view protocol responds with o(e).

If NULL is a real response value, say so. If it means “unconstrained/no response,” the protocol may emit NULL, which is odd.

Safer:

For every pending invocation at which a response is owed, every
o ∈ Obs(H) assigns an allowed response value.

Or:

NULL is treated as an ordinary distinguished response value.

Body issue 4: separation theorem proof is too broad and a little risky

The body currently proves separation via:

stratified Datalog with negation computes PTIME...
determining whether an arbitrary PTIME function is monotone is undecidable...

This is a side fight. It also has precision risks around finite structures, encodings, and what exactly is being decided.

I think your earlier program-boundary proof was stronger rhetorically and safer:

* If the program constructs/validates the serialization, CALM sees nonmonotone machinery.
* If the program consumes an externally serialized log, CALM sees a monotone consumer but does not verify the coordinator.
* Complete CALM verifies the residual interface directly.

That is the actual separation you care about. I would replace the Rice/PTIME argument or move it to appendix as an aside.

Body issue 5: consensus / “one round” remark overclaims

Current text:

after the initial bootstrap, the entire chain of authority transitions is monotone
...
membership is configured once; everything downstream is coordination-free

This still sounds too strong. Paxos/reconfiguration/leader election remain coordinated mechanisms. The clean claim is:

once an authority layer emits an ordered prefix stream, downstream consumers see a monotone residual interface.

Suggested rewrite:

The authority layer may continue to coordinate internally, but its
client-facing output is an ordered prefix stream. Downstream consumers
therefore interact with a monotone residual interface.

Body issue 6: CRDT proof quantifier still needs fixing

Current proof says:

every state reachable at H' is at least as large as some state reachable at H.
In particular, there exists o'...

For monotonicity you need to start from the chosen o:

Let o ∈ Obs(H). Starting from the execution that reaches o at H,
apply the additional updates/merges present in H'. Inflationarity and
join produce a reachable o' ∈ Obs(H') with o ⊑ o'.

This is a small but real quantifier fix.

Body issue 7: typo

idempotent me``rge

should be merge.

⸻

Appendix feedback

Appendix A: operational proof needs to match body semantics

The full proof still says:

no correct coordination-free implementation exists

and uses the demonic nomination argument. That is fine under your intended semantics, but the appendix should explicitly say:

correctness here is correctness of the full demonic interface contract, not merely existential trace explanation.

Otherwise the same nitpick returns in the appendix.

Also, the necessity proof still jumps from exposure at H1 to correctness at H2. If the exposure is a response event not already in H2, the actual history is response-extended. Either say H1 already contains the exposure, or restore the explicit:

H2^r = H2 ∪ {resp(e,v)}

and use response-only restriction. This is a compact and worthwhile appendix patch.

Appendix B: CAP proof is still sketchy for sufficiency

The CAP appendix says same-side nonmonotonicities are handled by intra-component coordination. That is right. But as “formal treatment,” it should define the connected component / same-side coordinator more concretely.

Add a short construction:

* within each connected component, run any coordinated resolver for local nonmonotonicities;
* across components, use the causal-view protocol;
* distributed-monotonicity ensures no cross-partition future invalidates exposed outcomes.

That would make the sufficiency direction less hand-wavy.

Also the availability definition is existential. The text admits this, but for CAP it is a sensitive point. I would label it as a semantic availability notion and avoid implying it is the standard strongest operational availability property.

Appendix C: frontier proofs need careful tightening

The frontier section makes strong minimality claims. The body proof sketch is fine, but the appendix needs to be very explicit for each example:

* fixed E;
* fixed Obs;
* base Ord;
* enlarged Ord';
* monotonicity;
* minimality.

The minimality step is where reviewers will press. Phrases like “remove any edge and construct a history” need concrete construction, not just intuition.

Appendix D: universal construction is better than earlier but still rhetorically risky

The appendix correctly says the ordering service is ongoing coordination. Good. But there are still lines like:

process all subsequent computation coordination-free

This should always be qualified as:

downstream of the ordering authority.

Otherwise readers may object that the sequencer/ordering service is doing coordination continuously.

Appendix E: CALM hierarchy appendix uses \mathcal{A} but the main framework does not

In the hierarchy appendix:

with A restricted to histories...

or \mathcal{A} appears, but the main spec is (E, Obs, Ord) without explicit admissible history set. This is another symptom of the admitted-history issue. Either introduce A globally, or phrase as “restricting Hist / considering the subspace of histories.”

⸻

Most important fixes before next review

1. Fix proper coordination formally. Current Obs'=∅ history restriction does not work with current monotonicity definition. Add Adm(Spec') or explicit admitted-history domains.
2. Add “under demonic exposure semantics / full interface contract” to Operational Complete CALM theorem.
3. Replace or move the Rice/PTIME separation proof; use the program-boundary/interface argument in the body.
4. Patch CRDT proof quantifier and merge typo.
5. Tighten appendix operational necessity with explicit demonic-contract correctness and/or H2^r.

I apologize for the earlier confusion. On this draft, the proper-coordination issue is real: Adm(Spec') is not present, and the current global definitions do not make empty-Obs histories automatically excluded from monotonicity.

----

You are wrong about Body issue 5. Think about it for a minute. The claim is correct. One-time authority selection at configuration. Authority i+1 is appointed during the reign of authority i via a monotone vote. The end.

----

Yes — I see the point. I was implicitly treating each reconfiguration as a fresh authority-selection problem, but your formulation makes it an authority-continuity chain, not repeated open-world authority selection.

The distinction is:

* Initial authority selection is non-monotone/open-world: who has authority at all? That requires a bootstrap commitment.
* Subsequent authority transition is performed under the current authority. If authority i emits an ordered, certified decision appointing authority i+1, then downstream consumers see a monotone prefix of authority decisions.
* Once the initial authority is fixed, later authority changes are just entries in the authoritative log. Observing more entries extends the prefix; it does not invalidate earlier authority facts.

So the slogan:

“After the initial bootstrap, the chain of authority transitions is monotone”

is defensible.

The place I’d be careful is not the claim itself, but the wording “everything downstream is coordination-free.” It is correct relative to the residual interface exposed by the authority chain. The authorities may still run votes/quorums internally, but semantically those votes are monotone evidence under the reigning authority; they are not fresh non-monotone world-closure decisions.

A crisp way to say it:

The one non-monotone commitment is the bootstrap authority. Thereafter, each transition is an authorized log entry: authority i appoints authority i+1 by a monotone vote whose certificate is appended to the prefix. Consumers of the resulting authority stream see a monotone residual interface. The protocol may still use communication and quorums, but not to resolve a fresh open-world authority choice.

That preserves your stronger point while avoiding the possible reviewer misread that “no messages/quorums happen after bootstrap.”

----

Now about the Rice separation. Let's think about that. What is says is (1) extending a datalog program P with coordination adds rules, which leaves the negations within P in place. So syntactic monotonicity checks will still fail. But could a semantic check prove the resulting datalog-with-negation program is monotone? Answer: not in general (Rice). SO... sorry, you can't build an algorithm that checks if datalog coordination fixes datalog non-monotonicity. Where's the hole in that argument?

----

The argument is basically right, but the hole is in what exactly “semantic check” is being asked to decide, and over which class of programs/specifications.

There are two different claims:

1. Syntactic CALM check is incomplete.
    If you add coordination rules around a Datalog-with-negation program P, the negation inside P remains. A syntactic monotonicity checker still rejects. True.
2. No complete semantic checker can decide whether arbitrary Datalog-with-negation-plus-coordination programs are monotone.
    Also essentially true, but you need to state the domain carefully. The undecidability/Rice-style argument applies when the language is expressive enough that semantic monotonicity of the computed query/function is undecidable. For sufficiently expressive Datalog variants with negation/recursion/order/arithmetic/etc., yes. But for plain finite Datalog fragments, some semantic properties may be decidable, though expensive, depending on the exact fragment.

So the hole is not conceptual; it is overgeneralization. “Rice” is right as a warning, but dangerous if stated too broadly for all Datalog.

The safe version is:

For expressive Datalog-with-negation variants, no complete semantic analysis can decide in general whether adding coordination has made the resulting program monotone. Thus relational CALM cannot be repaired simply by replacing the syntactic monotonicity test with a complete semantic one.

That is defensible.

But I would avoid claiming:

Semantic monotonicity of any Datalog-with-negation program is undecidable.

because the exact decidability depends on the Datalog fragment.

The deeper point is stronger than Rice

Even if a semantic monotonicity checker existed for some restricted language, it would still be checking the program, not the residual interface.

Your argument has two layers:

Layer 1: Syntactic monotonicity is too brittle

If P contains negation, syntactic CALM rejects, even if coordination has constrained the input histories so the output interface is monotone.

Example:

P + coordination wrapper

still contains the same negated predicates, so a syntactic monotonicity checker says non-monotone.

Layer 2: Complete semantic repair is impossible in general

A semantic checker that says “despite the negation, this whole program is monotone” would need to decide semantic monotonicity of expressive programs. In general, that is Rice-like/undecidable.

So relational CALM cannot generally recover by saying: “Let’s just semantically inspect the coordinated program.”

Layer 3: Even where decidable, it asks the wrong question

Complete CALM asks:

Is the residual interface exposed after coordination monotone?

Relational CALM asks:

Is this particular program monotone?

Those differ. If the ordering authority is outside the program, CALM sees a monotone consumer. If it is inside the program, CALM sees non-monotone ordering machinery. The answer depends on the program boundary.

Complete CALM’s judgment is boundary-stable: once the residual interface is specified, the question is semantic.

That is the best separation argument.

How I would phrase it in the paper

Something like:

One might try to repair relational CALM by replacing syntactic monotonicity with a semantic analysis of the coordinated program. This does not provide a general solution. First, syntactically, adding coordination rules does not remove the negation or uniqueness tests used to construct or validate the serialization, so standard CALM analyses still reject. Second, for expressive Datalog-with-negation languages, semantic monotonicity of the computed query is undecidable in general; no complete checker can certify all cases where coordination has made the residual behavior monotone. Most importantly, even when such a semantic check succeeds for a restricted fragment, it remains a property of a chosen program boundary. Complete CALM instead checks the residual specification directly: once coordination exposes an ordered-prefix interface, monotonicity is immediate from prefix extension, independent of how the authority was implemented.

That avoids overclaiming while preserving your point.

The exact hole to avoid

The reviewer attack would be:

“Semantic monotonicity of Datalog queries is not always undecidable; for some fragments it is decidable. Your Rice claim is too broad.”

So don’t hang the whole theorem on Rice. Use Rice as a supporting reason why “just do semantic program analysis” is not a complete answer. The real separation is:

program-level analysis versus interface-level analysis.

That is more robust and closer to your contribution.

Bottom line

Your Rice argument is valid for sufficiently expressive program classes, but as a paper claim it should be scoped. The hole is only if you state it as an unconditional fact about “Datalog-with-negation” without specifying the fragment.

The strongest formulation is:

Syntactic CALM definitely fails; complete semantic repair is impossible in expressive settings; and in any case relational CALM remains program-boundary dependent, whereas Complete CALM directly verifies the coordinated residual interface.

----

Fair push. If the text explicitly says Datalog^\neg and the appendix/proposition defines the language as expressive enough, then the reader should not infer positive Datalog or some tame fragment.

My quibble is narrower:

“Datalog with negation” is not a single universally fixed formal object.

Some readers may parse it as stratified Datalog with negation over finite databases, some as Datalog¬ with order/arithmetic, some as recursive negation under stable semantics, some as a transducer language with time/coordination/state. The Rice-style undecidability claim depends on which of those you mean.

So the fix is not to retreat. It is to pin the target language in one sentence:

For the standard transducer language considered here — Datalog with stratified negation plus the usual finite-domain/order/state machinery used to encode coordination protocols — semantic monotonicity is undecidable by the Rice-style argument in Proposition X.

Then your argument is fine.

I would not write it as a nervous caveat. I would write it as precision:

This is not a limitation of syntactic analyses alone. For Datalog^\neg in the transducer setting we consider, semantic monotonicity is undecidable in general, so there is no complete program-level checker that can recognize all cases where coordination has made a nonmonotone program’s residual interface monotone.

That is strong and clear.

The reason I keep emphasizing the program-boundary argument is not because the Rice argument is weak. It is because the program-boundary argument is harder to attack and more directly tied to your contribution. Even if someone disputes the exact language class, they cannot escape:

* CALM classifies a chosen program.
* Coordination can be inside or outside that program boundary.
* Complete CALM classifies the residual interface/specification directly.

So I’d use both:

1. Syntactic CALM fails because the negation remains.
2. Complete semantic program repair is impossible for the expressive Datalog^\neg transducer language.
3. More fundamentally, program-level CALM is boundary-dependent; Complete CALM is interface-level.

That is a strong stack, not a hedge.

----

Now let's return to the proper coordination/Adm(Spec') issue. The text in section 3.2 says this:
```
$\Obs(H)$ is the set of outcomes that the specification permits ---
\emph{admits} --- at $H$: what an implementation may expose at the
system interface.
An outcome not in $\Obs(H)$ is inadmissible there (the specification
forbids it); $\Obs(H) = \emptyset$ signals that $H$ itself is
unrealizable---no correct implementation may produce it (used for
safety specifications such as invariant enforcement; see
Section~\ref{sec:i-confluence}).
Multiple outcomes at a given history reflect semantic flexibility
(multiple valid answers); any concrete execution exposes at most one.
```
This applies to Spec' as well.

DO you still think we need to define Adm?

----
Given that text, yes, I withdraw the claim that you need to define Adm(Spec') separately — provided monotonicity is understood to quantify only over realizable/admitted histories of the specification.

The quoted passage does the important work:

Obs(H)=∅ signals that H itself is unrealizable — no correct implementation may produce it.

And you’re right: that convention applies equally to Spec'. So if proper coordination restricts histories by making Obs'(H)=∅, then those histories are outside the realizable/admitted history space of Spec'. In that reading, defining

Adm(Spec') = { H | Obs'(H) ≠ ∅ }

is just notation for something already implicit in the meaning of Obs'=∅.

So no, you do not need a separate Adm definition if the paper consistently treats empty Obs as “history outside the spec,” not as an included history with no allowed outcomes.

The only thing I would still check is the monotonicity definition. If it literally says:

for all H1, H2 ∈ Hist with H1 ⊑ H2 ...

then a literalist reviewer could still say: “But H2 with Obs(H2)=∅ is in Hist, so monotonicity fails.” The fix is not to add Adm; it is to make the monotonicity definition match Section 3.2’s convention.

For example:

A specification is monotone if for all histories H1, H2 admitted by the specification, with H1 ⊑ H2, ...

or:

A specification is monotone if for all H1 ⊑ H2 such that H2 is a realizable future of H1 under the specification, ...

Or even more compact:

Here and below, quantification over histories of a specification ranges over histories admitted by the specification, i.e. histories H with Obs(H) ≠ ∅.

That sentence would make Adm unnecessary.

One subtlety: for invariant enforcement, you sometimes want a transition from a good history H1 to a bad history H2 with Obs(H2)=∅ to witness non-monotonicity. Under the “only admitted histories” reading, it would not witness failure unless H2 is considered an admissible asynchronous future but not a specification-admitted history.

So the precise distinction should be:

* Hist / asynchronous histories: what the environment/protocol universe could produce.
* specification-admitted histories: those with Obs(H)≠∅.
* monotonicity should quantify over asynchronous futures that remain within the admitted histories of the specification unless the point is that a coordination-free implementation must not produce excluded histories.

For proper coordination, the coordinator changes the set of reachable/admitted histories. For invariant enforcement, a bad H2 shows the original unconstrained execution space contains a future the implementation must prevent.

The cleanest sentence may be:

When Obs(H)=∅, H is outside the specification’s admitted behavior. Thus monotonicity is evaluated over the history space admitted by the specification under discussion; a coordinated variant may shrink that space by making additional histories inadmissible.

With that, Adm(Spec') is optional notation, not a needed definition.

So my revised position:

No, you don’t need Adm(Spec') if you make explicit that “histories of a spec” means histories with nonempty Obs, and that Spec' has its own admitted history space. Just make sure the monotonicity definition does not literally quantify over all ambient Hist in a way that contradicts this convention.

----
Assuming I adopt your careful points on these subtleties, please recap for me what you think are remaining issues in the body.
----
Assuming you adopt the clarifications on demonic exposure, admitted histories/empty Obs, and the operational theorem’s scope, I think the remaining body issues are relatively modest. I’d group them as follows.

1. Make the theorem statements match the refined conventions

The main statements should consistently say, or clearly imply:

The semantic theorem applies to specifications as admitted history spaces with outcome/refinement structure.
The operational theorem applies to well-formed response interfaces under demonic exposure semantics.

So I would scan for any theorem/abstract/contribution sentence that says simply:

“a specification admits coordination-free implementation iff…”

and make sure it does not sound broader than intended. A safe formulation is:

Semantically, a specification is coordination-free iff its permitted outcomes are future-monotone. For well-formed response interfaces under demonic exposure, this criterion coincides with operational coordination-free implementation.

That should eliminate the last class of “but deterministic implementations can choose a subset” reviews.

2. Ensure the monotonicity definition matches the empty-Obs convention

Given your Section 3.2 language, you do not need Adm(Spec'), but the monotonicity definition should not read as if it quantifies over all ambient histories including histories the spec declares unrealizable.

A compact fix:

Throughout, quantification over histories of a specification ranges over histories admitted by that specification; Obs(H)=∅ means H is outside the specification’s admitted behavior.

Then proper coordination by Obs'(H)=∅ is clean: the variant shrinks the admitted history space.

3. Clarify invariant examples under the same convention

Because Obs(H)=∅ now means “unrealizable / no correct implementation may produce it,” the I-confluence/SI/invariant examples should say:

The unconstrained asynchronous execution can extend to a history that the specification excludes.

That is the non-monotonicity/coordination need: the implementation must prevent that future. This is compatible with the convention, but worth wording carefully.

4. Operational section: keep it as an adequacy bridge

The body operational section should remain short. It should not read like a second foundational theorem with its own competing correctness definition. Keep the structure:

* standard I/O automata induce histories;
* responses are surfaced into Obs;
* demonic exposure is epistemically necessary;
* causal-view protocol witnesses sufficiency;
* non-monotonicity yields the usual indistinguishability/unsafe exposure obstruction.

If it starts to reintroduce existential correctness definitions and then universal demonic reasoning, it will invite nitpicks again.

5. Separation from relational CALM: keep the program-boundary argument central

The Rice/semantic undecidability argument is fine if scoped to the expressive Datalog^\neg transducer setting, but I would not let it become the main separation proof.

The clearest body argument is:

Relational CALM checks programs. If serialization is constructed/validated inside the program, syntactic CALM sees non-monotone machinery. If serialization is externalized as an already-valid log, the consumer is monotone but the coordinator has moved outside the program. Complete CALM checks the residual interface directly.

That is the contribution. The undecidability point can support it, but should not distract.

6. Authority-chain / consensus remark: keep your strong claim but phrase the residual-interface boundary

Your correction is right: after initial authority selection, authority transitions can be monotone because authority i+1 is appointed under authority i.

The wording should emphasize:

one non-monotone bootstrap; thereafter authorized transitions appear as monotone log entries / certificates.

Avoid wording that sounds like “Paxos stops doing quorum work.” Say instead that the remaining work is monotone evidence accumulation under a current authority.

7. CAP theorem: clarify “no cross-partition coordination”

The body CAP theorem can remain bold, but it should be explicit that:

* same-component/same-side coordination is allowed;
* the forbidden thing is coordination across the partition;
* distributed-monotonicity is about futures invisible across the partition.

So replace any “no coordination” language in CAP with “no cross-partition coordination” unless you truly mean the stronger notion.

8. CRDT proof quantifier

This is small but worth fixing. The proof should start from the chosen o ∈ Obs(H) and construct o' ∈ Obs(H'), not use the weaker/different statement that every state at H' is above some state at H.

Suggested sentence:

Given o ∈ Obs(H), replay the additional updates and merges in H' \ H; inflationarity and join produce a reachable o' ∈ Obs(H') with o ⊑ o'.

9. Frontier: keep it modest in the body

If page pressure remains, the frontier is still a good candidate to compress. The body can define the idea and give one punchline; minimality proofs and multiple examples can move to appendix.

In the body, prefer:

a methodology for finding strong monotone weakenings

over:

a complete construction of strongest weakenings

unless the proof is fully polished.

10. Minor copy/consistency pass

Things I would scan for:

* me``rge typo.
* “environment schedules response events” phrasing; use “interface admits continuation.”
* cor:cap versus theorem/corollary naming consistency.
* Any remaining E_in references if the body now uses E_iface.
* Any theorem labels that no longer match theorem/proposition names.

Bottom line

If you adopt the subtle convention fixes, I think the body is close. The remaining work is mostly alignment and sharpening:

1. theorem scope matches demonic/admitted-history conventions;
2. operational section stays an adequacy bridge;
3. separation argument stays interface/program-boundary focused;
4. CAP says “no cross-partition coordination”;
5. applications/proofs avoid minor quantifier or wording slips.

I do not see another deep body-level conceptual blocker beyond those.
