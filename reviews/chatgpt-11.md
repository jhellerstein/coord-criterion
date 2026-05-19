I checked the current main.tex directly. Your summary is accurate on several points: the CAP theorem has been genuinely reframed around distributed-monotonicity, the old orphan proof block is not present, labels/refs look clean, \rightsquigarrow/\Poss are gone, and the Datalog-prefix claim is softened in both the main statement and appendix proof.

But I do not think all issues are resolved. The remaining problems are now more focused. The biggest one is still the running example.

High-level judgment

The paper is much more stable than before. The Complete CALM theorem, proper coordination framing, CALM instantiation, and distributed-monotonicity/CAP move are now coherent.

However, I would not yet submit without addressing two issues:

1. The SC/CC running example is still formally fragile.
2. The frontier appendix still overclaims maximality in the queue/search examples.

The CAP change is a real improvement. The running example is now the main risk.

⸻

P0 — The running example still has a formal tension

Your summary says:

CC evaluates each read against its own causal past at decision time. SC requires a global total order consistent with the full happens-before relation at the history where the outcome is assessed.

That is a plausible intuitive distinction, but in the paper’s formal model it still does not fully line up.

The key sentence in the paper is:

Formally, an outcome containing $\mathsf{r}{\,\mapsto}v$ for a
pending read represents a decision made at the current history; the
decision's causal past is determined by the history at decision time,
not by later events that may precede the eventual response.

This saves causal consistency. But it also weakens the SC witness.

At H_1, the outcome

o_{H_1} = { (r -> 0, w(1)) }

represents a decision to return 0 made at H_1. Then H_2 adds recv(w) later. If the decision was already made at H_1, recv(w) cannot become a predecessor of that decision. That is exactly what the decision-time convention says.

The SC section tries to avoid this by saying SC’s constraint is global and evaluated at H_2. But the object being refined is still the earlier outcome o_{H_1}. If that outcome represents a decision made at H_1, the later history cannot simply reinterpret the read as a future response after recv(w) without changing what the outcome meant.

So the tension remains:

* For CC, r -> 0 is a decision at H_1.
* For SC, r -> 0 is treated as if it must be placed relative to the later recv(w)/future response at H_2.

That is not obviously sound.

Suggested fix

I would either replace the running witness or make the outcome model more explicit.

The cleanest repair is probably to stop using a pending single read as the SC witness. Use a completed-observation disagreement pattern instead.

For example:

* node p: write x=1, then read y=0;
* node q: write y=1, then read x=0.

Each local read can be justified under a causal/local spec, but no single total order respecting both process orders can justify both reads. This is the standard “two processes observe opposite orders” witness. It avoids pending-response commitments entirely and makes the total-order issue obvious.

If you want to keep the current example, I think you need a formal convention like:

An SC outcome for a pending read is not a decision event; it is a proposed eventual response whose operation interval remains open until the response event occurs.

But then the CC decision-time convention is different for CC and SC, which is odd because you say they share histories and differ in outcome structure/order. It would be cleaner to avoid that.

⸻

P0/P1 — The current “sequential consistency” is no longer standard SC

You changed the definition to:

outcomes are total orders ... consistent with happens-before at each history

That is much stronger than Lamport sequential consistency, which respects process/program order, not arbitrary message-delivery happens-before. You cite Lamport SC, but the spec is closer to a single-copy causal order, happens-before serializability, or a linearizability-adjacent order constraint.

This is risky because a distributed systems/PODC-aware reviewer may object immediately.

You have two options:

1. Rename the spec. Call it “happens-before sequential consistency,” “causal single-copy order,” or “HB-serial register.” Then say it is stronger than Lamport SC and chosen to illustrate the total-order-vs-causal-order distinction.
2. Use standard SC. Then the witness should be based on process-order constraints rather than message delivery.

I would not keep “sequential consistency” unqualified with a happens-before-respecting definition.

⸻

P1 — Complete CAP is much improved, but one local-exposure definition remains thin

The shift to distributed-monotonicity works. This is the right move:

a specification admits ... CAP implementation iff it is distributed-monotone

That avoids the earlier “local non-monotonicity becomes CAP” bug.

The remaining issue is this definition:

An outcome is exposed at p if p is the process that would communicate
it to a client---formally, if o determines a response to an invocation
event at p.

This is acceptable for register/read-response outcomes, but less clearly defined for:

* log-prefix outcomes,
* CRDT states,
* transaction fact sets,
* global outcomes involving multiple operations,
* outcomes that contain several responses at different processes.

A lightweight fix is to add Obs_p(H) as derived notation:

Let \Obs_p(H) denote the outcomes in \Obs(H) that determine a response
to some invocation at process p. For outcomes containing multiple
responses, o is exposed at every p whose response it determines.

Then use o \in \Obs_p(H_1) in the distributed-monotone definition.

This is not a huge issue, but it would make the CAP theorem feel formally cleaner.

⸻

P1 — CAP availability theorem is now logically scoped, but the sufficiency remains semantic

The appendix note about semantic availability is good. The main proof says:

Hence every process can safely expose any admissible outcome without
waiting---both availability and consistency hold.

This is fine as a semantic existence claim, but a reviewer may still ask how the process chooses/enumerates an admissible outcome. You already say:

Complete CAP is a semantic characterization ... not how a process algorithmically selects an outcome.

That is the right caveat. I would move this caveat closer to the theorem proof, perhaps immediately after it, not after the monotone/distributed-monotone relationship. It matters for interpreting the sufficiency direction.

⸻

P1/P2 — Frontier appendix still overclaims maximality

You softened the prose, but some proof language remains too strong.

Register

The proposition is now titled “Register interface frontier,” and no longer says Ord^* = Ord_causal. Good.

But the proof still says:

with causal structure such that o_2 is the only causally-consistent
extension of o_1 at H_2

This is a nontrivial uniqueness/realizability assertion. It may be true under some setup, but the proof does not establish it. I’d weaken the maximality paragraph further unless you want to add a lemma.

Queue

The queue proof still says:

Any order smaller than causal FIFO must declare one of these pairs
incompatible...

That does not follow in general. A smaller order can remove a refinement edge without imposing a global a-before-b preference. Your argument establishes that orders that try to preserve a fixed order among concurrent enqueues are not monotone. It does not prove full minimality over all smaller orders.

Suggested wording:

Any strengthening that attempts to distinguish a preferred order among concurrent enqueues creates a future-inconsistency witness.

That is much safer.

Search structures

This remains the least rigorous frontier example. The proof says:

Any order smaller than forward-reachability must declare some pair
(k,p) invalid even though k is reachable from p via links.
That is, it requires the lookup to arrive at the exact current position...

The second sentence does not follow. There may be intermediate lookup guarantees between exact location and arbitrary forward reachability.

I would change the proposition to:

forward-reachability is a natural monotone weakening under the link invariant

and avoid “no weaker order suffices” unless you formalize the class of allowed lookup guarantees.

⸻

P2 — Separation theorem still leans on the running example

The separation theorem says:

Sequential consistency is non-monotone (Section~\ref{sec:example}).

So if the running SC witness is vulnerable, this theorem inherits the vulnerability. Once you fix/rename the running example, this section should be fine.

Also, the proof says relational-transducer CALM cannot certify the variant. The current phrasing is much safer than before, but I would still consider saying:

cannot certify it at this semantic boundary without encoding the coordinated variant as a separate monotone transducer program.

That small qualifier avoids another “but I can encode a log consumer” objection.

⸻

P2 — Prefix-extension Datalog proof is mostly fixed

I verified that the main proposition now says “Standard encodings,” and the appendix proof ends with “such encodings.” Good.

The main proof sketch says “Full proof in Appendix~\ref{app:hierarchy},” and the appendix does contain a restated proposition and proof. That part is fine.

⸻

P3 — Rhetorical balance

The abstract and contributions are much improved. I still think the frontier material is a little too prominent relative to how formal it currently is. But it is in the appendix, and the main claim is now qualified as:

for a fixed observation interface, minimal monotone enlargements...
More generally, weakening the interface itself yields...

That is acceptable.

The title “Complete CAP” now feels much more defensible because the theorem says “distributed-monotone,” not plain monotone. I would keep it.

⸻

What is clearly fixed

I verified these in the attached file:

* CAP is now based on distributed-monotonicity, not plain monotonicity.
* No duplicate labels.
* No undefined refs.
* No orphan proof block.
* \rightsquigarrow is gone.
* \Poss is gone.
* Empty Obs is allowed.
* The Hydro sentence is in related work.
* The “model-specific formalisms” sentence is softened.
* Datalog-prefix claim is softened to standard encodings.
* The separation theorem no longer points to the wrong appendix.

⸻

Priority summary

Priority	Item	Recommendation
P0	Pending-read SC witness still conflicts with decision-time convention	Replace witness or formalize different pending semantics
P0	“Sequential consistency” now means happens-before-respecting total order	Rename spec or use standard SC witness
P1	exposed at p is thin for compound/global outcomes	Add \Obs_p(H) notation
P1	Frontier maximality proofs overclaim	Soften register/queue/search maximality further
P2	Separation theorem depends on SC example	Recheck after fixing running example
P2	CAP sufficiency is semantic	Move caveat closer to theorem

Bottom line

The CAP strategy worked. The paper is no longer vulnerable to the earlier “not every non-monotonicity is cross-partition” objection.

But the running example still needs one more rethink. The decision-time convention makes causal consistency monotone, but it also undermines the current single-read SC witness. I would replace that witness with a completed two-process disagreement example or rename/reformalize the SC spec as a happens-before-serial order with explicit pending-response semantics.