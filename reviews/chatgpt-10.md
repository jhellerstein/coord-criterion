I read the current uploaded main.tex directly. Your summary is mostly accurate: the CAP strategy has materially changed, the orphan proof block is not there, the old \rightsquigarrow/\Poss issues are gone, and the distributed-monotone formulation is a real improvement. But I do still see a few issues in the current file that I would treat seriously.

Older uploaded files have expired, so I’m basing this only on the current attached main.tex.

Bottom line

The CAP revision strategy worked much better than the prior version. Replacing “monotone iff CAP-implementable” with “distributed-monotone iff CAP-implementable” is the right move. It correctly avoids the earlier problem that purely local non-monotonicity should not become a CAP impossibility.

However, I now think the running register example is the highest-risk part of the paper, not CAP. There is a subtle inconsistency between the “decision-time” convention that saves causal consistency and the future-response argument used to make sequential consistency non-monotone.

⸻

P0 — Must address

1. The running example’s SC witness is still not sound as written

The current example says an outcome containing r ↦ v for a pending read represents a decision made at the current history, and that its causal past is determined at decision time. This is the right move for causal consistency. It explains why a later recv(w) should not retroactively invalidate a local decision to return 0.

But then the sequential-consistency witness says that in H_2, because recv(w) has occurred at q, any subsequent response at q has:

w -> send -> recv -> r

and therefore SC must order the write before the read.

Those two interpretations conflict.

If r ↦ 0 in o_{H_1} is a decision made at H_1, then the later receive in H_2 cannot become a predecessor of that decision. The future cannot insert a new causal predecessor of an existing decision. Under the decision-time convention, the read decision and the write are still concurrent, so the earlier SC order r before w is not obviously invalidated.

If instead r in the SC witness denotes the eventual response event, not the decision at H_1, then the CC argument becomes fragile again, because later delivery before the response could change the read’s causal past.

So the paper needs to choose one model consistently:

1. Decision-as-event model. If Obs(H_1) contains r ↦ 0, treat that as adding a decision event at H_1. Then H_2 cannot insert recv(w) before that decision. The current one-read SC witness fails, and you need a different SC witness.
2. Possible-future-response model. If Obs(H_1) contains possible future responses, then H_2 can constrain the later response, but the CC monotonicity explanation needs to be restated because the response is not actually decided at H_1.

I suspect the cleanest fix is to abandon this one-read SC witness and use a more standard two-read/two-write disagreement witness for sequential consistency: two replicas make concurrent writes and local reads that force incompatible total orders. That would show why a single global order requires coordination without relying on the ambiguous pending-read decision convention.

This is the one issue I would not leave to reviewer interpretation.

2. Sequential consistency is defined as program-order consistency but used as happens-before consistency

The spec says SC outcomes are total orders:

consistent with program order at each node

But the witness later says:

SC requires the total order to respect happens-before

Those are different. Lamport sequential consistency respects per-process program order, not arbitrary message-delivery happens-before. The current witness relies on an internal propagation receive forcing w before r, which is not a standard SC requirement unless you define SC here as “total order extending happens-before.”

You can fix this either way:

* Rename the spec to something like causal sequential consistency, atomic/linearizable register, or single-copy serial order extending happens-before; or
* Keep Lamport SC, but replace the witness with one based on conflicting per-process observations.

Right now a distributed-systems reviewer will likely catch this.

⸻

P1 — Strongly recommended

3. Complete CAP is much improved, but “outcome exposed at process p” needs formal definition

The new definitions are a good strategy:

Partition-constrained future
Distributed-monotone
Complete CAP iff distributed-monotone

This is much cleaner than the prior relocation argument.

The remaining gap is that distributed-monotone quantifies over:

every outcome o in Obs(H_1) exposed at p

but the base specification does not define which outcomes are “exposed at p.” Obs(H) is global. Outcomes may mention operations at several processes. Some outcomes are local read responses; some are logs; some are states; some are fact sets.

I would add one small piece of structure for distributed specs:

An exposure relation \mathsf{loc}(o,H) \subseteq Proc

or:

\Obs_p(H) \subseteq \Obs(H)

where \Obs_p(H) is the set of outcomes process p may expose at H.

Then distributed-monotonicity becomes:

for every p in S, every o in Obs_p(H_1), and every P-constrained future H_2...

That would make the CAP theorem much sharper and avoid a “what does exposed at p mean?” objection.

4. The appendix CAP theorem is better, but the direction labels are confusing

In the appendix, the proof starts:

($\Rightarrow$, not distributed-monotone implies CAP obstruction.)

That is really the contrapositive of the => direction. It is not wrong, but I would write:

(Contrapositive of $\Rightarrow$.)

Small change, but it helps readers.

5. The separation theorem points to the wrong appendix

In the Proper Coordination section, the proof says:

Proof sketch (full proof in Appendix~\ref{app:proofs})

But app:proofs is now the label on Complete CAP: Formal Treatment, not a full proof of the separation theorem. I verified the current file: \label{app:proofs} appears at the CAP appendix section.

This is a concrete fix. Either remove “full proof in Appendix…” or add a real appendix subsection for the separation proof and label it accordingly.

6. The CAP theorem’s sufficiency still assumes an implementation can “expose any admissible outcome”

The proof says:

Since every outcome survives all such futures, p can expose any admissible outcome immediately

This is consistent with the paper’s spec-level model. But it is a semantic implementation existence claim, not an algorithmic one. That is okay, but I would add the same sort of caveat you use elsewhere:

This is a semantic availability theorem: it characterizes when no coordination is required for safety; it does not assert decidability or construct an efficient local algorithm for choosing an outcome.

Otherwise a reviewer may ask how p computes or enumerates Obs_p(H).

⸻

P2 — Important but lower risk

7. Frontier section is improved, but maximality claims are still the softest part

The new frontier framing is better:

* fixed observation interface → minimal monotone enlargements of Ord;
* broader interface weakenings → register/queue/search examples.

But some maximality language is still too strong relative to the proofs.

Register

The proposition now says “natural frontier point,” which is good. But the proof still contains:

with causal structure such that o_2 is the only causally-consistent extension of o_1

That is a nontrivial realizability/uniqueness assertion. I would either add a lemma or soften the proof further.

Queue

The proof says:

Any order smaller than causal FIFO must declare one of these pairs incompatible

That is still broad. A smaller order might remove some refinements without imposing the particular global incompatibility you describe. This is less dangerous because it is appendix material, but I would soften to “any order that attempts to preserve a fixed order among concurrent enqueues…”

Search

This statement remains too strong:

under the link invariant no weaker order suffices

There may be intermediate lookup guarantees between exact location and arbitrary forward reachability. The monotonicity proof for forward-reachability is nice; the maximality claim is the risky part. I would say “forward-reachability is a natural monotone weakening” rather than “no weaker order suffices,” unless you formalize the lattice of lookup guarantees.

8. The prefix-extension Datalog proof is still too strong at the last sentence

The appendix proposition is now scoped to “standard encodings,” which is good. But the proof ends:

Hence any Datalog encoding of prefix-extension semantics requires...

That reintroduces the universal claim. Change “any” to “the standard position-fact encoding” or “such encodings.”

This is minor but worth fixing.

9. The intro still slightly overstates model-driven formalisms

This sentence is punchy:

Model-driven formalisms cannot do this by construction...

I would soften it:

Existing model-specific formalisms do not provide this test directly: they analyze programs inside the model rather than arbitrary residual output specifications.

This avoids a reviewer responding with “but I can encode a log consumer in Datalog.”

⸻

What is clearly fixed now

I verified these against the current file:

* The old Poss-preservation issue is gone.
* \Poss macro is gone.
* \rightsquigarrow is gone.
* The orphan proof block I previously mentioned is not present.
* No duplicate labels.
* No undefined \refs in the source.
* Empty Obs is now allowed.
* CAP is now based on distributed-monotonicity, not plain monotonicity.
* The CALM instantiation is much cleaner.
* The Hydro line has moved to related work.
* “CALM conflates…” has been softened.
* The abstract’s frontier claim is more scoped than before.

⸻

Did the new strategy work?

Yes, for CAP it mostly worked. The shift to distributed-monotonicity is the right formal move. It is much better than trying to prove all non-monotonicity can be relocated across a partition.

But the paper now needs two final stabilizations:

1. Fix the running SC/CC witness. The decision-time convention and the SC future argument currently pull in opposite directions.
2. Add a formal notion of process-local exposure for Complete CAP.

If you fix those, the core paper will be much harder to attack. The remaining frontier/maximality issues are less central and could be handled by softening appendix claims rather than rebuilding the theory.

My priority list

Priority	Issue	Recommendation
P0	SC witness conflicts with decision-time convention	Replace witness or formalize decision/response distinction
P0	SC defined as program-order but used as happens-before	Rename spec or change witness
P1	“Outcome exposed at p” undefined	Add Obs_p(H) or loc(o,H)
P1	Separation proof points to CAP appendix	Fix/remove appendix reference
P1	CAP sufficiency is semantic, not algorithmic	Add caveat
P2	Frontier maximality for register/queue/search	Soften unless fully proved
P2	Prefix Datalog proof ends with “any encoding”	Change to “standard/such encodings”
P2	“Model-driven formalisms cannot”	Soften slightly

The draft is now in much better shape than earlier versions. I’d focus almost entirely on the running example and the Obs_p issue next.