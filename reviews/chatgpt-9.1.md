You’re right to challenge me. Looking again at the current main.tex, I did not read the Complete CAP discussion carefully enough in my previous pass. I missed that the main-text CAP section still says the fully general iff, and I also missed that the orphan proof block is still present immediately after the CAP corollary.

So, correcting myself: my concern about Complete CAP still stands, but now more strongly and more specifically.

What the current text actually says

The main text states:

\begin{corollary}[Complete CAP]
  \label{cor:cap}
  A specification admits a consistent, available, partition-tolerant
  distributed implementation if and only if it is monotone.
\end{corollary}

and the proof says:

By Complete CALM, the specification requires coordination.
By Lemma~\ref{lem:coord-comm}, coordination requires communication.
By Lemma~\ref{lem:partition}, communication fails under partitions,
forcing a choice between availability and consistency.

That argument silently assumes that every non-monotonicity witness requires cross-partition communication. But Lemma 1 only supports that when:

A partition isolating the exposing process from all processes that
could confirm or rule out H_2 ...

So the iff is too broad unless you can prove that every non-monotone distributed specification has such a partition-relevant witness. I do not think that is true as stated.

The appendix confirms the mismatch

The appendix has the right machinery:

\begin{definition}[Cross-partition witness]
...

and later says:

CAP is not tied to linearizability.
It applies to any specification admitting a cross-partition
future-inconsistent outcome...

That is the correct scoped claim.

But the main corollary says:

iff monotone

rather than:

iff no cross-partition future-inconsistent outcomes exist, under the chosen partition model.

Those are not the same.

A non-monotone specification can fail monotonicity for a purely local reason, or for a same-partition concurrency reason. Complete CALM says it requires coordination in the broad semantic sense, but CAP only bites when the required coordination crosses a partition.

I also missed the orphan proof block

After the CAP corollary, the current file still has:

\begin{proof}
  We exhibit a concrete witness for item~(2).
  ...
\end{proof}

This is indeed still orphaned. It follows the CAP discussion but is about the Paxos/log-prefix separation. It needs to be deleted or moved back under the separation theorem.

This is not a philosophical issue; it is a straightforward draft bug reviewers will catch.

Recommended fix

I would revise the main CAP corollary to something like:

\begin{corollary}[CAP as cross-partition future-inconsistency]
Fix a partition pattern P. If a distributed specification has a
future-inconsistent outcome whose distinguishing events lie across P,
then no implementation can be simultaneously correct, available under P,
and partition-tolerant. Conversely, monotone specifications have no
future-inconsistent outcomes, and hence no CAP-style obstruction of this
form.
\end{corollary}

Then the prose can still say:

Complete CALM generalizes the semantic side of CAP: non-monotonicity identifies where coordination is needed; cross-partition non-monotonicity identifies where that need becomes a CAP availability failure.

That is strong, accurate, and still memorable.

On the name “Complete CAP”

You can keep the phrase, but I would qualify it in the section title or corollary title:

Complete CAP: Cross-Partition Future-Inconsistency

or

Complete CAP in the Asynchronous Partition Model

The unqualified corollary “iff monotone” is currently the part I would not defend.

So: yes, you were right to ask. I had not tracked the actual current CAP text carefully enough, and the current version still needs a scoped CAP statement plus removal/movement of the orphan proof block. 