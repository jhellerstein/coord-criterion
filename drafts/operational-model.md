# Operational Model for Complete CALM — Draft v2

## Overview

We define a discrete-event operational model of distributed processes and prove
that a specification admits a correct, coordination-free implementation in this
model iff it is monotone. The model is a message-passing system with
deterministic local processes that react to events. Processes may also take
internal steps (stutter-steps) for background computation, gossip, or
pre-computation. The coordination-freedom condition constrains only client
responses: a process must respond to every invocation immediately, without
waiting for future messages.

---

## The Model

### Processes

A system consists of $n$ processes $p_1, \ldots, p_n$. Each process $p_i$ has:

- A **local state** $\sigma_i \in \Sigma_i$ (arbitrary — think CPU+RAM, not a
  finite automaton).
- A **deterministic handler** $h_i : \Sigma_i \times \mathsf{Event}_i \to
  \Sigma_i \times \mathsf{Out}_i$.

Events at process $p_i$ are one of three kinds:

$$\mathsf{Event}_i = \mathsf{Inv}_i \cup \mathsf{Msg}_i \cup \{\tau\}$$

- $\mathsf{Inv}_i$: a client invocation (external input requesting a response).
- $\mathsf{Msg}_i$: an arriving message from another process.
- $\tau$: an internal tick (stutter-step — background computation).

The handler output depends on the event type:

$$\mathsf{Out}_i = (\mathsf{Resp}_i \cup \{\bot\}) \times \mathsf{Msg}^*$$

- A client response $r \in \mathsf{Resp}_i$ (or $\bot$ if no response).
- Zero or more outgoing messages to other processes.

**Constraints:**
- On a client invocation ($e \in \mathsf{Inv}_i$): the handler MUST produce
  $r \neq \bot$ (a response). This is the coordination-freedom condition.
- On a message arrival ($e \in \mathsf{Msg}_i$): the handler MAY produce
  $r = \bot$ (no client response) or $r \neq \bot$ (if a deferred response is
  being completed — but see below).
- On an internal tick ($e = \tau$): the handler produces $r = \bot$ (no client
  response — ticks are internal). It may update state and send messages.

### Executions

An **execution** is a sequence of (process, event) pairs, determined by an
adversarial asynchronous scheduler:

- The scheduler delivers client invocations to specific processes (modeling the
  workload/environment).
- The scheduler delivers messages to their destinations in any order, with
  arbitrary finite delay.
- The scheduler triggers internal ticks at any process at any time (modeling
  background computation, timers, gossip decisions).
- **Fairness:** every sent message is eventually delivered. Internal ticks may
  occur at any time but are not required (a process need not take background
  steps).

The scheduler is adversarial: it chooses the worst-case delivery order and
timing. The implementation must be correct under ALL schedules.

### Histories and Traces

An execution determines:

- A **history** $H = (E, \to)$: the partial order of all events ordered by
  happens-before:
  - Program order within each process (sequential handler invocations).
  - Send-before-receive for each message.
  - Internal ticks are ordered by program order at their process.
- An **observation trace** $\mathsf{resp}(H)$: the multiset of (invocation,
  response) pairs emitted so far.

### Correctness

An implementation is **correct** for specification $\Spec = (E, \Obs, \Ord)$
if: for every execution, at every prefix with history $H$, the observation
trace $\mathsf{resp}(H)$ is consistent with some admissible outcome
$o \in \Obs(H)$.

"Consistent with" means: for every invocation $e$ that has received response
$r$ in the trace, the outcome $o$ prescribes $r$ as the response to $e$.

### Coordination-Freedom

An implementation is **coordination-free** if:

> For every process $p_i$ and every client invocation $e \in \mathsf{Inv}_i$,
> the handler $h_i(\sigma_i, e)$ produces a response $r \neq \bot$.

That is: the process responds to every client invocation **in the same handler
step** that receives it. It uses only its current local state $\sigma_i$ —
which reflects all prior events at $p_i$ (invocations, messages received,
internal ticks) but NOT messages in flight or future events at other processes.

The process never says "I'll respond later when I get more information." It
commits immediately.

**What stutter-steps buy:** A process can use internal ticks to:
- Send gossip messages (propagating local state to peers).
- Process received gossip (enriching local state with remote information).
- Pre-compute outcomes for anticipated future invocations.

All of this enriches $\sigma_i$ BEFORE the next invocation arrives. But when
the invocation arrives, the response is immediate — no further waiting.

---

## The Theorem

**Theorem (Complete CALM, operational).** A specification $\Spec$ admits a
correct coordination-free implementation iff $\Spec$ is monotone.

### Proof of Sufficiency (Monotone → Implementation Exists)

**Construction.** Define the "causal-view" implementation:

- **State:** Each process $p_i$ maintains $\sigma_i = H_i$, its **local causal
  history** — the set of all events it knows about, with their causal ordering.
  Initially $H_i = \emptyset$.

- **On client invocation $e$ at $p_i$:**
  1. Add $e$ to $H_i$ (with appropriate happens-before edges).
  2. Compute $\Obs(H_i)$ — the admissible outcomes at the local causal history.
  3. Choose any $o \in \Obs(H_i)$ and respond with the value $o$ prescribes
     for $e$.
  4. (The choice among multiple valid outcomes can be arbitrary/deterministic —
     e.g., lexicographically first.)

- **On message arrival $m$ at $p_i$:**
  1. Merge the information in $m$ into $H_i$ (add events and edges from the
     sender's view).
  2. No client response ($r = \bot$).

- **On internal tick $\tau$ at $p_i$:**
  1. Send a gossip message containing $H_i$ (or a delta) to some other
     process.
  2. No client response ($r = \bot$).

**Correctness proof:**

At any point in the execution, the global history $H$ satisfies
$H_i \sqsubseteq H$ for every process $p_i$ (the local view is a prefix of
the global history — it contains only events that have causally reached $p_i$).

When $p_i$ responds to invocation $e$ with value $r$, it chose an outcome
$o \in \Obs(H_i)$ prescribing $r$ for $e$.

By monotonicity of $\Spec$: since $H_i \sqsubseteq H$, there exists
$o' \in \Obs(H)$ with $o \preceq o'$. Since refinement preserves earlier
responses (the response to $e$ in $o'$ is the same as in $o$ — refinement
only adds detail, it doesn't contradict), the response $r$ is consistent with
$o' \in \Obs(H)$.

Hence at every execution prefix, every emitted response is consistent with
some admissible outcome at the global history. The implementation is correct.

**Coordination-freedom:** The handler always responds on invocation (step 3
above). No waiting. □

**Remark:** The construction propagates full local histories via gossip, which
is expensive. Practical implementations propagate less (vector clocks, deltas,
Merkle trees). The theorem requires only existence of *some* correct
coordination-free implementation — efficiency is a separate concern.

### Proof of Necessity (Coordination-Free → Monotone)

**Contrapositive:** If $\Spec$ is not monotone, no correct implementation is
coordination-free.

Assume $\Spec$ is not monotone. Then there exists a history $H_1$, an outcome
$o \in \Obs(H_1)$ with a response to some invocation $e$ at process $p$, and
a future $H_2 \sqsupseteq H_1$ such that no $o' \in \Obs(H_2)$ refines $o$.

Let $r$ be the response that $o$ prescribes for $e$.

**Construct two executions indistinguishable to $p$:**

- **Execution α (safe world):**
  The scheduler delivers events to all processes producing global history
  $H_1$. At the moment $p$ receives invocation $e$, its local state $\sigma_p$
  reflects all events that have causally reached $p$ in $H_1$ — call this
  $H_1|_p$ (the local projection). After $p$ responds, no further events
  occur that would invalidate the response.

- **Execution β (dangerous world):**
  The scheduler delivers the same events to $p$ in the same order (producing
  the same local state $\sigma_p = H_1|_p$ at the moment of invocation $e$).
  But concurrently, other processes advance — and messages from them to $p$ are
  delayed by the adversarial scheduler. The global history reaches $H_2$.

In both executions, $p$ has identical local state $\sigma_p$ when it receives
$e$. Since the handler is deterministic, $p$ must make the same choice in both.

**Case 1: $p$ responds with $r$ (coordination-free).**
In execution α, this is correct: $r$ is consistent with $o \in \Obs(H_1)$.
In execution β, the global history is $H_2$. The response $r$ was chosen to be
consistent with $o$, but no $o' \in \Obs(H_2)$ refines $o$. Hence $r$ is not
consistent with any admissible outcome at $H_2$. Correctness is violated.

**Case 2: $p$ does not respond (defers).**
Then the implementation is not coordination-free (it fails to respond
immediately to a client invocation).

In either case, no correct coordination-free implementation exists. □

**Key point:** The adversarial scheduler's power to delay messages creates the
indistinguishability. Process $p$ cannot tell whether it's in the safe world
(where responding is fine) or the dangerous world (where responding leads to
inconsistency). This is the fundamental tension that coordination resolves —
and that monotonicity eliminates.

---

## What This Buys Over the Current Paper

| Current paper | Operational version |
|---|---|
| Coordination-free = spec-level property (Def 3.6) | Coordination-free = behavioral property of processes |
| Proof: unpack definitions (2 lines) | Proof: construction + indistinguishability argument |
| Reviewer objection: "definitional" | No such objection: genuine operational characterization |
| Implementation model is abstract | Implementation model is concrete (handlers, messages, scheduler) |

The operational theorem says something genuinely non-trivial: **there exists a
distributed protocol (the causal-view protocol) that is correct under all
adversarial schedules iff the specification is monotone.** The sufficiency
direction builds something; the necessity direction uses a real distributed
computing argument.

---

## Design Choices and Alternatives

### Why deterministic handlers?

Determinism is needed for the necessity proof (indistinguishability requires
that the same local state produces the same response). If handlers are
nondeterministic, a process could "guess" which world it's in and respond
differently — but then correctness requires the guess to always be right,
which is impossible under adversarial scheduling. So determinism is natural
but not strictly necessary; the argument works for any handler that must
produce the same distribution of responses given the same local state.

### Why fairness (eventual delivery)?

Fairness is needed for the sufficiency direction: the causal-view protocol
relies on gossip eventually reaching all processes (so local views converge
toward the global history). Without fairness, a process might never learn
about remote events, and its local view might be permanently stale. But
monotonicity still guarantees that stale-view responses are correct — they
just might be less refined than what a better-informed process would produce.

Actually, fairness is NOT needed for correctness — only for convergence of
local views. The causal-view protocol is correct even without fairness
(monotonicity guarantees safety regardless of how stale the local view is).
Fairness is needed only if we want eventual consistency / convergence as an
additional property.

So we can drop fairness and still get the theorem. The model becomes: messages
may be delayed arbitrarily or lost. The causal-view protocol is still correct
and coordination-free. This is actually stronger — it shows that
coordination-free implementations work even under message loss.

### Why allow internal ticks?

Internal ticks model background gossip, anti-entropy, and pre-computation.
They make the sufficiency construction more natural (gossip propagates state)
but are not strictly necessary for the theorem. Without ticks, the causal-view
protocol can piggyback state propagation on response messages or client-
triggered messages. The theorem holds either way.

Ticks make the model more realistic and connect to how real systems work
(background replication, heartbeats, etc.).

### Relationship to Ameloot et al.'s transducer model

Ameloot et al.'s relational transducers are a special case:
- Processes are nodes in a network.
- State is a set of local facts.
- Handlers are Datalog rule applications.
- Messages are "heartbeats" carrying fact sets.
- Coordination-free = quiescence reached by heartbeats alone.

Our model generalizes by:
- Allowing arbitrary state (not just fact sets).
- Allowing arbitrary handlers (not just Datalog rules).
- Defining coordination-freedom as immediate response (not quiescence).
- Allowing any refinement order (not just set inclusion).

The CALM subsumption theorem (Theorem 5.1 in the current paper) shows that
under the transducer instantiation, the two notions of coordination-freedom
coincide.

---

## Proposed LaTeX (sketch)

```latex
\subsection{Operational Model}
\label{sec:operational}

We now ground the semantic criterion in a concrete operational model.
A \emph{distributed implementation} consists of $n$ processes, each
with a deterministic event handler.

\begin{definition}[Process]
  Process $p_i$ has local state $\sigma_i \in \Sigma_i$ and a
  deterministic handler
  $h_i : \Sigma_i \times \mathsf{Event}_i \to
  \Sigma_i \times \mathsf{Out}_i$
  where $\mathsf{Event}_i = \mathsf{Inv}_i \cup \mathsf{Msg}_i
  \cup \{\tau\}$ (client invocations, message arrivals, internal
  ticks) and $\mathsf{Out}_i = (\mathsf{Resp}_i \cup \{\bot\})
  \times \mathsf{Msg}^*$ (optional response plus outgoing messages).
\end{definition}

\noindent
On a client invocation, the handler updates state, emits a response,
and optionally sends messages.
On a message arrival or internal tick, it updates state and optionally
sends messages but need not respond to a client.
Internal ticks model background computation: gossip, anti-entropy,
pre-computation.

An \emph{execution} is a sequence of events delivered by an
adversarial asynchronous scheduler that controls message delivery
order and timing.
The scheduler may trigger internal ticks at any process at any time.

\begin{definition}[Coordination-free implementation]
  \label{def:coordfree-op}
  An implementation is \emph{coordination-free} if for every process
  $p_i$ and every client invocation $e \in \mathsf{Inv}_i$, the
  handler produces a response: $h_i(\sigma_i, e) = (\sigma_i',
  (r, \vec{m}))$ with $r \neq \bot$.
\end{definition}

\noindent
The process responds immediately using only its current local state.
It never defers a response to await a future message.

\begin{definition}[Correctness]
  An implementation is \emph{correct} for $\Spec$ if for every
  execution prefix with history $H$, the emitted responses are
  consistent with some $o \in \Obs(H)$.
\end{definition}

\begin{theorem}[Complete CALM, operational]
  \label{thm:complete-calm-op}
  A specification $\Spec$ admits a correct coordination-free
  implementation iff $\Spec$ is monotone.
\end{theorem}

\begin{proof}
  \emph{Sufficiency.}
  Construct the causal-view protocol: each process maintains its
  local causal history $H_i$ and propagates it via gossip (on
  internal ticks).
  On invocation $e$, the process computes $\Obs(H_i)$, chooses
  $o \in \Obs(H_i)$, and responds with $o$'s prescription for $e$.
  Since $H_i \sqsubseteq H$ (the global history is a future of
  every local view), monotonicity guarantees a refinement
  $o' \in \Obs(H)$ with $o \preceq o'$, so the response is
  consistent with $o'$.
  The implementation is correct and coordination-free.

  \emph{Necessity.}
  If not monotone, some $o \in \Obs(H_1)$ at process $p$ has no
  refinement at a future $H_2$.
  Construct executions $\alpha$ (global history stays at $H_1$) and
  $\beta$ (global history reaches $H_2$, but messages to $p$ are
  delayed).
  Process $p$ has identical local state in both at the invocation
  point.
  If $p$ responds (coordination-free), correctness fails in $\beta$.
  If $p$ defers, it is not coordination-free.
\end{proof}
```

---

## Summary

The operational model transforms Complete CALM from a near-definitional
equivalence into a genuine distributed computing theorem: the existence of a
correct protocol under adversarial scheduling is equivalent to monotonicity of
the specification. The proof has real content (protocol construction +
indistinguishability), and the model connects naturally to deterministic
simulation testing frameworks.
