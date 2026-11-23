# Notes: Subsumption Theorem Strategy

## Goal
Prove a single theorem showing that the entire Ameloot/Zinn/Baccaert-Ketsman
literature is subsumed by Complete CALM. Not case-by-case, but a structural
argument.

## The Key Papers and Their Results

### Ameloot et al. 2013 (JACM)
- **Model**: Relational transducer networks. Nodes hold local relations, receive
  input facts, exchange messages, derive output facts.
- **System relations**: `Id` (local node id), `All` (set of all nodes).
- **Key definitions**:
  - *Consistent*: all fair runs on all horizontal partitions produce the same output
  - *Network-topology independent*: consistent on every network, computing the same query
  - *Coordination-free*: for every input I, there EXISTS a horizontal partition H
    where quiescence is reached by heartbeat transitions alone (no communication)
  - *Oblivious*: doesn't use Id or All
- **Main results** (Corollary 13):
  (1) Q computed by coordination-free transducer ⟺
  (2) Q computed by oblivious transducer ⟺
  (3) Q is monotone
- **Proof of (1)⟹(3)** (Theorem 12): If coord-free, then for I⊆J and t∈Q(I),
  the partition for I can be extended to J by placing J\I at another node.
  The first node still outputs t (no communication needed). By consistency,
  t∈Q(J). Hence monotone.
- **Key structural feature**: outputs are irretractable ("outputs cannot later
  be retracted"). This is what makes the output monotone in time.

### Zinn 2012 / Ameloot-Ketsman-Neven-Zinn 2016 (TODS)
- **Hierarchy**: M = F[N0] ⊂ F[N1] ⊂ F[N2] ⊂ F[N3] = C
  - N0: basic model (no knowledge of distribution) → monotone queries
  - N1: nodes know partitioning policy → adom-monotone queries
  - N2: data replicated by constant assignment → weak-adom-monotone queries
  - N3: nodes know active domain of global input → all computable queries
- **Key insight**: each level adds knowledge that converts some universal
  quantification into bounded (hence monotone) computation
- **Weaker monotonicity notions**:
  - adom-monotone: Q(I) ⊆ Q(I∪{f}) when f contains a NEW constant
  - weak-adom-monotone: Q(I) ⊆ Q(I∪{f}) when f is non-nullary and contains ONLY new constants
- F[N1] = adom-monotone, F[N2] = weak-adom-monotone

### Ameloot et al. 2016 (TPLP, "Stable Grounds")
- Shows stable models of distributed Datalog programs correspond to
  operational traces of the distributed system
- Key bridge: the nondeterminism of distributed execution (message ordering,
  concurrency) maps to the nondeterminism of stable model choice
- Relevant for our provenance paper more than this one, but establishes
  that the logic-programming and distributed-systems views are formally equivalent

### Baccaert-Ketsman 2026 (Information Systems) — NEED TO READ
- Extends to non-deterministic "behaviors" (distributed instances → distributed instances)
- Parameterizes system relations available to nodes
- Yields a coordination spectrum based on shared information

## The Formal Bridge: Ameloot-CF ⟺ Future-Monotone

### Instantiation
Given a transducer network computing query Q:
- **Event universe E**: input-fact arrivals (E_in), rule firings (E_int),
  message sends (E_send), message receives (E_recv)
- **Histories**: prefixes of fair runs of the transducer network
- **Outcomes**: output fact sets produced so far, ordered by set inclusion
  (o₁ ≤ o₂ iff o₁ ⊆ o₂)
- **Obs(H)**: the set of output facts that have been irretractably produced
  by history H. Since outputs are irretractable, Obs(H) is a singleton
  {current output set at H}.
- **Future**: extending the run with more transitions (heartbeat, delivery, send)

### The Equivalence

**Claim**: Under this instantiation, Q is monotone ⟺ Spec_Q is future-monotone.

**Proof of ⟹ (monotone query → future-monotone spec)**:
- If Q is monotone, then as input facts grow (I ⊆ J), output grows (Q(I) ⊆ Q(J)).
- In our framework: extending a history can only add input facts (futures add events).
- Since outputs are irretractable and Q is monotone, the output set at any future
  H₂ ⊇ H₁ satisfies Obs(H₁) ⊆ Obs(H₂).
- Since Ord is set inclusion, this means o₁ ≤ o₂ for o₁∈Obs(H₁), o₂∈Obs(H₂).
- Hence future-monotone.

**Proof of ⟸ (future-monotone spec → monotone query)**:
- If Spec_Q is future-monotone, then for any H₁ ⊑ H₂, Obs(H₁) ⊆ Obs(H₂)
  (under set-inclusion order on outcomes).
- Consider inputs I ⊆ J. There exist histories H_I and H_J (complete runs)
  with Obs(H_I) = Q(I) and Obs(H_J) = Q(J).
- The history H_I can be extended to a history H' that includes the additional
  facts J\I (by adding input-fact arrival events). Since Spec is future-monotone,
  Q(I) ⊆ Obs(H') ⊆ Q(J).
- Hence Q is monotone.

**The deeper equivalence (coordination-freedom)**:
- Ameloot-CF says: ∃ partition where no communication needed
- Our CF says: Poss^I = Poss (no admissible futures suppressed)
- These are equivalent because:
  - If Ameloot-CF holds: the implementation realizes all admissible histories
    (it never needs to suppress a future, because heartbeat-only runs succeed
    on some partition). Hence Poss^I = Poss.
  - If our CF holds: the implementation never suppresses futures. In particular,
    it can succeed without communication on a suitable partition (the one where
    each node has enough input to produce its share of the output independently).

### Handling the Hierarchy
For each level N_i, the instantiation changes:
- **N0**: Obs(H) = output derivable from LOCAL input only (no knowledge of others)
- **N1**: Obs(H) = output derivable from local input + policy oracle
- **N2**: Obs(H) = output derivable from replicated input
- **N3**: Obs(H) = output derivable from full input (active domain known)

At each level, "future-monotone" means "output doesn't shrink when the
RELEVANT input grows" — where "relevant" is determined by what the node
can see. This gives exactly the corresponding monotonicity notion:
- N0 + future-monotone = monotone (output grows when any input grows)
- N1 + future-monotone = adom-monotone (output grows when new-constant facts arrive)
- N2 + future-monotone = weak-adom-monotone (output grows when fully-new facts arrive)
- N3 + future-monotone = always (all queries are trivially future-monotone when you see everything)

## The Subsumption Theorem Statement

**Theorem (Subsumption of the CALM Literature)**:
Let M be any of the transducer models N0, N1, N2, N3 (or their extensions).
For a query Q, define the specification Spec_M(Q) = (E_M, Obs_M, ⊆) where:
- E_M is the event universe of model M
- Obs_M(H) is the output fact set derivable at history H under model M's
  knowledge assumptions
- ⊆ is set inclusion on output fact sets

Then: Q is coordination-free under model M ⟺ Spec_M(Q) is future-monotone.

**Corollary**: The hierarchy M = F[N0] ⊂ F[N1] ⊂ F[N2] ⊂ F[N3] = C
corresponds to a hierarchy of specifications with increasingly permissive
observability functions, all tested by the same criterion (future-monotonicity).

## What Makes This a Real Theorem (Not Just Re-Notation)

1. **Single criterion, multiple models**: The same condition (future-monotonicity)
   characterizes coordination-freedom across ALL levels of the hierarchy.
   The hierarchy arises from varying the SPECIFICATION, not the criterion.

2. **The separation applies at every level**: At each level N_i, Complete CALM
   can see past coordination boundaries that the N_i-specific analysis cannot.
   A program that uses coordination internally to produce N_i-monotone output
   is correctly identified as coordination-free by Complete CALM.

3. **The universal construction applies at every level**: Membership (All)
   collapses the hierarchy to N3 = C, which is exactly our Theorem 4.3.

## Connection to Universal Construction
- N3 (full active domain knowledge) ≈ full membership knowledge
- Our Theorem 4.3 says: once you have membership, everything is coord-free
- This is exactly N3 = C in Zinn's hierarchy
- The universal construction is the constructive proof that N3 = C
- Ameloot's Lemma 5.1 (flooding protocol) is the transducer-model version
  of our universal construction

## Open: Baccaert-Ketsman
Need to read their paper to verify that their "behaviors" formalization
also maps cleanly. Their key innovation is non-deterministic computation
(multiple valid outputs for same input), which maps to our Obs(H) being
set-valued (multiple admissible outcomes). This should work naturally.


## Baccaert-Ketsman 2026: Key Findings

### Their Framework
- **Behavior**: a non-deterministic mapping from distributed instances to
  distributed instances (dist(sigma1) -> dist(sigma2))
- **Configuration constraint C**: determines what system relations nodes have
  (generalizes Id, All, partitioning policy, etc.)
- **C-transducer**: a transducer parameterized by constraint C
- **Coordination-freedom**: defined as "computable by a transducer oblivious
  to All" (the alternative definition from Ameloot)

### Their Main Theorem (Theorem 6)
For any configuration constraint C:
  F(Id+Ord+C) = M_C
i.e., the behaviors computable coordination-free under constraint C are
exactly the C-monotone behaviors.

### C-Monotonicity (Definition 8)
A behavior B is C-monotone if: when you partition the input across disjoint
node sets, compute valid outputs on each partition (under constraint C),
the partial outputs can be combined into a valid output on the whole input.

Formally: for partitioned inputs H0,...,Hk with valid partial outputs Ki
(each (Hi, Ki) valid under the restricted constraint), there exists K
with (H, K) in B and K extends union of Ki.

### The Bridge to Our Framework
C-monotonicity is "composability under partition merging":
- Partial outputs on subsets of the input remain valid when more input arrives
- This is EXACTLY future-monotonicity when:
  - "History grows" = "more input arrives from other partitions"
  - "Outcome refines" = "output extends under set inclusion"
  - The constraint C determines what each node can observe = our Obs function

### Key Results We Can Subsume
- Theorem 1: Leader election not in F(Id+All) -- leader election is not
  future-monotone under the Id+All instantiation
- Theorem 2: F(Id+All+Ord) = F(Id+All+L) -- order and leader are equivalent
- Theorem 3: F(Id+All+L) = B -- with a leader, everything is computable
  (= our universal construction: membership + authority = all specs resolved)
- Theorem 6: The meta-theorem parameterized by C

### Subsumption Argument
Our subsumption theorem will state:
For any constraint C in the Baccaert-Ketsman framework, define
Spec_C(B) = (E_C, Obs_C, subset-inclusion) where Obs_C(H) captures what
nodes can observe under constraint C at history H.

Then: B is C-monotone iff Spec_C(B) is future-monotone.

This single equivalence subsumes their entire Theorem 6 (and by extension,
all of Ameloot 2013 and Zinn 2012/2016).

### Their Theorem 3 = Our Universal Construction
Their Theorem 3 says: with Id+All+Leader, every behavior is computable.
Our Theorem 4.3 says: with membership (All), every spec is coordination-free.
These are the same result! A leader is just one way to implement the
authority that membership enables. Both say: once you know who is
participating, everything else is coordination-free.

## Validation: The Fundamental Limitation Persists (Point 3)

All papers in the CALM literature (Ameloot 2013, Zinn 2012, Ameloot et al.
2016, Baccaert-Ketsman 2026) share a fundamental structural limitation:
they analyze the TRANSDUCER PROGRAM, not the OUTPUT SPECIFICATION.

### The limitation in detail:

1. **Baccaert-Ketsman analyze behaviors, not compositions.**
   Their Theorem 6 classifies a behavior B as coordination-free iff B is
   C-monotone. But "coordination-free" means "computable by a transducer
   oblivious to All." A Paxos implementation NEEDS All (for quorum
   membership). So any Paxos transducer is not oblivious, and B-K would
   classify it as "requiring coordination." They cannot then observe that
   the OUTPUT of Paxos (the ordered log) is monotone.

2. **They cannot express system composition.**
   Their framework analyzes a SINGLE transducer (or network of identical
   transducers). It cannot express: "transducer A (Paxos, non-monotone,
   uses All) produces output consumed by transducer B (application,
   monotone, oblivious)." Our framework can, because we analyze the
   specification of the output, not the program.

3. **Ameloot's irretractability is a model constraint, not a diagnostic.**
   "Outputs cannot later be retracted" ensures output is monotone in time.
   But they use this only as a model assumption, never asking: "given
   irretractability, is the RESOLVED output specification future-monotone?"

4. **The concrete test:**
   Consider a Datalog program implementing Paxos that produces an ordered
   log. The program text contains:
   - "no_higher_ballot(B) :- not exists_higher(B)." (negation)
   - "quorum_reached(S) :- count_acks(S,N), majority(N)." (aggregation)
   
   ALL frameworks in the literature would classify this program as
   non-monotone and therefore "requiring coordination." They are correct
   that the INTERNAL specification requires coordination. But they cannot
   observe that the EXTERNAL output (the log) is future-monotone.
   
   Complete CALM can: it analyzes the output specification (log prefixes
   ordered by prefix extension) and correctly identifies it as
   coordination-free to consume.

### What B-K's Theorem 3 tells us:
Their Theorem 3 says F(Id+All+L) = B (with a leader, everything is
computable). This is the closest they get to our universal construction.
But note: they need LEADER as a system relation (given for free). They
cannot analyze HOW the leader is established (that's outside their model).
We can: establishing the leader is one round of distributed coordination
(membership), after which everything is coordination-free.

## Credit and Transparency (Point 2)

### What B-K scooped us on (within their framework):
1. **Non-deterministic behaviors**: They handle non-deterministic problems
   (multiple valid outputs). We should credit this -- our Obs(H) being
   set-valued is the same idea.
2. **The coordination spectrum**: They parameterize by constraint C and
   get a spectrum. We should credit this -- our "varying the specification"
   is the same structural move.
3. **The meta-theorem (Theorem 6)**: They prove a single theorem
   parameterized by C. We should credit this -- our subsumption theorem
   is the same structural move at a higher level of generality.

### What we add that they don't have:
1. **Model-independence**: We don't assume transducers, relations, or any
   computational model.
2. **The separation**: We can see past coordination boundaries.
3. **The universal construction on membership**: They need Leader as a
   given system relation; we show membership suffices and explain how
   authority chains work.
4. **Arbitrary outcome orders**: They use set inclusion on output facts;
   we allow any partial order (prefix extension, lattice order, etc.).

### How to be transparent in the paper:
In the "CALM as an Instance" subsection, we should say something like:
"Baccaert and Ketsman [2026] independently arrived at a similar structural
insight within the transducer model: their Theorem 6 parameterizes
coordination-freedom by a configuration constraint C, yielding a
coordination spectrum. Our subsumption theorem (Theorem X) shows that
their C-monotonicity is an instance of future-monotonicity under the
natural instantiation. The key advance of Complete CALM is not the
parameterization (which B-K also achieve within their model) but the
model-independence and the separation theorem, which requires reasoning
about output semantics rather than program text."

## Li & Lee (Point 4)

### Their framework (from what we know):
- Replicated-object architecture
- Coordination-freedom characterized in terms of replica consistency
  under growing input sets
- CALM-style equivalence: monotonicity = coordination-freedom
- Model assumes replication and merge semantics as primitives

### Key differences from B-K and Ameloot:
- They work in a REPLICATED OBJECT model, not a transducer model
- Their "input growth" is writes arriving at replicas
- Their "monotonicity" is about merge-compatibility of replica states

### How to handle them:
1. Their model is ALSO an instance of Complete CALM:
   - Histories = sequences of writes and merges at replicas
   - Outcomes = replica states, ordered by the merge lattice
   - Future = more writes arriving
   - Future-monotone = merge-compatible (states only grow in the lattice)

2. They ALSO suffer from the syntactic limitation:
   - They analyze the replicated object's merge function
   - They cannot see past a coordination layer that produces a
     merge-compatible output from non-merge-compatible internals

3. Their contribution relative to Ameloot/B-K:
   - Different computational model (replicated objects vs transducers)
   - Same structural result (monotonicity = coord-free)
   - Same limitation (syntactic, model-bound)

4. In the paper, we should:
   - Acknowledge their independent contribution in a different model
   - Show it's an instance of Complete CALM under the natural instantiation
   - Note that the separation theorem applies to their setting too
   
### The subsumption for Li & Lee:
Define Spec_LL(O) for a replicated object O:
- E = write events, merge events, read events
- Obs(H) = set of states observable at replicas after history H
- Ord = the merge lattice order (s1 <= s2 iff s1 join s2 = s2)

Then: O is coordination-free in Li-Lee's sense iff Spec_LL(O) is
future-monotone.

This should be straightforward to prove since their "replica consistency
under growing input" is exactly "outcomes refine under history extension"
when the outcome order is the merge lattice.

## Other Ameloot Papers (Point 1)

### Papers we couldn't fetch but know about from DBLP:

1. **Ameloot 2015 "Deciding Determinism with Fairness for Simple Transducer
   Networks" (TODS)**
   - Decidability result: can you decide if a transducer network is
     deterministic (consistent) under fairness?
   - Relevant to us: shows that even CHECKING consistency is non-trivial
     in the transducer model. Our framework sidesteps this by working at
     the specification level.

2. **Ameloot, Van den Bussche 2012 "Deciding Eventual Consistency for a
   Simple Class of Relational Transducer Networks" (ICDT)**
   - Decidability of eventual consistency for restricted transducers
   - Relevant: shows the transducer model has decidability issues that
     our specification-level approach avoids.

3. **Ameloot, Van den Bussche 2014 "Positive Dedalus Programs Tolerate
   Non-Causality" (JCSS)**
   - Shows positive (monotone) Dedalus programs produce the same result
     regardless of message ordering (non-causality tolerance)
   - VERY relevant: this is essentially saying "monotone programs are
     coordination-free" in the Dedalus setting. It's another instance
     of CALM. Our framework subsumes it: positive Dedalus programs
     induce future-monotone specifications.

4. **Ameloot, Ketsman, Neven, Zinn 2015/2017 "Datalog Queries Distributing
   over Components" (ICDT/TOCL)**
   - Characterizes which Datalog queries can be evaluated by processing
     connected components independently
   - Related to coordination-freedom: if a query distributes over
     components, it can be evaluated without cross-component coordination
   - In our framework: distributing over components = the specification
     restricted to each component is future-monotone independently

5. **Ameloot, Geck, Ketsman, Neven, Schwentick 2017 "Parallel-Correctness
   and Transferability for Conjunctive Queries" (JACM)**
   - About parallel evaluation of CQs: when can a CQ be correctly
     evaluated on a single round of parallel computation?
   - Less directly relevant to coordination-freedom per se, more about
     parallel query processing. But the "single round" aspect connects
     to our "one round suffices" universal construction.

### Assessment:
None of these papers contain results that would challenge our subsumption
claim. They are all:
(a) Within the transducer model (or Dedalus, which maps to transducers)
(b) About decidability/complexity of properties within that model
(c) Instances of the general pattern: monotonicity = coordination-freedom

The "Positive Dedalus" paper (3) is worth citing as another instance we
subsume. The "Distributing over Components" paper (4) is worth mentioning
as related to our applications (it's about when queries can be evaluated
without cross-partition coordination).

## Summary: What We Need to Do

1. **Subsumption theorem**: State and prove that C-monotonicity (B-K) is
   equivalent to future-monotonicity under the natural instantiation.
   This single theorem subsumes Ameloot 2013, Zinn 2012, B-K 2026.

2. **Li-Lee instantiation**: Show their replicated-object coordination-freedom
   is also an instance (straightforward, merge-lattice order).

3. **Be transparent about B-K's contributions**: Credit their parameterization
   and non-deterministic behaviors. Our advance is model-independence +
   separation + universal construction.

4. **Validate the separation clearly**: Show with a concrete example that
   a Paxos-implementing transducer is classified as "non-monotone/requires
   coordination" by ALL prior frameworks, but its output is correctly
   identified as coordination-free by Complete CALM.

## Li & Lee 2025: Full Analysis

### Their Framework (ONE formalism, not two)
- **Abstract Data Type**: (W, Q, M, s0) over domains (S, I, V)
  - W: write function (S × I → S)
  - Q: query function (S → V)  
  - M: merge function (S × S → S)
  - s0: initial state
- **Coordination function**: F : X → 2^C (maps total inputs to allowed clauses/traces)
- **Problem**: (P, X, V, ≤) where ≤ is a partial order on outputs
- **Clause**: execution trace built from W and M operations
- **Clause partial order**: c1 ⪯ c2 if c1 is a "sub-clause" (partition) of c2

### Their Key Definitions
- **Confluent** (Def 5.4): F(x) contains ALL clauses with input set x
  (any ordering/distribution of inputs is allowed)
- **Consistent under partition** (Def 5.7): for all c0 ⪯ c in F(x),
  Q(E(c0)) ≤ Q(E(c))
  i.e., query output at any prefix is ≤ query output at the full execution
- **Coordination-free** (Def 5.8): confluent AND consistent under partition
- **Monotonic problem** (Def 6.2): x1 ⊆ x2 ⇒ P(x1) ≤ P(x2)

### Their CALM Theorem (Corollary 6.5)
A problem has a coordination-free implementation iff it is monotonic.

### The Bridge to Our Framework
Their "consistent under partition" IS our future-monotonicity:
- Their "clause c0 ⪯ c" = our "history H1 ⊑ H2" (prefix/sub-execution)
- Their "Q(E(c0)) ≤ Q(E(c))" = our "o ∈ Obs(H1) implies ∃o' ∈ Obs(H2) with o ⪯ o'"
- Their partial order (V, ≤) = our outcome order (O, ⪯)

The mapping is essentially identity under renaming.

### Do They Suffer from the Syntactic Limitation? YES.
Their framework analyzes the PROBLEM FUNCTION P directly:
- P : X → V maps total inputs to outputs
- Monotonicity is P(x1) ≤ P(x2) when x1 ⊆ x2

If you implement Paxos to produce an ordered log, then apply some
computation to the log:
- The INTERNAL state of Paxos (ballots, quorum counts) is non-monotone
- Their framework would need to analyze the COMPOSED system
- The composed system's "problem function" includes Paxos internals
- They cannot separate "Paxos is non-monotone internally" from
  "the output of Paxos is monotone"

Specifically: their Definition 5.7 requires Q(E(c0)) ≤ Q(E(c)) for ALL
sub-clauses c0 of c. But a sub-clause of a Paxos execution might be in
a state where the ballot is being contested (non-monotone intermediate
state). The query output at that intermediate state might not satisfy
the ≤ relation with the final output.

### What They Contribute That We Should Credit
1. **The partial order on outputs as consistency**: Their Definition 4.4
   defines consistency as a partial order on V. This is essentially our
   outcome order. They arrived at this independently.
2. **Separation of coordination and computation layers**: Their model
   explicitly separates F (coordination) from RO (computation). This is
   a good structural insight.
3. **The "consistent under partition" definition**: This is essentially
   future-monotonicity stated in their language. They arrived at it
   independently from a distributed-systems (not database) perspective.

### What We Add
1. **Model-independence**: They assume replicated objects with W/Q/M.
   We assume nothing about the computational model.
2. **The separation theorem**: They cannot see past coordination boundaries.
3. **Arbitrary history structure**: Their "clauses" are trees of W and M
   operations. Our histories are arbitrary partial orders (Lamport histories).
   This matters for specifications that don't decompose into write+merge
   (e.g., linearizability, isolation levels).
4. **The universal construction**: They don't have an analog.

### How to Handle in the Paper
Li & Lee independently arrived at essentially the same characterization
(monotonicity = coordination-freedom) in a replicated-object model, with
the partial order on outputs playing the same role as our outcome order.
We should:
1. Credit them for the independent formulation
2. Note that "consistent under partition" is future-monotonicity in their setting
3. Show their framework is an instance of ours (straightforward instantiation)
4. Note the separation theorem applies to their setting too
5. Note they assume replicated objects (W/Q/M structure) while we don't

## Correction: Li & Lee's Two-Part Definition

Their coordination-free = confluent AND consistent under partition.
These are NOT redundant — they capture different aspects:

- **Confluence**: F(x) contains ALL clauses with input set x.
  The implementation tolerates any ordering/distribution of inputs.
  = "no suppression of admissible futures" = our R_I = A (realize all)

- **Consistent under partition**: Q(E(c0)) ≤ Q(E(c)) for sub-clauses.
  Outputs at prefixes are consistent with outputs at extensions.
  = "outcomes refine as histories grow" = future-monotonicity of output

Together: the implementation realizes all possible executions (confluence)
AND the outputs are monotone along execution prefixes (consistent-under-partition).

In our framework, these two conditions are UNIFIED into possibility
preservation (Poss^I = Poss). Possibility preservation says:
- You realize all admissible histories (≈ confluence), AND
- You never need to suppress any (≈ because outcomes are compatible,
  i.e., future-monotone)

The key structural difference:
- Li & Lee state BOTH as requirements on the IMPLEMENTATION
- We derive the equivalence as a THEOREM: future-monotonicity of the
  SPECIFICATION is necessary and sufficient for a coordination-free
  IMPLEMENTATION to exist

Their theorem: monotonic problem ⟺ ∃ coord-free implementation
Our theorem: future-monotone spec ⟺ ∃ coord-free implementation

Same structure, same result, different formalism. The mapping is:
- Their "monotonic problem (P, X, V, ≤)" = our "future-monotone spec (E, Obs, ⪯)"
- Their "confluence" = our "R_I = A" (in the sufficiency construction)
- Their "consistent under partition" = our "future-monotonicity implies
  Poss^I = Poss" (the content of the sufficiency proof)

Without confluence, an implementation could be "consistent under partition"
trivially by restricting to one trace. Confluence prevents this — it's the
"no coordination" part. Consistent-under-partition is the "correctness
despite no coordination" part. Together = coordination-free.
