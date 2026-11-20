# Appendix G (Classical Problems in Distributed Computing): status notes

Recorded 2026-11-21 so nuance from the helper threads is not lost.
Appendix G = `appendices/classical-problems.tex`, label `app:additional-applications`
(the paper's PODC-relevance appendix; author wants it on par with the 2PL/MVTO material).

## Branches (neither merged to main)

- `classical-problems` @ 266c9313: first draft (helper 6ac3ec5a). Superseded.
- `classical-problems-2` @ a9a1fb45: second draft (helper 5a850c90), based on the first
  with main merged at the time. Validated: Lean builds, no sorry, main unrated 0,
  main.pdf 46 pp / cidr.pdf 14 pp, 0 unresolved refs, 0 "[?]" citations.
  ~4,575 words incl. acks. Not merged; awaiting author answers below.
  Main has moved since (intro edits, appendix tightening); expect a merge.

## Author decisions so far (from discussion)

- Criterion for inclusion: report a topic only where the framework hits what the PODC
  literature celebrates; otherwise drop it.
- Causal FIFO queue (sequence/prefix order) as in attic/pods27: NOT monotone in our
  framework (two concurrent enqueues give dequeue sequences with no common extension;
  fiber not directed; Relational Monotonicity does hold). It was meant as a maximal-frontier
  witness, so drop it in that form. Author asked to recover a queue analogue as a partial
  (causal) order on inputs and outputs and show *that* is maximal. (Done in draft 2, see below.)
- Renaming: author was not convinced the framework cannot separate (2n-1)-renaming from
  tight renaming; suggested "shared memory is a single participant with a request queue
  managing all state". Helper 2 worked it (see Q2 below): no mechanical recovery.
- Snapshots: author wants the framework to separate Chandy-Lamport from atomic snapshots
  w.r.t. needing coordination. (Done in draft 2.)
- Leader election: use the standard literature definition (see below).
- Herlihy hierarchy via Proper Coordination with object levels as stages: investigated (Q4).
- Table referred to in discussion = `tab:classical-problems` (classification table in G.1).
- Title confirmed: "Classical Problems in Distributed Computing".

## Draft 2 outline (classical-problems-2)

1. Three patterns (`app:classical-patterns`): Lemma `lem:accumulating` (sets of facts that
   stay permitted and close under union are monotone; works with max, e.g. counter),
   Lemma `lem:order-commitment` (two outputs ordering concurrent events oppositely =>
   non-monotone; non-directed fiber if at one input), Lemma `lem:bounded-values` (k+1 rows
   deciding distinct values against bound k => non-monotone). Paragraph on what Complete
   CALM / No-commitment test / Complete CAP (E=P) conclude. Table `tab:classical-problems`
   now column-width, [t], in this subsection (draft 1 had a table* landing 2 pages late).
2. Broadcast: reliable, causal, grow-only counter, total-order broadcast; framework draws
   the line where Chandra-Toueg's TOB = consensus equivalence does.
3. Consensus: committed authority, then monotone evidence (`app:consensus`,
   Prop `prop:monotone-evidence`, eq `eq:authority-refinement`); which Paxos/Raft steps
   need commitments (choosing a value in a slot does; certified evidence/quorum
   certificates are monotone); Multi-Paxos/Raft/Mencius placement. k-set agreement reduced
   to one sentence (bounded-values pattern). New "Shared memory" paragraph (see Q2/Q4).
4. Leader election (new). See below.
5. Snapshots, Prop `prop:snapshots` (new). See Q3.
6. Queues, Prop `prop:causal-queue` (new). See Q1b.
7. Search structures, Props `prop:persistent-forwarding`, `prop:remembered-claims` (new). See Q1a.
Removed vs draft 1: causal FIFO subsection, renaming subsection, comparable-views atomic
snapshot, separate k-set subsection, eq `eq:tight-renaming`. Acks block stays at file end.

## Research findings (helper 2 memo + final report)

### Q1a B-link trees / persistent forwarding (Lehman-Yao)
- Claims (k, pi) = "search for k from position pi finds k". Spec for validity map V permits
  any subset of V(h), ordered by inclusion; stronger = pointwise smaller V. LM iff V grows
  along histories.
- (i) Remembered-output (attic thm:monotone-hull): least monotone V containing the exact
  claims X is X^(h) = claims exact at some prefix of h. Forward reachability C contains X^
  but is NOT least: e.g. key inserted into new right sibling after a split, (k,a) in C via
  link but never exact.
- (ii) Requiring V to depend only on the current structure (a lookup inspects structure,
  not history), and continuations depending only on current snapshot: least such relaxation
  is X~(G) = claims exact at some snapshot on some legal path to G. C is snapshot-based and
  monotone, so X~ subset of C.
- Result: C is at the frontier iff hypothesis (H): every forwarding claim at G was exact at
  some earlier snapshot on some legal path to G. Expected to hold for an abstract B-link
  model (inserts commute before splits) but NOT proved; paper states the iff and leaves (H)
  open for Lehman-Yao. Strict-containment example (C larger than history-remembered claims)
  dropped (not formalized).
- Open for author: keep B-link subsection with open condition, or trim to monotonicity only?

### Q1b Queue (clean maximality result)
- Input: causal history h of enqueues. Output: dequeue report (D,<): set D of dequeued
  enqueues with strict order < guaranteed among them. Order used in draft: "extension":
  D subset of D', old items keep their order, and D is a down-set of (D',<') (later items
  never precede earlier ones). On total orders = prefix order. (Memo's "add order info"
  variant is not transitive; theorem unaffected.)
- Causal queue Q permits (D, ->|D) for every causally down-closed D. Satisfies LM (unions
  of down-sets carry causal order).
- Theorem: any spec T with directed fibers (so any monotone T) that, for each event b,
  permits some output with set = down-closure of b (items dequeuable once causal
  predecessors are) orders only causally ordered pairs. Proof: a<b with a,b concurrent;
  common upper bound has a<b and down(b) must be a down-set of it, forcing a in down(b).
- Corollary: if T also permits every down-set and its orders contain causality, T = Q.
  Q is the unique monotone queue spec letting items be dequeued as soon as their causal
  predecessors are. Reporting order between concurrent enqueues breaks directedness at one
  input. Proved directly, not via thm:product-frontier or the order lemma.
- Open for author: is "dequeue report" (set + guaranteed order) acceptable as queue output?

### Q2 Renaming / Q4 Herlihy hierarchy (no mechanical recovery)
- Old attic/podc26 renaming witness was wrong: adding q to n participants holding 1..n,
  q takes n+1, valid tight renaming; Relational Monotonicity holds. Real failure:
  concurrency (p alone and q alone both must take name 1; no injective common extension
  at {p,q}). That witness applies for any bound with f(1)=1, incl. 2n-1, so it does not
  separate the bounds.
- With memory as one participant serializing a request queue (sec 6.5): serialization is
  the ordering commitment; memory's outputs are a log (chain). Any algorithm's decision
  map (log -> decisions so far) is monotone (irrevocable, depends on log prefix), so by
  Proper Coordination the pipeline is proper for every algorithm/task/object, incl.
  consensus over plain registers. Lean: `monotone_stage_proper`; also the request queue
  = tobSpec is not LM and needs a commitment.
- The 2n-1 vs n and register vs CAS separations concern wait-free TERMINATION; LM is a
  safety condition and the never-deciding stage is always monotone. Over registers, safe
  consensus exists ("wait for p1") but does not terminate if p1 crashes.
- Faithful reformulation exists but only restates the classical definition: stage-1
  outputs = partial view maps of iterated immediate snapshot, ordered by extension, each
  process decides its own name under owner deployment, rows determined by own view;
  monotone across partitions = valid simplicial map; Deployment Availability = wait-free
  termination; monotone decision map over views <=> locality. Then "monotone across
  partitions with availability under a view-determined deployment" <=> wait-free solvable
  in r rounds. n=2: 3 names solvable in one round; 2 names impossible in every round count
  by classical path-parity + comparison-based symmetry (topology, not a framework
  consequence). One-round n=2 instance could be done in Lean; all rounds is substantial.
- Q4: "n-process consensus over level-l stage needs no further commitment iff n <= l" is
  false as a safety statement ("if" holds for every l). With termination it is Herlihy's
  theorem, per object by valency arguments.
- Draft 2: no renaming subsection; shared-memory paragraph in consensus subsection says
  the hierarchy is a termination property specs don't express.
- Open for author: framing of the shared-memory paragraph OK? Want the deployment-level
  reformulation of wait-free renaming added (not in draft)?

### Q3 Snapshots (clean separation)
- Input: causal history of updates and scans at processes. Outputs: partial tuples, one
  view per process; view maps the process's scans to sets of updates. Owner deployment:
  each process answers its own scans.
- Chandy-Lamport-style view: cut C_s for scan s is causally down-closed, contains every
  update causally before s and none causally after s. (Draft text says global snapshots
  record consistent cuts and these two conditions tie the cut to the scan; does not
  attribute the two conditions to Chandy-Lamport.) Monotone across partitions under owner
  deployment via thm:product-frontier(1); Complete CAP for a deployment holds.
- Atomic snapshot: strengthening selecting tuples explained by one strict total order L
  extending causality, each view = updates before s in L. Witness: u_p -> s_p, u_q -> s_q,
  processes concurrent; answers {u_p} for s_p and {u_q} for s_q each realizable but
  together force a cycle in L. Not monotone across partitions under owner deployment;
  C-L permits both answers.
- Stated as "monotone across partitions under the owner deployment" (product-interface
  machinery), not plain LM: under LM with E=P two answers to the same scan already conflict.
- Remark (optional): atomic snapshot satisfies Relational Monotonicity, so monotone under a
  single-authority deployment, matching wait-free implementations from registers (memory
  makes the commitments). Full maximality "C-L is strongest" via product-frontier(2)
  plausible, needs local conservativity (linear extensions in Lean); deferred.

### Leader election
- Standard: exactly one process eventually outputs leader. Solvable deterministically in
  failure-free async networks with UIDs when ring/membership known (LeLann, Chang-Roberts,
  Hirschberg-Sinclair); impossible in anonymous rings (Angluin); Omega weakest failure
  detector for consensus (Chandra-Hadzilacos-Toueg 1996).
- Caution: if the input includes the participant list and leader = max(All), no messages
  needed at all. Meaningful version: input = fixed list All plus a partial map
  participant -> candidate / not-candidate, ordered by extension; output max of candidates
  once map covers All, else bottom. Monotone (only waits). Without All: input = candidacies
  heard; "exactly one leader among candidates" fails bounded-values (k=1), needs a
  commitment (closing the candidate list); partitioned sides can elect different leaders.
  On a ring, the message returning to its sender plays the role of All.
- Open for author: candidacy-status model OK?

## Lean (branch classical-problems-2)
- New library file lean/CoordCriterion/Appendix/ClassicalFrontiers.lean (namespace
  CC.Apps): queue (DReport + order, cqSpec, cqSpec_liftedMono, directed_orders_causal,
  monotone_orders_causal, cq_unique, total_report_not_directed); lookup (boundSpec_
  liftedMono_iff, remembered_*, StateDet, stateRemembered_*, restr_stateDet,
  fwd_contains_stateRemembered, fwd_eq_iff); snapshots (ClCut, ClView, cl_continue,
  cl_antichain, cl_nonempty, clSpec, cl_monoAcross via product_monoAcross, cl_cap via
  deployment_complete_cap_exists, LinExt, linExt_exists, atomicView_cl, atomicStr, atSpec,
  local_not_monoAcross (localized product-frontier(2)), Four witness, atomic_not_monoAcross,
  atomic_no_cap, Four.cl_row); leader (Flat, leaderAllSpec, leaderAll_mono,
  leaderAll_consistent, leaderSpec, leader_not_monotone); memory (funSpec,
  monotone_stage_proper).
- Draft 1 library file lean/CoordCriterion/Appendix/Classical.lean (pattern lemmas, specs,
  k-set, renaming, old queue, snapSpec) still built; old renaming/queue/snapSpec decls no
  longer cited.
- Paper layer lean/CoordCriterion/Paper/AppH_Applications.lean rewritten; gen_index.py now
  labels it "Appendix G ... appendices/classical-problems.tex".
- Citation-only: FLP; Herlihy hierarchy; renaming bounds; Chandra-Toueg; Hadzilacos-Toueg
  broadcast; reliable-broadcast liveness; ring algorithms; Angluin; CHT96; global snapshots
  record consistent cuts; Afek et al. wait-free snapshots; Paxos quorum intersection;
  Multi-Paxos/Raft/Mencius placement; "wait for designated process" register algorithm and
  ring-message intuition (prose, not formalized).
- New bib entries (no DOIs, from memory; spot-check): draft 1: chaudhuri1993more,
  attiya1990renaming, hadzilacos1994modular, defago2004total, ongaro2014raft,
  demers1987epidemic; draft 2: lelann1977distributed, chang1979improved,
  hirschberg1980decentralized, angluin1980local, chandra1996weakest.

## Open questions for the author (consolidated)
1. B-link subsection: keep with open condition (H), trim to monotonicity, or drop?
2. Queue output model "dequeue report" acceptable?
3. Shared-memory paragraph framing (request queue = TOB spec; wait-free hierarchy is a
   termination property) acceptable? Add deployment-level wait-free renaming reformulation?
4. Leader election with candidacy statuses acceptable?
5. Draft 2 intro mentions frontier results for queues/search structures: check tone.
6. Ratings flag paragraphs that could be tightened (draft 1 list: atomic-snapshot,
   k-set witness, evidence-spec definition, queue proof two-direction argument).

## Related pending (not Appendix G)
- Intro "criterion" rewrite (CIDR + main), "lifted monotone" adjective in Def LM, main
  abstract mirror of author's 8b517bcc, main intro automaton paragraph moved after
  commitments, §3.3 complexity remark: applied locally in .infinity/work/sk, NOT yet
  validated/pushed at time of writing.
- Planned: helper to construct a spec with O(n) rows whose runs reach 2^n distinct states
  without commitment (Lean), to firm up the §3.3 complexity paragraph. Do NOT claim
  consistency is hard (Complete CALM makes it polynomial for finite tables); confluence of
  systems may be hard but is unexamined.
