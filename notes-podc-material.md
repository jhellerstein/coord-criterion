# PODC Material Assessment: What to Bring Over

## Material in the PODC paper (body + appendix)

### 1. Full Proof of the Coordination Criterion (App. A)
**Status**: Must include in our appendix.
**Priority**: HIGH — reviewers will want to see it.
**Action**: Copy directly. Already written, just needs reformatting.

### 2. Minimality / Semantic Minimality Proposition (App. B)
**Status**: Should include — it's the formal backing for our "tightness" claim.
**Priority**: HIGH — we claim tightness in the body; the proof must be somewhere.
**Action**: Include in appendix. The proposition shows that any coordination-free
implementation *induces* a partial order under which the spec is future-monotone.
This is the formal content behind "no further generalization is possible."

### 3. Consensus / Authority Closure Analysis (App. A.3)
**Status**: This is excellent material — decomposes consensus into authority
closure (non-monotone) + value exposure (monotone). Directly relevant to our
"well-coordinated" framing: after authority is established, value exposure is
well-coordinated.
**Priority**: MEDIUM-HIGH for appendix. Could strengthen the "well-coordinated"
narrative. But it's distributed-systems material, not core PODS.
**Action**: Include in appendix as an additional application. Reference from body
when discussing the universal construction (authority = membership).

### 4. Snapshots: Partial-Order vs Total-Order Commitments (App. A.5)
**Status**: Beautiful structural insight — "partial-order commitments are monotone,
total-order commitments are non-monotone." This is a general principle that
explains WHY serializability/linearizability require coordination.
**Priority**: HIGH — this should be in the BODY, not just appendix. It's the
structural explanation behind the isolation-levels application.
**Action**: Add 2-3 sentences to the isolation-levels subsection stating this
principle. It's the "why" that makes the result insightful rather than just
a re-derivation.

### 5. k-set Agreement (App. A.6)
**Status**: Distributed-systems material. Shows weakening agreement doesn't
restore monotonicity.
**Priority**: LOW for PODS. Include in appendix for completeness.
**Action**: Appendix only.

### 6. Strong Renaming (App. A.7)
**Status**: Distributed-systems material. Membership-sensitivity as source of
non-monotonicity.
**Priority**: LOW for PODS.
**Action**: Appendix only.

### 7. Extended Related Work (App. D)
**Status**: Has good material on programming languages (Gallifrey, Flo, Dedalus,
Bloom, Lasp) and transactional/weak consistency.
**Priority**: MEDIUM — some of this should be in our related work.
**Action**: Cherry-pick relevant paragraphs for related work section.

### 8. The "Modeling the Specification" remark (Section 3.1 of PODC body)
**Status**: Important methodological point — the specification embodies a modeling
choice; if Obs or Ord is too coarse/fine, you get wrong answers.
**Priority**: MEDIUM — addresses a potential reviewer concern ("what if I choose
the wrong Obs?").
**Action**: Add a brief remark in the Framework section.

## Top Priorities for PODS Acceptance

1. **Full proof in appendix** (items 1, 2) — non-negotiable
2. **Partial-order vs total-order insight** (item 4) — adds depth to applications
3. **Consensus/authority decomposition** (item 3) — strengthens well-coordinated narrative
4. **Modeling remark** (item 8) — preempts reviewer concern

## What NOT to Bring Over

- The "Core Intuition" subsection (replaced by our running example)
- The register/CAP body sections (already incorporated differently)
- The CALM appendix (replaced by our stronger subsumption)
- k-set agreement, strong renaming (too PODC-specific for body)
- The verbose definition-heavy style (already fixed)
