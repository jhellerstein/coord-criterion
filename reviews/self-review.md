# Self-Review: Complete CALM (main.tex)

Systematic line-by-line review for internal inconsistencies, stale text, logical gaps, broken references, and notation issues.

---

## 1. Orphaned/Unused Macros

**Line 43 — `\Expose` macro defined but never used**
```latex
\newcommand{\Expose}{\mathsf{Expose}}
```
This macro is defined in the preamble but never appears in the paper body. Likely a remnant from an earlier draft that used an "Expose" function in the framework.

**Line 44 — `\Reach` macro defined but never used**
```latex
\newcommand{\Reach}{\mathsf{Reach}}
```
Same issue. Defined but never referenced anywhere in the document.

---

## 2. Duplicate / Unreferenced Labels

**Lines 1836–1837 — Two labels on the same section, neither referenced**
```latex
\label{app:proofs}
\label{app:cap-formal}
```
The appendix "Complete CAP: Formal Treatment" has two labels (`app:proofs` and `app:cap-formal`), but neither is ever `\ref`'d anywhere in the paper. The `app:proofs` label name is stale—it suggests a generic "proofs appendix" that no longer exists as such. The section is only reached by readers navigating the appendix sequentially; no in-text pointer directs them there.

**Line 1153 — Label `cor:cap` on a `theorem` environment**
```latex
\begin{theorem}[Complete CAP]
  \label{cor:cap}
```
The label prefix `cor:` suggests this was once a corollary. It's now a theorem. The label works but is misleading for maintenance. Similarly `cor:cap-formal` on line 1864.

**Line 1864 — `cor:cap-formal` never referenced**
```latex
\label{cor:cap-formal}
```
The restated theorem in the appendix has a label that is never `\ref`'d.

---

## 3. Structural / Logical Issues

**Lines 923–970 — Theorem 2 (Complete CALM) has two proofs**

Theorem~\ref{thm:complete-calm} (line 923) is stated, then given a one-line proof ("Immediate from Theorem 1"), then an *example* intervenes, and then a second `\begin{proof}[Proof sketch]` block appears (line 953) giving a direct sufficiency/necessity argument. This is confusing: the reader encounters two proofs for the same theorem with different content. The second proof sketch uses the semantic definition (Definition 5) rather than the operational theorem, making it a genuinely different argument. Consider either:
- Removing the proof sketch (since the operational theorem already proves it), or
- Labeling the second block as a "Remark" or "Alternative proof sketch" to avoid the appearance of redundancy.

**Lines 654–660 — Definition of "future-consistent" vs. monotonicity**

Definition 6 (future-consistent outcome) quantifies over *every* future: "for every future $H'$ of $H$, there exists $o' \in \Obs(H')$ with $o \preceq o'$." This is exactly the monotonicity condition applied pointwise. The paper later defines monotonicity (Definition 8, line 903) identically but at the specification level. The relationship is stated informally but never as a formal lemma (monotone ⟺ every outcome at every history is future-consistent). This is logically obvious but the paper treats them as if they need separate proof (the "proof sketch" on line 953 essentially re-derives this equivalence). A one-line lemma bridging them would tighten the exposition.

**Lines 806–811 — "Response totality" assumption introduced mid-proof**

The sufficiency proof of Theorem 1 introduces an assumption ("We assume *response totality*") that is not part of any prior definition. It's a well-formedness condition on specifications but is never formally stated as a definition or requirement. This is a gap: the theorem statement says "a specification admits a correct coordination-free implementation iff it is monotone," but the proof actually requires response totality as a precondition. Either:
- Add response totality to the specification definition (Definition 4), or
- State the theorem with this precondition explicit, or
- Argue that monotonicity implies response totality (the parenthetical on line 811 gestures at this but doesn't prove it).

**Lines 619–635 — "Admissible histories" definition uses $\hext$ in a potentially confusing direction**

The definition says $\mathcal{A}(H_{\mathit{iface}}) = \{H \in \Hist \mid H_{\mathit{iface}} \hext \In(H)\}$. This means the interface projection of $H$ is a *future* of the given interface prefix. But $\hext$ was defined (line 465) as "$H_2$ is a future of $H_1$" when $H_1 \hext H_2$. So the condition reads "$H_{\mathit{iface}}$ is extended by $\In(H)$"—i.e., the full history's interface projection extends the given prefix. This is correct but the direction is easy to misread because $\hext$ looks like "is a prefix of" but is defined as "the left side is the prefix." Consider a brief clarifying note.

---

## 4. Terminology / Notation Inconsistencies

**Abstract (line 68) — "future-monotonicity" mentioned but never defined**

The abstract says the criterion is "future-monotonicity" but this exact term never appears in the body. The body uses "monotone" (Definition 8) and "future-consistent" (Definition 6) as the key terms. The abstract's phrasing "iff its outcomes are monotone—iff the physical growth of exposed observations..." conflates two characterizations without the term "future-monotonicity" being grounded anywhere.

**Line 1540 — Proposition statement uses $T$ without introduction**
```latex
$\Spec_I$ is monotone iff $T$ is $I$-confluent with respect to $I$.
```
The variable $T$ (transaction set? update set?) appears here for the first time in this subsection. The preceding paragraph discusses "an application invariant" and "merging any two invariant-preserving states" but never introduces $T$ as a formal object. The reader must guess that $T$ refers to the set of allowed transactions/updates.

**Lines 2127, 2130 — Inconsistent hyphenation of "causal-FIFO" in math mode**

Earlier (lines 2078, 2098, 2109) the paper uses `\mathit{causal\text{-}FIFO}` (with `\text{-}`), but on lines 2127 and 2130 it switches to `\mathit{causal-FIFO}` (plain hyphen in math mode). The plain hyphen in math mode renders as a minus sign. This is a typographic inconsistency—use `\text{-}` consistently.

**Line 1195 — `Table~\ref{tab:mechanisms}` placement**

The text says "Table 1 classifies well-known mechanisms" but the table is placed *after* this sentence using `[t]` float. In a two-column format this is fine, but worth verifying the table doesn't float to a confusing location.

---

## 5. Potential Logical Gaps

**Lines 857–885 — Necessity proof assumes the witness future $H_2$ is reachable without input at $p$**

The necessity proof constructs execution $\beta$ where "the global history reaches $H_2$ (the additional events in $H_2 \setminus H_1$ occur without input actions at $p$)." This requires that the future-inconsistency witness $H_2$ can be reached by events *not* involving new input actions at $p$. The proof parenthetically says these events occur "either at other processes, or as consequences of prior events at $p$ that have already been processed." But this isn't guaranteed for arbitrary witnesses—what if the only future-inconsistency witness requires a new invocation at $p$? The proof needs the witness to be constructible from remote activity alone. This is true for the distributed case (remote processes can act independently) but less obvious for the single-process case. The paper claims the criterion applies to local concurrency too (line 766), so this gap matters.

**Lines 1160–1175 — Complete CAP sufficiency proof is too brief**

The $(\Leftarrow)$ direction says "every process can safely expose any admissible outcome immediately—both availability and consistency hold." But this doesn't construct a protocol. Unlike the Complete CALM proof (which constructs the causal-view protocol), the CAP sufficiency just asserts the conclusion. A reader might ask: *how* does the process choose which outcome to expose? The causal-view protocol from Theorem 1 works here too, but the connection should be explicit.

**Lines 2023–2048 — Register frontier maximality proof has a gap**

The maximality proof for causal consistency constructs a scenario where "the only causally-consistent return value is $v$" (line 2042). But this requires that no *other* write in $r$'s causal past writes a different value. The proof states this assumption ("and no other write in $r$'s causal past writes a different value") but doesn't argue that such a history is always constructible for an arbitrary removed edge. The proof needs to show that for *every* edge in $\Ord_{\mathit{causal}}$, a forcing history exists—not just for edges of the form "append a read." Since $\Ord_{\mathit{causal}}$ is prefix extension, all edges *are* of this form, so the argument works, but this should be stated explicitly.

---

## 6. Missing/Broken References

**No broken `\ref` commands detected.** All `\ref{...}` targets have corresponding `\label{...}` definitions.

**No missing `\cite` keys detected.** All citation keys used in the paper appear in `references.bib`.

**However:** Several bib entries have quality issues (missing page numbers, empty publishers) that will produce warnings but not errors. Notable: `attiya2023arbitration` has year 2023 in the key but 2025 in the `year` field.

---

## 7. Redundancy

**Lines 929–932 and 953–970 — Duplicate proof content for Theorem 2**

As noted above, the Complete CALM theorem gets both a one-line proof (delegating to Theorem 1) and a standalone proof sketch. The proof sketch (lines 953–970) essentially restates the semantic equivalence that *is* the content of Theorem 1's proof. This is redundant—one or the other should be removed or clearly distinguished.

**Lines 183–231 (Contributions list) vs. Abstract (lines 62–97)**

The contributions enumeration in the introduction substantially overlaps with the abstract. This is normal for a paper, but contribution item 1 repeats almost verbatim what the abstract says. Not a bug, but worth noting for tightening.

---

## 8. Minor Issues

**Line 50 — Title says "Coordination Analysis for Specifications"**

The subtitle "Coordination Analysis for Specifications" doesn't appear elsewhere. The body consistently uses "Complete CALM" as the name. The subtitle is fine but slightly disconnected from the paper's internal terminology.

**Line 1178 — Informal relationship statement could be tighter**
```
monotone ⟹ distributed-monotone ⟹ CAP-free,
and monotone ⟹ coordination-free.
```
The term "CAP-free" is used here but never defined. From context it means "admits a CAP-compliant implementation," but the paper elsewhere uses "admits a consistent, available, partition-tolerant implementation." This is the only occurrence of "CAP-free."

**Line 377–378 — Forward reference to Appendix~\ref{app:universal} before the framework is established**

The text says "establishing membership and a consistent input-ordering authority isolates all coordination into a single reusable layer; downstream evaluation of the ordered stream is coordination-free (Appendix~\ref{app:universal})." This appears in the Framework section introduction, before the reader has the definitions needed to understand what this means. It's a valid forward reference but may confuse readers encountering the framework for the first time.

**Line 1682 — Section~\ref{sec:crdts} forward-referenced from Replica Consistency subsection**

The text says "Section~\ref{sec:crdts} develops this connection formally" but sec:crdts *precedes* sec:replica-consistency in the document (CRDTs is 5.3, Replica Consistency is 5.4). This is a backward reference, not a forward reference—the phrasing "develops this connection" suggests the reader hasn't seen it yet, but they have. Should say "Section~\ref{sec:crdts} developed this connection" or restructure.

**Line 2312–2314 — Immerman–Vardi characterization is slightly misattributed**

The paper says "This is the same mechanism underlying the Immerman–Vardi theorem: bounded quantification over a known domain is expressible in fixpoint logic." The Immerman–Vardi theorem is about capturing PTIME on ordered structures via fixpoint logic—it's not primarily about "bounded quantification over a known domain." The analogy is reasonable but the characterization is loose enough that a knowledgeable reviewer might object.

**Line 1539–1540 — Proposition statement is asymmetric**
```latex
$\Spec_I$ is monotone iff $T$ is $I$-confluent with respect to $I$.
```
"$T$ is $I$-confluent with respect to $I$" is tautological phrasing—$I$-confluence is already defined with respect to $I$. Should be "$T$ is $I$-confluent" (dropping "with respect to $I$").

---

## 9. Summary of Severity

| Category | Count | Severity |
|----------|-------|----------|
| Orphaned macros | 2 | Low (cosmetic) |
| Unreferenced/stale labels | 4 | Low (maintenance) |
| Duplicate proofs / redundancy | 1 | Medium (confusing) |
| Undefined assumptions in proofs | 1 | Medium-High (response totality) |
| Logical gaps in proofs | 2 | Medium (necessity proof scope; CAP sufficiency) |
| Terminology inconsistencies | 3 | Medium (future-monotonicity, $T$, CAP-free) |
| Notation inconsistencies | 1 | Low (causal-FIFO hyphen) |
| Backward reference phrased as forward | 1 | Low |
| Misattribution | 1 | Low |

The most substantive issues are: (1) the "response totality" assumption that appears mid-proof without formal status, (2) the necessity proof's implicit assumption that the witness future is reachable without input at the responding process, and (3) the duplicate proof blocks for Theorem 2 that may confuse reviewers about what exactly is being proved where.
