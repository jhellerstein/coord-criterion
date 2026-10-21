# Manual re-review: changed prose in Abstract, §1, §2

Baseline `c7ef9a0` (last manual pass) → `fac66a1` (PR #4 head).
Line numbers refer to `fac66a1`; they will drift after later edits.
Everything not listed is unchanged and can be skipped.
The word-level diff of the three files is at the end of this note.

## Abstract (`main.tex`)

- 58: "universal" → "single".
- 66–67: Functional CALM claim: "consistent exactly when it is monotone, and
  then no output ever requires a commitment."
- 72–77: determination sentence (input events …; output events may carry
  commitments); Lifted Monotonicity defined inline as the common-refinement
  condition.
- 83–88: Complete CAP in Brewer framing; Gilbert–Lynch as special case.

## §1 Introduction (`sections/introduction.tex`)

- 41: "within spec" → "it permits".
- 58, 90: small rewording ("We first focus…").
- 72–73: "a monotone specification can emit every output it permits without
  [a commitment]."
- 78, 146: "Lamport history" → "distributed history".
- 83–87 (new): state determined by input → convergence sentence.
- 92–94: determination sentences trimmed.
- 99–111 (new): shared common-refinement condition; mutual exclusion as the
  consequence when Consistency is required; safety vs. liveness. Paragraph was
  split.
- 124–136: CAP paragraph rewritten.
- 152–156: contribution 4.
- 166–179: roadmap paragraph.

## §2 Functional CALM (`sections/functional-calm.tex`)

- 17–19: section roadmap sentence.
- 86–96: Fig 1 caption/legend (gray = removed; struck = removed by commitment;
  gray alone = retired).
- 136–143: panel (d) narration — registrar emits ⊥ and seals in one event.
- 174–180: informal output-event description ("Emitting o is a promise").
- 192–196 (new): obstruction stated on the table: (x··,⊥), (xx·,x) at xxx.
- 198–203: informal Consistency wording.
- 223–239: Fig 2 summary table (new rows).
- 258–276: Def Functional ordered specification — totality stated separately;
  "ordered specification" umbrella term.
- 297: "Functional monotonicity" definition name.
- 344–347: Def Commitment basis — "seals".
- 377–378: s_o gloss.
- 401–412: "input retirement" named; non-lattice example to footnote.
- 423–450: Defs Output event, Exposable (now formal and general).
- 452–489: Prop Event contract (four clauses, motivating sentence, new proof).
- 491–503: Determination paragraph (moved here; "sealed" state redefined).
- 508–523: §2.4 roadmap (merged with old opener).
- 538–542: commitment-free run, "reachable without commitment".
- 562–575: proof of Lemma canonical-equivalent.
- 602–615: proof of Lemma run-residual, plus new example.
- 620–630: Def Consistency (any ordered specification).
- 632–660: Prop Survivor test (renamed), functional remark.
- 662–671 (new): "runs never diverge irreparably" paragraph.
- 681–718 (new): Def Common-refinement condition; Thm Common-refinement
  characterization, with election example.
- 720–735: Thm Functional CALM (short proof).
- 737–760 (new): Cor State determined by input.
- 761–787: Prop Exposure boundary (general, new proof).
- 789–813: CALM history / Datalog / CRDT paragraph (moved up) and transition
  to §3; old §2.6 deleted.

Heaviest stretches: 423–489 and 681–787 (formal content, not only prose).

## Word diff

Generated with
`git diff --word-diff=plain c7ef9a0 fac66a1 -- main.tex sections/introduction.tex sections/functional-calm.tex`
(`[-deleted-]`, `{+added+}`).

```diff
diff --git a/main.tex b/main.tex
index 67b7dd1..b543ed6 100644
--- a/main.tex
+++ b/main.tex
@@ -10,6 +10,7 @@

\newtheorem{theorem}{Theorem}
\newtheorem{proposition}{Proposition}
{+\newtheorem{lemma}{Lemma}+}
\newtheorem{corollary}{Corollary}
\newtheorem{definition}{Definition}
\theoremstyle{remark}
@@ -54,7 +55,7 @@ When does a concurrent system inherently require coordination?  CALM, CAP,
CRDTs, Highly Available Transactions, and Invariant Confluence explore versions
of this question in different formal models, making their conclusions hard to compare
or reuse.  We give them a common declarative specification framework and a
[-universal-]{+single+} definition of consistency: confluence of executions admitted by a
specification.  Coordination appears in this declarative model as a
\emph{commitment}: an irrevocable removal of possibilities from the current
specification.
@@ -62,25 +63,29 @@ specification.
\emph{Functional CALM} uses this framework to generalize the original CALM Theorem from Datalog
queries to arbitrary functions between ordered domains.  This makes the familiar
monotonicity test independent of the language or formalism used to express the
function: [-every-]{+a+} functional specification is consistent[-without commitment-] exactly when it is
[-monotone.-]{+monotone, and then no output ever requires a commitment.+}
\emph{Complete CALM} handles \emph{ambiguous} specifications that offer several
outputs for one input, including choices such as transaction order or leader
selection.  As execution narrows the possible outputs, the result moves toward
\emph{determination}; it is \emph{determined} when only one possibility remains.
Determination [-occurs via-]{+has+} two [-kinds of events: inputs-]{+sources: input events+} may make some alternatives
[-unreachable;-]{+unreachable, and output events may carry+} commitments {+that+} exclude alternatives
that would otherwise remain possible.[-The \emph{Lifted-]
[-Monotonicity} criterion characterizes when outputs can be emitted consistently-]
[-without commitment.-]  Complete CALM proves that {+such+} a specification is consistent
exactly when it satisfies [-this criterion.-]{+\emph{Lifted Monotonicity}, which, like functional+}
{+monotonicity, requires outputs permitted at inputs with a common refinement to+}
{+share a refinement permitted there.+}

Representing commitments also lets us verify \emph{Proper Coordination}: whether
a chosen use of coordination is sufficient.  Totally ordered logging and
key-value stores are both non-monotone, yet committing to their shared log order
makes the composed system monotone and consistent.  Finally, Complete CALM
yields a Complete CAP [-theorem, extending CAP's-]{+theorem that makes Brewer's intuition precise for any+}
{+declared consistency guarantee: a system can keep its interface available and+}
{+consistent through partitions exactly when the specification passes the same+}
{+common-refinement test.  Gilbert and Lynch's+} register impossibility [-to classify-]
[-specifications under-]{+appears as+}
the [-paper's interface-wide availability criterion.-]{+special case in which a partition forces a replica to answer before it can+}
{+see a conflicting write.+}
\end{abstract}

\begin{CCSXML}
@@ -117,6 +122,7 @@ specifications under the paper's interface-wide availability criterion.
\appendix
\input{appendices/composition.tex}
\input{appendices/deployment.tex}
{+\input{appendices/cap-response.tex}+}
\input{appendices/commitment-bases.tex}
\input{appendices/frontiers.tex}
\input{appendices/additional-applications.tex}
diff --git a/sections/functional-calm.tex b/sections/functional-calm.tex
index f231c9d..212857b 100644
--- a/sections/functional-calm.tex
+++ b/sections/functional-calm.tex
@@ -14,9 +14,9 @@ through the framework informally on an election.
Section~\ref{sec:functional-specifications} defines specifications, states, and
commitment bases; Section~\ref{sec:functional-events} defines input and output
events; Section~\ref{sec:determination} assembles executions and Consistency;
{+and+} Section~\ref{sec:functional-calm-theorem} {+reduces Consistency to a single+}
{+condition on the specification table,+} proves Functional [-CALM;-]{+CALM,+} and[-Section~\ref{sec:canonical-transition-system}-] identifies
when an output can be emitted without commitment.

\subsection{The framework by example}
\label{sec:election-story}
@@ -83,13 +83,15 @@ emitted without commitment.
    \retired{$xxy$} & \retired{$x$} \\
    \bottomrule
    \multicolumn{2}{@{}l}{\footnotesize possible outputs $\{\bot\}$; sealed and}\\
    \multicolumn{2}{@{}l}{\footnotesize [-determined by commitment;-]{+commitment-resolved;+} $\bot$ is the result}
  \end{tabular}
  \caption{The election specification and three states reached from it.  Only
  rows [-above the-]{+whose+} input {+refines+} $x\cdot\cdot$ are shown.  The current input is
  in bold; shaded cells are the current input and outputs still possible at it.
  Gray: the row has been [-retired by an input event.-]
[-  Struck through:-]{+removed from+} the [-row has been-]{+remainder table.  Gray and struck+}
{+  through: it was+} removed by a commitment; [-no remaining row-]
[-  preserves its contents.-]{+gray alone: it was retired, by an+}
{+  input event or (Figure~\ref{fig:ambiguity-frames}) an output retirement.+}
  Panels (b) and (c) follow input events; panel (d)
  follows an output event for $\bot$ that contains a seal commitment.}
  \label{fig:election-frames}
\end{figure*}
@@ -131,11 +133,14 @@ $\{\bot,x,y\}$.

If $v_2$ instead votes for $x$, as in panel~(c), the upper fiber is $\{x\}$.  The state
is \emph{determined}: input has resolved the ambiguity alone, without commitment.  In
panel~(d), by contrast, a registrar {+emits $\bot$ and+} closes the polls at
[-$xy\cdot$, removing-]{+$xy\cdot$ in the same output event.  Its irrevocable \emph{seal commitment}+}
{+removes+} the still-valid $xyx$ and $xyy$ rows but [-leaving-]{+leaves+} the current input
[-unchanged.-]
[-This is an irrevocable \emph{seal commitment}, which-]{+unchanged, and so+} determines $\bot$.  {+Here $\bot$ needed no commitment; the+}
{+seal is the registrar's choice, not a requirement of the specification.+}
Commitments belong to a system's declared \emph{commitment basis} $\mathcal B$,
not to the specification itself; a system whose polls cannot close does not
have this commitment in its basis.

\begin{figure}[t]
  \centering
@@ -153,25 +158,26 @@ specification itself; a system whose polls cannot close does not have this commi
    \retired{$xxx$} & \retired{$x$} \\ \strikerow
    \retired{$xxy$} & \retired{$x$} \\ \strikerow
    \bottomrule
    \multicolumn{2}{@{}l}{\footnotesize possible outputs [-$\{\bot\}$; determined}\\-]{+$\{\bot\}$;}\\+}
    \multicolumn{2}{@{}l}{\footnotesize [-by commitment; $\bot$ needs no further commitment}-]{+commitment-resolved}+}
  \end{tabular}
  \caption{Panel (a) of Figure~\ref{fig:election-frames} with all outputs
  incomparable, after the registrar emits $\bot$ while closing the polls at
  $x\cdot\cdot$.  Every refinement of $x\cdot\cdot$ is removed by the output
  [-action's-]{+event's+} seal commitment.  Legend as in
  Figure~\ref{fig:election-frames}.}
  \label{fig:nonmonotone-frame}
\end{figure}

\paragraph{Output and consistency.}
An output $o$ is \emph{exposable} when every output still possible at the
current input or a valid refinement [-can preserve-]{+refines+} it.  Hence $\bot$ is exposable
in panels~(a) and~(b), and $x$ in panel~(c).  The atomic $\mathsf{output}(o)$
[-action has three parts: apply-]{+event applies+} any [-required commitments,-]
[-retire rows superseded by-]{+seal commitments needed so that every remaining row's output+}
{+refines $o$, then emits+} $o$,[-and emit $o$.  They occur-] in one transition.  {+Emitting $o$ is a promise:+}
{+from then on, only rows whose outputs refine $o$ remain.+}  The emission [-remains-]{+stays+}
explicit in the history because the uncontrolled environment may use it when
choosing later input.

Figure~\ref{fig:nonmonotone-frame} considers a variant of our example that
changes only the output order: all outputs are incomparable, including $\bot$
@@ -183,10 +189,18 @@ Functional CALM boundary: under the original monotone order, outputs remain
valid as input grows; under the equality order, some outputs require commitment
before they can be emitted.

{+The obstruction is a property of the table alone.  Rows $(x\cdot\cdot,\bot)$ and+}
{+$(xx\cdot,x)$ have the common refinement $xxx$, but under the equality order no+}
{+output at $xxx$ refines both.  A run that emits $\bot$ at $x\cdot\cdot$ and one+}
{+that receives $xx\cdot$ can therefore never meet at $xxx$.+}

Input and output events form a transition system between system states.  A
specification is \emph{consistent} when [-paths with compatible-]{+runs whose+} inputs {+have a common+}
{+refinement+} can [-still-]
[-converge after any way of extending all of those inputs.  Functional CALM proves-]{+always be extended to one common state there.+}
{+Section~\ref{sec:functional-calm-theorem} shows+} that {+the test above is exactly+}
{+what consistency requires: outputs at inputs with a common refinement $j$ must+}
{+share+} a {+refinement at $j$.  For+} functional [-specification-]{+tables this test+} is [-consistent exactly when it-]{+monotonicity,+}
{+which+} is [-monotone.-]{+Functional CALM.+}

The rest of this section formalizes these notions; Figure~\ref{fig:formalism-summary}
serves as a reference.
@@ -206,20 +220,23 @@ serves as a reference.
    \textbf{Shared state and input} & & \\
    \midrule
    specification state & $(i,R)$: \ current input $i$ and remainder table $R\subseteq S$ & Def.~\ref{def:residual-state} \\
    canonical state & [-$\sigma_S(i)=(i,\{(k,o)\in S:i\InputOrd k\})$-]{+$\sigma_S(i)=(i,S[\mathrm{in}\succeq_I i])$+} & Eq.~\ref{eq:canonical-state} \\
    input event & $(i,R)\xrightarrow{\mathsf{input}(j)}(j,R[\mathrm{in}\succeq_I j])$ & [-Def.~\ref{def:io-transition-system}-]{+Eq.~\ref{eq:input-event}+} \\
    \addlinespace
    \textbf{Output handling} & & \\
    \midrule
    output event & [-commitments and retirements,-]{+commitments,+} then emit {+$o$; valid if every remaining row refines+} $o$ & [-Eq.~\ref{eq:output-action}-]{+Def.~\ref{def:output-event}+} \\
    canonical commitment basis & supports every permitted output event & [-Sec.~\ref{sec:functional-specifications}-]{+Def.~\ref{def:canonical-commitment-basis} \\+}
{+    event contract & containment, canonical support, commitment-free events, exposure test & Prop.~\ref{prop:canonical-output-preservation}+} \\
    exposable output & output event uses no commitment & Def.~\ref{def:exposable} \\
    run & finite input and output events & Def.~\ref{def:run} \\
    \addlinespace
    \textbf{Results} & & \\
    \midrule
    consistent & paths confluent: \ $\bigcap_r R_r(j)\neq\varnothing$ at every common refinement $j$ of their current inputs & Def.~\ref{def:consistency}, Prop.~\ref{prop:confluence} \\
    {+common-refinement char. & consistent $\iff$ common-refinement condition & Thm.~\ref{thm:common-refinement} \\+}
    Functional CALM & consistent $\iff$ monotone & Thm.~\ref{thm:functional-calm} \\
    {+exposure boundary & common-refinement condition $\iff$ every reachable output exposable & Prop.~\ref{prop:functional-exposure-boundary} \\+}
    \bottomrule
  \end{tabular}
  \caption{Reference for Functional CALM: one transition system embeds the
@@ -238,9 +255,9 @@ A \emph{functional ordered specification} is a tuple
  \Spec=(I,\InputOrd,O,\OutputOrd,S),
\]
where $(I,\InputOrd)$ and $(O,\OutputOrd)$ are partially ordered input and
output types, and $S\subseteq I\times O$ is a typed relation [-that is total on-]
[-$I$ and satisfies the functional dependency from input to output:-]{+in which+} every
input appears in at least one [-row,-]{+row ($S$ is \emph{total} on $I$)+} and {+at most one+}
{+(the functional dependency):+}
\[
  (i,o)\in S\ \land\ (i,o')\in S
  \quad\Longrightarrow\quad o=o'.
@@ -248,13 +265,15 @@ appears in at least one row, and
\end{definition}

The unique output paired with $i$ induces the function
\[f:(I,\InputOrd)\to(O,\OutputOrd)\]
with $S=\{(i,f(i)):i\in I\}.$
We call
$\InputOrd$ the \emph{input-refinement order}: $i\InputOrd j$ means that $j$
contains at least the input information in $i$.  We call $\OutputOrd$ the
\emph{output-refinement order}: $o\OutputOrd u$ means that $u$ preserves every
externally visible claim in $o$ and may add more.  {+Section~\ref{sec:ambiguous-specifications}+}
{+drops the functional dependency; we say \emph{ordered specification} for+}
{+either kind.+}

The two orders are independent: the input order compares inputs; the output
order compares outputs.  Either may be the \emph{equality order}, under which an
@@ -275,7 +294,7 @@ To project onto a single column, we write $\mathrm{in}(R)$ and
$\mathrm{out}(R)$ for the sets of inputs and outputs that appear in $R$, and
$R(k)=\mathrm{out}(R[\mathrm{in}=k])$ for the \emph{fiber} of $R$ at $k$.

[-\begin{definition}[Monotonicity]-]{+\begin{definition}[Functional monotonicity]+}
\label{def:functional-monotonicity}
A functional ordered specification $\Spec$, with induced function $f$, is
\emph{monotone} if
@@ -288,7 +307,6 @@ A functional ordered specification $\Spec$, with induced function $f$, is
\end{definition}

Thus an output emitted from partial input remains valid as more input arrives.
[-For $i,k\in I$, write $i\prec_I k$ when $i\InputOrd k$ and $i\neq k$.-]

A specification describes every permitted input/output pair.  During execution,
input arrives and choices become binding, so only some of those pairs remain
@@ -323,9 +341,10 @@ separate part of the model, as follows.
A \emph{commitment} is a partial function on specification states that preserves
the current input and strictly reduces the remainder table: whenever
$c(i,R)=(i,R')$, we have $R'\subsetneq R$.  A \emph{commitment basis}
$\mathcal B$ is a set of commitments available to a system.  {+A commitment that+}
{+removes every row at a valid input \emph{seals} that input.+}  In a functional
[-specification, removing a row invalidates its input;-]{+specification every commitment seals the inputs whose rows it removes, and+} we
call [-such an action-]{+it+} a \emph{seal commitment}.
\end{definition}

Note that commitments are \emph{partial} functions:  a system may be designed to
@@ -336,7 +355,7 @@ only after some candidate has a majority.

A commitment basis therefore describes the authority of a particular system.
In our proofs, we also need a basis that supports every output permitted by
$S$, independent of the authority granted to any particular system.  To that end,
we derive a canonical basis from $S$.  For each permitted output, it
removes exactly the rows incompatible with that output's promise.

@@ -355,9 +374,8 @@ function
  \label{eq:canonical-seal-commitment}
\end{equation}
defined at every specification state $(i,R)$ where $(i,o)\in R$ and
$R[\mathrm{out}\succeq_O o]\neq R$.  [-At such a state, reaching $R[\mathrm{out}\succeq_O o]$ removes-]{+It seals exactly+} the [-sole row at one or-]
[-more-]{+valid+} inputs [-and therefore requires a seal commitment.-]{+whose+}
{+outputs do not refine $o$.+}  The \emph{canonical commitment basis} is exactly
\begin{equation}
  \mathcal B_S
    =\{s_o:o\in O,\ \operatorname{dom}(s_o)\neq\varnothing\}.
@@ -380,21 +398,18 @@ For a state $(i,R)$ and valid input $j$ with $i\InputOrd j$, the input event is
  \bigl(j,\ R[\mathrm{in}\succeq_I j]\bigr).
  \label{eq:input-event}
\end{equation}
It makes $j$ current and \emph{retires} every row whose input does not refine
[-$j$.-]{+$j$; we call this \emph{input retirement}.+}

An input event records a new cumulative input $j$, not how $j$ was
[-assembled.-]
[-The accumulation of inputs is handled outside the scope of our discussion.-]
[-Our-]{+assembled.\footnote{The+} framework does not require cumulative inputs to come
from a least common refinement or a lattice, only that they grow according to
$\InputOrd$.  For example, transaction schedules ordered by subsequence form a
partial order but[-need-] not[-form-] a [-lattice.  Two-]{+lattice: two+} independent events $a$ and $b$ have two
incomparable minimal common refinements, $ab$ and [-$ba$, rather than one-]
[-distinguished least common refinement.  This poses no difficulty in our-]
[-framework.-]{+$ba$.}+}  Because inputs are
cumulative, applying $\mathsf{input}(j)$ and then $\mathsf{input}(k)$ has the
same effect as applying $\mathsf{input}(k)$ directly; $\mathsf{input}(i)$ at
$(i,R)$ has no effect.

\paragraph{Output events.}
A system controls what it tells the outside world.  We study what it can safely
@@ -403,59 +418,109 @@ must therefore be preserved by later outputs according to $\OutputOrd$.

At state $(i,R)$, the current input has a unique row $(i,o)$, so $o$ is the only
output the system may emit.  Before doing so, it must invalidate every valid
future input whose output does not refine $o$.

[-The output event-]{+\begin{definition}[Output event]+}
{+\label{def:output-event}+}
{+Let $(i,R)$ be a state and $o\in R(i)$.  An \emph{output event}+}
$\mathsf{output}(o)$ {+under a basis $\mathcal B$+} applies a finite, possibly
empty sequence of[-seal-] commitments from [-the system's basis-]{+$\mathcal B$+} and then emits $o$, all
atomically.  If the commitments leave remainder table $R'$, {+the event is+}
{+\emph{valid} when+} every remaining row [-must preserve-]{+preserves+} $o$:
\begin{equation}
  (k,u)\in R' \Longrightarrow o\OutputOrd u,
  \quad\text{or equivalently}\quad R'\subseteq R[\mathrm{out}\succeq_O o].
  \label{eq:supported-output-action}
\end{equation}
[-The execution records which commitments the event applies.-]{+\end{definition}+}

{+Since commitments preserve the current input and yield states, $R'$ still+}
{+contains the current row $(i,o)$.+}  The [-canonical event-]{+\emph{canonical event}+} retains exactly
the compatible rows:
\begin{equation}
  (i,R)\xrightarrow{\mathsf{output}(o)}(i,R[\mathrm{out}\succeq_O o]).
  \label{eq:output-action}
\end{equation}
It applies $s_o$ when $R[\mathrm{out}\succeq_O o]\neq R$, and no commitment otherwise.

{+\begin{definition}[Exposable output]+}
{+\label{def:exposable}+}
{+An output $o\in R(i)$ is \emph{exposable} at $(i,R)$ when some valid output+}
{+event for $o$ applies no commitment.+}
{+\end{definition}+}

{+Systems differ in which commitments they hold, so one output can be emitted by+}
{+many different events.  To reason about all of them at once, we isolate what+}
{+they share.+}  No system-specific basis [-can do better: whatever another basis can emit,-]{+retains more rows than+} the canonical
[-event can emit too, while retaining at least-]{+event, and the results that follow depend on output events only through four+}
{+facts, which we collect+} as [-many rows.-]{+the \emph{event contract}.+}

[-\begin{proposition}[Canonical basis supports every output]-]{+\begin{proposition}[Event contract]+}
\label{prop:canonical-output-preservation}
[-Suppose an-]{+Let $(i,R)$ be a state and $o\in R(i)$.+}
{+\begin{enumerate}+}
{+  \item \emph{Containment.}  Under any commitment basis, a valid+} output event
        for $o$[-under any commitment basis-] takes $(i,R)$ to [-$(i,R')$.-]{+some $(i,R')$ with+}
{+        $R'\subseteq R[\mathrm{out}\succeq_O o]$.+}
{+  \item \emph{Canonical support.}+}  The canonical[-basis supports an output-] event for[-the same-] $o$ [-from-]
[-$(i,R)$, taking-]{+is valid at+}
{+        $(i,R)$ and takes+} it to $(i,R[\mathrm{out}\succeq_O [-o])$, with $R'\subseteq R[\mathrm{out}\succeq_O o]$.  Thus the canonical-]
[-event-]{+o])$.  It therefore+}
        retains every row [-retained by the original event,-]{+that any valid event for $o$ retains.+}
{+  \item \emph{Commitment-free events are canonical.}  A valid output event for+}
{+        $o$ that applies no commitment takes $(i,R)$ to+}
{+        $(i,R[\mathrm{out}\succeq_O o])$.+}
{+  \item \emph{Exposure test.}  The output $o$ is exposable at $(i,R)$ if and+}
{+        only if, for every valid $j\succeq_I i$ and every $x\in R(j)$, some+}
{+        $u\in R(j)$ refines both $o$+} and [-possibly more.-]{+$x$.+}
{+\end{enumerate}+}
\end{proposition}

\begin{proof}
[-The canonical transition-]{+Containment+} is [-defined above,-]{+Equation~\ref{eq:supported-output-action},+} and [-$R'\subseteq R[\mathrm{out}\succeq_O o]$-]{+canonical+}
{+support is Equation~\ref{eq:output-action}.  An output event that applies no+}
{+commitment leaves $R$ unchanged, so it+} is [-required by-]
[-Equation~\ref{eq:supported-output-action} for-]{+valid exactly when+}
{+$R\subseteq R[\mathrm{out}\succeq_O o]$, in which case+}
{+$R=R[\mathrm{out}\succeq_O o]$; this gives clause~3.  That condition says+}
{+$o\OutputOrd f(j)$ at+} every valid [-output event.-]{+$j\succeq_I i$; since $R(j)=\{f(j)\}$, taking+}
{+$u=x=f(j)$ shows that it is the condition of clause~4.+}
\end{proof}

In [-the best case, the canonical event needs no commitment at all:-]

[-\begin{definition}[Exposable output,-]{+a+} functional [-case]-]
[-\label{def:exposable}-]
[-The current output-]{+specification, then,+} $o$ is [-\emph{exposable} at $(i,R)$-]{+exposable exactly+} when
$R[\mathrm{out}\succeq_O [-o]=R$.-]
[-Equivalently, its output event needs no commitment,-]{+o]=R$,+} or {+equivalently+} $o\OutputOrd f(j)$ at every
valid $j\succeq_I i$.

[-\end{definition}-]

[-Section~\ref{sec:safe-exposure} extends this account with output retirement when-]{+\paragraph{Determination.}+}
{+Both kinds of event can narrow what remains possible.  For a state $(i,R)$, the+}
{+\emph{upper fiber} $\mathrm{out}(R[\mathrm{in}\succeq_I i])$ collects+} the
{+outputs at $i$ and its still-valid refinements.  The state is+}
{+\emph{determined} when its upper fiber has one element, regardless of how it+}
{+was reached, and \emph{sealed} when every strict refinement of $i$ has been+}
{+sealed, so that none remains valid.  A sealed+} functional [-dependency-]{+state is determined.+}
{+\emph{Determination}+} is [-removed.-]{+movement toward or arrival at a determined state.  An+}
{+input event may resolve ambiguity by retiring rows that no longer extend the+}
{+input received; a commitment may instead exclude an alternative that otherwise+}
{+remains possible.  We call the resulting outcomes \emph{input-resolved} and+}
{+\emph{commitment-resolved}, respectively, as in panels (c) and (d) of+}
{+Figure~\ref{fig:election-frames}.+}

\subsection{Executions and consistency}
\label{sec:determination}

[-Individual events describe one state change at a time.-]We now assemble [-them-]{+events+} into runs and ask the central consistency question:
when different runs follow different paths through the specification, can
their resulting states still be reconciled?  {+Consistency quantifies over all+}
{+runs of all systems.  We reduce it to a check+}
{+on the specification table in three steps.  First, any system's run can be+}
{+replaced by a canonical run that keeps at least as many rows+}
{+(Lemma~\ref{lem:canonical-equivalent}).  Second, a canonical run's remaining+}
{+rows depend only on its current input and the outputs it has emitted+}
{+(Lemma~\ref{lem:run-residual}).  Third, runs are therefore confluent exactly+}
{+when one row at their common input survives in all of them+}
{+(Proposition~\ref{prop:confluence}), which yields a condition on the table+}
{+alone (Theorem~\ref{thm:common-refinement}, Section~\ref{sec:functional-calm-theorem}).+}
{+None of these steps uses the functional dependency; they use output events only+}
{+through the event contract of Section~\ref{sec:functional-events}.+}
{+Section~\ref{sec:ambiguous-specifications} re-verifies that contract for+}
{+several outputs per input, and every step then carries over.+}

\begin{definition}[Transition system, run, canonical run]
\label{def:io-transition-system}
@@ -466,11 +531,15 @@ $\mathcal B$} is any finite transition sequence from the canonical state
$\sigma_S(i)$ at some input $i$; its output events may use only commitments
from $\mathcal B$.  We say simply \emph{run} when the basis is clear.  A
\emph{canonical run} is a run under $\mathcal B_S$ in which every output event
takes the canonical transition of [-Equation~\ref{eq:output-action} and hence-]
[-reaches $R[\mathrm{out}\succeq_O o]$.-]{+Equation~\ref{eq:output-action}.+}
\label{def:run}
\end{definition}

{+A run is \emph{commitment-free} when none of its output events applies a+}
{+commitment.  By clause~3 of the event contract, a commitment-free run under any+}
{+basis is a canonical run.  A state is \emph{reachable without commitment} when+}
{+some commitment-free run reaches it.+}

Our results quantify over canonical runs rather than over the runs of any
particular system.  To see that this excludes no system's behavior, call two
runs \emph{equivalent} when they start at the same canonical state and have the
@@ -490,16 +559,18 @@ each event, the canonical run's remainder table contains the original run's.
By induction on the events.  Both runs start at the same canonical state, so
their remainder tables are initially equal.  Suppose that before some event the
original run's table $R$ and the canonical run's table $\widehat R$ satisfy
$R\subseteq\widehat R$; we show that the inclusion holds afterward.  An input
event $\mathsf{input}(j)$ that is valid at $R$ is also valid at $\widehat R$.
It retires every row whose input does not refine $j$, keeping
$R[\mathrm{in}\succeq_I j]$ in the original run and
$\widehat R[\mathrm{in}\succeq_I j]$ in the canonical run.  Since
$R\subseteq\widehat R$, the first remains contained in the second.  For an
output event {+for $o\in R(i)$+} taking $R$ to $R'$, [-the original run keeps only rows whose outputs-]
[-refine $o$, so-]{+containment+}
{+(Proposition~\ref{prop:canonical-output-preservation}) gives+}
$R'\subseteq R[\mathrm{out}\succeq_O [-o]$-]
[-(Equation~\ref{eq:supported-output-action}).  The-]{+o]$.  Since $o\in R(i)\subseteq\widehat R(i)$,+}
{+canonical support applies at $\widehat R$: the+} canonical event takes
$\widehat R$ to $\widehat R[\mathrm{out}\succeq_O o]$, which contains
$R[\mathrm{out}\succeq_O [-o]$ because $R\subseteq\widehat R$.-]{+o]$.+}
\end{proof}

The converse does not hold: a canonical run need not be equivalent to any run
@@ -528,32 +599,40 @@ the rows at or above $i$ whose outputs refine every emitted output.

\begin{proof}
The run starts at a canonical state $\sigma_S(i_0)$, whose remainder table is
$S[\mathrm{in}\succeq_I i_0]$.  Each input event adds a conjunct
$\mathrm{in}\succeq_I j$ [-and-]{+and, by canonical support+}
{+(Proposition~\ref{prop:canonical-output-preservation}),+} each canonical output
event a conjunct $\mathrm{out}\succeq_O o$; since inputs only grow, the input
conjuncts reduce to the last one: $\mathrm{in}\succeq_I i$.
\end{proof}

{+For example, in Figure~\ref{fig:nonmonotone-frame}'s equality-order variant, a+}
{+canonical run that emits $\bot$ at $x\cdot\cdot$ keeps+}
{+$S[\mathrm{in}\succeq_I x\cdot\cdot,\ \mathrm{out}\succeq_O\bot]$: the rows+}
{+$(x\cdot\cdot,\bot)$ and $(xy\cdot,\bot)$.  The registrar in the figure also+}
{+removes $(xy\cdot,\bot)$, a stronger commitment than the specification+}
{+requires.+}

To compare runs that end at different inputs, we extend those inputs to a
common refinement.  A \emph{common refinement} of inputs $i_1,\ldots,i_k$ is
an input $j$ with $i_r\InputOrd j$ for every $r$.

\begin{definition}[Consistency]
\label{def:consistency}
[-A functional-]{+An+} ordered specification is \emph{consistent} when every finite family of
canonical runs is confluent: if the runs end at states
$(i_1,R_1),\ldots,(i_k,R_k)$ and $j$ is a common refinement of their current
inputs, each run can be extended by further canonical events to one common
state with current input $j$.  The runs are then \emph{confluent at} $j$.
\end{definition}

Confluence has a simple test: [-the runs must share a surviving-]{+some+} row at the common [-refinement.-]{+refinement must survive+}
{+in every run.+}

[-\begin{proposition}[Confluence at a common refinement]-]{+\begin{proposition}[Survivor test]+}
\label{prop:confluence}
Canonical runs ending at states $(i_1,R_1),\ldots,(i_k,R_k)$ are confluent
at $j$ if and only if some row at $j$ survives in every final [-state,-]{+state:+}
\begin{equation}
  (j,u)\in R_r\quad\text{for every }r,\ \text{for some }u\in O.
  \label{eq:reconciliation}
@@ -564,25 +643,28 @@ $\bigl(j,\ S[\mathrm{in}\succeq_I j,\ \mathrm{out}\succeq_O u]\bigr)$.
\end{proposition}

\begin{proof}
A common state with current input $j$ has a row at $j$, and {+since rows are+}
{+never added,+} that row belongs to every $R_r$.  Conversely, let $(j,u)$ belong
to every $R_r$.  Then $\mathsf{input}(j)$ is defined at every $(i_r,R_r)$.  By
Lemma~\ref{lem:run-residual}, $(j,u)\in R_r$ says that $u$ refines every output
emitted on run $r$.  After $\mathsf{input}(j)$ and $\mathsf{output}(u)$, the
same lemma leaves exactly
$S[\mathrm{in}\succeq_I j,\ \mathrm{out}\succeq_O u]$, independent of the
starting run.
\end{proof}

[-Inconsistency does not require concurrency.  Consider two runs from the same-]
[-canonical state $\sigma_S(i)$, which might be two replicas or two replays of one-]
[-system.  The first emits $f(i)$ at once; the second first accepts-]{+In+} a [-refinement-]
[-$k$ of $i$ with $f(i)\not\OutputOrd f(k)$.  To honor its promise, the first-]
[-run's canonical output event seals $k$, as the registrar does by closing-]{+functional specification+} the [-polls in Figure~\ref{fig:nonmonotone-frame}.  The seal-]{+only row at $j$+} is [-a commitment;-]{+$(j,f(j))$, so+} the [-inconsistency is what follows from it.  The two runs now disagree about-]{+test+}
{+asks+} whether [-$k$ is valid,-]{+that row survives in every run,+} and [-no extension reconciles them at $k$.  They differ only-]{+$u=f(j)$;+} in[-whether-] the
[-output came before-]{+equality-order election of Section~\ref{sec:election-story},+} the [-input, and-]{+row+}
{+$(xxx,x)$ does not survive the run that emits $\bot$ at $x\cdot\cdot$.+}

Consistency [-requires-]{+guarantees+} that [-such-]
[-timing not matter.  The proof-]{+runs never diverge irreparably.  Whatever input+}
{+and output events a finite collection+} of [-Functional CALM uses exactly this pair.-]{+runs has taken, any input refining all+}
{+of theirs leaves a single state that every run can reach: one that keeps every+}
{+promise any of them has made and accepts all of that input.+}
{+Proposition~\ref{prop:confluence} identifies that state, and+}
{+Section~\ref{sec:functional-calm-theorem} shows that for a consistent+}
{+functional specification it depends only on the input.+}

Consistency is a property of the specification.  It describes no protocol and
promises no delivery or termination; Section~\ref{sec:discussion} returns to
@@ -592,8 +674,48 @@ this.
\label{sec:functional-calm-theorem}

Consistency is a property of families of canonical runs, while monotonicity
is a local condition on pairs of inputs.  [-Functional CALM shows-]{+We first characterize Consistency by+}
{+a condition on the specification table alone, then specialize it to+}
{+functional specifications.+}

{+\begin{definition}[Common-refinement condition]+}
{+\label{def:common-refinement-condition}+}
{+An ordered specification satisfies the \emph{common-refinement condition} when,+}
{+for every finite set of rows $(i_1,o_1),\ldots,(i_k,o_k)$ of $S$ and every+}
{+common refinement $j$ of $i_1,\ldots,i_k$, some $u\in S(j)$ refines every+}
{+$o_r$.+}
{+\end{definition}+}

{+The inputs $i_r$ need not be comparable, because different runs meet only at a+}
{+common refinement.  For the empty set of rows the condition asks only+} that
{+$S(j)$ be nonempty, which totality guarantees.+}

{+\begin{theorem}[Common-refinement characterization]+}
{+\label{thm:common-refinement}+}
{+An ordered specification is consistent if and only if it satisfies the+}
{+common-refinement condition.+}
{+\end{theorem}+}

{+\begin{proof}+}
{+Suppose the condition holds, and let canonical runs end at $(i_r,R_r)$ with+}
{+common refinement $j$.  Each output $o$ emitted on a run was emitted at some+}
{+input $i_o\InputOrd j$, and since $o\in R(i_o)\subseteq S(i_o)$, it forms a row+}
{+$(i_o,o)$ of $S$.  The condition supplies $u\in S(j)$ refining all of these+}
{+outputs.  Since $j$ refines every current input $i_r$,+}
{+Lemma~\ref{lem:run-residual} puts $(j,u)$ in every $R_r$, and+}
{+Proposition~\ref{prop:confluence} gives confluence at $j$.  Conversely, let+}
{+rows $(i_r,o_r)$ have common refinement $j$.  For each $r$, the canonical run+}
{+that starts at $\sigma_S(i_r)$ and emits $o_r$ ends with remainder table+}
{+$S[\mathrm{in}\succeq_I i_r,\ \mathrm{out}\succeq_O o_r]$+}
{+(Lemma~\ref{lem:run-residual}).  Consistency and+}
{+Proposition~\ref{prop:confluence} supply a row $(j,u)$ surviving in every one+}
{+of these runs, so $u\in S(j)$ refines every $o_r$.+}
{+\end{proof}+}

{+In the equality-order election, the rows $(x\cdot\cdot,\bot)$ and $(xx\cdot,x)$+}
{+have common refinement $xxx$, but $S(xxx)=\{x\}$ and $x$ does not refine+}
{+$\bot$.  The condition fails, and so does Consistency:+} these {+are the+} two [-views coincide.-]{+runs of+}
{+Section~\ref{sec:election-story} that can never meet.+}

\begin{theorem}[Functional CALM]
\label{thm:functional-calm}
@@ -602,23 +724,74 @@ monotone.
\end{theorem}

\begin{proof}
[-Every input has one row, so if a canonical run emits $o_\ell$ at current input-]
[-$i_\ell$, then $o_\ell=f(i_\ell)$.-]By [-Lemma~\ref{lem:run-residual},-]{+Theorem~\ref{thm:common-refinement}, it suffices to show that, for+} a
[-canonical run-]
[-ending at input $i$ retains $(k,f(k))$ at $k\succeq_I i$ exactly when every output-]
[-$f(i_\ell)$ emitted on-]{+functional specification,+} the [-run satisfies $f(i_\ell)\OutputOrd f(k)$.  By-]
[-Proposition~\ref{prop:confluence}, a finite family of canonical runs is-]
[-confluent at a common refinement $k$ exactly when every output emitted on any-]
[-run lies below $f(k)$.  If $f$ is monotone this holds because each emitted $f(i_\ell)$ has-]
[-$i_\ell\InputOrd k$.  If $f$-]{+common-refinement condition+} is [-not monotone, some $i\prec_I k$ has-]
[-$f(i)\not\OutputOrd f(k)$.  Of two canonical runs from $\sigma_S(i)$, one-]{+equivalent to+}
{+monotonicity.  The rows of $S$ are $(i_r,f(i_r))$ and $S(j)=\{f(j)\}$, so the+}
{+condition says+} that [-emits $f(i)$ has no row at $k$, while-]{+$f(i_r)\OutputOrd f(j)$ whenever $i_r\InputOrd j$.  With+}
one[-that accepts $k$ retains $(k,f(k))$;-]
[-no-] row [-at $k$ survives in both, so they are not confluent at $k$.-]{+this is monotonicity, and monotonicity gives it for every row.+}
\end{proof}

{+In the functional case, Consistency has a strong consequence: outputs leave no+}
{+trace on the state.+}

{+\begin{corollary}[State is determined by input]+}
{+\label{cor:state-by-input}+}
{+In a consistent functional specification, every canonical run ending at current+}
{+input $i$ is in the canonical state $\sigma_S(i)$, whatever outputs it emitted+}
{+along the way.+}
{+\end{corollary}+}

{+\begin{proof}+}
{+By Functional CALM (Theorem~\ref{thm:functional-calm}), the specification is+}
{+monotone.  By Lemma~\ref{lem:run-residual}, the run's remainder table is+}
{+$S[\mathrm{in}\succeq_I i,\ \mathrm{out}\succeq_O o_1,\ \ldots,\+}
{+\mathrm{out}\succeq_O o_m]$, where each $o_\ell=f(i_\ell)$ for some+}
{+$i_\ell\InputOrd i$.  Every row at or above $i$ has the form $(k,f(k))$ with+}
{+$i_\ell\InputOrd k$, so monotonicity gives $o_\ell\OutputOrd f(k)$, and the+}
{+output conditions remove nothing.+}
{+\end{proof}+}

{+Confluence at a common refinement $j$ therefore needs only $\mathsf{input}(j)$:+}
{+every run reaches $\sigma_S(j)$, the state of a run that starts with all of the+}
{+input.  Knowing the input is enough to know the state, and with it the one+}
{+output $f(j)$.+}

{+Exposability, too, is governed by the common-refinement condition:+}

{+\begin{proposition}[Exposure boundary]+}
{+\label{prop:functional-exposure-boundary}+}
{+An ordered specification satisfies the common-refinement condition if and only+}
{+if every output at every state reachable without commitment is exposable.+}
{+\end{proposition}+}

{+\begin{proof}+}
{+Suppose the condition holds; by Theorem~\ref{thm:common-refinement}, the+}
{+specification is consistent.  Let $(i,R)$ be reached by a commitment-free run,+}
{+which is canonical, and let $o\in R(i)$, $j\succeq_I i$ valid, and+}
{+$x\in R(j)$.  Extend the run in two ways: by $\mathsf{output}(o)$, and by+}
{+$\mathsf{input}(j)$ followed by $\mathsf{output}(x)$.+}
{+Proposition~\ref{prop:confluence} supplies a row $(j,u)$ surviving in both, so+}
{+$u\in R(j)$ refines $o$ and $x$, and the exposure test+}
{+(Proposition~\ref{prop:canonical-output-preservation}) makes $o$ exposable.+}
{+Conversely, suppose every such output is exposable, and let rows+}
{+$(i_1,o_1),\ldots,(i_k,o_k)$ have common refinement $j$.  By totality pick+}
{+$u_0\in S(j)$.  For $r=1,\ldots,k$ in turn, the exposure test for $o_r$ at+}
{+$\sigma_S(i_r)$, applied with $x=u_{r-1}$, gives $u_r\in S(j)$ refining both+}
{+$o_r$ and $u_{r-1}$.  Then $u_k$ refines every $o_r$.+}
{+\end{proof}+}

{+For a functional specification, Functional CALM turns the condition into+}
{+monotonicity.  A monotone functional specification can emit every current+}
{+output without a commitment; if monotonicity fails at $i\InputOrd k$ with+}
{+$f(i)\not\OutputOrd f(k)$, the canonical output event for $f(i)$ seals $k$.+}

This is the familiar CALM dichotomy stated at the specification interface
rather than inside a particular programming language.  {+Historically, CALM+}
{+stands for \emph{Consistency As Logical Monotonicity}, and its C has been read+}
{+both as consistency and as confluence; Definition~\ref{def:consistency} is+}
{+both.+}  Classical CALM fits the pattern with inputs $J$ ordered by fact
inclusion and outputs $Q(J)$ ordered by answer inclusion.  Functional
monotonicity becomes
        \begin{equation}
  J\subseteq J'
  \quad\Longrightarrow\quad
@@ -628,73 +801,13 @@ answer inclusion.  Functional monotonicity becomes
the standard definition of a monotone query~\cite{abiteboul1995foundations},
which positive Datalog satisfies and negation may not.  Functional CALM
extends the statement from fact sets under inclusion to arbitrary input and
output refinement [-orders.-]{+orders, regardless of the formalism used to express the+}
{+specification.+}  The usual CRDT state interface has the same functional shape,
with received payloads ordered by inclusion and states by the semilattice
order~\cite{shapiro2011crdt}; Sections~\ref{sec:query-instance}
and~\ref{sec:crdt-instance} take up both instances.[-\subsection{Output events and exposability}-]
[-\label{sec:canonical-transition-system}-]

[-Having defined exposability for output events, we now relate it to-]
[-determination and monotonicity, while separating the specification-level-]
[-boundary from the strategy of a particular system.  The canonical basis-]
[-exercises every output the specification permits; an implementation supplies-]
[-its own basis and may support fewer output events.-]

[-For $R\subseteq S$, the \emph{upper fiber} at $i$,-]
[-$\mathrm{out}(R[\mathrm{in}\succeq_I i])$, collects the outputs at $i$ and its-]
[-still-valid refinements.  A state $(i,R)$ is \emph{determined} when-]
[-$|\mathrm{out}(R[\mathrm{in}\succeq_I i])|=1$, regardless of how it was-]
[-reached.  \emph{Determination} is movement toward or arrival at that condition.-]
[-A commitment may advance determination by excluding an alternative that-]
[-otherwise remains possible; an input event may instead resolve ambiguity by-]
[-retiring histories that no longer extend the input received.  We call the-]
[-resulting outcomes \emph{commitment-resolved} and \emph{input-resolved},-]
[-respectively.-]

[-As defined in Section~\ref{sec:functional-events}, the current output is-]
[-exposable exactly when its output event requires no commitment.-]

[-A state is \emph{sealed} when no strict refinement of its current input remains-]
[-valid.  A sealed functional state is determined.  Commitments that produce such-]
[-a state make it commitment-resolved, although determination need not seal every-]
[-strict refinement at once.-]

[-A system's \emph{strategy} chooses input and output events, including which-]
[-commitments from its basis an output event applies, using the specification-]
[-and any additional strategy state.  Strategy state is not part of the-]
[-specification state and affects the remainder table only through the selected-]
[-transitions.-]

[-\begin{proposition}[Functional exposure boundary]-]
[-\label{prop:functional-exposure-boundary}-]
[-A functional ordered specification is monotone if and only if every output at-]
[-every state reachable without commitment is exposable.-]
[-\end{proposition}-]

[-\begin{proof}-]
[-If $f$ is monotone, a commitment-free state has lost rows only to input events,-]
[-since its output events use no commitments and retire no rows.  If-]
[-its current input is $i$, then the only output paired with $i$ is $f(i)$, and-]
[-every valid $j\succeq_I i$ has $f(i)\OutputOrd f(j)$, so $f(i)$ is exposable.-]
[-Conversely, suppose every output at every commitment-free reachable state is-]
[-exposable.  At $\sigma_S(i)$, exposability of $f(i)$ preserves the row-]
[-$(j,f(j))$ for each $j\succeq_I i$, so $f(i)\OutputOrd f(j)$ and $f$ is-]
[-monotone.-]
[-\end{proof}-]

[-Functional CALM and this proposition give the operational boundary.  A-]
[-monotone functional specification can emit every current output without a-]
[-commitment.  If monotonicity fails at $i\prec_I k$, the canonical output event-]
[-for $f(i)$ includes a commitment that removes the conflicting row at $k$.-]

[-Historically, CALM stands for \emph{Consistency As Logical Monotonicity}, and-]
[-its C has been read both as consistency and as confluence;-]
[-Definition~\ref{def:consistency} is both.  Functional CALM states the result-]
[-for any functional specification, regardless of the formalism used to express-]
[-it.-]

Before dropping the functional dependency, we give this consistency condition
a distributed interpretation.  Section~\ref{sec:distributed-execution}
realizes runs as participant runs; the construction will apply unchanged when
Section~\ref{sec:ambiguous-specifications} introduces output choice.
diff --git a/sections/introduction.tex b/sections/introduction.tex
index f1e5187..36d8f1b 100644
--- a/sections/introduction.tex
+++ b/sections/introduction.tex
@@ -38,7 +38,7 @@ We develop a unified coordination criterion that spans this space,
including the translation questions above
(\S\ref{sec:cap-corollary}, \S\ref{sec:instances}).  We begin with a minimalist
specification model: a two-column relational table pairing input values with the
corresponding outputs that [-are within spec.-]{+it permits.+}  The model is purely declarative: it
describes what can be observed about a system, without reference to any
imperative procedure.  The input domain $(I,\InputOrd)$ includes a partial order
describing how input grows; the output domain $(O,\OutputOrd)$ has its own
@@ -55,7 +55,7 @@ a common state.  This unifies classical definitions of consistency: a specificat
table captures the space of acceptable outcomes, while confluence asks whether
those requirements are maintained across concurrent executions.

We [-begin by focusing-]{+first focus+} on specification tables with a functional dependency from
input to output (\S\ref{sec:functional-specifications}). These \emph{functional
ordered specifications} capture arbitrary functions
\(f:(I,\InputOrd)\to(O,\OutputOrd)\). Although each input has one output, a system
@@ -69,33 +69,46 @@ Our first result is \emph{Functional CALM}
functions and partial orders, proving that Consistency is equivalent to
monotonicity.  When monotonicity fails, emitting some output requires
irrevocably restricting subsequent results to those that preserve it.  We call
this restriction a \emph{commitment}.  [-Functional CALM characterizes exactly-]
[-when execution ambiguity-]{+Conversely, a monotone specification+} can
[-be handled consistently-]{+emit every output it permits+} without [-commitment.-]{+one.+}
This captures relational query languages and the usual CRDT state interface.

We then give Consistency a distributed interpretation without changing the
specification model (\S\ref{sec:distributed-execution}). We place one local
execution at each participant in a [-Lamport-]{+distributed+} history, then project away delivery
and strategy details that do not change specification state.
\emph{Distributed Consistency} asks whether the resulting participant states can
still be brought to the same state. We prove that a specification has
Distributed Consistency if and only if it is consistent in the sense above.
{+For a consistent functional specification, state is then determined by input+}
{+alone, so participants with the same input agree regardless of delivery order+}
{+or emitted outputs: the convergence that strong eventual consistency asks of+}
{+replicated state, derived from the specification rather than from a merge+}
{+operator.+}

The functional specifications above cannot capture settings like leader election
or transaction ordering, where many outputs are [-within spec-]{+permitted+} for a given input. In the
absence of a functional dependency determining the output for each input, a second source of
ambiguity arises: \emph{semantic ambiguity}. We call the resolution of either
[-type of-]
[-ambiguity \emph{determination}; it is complete when only one output remains-]
[-possible. Determination may occur through input, which-]{+kind \emph{determination}: input+} may make alternatives unreachable, or [-through commitments, which-]{+a+}
{+commitment may+} exclude [-alternatives that would-]
[-otherwise remain possible.-]{+them.+} To model semantic ambiguity, we must move beyond standard
monotonicity of functions. For the case of general relations we define an extension called
\emph{Lifted Monotonicity}, which asks whether outputs from different executions can remain
consistent with one another as input grows. Complete CALM proves that
Consistency, Lifted Monotonicity, and Distributed Consistency are equivalent
(\S\ref{sec:complete-calm-theorem}).  [-The participants' commitments must rule-]
[-out-]{+Both CALM theorems characterize+} the same
{+condition on the specification table: whenever permitted rows have inputs with+}
{+a common refinement $j$, some output permitted at $j$ refines all of their+}
{+outputs.  For one output per input this is ordinary monotonicity; for many, it+}
{+is Lifted Monotonicity.+}

{+Output choice has two further consequences.  When participants could make+}
conflicting [-alternatives.  Coordination-]{+commitments, their output events cannot both complete in a+}
{+confluent execution; a system that requires Consistency must therefore+}
{+mutually exclude them, and coordination+} mechanisms [-operationalize-]
[-this requirement.-]{+provide that exclusion.+}
{+Confluence is a safety guarantee: a reconciling state+}
{+always exists.  With output choice, reaching it is a matter of strategy, and+}
{+deterministic reconciliation is one strategy that terminates.+}

Classical CALM tells us when coordination is unnecessary, but not whether a
chosen use of coordination is sufficient.  Complete CALM can answer the second
@@ -108,11 +121,19 @@ commitments.  We call this analysis \emph{Proper Coordination} and formalize it
in Appendix~\ref{app:composition}.

Complete CALM also yields a Complete CAP Theorem
(\S\ref{sec:cap-corollary}).  [-For-]{+Brewer conjectured that a partitioned system+}
{+cannot be both consistent and available; Gilbert and Lynch proved this for one+}
{+guarantee, the linearizable register.  Complete CAP makes the conjecture+}
{+precise for+} any consistency guarantee expressed as a specification, [-monotonicity-]{+and in both+}
{+directions: it+} identifies which [-side of-]{+guarantees face+} the [-CAP boundary it-]
[-occupies.-]{+tradeoff and which escape+}
{+it.+}
A[-monotone-] specification {+satisfying Lifted Monotonicity+} can keep its [-full-]{+whole+} interface
available and confluent during a partition; [-a non-monotone one-]{+any other+} cannot.  [-Classical-]
[-linearizability-]{+A weaker,+}
{+response form asks only that every operation be answered, where the interface+}
{+declares which outputs count as answers, and characterizes exactly when that is+}
{+possible (Appendix~\ref{app:cap-response}).  The Gilbert--Lynch theorem+} is[-one instance on-] the
[-negative side.-]{+special case in which one replica's only permitted answer is invalidated by+}
{+input it cannot see.+}

This paper makes six contributions:
\begin{enumerate}
@@ -122,14 +143,17 @@ This paper makes six contributions:
  \item \emph{Consistency as confluence.} One definition applies to general
        consistency models and application-specific requirements.
        This run-level property is shown to be equivalent to Distributed
        Consistency over [-Lamport-]{+distributed+} histories.
  \item \emph{Functional CALM.} For arbitrary functions between ordered
        domains, Consistency---and hence Distributed Consistency---is equivalent
        to monotonicity.
  \item \emph{Complete CALM and CAP.} With multiple outputs per input,
        Consistency---and hence Distributed Consistency---is equivalent to
        Lifted [-Monotonicity.-]{+Monotonicity, the same common-refinement condition that+}
{+          underlies Functional CALM.+}  Complete CAP gives the corresponding
          [-availability-]{+partition+} boundary [-under partition.-]{+in two forms, for the whole interface and for+}
{+          answering every operation; the Gilbert--Lynch theorem is recovered as+}
{+          a special case.+}
  \item \emph{Composition and Proper Coordination.} Specifications compose by
        equijoin.  Committing a shared log order can make a non-monotone
        log/store composition consistent without further store commitments
@@ -139,14 +163,19 @@ This paper makes six contributions:
        (Appendix~\ref{sec:frontiers}).
\end{enumerate}

Section~\ref{sec:functional-calm} introduces the framework on an election and
[-develops-]{+proves a chain of results, ending in the common-refinement characterization of+}
{+Consistency, that depend on output events only through a small event contract;+}
Functional [-CALM.-]{+CALM then follows in a few lines.+}
Section~\ref{sec:distributed-execution} gives Consistency its distributed
reading.  Section~\ref{sec:ambiguous-specifications} [-extends the framework-]{+lifts output events+} to
[-ambiguous specifications,-]{+output choice+} and [-Section~\ref{sec:complete-calm}-]
[-combines-]{+verifies+} the [-two extensions in-]{+same contract, so Section~\ref{sec:complete-calm}+}
{+assembles+} Complete CALM and Complete [-CAP.-]{+CAP from the same parts.+}
Section~\ref{sec:instances} applies the results to familiar systems, and
Section~\ref{sec:discussion} draws out the design lessons and scope limits.
Appendix~\ref{app:composition} proves the composition and Proper Coordination
results, {+Appendix~\ref{app:cap-response} develops the response form of+}
{+Complete CAP and recovers Gilbert--Lynch,+} Appendix~\ref{sec:frontiers} derives
maximal coordination-free
interfaces, and Appendix~\ref{app:additional-applications} gives further
classical applications.
```
