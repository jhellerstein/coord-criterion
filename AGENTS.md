# Working on this repository

(Keep this file identical in content to `.kiro/steering/paper-and-lean.md`.)

## Paper and Lean must stay in sync

The Lean formalization in `lean/` checks every result and proved claim of the
paper.  `lean/CoordCriterion/Paper/*.lean` mirrors the paper section by
section: each LaTeX label is a declaration `CC.Paper.«label»` whose docstring
quotes the paper.

After any change to `sections/*.tex` or `appendices/*.tex`:

1. If a definition, statement, or proved claim changed, update the Lean so it
   still proves the current statement (library under `lean/CoordCriterion/`,
   entry in `Paper/`).  If the new claim is false or unproved, say so before
   committing the paper change.
2. If only wording changed, update the quoted text in the matching `Paper/`
   docstring.
3. If a label was added, removed, renamed, or moved between sections, move or
   rename the `Paper/` entry to match.
4. Rebuild and check, from `lean/`:
   `lake build`, `lake env lean scripts/CheckAxioms.lean`,
   `python3 scripts/gen_index.py`, `lake env lean scripts/CheckReadme.lean`.
5. Commit the `.tex` and `lean/` changes together, except during a revision
   round (below).

During a revision round, when the author is iterating on prose, `.tex`
changes may be committed and pushed alone after a paper build.  Tag each such
commit message `[lean-sync pending]`.  When the section settles, do one Lean
pass covering every tagged commit since the last sync (steps 1–4), and commit
it with a message that names the commits it syncs.  A text change that alters
a definition, statement, or proved claim must still be flagged to the author
when it is made, since the Lean may not prove it yet.

Prose-only claims (no Lean) are listed in `lean/README.md`; keep that list
current.

## Building

* Paper: `~/.local/bin/tectonic main.tex`; check the log for undefined or
  multiply defined references.
* Lean: `export ELAN_HOME=$HOME/.cache/elan PATH=$HOME/.cache/elan/bin:$PATH`,
  then `lake build` in `lean/` (Lean 4 core only, no Mathlib).

## Editing conventions

* Plainspoken CIDR tone; surgical edits; define before use; no oversell; avoid
  "promise" except colloquially in §2.
* Vocabulary macros: `\inrel` (expands), `\outrel` (refines), "fiber at k",
  "row at k"; named sets `\Sealed_o`, `\Retired_o`, `\Rejected_o`.
* Do not edit the abstract or introduction without discussing it first.
* Appendices are for theoreticians: definition, statement, proof.
* Work on `main`; stage specific files; pull before editing; push after.
* Never touch untracked files (uploaded PDFs, `.infinity/`).

## Voice

The author's voice (see his papers in `jmhpapers/`, untracked): medium
declaratives broken by short sentences that land a point; intuition before
formalism ("Intuitively, … Formally, …"), then an example ("Consider …");
concrete systems artifacts; coined names that are explained; owned, calibrated
hedges; plain signposting ("Recall that", "Note that", "First, … Second, …").

Avoid:

* Imperative "do X, and Y" constructions ("Compose them…, and…", "Write X
  down, and…", "Model X as Y", "Partition a database…").  Use "Consider…",
  "We model…", "Given…".  Standard proof imperatives ("Let", "Fix") are fine.
* Results or sections as agents ("the results ask one question"); abstract
  nouns as subjects ("This characterization yields…").
* Vague "boundary", "object", "machinery", "notion"; generic openers ("central
  goal", "core structures"); intensifiers ("crucially", "key insight").
* Semicolon chains of three or more clauses; stacked appositives and
  parentheticals; runs of "not X but Y"; slogan-like paragraph closers;
  restating what was just said; "In other words" (use "Said differently",
  "Simply put").
* Cute flourishes ("someone is watching"), "Simple as it is" (prefer "Despite
  its simplicity"), "the designer" for a hypothetical ("a designer").
* Conclusions that only recap; the author writes the research agenda.
