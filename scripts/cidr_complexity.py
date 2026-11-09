#!/usr/bin/env python3
"""Generate cidr-complexity.tex: cidr.tex marked up for rewriting work.

Each prose paragraph of cidr.tex (a blank-line-separated chunk outside
figures and tables) gets two ratings, keyed by paragraph number:

* Text color: how much a rewrite would clarify it
  (scripts/cidr_rewrite.json):
    R  large benefit       red
    O  moderate benefit    orange
    B  minor polish        blue
    N  leave as is         uncolored
* Margin bar: intrinsic reading complexity (scripts/cidr_complexity.json):
    XL difficult  red      L medium-hard  orange
    M  complex but smooth  blue           S simple  no bar

Each paragraph also gets a small tag "[id rewrite/complexity]" so
paragraphs can be discussed by number.  Bars are drawn with TikZ from
positions saved in the .aux file, so the document needs two passes (Tectonic
reruns automatically); bars split across column and page breaks.

cidr.tex itself is not modified.  Usage, from the repo root:
    python3 scripts/cidr_complexity.py            # write cidr-complexity.tex
    python3 scripts/cidr_complexity.py --list     # print numbered paragraphs
    tectonic cidr-complexity.tex
"""
import json
import os
import re
import sys

SRC = "cidr.tex"
OUT = "cidr-complexity.tex"
COMPLEXITY = os.path.join("scripts", "cidr_complexity.json")
REWRITE = os.path.join("scripts", "cidr_rewrite.json")
TEXT_COLORS = {"R": "red!80!black", "O": "orange!90!black", "B": "blue!75!black"}
BAR_COLORS = {"XL": "red!80!black", "L": "orange!90!black", "M": "blue!60"}
# The same colors as RGB, emitted directly: PGF and xcolor both cache colors
# across pictures and would skip setting a color they believe is current.
BAR_RGB = {"XL": "0.8 0 0", "L": "0.9 0.45 0", "M": "0.4 0.4 1"}
SKIP_ENVS = ("figure", "figure*", "table", "table*", "tikzpicture",
             "verbatim", "thebibliography", "CCSXML")
# Headings that may open a chunk; color starts after them.
HEAD = re.compile(r"(?:\s*(?:\\(?:section|subsection|subsubsection|paragraph)\*?"
                  r"\{(?:[^{}]|\{[^{}]*\})*\}|\\label\{[^}]*\}|%[^\n]*\n))*\s*")
# Leading material after which a paragraph's text starts.
LEAD = re.compile(r"(?:\s*(?:\\begin\{(?:theorem|lemma|proposition|corollary|"
                  r"definition|example|remark|proof|enumerate|itemize|"
                  r"abstract)\}(?:\[[^\]]*\])?|\\label\{[^}]*\}|\\item\b|"
                  r"\\noindent\b|\\vspace\{[^}]*\}|%[^\n]*\n))*\s*")
# Trailing material before which a paragraph's text ends.
TRAIL = re.compile(r"(?:\s|\\end\{(?:theorem|lemma|proposition|corollary|"
                   r"definition|example|remark|proof|enumerate|itemize|abstract|"
                   r"acks)\}|\\label\{[^}]*\}|\\proofinfull\b|%[^\n]*)*$")
DISPLAY_END = re.compile(r"(\\end\{(?:equation\*?|split|align\*?)\}|\\\])\s*$")
STRUCT_START = re.compile(r"\s*\\(bibliography|bibliographystyle|maketitle|appendix|"
                          r"end\{document\}|title|author|affiliation|email|"
                          r"keywords|settopmatter|input|newcommand|"
                          r"renewcommand|usepackage|documentclass|ccsdesc)\b")

PREAMBLE = r"""
\usepackage{xcolor}
\makeatletter
\newcommand{\cxtag}[2]{\textsuperscript{\textsf{\tiny[#1\,#2]}}}
% \cxdef{id}{s|e}{x sp}{y sp}{page}: read back from the .aux file.
\newcommand{\cxdef}[5]{\expandafter\gdef\csname cx@#1@#2\endcsname{{#3}{#4}{#5}}}
\newcommand{\cx@unpack}[4]{\def#1##1##2##3{%
  \dimen@=##1sp\edef#2{\strip@pt\dimen@}\dimen@=##2sp\edef#3{\strip@pt\dimen@}%
  \def#4{##3}}}
\newcommand{\cx@geom}[1]{% #1: page number
  \ifodd#1\relax\pgfmathsetmacro\cx@L{72.27+\oddsidemargin}%
  \else\pgfmathsetmacro\cx@L{72.27+\evensidemargin}\fi
  \pgfmathsetmacro\cx@T{\paperheight-72.27-\topmargin-\headheight-\headsep}%
  \pgfmathsetmacro\cx@B{\cx@T-\textheight}}
\newcommand{\cx@col}[2]{% x, macro to set
  \pgfmathsetmacro#2{((#1-\cx@L)>(\columnwidth+0.5*\columnsep))?1:0}}
\def\cx@rgb#1 #2 #3\relax{\pgfsys@color@rgb@stroke{#1}{#2}{#3}}
\newcommand{\cx@line}[4]{% "r g b", x, y1, y2 (pt, page coordinates)
  \begin{tikzpicture}[remember picture,overlay]
    \cx@rgb#1\relax
    \draw[line width=2.5pt] ([shift={(#2pt,#3pt)}]current page.south west)
      -- ([shift={(#2pt,#4pt)}]current page.south west);
  \end{tikzpicture}}
% \cxbar{id}{color}{s|e}: save this position; draw the bar piece on this page.
\newcommand{\cxbar}[3]{%
  \pdfsavepos
  \write\@auxout{\string\cxdef{#1}{#3}{\the\pdflastxpos}{\the\pdflastypos}{\thepage}}%
  \ifcsname cx@#1@s\endcsname\ifcsname cx@#1@e\endcsname
    \begingroup
    \expandafter\expandafter\expandafter\cx@gets\csname cx@#1@s\endcsname
    \expandafter\expandafter\expandafter\cx@gete\csname cx@#1@e\endcsname
    \cx@geom{\ifx#3s\cx@sp\else\cx@ep\fi}%
    \cx@col{\cx@sx}\cx@cs \cx@col{\cx@ex}\cx@ce
    \pgfmathsetmacro\cx@same{(\cx@sp==\cx@ep && \cx@cs==\cx@ce && \cx@ey<\cx@sy)?1:0}%
    \pgfmathsetmacro\cx@top{\cx@sy+8}\pgfmathsetmacro\cx@bot{\cx@ey-2}%
    \if#3s%
      \pgfmathsetmacro\cx@X{\cx@L+\cx@cs*(\columnwidth+\columnsep)-6}%
      \ifdim\cx@same pt=1pt \cx@line{#2}{\cx@X}{\cx@top}{\cx@bot}%
      \else \cx@line{#2}{\cx@X}{\cx@top}{\cx@B}\fi
    \else
      \pgfmathsetmacro\cx@X{\cx@L+\cx@ce*(\columnwidth+\columnsep)-6}%
      \ifdim\cx@same pt=1pt \else \cx@line{#2}{\cx@X}{\cx@T}{\cx@bot}\fi
    \fi
    \endgroup
  \fi\fi}
\cx@unpack\cx@gets\cx@sx\cx@sy\cx@sp
\cx@unpack\cx@gete\cx@ex\cx@ey\cx@ep
\makeatother
"""


def chunks(text):
    """Split into (start, end) spans of blank-line-separated chunks."""
    spans, pos = [], 0
    for m in re.finditer(r"\n[ \t]*\n", text):
        spans.append((pos, m.start()))
        pos = m.end()
    spans.append((pos, len(text)))
    return spans


def prose_paragraphs(text):
    """Yield (head, start, end, b) for prose paragraphs in the body.

    head: where the color starts (after headings); start: where the text
    starts (tag and bar start); end: where the text ends (bar end); b: chunk
    end."""
    body = text.index("\\begin{document}")
    depth = 0
    for a, b in chunks(text):
        if a < body:
            continue
        chunk = text[a:b]
        nocom = re.sub(r"(?<!\\)%.*", "", chunk)
        opened = sum(len(re.findall(r"\\begin\{%s\}" % re.escape(e), nocom)) for e in SKIP_ENVS)
        closed = sum(len(re.findall(r"\\end\{%s\}" % re.escape(e), nocom)) for e in SKIP_ENVS)
        was_inside = depth > 0
        depth += opened - closed
        if was_inside or opened or not nocom.strip():
            continue
        if STRUCT_START.match(nocom):
            continue
        head = a + HEAD.match(chunk).end()
        start = LEAD.match(text, head).end()
        rest = text[start:b]
        if not re.search(r"[A-Za-z]{3}", re.sub(r"\\[A-Za-z]+|\$[^$]*\$", "", rest)):
            continue
        if re.match(r"\s*\\(end|begin)\{", rest) and not re.search(r"[a-z]{4} [a-z]{3}", rest):
            continue
        end = start + TRAIL.search(rest).start()
        m = DISPLAY_END.search(text, start, end)
        if m:  # end the bar before a closing display, outside math mode
            opener = max(text.rfind("\\begin{equation", start, end),
                         text.rfind("\\[", start, end))
            if opener > start:
                end = opener
        yield head, start, end, b


def main():
    text = open(SRC).read()
    paras = list(prose_paragraphs(text))
    if "--list" in sys.argv:
        for n, (h, s, e, b) in enumerate(paras, 1):
            line = text.count("\n", 0, h) + 1
            print(f"=== [{n}] line {line}")
            print(text[h:b].strip())
        return
    cx = json.load(open(COMPLEXITY)) if os.path.exists(COMPLEXITY) else {}
    rw = json.load(open(REWRITE)) if os.path.exists(REWRITE) else {}
    title = text.index("\\maketitle")
    out, last = [], 0
    counts = {}
    for n, (h, s, e, b) in enumerate(paras, 1):
        c, r = cx.get(str(n), "?"), rw.get(str(n), "?")
        counts[r + "/" + c] = counts.get(r + "/" + c, 0) + 1
        bar = BAR_RGB.get(c) if h > title else None
        out.append(text[last:h])
        out.append("\\color{%s}" % TEXT_COLORS.get(r, "black"))
        out.append(text[h:s])
        out.append("\\cxtag{%d}{%s/%s}" % (n, r, c))
        if bar:
            out.append("\\cxbar{%d}{%s}{s}" % (n, bar))
        out.append(text[s:e])
        if bar:
            out.append("\\cxbar{%d}{%s}{e}" % (n, bar))
        last = e
    out.append(text[last:])
    res = "".join(out)
    res = res.replace("\\begin{document}", PREAMBLE + "\\begin{document}", 1)
    legend = ("\\maketitle\n\\noindent{\\small\\textsf{Text color, benefit of a rewrite: "
              "\\textcolor{%s}{R large}, \\textcolor{%s}{O moderate}, "
              "\\textcolor{%s}{B minor polish}, N leave (black).  "
              "Margin bar, intrinsic complexity: "
              "\\textcolor{%s}{XL}, \\textcolor{%s}{L}, \\textcolor{%s}{M}, "
              "S no bar.  Tags: [paragraph rewrite/complexity].}}\\par\n"
              % (TEXT_COLORS["R"], TEXT_COLORS["O"], TEXT_COLORS["B"],
                 BAR_COLORS["XL"], BAR_COLORS["L"], BAR_COLORS["M"]))
    res = res.replace("\\maketitle\n", legend, 1)
    res = "\n".join(ln.rstrip() for ln in res.split("\n"))
    open(OUT, "w").write(res)
    print(f"{len(paras)} paragraphs; " +
          ", ".join(f"{k}: {v}" for k, v in sorted(counts.items())))


if __name__ == "__main__":
    main()
