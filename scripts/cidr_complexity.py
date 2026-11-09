#!/usr/bin/env python3
"""Generate cidr-complexity.tex: cidr.tex colored by reading complexity.

Each prose paragraph of cidr.tex (a blank-line-separated chunk outside
figures and tables) gets a rating from
scripts/cidr_complexity.json, keyed by paragraph number:

  XL  difficult            red
  L   medium-hard          orange
  M   complex but smooth   blue
  S   very simple          uncolored

Each rated paragraph also gets a small tag "[id·rating]" so paragraphs can be
discussed by number.  Paragraphs with no rating are tagged "[id·?]".

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
RATINGS = os.path.join("scripts", "cidr_complexity.json")
COLORS = {"XL": "red!80!black", "L": "orange!90!black", "M": "blue!75!black"}
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
STRUCT_START = re.compile(r"\s*\\(bibliography|bibliographystyle|maketitle|appendix|"
                          r"end\{document\}|title|author|affiliation|email|"
                          r"keywords|settopmatter|input|newcommand|"
                          r"renewcommand|usepackage|documentclass|ccsdesc)\b")


def chunks(text):
    """Split into (start, end) spans of blank-line-separated chunks."""
    spans, pos = [], 0
    for m in re.finditer(r"\n[ \t]*\n", text):
        spans.append((pos, m.start()))
        pos = m.end()
    spans.append((pos, len(text)))
    return spans


def prose_paragraphs(text):
    """Yield (start_of_text, chunk) for prose paragraphs in the body."""
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
        start = head + LEAD.match(text, head).end() - head
        rest = text[start:b]
        if not re.search(r"[A-Za-z]{3}", re.sub(r"\\[A-Za-z]+|\$[^$]*\$", "", rest)):
            continue
        # A chunk that is only a displayed equation or \end{...} lines.
        if re.match(r"\s*\\(end|begin)\{", rest) and not re.search(r"[a-z]{4} [a-z]{3}", rest):
            continue
        yield head, start, b


def main():
    text = open(SRC).read()
    paras = list(prose_paragraphs(text))
    if "--list" in sys.argv:
        for n, (a, s, b) in enumerate(paras, 1):
            line = text.count("\n", 0, a) + 1
            print(f"=== [{n}] line {line}")
            print(text[a:b].strip())
        return
    ratings = json.load(open(RATINGS)) if os.path.exists(RATINGS) else {}
    out, last = [], 0
    counts = {}
    for n, (a, s, b) in enumerate(paras, 1):
        r = ratings.get(str(n), "?")
        counts[r] = counts.get(r, 0) + 1
        color = COLORS.get(r, "black")
        out.append(text[last:a])
        out.append("\\color{%s}" % color)
        out.append(text[a:s])
        out.append("\\cxtag{%d}{%s}" % (n, r))
        last = s
    out.append(text[last:])
    res = "".join(out)
    preamble = ("\\usepackage{xcolor}\n"
                "\\newcommand{\\cxtag}[2]{\\textsuperscript{\\textsf{\\tiny[#1\\,#2]}}}\n")
    res = res.replace("\\begin{document}", preamble + "\\begin{document}", 1)
    legend = ("\\maketitle\n\\noindent{\\small\\textsf{Reading complexity: "
              "\\textcolor{%s}{XL difficult}, \\textcolor{%s}{L medium-hard}, "
              "\\textcolor{%s}{M complex but smooth}, S simple (black).  "
              "Tags give paragraph number and rating.}}\\par\n"
              % (COLORS["XL"], COLORS["L"], COLORS["M"]))
    res = res.replace("\\maketitle\n", legend, 1)
    open(OUT, "w").write(res)
    print(f"{len(paras)} paragraphs; " +
          ", ".join(f"{k}: {v}" for k, v in sorted(counts.items())))


if __name__ == "__main__":
    main()
