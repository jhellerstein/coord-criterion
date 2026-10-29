#!/usr/bin/env python3
"""Generate main-review.tex: main.tex with text already in cidr.tex grayed.

* Sentences of the full version that appear in cidr.tex verbatim (up to
  whitespace), or nearly so (character similarity >= THRESHOLD to some cidr
  sentence), are set in light gray: material already reviewed in the CIDR cut.
* Everything else (full-version-only text, appendices, and sentences whose
  wording differs from CIDR) stays black.
* Headings, labels, displays, figures, and tables are left untouched.

main.tex and the section files are not modified.  Usage, from the repo root:
    python3 scripts/main_review.py && ~/.local/bin/tectonic main-review.tex
"""
import difflib
import re
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from cidr_review import strip_comments, norm, prose_units  # noqa: E402

THRESHOLD = 0.85


def expand_inputs(text):
    def rep(m):
        name = m.group(1) if m.group(1).endswith(".tex") else m.group(1) + ".tex"
        return strip_comments(open(name).read())
    return re.sub(r"(?m)^\s*\\input\{([^}]*)\}", rep, text)


def cidr_sentences():
    src = strip_comments(open("cidr.tex").read())
    body = src.split("\\begin{document}", 1)[1].split("\\bibliographystyle", 1)[0]
    sens = [norm(x) for k, p in prose_units(body.split("\n")) if k == "par"
            for x in p if norm(x)]
    return norm(body), sens


def main():
    cidr_norm, cidr_sens = cidr_sentences()
    by_len = sorted(cidr_sens, key=len)

    def reviewed(sen):
        a = norm(sen)
        if len(a) < 12:
            return False
        if a in cidr_norm:
            return True
        sm = difflib.SequenceMatcher(None, a, autojunk=False)
        for b in by_len:
            if abs(len(a) - len(b)) > (1 - THRESHOLD) * len(a) * 2:
                continue
            sm.set_seq2(b)
            if sm.real_quick_ratio() >= THRESHOLD and sm.quick_ratio() >= THRESHOLD \
                    and sm.ratio() >= THRESHOLD:
                return True
        return False

    src = open("main.tex").read()
    head, rest = src.split("\\begin{document}", 1)
    body, tail = rest.split("\\bibliographystyle", 1)
    body = expand_inputs(strip_comments(body))

    out, n_gray, n_black = [], 0, 0

    def emit(units):
        nonlocal n_gray, n_black
        for kind, pay in units:
            if kind == "raw":
                out.append(pay); continue
            pieces = []
            for sen in pay:
                if not norm(sen):
                    continue
                if reviewed(sen):
                    n_gray += 1
                    if re.search(r"\\(begin|end|item|par)\b", sen):
                        pieces.append("{\\color{reviewed}" + sen.strip() + "}")
                    else:
                        pieces.append("\\textcolor{reviewed}{" + sen.strip() + "}")
                else:
                    n_black += 1
                    pieces.append(sen.strip())
            out.append(" ".join(pieces))

    # Only the abstract and the text after \maketitle are processed; the title
    # block, CCS concepts, and keywords pass through untouched.
    pre, rest2 = body.split("\\begin{abstract}", 1)
    abstract, rest2 = rest2.split("\\end{abstract}", 1)
    mid, after = rest2.split("\\maketitle", 1)
    out.append(pre + "\\begin{abstract}")
    emit(prose_units(abstract.split("\n")))
    out.append("\\end{abstract}" + mid + "\\maketitle")
    emit(prose_units(after.split("\n")))

    macros = ("\\definecolor{reviewed}{gray}{0.62}\n")
    legend = ("\\noindent{\\small\\textcolor{reviewed}{Gray: also in cidr.tex "
              "(verbatim or $\\ge$" + str(int(THRESHOLD * 100)) +
              "\\% similar), already reviewed.}"
              " Black: full version only, or worded differently.}\\par\\medskip\n")
    text = "\n".join(out).replace("\\maketitle", "\\maketitle\n" + legend, 1)
    open("main-review.tex", "w").write(head + macros + "\\begin{document}" + text +
                                       "\n\\bibliographystyle" + tail)
    print(f"sentences gray {n_gray}, black {n_black}")


if __name__ == "__main__":
    main()
