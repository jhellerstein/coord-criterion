#!/usr/bin/env python3
"""Generate main-complexity.tex: main.tex (flattened) marked up for rewriting.

The full-paper analogue of scripts/cidr_complexity.py.  Each prose paragraph
of each file that main.tex \\inputs gets a key "<file>#<n>" (n counts the
prose paragraphs of that file from 1) and two ratings, stored per file in
scripts/main-ratings/<basename>.json as {"<n>": {"r": ..., "c": ...}}:

* r, text color: benefit of a rewrite.  R large (red), O moderate (orange),
  B minor polish (blue), N leave (black).
* c, margin bar: intrinsic reading complexity.  XL (red), L (orange),
  M (blue), S (no bar).

Paragraphs whose text is mostly also in cidr.tex (by the sentence matcher of
scripts/main_review.py) are marked C, set in gray, and not rated: they were
reviewed in the CIDR pass.

Usage, from the repo root:
    python3 scripts/main_complexity.py              # write main-complexity.tex
    python3 scripts/main_complexity.py --list [F]   # print unshared paragraphs
    python3 scripts/main_complexity.py --stats
    tectonic main-complexity.tex
"""
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cidr_complexity as cx  # noqa: E402
from cidr_review import norm, split_sentences  # noqa: E402
import main_review as mr  # noqa: E402

OUT = "main-complexity.tex"
RATINGS = os.path.join("scripts", "main-ratings")
SHARED = 0.6  # fraction of a paragraph's characters in CIDR sentences
INITIAL = "--initial" in sys.argv  # show the first-pass ratings r0/c0
GRAY = "black!45"


def input_files(path="main.tex"):
    """Files \\input by main.tex, in order, including nested inputs."""
    out = []
    for m in re.finditer(r"(?m)^\s*\\input\{([^}]*)\}", open(path).read()):
        name = m.group(1) if m.group(1).endswith(".tex") else m.group(1) + ".tex"
        if os.path.exists(name):
            out.append(name)
            out += input_files(name)
    return out


def paragraphs(path):
    """(head, start, end, b) spans of the prose paragraphs of one file."""
    text = open(path).read()
    pre = "\\begin{document}\n"
    return text, [(h - len(pre), s - len(pre), e - len(pre), b - len(pre))
                  for h, s, e, b in cx.prose_paragraphs(pre + text)]


_reviewed = None


def reviewed_fn():
    """The sentence matcher of main_review.py, built once."""
    global _reviewed
    if _reviewed is None:
        import difflib
        cidr_norm, cidr_sens = mr.cidr_sentences()
        by_len = sorted(cidr_sens, key=len)

        def reviewed(sen):
            a = norm(sen)
            if len(a) < 12:
                return False
            if a in cidr_norm:
                return True
            sm = difflib.SequenceMatcher(None, a, autojunk=False)
            for b in by_len:
                if abs(len(a) - len(b)) > (1 - mr.THRESHOLD) * len(a) * 2:
                    continue
                sm.set_seq2(b)
                if sm.real_quick_ratio() >= mr.THRESHOLD and \
                        sm.quick_ratio() >= mr.THRESHOLD and sm.ratio() >= mr.THRESHOLD:
                    return True
            return False
        _reviewed = reviewed
    return _reviewed


def shared_fraction(par):
    sens = [s for s in split_sentences(par) if norm(s)]
    total = sum(len(norm(s)) for s in sens) or 1
    rev = reviewed_fn()
    return sum(len(norm(s)) for s in sens if rev(s)) / total


def ratings_file(path):
    """scripts/main-ratings/<basename>.json; an appendix whose basename is also
    a section file gets <basename>-app.json."""
    base = os.path.basename(path)[:-4]
    if path.startswith("appendices/") and os.path.exists(os.path.join("sections", base + ".tex")):
        base += "-app"
    return os.path.join(RATINGS, base + ".json")


def ratings(path):
    f = ratings_file(path)
    return json.load(open(f)) if os.path.exists(f) else {}


def analyze():
    """Yield (file, n, text, spans, para_text, shared?, rating dict)."""
    for f in input_files():
        text, paras = paragraphs(f)
        rt = ratings(f)
        for n, (h, s, e, b) in enumerate(paras, 1):
            if h < 0:  # the file's opening heading chunk; keeps numbering stable
                continue
            par = text[h:b]
            r = dict(rt.get(str(n), {}))
            if INITIAL:
                r = {"r": r.get("r0", r.get("r")), "c": r.get("c0", r.get("c"))}
            yield f, n, text, (h, s, e, b), par, shared_fraction(par) >= SHARED, r


def main():
    args = sys.argv[1:]
    if "--list" in args:
        only = [a for a in args if not a.startswith("--")]
        for f, n, text, (h, s, e, b), par, shared, rt in analyze():
            if shared or (only and f not in only and os.path.basename(f) not in only):
                continue
            line = text.count("\n", 0, h) + 1
            print(f"=== [{f}#{n}] line {line} {rt.get('r', '?')}/{rt.get('c', '?')}")
            print(par.strip())
        return
    rows = list(analyze())
    if "--stats" in args:
        counts = {}
        for f, n, *_, shared, rt in rows:
            k = "C" if shared else rt.get("r", "?") + "/" + rt.get("c", "?")
            counts.setdefault(f, {}).setdefault(k, 0)
            counts[f][k] += 1
        for f, c in counts.items():
            print(f, ", ".join(f"{k}: {v}" for k, v in sorted(c.items())))
        return
    by_file = {}
    for f, n, text, spans, par, shared, rt in rows:
        by_file.setdefault(f, (text, []))[1].append((n, spans, shared, rt))
    marked = {}
    for f, (text, items) in by_file.items():
        out, last = [], 0
        tag = os.path.basename(f)[:-4]
        for n, (h, s, e, b), shared, rt in items:
            if shared:
                color, label, bar = GRAY, "C", None
            else:
                r, c = rt.get("r", "?"), rt.get("c", "?")
                color = cx.TEXT_COLORS.get(r, "black")
                label, bar = f"{r}/{c}", cx.BAR_RGB.get(c)
            key = f"{tag}-{n}"
            out += [text[last:h], "\\color{%s}" % color, text[h:s],
                    "\\cxtag{%s:%d}{%s}" % (tag, n, label)]
            if bar:
                out.append("\\cxbar{%s}{%s}{s}" % (key, bar))
            out.append(text[s:e])
            if bar:
                out.append("\\cxbar{%s}{%s}{e}" % (key, bar))
            out.append("\\color{black}")
            last = e
        out.append(text[last:])
        marked[f] = "".join(out)
    src = open("main.tex").read()

    def rep(m):
        name = m.group(1) if m.group(1).endswith(".tex") else m.group(1) + ".tex"
        return marked.get(name, open(name).read()) if os.path.exists(name) else m.group(0)
    res = src
    for _ in range(3):  # nested inputs
        res = re.sub(r"(?m)^\s*\\input\{([^}]*)\}", lambda m: rep(m), res)
    res = res.replace("\\begin{document}", cx.PREAMBLE + "\\begin{document}", 1)
    legend = ("\\noindent{\\small\\textsf{Gray: mostly also in cidr.tex (reviewed there). "
              "Text color, benefit of a rewrite: \\textcolor{%s}{R large}, "
              "\\textcolor{%s}{O moderate}, \\textcolor{%s}{B minor polish}, N leave. "
              "Margin bar, intrinsic complexity: \\textcolor{%s}{XL}, \\textcolor{%s}{L}, "
              "\\textcolor{%s}{M}, S no bar.  Tags: [file:paragraph rewrite/complexity].}}\\par\n"
              % (cx.TEXT_COLORS["R"], cx.TEXT_COLORS["O"], cx.TEXT_COLORS["B"],
                 cx.BAR_COLORS["XL"], cx.BAR_COLORS["L"], cx.BAR_COLORS["M"]))
    res = res.replace("\\maketitle", "\\maketitle\n" + legend, 1)
    res = "\n".join(ln.rstrip() for ln in res.split("\n"))
    out_name = OUT.replace(".tex", "-initial.tex") if INITIAL else OUT
    open(out_name, "w").write(res)
    n_sh = sum(1 for r in rows if r[5])
    print(f"{len(rows)} paragraphs, {n_sh} shared with CIDR, {len(rows) - n_sh} to rate")


if __name__ == "__main__":
    main()
