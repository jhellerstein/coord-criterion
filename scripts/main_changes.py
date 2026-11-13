#!/usr/bin/env python3
"""Generate main-changes.tex: the full paper with every changed paragraph
shown twice, the old version (gray, small, labels stripped) above the new
one (blue).  Unchanged text is black.  Paragraphs are matched per input file
with difflib, so moved or split paragraphs show as removed and added.

Usage, from the repo root:
    python3 scripts/main_changes.py [BASE]      # BASE defaults to origin/main
    tectonic main-changes.tex
    python3 scripts/main_changes.py [BASE] --summary   # text summary only
"""
import difflib
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cidr_complexity as cx  # noqa: E402

OUT = "main-changes.tex"
NEWC, OLDC = "blue!70!black", "black!50"


def git_show(ref, path):
    r = subprocess.run(["git", "show", f"{ref}:{path}"], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else ""


def input_files(src):
    return [m.group(1) if m.group(1).endswith(".tex") else m.group(1) + ".tex"
            for m in re.finditer(r"(?m)^\s*\\input\{([^}]*)\}", src)]


def paras(text):
    pre = "\\begin{document}\n"
    spans = [(h - len(pre), s - len(pre), e - len(pre), b - len(pre))
             for h, s, e, b in cx.prose_paragraphs(pre + text)]
    return [sp for sp in spans if sp[0] >= 0]  # drop the file's opening heading chunk


def norm(s):
    return re.sub(r"\s+", " ", s).strip()


def old_block(t):
    t = re.sub(r"\\label\{[^}]*\}", "", t)
    t = re.sub(r"\n[ \t]*\n", "\n", t)  # no paragraph breaks (e.g. inside displays)
    t = re.sub(r"\\(begin|end)\{(theorem|lemma|proposition|corollary|definition|"
               r"example|remark|proof)\}(\[[^\]]*\])?", "", t)
    return ("\n\n{\\footnotesize\\color{%s}\\noindent\\textsf{[was]} %s\\par}\n\n"
            % (OLDC, t.strip()))


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    base = args[0] if args else "origin/main"
    summary = "--summary" in sys.argv
    src = open("main.tex").read()
    marked, n_changed, report = {}, 0, []
    for f in input_files(src):
        new, old = open(f).read(), git_show(base, f)
        pn, po = paras(new), paras(old)
        kn = [norm(new[h:b]) for h, s, e, b in pn]
        ko = [norm(old[h:b]) for h, s, e, b in po]
        sm = difflib.SequenceMatcher(a=ko, b=kn, autojunk=False)
        olds_for = {}   # new index -> list of old paragraph texts shown above it
        changed = set()
        tail_old = []
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag == "equal":
                continue
            ot = [old[po[i][0]:po[i][3]] for i in range(i1, i2)]
            if j2 > j1:
                olds_for.setdefault(j1, []).extend(ot)
                changed.update(range(j1, j2))
            elif j1 < len(pn):
                olds_for.setdefault(j1, []).extend(ot)
            else:
                tail_old.extend(ot)
            report.append((f, tag, list(range(i1 + 1, i2 + 1)), list(range(j1 + 1, j2 + 1))))
        n_changed += len(changed)
        out, last = [], 0
        for j, (h, s, e, b) in enumerate(pn):
            out.append(new[last:h])
            for t in olds_for.get(j, []):
                out.append(old_block(t))
            if j in changed:
                out += ["\\color{%s}" % NEWC, new[h:e], "\\color{black}"]
            else:
                out.append(new[h:e])
            last = e
        out.append(new[last:])
        for t in tail_old:
            out.append(old_block(t))
        marked[f] = "".join(out)
    if summary:
        for f, tag, oi, ni in report:
            print(f"{f}: {tag} old {oi} -> new {ni}")
        print(f"{n_changed} new or changed paragraphs")
        return

    def rep(m):
        name = m.group(1) if m.group(1).endswith(".tex") else m.group(1) + ".tex"
        return marked.get(name, m.group(0))
    res = re.sub(r"(?m)^\s*\\input\{([^}]*)\}", rep, src)
    legend = ("\\noindent{\\small\\textsf{Changes since %s: "
              "\\textcolor{%s}{blue} is new or changed text; "
              "\\textcolor{%s}{small gray [was]} is the old version.  %d paragraphs changed.}}"
              "\\par\\medskip\n" % (base.replace("_", "\\_"), NEWC, OLDC, n_changed))
    res = res.replace("\\maketitle", "\\maketitle\n" + legend, 1)
    open(OUT, "w").write(res)
    print(f"{n_changed} new or changed paragraphs; wrote {OUT}")


if __name__ == "__main__":
    main()
