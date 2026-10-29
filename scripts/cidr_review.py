#!/usr/bin/env python3
"""Generate cidr-review.tex: cidr.tex with review markup.

* Sentences of cidr.tex that do not appear verbatim (up to whitespace) in the
  full version's sections/ are colored blue: text written or edited for the
  CIDR cut.
* Runs of full-version sentences (and labels) that cidr.tex dropped are noted
  in place, in red, after the last kept sentence that precedes them.

cidr.tex itself is not modified.  Usage, from the repo root:
    python3 scripts/cidr_review.py && ~/.local/bin/tectonic cidr-review.tex
"""
import re
import difflib
import json
import os

SECTIONS = ["introduction", "functional-calm", "complete-calm", "distributed",
            "composition", "instances", "discussion", "conclusion"]
SKIP_ENVS = {"figure", "figure*", "table", "table*", "equation", "equation*",
             "align", "align*", "tabular", "tikzpicture", "displaymath",
             "verbatim"}
STRUCT = re.compile(r"\\(begin|end|label|section|subsection|subsubsection|"
                    r"bibliography|bibliographystyle|maketitle|appendix|"
                    r"input|centering)\b")


def strip_comments(text):
    return "\n".join(re.sub(r"(?<!\\)%.*$", "", ln) for ln in text.split("\n"))


def expand_inputs(text):
    def rep(m):
        return expand_inputs(strip_comments(open(m.group(1) if m.group(1).endswith(".tex")
                                                 else m.group(1) + ".tex").read()))
    return re.sub(r"\\input\{([^}]*)\}", rep, text)


def norm(s):
    return re.sub(r"\s+", " ", s).strip()


def split_sentences(par):
    """Split a prose paragraph at sentence ends outside math and braces."""
    out, cur, depth, math, i = [], [], 0, False, 0
    while i < len(par):
        c = par[i]
        if c == "\\" and i + 1 < len(par):
            cur.append(par[i:i + 2]); i += 2; continue
        if c == "$":
            math = not math
        elif c == "{":
            depth += 1
        elif c == "}":
            depth = max(0, depth - 1)
        cur.append(c)
        if (c in ".?!" and not math and depth == 0 and i + 1 < len(par)
                and par[i + 1].isspace()):
            j = i + 1
            while j < len(par) and par[j].isspace():
                j += 1
            if j < len(par) and (par[j].isupper() or par[j] in "\\$(`"):
                out.append("".join(cur)); cur = []; i = j; continue
        i += 1
    if "".join(cur).strip():
        out.append("".join(cur))
    return out


def prose_units(lines):
    """Yield (kind, payload) items: ('raw', line) or ('par', [sentences])."""
    depth_skip, buf = 0, []

    def flush():
        if buf:
            text = "\n".join(buf)
            buf.clear()
            return [("par", split_sentences(text))]
        return []

    for ln in lines:
        envs_open = re.findall(r"\\begin\{([^}]*)\}", ln)
        envs_close = re.findall(r"\\end\{([^}]*)\}", ln)
        if depth_skip or any(e in SKIP_ENVS for e in envs_open) or \
                ln.strip().startswith("\\["):
            yield from flush()
            depth_skip += sum(e in SKIP_ENVS for e in envs_open)
            depth_skip -= sum(e in SKIP_ENVS for e in envs_close)
            if ln.strip().startswith("\\["):
                depth_skip += 1
            if ln.strip().endswith("\\]"):
                depth_skip -= 1
            depth_skip = max(depth_skip, 0)
            yield ("raw", ln); continue
        s = ln.strip()
        m = re.match(r"(\\paragraph\{[^}]*\}|\\item(\[[^\]]*\])?)\s*(.*)$", s)
        if not s or (STRUCT.match(s) and not m):
            yield from flush(); yield ("raw", ln); continue
        if m:
            yield from flush(); yield ("raw", m.group(1))
            if m.group(3):
                buf.append(m.group(3))
            continue
        buf.append(ln)
    yield from flush()


def plain(s, n=16):
    s = re.sub(r"\$[^$]*\$", "[math]", s)
    s = re.sub(r"\\(cite|ref|label)\{[^}]*\}", "", s)
    s = re.sub(r"\\[a-zA-Z]+\*?(\[[^\]]*\])?", "", s)
    s = re.sub(r"[{}~\\_^&#%]", " ", s)
    w = s.split()
    return " ".join(w[:n]) + (" ..." if len(w) > n else "")


BLOCKS = []
CATNAME = {"F": "formal definition/notation", "C": "formal caution", "E": "example",
           "X": "explanation", "R": "signposting", "T": "result",
           "W": "related-work detail", "?": "unclassified"}


def main():
    corpus_text = "\n".join(expand_inputs(strip_comments(open(f"sections/{n}.tex").read()))
                            for n in SECTIONS)
    corpus_norm = norm(corpus_text)
    src = open("cidr.tex").read()
    head, rest = src.split("\\begin{document}", 1)
    body, tail = rest.split("\\bibliographystyle", 1)
    front, body = body.split("\\maketitle", 1)
    front += "\\maketitle"
    body = strip_comments(body)
    cidr_norm = norm(body)
    cidr_labels = set(re.findall(r"\\label\{([^}]*)\}", body))

    # cidr sentences not found verbatim: candidates for "edited" matches.
    cidr_sens = [norm(x) for k, p in prose_units(body.split("\n")) if k == "par"
                 for x in p if norm(x) and norm(x) not in corpus_norm]

    def edited(sen):
        """A removed source sentence that survives, lightly edited, in cidr."""
        a = norm(sen)
        best, key = 0.0, None
        for b in cidr_sens:
            if abs(len(a) - len(b)) < 0.5 * len(a):
                r = difflib.SequenceMatcher(None, a, b, autojunk=False).ratio()
                if r > best:
                    best, key = r, b
        return key if best >= 0.75 else None

    # Source units in order: sentences and labels, marked kept or removed.
    src_units = []
    for kind, pay in prose_units(corpus_text.split("\n")):
        if kind == "par":
            for sen in pay:
                if norm(sen):
                    if norm(sen) in cidr_norm:
                        src_units.append(("s", norm(sen), True))
                    else:
                        k = edited(sen)
                        src_units.append(("s", k if k else sen, bool(k)))
        for lab in re.findall(r"\\label\{([^}]*)\}", pay if kind == "raw" else " ".join(pay)):
            src_units.append(("l", lab, lab in cidr_labels))
    # Removed blocks keyed by the normalized text of the preceding kept sentence.
    notes, last_kept, block = {}, "__START__", []
    def close():
        if block:
            BLOCKS.append({"anchor": last_kept[:80],
                           "sentences": [u[1] for u in block if u[0] == "s"],
                           "labels": [u[1] for u in block if u[0] == "l"]})
            notes.setdefault(last_kept, []).append(len(BLOCKS) - 1)
            block.clear()
    for u in src_units:
        if u[2]:
            close()
            if u[0] == "s":
                last_kept = norm(u[1])
                if last_kept not in cidr_norm:
                    # source sentence is a substring of a larger cidr sentence
                    pass
        else:
            block.append(u)
    close()
    cats = json.load(open(os.path.join(os.path.dirname(__file__), "cidr_categories.json")))

    def bkey(b):
        if b["sentences"]:
            return re.sub(r"\s+", " ", b["sentences"][0]).strip()[:60]
        return "LABELS:" + ",".join(b["labels"])

    for b in BLOCKS:
        b["words"] = sum(len(re.sub(r"\$[^$]*\$", "M", x).split()) for x in b["sentences"])
        b["cat"] = cats.get(bkey(b), "?")
    order = sorted(range(len(BLOCKS)), key=lambda i: -BLOCKS[i]["words"])
    for r, i in enumerate(order, 1):
        BLOCKS[i]["rank"] = r

    def render(i):
        b = BLOCKS[i]
        msg = [f"\\textbf{{{CATNAME[b['cat']]}}}, {b['words']} words, rank {b['rank']}"]
        if b["sentences"]:
            msg.append(f"\\textit{{{plain(b['sentences'][0])}}}")
        if b["labels"]:
            msg.append("labels " + ", ".join(l.replace("_", "\\_") for l in b["labels"]))
        return "; ".join(msg)

    notes = {k: [render(i) for i in v] for k, v in notes.items()}

    # Re-key notes whose anchor sentence sits inside a longer cidr sentence.
    all_cidr = [norm(x) for k, p in prose_units(body.split("\n")) if k == "par"
                for x in p if norm(x)]
    for k in list(notes):
        if k != "__START__" and k not in all_cidr:
            host = next((c for c in all_cidr if k in c), None)
            if host:
                notes.setdefault(host, []).extend(notes.pop(k))

    out, n_new, n_old, used = [], 0, 0, set()
    pending_start = notes.get("__START__")
    for kind, pay in prose_units(body.split("\n")):
        if kind == "raw":
            out.append(pay); continue
        pieces = []
        for sen in pay:
            key = norm(sen)
            if not key:
                continue
            if key in corpus_norm:
                n_old += 1; pieces.append(sen.strip())
            else:
                n_new += 1
                wrap = ("\\textcolor{newblue}{" + sen.strip() + "}"
                        if not re.search(r"\\(begin|end|item|par)\b", sen)
                        else "{\\color{newblue}" + sen.strip() + "}")
                pieces.append(wrap)
            if key in notes and key not in used:
                used.add(key)
                for nt in notes[key]:
                    pieces.append("\\removednote{" + nt + "}")
        if pending_start and pieces:
            pieces.insert(0, "\\removednote{" + "; ".join(pending_start) + "}")
            pending_start = None
        out.append(" ".join(pieces))
    unplaced = [k for k in notes if k not in used and k != "__START__"]
    macros = (
        "\\usepackage{xcolor}\n"
        "\\definecolor{newblue}{RGB}{0,70,200}\n"
        "\\definecolor{cutred}{RGB}{190,0,0}\n"
        "\\newcommand{\\removednote}[1]{{\\color{cutred}\\footnotesize"
        "\\,[removed: #1]\\,}}\n")
    tot = {}
    for b in BLOCKS:
        tot.setdefault(b["cat"], [0, 0]); tot[b["cat"]][0] += 1; tot[b["cat"]][1] += b["words"]
    rows = "".join(f"{CATNAME[c]} & {n} & {w}\\\\\n" for c, (n, w) in
                   sorted(tot.items(), key=lambda kv: -kv[1][1]))
    top = "".join(f"{BLOCKS[i]['rank']}. {CATNAME[BLOCKS[i]['cat']]}, {BLOCKS[i]['words']} words: "
                  f"\\textit{{{plain(BLOCKS[i]['sentences'][0], 10) if BLOCKS[i]['sentences'] else ''}}}\\par\n"
                  for i in order[:12])
    summary = ("\\noindent{\\color{cutred}\\footnotesize\\textbf{Removals by category}\\par\n"
               "\\begin{tabular}{lrr}category & blocks & words\\\\\\hline\n" + rows +
               "\\end{tabular}\\par\\smallskip\\textbf{Largest removals}\\par\n" + top + "}\\par\\medskip\n")
    review = (head + macros + "\\begin{document}" + front + "\n" + summary +
              "\\noindent{\\color{newblue}Blue: new or edited for CIDR.}\\quad"
              "{\\color{cutred}Red: removed from the full version.}\\par\n"
              + "\n".join(out) + "\n\\bibliographystyle" + tail)
    open("cidr-review.tex", "w").write(review)
    json.dump(BLOCKS, open(os.environ.get("TMPDIR", ".") + "/cidr_blocks.json", "w"), indent=1)
    print(f"sentences kept {n_old}, new/edited {n_new}, removed-note anchors "
          f"{len(used)}, unplaced {len(unplaced)}")


if __name__ == "__main__":
    main()
