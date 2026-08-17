#!/usr/bin/env python3
"""FROZEN RECORD, not a tool. The retrieval scoping experiment of 2026-08-17.

Cited by dev/POD.md section 7.4. Its output is
dev/measurements/pod-retrieval-scoping-2026-08-17.txt, beside this file.

Nothing runs this. It is kept so the measurement method can be read, and
because dev/measurements/README.md rules that a record of a tree state that no
longer exists cannot be regenerated. Part 1 is the ranker and the episode
table; part 2 is the archive-scoped run. Part 2 imported part 1 as a module
when it ran, and the two are joined here so the record is one file.

PARAMETERS WERE FIXED BEFORE ANY RESULT WAS INSPECTED. No constant is tuned
to a gold label.
"""

# ============================ PART 1: the ranker and the episodes ============
"""
import math, os, re, sys, json
from collections import Counter

ROOT = "/Users/alsg/Agentic/Bedrock"

# ---------------------------------------------------------------- tokenizer
WORD = re.compile(r"[A-Za-z][A-Za-z0-9_']*|[0-9]+")
CJK = re.compile(r"[㐀-鿿]")

STOP = set("""a an the and or but if then else of in on at to for from by with without
as is are was were be been being do does did done has have had having this that these those
it its it's he she they them his her their we our you your i me my not no nor so than too very
can could may might must shall should will would there here what which who whom whose when where
why how all any both each few more most other some such only own same s t just don now
one two three four five six seven eight nine ten first second third
use used using make makes made get gets got give gives given take takes taken
also into over under out up down again further once about against between during before after
above below off through during while because until up
""".split())

def tokens(text):
    out = []
    for m in WORD.finditer(text):
        w = m.group(0).lower()
        if len(w) < 2:
            continue
        if w in STOP:
            continue
        out.append(w)
    out.extend(CJK.findall(text))
    return out

# ---------------------------------------------------------------- corpus
def rel(p):
    return os.path.relpath(p, ROOT)

def walk(subdir, exts):
    hits = []
    for dirpath, _dirs, files in os.walk(os.path.join(ROOT, subdir)):
        for f in files:
            if any(f.endswith(e) for e in exts):
                hits.append(rel(os.path.join(dirpath, f)))
    return sorted(hits)

CORPUS_A = walk("agents/tasks", [".md"]) + walk("archive/dev", [".md"]) + walk("archive/src", [".lagda.md"])
CORPUS_B = CORPUS_A + walk("dev", [".md"]) + walk("src", [".lagda.md"])
CORPUS_A = sorted(set(CORPUS_A)); CORPUS_B = sorted(set(CORPUS_B))

def read(p):
    with open(os.path.join(ROOT, p), encoding="utf-8", errors="replace") as fh:
        return fh.read()

FULL = {}      # path -> token list (full text)
HEAD = {}      # path -> token list (headings + first 20 lines)
for p in CORPUS_B:
    txt = read(p)
    FULL[p] = tokens(txt)
    lines = txt.splitlines()
    head_lines = [l for l in lines if l.startswith("#")] + lines[:20]
    HEAD[p] = tokens("\n".join(head_lines))

# ---------------------------------------------------------------- index
class Index:
    def __init__(self, paths, toks):
        self.paths = list(paths)
        self.tf = {p: Counter(toks[p]) for p in self.paths}
        self.len = {p: max(1, len(toks[p])) for p in self.paths}
        self.N = len(self.paths)
        self.avgdl = sum(self.len.values()) / max(1, self.N)
        self.df = Counter()
        for p in self.paths:
            for w in self.tf[p]:
                self.df[w] += 1

    def bm25(self, qterms, k1=1.5, b=0.75):
        scores = {}
        for p in self.paths:
            tf = self.tf[p]; dl = self.len[p]; s = 0.0
            for w in qterms:
                f = tf.get(w, 0)
                if not f:
                    continue
                idf = math.log((self.N - self.df[w] + 0.5) / (self.df[w] + 0.5) + 1.0)
                s += idf * (f * (k1 + 1)) / (f + k1 * (1 - b + b * dl / self.avgdl))
            scores[p] = s
        return scores

    def overlap(self, qterms):
        return {p: sum(1 for w in qterms if w in self.tf[p]) for p in self.paths}

# ---------------------------------------------------------------- queries
def goal_text(brief_path):
    txt = read(brief_path)
    lines = txt.splitlines()
    start = None
    for i, l in enumerate(lines):
        if re.match(r"^#+\s*GOAL\b", l.strip(), re.I):
            start = i + 1
            break
    if start is None:
        return "\n".join(lines[:40]), "first 40 lines (no GOAL heading)"
    end = len(lines)
    for j in range(start, len(lines)):
        if re.match(r"^#{1,2}\s+\S", lines[j]):
            end = j
            break
    return "\n".join(lines[start:end]), "GOAL section (lines %d-%d)" % (start + 1, end)

# ---------------------------------------------------------------- episodes
# gold = path of the file named under "**The reading:**" in lj-1.376-report.md
EPISODES = [
    # (id, cost, brief path, gold path, note, secondary_gold)
    ("1",  2.0,  "agents/tasks/LJ-1-242/LJ-1.242.md", "dev/PLAN.md",
     "step-6 price already on the open-work list", None),
    ("2",  1.5,  "agents/tasks/LJ-1-373/LJ-1.373.md", "dev/literature/truncation-and-selection.md",
     "digest already answered the shape question", "src/Base/Choice.lagda.md"),
    ("3",  1.5,  "agents/tasks/LJ-1-230/LJ-1.230.md", "dev/PLAN.md",
     "wall (a) already measured CLOSED, index row :1047", None),
    ("3b", 1.5,  "agents/tasks/LJ-1-228/LJ-1.228.md", "dev/PLAN.md",
     "same episode, the other brief", None),
    ("4",  1.0,  "agents/tasks/LJ-1-177/LJ-1.177.md", "dev/PLAN.md",
     "term cured five rows earlier, index row :1078", None),
    ("5",  1.0,  "agents/tasks/LJ-1-353/LJ-1.353.md",
     "archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md",
     "archived csb never named by the brief", None),
    ("5b", 1.0,  "agents/tasks/LJ-1-136/LJ-1.136.md",
     "archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md",
     "same episode, the false 'CSB nowhere' measurement", None),
    ("6",  0.5,  "agents/tasks/LJ-1-92/LJ-1.92.md",
     "archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md",
     "order-type assembly rebuilt in a 365-line probe", None),
    ("7",  0.5,  "agents/tasks/LJ-1-237/LJ-1.237.md",
     "archive/src/2026-08-09-rud-route/L/Condensation.lagda.md",
     "levelStory declined as not bearing", None),
    ("7b", 0.5,  "agents/tasks/LJ-1-239/LJ-1.239.md",
     "archive/src/2026-08-09-rud-route/L/Condensation.lagda.md",
     "same episode, the second declining brief", None),
    ("9",  0.5,  "agents/tasks/LJ-1-329/LJ-1.329.md",
     "agents/tasks/LJ-1-321/lj-1.321-report.md",
     "pullOrder wants a total map out of sq", None),
    ("10", 0.25, "agents/tasks/archive/LJ-1-6/LJ-1.6.md", "archive/dev/TASKS-archived.md",
     "T85 had cured the quotient objection", None),
    ("11", 0.5,  "agents/tasks/archive/LJ-1-10/LJ-1.10.md", "archive/dev/TASKS-archived.md",
     "T130 recorded the Def-step as MISSING content", None),
]

def rank_of(scores, gold, excluded):
    """(deterministic rank, n_strictly_better, tie_group_size, gold_score) or None if gold absent."""
    if gold not in scores:
        return None
    live = {p: s for p, s in scores.items() if p not in excluded}
    if gold not in live:
        return None
    g = live[gold]
    better = sum(1 for p, s in live.items() if s > g + 1e-12)
    ties = [p for p, s in live.items() if abs(s - g) <= 1e-12]
    ties.sort()
    det = better + 1 + ties.index(gold)
    return (det, better + 1, len(ties), g)

def bucket(r):
    if r is None:
        return "ABSENT"
    d = r[0]
    if d <= 1: return "top1"
    if d <= 3: return "top3"
    if d <= 10: return "top10"
    return "miss(rank %d)" % d

def run(corpus_name, paths):
    idxF = Index(paths, FULL)
    idxH = Index(paths, HEAD)
    rows = []
    for eid, cost, brief, gold, note, gold2 in EPISODES:
        qtext, qsrc = goal_text(brief)
        qterms = sorted(set(tokens(qtext)))
        own_dir = os.path.dirname(brief)
        excluded = {p for p in paths if p.startswith(own_dir + "/")}
        excluded |= {p for p in paths if p.startswith("agents/tasks/LJ-1-376/")}
        r1 = idxF.overlap(qterms)
        r2 = idxF.bm25(qterms)
        r3 = idxH.bm25(qterms)
        res = {}
        for tag, sc in (("R1", r1), ("R2", r2), ("R3", r3)):
            res[tag] = rank_of(sc, gold, excluded)
            top = sorted(((s, p) for p, s in sc.items() if p not in excluded),
                         key=lambda x: (-x[0], x[1]))[:10]
            res[tag + "_top"] = [(p, round(s, 3)) for s, p in top]
        rows.append(dict(id=eid, cost=cost, brief=brief, gold=gold, gold2=gold2,
                         note=note, qsrc=qsrc, nq=len(qterms), qterms=qterms, res=res))
    return rows

out = {}
for name, paths in (("A_specified", CORPUS_A), ("B_extended", CORPUS_B)):
    out[name] = run(name, paths)

print("corpus A (specified) files:", len(CORPUS_A))
print("corpus B (extended)  files:", len(CORPUS_B))
print()
for name in out:
    print("=" * 78)
    print("CORPUS", name)
    print("%-4s %-6s %-42s %-14s %-14s %-14s" % ("ep", "cost", "gold", "R1", "R2", "R3"))
    for r in out[name]:
        print("%-4s %-6s %-42s %-14s %-14s %-14s" % (
            r["id"], r["cost"], r["gold"][-42:],
            bucket(r["res"]["R1"]), bucket(r["res"]["R2"]), bucket(r["res"]["R3"])))
    print()

with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "results.json"), "w") as fh:
    json.dump(out, fh, indent=1, default=str)

# ============================ PART 2: the archive-scoped run ================
# It ran as a separate file importing part 1. The import lines are dropped.

S = os.path.dirname(os.path.abspath(__file__))

# ---- (1) episode 1: does the query share a word with the gold passage?
plan = open(os.path.join(S, "PLAN_at_242.md"), encoding="utf-8").read().splitlines()
goldp = "\n".join(plan[52:57])          # lines 53-57, open work item 1
q, qsrc = retr.goal_text("agents/tasks/LJ-1-242/LJ-1.242.md")
qs = set(retr.tokens(q)); gs = set(retr.tokens(goldp))
print("EPISODE 1 word-overlap check")
print("  query (%s): %s" % (qsrc, sorted(qs)))
print("  gold passage PLAN@242:53-57: %s" % sorted(gs))
print("  SHARED: %s" % sorted(qs & gs))
print()
n1 = set(retr.tokens("Step 6"))
n2 = set(retr.tokens("the leaf supply"))
print("  name-level check, JOURNAL's own claim:")
print("   'Step 6' -> %s ; 'the leaf supply' -> %s ; shared: %s" % (sorted(n1), sorted(n2), sorted(n1 & n2)))
print()

# ---- (2) archive-scoped retrieval, the search DD18's ARCHIVE section asks for
SCOPES = {
    "archive/src": [p for p in retr.CORPUS_B if p.startswith("archive/src/")],
    "archive/dev": [p for p in retr.CORPUS_B if p.startswith("archive/dev/")],
}
CASES = [
    ("5",  "agents/tasks/LJ-1-353/LJ-1.353.md", "archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md", "archive/src"),
    ("5b", "agents/tasks/LJ-1-136/LJ-1.136.md", "archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md", "archive/src"),
    ("6",  "agents/tasks/LJ-1-92/LJ-1.92.md",  "archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md", "archive/src"),
    ("7",  "agents/tasks/LJ-1-237/LJ-1.237.md","archive/src/2026-08-09-rud-route/L/Condensation.lagda.md", "archive/src"),
    ("7b", "agents/tasks/LJ-1-239/LJ-1.239.md","archive/src/2026-08-09-rud-route/L/Condensation.lagda.md", "archive/src"),
    ("10", "agents/tasks/archive/LJ-1-6/LJ-1.6.md", "archive/dev/TASKS-archived.md", "archive/dev"),
    ("11", "agents/tasks/archive/LJ-1-10/LJ-1.10.md", "archive/dev/TASKS-archived.md", "archive/dev"),
]
print("ARCHIVE-SCOPED RETRIEVAL (BM25 full text, same constants)")
print("%-4s %-12s %-6s %-14s %s" % ("ep", "scope", "N", "gold rank", "top3"))
for eid, brief, gold, scope in CASES:
    paths = SCOPES[scope]
    idx = retr.Index(paths, retr.FULL)
    qtext, _ = retr.goal_text(brief)
    qt = sorted(set(retr.tokens(qtext)))
    sc = idx.bm25(qt)
    ranked = sorted(((s, p) for p, s in sc.items()), key=lambda x: (-x[0], x[1]))
    r = next(i for i, (s, p) in enumerate(ranked, 1) if p == gold)
    print("%-4s %-12s %-6d %-14d %s" % (eid, scope, len(paths), r,
          "; ".join(os.path.basename(p) for s, p in ranked[:3])))
