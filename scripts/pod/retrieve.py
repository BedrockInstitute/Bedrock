#!/usr/bin/env python3
"""The retrieval seam of the POD, and the miss signal that measures it.

Design: `dev/memos/LJ-4-pod-program-design.md` section 7.4, Parts 1a and 1b.
Rule R10: the program retrieves the archive and the literature, and the worker
never surveys by hand.

WHY THIS EXISTS, and it is measured rather than feared.
`scripts/gate/check-dd18-survey.py` gates the RETURN side of DD18 and prints the
BRIEF side. Measured on 2026-08-17 by that checker: 19 gated tasks and 0
defects, over 282 live briefs of which 244 never name
`archive/dev/JOURNAL-archived.md`. The form was healthy and the content was not,
because a survey an author performs by hand decays into a ritual line. The
program performs the search now, so the worker cannot skip a survey it never had
to run.

THE SEAM, Part 1a. One function builds the `## ARCHIVE` and the `## LITERATURE`
block of a brief:

    retrieve(query: str, scope: list[str], k: int) -> list[tuple[str, float]]

A later implementation replaces this one function and nothing else. The first
implementation is BM25 over whole files, `K1 = 1.5`, `B = 0.75`, standard
library only, no index file and no cache. The archive scope is 103 files and
near 1 MB, so one ranking is one pass.

THE SCOPE IS THE MEASURED PART AND THE RANKER IS NOT. MEASURED 2026-08-17 over
the seven archive cases of `agents/tasks/LJ-1-376/lj-1.376-report.md`, recorded
at `dev/measurements/pod-retrieval-scoping-2026-08-17.txt:19-31`. The same BM25
ran twice with the same constants and the same queries. Over the full corpus of
1,706 documents the gold file reached rank 444 for episode 7; over the archive
scope alone it reached rank 1. The measured cause is dilution by the live task
corpus: 443 documents outranked the gold file and 418 of them were live task
documents (`:33-36`).

THE CORPUS RULE, lifted from that experiment
(`dev/measurements/pod-retrieval-scoping-2026-08-17.py:63-64`). A directory that
holds an Agda master contributes its masters, because that is its content. A
directory that holds no master contributes its Markdown records. MEASURED
2026-08-17 by the reproduction in `scripts/tests/test_pod_gates.py`: the looser
rule, every `*.md` under the prefix, adds the three `README.md` index files of
`archive/src/` and costs episode 7 three ranks (1 to 4) and episode 5 three
ranks (3 to 6). An index file names every module, so it ranks high for any query
and holds no answer. That is the same dilution finding at file scale.

A ZERO SCORE IS NOT A CANDIDATE, and that is what makes `NO HIT` reachable.
BM25 scores every file of the scope, and a file that shares no query token
scores exactly 0.0. An earlier form of `retrieve()` returned the top `k` of that
full ranking, so a brief always carried 5 CANDIDATE paths, and 5 paths that
share no token with the query are noise the worker must still read. Section 7.4
rules that "A `NO HIT` line is a first-class result" and that it "removes the
whole class of declined by ritual". `retrieve()` therefore drops every zero
score and returns fewer than `k`, or nothing at all.

THE MISS SIGNAL, Part 1b. The program measures its own retrieval from data the
flow already gives it. At brief build it records the `k` paths it injected. At
the return it reads `ARCHIVE USED` and extracts every path there. The miss set
is what the return used and the injection did not offer. `miss_signal()` builds
one JSON line per dispatch for the tracked transition log:

    {"event":"retrieval","task":"<code>","offered":5,"used":3,
     "missed":["<path>"],"overlap":0.0}

THE PRODUCER OF THAT LINE, AND WHERE THE LOOP MUST CALL IT. `miss_signal()` is
the arithmetic and it needs the two lists. `dispatch_signal()` is the producer:
it takes ONE dispatch's two tracked artifacts, the brief the program wrote and
the report the worker returned, and it builds the record with no second state
file. The `offered` list is read back out of the brief's own
`## ARCHIVE (program-generated, do not edit)` block, because `candidate_block()`
wrote it there; the scope comes from the same block's `Corpus search over` line.

    dispatch_signal("LJ-1.386", brief_path, report_path) -> dict

`scripts/pod/pod.py` must call it ONCE per return. THE CALL SITE IS `_rule_c()`,
next to `emit(st, t, RETURNED, CHECKING, root=root)`, which fires exactly once
for each return; the record then goes to `emit_event()`, which already names the
`retrieval` line as one of its two kinds and needs no new transition. The two
functions are the anchor and the line numbers move: at
`scripts/pod/pod.py:2034` and `:539` when this was written on 2026-08-17.
MEASURED the same day by grep over `scripts/`: `miss_signal(` had zero callers,
so Part 1b measured nothing at all. `scripts/pod/pod.py` belongs to another
agent, so this module states the seam and never writes the call.

`overlap` is the discriminative overlap. It counts the shared tokens whose
document frequency is below half the scope's file count, and it separates the
two failure kinds mechanically. A HIGH overlap says the file shares real words
and only ranked low, so the cure is a narrower scope or a better ranker. A ZERO
overlap says the file and the query share no discriminative token, and no
lexical method reaches it. MEASURED precedent, episode 1: the query and the gold
passage share `step` at document frequency 1,072 of 1,706 and `lj` at 886 of
1,706, and both are noise at corpus scale
(`dev/measurements/pod-retrieval-scoping-2026-08-17.txt:38-43`).

THE TRIGGER TO ADOPT A SEMANTIC INDEX, and this module reports it and never
fires it. ADOPT when both conditions hold over two consecutive weeks: the miss
rate `missed / used` goes above 20 percent, AND most missed paths carry ZERO
discriminative overlap. DO NOT ADOPT when the misses carry a high overlap,
because that is a scope problem or a ranking problem.

USAGE, as a library and as a hand tool:

    from retrieve import retrieve, build_query, miss_signal, dispatch_signal
    hits = retrieve(build_query(modules, obligations, goal), ARCHIVE_SCOPE, 5)

    python3 scripts/pod/retrieve.py --scope archive/src --k 5 "<query text>"
    python3 scripts/pod/retrieve.py --scope archive/src --k 5 \
        --goal-of agents/tasks/LJ-1-237/LJ-1.237.md
    python3 scripts/pod/retrieve.py --signal LJ-1.386 \
        --brief agents/tasks/LJ-1-386/LJ-1.386.md

Exit status: 0 in query mode and in signal mode, 2 on a usage or environment
failure. No mode of this module gates, so no mode exits 1.
"""

from __future__ import annotations

import argparse
import json
import math
import re
import sys
from collections import Counter
from pathlib import Path

# LJ-1.291: the root is found by walking up to the repository marker, never by
# counting directories; `scripts/repo_root.py` holds the one walk. LJ-1.295:
# this script lives in a group directory under scripts/, so the SCRIPTS root,
# where `repo_root.py` and `agents_tree.py` sit flat, is found the same way,
# by walking up to `repo_root.py` itself; the group directory joins sys.path
# for siblings imported by bare name.
_HERE = Path(__file__).resolve()
sys.path.insert(0, str(_HERE.parent))
_SCRIPTS = next((p for p in _HERE.parents if (p / "repo_root.py").is_file()), None)
if _SCRIPTS is None:
    raise FileNotFoundError(
        f"no repo_root.py above {_HERE}: refusing to guess the scripts root (C-43)")
sys.path.insert(0, str(_SCRIPTS))
from repo_root import find_root  # noqa: E402

ROOT = find_root(__file__)

#: The BM25 constants of the frozen experiment. They were fixed before any
#: result was inspected and no constant is tuned to a gold label.
K1 = 1.5
B = 0.75

#: The archive corpus of section 7.4. The builder passes it for `## ARCHIVE`.
ARCHIVE_SCOPE = [
    "archive/src",
    "archive/dev/TASKS-archived.md",
    "archive/dev/JOURNAL-archived.md",
    "archive/dev/DECISIONS-archived.md",
    "dev/ARCHIVE.md",
]

#: The literature corpus of section 7.4, for `## LITERATURE`.
LITERATURE_SCOPE = ["dev/literature"]

#: The tokenizer, lifted verbatim from
#: `dev/measurements/pod-retrieval-scoping-2026-08-17.py:25-49`. A word starts
#: with a letter, a number stands alone, and a CJK character is one token.
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

#: The GOAL section of a brief, the query the measurement used. A brief with no
#: GOAL heading falls back to its first 40 lines, exactly as the record did.
GOAL_HEAD = re.compile(r"^#+\s*GOAL\b", re.I)
NEXT_HEAD = re.compile(r"^#{1,2}\s+\S")

#: The `## ARCHIVE USED` section of a return, and every repository-relative path
#: inside it. Part 1b reads the paths a worker actually took.
USED_SECTION = re.compile(
    r"^#{1,}\s*(?:\d+\.?\s*)?(?:ARCHIVE|LITERATURE)\s+USED\b.*?$(.*?)(?=^#{1,}\s|\Z)",
    re.S | re.M)
USED_PATH = re.compile(
    r"(?<![\w/.-])(?:archive|dev|src|scripts|agents)/[A-Za-z0-9./_+-]+")

#: The program-generated block of a brief, and the two lines the producer of
#: Part 1b reads back out of it. `candidate_block()` writes both, so the brief
#: is the record of what the program offered and no second state file exists.
INJECTED_BLOCK = re.compile(
    r"^##\s+(ARCHIVE|LITERATURE)\s+\(program-generated[^)\n]*\)\s*$(.*?)(?=^##\s|\Z)",
    re.S | re.M)
OFFERED_LINE = re.compile(r"^-\s+CANDIDATE\s+(\S+)", re.M)
SCOPE_LINE = re.compile(r"^Corpus search over ([^:\n]+):", re.M)


def tokens(text: str) -> list[str]:
    """The token list of one text. Short words and stop words are dropped."""
    out: list[str] = []
    for m in WORD.finditer(text):
        w = m.group(0).lower()
        if len(w) < 2 or w in STOP:
            continue
        out.append(w)
    out.extend(CJK.findall(text))
    return out


def read(rel: str) -> str:
    with open(ROOT / rel, encoding="utf-8", errors="replace") as fh:
        return fh.read()


def corpus(scope: list[str]) -> list[str]:
    """The repository-relative files one scope admits, sorted and unique.

    A scope entry is a file or a directory prefix. A file entry admits itself. A
    directory entry admits its Agda masters when it holds any, and its Markdown
    records otherwise. The docstring above records what the looser rule costs.
    """
    found: list[str] = []
    for entry in scope:
        p = ROOT / entry
        if p.is_file():
            found.append(entry)
            continue
        if not p.is_dir():
            continue
        masters = sorted(p.rglob("*.lagda.md"))
        chosen = masters or sorted(q for q in p.rglob("*.md") if q.is_file())
        found += [str(q.relative_to(ROOT)) for q in chosen]
    return sorted(set(found))


class Index:
    """One BM25 index over whole files. It is built per call and never cached.

    Lifted from `dev/measurements/pod-retrieval-scoping-2026-08-17.py:81-107`,
    which is the frozen experiment the scoping figures come from.
    """

    def __init__(self, paths: list[str]) -> None:
        self.paths = list(paths)
        self.tf = {p: Counter(tokens(read(p))) for p in self.paths}
        self.len = {p: max(1, sum(self.tf[p].values())) for p in self.paths}
        self.N = len(self.paths)
        self.avgdl = sum(self.len.values()) / max(1, self.N)
        self.df: Counter = Counter()
        for p in self.paths:
            for w in self.tf[p]:
                self.df[w] += 1

    def bm25(self, qterms: list[str]) -> dict[str, float]:
        scores: dict[str, float] = {}
        for p in self.paths:
            tf = self.tf[p]
            dl = self.len[p]
            s = 0.0
            for w in qterms:
                f = tf.get(w, 0)
                if not f:
                    continue
                idf = math.log((self.N - self.df[w] + 0.5) / (self.df[w] + 0.5) + 1.0)
                s += idf * (f * (K1 + 1)) / (f + K1 * (1 - B + B * dl / self.avgdl))
            scores[p] = s
        return scores

    def discriminative(self, qterms: list[str], text: str) -> int:
        """Shared tokens whose document frequency is below half the scope size.

        A token the scope never holds has document frequency 0, so it counts as
        discriminative. That is the honest direction: a rare word is a word a
        lexical ranker could have used.
        """
        have = set(tokens(text))
        limit = self.N / 2
        return sum(1 for w in set(qterms) if w in have and self.df[w] < limit)


def retrieve(query: str, scope: list[str], k: int) -> list[tuple[str, float]]:
    """The seam of Part 1a. Rank the scope against the query, best first.

    Returns `(repository-relative path, score)` pairs, highest score first, at
    most `k` of them. A tie breaks by path, so the result is deterministic and
    a record of it reproduces.

    A FILE THAT SCORES 0.0 IS NOT A CANDIDATE and it never enters the list. BM25
    scores every file of the scope, so the top `k` of the raw ranking always
    holds `k` paths, even when the query shares no token with any of them. The
    result is then `NO HIT`, which section 7.4 rules a first-class result.
    """
    paths = corpus(scope)
    if not paths or k <= 0:
        return []
    index = Index(paths)
    qterms = sorted(set(tokens(query)))
    scores = index.bm25(qterms)
    ranked = sorted(((p, s) for p, s in scores.items() if s > 0.0),
                    key=lambda kv: (-kv[1], kv[0]))
    return ranked[:k]


def goal_text(brief: str) -> str:
    """The GOAL section of the brief at this path. See `goal_text_of()`."""
    return goal_text_of(read(brief))


def goal_text_of(text: str) -> str:
    """The GOAL section of a brief, or its first 40 lines when it has none.

    Lifted from `dev/measurements/pod-retrieval-scoping-2026-08-17.py:110-125`,
    so a query built here is the query the measurement ranked. It takes the
    TEXT, so the producer of Part 1b rebuilds the query from a brief it already
    read and never opens the same file twice.
    """
    lines = text.splitlines()
    start = None
    for i, line in enumerate(lines):
        if GOAL_HEAD.match(line.strip()):
            start = i + 1
            break
    if start is None:
        return "\n".join(lines[:40])
    end = len(lines)
    for j in range(start, len(lines)):
        if NEXT_HEAD.match(lines[j]):
            end = j
            break
    return "\n".join(lines[start:end])


def build_query(modules: list[str], obligations: list[str], goal: str) -> str:
    """The query of section 7.4: module names, obligation names, and the goal.

    The keys are DERIVED and never typed. `modules` comes from the write scope
    and `obligations` from the obligation list, so no author writes a search
    term.
    """
    names = [n.split("::")[-1] for n in obligations]
    return "\n".join([*modules, *names, goal])


def candidate_block(heading: str, query: str, scope: list[str],
                    k: int = 5) -> str:
    """The program-generated block a brief carries, `## ARCHIVE` or the other.

    It writes the `k` paths as CANDIDATE lines and it never says that a file
    bears on the task. A scope that returns nothing prints `NO HIT`, which is a
    first-class result: it removes the whole class of "declined by ritual",
    because the program declined it and not the author.
    """
    hits = retrieve(query, scope, k)
    out = [f"## {heading} (program-generated, do not edit)", ""]
    if not hits:
        out.append(f"Corpus search over {', '.join(scope)}: NO HIT")
        return "\n".join(out) + "\n"
    out.append(f"Corpus search over {', '.join(scope)}:")
    for path, score in hits:
        out.append(f"- CANDIDATE {path}  (score {score:.3f})")
    return "\n".join(out) + "\n"


def used_paths(report_text: str) -> list[str]:
    """Every repository-relative path a return names in a USED section."""
    found: list[str] = []
    for m in USED_SECTION.finditer(report_text):
        for p in USED_PATH.finditer(m.group(1)):
            path = p.group(0).rstrip("./")
            if path not in found:
                found.append(path)
    return found


def miss_signal(task: str, offered: list[str], used: list[str],
                query: str, scope: list[str]) -> dict:
    """The one JSON-ready record of Part 1b, for the transition log.

    `offered` is what the builder injected. `used` is what the return names.
    The miss set is `used` minus `offered`. `overlap` is the MEAN
    discriminative overlap over the missed files, and it is 0.0 when nothing is
    missed. A file the tree no longer holds contributes 0.
    """
    missed = [p for p in used if p not in set(offered)]
    scores: list[int] = []
    if missed:
        index = Index(corpus(scope))
        qterms = sorted(set(tokens(query)))
        for path in missed:
            p = ROOT / path
            scores.append(index.discriminative(qterms, read(path))
                          if p.is_file() else 0)
    overlap = round(sum(scores) / len(scores), 3) if scores else 0.0
    return {"event": "retrieval", "task": task, "offered": len(offered),
            "used": len(used), "missed": missed, "overlap": overlap}


def _abs(path: str | Path) -> Path:
    """One repository-relative or absolute path, as one absolute path."""
    p = Path(path)
    return p if p.is_absolute() else ROOT / p


def injected_blocks(brief_text: str) -> list[tuple[str, list[str], list[str]]]:
    """Each program-generated block of one brief, as (heading, scope, offered).

    `candidate_block()` wrote the block, so the brief IS the record of what the
    program offered. A `NO HIT` block gives an empty offered list and keeps its
    scope, because the provenance line names the scope in both cases. A block
    written without that line falls back to the standing scope of its heading.
    """
    out: list[tuple[str, list[str], list[str]]] = []
    for m in INJECTED_BLOCK.finditer(brief_text):
        heading, body = m.group(1), m.group(2)
        found = SCOPE_LINE.search(body)
        scope = ([s.strip() for s in found.group(1).split(",") if s.strip()]
                 if found else
                 (ARCHIVE_SCOPE if heading == "ARCHIVE" else LITERATURE_SCOPE))
        out.append((heading, scope, OFFERED_LINE.findall(body)))
    return out


def report_beside(brief: str | Path) -> Path | None:
    """The return that sits beside a brief, in the ONE directory of a task.

    `agents/README.md` rules that the brief and the report share one directory,
    so the return needs no second lookup path. `REPORT.md` wins, then the single
    `*-report.md`. A caller that knows the path passes it instead.
    """
    d = _abs(brief).parent
    named = d / "REPORT.md"
    if named.is_file():
        return named
    found = sorted(p for p in d.glob("*.md") if p.stem.lower().endswith("-report"))
    return found[0] if found else None


def dispatch_signal(task: str, brief: str | Path,
                    report: str | Path | None = None) -> dict:
    """THE PRODUCER of Part 1b: one retrieval record for one dispatch.

    It reads the two tracked artifacts of the dispatch and nothing else. The
    brief gives the offered paths and the scope, because the program wrote them
    into it; the report gives the used paths. A return with no report gives
    `used = 0` and an empty miss set, which is the honest reading: a dispatch
    that returned no document used nothing the program can see. A brief with no
    program-generated block gives `offered = 0` and makes every used path a
    miss, which is also the honest reading: the program offered nothing.

    The loop calls this once per return, in `_rule_c()` of
    `scripts/pod/pod.py`, and the record goes to `emit_event()` there.
    """
    btext = _abs(brief).read_text(encoding="utf-8", errors="replace")
    offered: list[str] = []
    scope: list[str] = []
    for _heading, block_scope, paths in injected_blocks(btext):
        for p in paths:
            if p not in offered:
                offered.append(p)
        for s in block_scope:
            if s not in scope:
                scope.append(s)
    if report is None:
        report = report_beside(brief)
    rtext = ""
    if report is not None and _abs(report).is_file():
        rtext = _abs(report).read_text(encoding="utf-8", errors="replace")
    return miss_signal(task, offered, used_paths(rtext), goal_text_of(btext),
                       scope or ARCHIVE_SCOPE)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description="POD retrieval, section 7.4")
    parser.add_argument("query", nargs="?", default="",
                        help="the query text")
    parser.add_argument("--goal-of", metavar="BRIEF",
                        help="take the query from this brief's GOAL section")
    parser.add_argument("--scope", action="append", metavar="PREFIX",
                        help="a repository-relative file or directory prefix; "
                             "repeat it, or omit it for the archive corpus")
    parser.add_argument("--k", type=int, default=5, help="how many candidates")
    parser.add_argument("--signal", metavar="TASK",
                        help="Part 1b: print the retrieval record of one "
                             "dispatch, from its brief and its report")
    parser.add_argument("--brief", metavar="PATH",
                        help="the brief of --signal's dispatch")
    parser.add_argument("--report", metavar="PATH",
                        help="the return of --signal's dispatch; the default "
                             "is the report beside the brief")
    args = parser.parse_args(argv[1:])

    if args.signal:
        if not args.brief:
            print("retrieve: --signal needs --brief", file=sys.stderr)
            return 2
        if not _abs(args.brief).is_file():
            print(f"retrieve: no such brief: {args.brief}", file=sys.stderr)
            return 2
        if args.report and not _abs(args.report).is_file():
            print(f"retrieve: no such report: {args.report}", file=sys.stderr)
            return 2
        print(json.dumps(dispatch_signal(args.signal, args.brief, args.report),
                         ensure_ascii=False))
        return 0
    if args.brief or args.report:
        print("retrieve: --brief and --report belong to --signal",
              file=sys.stderr)
        return 2

    query = args.query
    if args.goal_of:
        if not (ROOT / args.goal_of).is_file():
            print(f"retrieve: no such brief: {args.goal_of}", file=sys.stderr)
            return 2
        query = goal_text(args.goal_of)
    if not query.strip():
        print("retrieve: give a query, or --goal-of a brief", file=sys.stderr)
        return 2

    scope = args.scope or ARCHIVE_SCOPE
    hits = retrieve(query, scope, args.k)
    print(json.dumps({"scope": scope, "files": len(corpus(scope)),
                      "k": args.k}, ensure_ascii=False))
    for path, score in hits:
        print(f"{score:9.3f}  {path}")
    if not hits:
        print("NO HIT")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
