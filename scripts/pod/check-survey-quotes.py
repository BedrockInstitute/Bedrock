#!/usr/bin/env python3
"""The survey verification of the POD: every injected path answered, at its line.

Design: `dev/memos/LJ-4-pod-program-design.md` section 7.4, Part 2. It fires at
acceptance conjunct 6, section 5.4, on the task that just returned.

WHY THIS EXISTS. It is lifted from `scripts/gate/check-dd18-survey.py`, which
stays in place until the cutover, and it keeps BOTH gated halves of that file:
`answered()` at `:302`, so the return must name every path the brief injected,
and `audit_quotes()` at `:339`, so a quoted phrase of twelve characters or more
must sit AT each cited `path:line`. `WINDOW = 3` and the three verdicts are
kept, because they are the measured part: a quote found only in a window of
three lines is a mis-cited line, and `[LJ-1.357]` found that defect twice by
hand.

WHY THE QUOTE DUTY GATES AND A COUNT DOES NOT. The minimal compliant form of
this check forces an ACT: the author must open the file to quote a line that
exists at the cited line number, and a pasted quote from another brief fails.
`[LJ-1.358]` measured the alternative: under a one-honest-line clause the survey
decay was LEGAL, one bullet sat verbatim in 63 briefs, and every gate stayed
green.

WHAT MOVED, and section 7.4 splits the old checker into three parts.

  * Part 1, RETRIEVAL, moved to the program. `scripts/pod/retrieve.py` injects
    the candidate list into `## ARCHIVE` and `## LITERATURE` at brief build, so
    a worker cannot skip a survey it never had to perform.
  * Part 2 is this file. It is physics: a quote sits at a line, or it does not.
  * Part 3, JUDGEMENT, moved to the adversarial reviewer of section 6.6.
    Whether an archive BEARS on a task is a judgement and no checker claimed
    otherwise (`check-dd18-survey.py:54`).

WHAT THIS FILE DROPS, stated rather than absorbed. The brief-side print of the
old B1 half goes: the template counter and the per-corpus naming score counted
prose compliance rather than reading, and retrieval makes both moot. The three
EPOCHS go, because the POD judges the task it just ran and never the corpus. The
`dev/PLAN.md` task-index backstop goes, because the runner fires this check at
the RETURN, so no report is mid-write, and `dev/pod/queue.toml` replaces that
section.

WHAT THIS REFUSES TO CHECK, because a row claiming more than its checker
delivers is false safety.

  * It cannot tell whether an archive BEARS on a task. Relevance stays review.
  * It cannot tell a true line quoted without understanding from one read
    deeply. The quote duty forces the file to be opened, not understood.
  * A quote from a `dev/literature/` file that no longer matches is COUNTED and
    never failed: those files are live and drift, while the archive corpora are
    frozen, so only the frozen corpora give a decisive verdict.

USAGE

    python3 scripts/pod/check-survey-quotes.py LJ-1.383
    python3 scripts/pod/check-survey-quotes.py --brief PATH --report PATH
    python3 scripts/pod/check-survey-quotes.py --all [--verbose]

THE GATE IS ONE TASK, AND `--all` IS A SURVEY TOOL. The runner names the task
that just returned. `--all` sweeps the whole tree and MEASURED 2026-08-17: 278
task pairs, 80 fail. Every one of those 80 is a record written before the
amendment of 2026-08-16, and a record is never rewritten, so `--all` must never
gate. On the epoch the old checker gates, `LJ-1-363` and later, this file and
`check-dd18-survey.py` agree: MEASURED 2026-08-17, 17 pairs, 0 defects on both.

Exit status: 0 clean, 1 a return failed, 2 a usage or environment failure.
"""

from __future__ import annotations

import argparse
import re
import sys
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
import agents_tree  # noqa: E402
from repo_root import find_root  # noqa: E402

ROOT = find_root(__file__)

SECTION = {
    "ARCHIVE": re.compile(
        r"^#{1,}\s*(?:\d+\.?\s*)?ARCHIVE\b(?!\s*USED).*?$(.*?)(?=^#{1,}\s|\Z)",
        re.S | re.M),
    "ARCHIVE USED": re.compile(
        r"^#{1,}\s*(?:\d+\.?\s*)?ARCHIVE\s+USED\b.*?$(.*?)(?=^#{1,}\s|\Z)",
        re.S | re.M),
    "LITERATURE": re.compile(
        r"^#{1,}\s*(?:\d+\.?\s*)?LITERATURE\b(?!\s*USED).*?$(.*?)(?=^#{1,}\s|\Z)",
        re.S | re.M),
    "LITERATURE USED": re.compile(
        r"^#{1,}\s*(?:\d+\.?\s*)?LITERATURE\s+USED\b.*?$(.*?)(?=^#{1,}\s|\Z)",
        re.S | re.M),
}

#: An archive citation: a path under `archive/` or the registry
#: `dev/ARCHIVE.md`. The lookbehind refuses `agents/tasks/archive/`, which
#: `[LJ-1.357]` settled is OUTSIDE the corpora.
ARCHIVE_PATH = re.compile(r"(?<![\w/.-])(?:archive/[A-Za-z0-9./_-]+|dev/ARCHIVE\.md)")

#: The literature corpus.
LIT_PATH = re.compile(r"dev/literature/[A-Za-z0-9./_-]+")

#: A path:line citation inside a USED section, the form the quote duty binds.
CITE = re.compile(
    r"`?((?:archive|agents/tasks|dev)/[A-Za-z0-9./_+-]+?)`?"
    r"(?::(\d+)(?:-(\d+))?(?:,\d+)*)+")

#: Any file-shaped token, for declines spelled relative to a root.
BARE = re.compile(r"\b[A-Za-z0-9][A-Za-z0-9./_+-]*\.(?:md|toml|py|agda)\b")

#: A written decline. Suffix spellings, "NOT read" and "WHY NOT" prose are
#: compliance, never a defect (`[LJ-1.357]`, the LJ-1-168 case).
DECLINE = re.compile(
    r"(?i)\b(?:not\s+read|declin\w*|not\s+re-?opened|nothing\s+(?:in\s+it\s+)?bears|"
    r"not\s+used|not\s+surveyed|why\s+not)\b")

#: The PROVENANCE line of a program-generated block, which names the CORPORA
#: the program searched and never a path it injected. `retrieve.py` writes it as
#: `Corpus search over <scope>:`. MEASURED 2026-08-17 over the archive scope: a
#: block that injected 2 candidates named 5 corpus paths on this line, so the
#: return had to decline 3 files the program had already declined for it.
#: Section 7.4 rules the opposite, that a `NO HIT` "removes the whole class of
#: declined by ritual, because the program declined it and not the author". The
#: line is therefore cut before the injected paths are read.
PROVENANCE = re.compile(r"^Corpus search (?:over|for)\b.*$", re.M)

#: A quoted span worth verifying: 12 or more characters inside double quotes
#: (straight or curly), inside CJK corner quotes, or inside backticks, which
#: is how LJ-1-361 quotes a module line. Short spans match everywhere and
#: verify nothing, and a span with no space is a term mention, not a line.
QUOTE = re.compile(
    r'["“]([^"”]{12,})["”]|'
    r"「([^」]{12,})」|"
    r"`([^`]{12,})`")

WINDOW = 3  # lines of slack before a quote is a mis-cited line


def section_of(text: str, name: str) -> str:
    m = SECTION[name].search(text)
    return m.group(1) if m else ""


def injected(sec: str) -> str:
    """One brief section, with the program's provenance line removed.

    What the return must ANSWER is what the program INJECTED: the candidate
    lines. The corpora the search ran over are provenance, and a corpus with no
    candidate was declined by the program itself.
    """
    return PROVENANCE.sub("", sec)


def normalize(s: str) -> str:
    s = re.sub(r"[*`_]", "", s)
    return re.sub(r"\s+", " ", s).strip()


def resolve(rel: str) -> Path | None:
    p = ROOT / rel
    if p.is_file():
        return p
    # A spelling relative to the retired route's root, the LJ-1-168 form.
    cand = ROOT / "archive" / "src" / "2026-08-09-rud-route" / rel
    return cand if cand.is_file() else None


def answered(want: str, have: set[str]) -> bool:
    """Exact, deeper, or a relative spelling of the SAME file.

    The prefix rule is ONE-WAY: a report may answer an injected directory by
    citing a file inside it, but a vaguer parent mention answers nothing.
    """
    w = want.rstrip("/")
    if want in have or w in have:
        return True
    for h in have:
        h = h.rstrip("/")
        if h.startswith(w + "/"):
            return True  # the report went deeper than the brief asked
        if h.endswith(w) or w.endswith(h):
            return True  # a decline spelled relative to a root
    return False


def bullets(sec: str) -> list[str]:
    """Bullets with whitespace collapsed only. Emphasis and backticks are
    kept, because a quote is EXTRACTED from the raw bullet and normalized
    only for comparison: stripping backticks first made LJ-1-361's
    backtick-quoted module line invisible to the very check it answers."""
    return [re.sub(r"\s+", " ", b).strip()
            for b in re.findall(r"(?:^|\n)\s*-\s+(.*?)(?=\n\s*-\s|\Z)", sec, re.S)]


def quote_fragments(q: str) -> list[str]:
    """A quote verifies when every fragment occurs in the cited range.
    Ellipsis, the CJK ellipsis, and the table-cell pipe are cut marks: a
    report that quotes two cells of a table row without naming the cells
    between them is using the row's own rendering convention, MEASURED on
    LJ-1-360's quote of TASKS-archived.md:171, not misquoting the file."""
    return [f for f in re.split(r"\.\.\.|…|\|", q) if len(f) >= 6]


def audit_quotes(sec: str) -> dict[str, dict]:
    """Per archived or literature FILE named in a USED section.

    Returns, per resolved file path: whether it was cited as read, declined
    in writing, or carries a quote verified at the cited line, plus the fail
    reasons of unverified quotes. A quote belongs to the NEAREST citation
    before it in the bullet, never to every citation in the bullet.

    **A MARKDOWN BLOCKQUOTE LINE IS A FOURTH QUOTE FORM, folded into the
    other three before a bullet is ever extracted.** MEASURED 2026-08-22 on
    `[LJ-1.500]`: three independent returns (the coder's report, both
    critic reviews) each cited `archive/dev/LJ-dispatch-index.md:433` with
    `Quote at ...:` followed by `> | LJ-1.379 | ... |` on its own line, and
    the cited text is verbatim correct. `QUOTE`'s three delimiters (double
    quotes, CJK corner quotes, backticks) do not cover `>`, so the checker
    fell through past the real quote to unrelated backtick spans nearby (the
    citation's own backtick-quoted path, a stray phrase in the surrounding
    prose) and reported a correct quote as "text the file does not hold".
    A `>`-prefixed line is rewritten to a double-quoted span HERE, while
    newlines still mark where a blockquote starts and ends; `bullets()`
    collapses them right after, and the existing double-quote branch of
    `QUOTE` needs no change to pick it up.
    """
    sec = re.sub(r'(?m)^[ \t]*>[ \t]*(.+)$', r'"\1"', sec)
    files: dict[str, dict] = {}
    for raw in bullets(sec):
        events = ([(m.start(), "cite", m) for m in CITE.finditer(raw)]
                  + [(m.start(), "quote", m) for m in QUOTE.finditer(raw)])
        events.sort(key=lambda e: e[0])
        current: re.Match | None = None
        pairs: list[tuple[re.Match, str]] = []
        for _, kind, m in events:
            if kind == "cite":
                current = m
            elif current is not None:
                g = next(g for g in m.groups() if g is not None)
                if " " in g:  # a phrase, not a term mention
                    pairs.append((current, normalize(g)))
        decline = bool(DECLINE.search(raw))
        cites = [m for _, k, m in events if k == "cite"]
        extra = [int(n) for n in re.findall(r"`?:(\d{1,4})\b`?", raw)]
        for m in cites:
            rel = m.group(1)
            # The quote duty binds the survey corpora only: `archive/`, the
            # registry, and `dev/literature/`. A citation of a live `src/` or
            # `scripts/` file is evidence, and its truth stays review; gating
            # it would over-reach the rule's words.
            if not (rel.startswith("archive/") or rel == "dev/ARCHIVE.md"
                    or rel.startswith("dev/literature/")):
                continue
            fp = resolve(rel)
            if fp is None:
                continue
            frozen = not rel.startswith("dev/literature/")
            rec = files.setdefault(str(fp.relative_to(ROOT)),
                                   {"read": False, "declined": False,
                                    "verified": False, "fails": [],
                                    "frozen": frozen})
            rec["read"] = True
            if decline:
                rec["declined"] = True
        for m, q in pairs:
            rel = m.group(1)
            fp = resolve(rel)
            if fp is None:
                continue
            key = str(fp.relative_to(ROOT))
            if key not in files:
                continue
            start = int(m.group(2))
            end = int(m.group(3) or m.group(2))
            body = fp.read_text(encoding="utf-8", errors="replace").splitlines()
            if start > len(body) or not (1 <= start):
                files[key]["fails"].append(f"{rel}:{start} cites past the file")
                continue
            extras = [n for n in extra if 1 <= n <= len(body)]

            def joined(a: int, b: int) -> str:
                return normalize(" ".join(body[max(0, a - 1):b]))
            spans = [(start, end)] + [(n, n) for n in extras]
            exact = " § ".join(joined(a, b) for a, b in spans)
            near = " § ".join(joined(max(1, a - WINDOW), b + WINDOW)
                              for a, b in spans)
            frags = quote_fragments(q)

            def hits(text: str) -> bool:
                return bool(frags) and all(
                    f.casefold() in text.casefold() for f in frags)

            if hits(exact):
                files[key]["verified"] = True
                files[key]["fails"] = []
            elif not files[key]["verified"]:
                if hits(near):
                    files[key]["fails"].append(
                        f"{rel}:{start} quotes a line off by a few lines")
                elif any(hits(joined(i, min(i + 40, len(body))))
                         for i in range(1, len(body), 20)):
                    files[key]["fails"].append(
                        f"{rel}:{start} is quoted from elsewhere in the file")
                else:
                    files[key]["fails"].append(
                        f"{rel}:{start} quotes text the file does not hold")
    return files


def findings(brief: Path, report: Path) -> tuple[list[str], list[str]]:
    """(defects, notes) for one return. A defect reads `kind: detail`.

    A byte the decoder cannot read is REPLACED and never raised. This gate runs
    inside an unattended loop, where a `UnicodeDecodeError` on one worker's
    return is a traceback that stops every task, and a replaced byte can only
    make a quote fail to verify, which is the verdict this gate already gives.
    """
    btext = brief.read_text(encoding="utf-8", errors="replace")
    rtext = report.read_text(encoding="utf-8", errors="replace")
    defects: list[str] = []
    notes: list[str] = []
    barch = section_of(btext, "ARCHIVE")
    if not barch.strip():
        return [], ["the brief carries no ARCHIVE section: the program "
                    "injected nothing, so this return has nothing to answer"]

    wants = {m.group(0).rstrip("./")
             for m in ARCHIVE_PATH.finditer(injected(barch))}
    lit_sec = section_of(btext, "LITERATURE")
    lit_wants = {m.group(0).rstrip("./")
                 for m in LIT_PATH.finditer(injected(lit_sec))}
    have = ({m.group(0).rstrip("./") for m in ARCHIVE_PATH.finditer(rtext)}
            | {m.group(0).rstrip("./") for m in LIT_PATH.finditer(rtext)}
            | {t for t in BARE.findall(rtext) if len(t) > 8})

    if not SECTION["ARCHIVE USED"].search(rtext):
        defects.append("no-heading: the return carries no ARCHIVE USED section")
    for w in sorted(wants):
        if not answered(w, have):
            defects.append(f"unanswered: the return never names {w}")
    if lit_wants and not SECTION["LITERATURE USED"].search(rtext):
        defects.append("no-lit-heading: the brief cites dev/literature/ and the "
                       "return carries no LITERATURE USED section")
    elif lit_wants:
        # A missing heading is its own defect kind and already covers the
        # paths; unanswered is the separate duty, reported only when the
        # section exists and an injected path is still nowhere in the return.
        for w in sorted(lit_wants):
            if not answered(w, have):
                defects.append(f"unanswered: the return never names {w}")

    for name in ("ARCHIVE USED", "LITERATURE USED"):
        sec = section_of(rtext, name)
        if not sec:
            continue
        for rel, rec in audit_quotes(sec).items():
            if rec["declined"] or rec["verified"]:
                continue
            # A live literature file drifts, so a mismatch there is counted and
            # never failed; a missing quote is not drift.
            if rec["fails"] and not rec["frozen"]:
                notes.append(f"quote mismatch on live file {rel}: "
                             f"{rec['fails'][0]}")
                continue
            if rec["fails"]:
                defects.append(f"quote: {rec['fails'][0]}")
            elif rec["read"]:
                defects.append(f"no-quote: {rel} is named as read with no "
                               f"line quoted at a cited line")
    return defects, notes


def brief_of(task: Path) -> Path | None:
    found = [p for p in sorted(task.glob("*.md"))
             if not p.name.endswith(".lagda.md") and agents_tree.is_brief(p)]
    return found[0] if found else None


def report_of(task: Path) -> Path | None:
    """The task's own return: the report named for the task, else `REPORT.md`,
    else the single report. A review companion is another dispatch's return and
    is not judged here."""
    exact = [p for p in task.glob("*.md")
             if p.stem.lower() == f"{task.name.lower()}-report"]
    if exact:
        return exact[0]
    rep = list(task.glob("REPORT.md"))
    if rep:
        return rep[0]
    found = [p for p in sorted(task.glob("*.md")) if agents_tree.is_report(p)]
    return found[0] if found else None


def judge(brief: Path, report: Path, label: str, verbose: bool) -> int:
    defects, notes = findings(brief, report)
    if defects:
        print(f"check-survey-quotes: {label} FAILS the survey duty:",
              file=sys.stderr)
        for d in defects:
            print(f"  {d}", file=sys.stderr)
        print("", file=sys.stderr)
        print("A return names every path the program injected, and quotes one "
              "line read per\nfile: the quote must occur AT the cited line in "
              "the cited file. A written\ndecline is compliance.",
              file=sys.stderr)
        return 1
    if verbose:
        for n in notes:
            print(f"  note {label}: {n}")
    print(f"check-survey-quotes: {label} clean "
          f"({len(notes)} note(s), 0 defect(s))")
    return 0


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description="the survey verification, 7.4")
    parser.add_argument("code", nargs="?", help="the task code, LJ-1.383")
    parser.add_argument("--brief", metavar="PATH")
    parser.add_argument("--report", metavar="PATH")
    parser.add_argument("--all", action="store_true",
                        help="a SURVEY over every task pair, never the gate: "
                             "the frozen records fail it by construction")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args(argv[1:])

    if args.all:
        bad = 0
        checked = 0
        for d in agents_tree.task_dirs(include_archive=False):
            brief, report = brief_of(d), report_of(d)
            if brief is None or report is None:
                continue
            checked += 1
            defects, _ = findings(brief, report)
            if defects:
                bad += 1
                if args.verbose:
                    judge(brief, report, d.name, args.verbose)
        print(f"check-survey-quotes: swept {checked} task(s), {bad} fail")
        return 1 if bad else 0

    if args.brief or args.report:
        if not (args.brief and args.report):
            print("check-survey-quotes: give BOTH --brief and --report",
                  file=sys.stderr)
            return 2
        brief, report = Path(args.brief), Path(args.report)
        if not brief.is_file() or not report.is_file():
            print("check-survey-quotes: a named file does not exist",
                  file=sys.stderr)
            return 2
        return judge(brief, report, brief.parent.name, args.verbose)

    if not args.code:
        parser.print_usage(sys.stderr)
        return 2
    task = agents_tree.task_dir(args.code)
    if task is None:
        print(f"check-survey-quotes: no task directory for {args.code}",
              file=sys.stderr)
        return 2
    brief, report = brief_of(task), report_of(task)
    if brief is None:
        print(f"check-survey-quotes: {task.name} has no brief", file=sys.stderr)
        return 2
    if report is None:
        print(f"check-survey-quotes: {task.name} has no report", file=sys.stderr)
        return 2
    return judge(brief, report, task.name, args.verbose)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
