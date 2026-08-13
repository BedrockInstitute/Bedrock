#!/usr/bin/env python3
"""Never-commit checker: probe files and generated files must not enter the repository.

Two standing rules from AGENTS.md's Never list, both of which have already been broken once:

- **Probes are never committed** (dev/LESSONS.md D-1's lifecycle). A probe prices what one
  setting costs and is then thrown away; the verdict lives in a report under agents/reports/, not in
  the tree. On 2026-08-04 a single `git add -A src/` committed 13 probe files, 3,274 lines,
  which had to be untracked afterwards.
- **Generated files are never committed**: anything under _build/, and the woven mono-lingual
  .lagda.md copies that `make gen` produces.

.gitignore already covers both, which is why this script exists rather than not existing:
an ignore rule is a default, not a gate. `git add -f` walks straight past it, a pattern that
does not match a new naming shape silently stops covering it, and neither case produces any
signal at all. This script is the gate. It runs in two places:

  check-probes.py --check      every TRACKED file; this is what `make check` runs, and it
                               catches anything that got in historically or past a bypass
  check-probes.py --staged     the STAGED files only; this is what the pre-commit hook runs,
                               and it is what stops the commit before it happens

The ONE exemption is archive/probes/, ruled by the owner on 2026-08-13 (archive/README.md:16-29).
A probe changes species when a document points INTO it at a file:line: it stops being a
throwaway miniature and becomes the evidence for a checkable claim. src/ is not weakened.

It also carries the other half of D-1, the one an ignore rule cannot express: a probe is
THROWN AWAY once its verdict is recorded. Untracked probes accumulate in src/ and are then
mistaken for committed ones, which is what prompted this tool.

  check-probes.py --gate               FAIL when a sweepable probe waits in src/; make check
  check-probes.py --stale              give every probe under src/ one of four verdicts
  check-probes.py --sweep              archive what is archivable, delete what is deletable
  check-probes.py --stale --archive    move the EVIDENCE and NAMED groups to archive/probes/
  check-probes.py --stale --delete     delete the ORPHAN group past the deletion floor

**THE TRIGGER.** A probe may be swept when its own task is closed AND no LIVE task needs it.
Both halves are read off files on disk. [LJ-1.138] replaced the old clock, which was the
file's mtime, because mtime is a PROXY for "a task is live" and it failed in both directions:
a probe written at the start of a three-hour task aged out while the agent still needed it,
and a finished task's probe stayed protected for six hours after it was dead. On 2026-08-13
the tool called all 14 probes in src/ FRESH ("an agent may still be writing it") while all 14
tasks were closed with their reports written.

**HOW A TOOL KNOWS A TASK IS LIVE.** Three tests, and a probe is HELD when ANY of them fires,
so every test can only ADD a hold and none can release one:

1. **The task index says so.** dev/PLAN.md section 11 carries one row per dispatched code
   (PLAN section 6.0 rules 6 to 8, gated by scripts/check-task-index.py), and the row is
   written BEFORE the work starts. A verdict cell of `DISPATCHED` or `planned` is a live task.
2. **A live task's brief names the probe**, directly or through one hop: the brief names a
   document, and that document names the probe. This is what holds src/ProbeLJ1134A.agda,
   whose own task [LJ-1.134] is closed while [LJ-1.136] reads it.
3. **A brief exists for the code and NO report file exists.** A MISSING report proves the task
   is not finished.

**"THE REPORT EXISTS" NEVER CLOSES A TASK, and C-22 is the reason.** C-22 orders every agent
to write its deliverable as a skeleton FIRST and fill it as answers land, so a running task's
report file exists from its first minute. MEASURED on 2026-08-13:
agents/reports/lj-1.136-report.md was 39,948 bytes while [LJ-1.136] was still reading.
Test 3 is therefore a one-way signal, a widener and never a closer.

The four verdicts, in the order the tests run:

- **HELD**: a live task needs it. Never touched for any reason. A live agent's probe file must
  not be pulled out from under it; two agents were killed on 2026-08-05 by exactly that class
  of carelessness.
- **EVIDENCE**: some document points INTO the file, by a line number (`ProbeX.agda:143`) or by
  prose that sends the reader there ("in full", "diff against", "verbatim"). Such a citation
  resolves against the file and against nothing else. This group is ARCHIVED, never deleted.
- **NAMED**: a document names the file but nothing points into it. The report probably holds
  the whole verdict, because a verdict is a sentence and copies into prose losslessly.
  **This group is ARCHIVED and never deleted**, ruled by the owner on 2026-08-13. The reason is
  measured: [LJ-1.133] read a random sample of eight and two of them had reports that sent the
  reader into the file with prose the regex above was written from. **A regex fitted to its own
  counterexamples cannot be trusted for recall, so the test cannot separate NAMED from EVIDENCE.
  When a test cannot separate two classes reliably, take the recoverable side**: archiving costs
  disk and reverses, while a deletion and a dangling pointer do not.
- **ORPHAN**: nothing anywhere names it. The verdict D-1 requires was never recorded, so there
  is no verdict to protect and nothing is lost. This group is deletable, but only after the
  DELETION FLOOR below.

**THE DELETION FLOOR, and it is NOT the old freshness rule.** An ORPHAN younger than
DELETE_FLOOR_HOURS is reported and kept. mtime is used here in the opposite way: the old rule
made mtime the SOLE protection, so its expiry RELEASED a live agent's file. Here three
task-derived holds do the protecting, and mtime only DELAYS the one irreversible operation. Its
expiry releases nothing that a hold protects. That is what closes the residual hole: an agent
who writes src/ProbeFoo.agda under a task nobody registered gets no hold from any of the three
tests, and the floor keeps the file until a human looks.

**EVIDENCE and NAMED therefore share a destination and differ only in the strength of the
citation.** The distinction is kept because `--index` records it per file: a reader of
archive/probes/README.md can see which files a document points into and which merely have a
name in a report.

**Why NAMED is the honest limit.** A report is the evidence for a VERDICT; a probe carries a
TERM. A verdict ("GREEN, 2.88 s, 26 lines, WALL at 65 s") survives in prose. A term does not:
`agents/reports/lj-1.118-report.md:68-81` gives the location and the line count of a 49-line
proof at `src/ProbeLJ1118A.agda:72-130` and does not carry the proof. Only reading the report
settles which kind a given probe is, and no checker can read a report.

Exit status: 0 clean, 1 violations found, 2 usage error.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


#: The ONE directory where a probe may be tracked. Owner's ruling, 2026-08-13, recorded at
#: archive/README.md:16-29. A probe changes species when a document points INTO it at a
#: file:line: it stops being a throwaway miniature and becomes the evidence for a checkable
#: claim, and a claim this project cannot check is a claim it does not make. The exemption is
#: this prefix and nothing else, so `src/` stays absolutely protected; that rule was bought on
#: 2026-08-04 with 13 committed probe files and it is not weakened here.
ARCHIVED_PROBES = "archive/probes/"


def classify(path: str) -> str | None:
    """Return the rule a path breaks, or None. Matching is on shape, not on an ignore list."""
    p = Path(path)
    # Probe files: the doctrine names src/Probe*.agda, but a probe is a probe wherever it is
    # written and whatever extension it carries, so match the basename shape anywhere. The
    # single exemption is archive/probes/, where a probe is no longer in flight.
    if not path.startswith(ARCHIVED_PROBES):
        if p.name.startswith("Probe") and p.suffix in {".agda", ".agdai", ".md"}:
            return "probe file (D-1: probes are never committed; the verdict goes in a report under agents/reports/)"
        if p.name.startswith("Probe") and p.name.endswith(".lagda.md"):
            return "probe file (D-1: probes are never committed)"
    # An interface file is a build output and never belongs in the repository, archived or not.
    elif p.suffix == ".agdai":
        return "compiled interface (a build output, never committed, not even under archive/probes/)"
    # Generated: the build tree, and the woven mono-lingual copies.
    if path.startswith("_build/"):
        return "generated file under _build/ (never committed)"
    if "/woven/" in path or path.startswith("woven/"):
        return "woven mono-lingual copy (a `make gen` output, never committed)"
    return None


def tracked() -> list[str]:
    return subprocess.run(
        ["git", "ls-files"], cwd=ROOT, capture_output=True, text=True, check=True
    ).stdout.split("\n")


def staged() -> list[str]:
    return subprocess.run(
        ["git", "diff", "--cached", "--name-only", "--diff-filter=ACM"],
        cwd=ROOT, capture_output=True, text=True, check=True,
    ).stdout.split("\n")


#: How long an ORPHAN waits before `--delete` may take it. This is a FLOOR under the one
#: irreversible operation, not a hold: the three live-task tests do the protecting, and this
#: clock only delays a deletion. The old rule made the same clock the SOLE protection at 6
#: hours, so its expiry released a live agent's file; a three-hour task outlived it.
DELETE_FLOOR_HOURS = 24.0

#: dev/PLAN.md section 11's task index. One row per dispatched code, written BEFORE the work
#: starts (PLAN section 6.0 rule 6), gated for one-row-per-code by scripts/check-task-index.py.
TASK_INDEX_SECTION = "### Task index"
TASK_ROW = re.compile(
    r"^\| (LJ-\d+\.\d+[a-z]*(?:-R)?|L3\.32-T\d+) \|[^|]*\|([^|]*)\|", re.M)

#: A verdict cell that means the task has NOT delivered. Everything else in that column is a
#: verdict, and a verdict closes the task. Both words are the live vocabulary of the index
#: today: MEASURED 2026-08-13, 8 rows read `DISPATCHED` and 15 read `planned`.
LIVE_STATUS = re.compile(r"\b(DISPATCHED|planned|QUEUED|RUNNING|IN PROGRESS)\b", re.I)

#: A file under agents/briefs/ or agents/reports/ carries its task code in its NAME. Both
#: series resolve: `LJ-1.136.md` and `lj-1.136-report.md` are one task, and `t26-pairkit-brief.md`
#: and `l3.32-t26-report.md` are another. Pairing on the CODE rather than on the filename stem
#: is what makes the two nameable: stem pairing read 81 briefs as unreported, code pairing
#: reads 8. MEASURED 2026-08-13.
FILE_CODE_LJ = re.compile(r"^lj-(\d+)\.(\d+[a-z]*(?:-r)?)\b")
FILE_CODE_T = re.compile(r"^(?:l3\.32-)?t(\d+)\b")

#: A probe carries its task code in its own name, which is how build-manifest's `working` class
#: says a temporary file names its owner. The digit split is AMBIGUOUS: `ProbeLJ1134A` reads as
#: LJ-1.134, LJ-11.34 or LJ-113.4, and no rule in the tree settles it. Every split is generated
#: and ANY of them being live holds the file, because over-holding costs disk and under-holding
#: kills an agent.
STEM_CODE_LJ = re.compile(r"^Probe(?:LJ)(\d+)[A-Za-z0-9]*$")
STEM_CODE_T = re.compile(r"^ProbeT(\d+)[A-Za-z0-9]*$")

#: A document path written inside a brief. A live brief that sends its agent into a report
#: holds every probe that report POINTS INTO: one hop, and one hop is enough for the case this
#: rule was built on. agents/briefs/LJ-1.136.md:152 sends [LJ-1.136] into
#: agents/reports/lj-1.134-report.md, which cites src/ProbeLJ1134A.agda at 17 line numbers.
#:
#: THE HOP IS DELIBERATELY NARROW, and the width was measured on 2026-08-13 over all 255
#: probes in the tree, src/ and archive/probes/ together:
#:
#:   hop into agents/ and dev/, a NAME is enough   69 of 255 held
#:   hop into agents/ only, a NAME is enough       57 of 255 held
#:   hop into agents/ only, must POINT IN          23 of 255 held   <- this rule
#:   no hop at all                                  2 of 255 held
#:
#: The wide forms re-create the backlog this task exists to end: a live brief's ARCHIVE
#: section names a prior report, and that report names every probe its task ever ran, so a
#: quarter of the corpus never leaves src/. dev/ is excluded for a second reason: a dev/
#: document is a PERMANENT binding rule, not evidence that some task is running, and a probe it
#: names is already EVIDENCE and already archived where the citation still resolves.
HOP_INTO = ("agents/reports/", "agents/briefs/")
DOC_PATH = re.compile(r"\b((?:agents/reports/(?:archive/)?|agents/briefs/)"
                      r"[A-Za-z0-9._-]+\.md)\b")


def _file_code(name: str) -> str | None:
    """The task code a brief or report filename carries, or None."""
    n = name.lower()
    m = FILE_CODE_LJ.match(n)
    if m:
        return f"LJ-{int(m.group(1))}.{m.group(2)}"
    m = FILE_CODE_T.match(n)
    if m:
        return f"T{int(m.group(1))}"
    return None


def stem_codes(stem: str) -> set[str]:
    """Every task code a probe's own name could name. See STEM_CODE_LJ for the ambiguity."""
    out: set[str] = set()
    m = STEM_CODE_LJ.match(stem)
    if m:
        d = m.group(1)
        out |= {f"LJ-{int(d[:i])}.{int(d[i:])}" for i in range(1, len(d))}
    m = STEM_CODE_T.match(stem)
    if m:
        out.add(f"T{int(m.group(1))}")
    return out


def live_tasks() -> dict[str, str]:
    """Every task code that is LIVE, mapped to the evidence on disk that says so.

    Two independent tests, unioned. A union is the whole point: each test can only ADD a
    hold, so a test that goes stale over-holds and never releases a running agent's file.
    """
    live: dict[str, str] = {}

    plan = (ROOT / "dev" / "PLAN.md")
    if plan.exists():
        text = plan.read_text(encoding="utf-8", errors="ignore")
        m = re.search(rf"^{re.escape(TASK_INDEX_SECTION)}.*?^(?=### |## )", text, re.S | re.M)
        block = m.group(0) if m else ""
        offset = text[:m.start()].count("\n") + 1 if m else 0
        for row in TASK_ROW.finditer(block):
            if LIVE_STATUS.search(row.group(2)):
                line = offset + block[:row.start()].count("\n") + 1
                live.setdefault(row.group(1),
                                f"dev/PLAN.md:{line} reads `{row.group(2).strip()}`")

    briefs: dict[str, str] = {}
    for b in sorted((ROOT / "agents" / "briefs").glob("*.md")):
        code = _file_code(b.name)
        if code:
            briefs.setdefault(code, f"agents/briefs/{b.name}")
    reported = set()
    for d in ("agents/reports", "agents/reports/archive"):
        for r in (ROOT / d).glob("*.md"):
            code = _file_code(r.name)
            if code:
                reported.add(code)
    for code, where in briefs.items():
        # A MISSING report proves the task is unfinished. The converse is FALSE and must never
        # be used: C-22 makes every running agent write its report file in its first minute.
        if code not in reported:
            live.setdefault(code, f"{where} exists and no report names {code}")
    return live


def held_probes(corpus: dict[str, list[str]]) -> dict[str, str]:
    """Probe stem -> why a LIVE task needs it. Three tests, and any one of them holds."""
    live = live_tasks()
    if not live:
        return {}

    # A live task's own brief, where a bare NAME is enough, and the documents that brief sends
    # its agent into, where the citation must POINT INTO the file. See HOP_INTO for the widths
    # that were measured and rejected.
    direct: dict[str, str] = {}
    hopped: dict[str, str] = {}
    for code in live:
        for b in sorted((ROOT / "agents" / "briefs").glob("*.md")):
            if _file_code(b.name) != code:
                continue
            key = f"agents/briefs/{b.name}"
            direct.setdefault(key, f"the brief of the live task {code}")
            for path in set(DOC_PATH.findall(b.read_text(encoding="utf-8", errors="ignore"))):
                if path.startswith(HOP_INTO) and (ROOT / path).is_file():
                    hopped.setdefault(
                        path, f"named by {key}, the brief of the live task {code}")

    out: dict[str, str] = {}
    stems = {f.stem for f in (ROOT / "src").glob("Probe*.agda")}
    for stem in stems:
        hit = sorted(stem_codes(stem) & live.keys())
        if hit:
            out[stem] = f"its own task {hit[0]} is live: {live[hit[0]]}"

    def scan(path: str, why: str, points_in_required: bool) -> None:
        lines = corpus.get(path)
        if lines is None:
            lines = (ROOT / path).read_text(encoding="utf-8", errors="ignore").split("\n")
        for i, ln in enumerate(lines, 1):
            if "Probe" not in ln:
                continue
            for stem in stems:
                if stem not in ln or stem in out:
                    continue
                if points_in_required:
                    window = "\n".join(lines[max(0, i - 3):i + 2])
                    if not (re.search(LINE_CITE % re.escape(stem), ln)
                            or POINTS_IN.search(window)):
                        continue
                out[stem] = f"{path}:{i} names it, and that document is {why}"

    for path, why in sorted(direct.items()):
        scan(path, why, points_in_required=False)
    for path, why in sorted(hopped.items()):
        if path not in direct:
            scan(path, why, points_in_required=True)
    return out


#: A citation that points INTO the file: `ProbeX.agda:143`, `src/ProbeX.agda:72-130`,
#: `ProbeX.agda:81,105`. Such a citation resolves against the file and against nothing else.
#: The `.agda` is OPTIONAL, because reports drop it: agents/reports/archive/lj-1.54-report.md:43
#: writes `ProbeLJ154A:61`, and requiring the extension read that file as merely NAMED.
#: The stem is substituted in by probe_verdicts().
LINE_CITE = r"(?:src/)?%s(?:\.agda)?\s*:\s*\d"

#: Prose that sends the reader to the file rather than reporting an outcome. Measured at
#: [LJ-1.133]: 20 of 117 name-only citations carry one of these, and two of them
#: (`agents/reports/archive/lj-1.39-report.md:128` "Diff ... for the exact edit list",
#: `agents/reports/archive/lj-1.31-report.md:121` "in full. It is the adequacy proof model")
#: turned up in a random sample of eight. A name-only citation is therefore NOT proof that the
#: report is self-sufficient, which is why NAMED below is never deleted automatically.
POINTS_IN = re.compile(
    r"\b(in full|diff\b|diffed|exact edit|line[- ]by[- ]line|verbatim|read WHOLE"
    r"|ported from|the model|body of)\b", re.IGNORECASE)

#: Range and brace shorthand for a family of probes: `src/ProbeLJ174A..F.agda`,
#: `src/ProbeDD25F41{A,B,C,D}.agda`. A stem-substring test cannot see the members such a
#: citation names, and the members it cannot see look like orphans. [LJ-1.132] was bitten by
#: the same shape at agents/reports/lj-1.128-report.md:86, where four logs were cited as
#: `-run3.log`, `-run4.log`, `-run5.log`. [LJ-1.133] then measured three more here:
#: ProbeLJ174E, ProbeLJ174P2 and ProbeLJ174P3 read as orphans while
#: agents/reports/archive/lj-1.74-report.md:209 names them. The cure is deliberately blunt.
#: A shorthand puts its WHOLE family beyond ORPHAN, because over-keeping costs disk and
#: under-keeping destroys evidence.
SHORTHAND_BRACE = re.compile(r"(Probe[A-Za-z0-9]*)\{")
SHORTHAND_RANGE = re.compile(r"(Probe[A-Za-z0-9]*)\.\.([A-Za-z0-9]+)")


def _shorthand_bases(corpus: dict[str, list[str]]) -> dict[str, str]:
    """Family prefixes that a range or brace citation names, mapped to where it says so."""
    bases: dict[str, str] = {}
    for path, lines in corpus.items():
        for i, ln in enumerate(lines, 1):
            if "Probe" not in ln:
                continue
            for m in SHORTHAND_BRACE.finditer(ln):
                bases.setdefault(m.group(1), f"{path}:{i}")
            for m in SHORTHAND_RANGE.finditer(ln):
                # `ProbeLJ174P0..P3` names P1 and P2: drop as many trailing characters from the
                # left endpoint as the right endpoint carries, and keep what both share.
                base = m.group(1)[:-len(m.group(2))] or m.group(1)
                bases.setdefault(base, f"{path}:{i}")
    return bases


#: Documents that can point into a probe. Reports and briefs are the frozen record; dev/ holds
#: the binding rules, and dev/LESSONS.md names 21 probes as the provenance of live laws.
CITING_GLOBS = ("agents/reports/*.md", "agents/reports/archive/*.md",
                "agents/briefs/*.md", "dev/*.md", "dev/*.toml",
                "dev/**/*.md", "dev/**/*.toml")

# The four verdicts. HELD is never touched, EVIDENCE and NAMED are archived, and ORPHAN is the
# only deletable group; see the module docstring for the trigger and the deletion floor.
HELD, EVIDENCE, NAMED, ORPHAN = "HELD", "EVIDENCE", "NAMED", "ORPHAN"


def _citing_corpus() -> dict[str, list[str]]:
    """Every document that may cite a probe, as path -> lines."""
    seen: dict[str, list[str]] = {}
    for pattern in CITING_GLOBS:
        for f in ROOT.glob(pattern):
            key = str(f.relative_to(ROOT))
            if f.is_file() and key not in seen:
                seen[key] = f.read_text(encoding="utf-8", errors="ignore").split("\n")
    return seen


def probe_verdicts(_unused: float | None = None):
    """Every probe under src/, with one of the four verdicts and the evidence for it.

    Returns a list of (path, verdict, reason). The order of the tests is the whole design:
    the LIVE-TASK test first, because a live agent's file is never touched for any reason;
    then the points-into test, because that is what makes a probe evidence.
    """
    corpus = _citing_corpus()
    shorthand = _shorthand_bases(corpus)
    held = held_probes(corpus)
    out = []
    for f in sorted((ROOT / "src").glob("Probe*.agda")):
        stem = f.stem
        if stem in held:
            out.append((f, HELD, held[stem]))
            continue
        line_cite = re.compile(LINE_CITE % re.escape(stem))
        named_at, points_at, binding_at = [], [], []
        for path, lines in corpus.items():
            for i, ln in enumerate(lines, 1):
                if stem not in ln:
                    continue
                named_at.append(f"{path}:{i}")
                window = "\n".join(lines[max(0, i - 3):i + 2])
                if line_cite.search(ln) or POINTS_IN.search(window):
                    points_at.append(f"{path}:{i}")
                # A dev/ document is a BINDING rule, not a frozen record. dev/LESSONS.md names
                # 21 probes as the provenance of live laws, and a law whose provenance cannot
                # be opened is a law nobody can check. [LJ-1.132] found the same shape at
                # dev/LESSONS.md:1012, where rule I-2 cited a probe that make clean could take.
                if path.startswith("dev/"):
                    binding_at.append(f"{path}:{i}")
        if points_at or binding_at:
            where = (f"{len(points_at)} citation(s) point INTO the file, first at {points_at[0]}"
                     if points_at else
                     f"the binding document {binding_at[0]} names it as a live rule's provenance")
            out.append((f, EVIDENCE, f"{where}; such a citation resolves against nothing else"))
        elif named_at:
            out.append((f, NAMED, f"named at {named_at[0]} and {len(named_at) - 1} other place(s), "
                                  f"but nothing points into the file"))
        else:
            hit = next((b for b in shorthand if stem.startswith(b) and stem != b), None)
            if hit:
                out.append((f, NAMED, f"named only by the family shorthand `{hit}` at "
                                      f"{shorthand[hit]}; no citation writes the stem out"))
            else:
                out.append((f, ORPHAN, "no report, brief or dev document names it: the verdict "
                                       "D-1 requires was never recorded, so there is none to "
                                       "protect"))
    return out


def _grouped(floor_hours: float):
    """The four groups, with ORPHAN split by the deletion floor."""
    import time
    verdicts = probe_verdicts()
    groups = {v: [(f, why) for f, k, why in verdicts if k == v]
              for v in (HELD, EVIDENCE, NAMED, ORPHAN)}
    now = time.time()
    ripe, waiting = [], []
    for f, why in groups[ORPHAN]:
        age_h = (now - f.stat().st_mtime) / 3600.0
        if age_h >= floor_hours:
            ripe.append((f, f"{why}; {age_h:.1f}h old, past the {floor_hours:.0f}h floor"))
        else:
            waiting.append((f, f"{why}; but only {age_h:.1f}h old, inside the "
                               f"{floor_hours:.0f}h deletion floor"))
    return groups, ripe, waiting


def cmd_stale(delete: bool, archive: bool, floor_hours: float) -> int:
    groups, ripe, waiting = _grouped(floor_hours)

    headings = {
        HELD: "HELD: a LIVE task needs these. Never touched, for any reason",
        EVIDENCE: f"EVIDENCE: a document points into the file. Archive to {ARCHIVED_PROBES}, never delete",
        NAMED: f"NAMED only: nothing points in, but the test cannot prove nothing does. "
               f"Archive to {ARCHIVED_PROBES}; owner's ruling, 2026-08-13",
        ORPHAN: "ORPHAN: nothing names it anywhere and no live task needs it",
    }
    shown = {HELD: groups[HELD], EVIDENCE: groups[EVIDENCE], NAMED: groups[NAMED],
             ORPHAN: ripe + waiting}
    for v in (HELD, EVIDENCE, NAMED, ORPHAN):
        if not shown[v]:
            continue
        print(f"{headings[v]} ({len(shown[v])}):")
        for f, why in shown[v]:
            print(f"  {f.relative_to(ROOT)}\n      {why}")
        print("")

    if archive:
        dest = ROOT / ARCHIVED_PROBES
        dest.mkdir(parents=True, exist_ok=True)
        movable = groups[EVIDENCE] + groups[NAMED]
        for f, _ in movable:
            f.rename(dest / f.name)
            agdai = f.with_suffix(".agdai")
            if agdai.exists():
                agdai.unlink()
        print(f"check-probes: archived {len(movable)} probe(s) to {ARCHIVED_PROBES} "
              f"({len(groups[EVIDENCE])} EVIDENCE, {len(groups[NAMED])} NAMED)")
    if delete:
        for f, _ in ripe:
            f.unlink()
            agdai = f.with_suffix(".agdai")
            if agdai.exists():
                agdai.unlink()
        print(f"check-probes: deleted {len(ripe)} orphan probe(s); {len(waiting)} still "
              f"inside the {floor_hours:.0f}h deletion floor")
    if not (archive or delete):
        print(f"{len(ripe)} orphan(s) deletable with --delete and {len(waiting)} waiting on the "
              f"{floor_hours:.0f}h floor; "
              f"{len(groups[EVIDENCE]) + len(groups[NAMED])} archivable with --archive. "
              f"{len(groups[HELD])} HELD probe(s) are never touched.")
    return 0


def cmd_gate(floor_hours: float) -> int:
    """FAIL when a sweepable probe waits in src/. This is what `make check` runs.

    THRESHOLD ZERO, and the reason is measured. `[LJ-1.133]` found 284 probes in src/ because
    `--stale`, `--archive` and `--delete` had never been run by anything except a human typing
    them. A reminder that does not fail is what produced that backlog. A threshold above zero
    would only set the size of the next one.

    THIS GATE MOVES NO FILE. A gate with a side effect on the working tree is not idempotent,
    its output is not reproducible, and AGENTS.md tells a dispatched agent to leave the tree as
    its report describes it. The guarantee is the red gate, which no commit may pass, and the
    fix is one command.
    """
    groups, ripe, waiting = _grouped(floor_hours)
    backlog = groups[EVIDENCE] + groups[NAMED] + ripe
    if not backlog:
        print(f"check-probes: no probe backlog ({len(groups[HELD])} HELD by a live task, "
              f"{len(waiting)} orphan(s) inside the {floor_hours:.0f}h deletion floor)")
        return 0
    print(f"check-probes: {len(backlog)} probe(s) in src/ are finished and must be swept:",
          file=sys.stderr)
    for f, why in backlog:
        print(f"  {f.relative_to(ROOT)}\n      {why}", file=sys.stderr)
    print("\nD-1: a probe is thrown away once its verdict is recorded. Sweep them:",
          file=sys.stderr)
    print("    make probes-sweep", file=sys.stderr)
    print(f"Nothing HELD by a live task is touched ({len(groups[HELD])} today).", file=sys.stderr)
    return 1


INDEX_BEGIN = "<!-- BEGIN GENERATED INDEX: scripts/check-probes.py --index -->"
INDEX_END = "<!-- END GENERATED INDEX -->"


def cmd_index() -> int:
    """Regenerate the evidence table in archive/probes/README.md from the directory itself.

    The table is DERIVED, never transcribed. Once a probe leaves src/, probe_verdicts() stops
    seeing it, so the citation that justified keeping it would be lost if a hand-written table
    were the only record. This rebuilds it from the corpus on demand.
    """
    corpus = _citing_corpus()
    rows = []
    for f in sorted((ROOT / ARCHIVED_PROBES).glob("*.agda")):
        stem = f.stem
        line_cite = re.compile(LINE_CITE % re.escape(stem))
        best = None
        for path, lines in corpus.items():
            for i, ln in enumerate(lines, 1):
                if stem not in ln:
                    continue
                rank = 0 if path.startswith("dev/") else (1 if line_cite.search(ln) else 2)
                if best is None or rank < best[0]:
                    best = (rank, f"{path}:{i}")
        why = {0: "binding rule", 1: "line citation", 2: "named"}
        rows.append(f"| `{f.name}` | {best[1] if best else 'NONE'} | "
                    f"{why[best[0]] if best else 'orphan, review it'} |")

    readme = ROOT / ARCHIVED_PROBES / "README.md"
    text = readme.read_text(encoding="utf-8")
    table = ("| File | Strongest citation | Kind |\n|---|---|---|\n" + "\n".join(rows))
    head, _, rest = text.partition(INDEX_BEGIN)
    _, _, tail = rest.partition(INDEX_END)
    readme.write_text(f"{head}{INDEX_BEGIN}\n\n{table}\n\n{INDEX_END}{tail}", encoding="utf-8")
    print(f"check-probes: wrote {len(rows)} row(s) into {readme.relative_to(ROOT)}")
    return 0


#: A flag that only makes sense under a mode that reads it. `--archive` alone used to fall
#: through to the default check, do nothing, and print "check-probes: clean": a command that
#: no-ops while printing a success line is worse than one that errors, and it cost [LJ-1.138]'s
#: orchestrator an hour on 2026-08-13. Every such pair is now a usage error.
MODIFIER_MODES = {"--delete": {"stale", "sweep"},
                  "--archive": {"stale", "sweep"},
                  "--floor-hours": {"stale", "sweep", "gate"}}


def main(argv: list[str]) -> int:
    mode = None
    delete = False
    archive = False
    floor = DELETE_FLOOR_HOURS
    seen: list[str] = []
    args = argv[1:]
    for i, arg in enumerate(args):
        if arg in ("--staged", "--check", "--stale", "--index", "--gate", "--sweep"):
            if mode is not None:
                print(f"check-probes: `{arg}` and `--{mode}` are two modes; pass one.",
                      file=sys.stderr)
                return 2
            mode = arg[2:]
        elif arg in ("--delete", "--archive"):
            seen.append(arg)
            delete = delete or arg == "--delete"
            archive = archive or arg == "--archive"
        elif arg == "--floor-hours":
            seen.append(arg)
            if i + 1 >= len(args):
                print("check-probes: --floor-hours needs a number.", file=sys.stderr)
                return 2
            floor = float(args[i + 1])
        elif i > 0 and args[i - 1] == "--floor-hours":
            pass
        else:
            print(__doc__, file=sys.stderr)
            return 2

    # An ineffective flag combination FAILS. It never falls through to another mode's success
    # line. See MODIFIER_MODES.
    effective = mode or "check"
    for flag in seen:
        if effective not in MODIFIER_MODES[flag]:
            wants = " or ".join(f"--{m}" for m in sorted(MODIFIER_MODES[flag]))
            print(f"check-probes: `{flag}` does nothing under `--{effective}`. "
                  f"It needs {wants}.", file=sys.stderr)
            return 2

    if mode == "index":
        return cmd_index()
    if mode == "gate":
        return cmd_gate(floor)
    if mode == "sweep":
        return cmd_stale(True, True, floor)
    if mode == "stale":
        return cmd_stale(delete, archive, floor)
    mode = mode or "check"

    files = [f for f in (staged() if mode == "staged" else tracked()) if f]
    bad = [(f, why) for f in files if (why := classify(f))]

    if bad:
        where = "staged for commit" if mode == "staged" else "tracked in the repository"
        print(f"check-probes: {len(bad)} file(s) {where} that must never be committed:",
              file=sys.stderr)
        for f, why in bad:
            print(f"  {f}\n      {why}", file=sys.stderr)
        print("", file=sys.stderr)
        if mode == "staged":
            print("Unstage them and commit the rest:", file=sys.stderr)
            print(f"    git restore --staged {' '.join(f for f, _ in bad)}", file=sys.stderr)
            print("Never use `git add -A src/` while probes are on disk; stage explicit paths.",
                  file=sys.stderr)
        else:
            print("Untrack them, keeping the files on disk:", file=sys.stderr)
            print(f"    git rm --cached {' '.join(f for f, _ in bad)}", file=sys.stderr)
        return 1

    scope = "staged" if mode == "staged" else f"{len(files)} tracked"
    print(f"check-probes: clean ({scope} files, no probe and no generated file)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
