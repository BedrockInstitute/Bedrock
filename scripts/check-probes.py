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

  check-probes.py --stale              give every probe under src/ one of four verdicts
  check-probes.py --stale --delete     delete the ORPHAN group
  check-probes.py --stale --archive    move the EVIDENCE group to archive/probes/

The four verdicts, in the order the tests run:

- **FRESH**: modified inside the freshness window (default 6 hours). Never touched for any
  reason. A live agent's probe file must not be pulled out from under it; two agents were
  killed on 2026-08-05 by exactly that class of carelessness.
- **EVIDENCE**: some document points INTO the file, by a line number (`ProbeX.agda:143`) or by
  prose that sends the reader there ("in full", "diff against", "verbatim"). Such a citation
  resolves against the file and against nothing else. This group is ARCHIVED, never deleted.
- **NAMED**: a document names the file but nothing points into it. The report probably holds
  the whole verdict, because a verdict is a sentence and copies into prose losslessly.
  **This group is never deleted automatically**, and the reason is measured: [LJ-1.133] read a
  random sample of eight and two of them had reports that sent the reader into the file with
  prose the regex above was written from. A regex that was fitted to its own counterexamples
  cannot be trusted for recall. A human reads the report and decides.
- **ORPHAN**: nothing anywhere names it. The verdict D-1 requires was never recorded, so there
  is no verdict to protect and nothing is lost. This group is deletable.

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


FRESH_HOURS = 6.0

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

# The four verdicts. Only ORPHAN is deletable and only EVIDENCE is archivable; see the module
# docstring for why NAMED is neither.
FRESH, EVIDENCE, NAMED, ORPHAN = "FRESH", "EVIDENCE", "NAMED", "ORPHAN"


def _citing_corpus() -> dict[str, list[str]]:
    """Every document that may cite a probe, as path -> lines."""
    seen: dict[str, list[str]] = {}
    for pattern in CITING_GLOBS:
        for f in ROOT.glob(pattern):
            key = str(f.relative_to(ROOT))
            if f.is_file() and key not in seen:
                seen[key] = f.read_text(encoding="utf-8", errors="ignore").split("\n")
    return seen


def probe_verdicts(fresh_hours: float = FRESH_HOURS):
    """Every probe under src/, with one of the four verdicts and the evidence for it.

    Returns a list of (path, verdict, reason). The order of the tests is the whole design:
    freshness first, because a live agent's file is never touched for any reason; then the
    points-into test, because that is what makes a probe evidence.
    """
    import time
    corpus = _citing_corpus()
    shorthand = _shorthand_bases(corpus)
    out = []
    for f in sorted((ROOT / "src").glob("Probe*.agda")):
        stem = f.stem
        age_h = (time.time() - f.stat().st_mtime) / 3600.0
        if age_h < fresh_hours:
            out.append((f, FRESH, f"modified {age_h:.1f}h ago, inside the {fresh_hours:.0f}h "
                                  f"freshness window: an agent may still be writing it"))
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


def cmd_stale(delete: bool, archive: bool, fresh_hours: float) -> int:
    verdicts = probe_verdicts(fresh_hours)
    groups = {v: [(f, why) for f, k, why in verdicts if k == v]
              for v in (FRESH, EVIDENCE, NAMED, ORPHAN)}

    headings = {
        FRESH: "FRESH, untouchable: an agent may still be writing these",
        EVIDENCE: f"EVIDENCE: a document points into the file. Archive to {ARCHIVED_PROBES}, never delete",
        NAMED: "NAMED only: the report may hold the whole verdict. A HUMAN must read the report",
        ORPHAN: "ORPHAN: nothing names it anywhere. Safe to delete",
    }
    for v in (FRESH, EVIDENCE, NAMED, ORPHAN):
        if not groups[v]:
            continue
        print(f"{headings[v]} ({len(groups[v])}):")
        for f, why in groups[v]:
            print(f"  {f.relative_to(ROOT)}\n      {why}")
        print("")

    if archive:
        dest = ROOT / ARCHIVED_PROBES
        dest.mkdir(parents=True, exist_ok=True)
        for f, _ in groups[EVIDENCE]:
            f.rename(dest / f.name)
            agdai = f.with_suffix(".agdai")
            if agdai.exists():
                agdai.unlink()
        print(f"check-probes: archived {len(groups[EVIDENCE])} probe(s) to {ARCHIVED_PROBES}")
    if delete:
        for f, _ in groups[ORPHAN]:
            f.unlink()
            agdai = f.with_suffix(".agdai")
            if agdai.exists():
                agdai.unlink()
        print(f"check-probes: deleted {len(groups[ORPHAN])} orphan probe(s)")
    if not (archive or delete):
        print(f"{len(groups[ORPHAN])} orphan(s) deletable with --delete; "
              f"{len(groups[EVIDENCE])} archivable with --archive. "
              f"NAMED is never automatic: read the report first.")
    return 0


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


def main(argv: list[str]) -> int:
    mode = "check"
    delete = False
    archive = False
    fresh = FRESH_HOURS
    args = argv[1:]
    for i, arg in enumerate(args):
        if arg == "--staged":
            mode = "staged"
        elif arg == "--check":
            mode = "check"
        elif arg == "--stale":
            mode = "stale"
        elif arg == "--delete":
            delete = True
        elif arg == "--archive":
            archive = True
        elif arg == "--index":
            mode = "index"
        elif arg == "--fresh-hours":
            fresh = float(args[i + 1])
        elif i > 0 and args[i - 1] == "--fresh-hours":
            pass
        else:
            print(__doc__, file=sys.stderr)
            return 2

    if mode == "index":
        return cmd_index()
    if mode == "stale":
        return cmd_stale(delete, archive, fresh)

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
