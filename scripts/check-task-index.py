#!/usr/bin/env python3
"""Fail any dispatched-task code that does not occupy exactly one short row.

WHY THIS EXISTS. Dispatched tasks were numbered `T1` to `T110` in briefs,
commits, reports and prose with no registration and no index, and the one
place that tried to carry their verdicts, the `[L3.32]` row of the master
table, grew to a 12,633-token cell. `[T108]` moved the episode content out;
`[T111]` amends the coding rules (§6.0 rules 7 and 8) and builds the index.
This checker is the machine half of those rules: every code cited anywhere in
`dev/`, `_build/briefs/` or the git log must have exactly one row in the task
index in `dev/PLAN.md` section 11, and no row may exceed the 200-character
cap. A task whose verdict paragraph sneaks back into its row fails the gate
on length, which is the regression the cap exists to stop.

WHAT IT CHECKS. It extracts codes from bracket-enclosed tokens only:
`[L3.32-T101]` (full form) and `[T101]` (the short form used in prose). It
does NOT extract bare `T101`, which is how the trap is avoided: a first
draft of the rule-id checker flagged `T-function`, `I-ideal` and `D-bucket`,
ordinary English with a capital, and `T<n>` is even more collision-prone.
Requiring the brackets means every hit is a true positive in this tree.

WHAT IT DOES NOT DO. It cannot tell you a row's verdict is right, only that
the code has a row and the row is short. Citation is not application, the
same limit `[L3.32-T105]` established for rule IDs.

USAGE
    python3 scripts/check-task-index.py

Exit status: 0 clean, 1 defect found, 2 environment failure.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PLAN = ROOT / "dev" / "PLAN.md"
BRIEFS = ROOT / "_build" / "briefs"

SECTION = "### Task index"
CAP = 200

# Brackets are load-bearing: without them `T88` collides with prose. The
# full form is unambiguous; the short form is the bracket citation `[T88]`
# used everywhere in dev/ and the briefs.
# TWO SERIES since 2026-08-09. The live goal is `LJ1`, the two-tower bridge
# route. The retired `L3.32` series is archived WHOLE to archive/dev/TASKS-archived.md
# and its citations still resolve: 264 rows of measured dispatch history are
# cited across JOURNAL, the memos, the briefs and the git history, and the
# owner's archive-survey mechanism requires a new brief to read them. A number
# is never reused in either series.
GOAL = "LJ"
ARCHIVED_GOAL = "L3.32"
ARCHIVED_INDEX = ROOT / "archive" / "dev" / "TASKS-archived.md"
FULL = re.compile(r"\[(?:LJ-(\d+)\.(\d+)|L3\.32-T(\d+))\]")
SHORT = re.compile(r"\[T(\d+)\]")
ROW = re.compile(r"^\| ((?:LJ-(?:\d+)\.(?:\d+))|(?:L3\.32-T\d+)) \|")

# dev/ holds .md prose and .toml data (ledger, glossary, rules). Nothing else
# under dev/ is text worth scanning; `.DS_Store` is binary.
TEXT_SUFFIXES = {".md", ".toml"}


def extract_codes(text: str) -> set[int]:
    """Every dispatched-task NUMBER cited in a corpus, full or short form.

    The number is the key, not the series. The short form `[T101]` cannot say
    which series it means, and the whole existing corpus uses it for the
    retired one, so a number resolves if EITHER index carries it. The two
    series never reuse a number, which is what makes that safe.
    """
    codes = set()
    for phase, step, old in FULL.findall(text):
        codes.add(f"LJ-{phase}.{step}" if phase else f"T{old}")
    codes |= {f"T{n}" for n in SHORT.findall(text)}
    return codes


def index_rows(plan_text: str) -> list[tuple[int, str]]:
    """All `(code, row line)` pairs in PLAN's task index section.

    Only the `### Task index` section is read, so a stray `| L3.32-T... |`
    row anywhere else in the document is not mistaken for an index row.
    """
    m = re.search(rf"^{re.escape(SECTION)}.*?^(?=### |## )", plan_text,
                  re.S | re.M)
    block = m.group(0) if m else ""
    # The retired series lives in its own file, and its rows count as rows:
    # a citation of an archived task must still resolve.
    if ARCHIVED_INDEX.exists():
        block += ARCHIVED_INDEX.read_text(encoding="utf-8")
    # Keyed by the FULL code, not the number. The two series share numbers by
    # design (neither reuses one WITHIN itself), so LJ-1.1 and L3.32-T1 are
    # different rows and a number-keyed dedup would call them a duplicate.
    rows = []
    for line in re.findall(r"^\| (?:LJ-\d+\.\d+|L3\.32-T\d+) \|.*$", block, re.M):
        code = ROW.match(line).group(1)
        key = code if code.startswith("LJ-") else "T" + code.split("-T")[1]
        rows.append((code, key, line))
    return rows


def check_index(plan_text: str, sources_text: str) -> tuple[list[str], int, int]:
    """Enforce one row per cited code and the row-length cap.

    Returns (errors, number of distinct cited codes, number of distinct rows).
    An empty error list is a pass.
    """
    errors: list[str] = []
    rows = index_rows(plan_text)
    if not rows:
        errors.append(f"no task index section (`{SECTION}`) in {PLAN}")
    seen: dict[str, list[str]] = {}
    numbers: set[str] = set()
    for code, key, line in rows:
        seen.setdefault(code, []).append(line)
        numbers.add(key)
    for code, lines in sorted(seen.items()):
        if len(lines) > 1:
            errors.append(
                f"duplicate index row: task {code} appears {len(lines)} times")
    cited = extract_codes(sources_text)
    for code in sorted(cited):
        if code not in numbers:
            errors.append(
                f"no index row: task {code} is cited in dev/, briefs or git log")
    for code, lines in sorted(seen.items()):
        for line in lines:
            length = len(line.rstrip())
            if length > CAP:
                errors.append(
                    f"row over cap: {code} is {length} characters "
                    f"(cap {CAP}): {line}")
    return errors, len(cited), len(seen)


def scanned_texts() -> str:
    """All scanned sources: dev/ files, briefs, and the git log."""
    texts = []
    for path in sorted(ROOT.joinpath("dev").rglob("*")):
        if path.is_file() and path.suffix in TEXT_SUFFIXES:
            texts.append(path.read_text(encoding="utf-8", errors="replace"))
    for path in sorted(BRIEFS.glob("*.md")):
        texts.append(path.read_text(encoding="utf-8", errors="replace"))
    log = subprocess.run(["git", "log", "--oneline", "--all"], cwd=ROOT,
                         capture_output=True, text=True)
    if log.returncode != 0:
        raise RuntimeError(f"git log failed: {log.stderr.strip()}")
    texts.append(log.stdout)
    return "\n".join(texts)


def main() -> int:
    try:
        plan_text = PLAN.read_text(encoding="utf-8")
        sources_text = scanned_texts()
    except (OSError, RuntimeError) as exc:
        print(f"check-task-index: {exc}")
        return 2
    errors, cited, rows = check_index(plan_text, sources_text)
    if not errors:
        print(f"task index OK: {cited} cited codes, {rows} unique rows, "
              f"all within {CAP} characters")
        return 0
    for error in errors:
        print(f"FAIL: {error}")
    print(f"{len(errors)} defect(s)")
    return 1


if __name__ == "__main__":
    sys.exit(main())
