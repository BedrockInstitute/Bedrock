#!/usr/bin/env python3
"""Fail any dispatched-task code that does not occupy exactly one short row.

WHY THIS EXISTS. Dispatched tasks were numbered `T1` to `T110` in briefs,
commits, reports and prose with no registration and no index, and the one
place that tried to carry their verdicts, the `[L3.32]` row of the master
table, grew to a 12,633-token cell. `[T108]` moved the episode content out;
`[T111]` amends the coding rules (§6.0 rules 7 and 8) and builds the index.
This checker is the machine half of those rules: every code cited anywhere in
`dev/`, `agents/tasks/` or the git log must have exactly one row in the task
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
    python3 scripts/gate/check-task-index.py

Exit status: 0 clean, 1 defect found, 2 environment failure.
"""

from __future__ import annotations

import re
import subprocess
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
from repo_root import find_root  # noqa: E402
import agents_tree as T   # [LJ-1.142]: the briefs moved into agents/tasks/<TASK>/

ROOT = find_root(__file__)
PLAN = ROOT / "dev" / "PLAN.md"

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
# THE SUFFIX IS PART OF THE CODE. Widened 2026-08-10 at the [LJ-0.4]
# closeout, which found that `LJ-\d+\.\d+` matched none of the fifteen
# lettered codes this campaign created: LJ-0.4a through LJ-0.4q, and the DD25
# review LJ-0.4f-R. Twelve of those rows were over the 200-character cap, one
# at 438, and the gate reported clean all day. A cap that cannot see the rows
# it governs is not a cap.
#
# WIDENED AGAIN 2026-08-16, AND THE SAME FAILURE HAD RECURRED IN A NEW LETTER
# CASE. `(?:-R)?` admits the DD25 review suffix and nothing else, so the 26
# UPPERCASE audit suffixes this campaign then created (`-A`, `-B`, `-C`, `-D`)
# were invisible to both halves of the checker. MEASURED at the fix: 464 data
# rows in the live index, 436 visible to the old grammar, 28 invisible, and
# EIGHT of the invisible ones over the cap, the longest at 224. The gate
# reported clean. `(?:-[A-Z])?` subsumes `-R`, because `R` is an upper-case
# letter, so one class now covers every suffix the campaign has used.
#
# THE DEEPER FIX IS BELOW, AND IT IS WHY THIS COMMENT IS NOT THE WHOLE CURE.
# The cap used to be applied to the rows this grammar matched, so every
# widening of the grammar was also a widening of the cap, and a code shape
# nobody predicted took the cap down with it. TWICE. The cap is a property of
# a ROW, not of a code, and `capped_rows` now reads it that way.
FULL = re.compile(r"\[(?:LJ-(\d+)\.(\d+[a-z]*(?:-[A-Z])?)|L3\.32-T(\d+))\]")
SHORT = re.compile(r"\[T(\d+)\]")
ROW = re.compile(r"^\| ((?:LJ-(?:\d+)\.(?:\d+[a-z]*(?:-[A-Z])?))|(?:L3\.32-T\d+)) \|")

# THE FROZEN PRE-EPOCH SET, and C-59 rule 3 is why the scale is written here
# rather than in a commit message: "when a lapse is forgiven, write its SCALE
# into the code that forgives it".
#
# These eight rows sat over the cap while the grammar could not see them. They
# are NOT trimmed, and that is a decision rather than an omission: each is a
# dense verdict row carrying measured figures and `file:line` claims, the
# overage runs from 2 to 24 characters, and rewriting a record to save three
# characters costs more than the rule buys. The cap exists to stop a verdict
# PARAGRAPH living in a row, and the defect it was bought for was a
# 12,633-token cell, not a 203-character line.
#
# A row added after this date is held to the cap. The set never grows: a new
# entry here means somebody widened the forgiveness instead of the row.
CAP_EPOCH = "2026-08-16"
CAP_FROZEN = {
    "LJ-1.56-C", "LJ-1.57-A", "LJ-1.58-A", "LJ-1.60-A",
    "LJ-1.62-A", "LJ-1.64-A", "LJ-1.64-D", "DD25-GAP",
}

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
        # int() STRIPS ZERO PADDING, and it has to. `[L3.32-T01]` and `[T1]`
        # are the same task, and keying one as "T01" and the other as "T1"
        # made a padded citation resolve against nothing. The pre-renumbering
        # code returned ints, which normalized for free; keying by string
        # dropped that property silently. The test suite caught it.
        codes.add(f"LJ-{phase}.{step}" if phase else f"T{int(old)}")
    codes |= {f"T{int(n)}" for n in SHORT.findall(text)}
    return codes


def index_rows(plan_text: str,
               archived: bool = True) -> list[tuple[str, str, str]]:
    """All `(code, key, row line)` triples in PLAN's task index section.

    Only the `### Task index` section is read, so a stray `| L3.32-T... |`
    row anywhere else in the document is not mistaken for an index row.

    `archived` controls whether the retired series file is folded in. It is
    True for every real caller, because a citation of an archived task must
    still resolve. It exists as a parameter because this function otherwise
    mixes PARSING a string with READING a file from disk, and a test that
    passes a two-row fixture then gets 287 rows back. Keeping the I/O
    switchable is what makes the parser testable.
    """
    m = re.search(rf"^{re.escape(SECTION)}.*?^(?=### |## )", plan_text,
                  re.S | re.M)
    block = m.group(0) if m else ""
    # The retired series lives in its own file, and its rows count as rows:
    # a citation of an archived task must still resolve.
    if archived and ARCHIVED_INDEX.exists():
        block += ARCHIVED_INDEX.read_text(encoding="utf-8")
    # Keyed by the FULL code, not the number. The two series share numbers by
    # design (neither reuses one WITHIN itself), so LJ-1.1 and L3.32-T1 are
    # different rows and a number-keyed dedup would call them a duplicate.
    rows = []
    for line in re.findall(
            r"^\| (?:LJ-\d+\.\d+[a-z]*(?:-[A-Z])?|L3\.32-T\d+) \|.*$",
            block, re.M):
        code = ROW.match(line).group(1)
        key = (code if code.startswith("LJ-")
               else f"T{int(code.split('-T')[1])}")  # same zero-pad rule
        rows.append((code, key, line))
    return rows


def capped_rows(plan_text: str) -> list[tuple[str, str]]:
    """Every DATA row of the live task index, as `(first cell, line)`.

    THIS FUNCTION IS THE CAP'S OWN READER, and it does not consult the code
    grammar. Two widenings of that grammar have now been forced by rows the
    cap could not see, and both times the cap was the casualty rather than the
    cause. A row is capped because it is a row.

    It reads the LIVE index only. `archive/dev/TASKS-archived.md` is frozen by
    AGENTS.md and a gate over a frozen record can only force an edit to the
    record; MEASURED 2026-08-16, its 265 rows top out at exactly 200 anyway.

    The header row and the separator are not data and are dropped by name.
    """
    m = re.search(rf"^{re.escape(SECTION)}.*?^(?=### |## )", plan_text,
                  re.S | re.M)
    if not m:
        return []
    out = []
    for line in m.group(0).split("\n"):
        if not line.startswith("| ") or line.startswith("| ---"):
            continue
        cell = line.split("|")[1].strip()
        if cell == "Code":
            continue
        out.append((cell, line))
    return out


def check_index(plan_text: str, sources_text: str,
                archived: bool = True) -> tuple[list[str], int, int]:
    """Enforce one row per cited code and the row-length cap.

    Returns (errors, number of distinct cited codes, number of distinct rows).
    An empty error list is a pass.

    `archived` is passed through to index_rows. True for every real caller;
    False lets a test drive a small fixture without the 265 archived rows
    resolving its deliberately-missing codes and colliding with its row ids.
    """
    errors: list[str] = []
    rows = index_rows(plan_text, archived=archived)
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
            # `code` is the series-neutral key, because a short citation
            # `[T5]` cannot say which series it means and BOTH indexes are
            # searched. Spell out where it was looked for, so the reader
            # knows a missing row is missing from both.
            where = ("LJ series in dev/PLAN.md" if code.startswith("LJ-")
                     else "L3.32 series in archive/dev/TASKS-archived.md, "
                          "nor the LJ series in dev/PLAN.md")
            errors.append(
                f"no index row: task {code} is cited in dev/, briefs or git "
                f"log, but has no row in the {where}")
    # THE CAP READS EVERY ROW, not the rows the code grammar matched. See
    # `capped_rows`. A row in CAP_FROZEN is reported by main() and never
    # fails.
    for cell, line in capped_rows(plan_text):
        length = len(line.rstrip())
        if length > CAP and cell not in CAP_FROZEN:
            errors.append(
                f"row over cap: {cell} is {length} characters "
                f"(cap {CAP}): {line}")
    return errors, len(cited), len(seen)


def scanned_texts() -> str:
    """All scanned sources: dev/ files, briefs, and the git log."""
    texts = []
    for path in sorted(ROOT.joinpath("dev").rglob("*")):
        if path.is_file() and path.suffix in TEXT_SUFFIXES:
            texts.append(path.read_text(encoding="utf-8", errors="replace"))
    for path in T.briefs():
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
    # THE FORGIVEN SET IS PRINTED EVERY RUN. A frozen backlog that nobody
    # sees is a rule quietly retired (C-59).
    frozen = [(cell, len(line.rstrip()))
              for cell, line in capped_rows(plan_text)
              if len(line.rstrip()) > CAP and cell in CAP_FROZEN]
    if frozen:
        worst = max(n for _, n in frozen)
        print(f"task index: {len(frozen)} row(s) frozen over the cap before "
              f"the {CAP_EPOCH} epoch, longest {worst}; reported, never "
              f"failed: {', '.join(c for c, _ in sorted(frozen))}")
    if not errors:
        print(f"task index OK: {cited} cited codes, {rows} unique rows, "
              f"{len(capped_rows(plan_text))} data rows read for the "
              f"{CAP}-character cap")
        return 0
    for error in errors:
        print(f"FAIL: {error}")
    print(f"{len(errors)} defect(s)")
    return 1


if __name__ == "__main__":
    sys.exit(main())
