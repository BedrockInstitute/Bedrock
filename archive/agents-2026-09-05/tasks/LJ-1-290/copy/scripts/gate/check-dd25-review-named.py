#!/usr/bin/env python3
"""DD25: the index row for a negative return names its review's code.

WHY THIS EXISTS, and it is measured rather than feared. DD25's own enforcement
point is the PLAN section 11 row: a row whose headline verdict is negative
must name the code of the adversarial review dispatched against it. `[LJ-1.183]`
measured that no negative row named a review code. The orchestrator fixed the
four rows it found, then let four MORE negatives go unreviewed inside the same
session, and the owner caught it again. The verdict cell is structured text and
a negative announces itself, so this is mechanical, and that is the whole
argument.

WHAT THIS CHECKS. For every row in the task index, the VERDICT CELL is read
for the negative-verdict vocabulary in `NEGATIVE_VERDICT` (a table, because the
next rule that needs "what counts as a negative" reads the table rather than
reinventing it). A row whose verdict cell carries a table token must do one of
three things, or it fails:

1. Name its review's code: cite a code (bracketed `[LJ-...]` or bare
   `LJ-...-R`) whose OWN row is a DD25 review, detected the same way a reader
   detects one: the `-R` suffix, or a task cell that says it is a DD25,
   adversarial or Fable-5 review. The four repaired controls, `[LJ-1.162]`,
   `[LJ-1.165]`, `[LJ-1.169]` and `[LJ-1.172]`, all name theirs today.
2. Declare, in the row, why this verdict is not a DD25 negative, as
   `DD25 review not needed: <reason>`. The gate does not judge the reason; it
   makes the declaration visible, and DD25's own row says the honest
   enforcement is that the row is empty and visible.
3. Be a pre-epoch row. The measured backlog is frozen in `PRE_EPOCH`, reported
   once and never failed, exactly as `check-dd4-stated.py` freezes its twelve.

A row that IS a DD25 review (its own code is a review row) is exempt: it is the
review, not a return needing review, and requiring a review to name its own
review would regress forever.

WHAT THIS REFUSES TO CHECK, and each refusal is a written limit, because
`AGENTS.md` says a row claiming more than its checker delivers turns a rule
into false safety.

- **It cannot tell whether a verdict is REALLY negative.** `GO AT 20 LINES, AND
  A NEW WALL` (`[LJ-1.161]`) is positive and negative at once, and `NOT
  REFUTED, FRAME GREEN` (`[LJ-1.125]`) announces no negative while carrying the
  word. So the table is tunable, the tool explains itself, and a false
  positive is silenced with a reason, never by deleting a word.
- **It cannot tell whether the review was any GOOD.** DD25 asks for an
  adversarial review at maximum effort; this checks that one was NAMED. A
  named review that agrees with the negative is a real result and still
  satisfies the gate.
- **It cannot fire at the moment the return lands**, which is when the
  orchestrator forgets. The honest enforcement point is the commit or the
  gate, and this tool is that gate: it fires at `make check`, later than the
  forgetting and exactly when the orchestrator is forced to look.
- **The vocabulary is not every negative.** A bare `NO` verdict, a `REGRESSED`
  row, a `RED` gate and an `ANSWERED NO` are real negatives that the table
  does not carry, deliberately: `NO` would fire on `NO REPLACEMENT` and `NO
  HYPOTHESIS LEFT`, which are GO rows. The table is the owner's ten tokens plus
  DD25's own word "refusal"; it over-approximates in some places and
  under-approximates in others, and both limits are this paragraph.
- **A declared reason is not a checked reason.** `DD25 review not needed:
  <reason>` is an escape hatch (C-43): the token becomes legal wherever the
  table fires, and a wrong use passes. What the gate delivers is a TRACE an
  audit can find: the row is no longer empty, and the reason is there to
  read. A gate that judged reasons would be a gate that reads minds, which is
  exactly what this tool refuses to be.

THE BACKLOG IS MEASURED, AND IT IS THE FINDING. On 2026-08-14 the real tree
carried forty-two rows whose verdict cell announces a negative and whose row
names no review. Every one is frozen history: a row is a record and
a record is never rewritten, so the set is reported once and never fails, and
nothing is ever added to it. A negative row authored after this gate that
names no review is a defect, and that is the whole point of the epoch.

USAGE
    python3 scripts/gate/check-dd25-review-named.py

Exit status: 0 clean (or clean after grandfathering), 1 defect found,
2 environment failure. `--quiet` suppresses the backlog listing and
`--plan <file>` reads a different PLAN file (what the test suite drives).
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
PLAN = ROOT / "dev" / "PLAN.md"

# The task index lives under section 11, headed `### Task index`. The header
# text after `### Task index` is load-bearing, so the section match is anchored
# on the words and read to the next `### ` or `## ` heading, exactly as
# `scripts/gate/check-task-index.py` reads it.
SECTION = "### Task index"

# ---------------------------------------------------------------------------
# THE NEGATIVE-VERDICT VOCABULARY, AS A TABLE. This is the shared table the
# next rule that needs "what counts as a negative" should read rather than
# reinvent. Each row is (token, match mode, reason it announces a negative).
#
#   word:   the token as a whole word (`\b<token>\b`), so `ZERO` does not fire
#           on `ZEROED` and `NO-GO` does not fire on `NO-GOOD`.
#   prefix: the token as a word prefix (`\b<token>`), so `STOP` catches
#           `STOPPED` and `WALL` catches `WALLS`.
#
# The ten tokens are the owner's list from the gate brief. `REFUSED`,
# `REFUSAL` and `REFUTABLE` are added as rows because DD25's trigger names "a
# refusal" and "a refutation" in as many words, and the shorthand list
# omitted those spellings. Ruling them out is deleting rows, which is the
# point of a table. Match modes are measured against the real index:
# `STOPPED`, `REFUTABLE` and `WALLS` all appear in verdict cells as
# negatives.
# ---------------------------------------------------------------------------
NEGATIVE_VERDICT: tuple[tuple[str, str, str], ...] = (
    ("STOP",      "prefix", "a stop taken as the deliverable is DD25's trigger"),
    ("NO-GO",     "word",   "a NO-GO is DD25's trigger by name"),
    ("REFUTED",   "word",   "a refutation of the brief's premise is DD25's trigger"),
    ("REFUTABLE", "word",   "a refutation of the brief's premise is DD25's trigger"),
    ("REFUSED",   "word",   "DD25's trigger names a refusal; the verdict spells it"),
    ("REFUSAL",   "word",   "DD25's trigger names a refusal; the verdict spells it"),
    ("BLOCKED",   "word",   "a landed result that cannot land is a negative"),
    ("FALSE",     "word",   "a stated fact found false is a refutation"),
    ("WALL",      "prefix", "a wall is a landed result that misses its band floor"),
    ("OVERTURNED","word",   "a negative overturned still announces the negative"),
    ("DOES NOT",  "word",   "a theorem that does not derive is a refutation"),
    ("NOTHING",   "word",   "a deliverable that proves nothing is a negative"),
    ("ZERO",      "word",   "a zero-line result is a stop or an unbuilt claim"),
)

# The review-code patterns: bracketed `[LJ-...]` and bare `LJ-...-R` (or an
# abbreviated `1.50-R`), the two forms the index actually writes.
BRACKETED = re.compile(r"\[(LJ-\d+\.\d+[a-z]*(?:-[A-Z])?)\]")
BARE = re.compile(r"(?<![\w.])(?:LJ-)?(\d+\.\d+[a-z]*(?:-[A-Z])?)(?![\w.])")

# The reason marker: the one way a negative-looking verdict is declared not to
# be a DD25 negative. The reason is whatever follows the colon and must start
# with a word character, so the `|` cell separator and an empty reason cannot
# satisfy it; the gate does not judge the reason, it makes it visible.
REASON = re.compile(r"DD25 review not needed:\s*\w", re.I)

# A row is a review row when a reader would call it one: the `-R` suffix, or a
# task cell that says it is a DD25, adversarial or Fable-5 review.
REVIEW_TASK = re.compile(r"(?:DD25.*review|adversarial review|fable 5)", re.I)

#: MEASURED 2026-08-14 by `[LJ-1.208]`: every row in the live task index whose
#: verdict cell announces a negative and whose row names no review. This is the
#: honest scale of the lapse and the whole reason the epoch exists. Frozen
#: records: reported once, never failed. Do not add to this set. A new lapse
#: is a defect, and that is the point.
PRE_EPOCH = frozenset({
    "LJ-0.4b", "LJ-0.4c", "LJ-0.4d", "LJ-0.4e",
    "LJ-1.2", "LJ-1.6", "LJ-1.17", "LJ-1.27", "LJ-1.33", "LJ-1.34",
    "LJ-1.38", "LJ-1.60", "LJ-1.61", "LJ-1.65", "LJ-1.72", "LJ-1.73",
    "LJ-1.80-A", "LJ-1.84", "LJ-1.95", "LJ-1.97", "LJ-1.112",
    "LJ-1.114", "LJ-1.121", "LJ-1.125", "LJ-1.146", "LJ-1.149",
    "LJ-1.150", "LJ-1.151", "LJ-1.153", "LJ-1.156", "LJ-1.160",
    "LJ-1.161", "LJ-1.167", "LJ-1.174", "LJ-1.175", "LJ-1.176",
    "LJ-1.177", "LJ-1.178", "LJ-1.185", "LJ-1.186", "LJ-1.196",
    "LJ-1.199",
})

ROW = re.compile(
    r"^\|\s*(LJ-\d+\.\d+[a-z]*(?:-[A-Z])?)\s*"
    r"\|\s*([^|]*?)\s*\|"
    r"\s*([^|]*?)\s*\|"
    r"\s*([^|]*?)\s*\|\s*$")


def index_rows(plan_text: str) -> list[tuple[str, str, str, str]]:
    """Every `(code, task, verdict, detail)` row in the task index section.

    Reading is kept separate from parsing so a test can drive a two-row
    fixture without the real 288-row section (the same switch
    `check-task-index.py` makes with its `archived` parameter). Only the
    `### Task index` section is read, so a stray table row elsewhere in the
    document is not mistaken for an index row.
    """
    m = re.search(rf"^{re.escape(SECTION)}.*?^(?=### |## )",
                  plan_text, re.S | re.M)
    rows: list[tuple[str, str, str, str]] = []
    if not m:
        return rows
    for line in m.group(0).splitlines():
        hit = ROW.match(line)
        if hit:
            rows.append(tuple(hit.groups()))  # type: ignore[arg-type]
    return rows


def negative_tokens(verdict: str) -> list[str]:
    """The table tokens a verdict cell carries, in table order."""
    v = verdict.upper()
    found = []
    for token, mode, _ in NEGATIVE_VERDICT:
        tail = "" if mode == "prefix" else r"\b"
        if re.search(rf"\b{re.escape(token)}{tail}", v):
            found.append(token)
    return found


def review_codes(rows: list[tuple[str, str, str, str]]) -> set[str]:
    """The codes whose own rows are DD25 reviews.

    The `-R` suffix, or a task cell that names the review (`DD25 review`,
    `adversarial review`, `Fable 5`). This is how the gate knows a cited code
    is really a review and not merely another task mentioned in the detail
    cell.
    """
    reviews = set()
    for code, task, _verdict, _detail in rows:
        if code.endswith("-R") or REVIEW_TASK.search(task):
            reviews.add(code)
    return reviews


def cited_codes(row: tuple[str, str, str, str], reviews: set[str]) -> set[str]:
    """The review codes a row names, its own code excluded."""
    code, task, verdict, detail = row
    text = " | ".join((task, verdict, detail))
    cited = set(BRACKETED.findall(text))
    cited |= {f"LJ-{m}" for m in BARE.findall(text)
              if m != code.removeprefix("LJ-")}
    cited.discard(code)
    return cited & reviews


def row_findings(row: tuple[str, str, str, str],
                 reviews: set[str]) -> list[str]:
    """The DD25 findings for one row: empty means the row satisfies DD25."""
    code, _task, verdict, detail = row
    if code in reviews:
        return []                       # a review is not a return needing one
    tokens = negative_tokens(verdict)
    if not tokens:
        return []
    if REASON.search(" | ".join((verdict, detail))):
        return []                       # declared, with the reason visible
    if cited_codes(row, reviews):
        return []                       # names its review's code
    named = ", ".join(tokens)
    return [
        f"DD25 unmet: row {code} carries the negative verdict "
        f"\"{verdict}\" (tokens: {named}) and names no DD25 review.",
        "DD25 requires the row to name its review's code. Append the review's "
        "verdict with its code, e.g. `DD25 review [LJ-x.y] UPHELD`, or write "
        "`DD25 review not needed: <reason>` in the row if this verdict is not "
        "a DD25 negative.",
    ]


def check_rows(rows: list[tuple[str, str, str, str]]
               ) -> tuple[list[list[str]], list[str]]:
    """(defect blocks, backlog codes) over the index rows.

    A defect is a negative row, not a review, not declared, naming no review,
    and NOT in `PRE_EPOCH`; one block of message lines per failing row. A
    backlog code is exactly that but IN `PRE_EPOCH`: frozen history, reported,
    never failed. The count of backlog codes is the honest scale of the lapse
    this gate exists to stop repeating.
    """
    reviews = review_codes(rows)
    defects: list[list[str]] = []
    backlog: list[str] = []
    for row in rows:
        found = row_findings(row, reviews)
        if not found:
            continue
        if row[0] in PRE_EPOCH:
            backlog.append(row[0])
        else:
            defects.append(found)
    return defects, sorted(backlog)


def main(argv: list[str]) -> int:
    quiet = "--quiet" in argv[1:]
    plan = PLAN
    if "--plan" in argv[1:]:
        plan = Path(argv[argv.index("--plan") + 1])
    try:
        plan_text = plan.read_text(encoding="utf-8")
    except OSError as exc:
        print(f"check-dd25-review-named: {exc}")
        return 2
    rows = index_rows(plan_text)
    if not rows:
        print(f"check-dd25-review-named: no task index section "
              f"(`{SECTION}`) in {PLAN}")
        return 2
    defects, backlog = check_rows(rows)

    if defects:
        print(f"check-dd25-review-named: {len(defects)} row(s) fail DD25, "
              f"{len(backlog)} frozen pre-epoch:", file=sys.stderr)
        for block in defects:
            for line in block:
                print(f"  {line}", file=sys.stderr)
        print("", file=sys.stderr)
        print("A negative return is reviewed at maximum effort, immediately, "
              "and its row names the review's code (DD25). A row that is "
              "negative and silent is the exact lapse this gate exists for.",
              file=sys.stderr)
        return 1

    note = "" if quiet else (
        f"; backlog: {len(backlog)} pre-epoch row(s) negative with no named "
        f"review, frozen: {', '.join(backlog)}")
    print(f"check-dd25-review-named: {len(rows)} index rows, "
          f"{len(backlog)} frozen pre-epoch negative row(s) without a named "
          f"review, 0 new defects{note}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
