#!/usr/bin/env python3
"""A brief that carries a TRIGGER TOKEN declares its load-bearing premises.

WHY THIS EXISTS, and it is measured rather than feared. `[LJ-1.211]` measured
the cause of every DD25 overturn on record. The briefs caused 8 of 10. The
reviewer caused 0. Two reviews wrote the cure in their own words:

- `[LJ-1.66-R]`: GO only if (a) the unit cost is 0.05 s or more AND (b) the
  applications genuinely collapse. Verify (b) by reading the sites BEFORE
  you build anything
  (`agents/tasks/archive/LJ-1-66/lj-1.66-review.md:230-258`).
- `[LJ-1.15-R]`: Derive every line gate from the booked row's own per-unit
  figure, and write that derivation in the brief
  (`agents/tasks/archive/LJ-1-15/lj-1.15-review.md:407-409`).

This gate makes those two sentences mechanical. A brief that carries a
trigger token and no `## PREMISES` section fails. The section lists each
load-bearing premise with a basis at `file:line`. The return marks each
premise VERIFIED or REFUTED at `file:line`. A DD25 review attacks that list
before anything else.

THE TRIGGER TABLE, AND IT IS TUNED AGAINST THE RECORD. `[LJ-1.211]` names
ten trigger tokens. The raw list fires on 118 of 118 live briefs, MEASURED
2026-08-14. That is the abort case its own brief names: a list that fires on
most briefs is wrong, because a gate that fires wrongly trains the author to
paste a heading. So the table below marks each token ACTIVE or REFUSED. An
ACTIVE token fires the gate. A REFUSED token does not fire, because its
measured fire rate is unworkable; its measured failure shape has another
home, named in its row. Each row names the fire rate over the 118 live
briefs. An ACTIVE row names the overturn that earns its place.

WHAT THIS CHECKS, and the narrowness is the whole design. A brief fails
when it carries an ACTIVE trigger token and its `## PREMISES` section is
missing or carries no basis at `file:line`. A section that exists but has no
basis is the pasted-heading failure, and it fails too. The refusal message
names the token that fired and shows the section's shape.

WHAT THIS REFUSES TO CHECK, and each refusal is a written limit, because
`AGENTS.md` says a row claiming more than its checker delivers turns a rule
into false safety.

- It cannot tell whether a premise is TRUE. It checks that the author listed
  one and gave it a basis.
- It cannot tell whether the basis at `file:line` says what the author
  claims. Write the basis so a review can read it.
- It cannot fire at the moment the brief is WRITTEN, which is when the
  failure happens. It fires at the commit or the gate.
- It reads the brief, never the return. The return's VERIFIED and REFUTED
  marks are not checked.
- A REFUSED token does not fire. `section` with a number fired on 45.8
  percent of live briefs, a LESSONS law ID on 100 percent, a bare figure
  with a unit on 67.8 percent, and `do not weaken` on 33.9 percent. A gate
  on those tokens would buy a pasted heading. Their cures live elsewhere:
  C-32 says cite whole documents, `[LJ-1.211]`'s change 3 quotes a law's
  action, and C-36 says write both halves of a strength instruction.

THE BACKLOG IS MEASURED, AND IT IS THE FINDING. On 2026-08-14, 28 of 118
live briefs carry an ACTIVE trigger and no declared premises. Every one is a
frozen record: a brief is a record and a record is never rewritten, so the
set is reported once and never fails, and nothing is ever added to it. A
brief authored after this gate that carries a trigger and no `## PREMISES`
section is a defect. `LJ-1-212` is in the set: it is the gate's own brief,
written before the gate existed.

USAGE
    python3 scripts/gate/check-premises-stated.py

Exit status: 0 clean (or clean after grandfathering), 1 defect found,
2 environment failure. `--quiet` suppresses the backlog listing and
`--tasks <dir>` reads a different task root (what the test suite drives).
"""

from __future__ import annotations

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
TASKS = ROOT / "agents" / "tasks"

# The section heading. The brief writes `## PREMISES`; a deeper heading with
# the same word counts, because the section is what matters, not the level.
HEADING = re.compile(r"^#{2,}\s*PREMISES\b", re.M)

# A basis at file:line. The project writes `path.md:230-258`, `file.py:40`
# and `dir/name.lagda.md:667-678`. A filename, a colon, and a line number
# (with an optional range) are the shape. This is what the gate can check.
BASIS = re.compile(
    r"\b[\w./-]+\.(?:md|lagda|agda|toml|py|sh|txt)"
    r":\s*\d+(?:\s*-\s*\d+)?\b")

NEXT_HEADING = re.compile(r"^#{1,6}\s", re.M)

# The match shapes behind the table's mode column. Each mode is one named
# pattern. The complex modes live here so a table row says only how to read
# its token.
THRESHOLD_FIGURE = re.compile(
    r"(?:\b\d+(?:\.\d+)?\s*(?:s|ms|secs?|seconds?|lines?)\b.{0,40}"
    r"\b(?:or[\s*_~`,;:]*fewer|or[\s*_~`,;:]*less|or[\s*_~`,;:]*more|"
    r"or[\s*_~`,;:]*greater|at[\s*_~`,;:]*least|at[\s*_~`,;:]*most|"
    r"exactly)\b)"
    r"|(?:\b(?:at[\s*_~`,;:]*least|at[\s*_~`,;:]*most|under|over|below|"
    r"above|fewer[\s*_~`,;:]*than|more[\s*_~`,;:]*than|"
    r"up[\s*_~`,;:]*to|no[\s*_~`,;:]*more[\s*_~`,;:]*than)"
    r"[\s*_~`,;:]*\d+(?:\.\d+)?\s*(?:s|ms|secs?|seconds?|lines?)\b)",
    re.I)

BARE_FIGURE = re.compile(
    r"\b\d+(?:\.\d+)?\s*(?:s|ms|secs?|seconds?|lines?|"
    r"per\s*line|lines\s*per)\b",
    re.I)

SECTION_REF = re.compile(r"\bsection\s+\d+\b", re.I)

LAW_ID = re.compile(r"\b(?:P-[a-z]|C-\d{1,2}|D-\d{1,2}|DD\d{1,2})\b", re.I)

# ---------------------------------------------------------------------------
# THE TRIGGER VOCABULARY, AS A TABLE. `[LJ-1.208]`'s gate needed a
# negative-verdict vocabulary and this gate needs a premise-trigger
# vocabulary; a third rule will need a third, and a vocabulary written
# inline is paid for every time. Each row is:
#
#   (token, mode, active, why it earns its place)
#
#   mode:   how to read the token. "phrase" joins the token's words with
#           optional markdown emphasis and punctuation. "word" matches the
#           whole word. "threshold" matches a figure with a unit and a
#           comparator, the shape a fixed gate writes. "bare", "section"
#           and "law" are the REFUSED shapes, kept in the table so the next
#           rule reads the vocabulary instead of reinventing it.
#   active: True fires the gate, False documents a measured refusal.
#
# The fire rates are MEASURED 2026-08-14 over the 118 live briefs, by
# `[LJ-1.212]`. A token earns its place if a brief carrying it produced an
# overturn, or if `[LJ-1.211]` names it. A REFUSED row still earns its
# place in the table: its measured rate is why it cannot gate.
# ---------------------------------------------------------------------------
TRIGGER: tuple[tuple[str, str, bool, str], ...] = (
    ("the gate is",
     "phrase", True,
     "2.5 percent fire; LJ-1.7-R's brief shipped its conclusion as a "
     "fixed gate"),
    ("GO needs",
     "phrase", True,
     "0.8 percent fire; LJ-1.15-R's brief fixed its gate as GO needs "
     "BOTH"),
    ("NO-GO is",
     "phrase", True,
     "2.5 percent fire; LJ-1.15-R's brief fixed its gate as NO-GO is"),
    ("the only lever",
     "phrase", True,
     "0 percent fire; [LJ-1.211] names it, and one lever is a "
     "load-bearing claim"),
    ("shapes",
     "word", True,
     "7.6 percent fire; LJ-1.16-R and LJ-1.33-R briefs named shapes"),
    ("measure it, do not argue it",
     "phrase", True,
     "0 percent fire among live briefs; LJ-1.34-R's brief carried it and "
     "C-34 measures its cost"),
    ("a figure with a unit",
     "threshold", True,
     "13.6 percent fire; LJ-1.15-R (40 lines or fewer) and LJ-1.66-R "
     "(under 0.05 s) fixed gates with thresholds"),
    ("a figure with a unit",
     "bare", False,
     "67.8 percent fire for time and line figures; REFUSED, a red gate "
     "would buy a pasted heading"),
    ("section",
     "section", False,
     "45.8 percent fire for section plus a number; REFUSED, C-32's cure "
     "is to cite whole documents"),
    ("a LESSONS law ID",
     "law", False,
     "100 percent fire; REFUSED, every brief lists its mandatory rules, "
     "and [LJ-1.211]'s change 3 quotes a law's action"),
    ("do not weaken",
     "phrase", False,
     "33.9 percent fire; REFUSED, C-36's cure is to write both halves of "
     "a strength instruction"),
)

ACTIVE = [(token, mode) for token, mode, active, _ in TRIGGER if active]

#: MEASURED 2026-08-14 by `[LJ-1.212]`: every live brief that carries an
#: ACTIVE trigger and no `## PREMISES` section with a basis. This is the
#: honest scale of the lapse and the whole reason the epoch exists. Frozen
#: records: reported once, never failed. Do not add to this set. A new
#: lapse is a defect, and that is the point.
PRE_EPOCH = frozenset({
    "LJ-1-93", "LJ-1-94", "LJ-1-98", "LJ-1-101", "LJ-1-108", "LJ-1-110",
    "LJ-1-115", "LJ-1-120", "LJ-1-147", "LJ-1-150", "LJ-1-156", "LJ-1-157",
    "LJ-1-161", "LJ-1-162", "LJ-1-163", "LJ-1-167", "LJ-1-169", "LJ-1-171",
    "LJ-1-173", "LJ-1-179", "LJ-1-198", "LJ-1-200", "LJ-1-201", "LJ-1-202",
    "LJ-1-204", "LJ-1-208", "LJ-1-209", "LJ-1-212",
})


def token_regex(token: str, mode: str) -> re.Pattern[str]:
    """The pattern for one table row, derived from the row's own words."""
    if mode == "word":
        return re.compile(rf"\b{re.escape(token)}\b", re.I)
    if mode == "phrase":
        words = [w for w in re.split(r"[^A-Za-z0-9-]+", token) if w]
        body = r"[\s*_~`,;:]*".join(re.escape(w) for w in words)
        return re.compile(rf"\b{body}\b", re.I)
    if mode == "threshold":
        return THRESHOLD_FIGURE
    if mode == "bare":
        return BARE_FIGURE
    if mode == "section":
        return SECTION_REF
    if mode == "law":
        return LAW_ID
    raise ValueError(f"unknown trigger mode: {mode}")


def trigger_hits(text: str) -> list[str]:
    """The ACTIVE table tokens a brief carries, in table order."""
    return [token for token, mode in ACTIVE
            if token_regex(token, mode).search(text)]


def premises_section(text: str) -> str | None:
    """The text under the `## PREMISES` heading, or None for no heading."""
    hit = HEADING.search(text)
    if hit is None:
        return None
    rest = text[hit.end():]
    nxt = NEXT_HEADING.search(rest)
    return rest if nxt is None else rest[:nxt.start()]


def briefs(tasks: Path) -> list[Path]:
    """Every live brief, from the ONE home for that question.

    THIS USED TO ROLL ITS OWN GLOB, `d.glob("[A-Z]*.md")`, and so did
    `check-dd4-stated.py`. `scripts/agents_tree.py` is where the brief-versus-report
    signal lives, written once by `[LJ-1.142]` so a correction reaches every reader at
    the same time, and both checkers bypassed it.

    MEASURED 2026-08-15: the glob read four `.lagda.md` measurement arms under
    `agents/tasks/LJ-1-275/` as briefs and demanded a PREMISES section from each.
    `agents_tree.documents()` has excluded `.lagda.md` since it was written.

    `tasks` is kept in the signature for the tests that pass a fixture root.
    """
    live = agents_tree.briefs()
    return [p for p in live
            if "archive" not in p.parts and str(p).startswith(str(tasks))]


def brief_findings(path: Path, text: str) -> tuple[list[str], str] | None:
    """(tokens, reason) for a failing brief, or None for a passing one."""
    tokens = trigger_hits(text)
    if not tokens:
        return None
    section = premises_section(text)
    if section is not None and BASIS.search(section):
        return None
    if section is None:
        reason = "carries no ## PREMISES section"
    else:
        reason = "carries a ## PREMISES section with no basis at file:line"
    return tokens, reason


def show(path: Path) -> str:
    """The path as a reader would write it: relative to ROOT when possible."""
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def main(argv: list[str]) -> int:
    quiet = "--quiet" in argv[1:]
    tasks = TASKS
    if "--tasks" in argv[1:]:
        tasks = Path(argv[argv.index("--tasks") + 1])
    try:
        files = briefs(tasks)
    except OSError as exc:
        print(f"check-premises-stated: {exc}")
        return 2
    if not files:
        print(f"check-premises-stated: no briefs under {tasks}")
        return 2

    defects: list[tuple[Path, list[str], str]] = []
    backlog: list[Path] = []
    for p in files:
        try:
            text = p.read_text(encoding="utf-8")
        except OSError as exc:
            print(f"check-premises-stated: {exc}")
            return 2
        found = brief_findings(p, text)
        if found is None:
            continue
        if p.parent.name in PRE_EPOCH:
            backlog.append(p)
        else:
            defects.append((p, *found))

    if defects:
        print(f"check-premises-stated: {len(defects)} brief(s) carry a "
              f"trigger and no declared premises, {len(backlog)} frozen "
              f"pre-epoch:", file=sys.stderr)
        for p, tokens, reason in defects:
            print(f"  {show(p)}: {reason}; carries: "
                  f"{', '.join(tokens)}", file=sys.stderr)
        print("", file=sys.stderr)
        print("A brief that funds a gate, a build or a probe on a premise "
              "declares that premise in a `## PREMISES` section.", file=sys.stderr)
        print("Write the section, one premise per line, each with a basis "
              "at `file:line`:", file=sys.stderr)
        print("  ## PREMISES", file=sys.stderr)
        print("  - <the premise> at <file:line>", file=sys.stderr)
        print("The return marks each premise VERIFIED or REFUTED at "
              "`file:line`.", file=sys.stderr)
        return 1

    note = "" if quiet else (
        f"; frozen: {', '.join(sorted(p.parent.name for p in backlog))}")
    print(f"check-premises-stated: {len(files)} briefs, {len(backlog)} "
          f"frozen pre-epoch brief(s) with a trigger and no declared "
          f"premises, 0 new defects{note}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
