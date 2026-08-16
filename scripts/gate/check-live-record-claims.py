#!/usr/bin/env python3
"""A brief answers the live record its own words implicate.

WHY THIS EXISTS, and it is measured rather than feared. `[LJ-1.376]` audited
the orchestrator's detours and found the dominant kind is NONE of the archive
kinds: it is the LIVE record not read, which caused 8 of the 10 overturned
DD25 reviews and the four costliest episodes. Its costliest single case:
ten dispatches re-derived a price that stood in `dev/PLAN.md` section 0.0
the whole time (`dev/JOURNAL.md:1002`), and the cure lived as a sentence in
the journal with no enforcement point. A rule no machine enforces must name
its enforcement point, and a rule with none is a wish (DD19). This gate is
that enforcement point, and `[LJ-1.377]` measured its shape against the
episodes before writing it.

THE MEASURED DESIGN CONSTRAINT, and it killed the first two candidates.

- Matching the WHOLE brief against every index row by token overlap fires on
  274 of 274 live briefs, MEASURED by the `[LJ-1.377]` probe. That is the
  `[LJ-1.212]` lesson again: a gate that fires on everything trains pasting.
- A duty to answer every row adjacent to every cited code fires on 100
  percent of briefs for the same reason. The adjacency read survives only
  as a PRINT (`--brief` mode), never as a gate.

WHAT SURVIVES is two narrow triggers, each tuned against the record like
`check-premises-stated.py`'s table:

1. THE CLAIM TRIGGER. A line carrying a negative-existence claim about the
   record ("nobody has run", "nothing on record", "exists nowhere", ...) is
   searched, BY THIS CHECKER, against the task index and the section 0.0
   screen as they stood when the brief was written. Every row that carries
   a positive status (GO, BUILT, GREEN, ...) and shares two or more content
   tokens with the claim line must be ANSWERED. `[LJ-1.230]`'s brief said
   "the probe nobody has run" while `[LJ-1.124]`'s row said "GO, 147 LINES":
   the search finds that row, MEASURED against the historical index by the
   `[LJ-1.377]` probe, and the brief must answer it or decline it in writing.
2. THE GOAL TRIGGER. A brief that names a goal code (`[LJ-1.7]`, `[LJ-2.3]`,
   the codes of the section 0.0 blocked table) must answer every numbered
   open-work item and the goal's blocked-table row. This is the journal's
   one-grep cure made mechanical: before briefing a blocked row, read the
   open-work list (`dev/JOURNAL.md:1026-1029`). The list is small (8 items
   on 2026-08-16, MEASURED) and the answer is one line per item.

THE ANSWER, so an author can comply without guessing. A `## LIVE RECORD`
section in the brief, one line per flagged object:

    ## LIVE RECORD
    - LJ-1.124: <a quote, or why this row does not bear>
    - open work item 1: <a quote, or why it does not bear>
    - screen:47: <a quote, or why it does not bear>

A written decline is compliance, the `[LJ-1.357]` lesson from DD18 B2: the
duty forces the row into view and the text into review; it cannot force
understanding, and says so.

THE RECORD AS THE WRITER FACED IT. Hits are derived from `dev/PLAN.md` at
the parent of the commit that added the brief, so a live screen that grows
cannot turn an old compliant brief red. An uncommitted brief is checked
against the working tree, which is the record its writer faces.

WHAT THIS REFUSES TO CHECK, because a row claiming more than its checker
delivers is false safety:

- It cannot tell whether a row BEARS on the brief. Relevance stays review;
  the decline line is where the author says so, and a review reads it.
- It cannot catch a renamed object that shares no token with its record.
  `[LJ-1.377]` measured this honestly: the `[LJ-1.242]`..`[LJ-1.250]` chain
  re-derived "Step 6" under names sharing no second token with the screen,
  and no token matcher sees it. The goal trigger gives that class its
  forced juxtaposition and nothing more; the connection stays the writer's.
- It cannot see the src/ tree, the ledger, or anything but `dev/PLAN.md`.
  Suppliers already delivered in code (the `[LJ-1.168]` class) need a
  different search, and P-l's re-measure duty stays review.
- It fires at the gate, not at the moment the brief is written. The
  `--brief <file>` mode exists for the writing moment; it PRINTS the claim
  hits, the goal duties, and the adjacent-row read, and gates nothing.

THE EPOCH, and its scale is written here and never in a commit message
(C-59). On 2026-08-16 the checker found 74 of 275 live briefs carrying a
trigger and no answered `## LIVE RECORD` section: median 4 duties per
failing brief, maximum 22. Every one is a frozen record, reported once and
never failed. A brief authored after this gate that carries a trigger and
no answered LIVE RECORD section is a defect.

USAGE
    python3 scripts/gate/check-live-record-claims.py [--quiet]
    python3 scripts/gate/check-live-record-claims.py --brief <path>

Exit status: 0 clean, 1 defect found, 2 environment failure.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

# LJ-1.291/LJ-1.295: the scripts root is found by walking up to
# repo_root.py, never by counting directories.
_HERE = Path(__file__).resolve()
_SCRIPTS = next((p for p in _HERE.parents if (p / "repo_root.py").is_file()), None)
if _SCRIPTS is None:
    raise FileNotFoundError(
        f"no repo_root.py above {_HERE}: refusing to guess the scripts root (C-43)")
sys.path.insert(0, str(_SCRIPTS))
import agents_tree  # noqa: E402
from repo_root import find_root  # noqa: E402

ROOT = find_root(__file__)
PLAN = ROOT / "dev" / "PLAN.md"

HEADING = re.compile(r"^#{2,}\s*LIVE RECORD\b", re.M)
NEXT_HEADING = re.compile(r"^#{1,6}\s", re.M)

# The claim vocabulary, as a trigger table. Each row is measured over the
# 274 live briefs on 2026-08-16 by the [LJ-1.377] probe. ACTIVE rows fire;
# REFUSED rows document why their wider shape cannot (the [LJ-1.212]
# lesson). An ACTIVE row names the episode that earns its place.
CLAIMS: tuple[tuple[str, bool, str], ...] = (
    (r"nobody has run", True,
     "1.1 percent fire; [LJ-1.228] and [LJ-1.230], the probe [LJ-1.124] "
     "had already run"),
    (r"nobody ran", True,
     "0.7 percent fire; the same episode, found by its review [LJ-1.233]"),
    (r"nobody has ever", True,
     "0.7 percent fire; the same claim shape, broader verb"),
    (r"nothing on record", True,
     "0.4 percent fire; [LJ-1.228]'s GOAL, OPEN AND UNPRICED BY ANYTHING"),
    (r"unpriced by any", True,
     "0.4 percent fire; the same line"),
    (r"exists? nowhere", True,
     "1.1 percent fire; [LJ-1.249] and [LJ-1.250], the ep1 chain"),
    (r"nowhere as", True,
     "0.7 percent fire; the same chain"),
    (r"no term exists", True,
     "0.4 percent fire; [LJ-1.246]'s provability claim"),
    (r"never run\b", True,
     "0.4 percent fire; the run-shaped claim without a subject"),
    (r"never measured", True,
     "1.1 percent fire; a figure asserted absent from the record"),
    (r"never written", True,
     "0.4 percent fire; [LJ-1.340], the composite's term"),
    (r"nobody has", False,
     "18.2 percent fire; REFUSED, the ACTIVE narrower forms carry it"),
    (r"never been", False,
     "5.8 percent fire; REFUSED, the phrase is usually about future work"),
    (r"has never been", False,
     "4.4 percent fire; REFUSED, same shape as above"),
)

ACTIVE_CLAIM = re.compile("|".join(t for t, active, _ in CLAIMS if active), re.I)

# A row answers a negative-existence claim only if the row says something
# EXISTS or was DONE. The status is the third cell of a section 11 row.
POSITIVE = re.compile(
    r"\b(GO|GREEN|BUILT|BUILDS|BUILD[S]?|COMPLETE[D]?|DONE|CURED|PRICED|"
    r"SUPPLIED|DELIVERED|LANDED|CLOSE[S]?|BOTH|ALL)\b", re.I)

CAMEL = re.compile(r"(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])")
SPLIT = re.compile(r"[^a-z0-9]+")
CODE = re.compile(r"LJ-1[.-](\d{1,4})\b")
GOAL = re.compile(r"(LJ-[12][.-]\d)\b")

#: MEASURED 2026-08-16 by the [LJ-1.377] probe, and this set is the epoch:
#: every live brief then carrying a trigger with no answered LIVE RECORD
#: section. 74 of 275 briefs, median 4 duties each, maximum 22. Frozen
#: records, reported once, never failed. Do not add. A new lapse is a
#: defect, and that is the point. Both ep3 briefs (LJ-1-228, LJ-1-230) and
#: the ep1 chain (LJ-1-246, LJ-1-249, LJ-1-250) are in the set, which is
#: the catch measured at tree scale. LJ-1-378 is in the set on the
#: LJ-1-212 precedent: authored before this gate landed, it is the gate's
#: FIRST LIVE FIRE, naming goal LJ-1.7 with the open-work list unanswered,
#: which is the ep1 shape itself.
FROZEN = frozenset({
    "LJ-1-160", "LJ-1-161", "LJ-1-162", "LJ-1-163", "LJ-1-164", "LJ-1-165",
    "LJ-1-169", "LJ-1-175", "LJ-1-176", "LJ-1-178", "LJ-1-179", "LJ-1-180",
    "LJ-1-181", "LJ-1-182", "LJ-1-184", "LJ-1-189", "LJ-1-196", "LJ-1-198",
    "LJ-1-200", "LJ-1-210", "LJ-1-215", "LJ-1-217", "LJ-1-218", "LJ-1-222",
    "LJ-1-223", "LJ-1-225", "LJ-1-227", "LJ-1-228", "LJ-1-230", "LJ-1-233",
    "LJ-1-235", "LJ-1-237", "LJ-1-238", "LJ-1-239", "LJ-1-240", "LJ-1-242",
    "LJ-1-246", "LJ-1-247", "LJ-1-248", "LJ-1-249", "LJ-1-250", "LJ-1-251",
    "LJ-1-252", "LJ-1-253", "LJ-1-254", "LJ-1-256", "LJ-1-262", "LJ-1-265",
    "LJ-1-267", "LJ-1-273", "LJ-1-274", "LJ-1-276", "LJ-1-293", "LJ-1-294",
    "LJ-1-297", "LJ-1-298", "LJ-1-299", "LJ-1-300", "LJ-1-301", "LJ-1-302",
    "LJ-1-304", "LJ-1-305", "LJ-1-306", "LJ-1-310", "LJ-1-312", "LJ-1-313",
    "LJ-1-324", "LJ-1-332", "LJ-1-333", "LJ-1-334", "LJ-1-340", "LJ-1-341",
    "LJ-1-365", "LJ-1-378",
})


#: FUNCTION WORDS ARE NOT CONTENT, and the length rule alone cannot tell.
#:
#: The duty fires on TWO shared tokens, so a pair of function words is enough
#: to raise one. MEASURED 2026-08-16: `agents/tasks/LJ-1-384/LJ-1.384.md` was
#: held by `screen:226` on the pair {site, this}, against a screen line reading
#: "At this one site the ratio is 238/186". Both documents are about a site and
#: both use the word "this"; nothing was implicated and there was nothing to
#: answer. The brief already answered the other TEN duties in its
#: `## LIVE RECORD` section, so the gate was red on its own noise.
#:
#: THIS IS THE FAILURE THIS CHECKER WAS DESIGNED AGAINST. `[LJ-1.377]` measured
#: two wider designs at 274 firings out of 274 briefs and refused both, on the
#: finding that a gate which fires on everything trains pasting. A stop list is
#: the same principle applied one level down: a duty raised on "this" teaches a
#: reader that the duties are noise, and then a real one is pasted past.
#:
#: THE LIST IS FUNCTION WORDS ONLY. No domain term is on it, so no duty about
#: the mathematics or the record can be silenced by it.
STOP = frozenset("""
about above after again against also although always among another because
been before being below between both cannot could does doing done down during
each either else enough even ever every from further had has have having here
how however into itself just less like made make many more most much must
never next none nor not now only onto other ought our out over own perhaps
rather same seem shall should since some still such than that their them then
there these they this those though through thus too under until upon very
was were what when where which while who whom whose why will with within
without would yet you your
""".split())


def tokens(text: str) -> set[str]:
    """Content tokens: camelCase split, 4 characters or more, no function word."""
    return {w for w in SPLIT.split(CAMEL.sub(" ", text).lower())
            if len(w) >= 4 and w not in STOP}


class Record:
    """The live record as one brief's writer faced it."""

    def __init__(self, plan_text: str) -> None:
        self.rows: list[tuple[int, str, str, int]] = []  # num, code, row, line
        self.screen: list[tuple[int, str]] = []  # line_no, text
        self.open_work: list[tuple[int, str, int, int]] = []  # n, head, lo, hi
        self.blocked: dict[str, int] = {}  # goal code -> line
        lines = plan_text.splitlines()
        sec11 = None
        in00 = False
        for i, ln in enumerate(lines, 1):
            if ln.startswith("## 11."):
                sec11 = i
            if ln.startswith("## 0.0"):
                in00 = True
                continue
            if in00 and ln.startswith("## "):
                in00 = False
            if in00:
                if ln.strip():
                    self.screen.append((i, ln))
                m = re.match(r"\|\s*`?\[?(LJ-[12][.-]\d)\]?`?\s*\|", ln)
                if m and m.group(1) not in self.blocked:
                    self.blocked[m.group(1)] = i
                continue
            if sec11 and i > sec11:
                m = re.match(r"\|\s*`?\[?LJ-1[.-](\d+)\]?`?\s*\|(.*)", ln)
                if m:
                    self.rows.append(
                        (int(m.group(1)), f"LJ-1.{m.group(1)}", m.group(2), i))
        # open-work items: numbered bold heads inside section 0.0
        text_lines = plan_text.splitlines()
        ow = None
        for i, ln in enumerate(text_lines, 1):
            if "THE OPEN WORK" in ln:
                ow = i
                break
        if ow is not None:
            for i in range(ow, len(text_lines) + 1):
                if i > ow and text_lines[i - 1].startswith("## "):
                    break
                m = re.match(r"\*\*(\d+)\.\s*(.*)", text_lines[i - 1])
                if m:
                    self.open_work.append(
                        (int(m.group(1)), m.group(2).strip(), i, i))


def plan_for(brief: Path) -> str:
    """`dev/PLAN.md` as the brief's writer faced it.

    The parent of the commit that added the brief, so a growing screen
    cannot turn an old compliant brief red. An uncommitted brief gets the
    working tree, which is what its writer faces. Any git failure falls
    back to the working tree rather than guessing an error.
    """
    try:
        tracked = subprocess.run(
            ["git", "ls-files", "--error-unmatch", str(brief)],
            capture_output=True, text=True, cwd=ROOT)
        if tracked.returncode != 0:
            return PLAN.read_text(encoding="utf-8")
        added = subprocess.run(
            ["git", "log", "--diff-filter=A", "--format=%H", "-1", "--",
             str(brief)], capture_output=True, text=True, cwd=ROOT)
        sha = added.stdout.strip()
        if not sha:
            return PLAN.read_text(encoding="utf-8")
        show = subprocess.run(
            ["git", "show", f"{sha}^:dev/PLAN.md"],
            capture_output=True, text=True, cwd=ROOT)
        if show.returncode == 0:
            return show.stdout
    except OSError:
        pass
    return PLAN.read_text(encoding="utf-8")


def live_record_section(text: str) -> str | None:
    hit = HEADING.search(text)
    if hit is None:
        return None
    rest = text[hit.end():]
    nxt = NEXT_HEADING.search(rest)
    return rest if nxt is None else rest[:nxt.start()]


def findings(brief_text: str, rec: Record) -> list[tuple[str, str]]:
    """(label, why) for every live-record object the brief must answer."""
    out: list[tuple[str, str]] = []
    cited = {f"LJ-1.{n}" for n in CODE.findall(brief_text)}
    for i, ln in enumerate(brief_text.splitlines(), 1):
        if not ACTIVE_CLAIM.search(ln):
            continue
        lt = tokens(ln)
        for num, code, row, line in rec.rows:
            if code in cited:
                continue
            cells = row.split("|")
            status = cells[1] if len(cells) > 1 else row
            shared = lt & tokens(row)
            if len(shared) >= 2 and POSITIVE.search(status):
                out.append((code,
                            f"claim line {i} shares "
                            f"{', '.join(sorted(shared))} with a positive "
                            f"row ({status.strip()[:40]}) at PLAN:{line}"))
        for line, text in rec.screen:
            shared = lt & tokens(text)
            if len(shared) >= 2:
                out.append((f"screen:{line}",
                            f"claim line {i} shares "
                            f"{', '.join(sorted(shared))} with the screen "
                            f"at PLAN:{line}"))
    goals = {g for g in GOAL.findall(brief_text)}
    for goal in sorted(goals):
        if goal in rec.blocked:
            out.append((f"blocked:{goal}",
                        f"the brief names goal {goal}, whose blocked row "
                        f"sits at PLAN:{rec.blocked[goal]}"))
        for n, head, lo, _hi in rec.open_work:
            out.append((f"open work item {n}",
                        f"the brief names goal {goal}; item {n} reads "
                        f"\"{head[:60]}\" at PLAN:{lo}"))
    # de-duplicate labels, keeping the first why
    seen: dict[str, str] = {}
    for label, why in out:
        seen.setdefault(label, why)
    return sorted(seen.items())


def unanswered(brief_text: str, found: list[tuple[str, str]]) -> list[tuple[str, str]]:
    section = live_record_section(brief_text)
    if section is None:
        return found
    return [(label, why) for label, why in found if label not in section]


def brief_mode(path: str) -> int:
    p = ROOT / path if not path.startswith("/") else Path(path)
    try:
        text = p.read_text(encoding="utf-8")
    except OSError as exc:
        print(f"check-live-record-claims: {exc}")
        return 2
    rec = Record(plan_for(p))
    found = findings(text, rec)
    if not found:
        print(f"{path}: no trigger, no duty. Adjacency read (advisory):")
    else:
        print(f"{path}: duties a gate would hold:")
        for label, why in found:
            print(f"  - {label}: {why}")
        print("Adjacency read (advisory, never gated):")
    bt = tokens(text)
    cited = {int(n) for n in CODE.findall(text)}
    rowmap = {num: (code, row) for num, code, row, _ in rec.rows}
    adjacents: list[tuple[int, str, str]] = []
    for c in sorted(cited):
        for num in range(max(1, c - 3), c + 4):
            if num in cited or num not in rowmap:
                continue
            code, row = rowmap[num]
            shared = bt & tokens(row)
            if len(shared) >= 3:
                adjacents.append((len(shared), code,
                                  f"{code} (adjacent to LJ-1.{c}) shares "
                                  f"{', '.join(sorted(shared))}"))
    # strongest first, so a cap never hides the densest neighbour
    adjacents.sort(key=lambda t: (-t[0], t[1]))
    for _, _, line in adjacents[:20]:
        print(f"  - {line}")
    if not adjacents:
        print("  (nothing adjacent shares three or more tokens)")
    return 0


def main(argv: list[str]) -> int:
    if "--brief" in argv[1:]:
        return brief_mode(argv[argv.index("--brief") + 1])
    quiet = "--quiet" in argv[1:]
    try:
        files = [p for p in agents_tree.briefs(include_archive=False)]
    except OSError as exc:
        print(f"check-live-record-claims: {exc}")
        return 2
    if not files:
        print("check-live-record-claims: no briefs found")
        return 2
    defects: list[tuple[Path, list[tuple[str, str]]]] = []
    frozen = 0
    for p in files:
        try:
            text = p.read_text(encoding="utf-8")
        except OSError as exc:
            print(f"check-live-record-claims: {exc}")
            return 2
        found = unanswered(text, findings(text, Record(plan_for(p))))
        if not found:
            continue
        if p.parent.name in FROZEN:
            frozen += 1
        else:
            defects.append((p, found))
    if defects:
        print(f"check-live-record-claims: {len(defects)} brief(s) carry a "
              f"trigger and no answered ## LIVE RECORD section; "
              f"{frozen} frozen pre-epoch:", file=sys.stderr)
        for p, found in defects:
            names = ", ".join(label for label, _ in found[:5])
            print(f"  {p.relative_to(ROOT)}: {names}"
                  f"{' ...' if len(found) > 5 else ''}", file=sys.stderr)
        print("", file=sys.stderr)
        print("Answer each flagged object in a ## LIVE RECORD section, one "
              "line each, a quote or a written decline:", file=sys.stderr)
        print("  ## LIVE RECORD", file=sys.stderr)
        print("  - LJ-1.124: <quote or why it does not bear>",
              file=sys.stderr)
        print("  - open work item 1: <quote or why it does not bear>",
              file=sys.stderr)
        print("Run with --brief <path> while writing to see the duties "
              "first.", file=sys.stderr)
        return 1
    print(f"check-live-record-claims: {len(files)} briefs, {frozen} frozen "
          f"pre-epoch with a trigger and no LIVE RECORD section, "
          f"0 new defects" + ("" if quiet else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
