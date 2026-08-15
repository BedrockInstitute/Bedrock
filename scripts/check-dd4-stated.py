#!/usr/bin/env python3
"""Every brief states DD4. This checks that it was SAID, never how well.

WHY THIS EXISTS, and it is measured rather than feared. DD4 is the route's core
constraint and `dev/PLAN.md` names its enforcement in its own words:

    THE COMPENSATING MECHANISM IS REPETITION, and it is the enforcement point
    this row names: the principle is stated in EVERY brief this project sends,
    whatever the task kind, and every return says what it did about it. A rule
    with no meter has to be said out loud every time or it decays into a
    preference.

**It decayed.** `[LJ-1.183]`, an adversarial audit of the orchestrator, measured
**11 briefs carrying no DD4 at all**, and one more that mentions DD4 with no
section. Every one is dated 2026-08-13. The orchestrator re-ran that census and
got the same 11 codes.

**All 11 are PROCESS tasks**: salvage, memo repair, probe rehoming, a checker,
an audit. Not one writes mathematics.

**So the decay has a shape.** The rule is remembered when the task touches code
and forgotten when it does not, which is the case DD4's row writes 「whatever the
task kind」 to cover. The eleventh is `[LJ-1.157]`, the previous audit OF this
orchestrator's rule compliance, whose brief dropped the rule whose only
enforcement is repetition.

**And the twelfth is the reason this is a checker and not a census.** The audit
counted by MENTION and put `[LJ-1.137]` in a separate row, because it names DD4
in prose and carries no section. A checker reading the HEADING caught it on its
first run.

WHAT THIS CHECKS, and the narrowness is the whole design: a brief has a section
whose heading is `DD4`. That is it.

WHAT THIS REFUSES TO CHECK, because DD4's row rules it out in as many words.
**There is no metric and there never will be.** A shared-line count would be
gamed the moment it gated anything: code can be moved into a shared module
without either proof needing it there, and the number would rise while the
architecture got worse. **This checker therefore reads a HEADING and never a
word of the content.** It cannot tell a brief that thought about reuse from one
that pasted a heading, and pasting a heading is a strictly better failure than
silence, because the next author sees the rule.

WHY A GATE HERE AND NOT A REPORT. `check-archive-cited.py` reports and never
gates, because it cannot tell whether an archive BEARS on a task, so a red gate
there would buy a pasted citation instead of a survey. **Here the check IS the
rule**: DD4 asks that the principle be stated, and a missing heading is a
missing statement, with nothing left to judge.

THE TWELVE ARE FROZEN AND THIS TOOL DOES NOT JUDGE THEM. A brief is a record and
a record is never rewritten, so `PRE_EPOCH` holds the measured twelve and they
are reported once, without failing. Everything authored after them is gated.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agents_tree  # noqa: E402
from repo_root import find_root  # noqa: E402

# LJ-1.291: the root is found by walking up to the repository marker, never by
# counting directories; `scripts/repo_root.py` holds the one walk.
ROOT = find_root(__file__)
TASKS = ROOT / "agents" / "tasks"

#: The heading, in the form every compliant brief already writes.
HEADING = re.compile(r"^#{2,}\s*DD4\b", re.M)

#: MEASURED by `[LJ-1.183]` and re-measured by the orchestrator, 2026-08-14. The
#: twelfth, `LJ-1-137`, is the audit's separate row: it MENTIONS DD4 and carries
#: no section, so the census by mention missed it and this checker caught it.
#: Frozen records: reported, never failed. Do not add to this set. A new lapse
#: is a defect, and that is the whole point of the epoch.
PRE_EPOCH = {
    "LJ-1-132", "LJ-1-133", "LJ-1-137", "LJ-1-138", "LJ-1-139", "LJ-1-140",
    "LJ-1-141", "LJ-1-142", "LJ-1-143", "LJ-1-148", "LJ-1-149", "LJ-1-157",
}


def briefs() -> list[Path]:
    """Every live brief, from the ONE home for that question.

    THIS USED TO ROLL ITS OWN GLOB AND THAT WAS THE DEFECT. `scripts/agents_tree.py`
    exists precisely so a correction reaches every reader at once, and its own
    docstring says so: the brief-versus-report signal was written once when
    `[LJ-1.142]` merged the two trees. This checker and `check-premises-stated.py`
    both bypassed it with `d.glob("[A-Z]*.md")`, so both carried blind spots the
    shared module had already fixed.

    MEASURED 2026-08-15, in one `make check` run: the glob read
    `agents/tasks/LJ-1-275/SupplyNewControl.lagda.md`, a measurement ARM, as a brief
    and demanded a DD4 section from it; and it read `agents/tasks/LJ-1-270/REPORT.md`,
    a report whose name does not end `-report.md`, as a brief too.
    `agents_tree.briefs()` gets both right and has since it was written, because it
    reads CONTENT rather than a name pattern.
    """
    return [p for p in agents_tree.briefs() if "archive" not in p.parts]


def main(argv: list[str]) -> int:
    quiet = "--quiet" in argv[1:]
    missing: list[Path] = []
    grandfathered: list[Path] = []

    for p in briefs():
        if HEADING.search(p.read_text(encoding="utf-8")):
            continue
        (grandfathered if p.parent.name in PRE_EPOCH else missing).append(p)

    total = len(briefs())

    if missing:
        print(f"check-dd4-stated: {len(missing)} brief(s) state no DD4:", file=sys.stderr)
        for p in missing:
            print(f"  {p.relative_to(ROOT)}", file=sys.stderr)
        print("", file=sys.stderr)
        print("DD4 is the route's CORE constraint and repetition is its ONLY enforcement. "
              "It has no metric by the owner's decision, so a brief that does not say it "
              "out loud lets it decay into a preference.", file=sys.stderr)
        print("Write a `## DD4` section. This tool reads the HEADING and never the "
              "content: there is no reuse metric here and there never will be.",
              file=sys.stderr)
        return 1

    note = f", {len(grandfathered)} frozen pre-epoch" if grandfathered and not quiet else ""
    print(f"check-dd4-stated: {total - len(grandfathered)} of {total} live brief(s) state "
          f"DD4{note}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
