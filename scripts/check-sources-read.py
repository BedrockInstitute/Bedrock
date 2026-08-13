#!/usr/bin/env python3
"""Did the agent actually OPEN the sources its brief named? (DD18)

WHY THIS EXISTS. DD18 makes every brief name what in `archive/` and
`dev/literature/` may bear on the task, and every return say what it used.
`dispatch.py` refuses a brief that omits either section, so the BRIEF half is
mechanical. The RETURN half is review-only, and on 2026-08-10 that gap cost a
day: `[LJ-1.6]` filed a filled ARCHIVE USED section, and the cure it needed had
been sitting in `archive/dev/TASKS-archived.md` for five days.

CITING A SOURCE AND READING IT ARE DIFFERENT THINGS. This script separates
them, using evidence that already exists: the dispatcher keeps the agent's
whole session log, and a file the agent opened appears there inside a TOOL
CALL, not merely in prose.

WHAT IT CANNOT DO, stated plainly so nobody trusts it further than it goes.

  1. It proves a path was OPENED. It cannot prove the agent read the part that
     mattered. `[LJ-1.6]` DID grep the archive, with a topic-shaped pattern
     (`Count|Cardinal|SquareLaw|counting`) piped through `head -30`; the row it
     needed was titled "Re-design the tower-induction gate" and matched none of
     those words. This script would have passed that task.
  2. A miss is a QUESTION, never a verdict. An agent may legitimately skip a
     named source and say why; DD18 asks for WHY NOT, not for compliance.

SO THE SECOND HALF OF THE CURE IS NOT MECHANICAL, and it belongs in the brief:
name the ROW, not just the file, or demand an artifact only reading produces,
a verbatim quote at `file:line` or the answer to a question the file alone
settles. `[LJ-1.19]`'s brief said "FIND IT and cite it at file:line" and the
agent came back with `LevelSigma.lagda.md:203`. That worked.

Usage:
  check-sources-read.py <task>...   one or more task codes, e.g. LJ-1.6
  check-sources-read.py --all       every task with a brief and a log
Exit 0 always: this REPORTS. It is an audit aid, not a gate.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(Path(__file__).resolve().parent))
import agents_tree as T   # [LJ-1.142]: the briefs moved into agents/tasks/<TASK>/
LOGS = ROOT / ".claude" / "skills" / "codex-dispatch" / ".state" / "logs"

# A path the brief names inside its ARCHIVE or LITERATURE section.
PATH_RE = re.compile(r"`([\w./-]+\.(?:md|txt|agda|lagda\.md|toml))`")
SECTION_RE = re.compile(r"^#*\s*(ARCHIVE|LITERATURE)\b(.*?)(?=^#|\Z)",
                        re.S | re.M | re.I)
# The dispatcher logs a shell tool call with this prefix. A path inside one is
# evidence of an OPEN; a path anywhere else is prose, which is what the brief
# and the report both are.
TOOLCALL_RE = re.compile(r"^/bin/\w*sh -lc .*$", re.M)


def named_sources(task: str) -> list[str]:
    brief = T.brief_for(task)
    if brief is None:
        return []
    text = brief.read_text(encoding="utf-8")
    out: list[str] = []
    for _, body in SECTION_RE.findall(text):
        out += PATH_RE.findall(body)
    # de-duplicate, keep order
    seen: set[str] = set()
    return [p for p in out if not (p in seen or seen.add(p))]


def opened(task: str) -> tuple[set[str], int]:
    """Paths appearing inside a tool call, and how many tool calls there were."""
    logs = sorted(LOGS.glob(f"{task}-*.log"))
    if not logs:
        return set(), 0
    text = logs[-1].read_text(encoding="utf-8", errors="replace")
    calls = TOOLCALL_RE.findall(text)
    blob = "\n".join(calls)
    return set(re.findall(r"[\w./-]+\.(?:md|txt|agda|lagda\.md|toml)", blob)), len(calls)


def report(task: str) -> None:
    named = named_sources(task)
    if not named:
        print(f"{task}: no brief, or its DD18 sections name no path")
        return
    seen, ncalls = opened(task)
    if not ncalls:
        print(f"{task}: no session log found")
        return
    # `dev/LESSONS.md` IS SATISFIED BY `scripts/rules.py`, which is the
    # sanctioned path: AGENTS.md says load the rules with `rules.py --for
    # <kind>` and NEVER pick them from memory, and the tool prints each
    # statement. An agent that ran it has read the rules without opening the
    # 125-entry file, and counting that as a miss would push agents toward
    # opening the corpus, which is the exact behaviour the routing exists to
    # prevent. [LJ-1.6] ran `rules.py --for build` eleven times.
    logs = sorted(LOGS.glob(f"{task}-*.log"))
    ran_rules = bool(logs) and "rules.py" in logs[-1].read_text(
        encoding="utf-8", errors="replace")
    hit = [p for p in named
           if any(p in s or s.endswith(p) for s in seen)
           or (ran_rules and p.endswith("LESSONS.md"))]
    miss = [p for p in named if p not in hit]
    print(f"{task}: {len(hit)}/{len(named)} named sources opened, "
          f"{ncalls} tool calls")
    for p in miss:
        print(f"  NOT OPENED  {p}")
    if miss:
        print("  ^ a miss is a QUESTION for the audit, not a verdict. DD18 "
              "allows skipping a source WITH a reason; check the return's "
              "WHY NOT before treating this as a defect.")


def main(argv: list[str]) -> int:
    tasks = argv[1:]
    if not tasks:
        print(__doc__)
        return 0
    if tasks == ["--all"]:
        tasks = sorted({p.stem for p in T.briefs()})
    for t in tasks:
        report(t)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
