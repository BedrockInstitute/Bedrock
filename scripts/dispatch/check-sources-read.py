#!/usr/bin/env python3
"""Did the agent actually OPEN the sources its brief named? (DD18)

STATUS: UNBUILT, and it gates nothing. The POD cutover of 2026-08-18 replaced
the codex dispatcher with `scripts/pod/launcher.py`. `LOGS` below now points at
the directory the POD writes, but `TOOLCALL_RE` at `:94` is still the CODEX
shell prefix. No Claude head has run through the new launcher, so no transcript
exists to write the Claude shape against. Design section 7.4 of
`dev/memos/L9-pod-program-design.md` and gap M9 schedule that for day 7:
capture one transcript, paste its tool-call line into section 7.4, write the
regex here, and set `REGEX_BUILT` to True. Until then this script prints UNBUILT
and scans nothing, because a codex regex over a Claude transcript reports a
false miss on every named source.

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
Exit 0 always: this REPORTS. It is an audit aid, not a gate. While
`REGEX_BUILT` is False it prints UNBUILT and exits 0 without a scan.
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
from repo_root import find_root  # noqa: E402
import agents_tree as T   # [LJ-1.142]: the briefs moved into agents/tasks/<TASK>/

ROOT = find_root(__file__)
# THE POD WRITES HERE. `scripts/pod/launcher.py:93` sets `LOGS = STATE / "logs"`
# under `<root>/.pod-state`, and it names each file `<task>-<stamp>.log` at
# `launcher.py:1198`, so the glob below still holds. The old target was
# `.claude/skills/codex-dispatch/.state/logs`, which belonged to the codex
# dispatcher. That dispatcher left at the cutover, so the old path is a
# directory nothing writes and every scan of it was a silent empty pass.
LOGS = ROOT / ".pod-state" / "logs"

# THE TOOL-CALL SHAPE IS UNBUILT, and this flag says so instead of passing in
# silence. Set it True in the same edit that writes the Claude tool-call regex,
# on day 7. See the STATUS paragraph of the module docstring.
REGEX_BUILT = False
UNBUILT = "UNBUILT: no Claude transcript exists yet (design section 7.4, gap M9)"

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
    # A task with no transcript is UNBUILT for this check, not a miss. The POD
    # writes one log for each dispatch, so an absent log means the task never
    # ran through the launcher.
    if not sorted(LOGS.glob(f"{task}-*.log")):
        print(f"{task}: {UNBUILT}")
        return
    named = named_sources(task)
    if not named:
        print(f"{task}: no brief, or its DD18 sections name no path")
        return
    seen, ncalls = opened(task)
    if not ncalls:
        print(f"{task}: no session log found")
        return
    # `dev/LESSONS.md` IS SATISFIED BY `scripts/dispatch/rules.py`, which is the
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
    if not REGEX_BUILT:
        print(UNBUILT)
        print("  TOOLCALL_RE is the codex shell prefix and matches no Claude "
              "transcript.")
        print("  A scan with it reports a false miss, so this script scans "
              "nothing.")
        print("  Day 7 writes the regex and sets REGEX_BUILT. Until then this "
              "gates nothing.")
        return 0
    if tasks == ["--all"]:
        tasks = sorted({p.stem for p in T.briefs()})
    for t in tasks:
        report(t)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
