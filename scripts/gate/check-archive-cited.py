#!/usr/bin/env python3
"""A brief's ARCHIVE section must cite an ARCHIVE, not only the new route's own tasks.

WHY THIS EXISTS, and it is measured rather than feared. `AGENTS.md` requires
every brief to carry an ARCHIVE section naming what may bear on the task, and
its enforcement is REVIEW ONLY. On 2026-08-13 the owner caught a brief whose
ARCHIVE section named four reports and one archived probe and did NOT name
`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md`, which holds a
DELIVERED, GREEN Cantor-Schroeder-Bernstein at 82 in-fence lines.

`[LJ-1.157]`, an adversarial review at maximum effort, then measured the shape
of the failure and it is not carelessness. **164 of 164 briefs carried the
ARCHIVE heading. The CONTENT decayed while the FORM survived**: after
`[LJ-1.94]` only process tasks cited a retired-route file, and the section's
meaning drifted to "the new route's own prior tasks". Two unbroken runs,
`[LJ-1.95]` to `[LJ-1.125]` and every mathematical brief of `[LJ-1.131]`
onward.

**That is `dev/LESSONS.md` C-41 one level down**: a rule keeps reading true
after the world it described has changed, and nothing notices, because the
heading is still there.

WHAT IT CHECKS, and it is deliberately narrow: a brief has an ARCHIVE section,
and that section cites at least one path under `archive/` or under
`agents/tasks/archive/`. **A section that names only live `agents/tasks/`
directories is the drift, and it is what this prints.**

WHAT IT CANNOT DO, stated because `AGENTS.md` says a row claiming more than its
checker delivers turns a rule into false safety:

  * It cannot tell whether the archive actually BEARS on the task. A brief may
    cite an irrelevant archive file and pass.
  * It cannot tell a process task, which may legitimately have nothing in the
    archive, from a mathematical one that does. **So it REPORTS and never
    gates**, exactly as `check-build-manifest.py` does, and for the same
    reason: a red gate here would train an author to paste a citation rather
    than to survey.
  * It reads the brief, never the return. A brief that cites an archive and a
    return that ignored it both pass.

Its whole claim is that the DRIFT IS VISIBLE. That was the thing missing.
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

ROOT = find_root(__file__)
TASKS = ROOT / "agents" / "tasks"

#: The heading, as `dev/ORCHESTRATION.md` writes it and as every brief carries it.
HEADING = re.compile(r"^#{2,}\s*ARCHIVE\b.*?$(.*?)(?=^#{2,}\s|\Z)", re.S | re.M)

#: A citation of a real archive. `agents/tasks/archive/` counts: a retired task's
#: report is archived material even though it sits under the live tasks tree.
CITE = re.compile(r"\barchive/")


def briefs() -> list[Path]:
    """Every live brief. The archive's own briefs are frozen records, not authored today."""
    out = []
    for d in sorted(TASKS.iterdir()):
        if not d.is_dir() or d.name == "archive":
            continue
        out += sorted(d.glob("[A-Z]*.md"))
    return out


def verdict(path: Path) -> str | None:
    text = path.read_text(encoding="utf-8")
    section = HEADING.search(text)
    if section is None:
        return "no ARCHIVE section at all"
    if not CITE.search(section.group(1)):
        return ("its ARCHIVE section cites no `archive/` path, so it surveyed the new "
                "route's own tasks and not the four archives")
    return None


def main(argv: list[str]) -> int:
    quiet = "--quiet" in argv[1:]
    rows = [(p, why) for p in briefs() if (why := verdict(p))]
    total = len(briefs())

    if rows and not quiet:
        print(f"check-archive-cited: {len(rows)} of {total} live brief(s) did not survey an "
              f"archive:", file=sys.stderr)
        for p, why in rows:
            print(f"  {p.relative_to(ROOT)}\n      {why}", file=sys.stderr)
        print("", file=sys.stderr)
        print("A brief that surveys nothing is how three tasks priced levelIn without the "
              "845-line comparable the route's own recon had already marked ADAPTABLE.",
              file=sys.stderr)
        print("THIS IS A REPORT AND NEVER A GATE. It cannot tell whether an archive bears on "
              "a task, and a red gate would buy a pasted citation rather than a survey.",
              file=sys.stderr)

    # [LJ-1.353] THE NEXT DRIFT DOWN, and the owner found it the same way as the
    # first: by reading a brief this checker had passed. A section citing ONLY
    # `archive/dev/` names the retired route's RECORDS, and a task index cannot
    # lead anybody to a line of archived CODE.
    #
    # THE FOUNDING STORY THIS FILE TOLD FOR MONTHS WAS FALSE, and `[LJ-1.357]`
    # measured it 2026-08-16. Both this printout and the comment here said
    # `[LJ-1.107]` rebuilt 82 lines of CSB because nobody surveyed. It DID
    # survey: `agents/tasks/LJ-1-107/lj-1.107-report.md:235-238` cites the T81
    # survey and names the retired module and its size, "keep ours, 145 lines
    # at the retired `L.Cardinal`", confirmed at
    # `archive/dev/TASKS-archived.md:116`. It then CHOSE to build its own
    # 97-line CSB for h-sets. A choice is not a lapse, and citing it as one
    # taught every reader of this gate a history that did not happen. The
    # levelIn case survives and is now the only case cited.
    # MEASURED 2026-08-16: ten briefs written in one session each cited exactly
    # ONE archive path, eight of them the SAME task index, and none cited a line
    # of archived CODE. One of the ten was a recon into Cantor-Schroeder-
    # Bernstein, which the archive delivers GREEN.
    #
    # This stays ADVISORY for the reason stated above: a red gate buys a pasted
    # citation. What changes is that the number it prints is now the one that
    # correlates with the failure.
    code = [p for p in briefs() if not verdict(p)
            and re.search(r"archive/src/|agents/tasks/archive/", p.read_text(encoding="utf-8"))]
    cited = total - len(rows)
    print(f"check-archive-cited: {cited} of {total} live brief(s) cite an archive, "
          f"and {len(code)} cite archived CODE rather than only the retired route's "
          f"RECORDS (advisory, never a gate)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
