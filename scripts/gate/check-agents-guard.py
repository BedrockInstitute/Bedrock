#!/usr/bin/env python3
"""Refuse an unruled edit to AGENTS.md (ruling D34).

WHY THIS EXISTS. AGENTS.md loads into every session of every agent, so a
wrong sentence there governs all work silently. On 2026-08-04 a bulk refresh
wrote "one Agda process at a time" into the rulebook, two days AFTER the
owner had widened the canonical law (LESSONS C-12) to four concurrent
writers. Two later rewrites polished the sentence and nobody re-checked the
claim against its canonical home. The wrong rule then steered dispatch
decisions for three days, until the owner caught it on 2026-08-07. Thirty
commits had touched the file by then, twenty-four of them in four days, and
not one carried a visible warrant.

THE RULE (D34, owner-approved 2026-08-07). An edit to AGENTS.md is shown to
the owner as a diff, with the reason, BEFORE it lands. The commit that lands
it carries a trailer line:

    AGENTS-diff-approved: YYYY-MM-DD

The orchestrator writes the trailer only after the owner's ruling; the
owner's own instruction dictating the change counts as the ruling. The
machine cannot verify that the ruling happened and does not pretend to: the
trailer converts silent drift into an explicit, dated assertion, and
`git log --grep=AGENTS-diff-approved` audits every one in seconds.

TWO MODES.

  (no arguments)      The history audit, run by `make check`. Every commit
                      that touches AGENTS.md and whose own tree contains
                      this checker must carry the trailer. Self-anchoring:
                      a commit from before the guard existed is not judged,
                      and no epoch hash needs pinning.

  --msg-file <path>   The commit-time gate, run by the commit-msg hook.
                      If AGENTS.md is staged, the message at <path> must
                      carry the trailer; otherwise the commit is refused.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

# LJ-1.291: the root is found by walking up to the repository marker, never by
# counting directories; `scripts/repo_root.py` holds the one walk. Every git
# call below runs with cwd=ROOT, so the `AGENTS.md` pathspec resolves from
# the root and never from wherever the caller sits. LJ-1.295:
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

TRAILER_RE = re.compile(r"^AGENTS-diff-approved: \d{4}-\d{2}-\d{2}\s*$", re.M)

#: The homes whose committed trees count as "this guard exists". The first is
#: DERIVED from where this file sits, so a move cannot orphan it; the literal
#: below is the FLAT home this file had until LJ-1.295, kept verbatim because
#: [LJ-1.290] Result 2 MEASURED the false green a lone rewritten literal
#: produces (`0 guarded commit(s)`, exit 0). A commit is judged when its tree
#: carries the guard at any home it has ever had, so history written against
#: the flat layout stays judged after the move.
GUARD_HOMES = list(dict.fromkeys([
    Path(__file__).resolve().relative_to(ROOT).as_posix(),
    "scripts/check-agents-guard.py",
]))


def git(*args: str) -> str:
    return subprocess.run(["git", *args], capture_output=True, text=True,
                          check=True, cwd=ROOT).stdout


def tree_has_guard(commit: str) -> bool:
    for home in GUARD_HOMES:
        probe = subprocess.run(["git", "cat-file", "-e", f"{commit}:{home}"],
                               capture_output=True, cwd=ROOT)
        if probe.returncode == 0:
            return True
    return False


def audit_history() -> int:
    commits = git("log", "--format=%H", "--", "AGENTS.md").split()
    bad: list[str] = []
    for commit in commits:
        if not tree_has_guard(commit):
            continue  # predates the guard; not judged
        message = git("show", "-s", "--format=%B", commit)
        if not TRAILER_RE.search(message):
            subject = git("show", "-s", "--format=%h %s", commit).strip()
            bad.append(subject)
    if bad:
        print("check-agents-guard: FAIL. AGENTS.md was edited without the "
              "owner's dated approval trailer (ruling D34):", file=sys.stderr)
        for line in bad:
            print(f"  {line}", file=sys.stderr)
        print("Each commit that touches AGENTS.md must carry a line "
              "`AGENTS-diff-approved: YYYY-MM-DD`,\nwritten only after the "
              "owner ruled on the presented diff.", file=sys.stderr)
        return 1
    guarded = sum(1 for c in commits if tree_has_guard(c))
    print(f"check-agents-guard: clean ({guarded} guarded commit(s), "
          f"{len(commits) - guarded} pre-guard)")
    return 0


def gate_commit(msg_file: str) -> int:
    staged = git("diff", "--cached", "--name-only").split()
    if "AGENTS.md" not in staged:
        return 0
    with open(msg_file, encoding="utf-8") as fh:
        message = fh.read()
    if TRAILER_RE.search(message):
        return 0
    print("check-agents-guard: REFUSED. This commit edits AGENTS.md and the "
          "message has no\n`AGENTS-diff-approved: YYYY-MM-DD` trailer "
          "(ruling D34).", file=sys.stderr)
    print("Show the owner the diff and the reason first. Add the trailer "
          "only after the ruling.", file=sys.stderr)
    return 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--msg-file", metavar="PATH",
                        help="commit-msg hook mode: the commit message file")
    args = parser.parse_args()
    if args.msg_file:
        return gate_commit(args.msg_file)
    return audit_history()


if __name__ == "__main__":
    sys.exit(main())
