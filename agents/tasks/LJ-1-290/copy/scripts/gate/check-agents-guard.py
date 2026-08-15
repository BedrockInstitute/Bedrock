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

TRAILER_RE = re.compile(r"^AGENTS-diff-approved: \d{4}-\d{2}-\d{2}\s*$", re.M)
GUARD_PATH = "scripts/gate/check-agents-guard.py"
# C-41: the guard kept its old home as a second accepted name. Without it,
# every commit made before the move reads as pre-guard and the history audit
# goes green over the whole record. Never drop this line.
GUARD_PATHS = ("scripts/gate/check-agents-guard.py",
               "scripts/gate/check-agents-guard.py")


def git(*args: str) -> str:
    return subprocess.run(["git", *args], capture_output=True, text=True,
                          check=True).stdout


def tree_has_guard(commit: str) -> bool:
    probe = subprocess.run(["git", "cat-file", "-e", f"{commit}:{GUARD_PATH}"],
                           capture_output=True)
    return probe.returncode == 0


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
