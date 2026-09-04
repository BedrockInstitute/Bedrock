#!/usr/bin/env python3
"""The one way a script in this repository finds its root.

WHY THIS EXISTS. 24 scripts computed the root as
`Path(__file__).resolve().parent.parent`: a DEPTH, hard-coded 24 times. A
gate copied or moved one level deeper then computed the wrong root, ran its
`git ls-files` against a near-empty tree, and still said `clean`:
[LJ-1.290] MEASURED the copy reporting 55 tracked files where the original
reported 2,369, both exit 0. Nothing in the exit code said which tree was
guarded. That is C-43's shape exactly: the escape hatch a wrong choice
hides in.

THE RULE. Walk up from the file that asks until a marker is found. The
marker is `.git`, and the choice is measured, not tasteful:

  * every gate here runs git or reads the tracked tree, so `.git` is the
    exact precondition for the script to function at all;
  * `.git` is a FILE in a worktree (six live under `.claude/worktrees/`),
    so the test is `exists()`, never `is_dir()`;
  * nothing else under the repository carries a `.git` (MEASURED by find),
    so a walk from any tracked script stops at the true root and cannot
    stop early.

A walk that reaches the top of the filesystem without a marker REFUSES
(C-48: a tool that can read a condition must refuse on it). It never falls
back to a guess: a script run outside a repository must fail loudly, never
guard a tree it guessed at (C-43).

USAGE, two stamped shapes and no judgement in either:

A script that sits FLAT in `scripts/` (this module, `agents_tree.py`) puts
its own directory on `sys.path` and imports:

    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from repo_root import find_root  # noqa: E402

    ROOT = find_root(__file__)

A script that lives in a GROUP directory under `scripts/` (LJ-1.295) finds
the scripts root the same way this module finds the repository root: by
walking up from the file to `repo_root.py` itself, never by counting
directories. The group directory joins `sys.path` too, for siblings
imported by bare name:

    _HERE = Path(__file__).resolve()
    sys.path.insert(0, str(_HERE.parent))
    _SCRIPTS = next((p for p in _HERE.parents
                     if (p / "repo_root.py").is_file()), None)
    if _SCRIPTS is None:
        raise FileNotFoundError("no repo_root.py above " + str(_HERE))
    sys.path.insert(0, str(_SCRIPTS))
    from repo_root import find_root  # noqa: E402

    ROOT = find_root(__file__)

The `sys.path` lines are what make the import survive being run from
anywhere; together with this module they are the whole anchor, and no script
owns a private depth any more.
"""

from __future__ import annotations

from pathlib import Path

MARKER = ".git"


def find_root(start: str | Path | None = None) -> Path:
    """Return the repository root: the nearest ancestor of `start` holding MARKER.

    `start` defaults to this module's own file. Raises FileNotFoundError when
    no ancestor holds the marker: refusing loudly is the contract, so a
    relocated or exported script can never silently guard the wrong tree.
    """
    here = Path(start if start is not None else __file__).resolve()
    for candidate in here.parents:
        if (candidate / MARKER).exists():
            return candidate
    raise FileNotFoundError(
        f"repo_root: no {MARKER} above {here}. This script must run from "
        "inside the repository; refusing to guess the root (C-43, C-48).")
