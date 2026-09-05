#!/usr/bin/env python3
"""[LJ-1.213] non-blank line diff for two plain Agda files.

Usage:
    .venv/bin/python agents/tasks/LJ-1-213/linediff.py A.agda B.agda
Prints added, deleted, unchanged non-blank lines and the changed-line sum.
"""

import sys
from difflib import SequenceMatcher


def nonblank(path: str) -> list[str]:
    with open(path, encoding="utf-8") as fh:
        return [line.rstrip("\n") for line in fh if line.strip()]


def main() -> None:
    a = nonblank(sys.argv[1])
    b = nonblank(sys.argv[2])
    sm = SequenceMatcher(a=a, b=b, autojunk=False)
    added = deleted = unchanged = 0
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            unchanged += i2 - i1
        elif tag == "delete":
            deleted += i2 - i1
        elif tag == "insert":
            added += j2 - j1
        elif tag == "replace":
            deleted += i2 - i1
            added += j2 - j1
    print(f"added={added} deleted={deleted} unchanged={unchanged} touched={added + deleted}")


if __name__ == "__main__":
    main()
