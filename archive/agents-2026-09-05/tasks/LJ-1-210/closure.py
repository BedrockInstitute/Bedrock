#!/usr/bin/env python3
"""[LJ-1.210] the class-fixed import closure.

Starts at a master and walks its `open import` / `import` lines through the
tree. It reports the modules that FIX the class, that is the ones that name
`𝒮ʟ` or `isL` inside a ```agda fence. A module that never names the class is
already generic and it is not in the closure.

Run it from the repository root.

    .venv/bin/python agents/tasks/LJ-1-210/closure.py L.Coding.Powerset
"""

import os
import re
import sys

IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.]+)")
CLASS = re.compile(r"𝒮ʟ|isL")


def path_of(mod: str) -> str | None:
    p = os.path.join("src", mod.replace(".", "/") + ".lagda.md")
    return p if os.path.exists(p) else None


def fence_lines(path: str) -> list[str]:
    out: list[str] = []
    inside = False
    for line in open(path, encoding="utf-8"):
        s = line.rstrip("\n")
        if s.startswith("```agda"):
            inside = True
            continue
        if s.startswith("```"):
            inside = False
            continue
        if inside and s.strip():
            out.append(s)
    return out


def main() -> None:
    start = sys.argv[1]
    seen: set[str] = set()
    stack = [start]
    fixed: dict[str, int] = {}
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        p = path_of(mod)
        if p is None:
            continue
        lines = fence_lines(p)
        hits = sum(1 for x in lines if CLASS.search(x))
        if hits:
            fixed[mod] = len(lines)
        for x in lines:
            m = IMPORT.match(x)
            if m:
                stack.append(m.group(1))
    total = 0
    for mod in sorted(fixed):
        print(f"{mod}\t{fixed[mod]}")
        total += fixed[mod]
    print(f"MODULES\t{len(fixed)}")
    print(f"CODE\t{total}")
    print(f"VISITED\t{len(seen)}")


if __name__ == "__main__":
    main()
