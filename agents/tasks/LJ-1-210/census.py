#!/usr/bin/env python3
"""[LJ-1.210] in-fence class-name census.

Counts non-blank lines inside ```agda fences (the DD8 method) and, of those,
how many name the constructible class. Run it from the repository root.

    .venv/bin/python agents/tasks/LJ-1-210/census.py src/L/Coding/*.lagda.md
"""

import re
import sys

CLASS = re.compile(r"𝒮ʟ|isL|Lset|𝒟ₒ|LsetS|ʟ\b|AbsL|InL|numeralL|tagAtL|keyʟ")


def fence_lines(path: str) -> list[str]:
    out: list[str] = []
    inside = False
    for line in open(path, encoding="utf-8"):
        stripped = line.rstrip("\n")
        if stripped.startswith("```agda"):
            inside = True
            continue
        if stripped.startswith("```"):
            inside = False
            continue
        if inside and stripped.strip():
            out.append(stripped)
    return out


def main() -> None:
    total = 0
    hit_total = 0
    for path in sys.argv[1:]:
        lines = fence_lines(path)
        hits = [line for line in lines if CLASS.search(line)]
        total += len(lines)
        hit_total += len(hits)
        print(f"{path}\t{len(lines)}\t{len(hits)}")
    print(f"TOTAL\t{total}\t{hit_total}")


if __name__ == "__main__":
    main()
