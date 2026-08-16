#!/usr/bin/env python3
"""LJ-1.357 probe. Re-derive [LJ-1.356] section 7 number 2.

The report claims the DD4 engagement paragraph is "distinct in 241 of 243
briefs" and names a `dd4dup.py` probe. That probe is NOT in
agents/tasks/LJ-1-356/, so the number is not reproducible from the delivered
artifacts. This re-derives it, and also prints the sections for reading.
"""
from __future__ import annotations

import hashlib
import re
import sys
from collections import defaultdict
from pathlib import Path

_HERE = Path(__file__).resolve()
_ROOT = next((p for p in _HERE.parents if (p / "AGENTS.md").is_file()), None)
sys.path.insert(0, str(_ROOT / "scripts"))
import agents_tree  # noqa: E402

DD4 = re.compile(r"^#{2,}\s*DD4\b.*?$(.*?)(?=^#{1,2}\s|\Z)", re.S | re.M)

#: The fixed rule sentence DD4 asks every brief to repeat. Everything that
#: survives its removal is the ENGAGEMENT text the report calls distinct.
FIXED = [
    r"maximi[sz]e the code the two proofs share[^.]*\.",
    r"one rule,? two ends[^.]*\.",
    r"\*\*NAME YOUR AXIS\*\*[^.]*\.",
    r"no metric and no checker",
    r"it has \*\*NO METRIC\*\*[^.]*\.",
]


def tail(sec: str) -> str:
    t = sec
    for rx in FIXED:
        t = re.sub(rx, " ", t, flags=re.I)
    t = re.sub(r"`[^`]*`", " ", t)          # drop inline code and paths
    t = re.sub(r"[*_>#|\-]+", " ", t)
    t = re.sub(r"\s+", " ", t).strip().lower()
    return t


def main(argv: list[str]) -> int:
    show = argv[1:]
    groups: dict[str, list[str]] = defaultdict(list)
    have = 0
    short: list[tuple[str, int]] = []
    for p in agents_tree.briefs(include_archive=False):
        text = p.read_text(encoding="utf-8")
        m = DD4.search(text)
        if not m:
            continue
        have += 1
        t = tail(m.group(1))
        groups[hashlib.sha1(t.encode()).hexdigest()].append(p.parent.name)
        short.append((p.parent.name, len(t.split())))
        if p.parent.name in show:
            print(f"\n--- {p.parent.name} DD4 section, raw ---\n{m.group(1).strip()}")
    dup = {h: c for h, c in groups.items() if len(c) > 1}
    print(f"\nbriefs with a DD4 section: {have}")
    print(f"distinct engagement tails : {len(groups)}")
    print(f"duplicate groups          : {len(dup)}")
    for h, codes in dup.items():
        print(f"  {len(codes)} share one tail: {codes}")
    short.sort(key=lambda x: x[1])
    print("\nthe 15 SHORTEST engagement tails, in words:")
    for name, n in short[:15]:
        print(f"  {n:4d}  {name}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
