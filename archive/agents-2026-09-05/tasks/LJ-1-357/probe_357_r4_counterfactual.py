#!/usr/bin/env python3
"""LJ-1.357 probe. Run R4 on named briefs, to test [LJ-1.356]'s counterfactual.

[LJ-1.356] section 2 claims R4 "is what would have stopped [LJ-1.107]".
That claim was never run. This runs it, with the prototype's own code.
"""
from __future__ import annotations

import sys
from pathlib import Path

_HERE = Path(__file__).resolve()
_ROOT = next((p for p in _HERE.parents if (p / "AGENTS.md").is_file()), None)
sys.path.insert(0, str(_ROOT / "scripts"))
sys.path.insert(0, str(_HERE.parent))
import agents_tree  # noqa: E402
import probe_357_rerun as P  # noqa: E402


def main(argv: list[str]) -> int:
    live = [(p, p.read_text(encoding="utf-8"))
            for p in agents_tree.briefs(include_archive=False)]
    df = P.doc_frequency(live)
    wanted = set(argv[1:]) or {"LJ-1-107"}
    for p, text in live:
        if p.parent.name not in wanted:
            continue
        print(f"\n=== {p.parent.name}: {p} ===")
        sec = P.section_of(text, "ARCHIVE")
        print(f"  R1: {P.r1_defects(p, text) or ['PASS']}")
        print(f"  ARCHIVE section length: {len(sec)} chars")
        words = {}
        for w in P.IDENT.findall(text):
            if df.get(w.lower(), 0) > max(3, 0.15 * len(live)):
                continue
            words[w] = words.get(w, 0) + 1
        keep = sorted((w for w, n in words.items() if n >= 2),
                      key=lambda w: -words[w])[:10]
        print(f"  R4 kept terms: {keep}")
        cands = P.r4_candidates(p, text, df, len(live))
        print(f"  R4 MISSED CANDIDATES: {cands or 'NONE'}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
