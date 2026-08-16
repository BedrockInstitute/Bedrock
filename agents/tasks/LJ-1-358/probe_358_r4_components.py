#!/usr/bin/env python3
"""PROBE, unwired (LJ-1.358). R4 with the synonym cure `[LJ-1.357]` upheld.

The diagnosis it upheld: the archive spells the theorem
"Cantor-Schroeder-Bernstein" (`L/Cardinal.lagda.md:7`) and briefs say
"Cantor-Bernstein", so an exact-term grep misses the file that holds the
proof. The cure follows from the diagnosis: match on HYPHEN COMPONENTS, so
"Cantor-Bernstein" contributes {cantor, bernstein} and any file holding both
components in one token matches.

This probe re-runs R4's LJ-1.353 decisive case with component matching and
answers one question: does the file that HOLDS the proof now print, and how
much noise prints beside it? The refuted counterfactual ("it would have
stopped `[LJ-1.107]`") is NOT re-tested: `[LJ-1.357]` measured that a brief
which never names its subject keeps zero terms, and that stands.
"""

from __future__ import annotations

import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

_HERE = Path(__file__).resolve()
_ROOT = next((p for p in _HERE.parents if (p / "AGENTS.md").is_file()), None)
if _ROOT is None:
    raise FileNotFoundError(f"no repo root above {_HERE}")
sys.path.insert(0, str(_ROOT / "scripts"))
import agents_tree  # noqa: E402

ROOT = _ROOT
ARCHIVE_SRC = ROOT / "archive" / "src"
IDENT = re.compile(r"\b(?:[a-z]+[A-Z][A-Za-z-]{4,}|[A-Z][a-z]+-[A-Z][A-Za-z-]{3,})\b")


def components(term: str) -> set[str]:
    return {p for p in term.lower().split("-") if len(p) >= 4}


def main(argv: list[str]) -> int:
    target = Path(argv[1]) if len(argv) > 1 else ROOT / "agents/tasks/LJ-1-353/LJ-1.353.md"
    text = target.read_text(encoding="utf-8")
    live = [(p, p.read_text(encoding="utf-8")) for p in agents_tree.briefs(include_archive=False)]
    df: dict[str, int] = defaultdict(int)
    for _, t in live:
        for w in set(w.lower() for w in IDENT.findall(t)):
            df[w] += 1
    total = len(live)
    words = defaultdict(int)
    for w in IDENT.findall(text):
        if df.get(w.lower(), 0) > max(3, 0.15 * total):
            continue
        words[w] += 1
    keep = sorted((w for w, n in words.items() if n >= 2), key=lambda w: -words[w])[:10]
    print(f"brief: {target.relative_to(ROOT)}")
    print(f"kept terms: {keep}")
    cited = set(re.findall(r"(?:archive|agents/tasks/archive)/[A-Za-z0-9./_-]+", text))
    for w in keep:
        comps = components(w)
        if not comps:
            continue
        # Intersect per-component greps, so the hyphen order never matters:
        # "Cantor-Schroeder-Bernstein" matches {cantor, bernstein}.
        sets = []
        for c in sorted(comps):
            out = subprocess.run(["grep", "-ril", "--", c, str(ARCHIVE_SRC)],
                                 capture_output=True, text=True, timeout=30)
            sets.append({Path(x).relative_to(ROOT).as_posix()
                         for x in out.stdout.splitlines()})
        files = sorted(set.intersection(*sets)) if sets else []
        new = [f for f in files if f not in cited]
        print(f"\n  {w}: {len(files)} file(s), {len(new)} uncited")
        for f in new[:8]:
            print(f"    UNCITED: {f}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
