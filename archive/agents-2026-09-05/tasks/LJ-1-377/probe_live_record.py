#!/usr/bin/env python3
"""LJ-1.377 probe: can a matcher connect a brief to the live-record rows it
missed, without firing on every brief?

Measures, over every live brief:
  RULE A (adjacency): the brief cites code LJ-1.N; rows within +-ADJ of N in
    dev/PLAN.md section 11 that share >= MIN_SHARED content tokens with the
    brief and are NOT cited.
  RULE B (overlap): any section-11 row, or any section-0.0 line, sharing
    >= MIN_SHARED content tokens (or >= 1 RARE token, row DF <= RARE_DF)
    with the brief and not cited.

Template tokens are dropped by document frequency over the brief corpus
(baseline-home shape: the threshold is derived from the data, not set).
Known-bad briefs from LJ-1.376's episodes 1, 3, 4 are checked for catches.
"""
from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve()
REPO = next(p for p in HERE.parents if (p / "scripts" / "agents_tree.py").is_file())
SCRIPTS = REPO / "scripts"
sys.path.insert(0, str(SCRIPTS))
import agents_tree  # noqa: E402
from repo_root import find_root  # noqa: E402

ROOT = find_root(__file__)
PLAN = ROOT / "dev" / "PLAN.md"

CAMEL = re.compile(r"(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])")
SPLIT = re.compile(r"[^a-z0-9]+")
CODE = re.compile(r"LJ-1[.-](\d{1,4})")


def tokens(text: str) -> set[str]:
    t = CAMEL.sub(" ", text)
    return {w for w in SPLIT.split(t.lower()) if len(w) >= 4}


def load_plan():
    lines = PLAN.read_text(encoding="utf-8").splitlines()
    sec11 = None
    rows: list[tuple[int, str, str]] = []  # (num, code, text)
    sec00: list[tuple[int, str]] = []  # (line_no, text)
    in00 = False
    for i, ln in enumerate(lines, 1):
        if ln.startswith("## 11."):
            sec11 = i
        if ln.startswith("## 0.0"):
            in00 = True
            continue
        if in00 and ln.startswith("## "):
            in00 = False
        if in00 and ln.strip():
            sec00.append((i, ln))
        if sec11 and i > sec11:
            m = re.match(r"\|\s*`?\[?LJ-1[.-](\d+)\]?`?\s*\|(.*)", ln)
            if m:
                rows.append((int(m.group(1)), f"LJ-1.{m.group(1)}", m.group(2)))
    return rows, sec00


def main() -> int:
    rows, sec00 = load_plan()
    briefs = [p for p in agents_tree.briefs(include_archive=False)]
    texts = {p: p.read_text(encoding="utf-8") for p in briefs}

    # template tokens: in > 15% of briefs
    df = Counter()
    for t in texts.values():
        df.update(tokens(t))
    template = {w for w, c in df.items() if c > 0.15 * len(texts)}
    # row-side common tokens: in > 15% of rows
    row_tokens = {num: tokens(txt) - template for num, _, txt in rows}
    rdf = Counter()
    for s in row_tokens.values():
        rdf.update(s)
    row_common = {w for w, c in rdf.items() if c > 0.15 * len(rows)}

    def content(s: set[str]) -> set[str]:
        return s - template - row_common

    print(f"briefs: {len(texts)}  sec11 rows: {len(rows)}  sec0.0 lines: "
          f"{len(sec00)}")
    print(f"template tokens dropped: {len(template)}; row-common dropped: "
          f"{len(row_common)}")
    print(f"sample template: {sorted(template)[:20]}")

    known_bad = {
        "LJ-1-228": "ep3 (wall already GO)",
        "LJ-1-230": "ep3 (wall already GO)",
        "LJ-1-177": "ep4 (term cured already)",
        "LJ-1-244": "ep1 chain",
        "LJ-1-246": "ep1 chain",
        "LJ-1-249": "ep1 chain",
        "LJ-1-250": "ep1 chain",
    }

    for adj, min_shared, rare_df in ((3, 2, 3), (3, 3, 3), (1, 2, 3), (3, 2, 1)):
        fire_a = fire_b = 0
        catches: dict[str, list[str]] = {}
        noise_sample = []
        for p, t in texts.items():
            cited = {int(n) for n in CODE.findall(t)}
            bt = content(tokens(t))
            fires: list[str] = []
            # RULE A: adjacency
            rowmap = {num: txt for num, _, txt in rows}
            for c in cited:
                for num, code, txt in rows:
                    if abs(num - c) <= adj and num not in cited:
                        shared = bt & content(row_tokens[num])
                        if len(shared) >= min_shared:
                            fires.append(f"A:{code}({','.join(sorted(shared))})")
            # RULE B: overlap anywhere in sec11 + sec0.0 lines
            for num, code, txt in rows:
                if num in cited:
                    continue
                shared = bt & content(row_tokens[num])
                if len(shared) >= min_shared or any(
                        rdf[w] <= rare_df for w in shared):
                    fires.append(f"B:{code}({','.join(sorted(shared))})")
            for lineno, txt in sec00:
                shared = bt & (tokens(txt) - template)
                if len(shared) >= min_shared:
                    fires.append(f"S:{lineno}({','.join(sorted(shared))})")
            if any(f.startswith("A:") for f in fires):
                fire_a += 1
            if any(f.startswith(("B:", "S:")) for f in fires):
                fire_b += 1
            key = p.parent.name
            if key in known_bad:
                catches[key] = fires[:6]
            elif fires and len(noise_sample) < 8:
                noise_sample.append((key, fires[:3]))
        print(f"\n== adj={adj} shared>={min_shared} rare_df<={rare_df} ==")
        print(f"RULE A fires on {fire_a}/{len(texts)} briefs "
              f"({100*fire_a/len(texts):.1f}%)")
        print(f"RULE B fires on {fire_b}/{len(texts)} briefs "
              f"({100*fire_b/len(texts):.1f}%)")
        print("known-bad catches:")
        for k in sorted(known_bad):
            print(f"  {k} [{known_bad[k]}]: {catches.get(k, 'MISSED')}")
        print("noise sample:")
        for k, f in noise_sample:
            print(f"  {k}: {f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
