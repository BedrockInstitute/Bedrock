#!/usr/bin/env python3
"""Turns the probe's run rows into the B3 table, so no figure is retyped by hand.

WHY THIS EXISTS. `dev/LESSONS.md` records the measured failure this answers: a standing
figure that nobody computed got re-quoted for nine dispatches, and
`scripts/measure/ledger.py:5-11` carries the same lesson. A probe report that retypes its
own numbers repeats it at a smaller scale. This script reads
`agents/tasks/L9-0/runs/results.tsv` and the reverse import closure at HEAD, then prints
the report table. The report copies its output and nothing else.

THE RATE THIS PRINTS. `seconds per line` divides the wall seconds by the REVERSE-CLOSURE
in-fence lines, because that is the set Agda must re-check and because the three rates that
bracket gap B3 are all seconds over lines. `net` first subtracts the warm floor, which is
the fixed cost of reading 97 interfaces and belongs to no depth class.

Usage: b3-table.py [--runs <dir>]
Exit status: 0 clean, 2 usage error.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, "/Users/alsg/Agentic/Bedrock/scripts/measure")
import ledger  # noqa: E402


def depths() -> tuple[dict[str, int], dict[str, int], dict[str, int]]:
    """Reverse-closure files, reverse-closure lines and own lines, countable caliber."""
    files = ledger.tracked_masters()
    graph = ledger.import_graph(files)
    rev: dict[str, set[str]] = {f: set() for f in files}
    for f, deps in graph.items():
        for d in deps:
            rev[d].add(f)
    sizes = {f: ledger.count(f) for f in files}
    uncounted = set(ledger.UNCOUNTED)
    nfiles, nlines = {}, {}
    for f in files:
        cl = ledger.closure(rev, [f]) - uncounted
        nfiles[f], nlines[f] = len(cl), sum(sizes[c] for c in cl)
    return nfiles, nlines, sizes


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", default="/Users/alsg/Agentic/Bedrock/agents/tasks/L9-0/runs")
    args = ap.parse_args(argv)
    rows = [ln.split("\t") for ln in
            Path(args.runs, "results.tsv").read_text(encoding="utf-8").splitlines()[1:]]
    nfiles, nlines, own = depths()
    warm = [float(r[2]) for r in rows if "warm-nochange" in r[0]]
    floor = min(warm) if warm else 0.0

    print(f"warm floor (min of {len(warm)}): {floor:.2f} s   "
          f"warm runs: {', '.join(f'{w:.2f}' for w in warm)}")
    print(f"{'class':12} {'master':34} {'revF':>5} {'revL':>7} {'own':>6} "
          f"{'sec':>8} {'s/line':>9} {'net s/line':>11}")
    for label, master, sec, rc in rows:
        sec = float(sec)
        if master == "-":
            print(f"{label:12} {'(no edit)':34} {'':>5} {'':>7} {'':>6} {sec:8.2f}")
            continue
        rl = nlines[master]
        print(f"{label:12} {master:34} {nfiles[master]:5d} {rl:7d} {own[master]:6d} "
              f"{sec:8.2f} {sec / rl:9.5f} {(sec - floor) / rl:11.5f}   exit {rc}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
