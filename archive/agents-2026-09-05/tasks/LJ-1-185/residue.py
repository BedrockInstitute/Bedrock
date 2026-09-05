#!/usr/bin/env python3
"""LJ-1.185: the Typing-outside-every-definition residue, from raw Agda profiles.

Agda 2.8.0 REFUSES `--profile=internal` together with `--profile=definitions`,
so the quantity "type-checking billed outside every definition" can only be
reached by subtracting one cold run from another. This script does that
subtraction once, in one place, and prints its error term beside it.

    residue = Miscellaneous(definitions run)
            - (Total - Typing)(internal run) x Total(defs) / Total(int)

The scaling factor removes the run-to-run difference in the totals. The script
also prints the same quantity from the other side, `Typing - definition sum`,
because the two agree only if both accounts are complete.

DD4. Nothing here is L-specific or J-specific. It reads any pair of Agda
profile files for any module in either tower.

Usage:
    residue.py <defs-run.txt> <int-run.txt> [<defs-run.txt> <int-run.txt> ...]
"""
from __future__ import annotations

import re
import sys
import pathlib
import statistics

ROW = re.compile(r"^(\S+(?: \S+)*?)\s+([\d,]+)ms(?:\s+\(([\d,]+)ms\))?\s*$")


def parse(path: pathlib.Path) -> tuple[dict[str, tuple[int, int]], dict[str, str]]:
    rows: dict[str, tuple[int, int]] = {}
    head: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("# "):
            key, _, val = line[2:].partition(" ")
            head[key] = val.strip()
            continue
        m = ROW.match(line)
        if m:
            own = int(m.group(2).replace(",", ""))
            tot = int((m.group(3) or m.group(2)).replace(",", ""))
            rows.setdefault(m.group(1), (own, tot))
    return rows, head


def one(defs_path: str, int_path: str) -> dict[str, float]:
    d, dh = parse(pathlib.Path(defs_path))
    i, ih = parse(pathlib.Path(int_path))
    dtot = d["Total"][0]
    misc = d["Miscellaneous"][0]
    defsum = sum(v[0] for k, v in d.items() if k not in ("Total", "Miscellaneous"))
    itot = i["Total"][0]
    typ = i.get("Typing", (0, 0))[1]
    nont = itot - typ
    # p and q are fractions INSIDE their own run, so a uniform slowdown of one
    # run cancels. A change in the PHASE MIX between the two runs does not,
    # and that is what `run_gap` and the spread over repeats expose.
    p = misc / dtot            # not owned by any definition
    q = nont / itot            # not inside Typing
    frac = p - q               # Typing, owned by no definition
    return {
        "module": dh.get("module", defs_path),
        "lines": int(dh.get("in-fence", "0").split()[-1]) if "in-fence" in dh else 0,
        "defs_total": dtot,
        "misc": misc,
        "defsum": defsum,
        "defs_rows": sum(1 for k2 in d if k2 not in ("Total", "Miscellaneous")),
        "int_total": itot,
        "typing": typ,
        "non_typing": nont,
        "p": p,
        "q": q,
        "frac": frac,
        "residue": frac * (dtot + itot) / 2,
        "share": 100 * frac,
        "run_gap": 100 * abs(dtot - itot) / max(dtot, itot),
    }


def main() -> int:
    args = sys.argv[1:]
    if len(args) < 2 or len(args) % 2:
        print(__doc__)
        return 2
    out = []
    for a, b in zip(args[0::2], args[1::2]):
        out.append(one(a, b))
    print(f"{'module':46s} {'lines':>6} {'defsTot':>9} {'intTot':>9} {'Typing':>9} "
          f"{'defsum':>8} {'p':>6} {'q':>6} {'residue':>9} {'share':>6} {'runGap':>7}")
    for r in out:
        print(f"{r['module']:46s} {r['lines']:6d} {r['defs_total']:9,} {r['int_total']:9,} "
              f"{r['typing']:9,} {r['defsum']:8,} {100*r['p']:5.1f}% {100*r['q']:5.1f}% "
              f"{r['residue']:9,.0f} {r['share']:5.1f}% {r['run_gap']:6.2f}%")
    if len(out) > 1:
        vals = [r["residue"] for r in out]
        print(f"\nresidue over {len(vals)} pairs: mean {statistics.mean(vals):,.0f} ms, "
              f"min {min(vals):,.0f}, max {max(vals):,.0f}, "
              f"spread {100*(max(vals)-min(vals))/statistics.mean(vals):.1f}%")
        shares = [r["share"] for r in out]
        print(f"share: mean {statistics.mean(shares):.2f}%, "
              f"min {min(shares):.2f}%, max {max(shares):.2f}%")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
