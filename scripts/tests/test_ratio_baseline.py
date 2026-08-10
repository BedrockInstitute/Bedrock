#!/usr/bin/env python3
"""Regression tests for DD24's ratio-baseline guard.

WHY THIS FILE EXISTS. On 2026-08-10 `[LJ-0.5]` measured the same tree two ways
and got two ratios: 0.007999 through `make typecheck`, which builds
`src/Everything.lagda.md` and therefore the GCH wing too, and 0.007904 through
`src/Landmarks.lagda.md`, whose import closure is the AC side by structure.
The first inflated the rise by 1.2 percentage points, because its NUMERATOR
carried 582 lines of wing seconds while its DENOMINATOR excluded those lines
by declaration. Unlike compared with unlike, which is the exact error DD24's
baseline exists to prevent.

The guard was rewritten to compare against the ratio's own tree, the cold-build
cone of `ac_baseline_root`. This file pins that behaviour, because the failure
it prevents is SILENT: a stale baseline still parses and still produces a
verdict, which is the C-28 class.

It also pins the distinction that makes the whole thing honest. The cone is
16,916 lines and the AC BUCKET is 16,995; the difference is
`src/Everything.lagda.md`'s own catalog lines, which no Landmarks build
compiles. The owner's compression target is measured on the BUCKET. Swapping
the two would make a bucket move look like progress, which is the trap
`[LJ-0.4]` already hit once with `V.Presentation`.

Run: `python3 scripts/tests/test_ratio_baseline.py`
"""

from __future__ import annotations

import importlib.util
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
spec = importlib.util.spec_from_file_location("ledger", ROOT / "scripts" / "ledger.py")
ledger = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(ledger)

FAILED: list[str] = []


def check(label: str, got, want) -> None:
    ok = got == want
    print(f"  {'ok  ' if ok else 'FAIL'} {label}: want {want} got {got}")
    if not ok:
        FAILED.append(label)


def check_true(label: str, got: bool) -> None:
    check(label, bool(got), True)


def main() -> int:
    data = tomllib.loads(ledger.LEDGER.read_text(encoding="utf-8"))
    ratio = data.get("ratio", {})

    print("the declared baseline is self-consistent")
    root = ratio.get("ac_baseline_root")
    check_true("a root is declared", bool(root))
    check_true("the root is a tracked master", root in ledger.tracked_masters())

    files = [f for f in ledger.countable_masters()
             if f not in set(data.get("retired", []))]
    cone = ledger.closure(ledger.import_graph(ledger.tracked_masters()), [root])
    cone_lines = sum(ledger.count(f) for f in cone if f not in ledger.UNCOUNTED)
    check("ac_baseline_lines IS the cone, not a nearby number",
          ratio.get("ac_baseline_lines"), cone_lines)

    print("the cone excludes the wing, by structure and not by declaration")
    for wing in ratio.get("gch_wing", []):
        check_true(f"{wing} is outside the cone", wing not in cone)

    print("the cone and the AC bucket are ONE number, after the catalog ruling")
    standing = sum(ledger.count(f) for f in files)
    wing_lines = sum(ledger.count(f) for f in ratio.get("gch_wing", []))
    bucket = standing - wing_lines
    # BEFORE 2026-08-10 these differed by 79, exactly Everything's own lines,
    # and both numbers had to be carried under one name. The owner's ruling
    # excludes both catalogs from every size figure and collapses them.
    check("the bucket EQUALS the cone", bucket, cone_lines)
    for cat in ledger.UNCOUNTED:
        check_true(f"{cat} is not in the countable list",
                   cat not in ledger.countable_masters())

    print("the guard is quiet on the declared tree")
    check("no defect at the declared baseline",
          ledger.validate_ratio_baseline(data, standing), [])

    print("the guard fires when the ratio's tree moves")
    slack = ratio.get("ac_baseline_tolerance_lines", 50)
    moved = {**data, "ratio": {**ratio,
                               "ac_baseline_lines": cone_lines + slack + 1}}
    defects = ledger.validate_ratio_baseline(moved, standing)
    check_true("a drift past tolerance is refused", len(defects) == 1)
    check_true("the refusal names the re-measurement task",
               defects and "LJ-0.5" in defects[0])
    check_true("the refusal names the cone, not the bucket",
               defects and "cone" in defects[0])

    print("the guard tolerates noise")
    nudged = {**data, "ratio": {**ratio,
                                "ac_baseline_lines": cone_lines + slack}}
    check("a drift inside tolerance is accepted",
          ledger.validate_ratio_baseline(nudged, standing), [])

    print("the guard stays silent when nothing is declared")
    bare = {**data, "ratio": {k: v for k, v in ratio.items()
                              if k != "ac_baseline_seconds_per_line"}}
    check("an undeclared baseline is not a defect",
          ledger.validate_ratio_baseline(bare, standing), [])

    print()
    if FAILED:
        print(f"FAIL: {len(FAILED)} failing check(s)")
        for f in FAILED:
            print(f"  - {f}")
        return 1
    print("PASS: 0 failing check(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
