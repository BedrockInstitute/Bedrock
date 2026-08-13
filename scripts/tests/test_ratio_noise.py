#!/usr/bin/env python3
"""Regression tests for check-ratio.py's noise reporting, added by [LJ-1.148].

WHY THIS FILE EXISTS. `check-ratio.py` took ONE sample of each module and
printed it as the module's cost. MEASURED 2026-08-13 on
`src/L/Ordinal/StageArith.lagda.md`, 25 cold runs in one series on a quiet
machine: run 1 cost 1.811 s and runs 2 to 25 cost 0.787 s on average. The
first figure is 1.78x DD24's bar and the second is 0.77x. **The same module,
the same tree, the same minute, and opposite verdicts.**

The penalty is a FIXED cost of about 0.9 s on the FIRST Agda invocation of a
series, not a percentage. MEASURED in one invocation over two modules: the
first module spread 79.0 percent and the second 2.0 percent. So the relative
error is set by module size, and a small module is wrecked by it.

WHAT THESE TESTS PIN, and the second is the one that protects the owner.

  1. The tool never invents a band. One sample has NO spread, and the honest
     answer is "unknown", never 0.0. A zero would advertise a perfectly
     repeatable instrument, which is the exact defect this work found.
  2. **A NOISE tag NEVER changes the exit code.** DD24's threshold and its
     tolerance are the owner's and are deferred. This tool reports what it
     knows; it does not rule. A tag that quietly turned a red gate green, or
     a green one red, would be a rule change written as a diagnostic.

Run: `python3 scripts/tests/test_ratio_noise.py`
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
spec = importlib.util.spec_from_file_location(
    "check_ratio", ROOT / "scripts" / "check-ratio.py")
cr = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(cr)

FAILED: list[str] = []


def check(label: str, got, want) -> None:
    ok = got == want
    print(f"  {'ok  ' if ok else 'FAIL'} {label}: want {want} got {got}")
    if not ok:
        FAILED.append(label)


def check_true(label: str, got: bool) -> None:
    check(label, bool(got), True)


class FakeTimer:
    """Stands in for check-timing.time_module, so no Agda runs in a test."""

    def __init__(self, series: dict[str, list[float | None]]):
        self.series = {k: list(v) for k, v in series.items()}
        self.calls: list[str] = []

    def time_module(self, path, cold, ghcrts=None):
        rel = str(Path(path).relative_to(ROOT))
        self.calls.append(rel)
        return self.series[rel].pop(0)


def run_main(argv: list[str], rows) -> tuple[int, str]:
    """main() with Agda, git and the process guard stubbed out."""
    saved = (cr.measure, cr.agda_blocker, sys.argv,
             cr.ledger_mod.validate_ratio_baseline, cr.ledger_mod.count)
    cr.measure = lambda *a, **k: rows
    cr.agda_blocker = lambda: None
    cr.ledger_mod.validate_ratio_baseline = lambda *a, **k: []
    cr.ledger_mod.count = lambda *a, **k: 100
    sys.argv = ["check-ratio.py"] + argv
    buf = io.StringIO()
    try:
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
            code = cr.main()
    finally:
        (cr.measure, cr.agda_blocker, sys.argv,
         cr.ledger_mod.validate_ratio_baseline, cr.ledger_mod.count) = saved
    return code, buf.getvalue()


def main() -> int:
    print("one sample has NO spread, and the tool says unknown rather than zero")
    check("a single sample gives None", cr.spread_of([1.0]), None)
    check("an empty series gives None", cr.spread_of([]), None)
    check("two samples give (max-min)/mean",
          round(cr.spread_of([1.0, 2.0]), 6), round(1.0 / 1.5, 6))
    # THE REAL SERIES, so the arithmetic is pinned against a measurement and
    # not against a hand-made example.
    measured = [1.811] + [0.787] * 24
    check_true("the StageArith series reads above 100 percent",
               cr.spread_of(measured) > 1.0)

    print("the declared band is the MEASURED between-series figure")
    # 12.8 percent: eight separate warmed series on StageArith, spanning about
    # forty minutes, 0.0104 to 0.0118 s per line. The band is
    # BETWEEN-series on purpose: a verdict is one series on one occasion, and
    # a series cannot see how far its own mean sits from the module's cost.
    check("the declared band is the measured one", cr.INSTRUMENT_SPREAD, 0.128)
    check_true("and it says where it came from",
               "MEASURED" in cr.INSTRUMENT_SPREAD_SOURCE)
    check("an unmeasured band cannot flag a row",
          cr.flips_verdict(0.0124, 0.0136, None), False)
    check("a zero band cannot flag a row",
          cr.flips_verdict(0.0124, 0.0136, 0.0), False)

    print("a band flags exactly the rows whose swing crosses the bar")
    # StageArith's own numbers: 0.0105 measured, 0.0136 bar. At the tail's
    # 5.2 percent the verdict holds; at the first-run swing it does not.
    check("a tight tail keeps its UNDER verdict",
          cr.flips_verdict(0.01049, 0.0136, 0.052), False)
    check("the first-run swing crosses the bar",
          cr.flips_verdict(0.01049, 0.0136, 0.40), True)
    check("a row far OVER stays OVER under its own spread",
          cr.flips_verdict(0.0993, 0.0136, 0.20), False)

    print("a series returns every sample, and a failure returns none of them")
    fake = FakeTimer({"src/A.lagda.md": [1.0, 2.0, 3.0]})
    cr._timing = lambda: fake
    saved_count = cr.ledger_mod.count
    cr.ledger_mod.count = lambda *a, **k: 50
    rows = cr.measure(["src/A.lagda.md"], cold=True, runs=3, warmup=False)
    check("three runs give three samples", rows[0][2], [1.0, 2.0, 3.0])
    check("the timer was called three times", len(fake.calls), 3)

    fake = FakeTimer({"src/A.lagda.md": [1.0, None, 3.0]})
    cr._timing = lambda: fake
    rows = cr.measure(["src/A.lagda.md"], cold=True, runs=3, warmup=False)
    # A PARTIAL SERIES IS NOT A MEASUREMENT. Folding a survivor into a mean
    # beside a failure would report a cost for a module that did not check.
    check("a failed run voids the whole series", rows[0][2], None)
    check("the series stops at the failure", len(fake.calls), 2)

    print("the warm-up run is DISCARDED, reported, and taken once per SERIES")
    # THE REAL SHAPE: 1.811 then a tight tail, which is StageArith's series.
    fake = FakeTimer({"src/A.lagda.md": [1.811, 0.787, 0.790],
                      "src/B.lagda.md": [0.500, 0.505]})
    cr._timing = lambda: fake
    rows = cr.measure(["src/A.lagda.md", "src/B.lagda.md"], cold=True, runs=2)
    check("the warm-up is not in the samples", rows[0][2], [0.787, 0.790])
    check("the warm-up is returned so it can be printed", rows[0][3], 1.811)
    check("the second module keeps every sample", rows[1][2], [0.500, 0.505])
    # ONE WARM-UP FOR THE SERIES, not one per module. MEASURED: the second
    # module in a series spreads 2.0 percent and needs none.
    check("the second module has no warm-up of its own", rows[1][3], None)
    check("the timer ran once for warm-up plus twice per module",
          len(fake.calls), 5)

    fake = FakeTimer({"src/A.lagda.md": [1.811, 0.787]})
    cr._timing = lambda: fake
    rows = cr.measure(["src/A.lagda.md"], cold=True, runs=1, warmup=False)
    check("--no-warmup restores the historical single sample",
          rows[0][2], [1.811])
    check("and takes no extra run", len(fake.calls), 1)
    cr.ledger_mod.count = saved_count

    print("--runs must be a real count")
    code, out = run_main(["--module", "src/Landmarks.lagda.md", "--runs", "0"],
                         [("src/Landmarks.lagda.md", 100, [1.0], None)])
    check("--runs 0 is refused", code, 1)
    check_true("the refusal says so", "--runs must be 1 or more" in out)

    print("A NOISE TAG NEVER CHANGES THE EXIT CODE, in either direction")
    # The bar is 0.011828 * 1.15 = 0.013602. A 100-line module at 1.36 s sits
    # on the bar, so any spread at all makes it fragile.
    on_bar = [("src/Landmarks.lagda.md", 100, [1.30, 1.42], None)]
    code, out = run_main(["--module", "src/Landmarks.lagda.md", "--runs", "2",
                          "--check"], on_bar)
    check_true("a fragile row is named NOISE", "NOISE" in out)
    check("a fragile row within the bar still exits 0", code, 0)

    # Far OVER, and fragile is impossible there: the verdict must still fail.
    over = [("src/Landmarks.lagda.md", 100, [9.0, 9.1], None)]
    code, out = run_main(["--module", "src/Landmarks.lagda.md", "--runs", "2",
                          "--check"], over)
    check("a wing far over the bar still exits 1", code, 1)
    check_true("and it is not called NOISE", "NOISE" not in out)

    # Fragile AND over: the tag must not rescue it.
    fragile_over = [("src/Landmarks.lagda.md", 100, [1.37, 1.50], None)]
    code, out = run_main(["--module", "src/Landmarks.lagda.md", "--runs", "2",
                          "--check"], fragile_over)
    check_true("a fragile OVER row is named NOISE", "NOISE" in out)
    check("a fragile row over the bar still exits 1", code, 1)

    print("a tight series NEVER shrinks the band below the measured floor")
    # THE DEFECT THIS PINS: five series spreading 0.6 to 4.0 percent each
    # landed 9.3 percent apart. A row 5 percent from the bar with a 1 percent
    # own-spread is NOT established, and reporting only the own-spread would
    # have called it solid.
    tight = [("src/Landmarks.lagda.md", 100, [1.30, 1.31], None)]
    code, out = run_main(["--module", "src/Landmarks.lagda.md", "--runs", "2"],
                         tight)
    check_true("a tight series near the bar is still NOISE", "NOISE" in out)
    check("and it still exits 0", code, 0)

    print("one run says so, and does not pretend to know its own swing")
    code, out = run_main(["--module", "src/Landmarks.lagda.md",
                          "--runs", "1"], on_bar[:1])
    check_true("a single run advertises n=1", "n=1" in out)
    check_true("and prints the declared floor", "at least" in out)

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
