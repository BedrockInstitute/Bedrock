#!/usr/bin/env python3
"""DD24's seconds-per-line bar, checkable at every stage of the build.

WHY THIS EXISTS. The owner ruled on 2026-08-09 that the internalization GCH
wing carries ONE threshold and only one: the ratio of build seconds to
in-fence lines, matched against the delivered internalization AC wing. It
carries NO separate line cap and NO separate seconds cap, and that omission
is deliberate. Task 5 exists to MEASURE what a GCH wing costs. A cap on its
lines or its seconds would make the measurement report the cap instead of the
cost, which is the failure this repository has already paid for twice.

WHY A RATIO IS THE RIGHT SINGLE BAR. A total can be met by writing less of a
worse thing; a ratio cannot. `dev/LESSONS.md` P-m measured that a rate
certifies a content class: parameterized work runs about 0.010 to 0.013
seconds per line and instantiation about 0.22 to 0.297, a twentyfold spread
that no line count reveals. P-t then measured a twentyeightfold spread inside
ONE file, so the carrier never certifies the class and the formula does. The
ratio is the only cheap number that sees any of this.

WHY IT IS STAGED. A bar that can only be read when the wing is finished is a
bar that is read too late to act on. This tool runs from the first GCH module
onward: it reports every module it can see, flags each one against the bar,
and judges the wing on the aggregate. Before any GCH module exists it reports
that fact and exits 0.

IT IS NOT IN `make check`, and MEASURES COLD BY DEFAULT. Both were wrong for
one day and [LJ-0.1] caught both. It runs Agda, so it cannot live in the
commit gate: `dev/ORCHESTRATION.md` forbids a typecheck there, and this tool
fails closed beside a live agda process, which would turn a busy machine into
a red commit. And the baseline is COLD, so a warm run is not a looser
comparison, it is a meaningless one.

WHAT IT REFUSES. It refuses to invent a baseline. If the ledger has no
measured AC ratio it says so and fails, because a bar guessed from a
comparable is a hypothesis and not a price (P-l). It refuses to run beside
another Agda process (C-12). It never writes to the ledger.

THE PER-MODULE FLAG IS ADVICE; THE AGGREGATE IS THE JUDGMENT. A single module
may sit above the bar for a reason the wing as a whole pays back, which is
exactly what a shared parameterized core does for its instantiations. Only the
aggregate fails the run.
"""

from __future__ import annotations

import argparse
import importlib.util
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "dev" / "ledger.toml"
sys.path.insert(0, str(Path(__file__).resolve().parent))

import ledger as ledger_mod  # noqa: E402  (sibling import; never re-implement the count)


def _timing():
    """scripts/check-timing.py, loaded by path because of the hyphen.

    Its `time_module` is the ONLY module timer in this repository and it stays
    that way. A second implementation drifts, which is the defect class this
    repository keeps finding (C-26).
    """
    spec = importlib.util.spec_from_file_location(
        "check_timing", Path(__file__).resolve().parent / "check-timing.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def config() -> dict:
    """The `[ratio]` table, or an empty one when undeclared."""
    with open(LEDGER, "rb") as handle:
        return tomllib.load(handle).get("ratio", {})


def agda_blocker() -> str | None:
    """The reason a run is refused, or None when no Agda process is live.

    pgrep exits 0 on a match, 1 on no match, 3 on a fatal error. The guard
    fails closed: a guard that cannot see the process list refuses, because
    its one job is to not run beside another typecheck (C-12).
    """
    probe = subprocess.run(["pgrep", "-x", "agda"], capture_output=True, text=True)
    if probe.returncode == 0:
        return "another Agda process is live"
    if probe.returncode == 1:
        return None
    return "pgrep cannot verify the process list; the guard fails closed"


def measure(paths: list[str], cold: bool) -> list[tuple[str, int, float | None]]:
    """(path, in-fence lines, seconds) for each module, in declaration order."""
    timing = _timing()
    out = []
    for rel in paths:
        lines = ledger_mod.count(rel)
        seconds = timing.time_module(ROOT / rel, cold=cold)
        out.append((rel, lines, seconds))
    return out


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--check", action="store_true",
                        help="gate mode: exit non-zero when the wing is over the bar")
    parser.add_argument("--warm", action="store_true",
                        help="reuse existing interfaces; fast, and NOT comparable "
                             "to the cold baseline. For a quick look only")
    parser.add_argument("--module", action="append", default=[],
                        help="measure this master instead of the declared wing; repeatable")
    args = parser.parse_args()

    cfg = config()
    baseline = cfg.get("ac_baseline_seconds_per_line")
    tolerance = cfg.get("tolerance")

    targets = args.module or cfg.get("gch_wing", [])
    if not targets:
        print("check-ratio: no GCH-wing module declared yet (ratio.gch_wing is "
              "empty), so there is nothing to measure. This is the expected "
              "state until LJ-1.3 lands its first module.")
        return 0

    missing = [t for t in targets if not (ROOT / t).exists()]
    if missing:
        for m in missing:
            print(f"check-ratio: declared module is not in the tree: {m}",
                  file=sys.stderr)
        return 1

    if baseline is None:
        print("check-ratio: ratio.ac_baseline_seconds_per_line is not declared. "
              "DD24's bar is a MEASUREMENT of the delivered AC wing, and this "
              "tool will not invent one from a comparable (P-l).", file=sys.stderr)
        return 1

    # THE BASELINE BELONGS TO ONE TREE. Refuse it on another, and refuse HERE
    # as well as in ledger.py --check, because this is the tool that actually
    # renders a verdict. A guard that lives only in the commit gate leaves the
    # measuring instrument free to print a wrong number when run by hand.
    declared_lines = cfg.get("ac_baseline_lines")
    if declared_lines:
        standing = sum(ledger_mod.count(f) for f in ledger_mod.tracked_masters())
        slack = cfg.get("ac_baseline_tolerance_lines", 50)
        if abs(standing - declared_lines) > slack:
            print(f"check-ratio: REFUSING. The baseline {baseline:.6f} s/line was "
                  f"measured over {declared_lines:,} in-fence lines; the tree now "
                  f"stands at {standing:,}. Both terms of the ratio moved and "
                  f"neither moved predictably (P-q: 315 lines removed bought "
                  f"11.8 s). Re-measure at [LJ-0.5] and write the new figure and "
                  f"ac_baseline_lines TOGETHER.", file=sys.stderr)
            return 1

    blocker = agda_blocker()
    if blocker:
        print(f"check-ratio: refusing to measure, {blocker} (C-12).", file=sys.stderr)
        return 1

    # COLD IS THE DEFAULT because the baseline is cold. A warm run against a
    # cold baseline is not a looser check, it is a wrong one: warm is several
    # times faster, so a wing far over the bar reads as under it. The gate was
    # wired warm until [LJ-0.1] caught it.
    cold = not args.warm
    rows = measure(targets, cold=cold)
    bar = baseline * tolerance if tolerance else baseline

    total_lines = 0
    total_seconds = 0.0
    unmeasured = []
    print(f"check-ratio | AC baseline {baseline:.4f} s/line | tolerance "
          f"{tolerance if tolerance else 1.0}x | bar {bar:.4f} s/line "
          f"| {'cold' if cold else 'WARM, NOT COMPARABLE'}")
    for rel, lines, seconds in rows:
        if seconds is None or not lines:
            unmeasured.append(rel)
            print(f"  {'?':>9}  {lines:6,} lines  {rel}  (not measured)")
            continue
        total_lines += lines
        total_seconds += seconds
        ratio = seconds / lines
        flag = "OVER " if ratio > bar else "     "
        print(f"  {flag}{ratio:.4f}  {lines:6,} lines  {seconds:8.2f} s  {rel}")

    if unmeasured:
        # A module that could not be timed is EXCLUDED from the aggregate and
        # said so, never folded in at zero. A silent zero would make the wing
        # look cheaper the more of it failed to measure.
        print(f"check-ratio: {len(unmeasured)} module(s) not measured and "
              f"EXCLUDED from the aggregate, not counted as zero: "
              f"{', '.join(unmeasured)}", file=sys.stderr)

    if not total_lines:
        print("check-ratio: nothing measurable in the declared wing.", file=sys.stderr)
        return 1

    aggregate = total_seconds / total_lines
    verdict = "OVER THE BAR" if aggregate > bar else "within the bar"
    print(f"check-ratio: wing aggregate {aggregate:.4f} s/line over "
          f"{total_lines:,} lines and {total_seconds:.2f} s, {verdict} "
          f"({aggregate / baseline:.2f}x the AC wing)")

    if aggregate > bar and args.check:
        print("check-ratio: DD24 is the only threshold on this wing and the "
              "wing is over it. There is no line cap and no seconds cap to "
              "trade against; the content class has to change. Read P-m, P-q "
              "and P-t before optimizing: a line lever is not a seconds "
              "lever.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
