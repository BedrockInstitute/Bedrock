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
import os
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# Set once in main(); recalibrate() has no args to read.
ASSUME_QUIET = False
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

    pgrep exits 0 on a match, 1 on no match, 3 on a fatal error. On a fatal
    error the guard tries `ps` before refusing, because failing closed on an
    unreadable process list made every agent bypass the guard by hand.
    """
    probe = subprocess.run(["pgrep", "-x", "agda"], capture_output=True, text=True)
    if probe.returncode == 0:
        return "another Agda process is live"
    if probe.returncode == 1:
        return None

    # FALLBACK, added 2026-08-12 because failing closed here bought NOTHING.
    # Agent sandboxes have no `sysmond`, so pgrep exits 3 and this guard refused
    # every time. Six consecutive dispatches then neutralised the guard by hand
    # and measured anyway, which is the worst of both: no protection AND, in the
    # returns that did not bypass it, no aggregate at all. A guard that is always
    # bypassed is not a guard. So try a second enumerator before giving up.
    for argv in (["ps", "-eo", "comm="], ["ps", "-A", "-o", "comm="]):
        alt = subprocess.run(argv, capture_output=True, text=True)
        if alt.returncode == 0 and alt.stdout:
            for line in alt.stdout.splitlines():
                if os.path.basename(line.strip()) == "agda":
                    return "another Agda process is live"
            return None

    # Neither enumerator works. Refuse, but say which switch makes the caller
    # take C-12's responsibility deliberately instead of editing the guard out.
    return ("no process enumerator works here (pgrep and ps both failed), so the "
            "guard cannot see a live typecheck. Confirm the machine is quiet and "
            "re-run with --assume-quiet, which records that you took C-12's call")


def measure(paths: list[str], cold: bool,
            ghcrts: str | None = None) -> list[tuple[str, int, float | None]]:
    """(path, in-fence lines, seconds) for each module, in declaration order.

    THE CALIBER COMES FROM THE LEDGER, never from this file's memory. The timer
    defaults to a bare `-M8g`, which is right for the `[[hot]]` rows and wrong
    here: the baseline was taken at the Makefile's exported setting, and the
    two GC flags it adds are worth 22.3 percent (163.49 s against 133.69 s on
    one tree). Timing a wing module without them and judging it against a
    baseline measured with them inflates the wing by up to a fifth.

    THE LINES COME FROM THE WORKING TREE, because the SECONDS do. `ledger.count`
    reads HEAD by default, and that default is right for the ledger and wrong
    here: this tool runs Agda on the files as they sit on disk, so counting HEAD
    pairs a committed numerator's line count with an uncommitted denominator's
    cost. MEASURED 2026-08-12 on [LJ-1.60]: the tool reported
    `0.0136  5,355 lines  73.07 s` for `L.Condensation`, pairing HEAD's 5,355
    lines with the working tree's 207 placed lines' cost. The reading was void
    in the safe direction that time (the corrected aggregate was 0.01214 against
    the printed 0.01248, both within the bar), but a void reading is void in
    whichever direction the tree happens to lean, and this one was being read as
    a gate verdict on whether a placement could proceed.
    """
    timing = _timing()
    out = []
    for rel in paths:
        lines = ledger_mod.count(rel, at_head=False)
        seconds = timing.time_module(ROOT / rel, cold=cold, ghcrts=ghcrts)
        out.append((rel, lines, seconds))
    return out


def recalibrate(cfg: dict) -> int:
    """Measure the AC side at THIS tool's caliber, so the verdict compares like.

    WHY IT EXISTS. `ac_baseline_seconds_per_line` is a WHOLE-CONE rate: one
    cold build, its seconds spread over every line it compiles, so each line
    carries a share of its dependencies. This tool sums module SLICES, each
    timed cold with dependencies WARM, so no line carries any dependency cost.
    P-s says a slice rate does not extrapolate to a tree, and the bias has a
    direction: slices are cheaper, so judging a wing against a cone rate is
    systematically too lenient.

    So the wing needs the AC side measured the SAME way. That is this.

    IT WRITES NOTHING. The orchestrator writes the ledger, because the figure
    and the line count it was taken over must land in one commit or the guard
    goes stale, which is the failure `[LJ-0.5]` spent a day clearing.
    """
    blocker = agda_blocker()
    if blocker and ASSUME_QUIET and "no process enumerator" in blocker:
        print("check-ratio: NO PROCESS ENUMERATOR; proceeding on --assume-quiet. "
              "C-12's call was the caller's, not this tool's.", file=sys.stderr)
        blocker = None
    if blocker:
        print(f"check-ratio: refusing to measure, {blocker} (C-12).", file=sys.stderr)
        return 1
    wing = set(cfg.get("gch_wing", []))
    targets = [f for f in ledger_mod.countable_masters() if f not in wing]
    if not targets:
        print("check-ratio: nothing to recalibrate against.", file=sys.stderr)
        return 1
    ghcrts = cfg.get("ac_baseline_ghcrts")
    print(f"check-ratio --recalibrate | {len(targets)} AC masters | cold, warm "
          f"dependencies | GHCRTS={ghcrts or '-M8g (timer default)'}")
    rows = measure(targets, cold=True, ghcrts=ghcrts)
    lines = sum(n for _, n, s in rows if s is not None and n)
    seconds = sum(s for _, n, s in rows if s is not None and n)
    skipped = [r for r, n, s in rows if s is None or not n]
    if skipped:
        print(f"check-ratio: {len(skipped)} master(s) not measured and EXCLUDED, "
              f"never counted as zero: {', '.join(skipped)}", file=sys.stderr)
    if not lines:
        print("check-ratio: nothing measurable.", file=sys.stderr)
        return 1
    rate = seconds / lines
    print(f"check-ratio: AC side at the module caliber is {rate:.6f} s/line "
          f"over {lines:,} lines and {seconds:.2f} s.")
    print(f"check-ratio: write this into dev/ledger.toml [ratio], WITH the line "
          f"count, in one commit:\n"
          f"    ac_baseline_module_rate = {rate:.6f}\n"
          f"    ac_baseline_module_lines = {lines}")
    return 0


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
    parser.add_argument("--assume-quiet", action="store_true",
                        help="proceed when no process enumerator works, taking C-12's "
                             "call yourself; the run says so in its output")
    parser.add_argument("--recalibrate", action="store_true",
                        help="measure the AC side at THIS tool's caliber and print "
                             "ratio.ac_baseline_module_rate for the ledger. Slow: it "
                             "times every AC master cold. It writes nothing")
    args = parser.parse_args()
    global ASSUME_QUIET
    ASSUME_QUIET = args.assume_quiet

    cfg = config()
    baseline = cfg.get("ac_baseline_seconds_per_line")
    tolerance = cfg.get("tolerance")

    if args.recalibrate:
        return recalibrate(cfg)

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
    # THE STALENESS GUARD IS CALLED, NOT COPIED, and this is the third time the
    # copy cost something. It was duplicated here on purpose, so the measuring
    # instrument would not trust the commit gate. The duplicate then missed the
    # AC-side fix and refused the moment the first wing chapter landed; its own
    # comment recorded the price, "a duplicated guard has to be fixed twice";
    # and on 2026-08-10 it went stale a second time when [LJ-0.5] moved the
    # baseline onto the Landmarks cone, refusing every run until it was found.
    #
    # C-26 is the lesson and the fix is to share the FUNCTION, not the file.
    # The instrument still renders its own verdict; it just stops carrying its
    # own copy of a rule that lives somewhere else.
    with open(LEDGER, "rb") as handle:
        full = tomllib.load(handle)
    standing = sum(ledger_mod.count(f) for f in ledger_mod.countable_masters())
    for defect in ledger_mod.validate_ratio_baseline(full, standing):
        print(f"check-ratio: REFUSING. {defect}", file=sys.stderr)
        return 1

    blocker = agda_blocker()
    if blocker and ASSUME_QUIET and "no process enumerator" in blocker:
        print("check-ratio: NO PROCESS ENUMERATOR; proceeding on --assume-quiet. "
              "C-12's call was the caller's, not this tool's.", file=sys.stderr)
        blocker = None
    if blocker:
        print(f"check-ratio: refusing to measure, {blocker} (C-12).", file=sys.stderr)
        return 1

    # COLD IS THE DEFAULT because the baseline is cold. A warm run against a
    # cold baseline is not a looser check, it is a wrong one: warm is several
    # times faster, so a wing far over the bar reads as under it. The gate was
    # wired warm until [LJ-0.1] caught it.
    cold = not args.warm
    rows = measure(targets, cold=cold, ghcrts=cfg.get("ac_baseline_ghcrts"))

    # THE HEADER MUST ADVERTISE THE BAR THAT IS ACTUALLY APPLIED. It printed
    # the whole-cone rate while the verdict used the module rate, so a reader
    # comparing a flagged row against the header's number compared it against
    # the wrong caliber. That is the same defect this whole section exists to
    # stop, reproduced in the display.
    module_rate = cfg.get("ac_baseline_module_rate")
    judged = module_rate or baseline
    bar = judged * tolerance if tolerance else judged
    caliber = ("module-cold, warm dependencies" if module_rate
               else "WHOLE-CONE, and NOT the caliber these rows are measured at")

    total_lines = 0
    total_seconds = 0.0
    unmeasured = []
    print(f"check-ratio | AC baseline {judged:.4f} s/line ({caliber}) | "
          f"tolerance {tolerance if tolerance else 1.0}x | bar {bar:.4f} s/line "
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

    # THE TWO RATES ARE DIFFERENT INSTRUMENTS, and comparing them was this
    # tool's deepest defect. [LJ-0.5] flagged it on 2026-08-10.
    #
    # `ac_baseline_seconds_per_line` is a WHOLE-CONE rate: one cold build of
    # src/Landmarks.lagda.md, its seconds over every line the build compiles.
    # Each line therefore carries a share of its dependencies' elaboration.
    #
    # The aggregate above is a SUM OF SLICES: each module timed cold with its
    # dependencies WARM, so no line carries any dependency cost at all.
    #
    # P-s says a slice rate does not extrapolate to a tree. I PREDICTED THE
    # DIRECTION AND THE MEASUREMENT REFUTED ME, so the prediction is struck and
    # the number stands in its place.
    #
    # I wrote here that a slice must be CHEAPER than a whole-cone share,
    # because it carries no dependency cost, and that the wing was therefore
    # judged too leniently. `--recalibrate` measured the opposite: the 73 AC
    # masters timed one at a time sum to 193.85 s against the same tree's
    # 133.70 s cold, which is 1.45x, 45 percent MORE. Timing modules
    # separately re-pays a fixed cost 73 times over, chiefly loading each
    # module's dependency interfaces from disk on every invocation, and that
    # dwarfs the dependency-share effect I reasoned from.
    #
    # So the slice caliber is systematically STRICTER, not more lenient, and a
    # wing judged against the whole-cone rate would have been judged too
    # HARSHLY. Which is why the tool refused to judge at all rather than pick a
    # caliber: the sign of the error was not knowable without measuring it.
    #
    # SO THE VERDICT NEEDS A MODULE-CALIBER BASELINE: the AC side measured the
    # same way, per module, cold with warm dependencies, at the same GHCRTS.
    # `--recalibrate` produces it. Until it is declared this tool REPORTS and
    # refuses to judge, because a confident wrong verdict is worse than none.
    if module_rate:
        module_bar = bar
        verdict = "OVER THE BAR" if aggregate > module_bar else "within the bar"
        print(f"check-ratio: wing aggregate {aggregate:.4f} s/line over "
              f"{total_lines:,} lines and {total_seconds:.2f} s, {verdict} "
              f"({aggregate / module_rate:.2f}x the AC side at the SAME "
              f"caliber, module-cold with warm dependencies)")
    else:
        print(f"check-ratio: wing aggregate {aggregate:.4f} s/line over "
              f"{total_lines:,} lines and {total_seconds:.2f} s. "
              f"NO VERDICT: this is a sum of module SLICES and the declared "
              f"baseline {baseline:.4f} is a WHOLE-CONE rate. A slice carries "
              f"no dependency cost, so the comparison is systematically too "
              f"lenient (P-s). Run --recalibrate and declare "
              f"ratio.ac_baseline_module_rate.")
        print(f"check-ratio: for scale only, NOT a judgment, the whole-cone "
              f"baseline is {baseline:.4f} s/line and this aggregate is "
              f"{aggregate / baseline:.2f}x it.")
        if args.check:
            print("check-ratio: --check cannot render a verdict without a "
                  "module-caliber baseline, and fails closed rather than "
                  "judge at the wrong caliber.", file=sys.stderr)
            return 1
        return 0

    if aggregate > module_bar and args.check:
        print("check-ratio: DD24 is the only threshold on this wing and the "
              "wing is over it. There is no line cap and no seconds cap to "
              "trade against; the content class has to change. Read P-m, P-q "
              "and P-t before optimizing: a line lever is not a seconds "
              "lever.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
