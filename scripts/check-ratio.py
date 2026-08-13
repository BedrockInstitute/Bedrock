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

IT REPORTS ITS OWN UNCERTAINTY, added 2026-08-13 by [LJ-1.148]. One run of one
module is one sample of a noisy instrument, and this tool used to print that
sample as though it were the module's cost. It was not: the SAME module, on
the SAME instrument, at the SAME GHCRTS, hours apart, has already flipped a
DD24 verdict. `[LJ-1.135]` measured src/L/Ordinal/StageArith.lagda.md at
0.0144 s per line, which is OVER the 0.0136 bar; the orchestrator measured it
at 0.0124 the same day, which is UNDER. Nothing in the tree changed.

So the tool now says how many runs a figure rests on, and marks a row whose
verdict the instrument's own swing can flip. It STILL RENDERS THE SAME
VERDICT and returns the SAME exit code: DD24's threshold and its tolerance are
the owner's and are untouched. A NOISE tag is information, never a ruling.
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

# THE INSTRUMENT'S OWN REPEATABILITY, as a fraction of a module's seconds.
#
# MEASURED 2026-08-13 by [LJ-1.148] on a quiet machine, load 3.1 to 3.6, and
# it is the BETWEEN-SERIES figure rather than the within-series one. That
# choice is the whole point of the constant.
#
# `src/L/Ordinal/StageArith.lagda.md`, EIGHT separate warmed series over about
# forty minutes, nothing in the tree changing: 0.0104 / 0.0104 / 0.0105 /
# 0.0106 / 0.0107 / 0.0114 / 0.0115 / 0.0118 s per line. Range 12.8 percent of
# the mean, relative standard deviation 5.2 percent. WITHIN any one of those
# series the spread was 0.5 to 4.0 percent, so a series cannot see its own
# displacement and reports a false confidence. A verdict is ONE series on ONE
# occasion, so the between-series figure is the one that governs it.
#
# THE FIRST VALUE OF THIS CONSTANT WAS 9.3 PERCENT, from the first five series,
# and the sixth series broke it within the hour. It is written at 12.8 rather
# than rounded down, and it is still a floor rather than a ceiling.
#
# NOT SEEDED FROM THE SPREADS ON RECORD, and P-l is why. `[LJ-1.135]` measured
# 5.5 percent over four runs and `[LJ-1.128]` 3.7 percent over five, but both
# are the spread of a SUM over many masters, and independent per-module noise
# averages DOWN as you sum. A sum's spread is a LOWER BOUND on one module's,
# so either would have understated this band in the direction that produces
# confident wrong verdicts.
#
# IT IS STILL A LOWER BOUND. It is one module, on one machine, on one day, and
# the BASELINE carries its own spread that this figure does not include.
INSTRUMENT_SPREAD: float | None = 0.128
INSTRUMENT_SPREAD_SOURCE = (
    "MEASURED [LJ-1.148] 2026-08-13, eight separate warmed series on "
    "src/L/Ordinal/StageArith.lagda.md, quiet machine")
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


def spread_of(samples: list[float]) -> float | None:
    """(max - min) / mean, or None from a single sample.

    ONE SAMPLE HAS NO SPREAD, and returning 0.0 here would be the whole defect
    this function exists to expose: a single run would advertise a perfectly
    repeatable instrument. None means "this run cannot tell you", which is the
    true answer.
    """
    if len(samples) < 2:
        return None
    mean = sum(samples) / len(samples)
    return (max(samples) - min(samples)) / mean if mean else None


def flips_verdict(ratio: float, bar: float, spread: float | None) -> bool:
    """Can the instrument's swing move this row across the bar?

    THE SWING IS IN THE MEASUREMENT, not in the bar, so the band is anchored on
    the measured ratio: the verdict is fragile when the bar sits inside
    ratio * (1 +- spread).

    THIS IS A LOWER BOUND ON THE UNCERTAINTY and the tool never pretends
    otherwise. The BASELINE is a measurement too and carries its own spread
    (`[LJ-1.135]` measured 5.5 percent over four runs of the whole AC set), and
    that half is not in this band. A row this function calls solid may still be
    fragile once the bar's own noise is counted.
    """
    if spread is None or spread <= 0:
        return False
    return ratio * (1 - spread) <= bar <= ratio * (1 + spread)


def measure(paths: list[str], cold: bool, ghcrts: str | None = None,
            runs: int = 1, warmup: bool = True
            ) -> list[tuple[str, int, list[float] | None, float | None]]:
    """(path, in-fence lines, seconds SAMPLES, discarded warm-up) per module.

    THE SECONDS ARE A LIST, changed 2026-08-13 by [LJ-1.148], because one run
    is one sample and the caller must be able to see how many it got. A module
    whose ANY run fails is returned unmeasured: a partial series would mix a
    failure's timing into a mean.

    THE FIRST AGDA INVOCATION OF A SERIES COSTS ABOUT 0.9 s MORE THAN THE REST,
    and that is why `warmup` exists. MEASURED 2026-08-13, and it is a FIXED
    cost rather than a percentage:

        src/L/Ordinal/StageArith.lagda.md    run 1 1.811 s, tail mean 0.787 s
        src/L/BoundedSubset.lagda.md         run 1 16.526 s, tail mean 15.566 s

    Two modules whose sizes differ twentyfold, one penalty of 1.02 and 0.96 s.
    It repeats 30 seconds after a previous series, so it is not a page cache
    that decays, and MEASURED over two modules in ONE series it hits only the
    FIRST: spreads of 79.0 and 2.0 percent by position.

    WHY IT IS A CORRECTNESS FIX AND NOT A PREFERENCE. `--recalibrate` times 73
    to 79 masters in ONE series, so the bar carries the penalty ONCE, about 0.3
    percent of 291 s. A `--module` run carries it in FULL: 130 percent on a
    75-line master, 6 percent on a 1,409-line one. So the bar was measured
    almost penalty-free and each module was judged with the penalty inside it.
    That is unlike compared with unlike, and it is the third time this file has
    found that shape: see the target-set note above and the two-rates note
    below. Discarding one warm-up run puts both sides on one instrument.

    IT IS NOT A THRESHOLD CHANGE. DD24's bar and its 1.15x tolerance are
    untouched and are the owner's. This changes only how faithfully the
    instrument reads. `--no-warmup` restores the historical behaviour exactly,
    and the discarded run is REPORTED rather than hidden.

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
    # ONE WARM-UP FOR THE WHOLE SERIES, not one per module, because the penalty
    # is a property of the series and not of the module. MEASURED: the second
    # module in a series spreads 2.0 percent, so it needs no warm-up of its own.
    discarded = None
    if warmup and paths:
        discarded = timing.time_module(ROOT / paths[0], cold=cold, ghcrts=ghcrts)
    for i, rel in enumerate(paths):
        lines = ledger_mod.count(rel, at_head=False)
        samples: list[float] | None = []
        for _ in range(max(1, runs)):
            seconds = timing.time_module(ROOT / rel, cold=cold, ghcrts=ghcrts)
            if seconds is None:
                samples = None
                break
            samples.append(seconds)
        out.append((rel, lines, samples, discarded if i == 0 else None))
    return out


def recalibrate(cfg: dict, runs: int = 1, warmup: bool = True) -> int:
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
    # THE AC SIDE IS THE LANDMARKS CONE, NOT "EVERYTHING MINUS THE WING".
    #
    # This selected by SUBTRACTION until 2026-08-13, and `[LJ-0.5]` had already
    # replaced exactly that construction for the whole-cone denominator on
    # 2026-08-10 without reaching this half. The two halves then disagreed by
    # 3,101 lines, every one of them GCH-campaign code that no hand-maintained
    # list had been updated to name, and `check-ratio.py` PREFERS this half for
    # a per-module verdict. So the wing's own most expensive masters were in
    # the baseline that judged the wing, and the bar was too lenient.
    #
    # The cure is the owner's rule, 2026-08-13: the AC side was FIXED when its
    # trophy landed and nothing written afterwards joins it. The cone states
    # that structurally rather than by declaration, and it holds: MEASURED the
    # same day, the cone gained ZERO members in the three days of wing work
    # that added 3,101 lines, because Landmarks imports none of them.
    #
    # `gch_wing` keeps its OTHER job below, naming what the bar judges.
    targets = sorted(f for f in ledger_mod.closure(
        ledger_mod.import_graph(ledger_mod.tracked_masters()),
        [cfg.get("ac_baseline_root", "src/Landmarks.lagda.md")])
        if f not in ledger_mod.UNCOUNTED)
    if not targets:
        print("check-ratio: nothing to recalibrate against.", file=sys.stderr)
        return 1
    wing = set(cfg.get("gch_wing", []))
    overlap = sorted(set(targets) & wing)
    if overlap:
        print(f"check-ratio: {len(overlap)} master(s) are in the cone AND "
              f"declared wing, so the baseline judges them against themselves: "
              f"{', '.join(overlap)}", file=sys.stderr)
        return 1
    ghcrts = cfg.get("ac_baseline_ghcrts")
    print(f"check-ratio --recalibrate | {len(targets)} AC masters | cold, warm "
          f"dependencies | GHCRTS={ghcrts or '-M8g (timer default)'} | "
          f"{runs} run(s) per master")
    rows = measure(targets, cold=True, ghcrts=ghcrts, runs=runs, warmup=warmup)
    lines = sum(n for _, n, s, _w in rows if s and n)
    seconds = sum(sum(s) / len(s) for _, n, s, _w in rows if s and n)
    skipped = [r for r, n, s, _w in rows if not s or not n]
    for _r, _n, _s, w in rows:
        if w is not None:
            print(f"check-ratio: warm-up run {w:.2f} s DISCARDED, so the "
                  f"series carries no first-run penalty.")
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
    parser.add_argument("--runs", type=int, default=1, metavar="N",
                        help="time each module N times and report the spread. "
                             "The verdict uses the MEAN. One run cannot see the "
                             "instrument's own swing, which has already flipped "
                             "a DD24 verdict on an unchanged module")
    parser.add_argument("--no-warmup", action="store_true",
                        help="do NOT discard a first run. Restores the "
                             "behaviour before [LJ-1.148], which loaded every "
                             "single-module figure with a fixed first-run cost "
                             "of about 0.9 s while the baseline carried almost "
                             "none of it")
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

    if args.runs < 1:
        print("check-ratio: --runs must be 1 or more.", file=sys.stderr)
        return 1

    if args.recalibrate:
        return recalibrate(cfg, runs=args.runs, warmup=not args.no_warmup)

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
    rows = measure(targets, cold=cold, ghcrts=cfg.get("ac_baseline_ghcrts"),
                   runs=args.runs, warmup=not args.no_warmup)

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
    fragile = []
    print(f"check-ratio | AC baseline {judged:.4f} s/line ({caliber}) | "
          f"tolerance {tolerance if tolerance else 1.0}x | bar {bar:.4f} s/line "
          f"| {'cold' if cold else 'WARM, NOT COMPARABLE'} | n={args.runs}")

    # WHAT THE TOOL KNOWS ABOUT ITS OWN SWING, said before any row is read.
    # A reader who does not know the band cannot tell a verdict from a coin
    # toss, and this tool printed rows for three days without it.
    if INSTRUMENT_SPREAD is None:
        print(f"check-ratio | noise band: UNKNOWN. This tool's repeatability is "
              f"{INSTRUMENT_SPREAD_SOURCE}, so NO row below can be called safe "
              f"from the instrument's own swing. Use --runs N")
    else:
        print(f"check-ratio | noise band: at least +-{INSTRUMENT_SPREAD:.1%}, "
              f"{INSTRUMENT_SPREAD_SOURCE}")
        if args.runs > 1:
            print(f"check-ratio | each row is flagged on the LARGER of that "
                  f"floor and its own {args.runs}-run spread")

    for rel, lines, samples, warm in rows:
        if warm is not None:
            print(f"  warm-up {warm:.2f} s on {rel}, DISCARDED: the first Agda "
                  f"of a series costs about 0.9 s more than the rest, and the "
                  f"baseline pays that once over 79 masters")
        if not samples or not lines:
            unmeasured.append(rel)
            print(f"  {'?':>9}  {lines:6,} lines  {rel}  (not measured)")
            continue
        seconds = sum(samples) / len(samples)
        total_lines += lines
        total_seconds += seconds
        ratio = seconds / lines
        flag = "OVER " if ratio > bar else "     "
        # THE BAND IS THE LARGER OF THE TWO, and that is not caution, it is
        # what the two numbers mean. A series' own spread measures how tightly
        # this occasion repeated; it CANNOT see how far the occasion itself
        # sits from the module's true cost. MEASURED: five series each
        # spreading 0.6 to 4.0 percent landed 9.3 percent apart. Taking the
        # within-series figure alone would print a confident band around a
        # displaced mean.
        own = spread_of(samples)
        if own is not None:
            band = f"n={len(samples)} spread {own:6.1%}"
            spread = max(own, INSTRUMENT_SPREAD or 0.0)
        else:
            spread = INSTRUMENT_SPREAD
            band = f"n=1 spread {'?':>6}"
        tag = ""
        if flips_verdict(ratio, bar, spread):
            # NOISE, NOT A VERDICT CHANGE. The row keeps its OVER or its blank
            # and the exit code is untouched: DD24's threshold is the owner's.
            # This says only that the instrument cannot tell the two apart.
            tag = "  NOISE: the swing crosses the bar"
            fragile.append(rel)
        print(f"  {flag}{ratio:.4f}  {lines:6,} lines  {seconds:8.2f} s  "
              f"{band}  {rel}{tag}")

    if fragile:
        print(f"check-ratio: {len(fragile)} row(s) sit INSIDE the instrument's "
              f"noise band, so their OVER or UNDER is not established by this "
              f"run: {', '.join(fragile)}. Re-run those with a larger --runs "
              f"before acting on the flag. The AGGREGATE is the judgment "
              f"(DD24); a per-module flag was always advice.")

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

    # THE AGGREGATE'S OWN SPREAD, and it is measured rather than derived from
    # the rows. Take the i-th run of every module, sum those, and you have one
    # whole-wing sample; the spread over the samples is the wing figure's swing.
    # That is exactly how `[LJ-1.135]` spread the AC side over four runs.
    #
    # IT IS SMALLER THAN THE ROWS' SPREADS AND THAT IS REAL, not a trick:
    # independent per-module noise averages down as you sum. So a wing verdict
    # is firmer than any row in it, which is the arithmetic behind DD24's own
    # rule that the aggregate is the judgment and a row is advice.
    measured = [s for _, n, s, _w in rows if s and n]
    agg_spread = None
    if measured and len({len(s) for s in measured}) == 1 and len(measured[0]) > 1:
        per_run = [sum(s[i] for s in measured) / total_lines
                   for i in range(len(measured[0]))]
        agg_spread = spread_of(per_run)

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
        agg_ref = max(agg_spread or 0.0, INSTRUMENT_SPREAD or 0.0) or None
        if agg_spread is not None:
            print(f"check-ratio: the aggregate rests on {args.runs} runs and "
                  f"spreads {agg_spread:.1%}.")
        if flips_verdict(aggregate, module_bar, agg_ref):
            # THE VERDICT IS STILL RENDERED AND THE EXIT CODE IS UNCHANGED.
            # Saying the swing crosses the bar is information; refusing to
            # judge would be a rule change, and DD24 is the owner's.
            print(f"check-ratio: NOISE. The wing verdict '{verdict}' sits "
                  f"inside the instrument's own swing, so this run does not "
                  f"establish it. Raise --runs before acting on it. The "
                  f"threshold is untouched and so is the exit code.")
        elif agg_ref is None:
            print(f"check-ratio: this verdict rests on ONE run per module and "
                  f"the instrument's repeatability is {INSTRUMENT_SPREAD_SOURCE}, "
                  f"so nothing here says whether the swing crosses the bar.")
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
