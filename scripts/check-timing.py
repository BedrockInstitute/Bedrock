#!/usr/bin/env python3
"""Catch a check-cost regression at the commit that causes it.

WHY THIS EXISTS. Every gate this project has is blind to cost. A slow module
typechecks correctly; `make check` goes green; the prose linter is happy; the
Agda linter is happy. `L.Ordinal.SquareLaw` reached 0.94 s/line and 44 percent
of the whole tree's check time without tripping anything, and nobody found out
until `[L3.32-T86]` ran a profile months later. By then the cost was load
bearing and the habit had spread to two more chapters.

So this is not a style check. It is the only gate in the repository that can
fail a module for being expensive.

WHAT IT DOES. For each master you name (or each one changed against a base
ref), it typechecks the module warm, one process at a time, and judges the
result two ways, both of them CALIBER-FREE (see the note on
SHARE_REQUIRING_PROFILE for why that matters):

  1. **Regression.** Against `dev/ledger.toml`'s `[[hot]]` baseline, if the
     module has one. This compares a module against itself, so no unit of
     mathematical content has to be agreed on for it to mean something.
  2. **Share of the tree.** A module at or above 2 percent of total check
     time must have a per-definition profile on record, which is D30's exit
     condition (1). Expensive is not a defect; expensive and UNMEASURED is.

WHAT IT DOES NOT DO. It is NOT in `make check` and must not be added to it.
A warm single-module check costs seconds to minutes; the commit gate has to
stay cheap or it stops being run. This is called at a return, by the
orchestrator, on the modules a dispatch actually touched.

It also cannot tell you WHY a module is slow. That needs
`agda --profile=definitions`, which is what a dispatch does after this flags
something. This tool's whole job is to make sure somebody gets sent.

USAGE
    python3 scripts/check-timing.py src/L/Foo.lagda.md [...]   # named masters
    python3 scripts/check-timing.py --changed [--base HEAD]    # what moved
    python3 scripts/check-timing.py --changed --warn-only      # do not fail

Requires the tree to be warm (interfaces built). Run it after a build, not
after a `make clean`, or every module will read as a regression against a cold
number that means something else.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import time
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "dev" / "ledger.toml"

# WHICH CALIBER THIS FLAGS ON, and why it is not seconds per line.
#
# A first version of this file failed a module at 0.25 s/line. [L3.32-F0]
# retired that: lines are not units of mathematical content, and the retiring
# subtree writes 56.5 lines per exported obligation against the trunk's 22.4,
# so a per-line rate mostly measures how verbosely a proof is written. Worse,
# a fixed rate lets a module off the hook for being small while saying nothing
# about whether its cost is REMOVABLE, which is the only thing that matters.
#
# So this flags on the two things that are caliber-free:
#
#   - a REGRESSION against the module's own recorded figure, where the
#     comparison is the module against itself and no caliber is involved;
#   - a SHARE of the whole tree's cost above SHARE_REQUIRING_PROFILE, which is
#     D30 exit condition (1): a module this expensive must have a
#     per-definition profile on record, whatever its size or rate.
#
# The per-line and per-obligation rates are still PRINTED, because they orient
# a reader, but nothing fails on them.
SHARE_REQUIRING_PROFILE = 0.02

# The rewrite exit condition, RULED 2026-08-06 by the owner: the retiring
# subtree's MEASURED rate, 0.063 s per obligation over 26,479 lines. It is not
# an aspiration and not a round number; it is what one delivered tree in this
# repository actually achieves, which is why it can be asked of another.
#
# This is checked per module and only for modules inside a ruled rewrite scope
# ([L3.32-F5] and [L3.32-F6]). A module outside those scopes is reported
# against it for orientation and never failed on it.
BENCHMARK_SECONDS_PER_OBLIGATION = 0.063
REWRITE_SCOPES = ("L.Ordinal.SquareLaw", "L.Rud.")

# A module may drift a little between runs on a loaded machine. Only a rise
# past this multiple of the recorded baseline is called a regression.
REGRESSION_FACTOR = 1.25


def code_lines(path: Path) -> int:
    """Non-blank lines inside ```agda fences: the project's standing caliber."""
    n, inside = 0, False
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if stripped.startswith("```"):
            if not inside and re.match(r"^```+\s*agda\b", stripped):
                inside = True
            elif inside:
                inside = False
            continue
        if inside and stripped:
            n += 1
    return n


def module_name(path: Path) -> str:
    rel = path.relative_to(ROOT / "src")
    return str(rel).removesuffix(".lagda.md").removesuffix(".agda").replace("/", ".")


def obligations(path: Path) -> int:
    """The settled caliber, imported rather than restated.

    [L3.32-F0] got this wrong twice by re-deriving it. There is one counter,
    `scripts/obligations.py`, and every consumer calls it.
    """
    import importlib.util

    spec = importlib.util.spec_from_file_location(
        "obligations", Path(__file__).parent / "obligations.py"
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    counts = mod.scan(path)
    return counts["obligations"] + counts["locals"]


def tree_seconds() -> float | None:
    """The whole tree's measured check cost, for the share test."""
    if not LEDGER.exists():
        return None
    data = tomllib.loads(LEDGER.read_text(encoding="utf-8"))
    return data.get("timing", {}).get("full_cold_seconds")


def baselines() -> dict[str, dict]:
    if not LEDGER.exists():
        return {}
    data = tomllib.loads(LEDGER.read_text(encoding="utf-8"))
    return {row["module"]: row for row in data.get("hot", [])}


def changed_masters(base: str) -> list[Path]:
    out = subprocess.run(
        ["git", "diff", "--name-only", base, "--", "src/"],
        cwd=ROOT, capture_output=True, text=True,
    ).stdout
    paths = []
    for name in out.split():
        p = ROOT / name
        # Everything.lagda.md is a catalog, not content; timing it measures the
        # whole tree and tells you nothing about the commit.
        if p.suffix == ".md" and p.exists() and p.name != "Everything.lagda.md":
            paths.append(p)
    return paths


def time_module(path: Path) -> float | None:
    """Typecheck one module warm and return wall seconds, or None if it failed.

    GHCRTS=-M8g and one process at a time, per C-12: a concurrent typecheck
    both thrashes the machine and corrupts the measurement.
    """
    env = dict(os.environ, GHCRTS="-M8g")
    start = time.monotonic()
    proc = subprocess.run(
        ["agda", str(path.relative_to(ROOT))],
        cwd=ROOT, capture_output=True, text=True, env=env,
    )
    elapsed = time.monotonic() - start
    if proc.returncode != 0:
        sys.stderr.write(f"  agda failed on {path}; timing is meaningless:\n")
        sys.stderr.write("  " + (proc.stderr or proc.stdout)[-500:] + "\n")
        return None
    return elapsed


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("paths", nargs="*", type=Path)
    ap.add_argument("--changed", action="store_true",
                    help="time every src master that differs from --base")
    ap.add_argument("--base", default="HEAD")
    ap.add_argument("--warn-only", action="store_true",
                    help="report but exit 0 (use while a fix is in flight)")
    args = ap.parse_args()

    targets = [p if p.is_absolute() else ROOT / p for p in args.paths]
    if args.changed:
        targets += changed_masters(args.base)
    targets = sorted({p.resolve() for p in targets if p.exists()})

    if not targets:
        print("check-timing: nothing to measure")
        return 0

    base = baselines()
    tree_total = tree_seconds()
    findings: list[str] = []

    print(f"check-timing: {len(targets)} module(s), warm, one process at a time")
    for path in targets:
        lines = code_lines(path)
        if lines == 0:
            continue
        name = module_name(path)
        seconds = time_module(path)
        if seconds is None:
            findings.append(f"{name}: does not typecheck; timing not established")
            continue

        rate = seconds / lines
        obs = obligations(path)
        per_ob = seconds / obs if obs else 0.0
        share = f"{seconds / tree_total:5.1%}" if tree_total else "    -"
        recorded = base.get(name)
        note = ""
        if recorded:
            was = recorded["seconds"]
            note = f"  (ledger: {was}s)"
            if seconds > was * REGRESSION_FACTOR:
                findings.append(
                    f"{name}: {seconds:.0f}s against a recorded {was}s, "
                    f"a {seconds / was:.1f}x regression"
                )
        print(f"  {name:34s} {seconds:7.1f}s  {lines:5d}L  "
              f"{rate:5.2f} s/line  {per_ob:5.3f} s/oblig  "
              f"{share} of tree{note}")

        if name.startswith(REWRITE_SCOPES) and per_ob > BENCHMARK_SECONDS_PER_OBLIGATION:
            findings.append(
                f"{name}: {per_ob:.3f} s/obligation, over the ruled rewrite "
                f"exit condition of {BENCHMARK_SECONDS_PER_OBLIGATION} "
                f"({per_ob / BENCHMARK_SECONDS_PER_OBLIGATION:.0f}x). That "
                f"number is the retiring subtree's MEASURED rate, so it is "
                f"known reachable. Batch this module into [L3.32-F6]."
            )

        if tree_total and seconds / tree_total >= SHARE_REQUIRING_PROFILE:
            findings.append(
                f"{name}: {seconds / tree_total:.0%} of the whole tree's check "
                f"time. D30 exit condition (1) requires a per-definition "
                f"profile on record for any module at or above "
                f"{SHARE_REQUIRING_PROFILE:.0%}: run "
                f"`agda --profile=definitions` and record the removable "
                f"fraction, or record why none is removable."
            )

    if not findings:
        print("check-timing: OK")
        return 0

    print()
    for f in findings:
        print(f"  DEFECT: {f}")
    print("\n  D30 (dev/PLAN.md section 3) freezes new mathematics until the tree's")
    print("  check cost comes down. A module over the cap is how it got there.")
    return 0 if args.warn_only else 1


if __name__ == "__main__":
    sys.exit(main())
