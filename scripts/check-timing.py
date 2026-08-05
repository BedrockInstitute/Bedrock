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
result two ways:

  1. Against `dev/ledger.toml`'s `[[hot]]` baseline, if the module has one.
     A module that got slower than its recorded figure is a regression.
  2. Against D30's cap of 0.25 s/line, which every master must meet. The
     number is not an ideal: the sealed `L.Rud.Bridge` measures 0.24, so the
     cap asks a master to reach what one measured fix already reached.

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

# D30's cap. Not a round number: the sealed L.Rud.Bridge measures 0.24 s/line,
# so this asks every master to reach what one measured fix already reached.
CAP_SECONDS_PER_LINE = 0.25

# Below this a module is too small for the ratio to mean anything: a 12-line
# module that takes 4 seconds is 0.33 s/line and is not a problem. The cap is
# about modules whose cost scales with their content.
MIN_LINES_FOR_CAP = 120

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
        print(f"  {name:34s} {seconds:7.1f}s  {lines:5d}L  {rate:5.2f} s/line{note}")

        if lines >= MIN_LINES_FOR_CAP and rate > CAP_SECONDS_PER_LINE:
            findings.append(
                f"{name}: {rate:.2f} s/line, over D30's cap of {CAP_SECONDS_PER_LINE}. "
                f"Profile it with `agda --profile=definitions` before adding to it."
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
