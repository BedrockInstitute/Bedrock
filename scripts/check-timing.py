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
# subtree's MEASURED rate. It is not an aspiration and not a round number; it
# is what one delivered tree in this repository actually achieves, which is why
# it can be asked of another.
#
# IT IS READ FROM THE LEDGER, NEVER HARDCODED. [L3.32-T95] found it living in
# two homes, and it had already moved once (0.063 to 0.074 when a parser defect
# was fixed) with nothing keeping the copies in sync. AGENTS.md requires one
# canonical home per rule, and for this number that home is dev/ledger.toml.
#
# Checked per module, and only inside a ruled rewrite scope. A module outside
# is reported against it for orientation and never failed on it.
REWRITE_SCOPES = ("L.Ordinal.SquareLaw", "L.Rud.")

# Modules ABOVE the line that the ruling deliberately leaves alone, because a
# rewrite there costs more than it buys in both dimensions (dev/PLAN.md
# [L3.32-F6]: four modules worth fourteen seconds combined over 1,223 lines).
# [T95] found the gate would fail exactly the modules the ruling keeps, which
# would have made the tool argue with the decision it exists to serve.
REWRITE_EXEMPT = {
    "L.Rud.HF", "L.Rud.DefInJ", "L.Rud.BaseBlock", "L.Rud.SatTable",
}

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
    return mod.scan(path)["signatures"]


def benchmark() -> float | None:
    """The ruled exit condition, from its one canonical home."""
    if not LEDGER.exists():
        return None
    data = tomllib.loads(LEDGER.read_text(encoding="utf-8"))
    return data.get("caliber", {}).get("retiring_seconds_per_signature")


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
    # `git diff` cannot see an untracked file, so a brand new module would
    # evade the gate entirely until someone added it ([T95] D6.5). Untracked
    # masters are exactly the ones nobody has measured yet.
    changed = subprocess.run(
        ["git", "diff", "--name-only", base, "--", "src/"],
        cwd=ROOT, capture_output=True, text=True,
    ).stdout.split()
    untracked = subprocess.run(
        ["git", "ls-files", "--others", "--exclude-standard", "--", "src/"],
        cwd=ROOT, capture_output=True, text=True,
    ).stdout.split()
    paths = []
    for name in changed + untracked:
        p = ROOT / name
        # Everything.lagda.md is a catalog, not content; timing it measures the
        # whole tree and tells you nothing about the commit.
        if p.suffix == ".md" and p.exists() and p.name != "Everything.lagda.md":
            paths.append(p)
    return paths


def interface_of(path: Path) -> Path | None:
    """The `.agdai` Agda caches for this master, or None if it is not there.

    The path is version-stamped (`_build/<agda-version>/agda/<src path>`), so
    it is DISCOVERED rather than assumed: a guessed path that does not exist
    would silently turn every cold run into a warm one, which is the exact
    failure this function was added to prevent.
    """
    rel = path.relative_to(ROOT).with_suffix("")
    while rel.suffix:                      # .lagda.md -> .lagda -> bare
        rel = rel.with_suffix("")
    hits = sorted((ROOT / "_build").glob(f"*/agda/{rel}.agdai"))
    return hits[0] if hits else None


def time_module(path: Path, cold: bool) -> float | None:
    """Typecheck one module and return wall seconds, or None if it failed.

    COLD BY DEFAULT, and that is the whole point. The ledger's `[[hot]]`
    figures are each module's own COLD elaboration with dependencies warm,
    which is how [T86], [T87], [T88] and [T89] all measured. A warm re-check
    reads the cached interface and returns in seconds no matter how expensive
    the module really is: the first version of this tool compared a warm 2.8 s
    against a cold 204 s baseline and reported OK, so a module could have
    tripled its real cost and passed. Comparing a measurement against a
    baseline taken a different way is worse than not comparing at all,
    because it produces a confident wrong answer.

    So: move the module's own interface aside, time it, put it back.

    GHCRTS=-M8g and one process at a time, per C-12: a concurrent typecheck
    both thrashes the machine and corrupts the measurement.
    """
    env = dict(os.environ, GHCRTS="-M8g")
    iface = interface_of(path)
    stashed = None
    if cold and iface is None:
        sys.stderr.write(
            f"  note: no cached interface found for {path.name}; this run is "
            f"cold by construction\n")
    if cold and iface is not None and iface.exists():
        stashed = iface.with_suffix(".agdai.check-timing-stash")
        iface.replace(stashed)
    try:
        start = time.monotonic()
        proc = subprocess.run(
            ["agda", str(path.relative_to(ROOT))],
            cwd=ROOT, capture_output=True, text=True, env=env,
        )
        elapsed = time.monotonic() - start
    finally:
        # Always restore, including on an exception or a heap kill: leaving a
        # module's interface missing would silently make the NEXT full gate
        # re-elaborate it and look like a regression somewhere else.
        if stashed is not None and stashed.exists():
            if iface.exists():
                iface.unlink()
            stashed.replace(iface)
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
    ap.add_argument("--warm", action="store_true",
                    help="do NOT clear the interface first. Fast, but the "
                         "number is not comparable to the ledger's cold "
                         "baselines, so baseline and share tests are skipped.")
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
    bench = benchmark()
    if bench is None:
        print("check-timing: dev/ledger.toml carries no "
              "caliber.retiring_seconds_per_signature; the rewrite gate is "
              "DISABLED. This is the [T95] D1 failure mode: the ledger lost "
              "its data blocks and both gates went silently dead.")
    findings: list[str] = []

    mode = "warm (NOT comparable to the cold baselines)" if args.warm else \
           "cold, interface cleared, one process at a time"
    print(f"check-timing: {len(targets)} module(s), {mode}")
    for path in targets:
        lines = code_lines(path)
        if lines == 0:
            continue
        name = module_name(path)
        seconds = time_module(path, cold=not args.warm)
        if seconds is None:
            findings.append(f"{name}: does not typecheck; timing not established")
            continue

        rate = seconds / lines
        obs = obligations(path)
        per_ob = seconds / obs if obs else 0.0
        share = f"{seconds / tree_total:5.1%}" if tree_total else "    -"
        recorded = None if args.warm else base.get(name)
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

        if obs == 0:
            # [T95] D3/D6: a module whose results are all written without
            # signatures counts zero obligations, and a zero denominator used
            # to read as 0.000 s/obligation and PASS regardless of cost. An
            # uncountable module is a finding, not a pass.
            findings.append(
                f"{name}: zero obligations counted over {lines} lines, so no "
                f"per-obligation rate exists and this module cannot be gated. "
                f"Its results are probably written without signatures, which "
                f"scripts/obligations.py cannot see."
            )
        elif (bench and name.startswith(REWRITE_SCOPES)
              and name not in REWRITE_EXEMPT and per_ob > bench):
            findings.append(
                f"{name}: {per_ob:.3f} s/obligation, over the ruled rewrite "
                f"exit condition of {bench:.3f} ({per_ob / bench:.0f}x). That "
                f"number is the retiring subtree's MEASURED rate, so it is "
                f"known reachable by SOME tree. It is not known reachable for "
                f"any given theorem: [L3.32-T88] measured the abstract-carrier "
                f"restatement of SquareLaw's counting chase and it heap "
                f"exhausted at -M8g, twice. Batch into [L3.32-F6] and price it."
            )

        if (not args.warm and tree_total
                and seconds / tree_total >= SHARE_REQUIRING_PROFILE):
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
