#!/usr/bin/env python3
"""[LJ-1.148] probe: what does ONE module's check time swing by, run to run?

WHY IT IS NOT `check-ratio.py --runs N`. That tool prints a SPREAD and hides
the series. A spread of 118 percent can be twenty scattered samples or one
outlier and nineteen tight ones, and those two need different cures. This
prints every sample, its load, and the running mean, so the shape is visible.

IT USES THE PROJECT'S OWN TIMER. `check-timing.time_module` is the only module
timer in this repository (C-26) and this probe imports it rather than
re-implementing it, so the numbers are the ones a DD24 verdict is made of.

C-12: ONE agda process, serial, at the ledger's own GHCRTS, cap never raised.

    .venv/bin/python agents/tasks/LJ-1-148/probe-noise.py <master> [N]
"""

from __future__ import annotations

import importlib.util
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent.parent


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def loadavg() -> float:
    out = subprocess.run(["sysctl", "-n", "vm.loadavg"],
                         capture_output=True, text=True).stdout
    return float(out.strip().strip("{} ").split()[0])


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    rel = sys.argv[1]
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 10

    if subprocess.run(["pgrep", "-x", "agda"], capture_output=True).returncode == 0:
        print("probe: another Agda process is live. C-12 refuses. STOPPING.")
        return 1

    timing = load_module("check_timing", ROOT / "scripts" / "check-timing.py")
    ledger = load_module("ledger", ROOT / "scripts" / "ledger.py")
    with open(ROOT / "dev" / "ledger.toml", "rb") as handle:
        cfg = tomllib.load(handle).get("ratio", {})
    ghcrts = cfg.get("ac_baseline_ghcrts")
    lines = ledger.count(rel, at_head=False)

    print(f"probe-noise | {rel} | {lines} in-fence lines | GHCRTS={ghcrts} | "
          f"{n} cold runs, dependencies warm")
    print(f"{'run':>3} {'seconds':>9} {'s/line':>9} {'load':>6} "
          f"{'running mean':>13} {'running spread':>15}")

    samples: list[float] = []
    for i in range(1, n + 1):
        before = loadavg()
        seconds = timing.time_module(ROOT / rel, cold=True, ghcrts=ghcrts)
        if seconds is None:
            print(f"{i:3d}   AGDA FAILED; the series stops here.")
            return 1
        samples.append(seconds)
        mean = sum(samples) / len(samples)
        spread = (max(samples) - min(samples)) / mean if len(samples) > 1 else 0.0
        print(f"{i:3d} {seconds:9.3f} {seconds / lines:9.5f} {before:6.2f} "
              f"{mean:13.3f} {spread:14.1%}")

    mean = sum(samples) / len(samples)
    # THE MEAN OF THE TAIL, because run 1 is a different measurement from the
    # rest: it meets a page cache that the runs after it leave warm. Reporting
    # both says whether that mechanism is present without assuming it.
    tail = samples[1:]
    print()
    print(f"n={len(samples)}  min {min(samples):.3f}  max {max(samples):.3f}  "
          f"mean {mean:.3f}  spread {(max(samples) - min(samples)) / mean:.1%}")
    if tail:
        tmean = sum(tail) / len(tail)
        print(f"run 1 {samples[0]:.3f} against the tail mean {tmean:.3f}, "
              f"{samples[0] / tmean:.2f}x")
        print(f"tail only: n={len(tail)} min {min(tail):.3f} max {max(tail):.3f} "
              f"mean {tmean:.3f} spread {(max(tail) - min(tail)) / tmean:.1%}")
    print(f"rate at the mean {mean / lines:.5f} s/line")
    return 0


if __name__ == "__main__":
    sys.exit(main())
