#!/usr/bin/env python3
"""A PINNED timing harness for [LJ-1.147], and it exists because of a hazard.

WHY IT EXISTS. `scripts/check-ratio.py` was being REWRITTEN by a sibling
dispatch while this task's BEFORE run was in flight: `git status` showed 237
changed lines at 19:23 on 2026-08-13, and this task's second invocation died
with `TypeError: unsupported operand type(s) for +=: 'float' and 'list'` on a
traceback whose source lines did not match the file. A before/after
measurement whose INSTRUMENT changes between the two halves measures the
instrument, not the tree.

WHAT IT DOES NOT DO. It does not re-implement the timer or the line counter.
C-26 says share the FUNCTION, not the file, so this calls
`scripts/check-timing.py:time_module` and `scripts/ledger.py:count`, the two
canonical ones, both verified at HEAD (`git hash-object`) before every run.
It reads the caliber from `dev/ledger.toml` exactly as `check-ratio.py` does.

WHAT IT ADDS. The machine load beside every module, because DD24's 1.15x
tolerance is narrower than the machine's own 20.1 percent swing.
"""

from __future__ import annotations

import importlib.util
import os
import subprocess
import sys
import time
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SCRIPTS = ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS))

import ledger as ledger_mod  # noqa: E402


def _timing():
    spec = importlib.util.spec_from_file_location(
        "check_timing", SCRIPTS / "check-timing.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def load() -> str:
    return subprocess.run(["uptime"], capture_output=True, text=True).stdout.strip()


def agda_live() -> bool:
    probe = subprocess.run(["pgrep", "-x", "agda"], capture_output=True, text=True)
    return probe.returncode == 0


def main(argv: list[str]) -> int:
    with open(ROOT / "dev" / "ledger.toml", "rb") as handle:
        cfg = tomllib.load(handle).get("ratio", {})
    ghcrts = cfg.get("ac_baseline_ghcrts")
    rate = cfg.get("ac_baseline_module_rate")
    tol = cfg.get("tolerance") or 1.0
    bar = rate * tol

    for name in ("check-timing.py", "ledger.py"):
        got = subprocess.run(["git", "hash-object", f"scripts/{name}"],
                             cwd=ROOT, capture_output=True, text=True).stdout.strip()
        want = subprocess.run(["git", "rev-parse", f"HEAD:scripts/{name}"],
                              cwd=ROOT, capture_output=True, text=True).stdout.strip()
        print(f"instrument scripts/{name}: {'AT HEAD' if got == want else 'MOVED, ' + got}")

    if agda_live():
        print("REFUSING: another agda process is live (C-12).", file=sys.stderr)
        return 1

    timing = _timing()
    print(f"measure | GHCRTS={ghcrts} | bar {bar:.4f} s/line | cold, warm dependencies")
    print(f"load at start: {load()}")
    total_lines, total_seconds, missing = 0, 0.0, []
    for rel in argv:
        lines = ledger_mod.count(rel, at_head=False)
        before = load()
        seconds = timing.time_module(ROOT / rel, cold=True, ghcrts=ghcrts)
        after = load()
        if seconds is None:
            missing.append(rel)
            print(f"  FAILED {rel}")
            continue
        flag = "OVER" if lines and seconds / lines > bar else "    "
        r = seconds / lines if lines else float("nan")
        print(f"{flag} {r:.4f}  {lines:>6,} lines  {seconds:>8.2f} s  {rel}")
        print(f"       load before: {before}")
        print(f"       load after : {after}")
        total_lines += lines
        total_seconds += seconds
    if total_lines:
        agg = total_seconds / total_lines
        print(f"AGGREGATE {agg:.4f} s/line over {total_lines:,} lines and "
              f"{total_seconds:.2f} s | {agg / bar:.2f}x the bar | "
              f"{agg / rate:.2f}x the AC side")
    if missing:
        print(f"NOT MEASURED (excluded, never counted as zero): {', '.join(missing)}")
        return 1
    print(f"load at end: {load()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
