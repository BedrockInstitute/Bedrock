#!/usr/bin/env python3
"""LJ-1.158 serializing runner. It waits for a quiet machine, then runs ONE command.

The machine carries sibling dispatches that also run Agda. C-12 gives every
agent ONE agda process, so this runner REFUSES to start beside another agda
binary and waits instead. It records the load before and after, and the wall
seconds, beside the command's own output.

It sets `GHCRTS` to the ledger caliber and never raises the cap.

Usage:
    run158.py <out-file> <command> [<arg> ...]
"""
from __future__ import annotations

import os
import pathlib
import subprocess
import sys
import time

ROOT = pathlib.Path("/Users/alsg/Agentic/Bedrock")
GHCRTS = "-A64m -I0 -M8g"


def load_avg() -> str:
    return "%.2f / %.2f / %.2f" % os.getloadavg()


def wait_for_quiet(limit: int = 3600) -> int:
    """Refuse to start while another agda binary is alive. Return seconds waited."""
    waited = 0
    while waited < limit:
        out = subprocess.run(["pgrep", "-x", "agda"], capture_output=True, text=True)
        if out.returncode != 0:
            return waited
        sys.stderr.write(f"  another agda is live (pid {out.stdout.split()}); waiting\n")
        sys.stderr.flush()
        time.sleep(15)
        waited += 15
    raise SystemExit("another agda held the machine for an hour; refusing to measure")


def main() -> int:
    dest = pathlib.Path(sys.argv[1])
    dest.parent.mkdir(parents=True, exist_ok=True)
    args = sys.argv[2:]
    waited = wait_for_quiet()
    before = load_avg()
    env = dict(os.environ, GHCRTS=GHCRTS)
    start = time.monotonic()
    proc = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, env=env)
    elapsed = time.monotonic() - start
    after = load_avg()
    dest.write_text(
        f"# command {' '.join(args)}\n"
        f"# GHCRTS {GHCRTS}\n"
        f"# waited for a quiet machine {waited} s\n"
        f"# load before {before}\n"
        f"# load after  {after}\n"
        f"# wall seconds {elapsed:.2f}\n"
        f"# exit {proc.returncode}\n"
        f"{proc.stdout}\n----- stderr -----\n{proc.stderr}\n",
        encoding="utf-8",
    )
    print(f"exit {proc.returncode}, {elapsed:.2f} s, load {before} -> {after} -> {dest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
