#!/usr/bin/env python3
"""LJ-1.275 paired cold-run harness. ONE agda process, alternating arms.

The design copies `[LJ-1.266]`'s harness so the two series compare directly.
It adds the REVERSAL that `[LJ-1.215]`'s law asks for: cycle 2 runs the arms
in the opposite order and cycle 3 rotates again. An order effect therefore
shows up as a between-cycle split inside one arm.

Each run: clear the module's own .agdai (cold), run `agda` under
GHCRTS="-A64m -I0 -M8g", record wall seconds, exit code and load before/after.
"""
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path("/Users/alsg/Agentic/Bedrock")
AGDAI = ROOT / "_build" / "2.8.0" / "agda" / "agents" / "tasks" / "LJ-1-275"
ARMS = {
    "C": ("SupplyNewControl.lagda.md", "newcontrol"),
    "N": ("SupplyEnvNew.lagda.md", "newenv"),
    "U": ("SupplyFullNew.lagda.md", "newfull"),
}
ORDERS = ["CNU", "UNC", "NUC"]


def load():
    try:
        out = subprocess.run(["uptime"], capture_output=True, text=True).stdout
        return out.strip().split("load averages:")[-1].strip()
    except Exception:
        return "?"


def cold_run(tag, fname):
    target = ROOT / "agents" / "tasks" / "LJ-1-275" / fname
    iface = AGDAI / (Path(fname).with_suffix("").with_suffix("").name + ".agdai")
    if iface.exists():
        iface.unlink()
    lb = load()
    start = time.monotonic()
    proc = subprocess.run(
        ["agda", str(target.relative_to(ROOT))],
        cwd=ROOT, capture_output=True, text=True,
        env=dict(os.environ, GHCRTS="-A64m -I0 -M8g"))
    elapsed = time.monotonic() - start
    la = load()
    status = "exit %d" % proc.returncode
    if proc.returncode != 0:
        tail = (proc.stderr or proc.stdout)[-200:].replace("\n", " | ")
        status += " :: " + tail
    print(f"{tag} {fname} {elapsed:.2f}s {status} load {lb} -> {la}", flush=True)
    return elapsed, proc.returncode


if __name__ == "__main__":
    cycles = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    results = {}
    for i in range(cycles):
        order = ORDERS[i % len(ORDERS)]
        print(f"--- cycle {i + 1}, order {order} ---", flush=True)
        for a in order:
            fname, key = ARMS[a]
            el, rc = cold_run(f"{a}{i + 1}", fname)
            results.setdefault(key, []).append((el, rc))
    print("\n=== SUMMARY ===", flush=True)
    for key, vals in results.items():
        secs = [v[0] for v in vals]
        mean = sum(secs) / len(secs)
        spread = (max(secs) - min(secs)) / mean if len(secs) > 1 else float("nan")
        runs = [f"{s:.1f}" for s in secs]
        print(f"{key}: n={len(vals)} mean={mean:.2f}s spread={spread:.1%} runs={runs}",
              flush=True)
