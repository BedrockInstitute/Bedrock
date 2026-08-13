#!/usr/bin/env python3
"""LJ-1.155 measurement harness. Cold profile of one master, at the ledger caliber.

It calls the canonical helpers rather than copying them (C-26):
`scripts/check-timing.py` `interface_of` for the interface path, and
`scripts/ledger.py` `count` for the in-fence lines.

It REFUSES to run beside another agda process, and it records the load before
and after every run.

Usage:
    measure.py <out-dir> <profile-kind> <module> [<module> ...]
"""
from __future__ import annotations

import importlib.util
import os
import pathlib
import subprocess
import sys
import time

ROOT = pathlib.Path("/Users/alsg/Agentic/Bedrock")
GHCRTS = "-A64m -I0 -M8g"


def _load(name: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / f"{name}.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


timing = _load("check_timing") if (ROOT / "scripts" / "check_timing.py").exists() else None
if timing is None:
    spec = importlib.util.spec_from_file_location("check_timing", ROOT / "scripts" / "check-timing.py")
    timing = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(timing)
spec = importlib.util.spec_from_file_location("ledger", ROOT / "scripts" / "ledger.py")
ledger = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ledger)


def load_avg() -> str:
    return "%.2f / %.2f / %.2f" % os.getloadavg()


def wait_for_quiet(limit: int = 600) -> None:
    """Refuse to start while another agda binary is alive."""
    waited = 0
    while waited < limit:
        out = subprocess.run(["pgrep", "-x", "agda"], capture_output=True, text=True)
        if out.returncode != 0:
            return
        sys.stderr.write(f"  another agda is live (pid {out.stdout.split()}); waiting\n")
        time.sleep(10)
        waited += 10
    raise SystemExit("another agda held the machine for 10 minutes; refusing to measure")


def run(module: str, kinds: list[str], out_dir: pathlib.Path, tag: str) -> None:
    path = ROOT / module
    iface = timing.interface_of(path)
    wait_for_quiet()
    before = load_avg()
    stashed = None
    if iface is not None and iface.exists():
        stashed = iface.with_suffix(".agdai.lj1155-stash")
        iface.replace(stashed)
    env = dict(os.environ, GHCRTS=GHCRTS)
    args = ["agda"] + [f"--profile={k}" for k in kinds] + [module]
    try:
        start = time.monotonic()
        proc = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, env=env)
        elapsed = time.monotonic() - start
    finally:
        if stashed is not None and stashed.exists():
            if iface.exists():
                iface.unlink()
            stashed.replace(iface)
    after = load_avg()
    name = module.replace("/", "_").replace(".lagda.md", "")
    dest = out_dir / f"{name}.{tag}.txt"
    dest.write_text(
        f"# module {module}\n"
        f"# in-fence lines {ledger.count(module, at_head=False)}\n"
        f"# GHCRTS {GHCRTS}\n"
        f"# command {' '.join(args)}\n"
        f"# load before {before}\n"
        f"# load after  {after}\n"
        f"# wall seconds {elapsed:.2f}\n"
        f"# exit {proc.returncode}\n"
        f"{proc.stdout}\n----- stderr -----\n{proc.stderr}\n",
        encoding="utf-8",
    )
    print(f"{module}: exit {proc.returncode}, {elapsed:.2f} s, load {before} -> {after} -> {dest}")


def main() -> int:
    out_dir = pathlib.Path(sys.argv[1])
    out_dir.mkdir(parents=True, exist_ok=True)
    kinds = sys.argv[2].split(",")
    tag = os.environ.get("LJ1155_TAG", "run1")
    for module in sys.argv[3:]:
        run(module, kinds, out_dir, tag)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
