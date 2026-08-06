#!/usr/bin/env python3
"""Informational staleness check for the generated owner's dashboard.

The dashboard must be regenerated on every sub-agent return that touched its
sources (dev/ledger.toml, dev/PLAN.md, _build/briefs/*.md, or
the generator itself). This checker reports whether _build/dashboard.html is
older than any of those sources.

It is INFORMATIONAL and always exits 0: _build/ is git-ignored, so a fresh
clone has no dashboard, and a gate that failed on a missing generated file
would block every new clone. The orchestrator reads this report at a return;
the owner reads the dashboard itself.

Usage:
  check-dashboard.py                  compare the default output path
  check-dashboard.py --out PATH       compare a different generated page
Exit status: 0 always (informational); 2 on usage error.
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location(
    "dashboard", ROOT / "scripts" / "dashboard.py"
)
dashboard = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(dashboard)


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", default=str(dashboard.DEFAULT_OUT),
                    help="generated page to check (default _build/dashboard.html)")
    args = ap.parse_args(argv[1:])
    out = Path(args.out)

    if not out.exists():
        print(f"{out}: MISSING (expected on a fresh clone; run `make dashboard`)")
        return 0

    stamps = dashboard.source_stamps()
    stale = dashboard.stale_sources(out)
    for label, when in stamps:
        stamp = dashboard.fmt_mtime(when) if when else "missing"
        state = "STALE" if label in stale else "fresh"
        print(f"  {state:5s} {label}  ({stamp})")
    print()
    if stale:
        print(f"{out}: STALE (mtime {dashboard.fmt_mtime(dashboard.mtime(out))}); "
              "run `make dashboard` to regenerate")
    else:
        print(f"{out}: fresh against all sources")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
