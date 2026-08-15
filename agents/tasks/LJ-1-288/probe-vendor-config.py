#!/usr/bin/env python3
"""PROBE for [LJ-1.288]. What the dispatch policy does under each vendor config.

WHAT IT MEASURES. It loads each probe config beside this file, puts it in force
inside the module, and prints what the policy then answers. It never edits
`dev/vendors.toml`, so a failed run leaves nothing to repair.

WHY IT IS A PROBE AND NOT A TEST. `scripts/tests/test_dispatch_clock.py` PINS
the behaviour and fails the gate. This file SHOWS it, in one readable page, for
the report and for a reader who wants the four cases side by side.

Run it:  .venv/bin/python agents/tasks/LJ-1-288/probe-vendor-config.py
"""

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import dispatch_policy as P  # noqa: E402


def show(title: str, path: Path | None) -> None:
    """Load one config, put it in force, and print every answer it changes."""
    print("=" * 78)
    print(title)
    print("-" * 78)
    saved = P.VENDOR
    try:
        try:
            v = P.load_vendor(path) if path else P.BUILTIN_VENDOR
        except SystemExit as exc:
            print(f"LOAD REFUSED: {exc}")
            return
        P.VENDOR = v
        try:
            P._validate_vendor_against_policy()
        except SystemExit as exc:
            print(f"VALIDATION REFUSED: {exc}")
            return
        print(f"vendor:        {v.name}")
        print(f"model:         {v.model}")
        print(f"pi_provider:   {v.pi_provider}")
        print(f"pi_wired:      {v.pi_wired}")
        print(f"banded:        {v.banded}")
        try:
            print(f"clock_state(): {P.clock_state()}")
        except SystemExit as exc:
            print(f"clock_state(): REFUSED. {exc}")
        try:
            print(f"auto_mode():   {P.auto_mode()}")
        except SystemExit as exc:
            print(f"auto_mode():   REFUSED. {exc}")
        try:
            print(f"default_harness(): {P.default_harness()}")
        except SystemExit as exc:
            print(f"default_harness(): REFUSED. {exc}")
        print("-" * 78)
        print(P.render_vendor())
    finally:
        P.VENDOR = saved
    print()


show("CASE 1. NO CONFIG. The built-in default vendor applies.", None)
show("CASE 2. THE SHIPPED CONFIG, which names deepseek.",
     ROOT / "dev" / "vendors.toml")
show("CASE 3. A FLAT VENDOR that pi cannot run (glm, pi_wired = false).",
     HERE / "probe-glm-flat.toml")
show("CASE 4. A BANDED VENDOR other than deepseek, with its own hours.",
     HERE / "probe-wired-glm-banded.toml")
show("CASE 5. AN UNKNOWN VENDOR named by in_force.",
     HERE / "probe-unknown-vendor.toml")
show("CASE 6. A FLAT VENDOR that names no default_mode.",
     HERE / "probe-flat-no-default.toml")
show("CASE 7. THREE PRICE BANDS, with no CLOCK_STATES row for the third.",
     HERE / "probe-three-bands.toml")
