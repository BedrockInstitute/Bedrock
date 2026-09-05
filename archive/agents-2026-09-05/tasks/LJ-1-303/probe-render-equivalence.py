#!/usr/bin/env python3
"""PROBE for [LJ-1.303]: `render()` is unchanged on EVERY branch, not only today's.

WHY IT EXISTS. `render()` has three branches: a banded vendor under `auto`, a
flat vendor under `auto`, and a pin. The live config is FLAT and the switch is
PINNED, so a plain run exercises ONE of the three. A diff of that one run would
prove almost nothing about the two-thirds it never enters, and this task hoisted
three lines out of all three branches.

WHAT IT DOES. It loads the pre-edit module from a file the caller names, loads
the live one, and compares `render()`, `render_vendor()` and every table reader
under all three configurations, with the mode pinned and unpinned.

Run:
    .venv/bin/python agents/tasks/LJ-1-303/probe-render-equivalence.py <orig.py>
"""

from __future__ import annotations

import importlib.util
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts" / "dispatch"))
sys.path.insert(0, str(ROOT / "scripts"))

BANDED = """
in_force = "acme"
[vendors.acme]
model = "acme-model"
pi_provider = "acme"
pi_wired = true
base_state = "off-peak"
windows = [ { state = "peak", start = "20:00", end = "23:00" } ]
"""

FLAT = """
in_force = "acme"
[vendors.acme]
model = "acme-model"
pi_provider = "acme"
pi_wired = true
default_mode = "pi-subagent-mode"
"""

UNWIRED = """
in_force = "acme"
[vendors.acme]
model = "acme-model"
pi_provider = "acme"
pi_wired = false
default_mode = "in-harness-subagent-mode"
"""


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


def vendor_of(mod, text: str):
    with tempfile.NamedTemporaryFile("w", suffix=".toml", delete=False,
                                     encoding="utf-8") as fh:
        fh.write(text)
        name = fh.name
    try:
        return mod.load_vendor(Path(name))
    finally:
        Path(name).unlink()


def snapshot(mod) -> list[str]:
    """Every string this module renders, over every configuration."""
    out: list[str] = []
    saved_v, saved_s = mod.VENDOR, mod.VERSION_IN_FORCE
    try:
        for cfg_name, cfg in (("shipped", None), ("banded", BANDED),
                              ("flat", FLAT), ("unwired", UNWIRED),
                              ("builtin", "")):
            if cfg is None:
                mod.VENDOR = saved_v
            elif cfg == "":
                mod.VENDOR = mod.BUILTIN_VENDOR
            else:
                mod.VENDOR = vendor_of(mod, cfg)
            for switch in ("auto", "pi-subagent-mode",
                           "in-harness-subagent-mode", "deepseek-subagent-mode"):
                mod.VERSION_IN_FORCE = switch
                for arg in (None, "auto", "pi-subagent-mode",
                            "in-harness-subagent-mode", "normal", "override",
                            "deepseek-subagent-mode"):
                    tag = f"[{cfg_name}|{switch}|{arg}]"
                    try:
                        out.append(f"{tag} render\n{mod.render(arg)}")
                    except SystemExit as exc:
                        out.append(f"{tag} render RAISED {exc}")
                    for fn in ("in_force", "auto_mode"):
                        try:
                            out.append(f"{tag} {fn} = {getattr(mod, fn)()}")
                        except SystemExit as exc:
                            out.append(f"{tag} {fn} RAISED {exc}")
                    for case in ("default", "adversarial", "fallback"):
                        try:
                            out.append(f"{tag} head({case}) = "
                                       f"{sorted(mod.head(case).items())}")
                            out.append(f"{tag} expected({case}) = "
                                       f"{sorted(mod.expected_tier_tokens(case))}")
                        except SystemExit as exc:
                            out.append(f"{tag} head({case}) RAISED {exc}")
                    try:
                        out.append(f"{tag} default_harness = "
                                   f"{mod.default_harness()}")
                    except SystemExit as exc:
                        out.append(f"{tag} default_harness RAISED {exc}")
            try:
                out.append(f"[{cfg_name}] render_vendor\n{mod.render_vendor()}")
            except SystemExit as exc:
                out.append(f"[{cfg_name}] render_vendor RAISED {exc}")
            for h in range(0, 24, 1):
                for m in (0, 59):
                    try:
                        from datetime import datetime, timedelta, timezone
                        bj = timezone(timedelta(hours=8))
                        t = datetime(2026, 8, 14, h, m, tzinfo=bj)
                        out.append(f"[{cfg_name}] clock {h:02d}:{m:02d} = "
                                   f"{mod.clock_state(t)} / {mod.clock_mode(t)} "
                                   f"/ {mod.next_boundary(t)}")
                    except SystemExit as exc:
                        out.append(f"[{cfg_name}] clock {h:02d}:{m:02d} "
                                   f"RAISED {exc}")
    finally:
        mod.VENDOR, mod.VERSION_IN_FORCE = saved_v, saved_s
    return out


def main() -> int:
    orig_path = Path(sys.argv[1])
    live = load(ROOT / "scripts" / "dispatch" / "dispatch_policy.py", "live_pol")
    orig = load(orig_path, "orig_pol")
    a, b = snapshot(orig), snapshot(live)
    # The vendor `source` names a temporary file whose name differs per load, so
    # the two snapshots are compared with those paths masked. Nothing else in a
    # rendered line varies between two runs.
    import re
    mask = lambda s: re.sub(r"/[^\s,`']*\.toml", "<TMP>.toml", s)
    a, b = [mask(x) for x in a], [mask(x) for x in b]
    if a == b:
        print(f"IDENTICAL: {len(a)} rendered strings match across "
              f"5 vendor configs x 4 switch values x 7 render arguments.")
        return 0
    print(f"DIFFERENT: {sum(1 for x, y in zip(a, b) if x != y)} of {len(a)}")
    for x, y in zip(a, b):
        if x != y:
            print(f"--- orig\n{x}\n+++ live\n{y}")
            return 1
    return 1


if __name__ == "__main__":
    sys.exit(main())
