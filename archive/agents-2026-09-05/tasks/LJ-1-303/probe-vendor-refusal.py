#!/usr/bin/env python3
"""PROBE for [LJ-1.303] check 7: an unwired vendor must not break inspection.

WHY A PROBE AND NOT A CONFIG EDIT. The brief's check 7 says to add a temporary
row to `dev/vendors.toml`. That file is OUTSIDE this task's write scope, and the
same seam is reachable without touching it: `dispatch.py` reads the vendor
THROUGH `dispatch_policy`, and `require_vendor_wired()` reads the module-level
`VENDOR` at call time. So this probe imports the policy FIRST, puts an unwired
vendor in force, and only then imports `dispatch.py`, whose import block then
runs against the unwired vendor exactly as it would with a config row.

It proves two halves:
  1. `status` still works. The import block catches the SystemExit.
  2. A LAUNCH still refuses, loudly, with the vendor named.

Run:  .venv/bin/python agents/tasks/LJ-1-303/probe-vendor-refusal.py
"""

from __future__ import annotations

import io
import sys
import tempfile
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts" / "dispatch"))
sys.path.insert(0, str(ROOT / ".claude" / "skills" / "codex-dispatch"))

import dispatch_policy as P  # noqa: E402

UNWIRED = """
in_force = "acme"
[vendors.acme]
model = "acme-model"
pi_provider = "acme"
pi_wired = false
default_mode = "pi-subagent-mode"
"""

with tempfile.NamedTemporaryFile("w", suffix=".toml", delete=False,
                                 encoding="utf-8") as fh:
    fh.write(UNWIRED)
    tmp = fh.name
P.VENDOR = P.load_vendor(Path(tmp))
Path(tmp).unlink()

if len(sys.argv) > 1:
    # A PATCHED COPY, named on the command line, so the same probe judges both.
    import importlib.util
    _spec = importlib.util.spec_from_file_location("D_under_test",
                                                   Path(sys.argv[1]))
    D = importlib.util.module_from_spec(_spec)
    sys.modules["D_under_test"] = D
    _spec.loader.exec_module(D)
    # A copy derives STATE from its OWN location, so re-point it at the live
    # one. Without this the census reads an empty registry and the comparison
    # measures the copy's address, not its code.
    _live = ROOT / ".claude" / "skills" / "codex-dispatch" / ".state"
    D.STATE, D.REGISTRY = _live, _live / "registry.json"
    D.LOCKFILE, D.LOGS = _live / "registry.lock", _live / "logs"
    D.WAITER_PID = _live / "waiter.pid"
else:
    import dispatch as D  # noqa: E402

print("1. IMPORT SURVIVED an unwired vendor.")
print(f"   HARNESS      = {D.HARNESS!r}")
print(f"   POLICY_ERROR = {D.POLICY_ERROR!r}")
print(f"   VENDOR_ERROR starts: {D.VENDOR_ERROR[:70]!r}")
print(f"   vendor named in the error: {'acme' in D.VENDOR_ERROR}")
print(f"   field named in the error: {'pi_wired = false' in D.VENDOR_ERROR}")


class _A:
    all = False
    sweep_panes = False


out, err = io.StringIO(), io.StringIO()
with redirect_stdout(out), redirect_stderr(err):
    rc_status = D.cmd_status(_A())
lines = out.getvalue().splitlines()
print(f"\n2. STATUS STILL WORKS: rc={rc_status}, {len(lines)} line(s) printed.")
print(f"   first line: {lines[0] if lines else '(none)'}")

out, err = io.StringIO(), io.StringIO()
with redirect_stdout(out), redirect_stderr(err):
    try:
        rc_launch = D.launch("probe-lj-1-303", Path("/nonexistent/brief.md"),
                             False, "workspace-write", "acme-model")
    except SystemExit as exc:
        rc_launch = f"SystemExit({exc.code})"
print(f"\n3. LAUNCH REFUSED: rc={rc_launch}")
print(f"   stderr: {err.getvalue().strip()[:200]}")
print(f"   the word REFUSED is present: {'REFUSED' in err.getvalue()}")
