#!/usr/bin/env python3
"""Run a PATCHED copy of `dispatch.py` against the REAL state directory.

WHY. `dispatch.py` derives `STATE` from its own location, so a copy in this
probe directory would read an empty registry and `status` would print a census
of nothing. That is not a comparison. This runner loads the copy, re-points the
four state paths at the live `.state`, and then drives the same subcommands the
brief's checks 5 and 6 name.

IT NEVER LAUNCHES AN AGENT. Only `status` and `check` are driven, and both are
read-only over the registry.

Usage:
    .venv/bin/python agents/tasks/LJ-1-303/probe/run-patched.py <module.py> \
        status | check <brief>
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path("/Users/alsg/Agentic/Bedrock")
LIVE_STATE = ROOT / ".claude" / "skills" / "codex-dispatch" / ".state"


def load(path: Path):
    sys.path.insert(0, str(ROOT / "scripts" / "dispatch"))
    sys.path.insert(0, str(ROOT / "scripts"))
    spec = importlib.util.spec_from_file_location("dispatch_under_test", path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["dispatch_under_test"] = mod
    spec.loader.exec_module(mod)
    # The four paths the copy derived from its own location.
    mod.STATE = LIVE_STATE
    mod.REGISTRY = LIVE_STATE / "registry.json"
    mod.LOCKFILE = LIVE_STATE / "registry.lock"
    mod.LOGS = LIVE_STATE / "logs"
    mod.WAITER_PID = LIVE_STATE / "waiter.pid"
    return mod


class Args:
    def __init__(self, **kw):
        self.all = False
        self.sweep_panes = False
        self.sandbox = "workspace-write"
        self.agda = False
        self.adversarial = False
        self.fallback = False
        for k, v in kw.items():
            setattr(self, k, v)


def main() -> int:
    mod = load(Path(sys.argv[1]))
    cmd = sys.argv[2]
    if cmd == "status":
        return mod.cmd_status(Args())
    if cmd == "check":
        return mod.cmd_check(Args(brief=sys.argv[3]))
    print(f"unknown command {cmd!r}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
