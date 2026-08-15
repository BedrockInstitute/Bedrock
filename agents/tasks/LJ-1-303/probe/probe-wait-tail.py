#!/usr/bin/env python3
"""PROBE for [LJ-1.303]: `cmd_wait`'s REPORT TAIL, before and after the slimming.

WHY THIS PROBE EXISTS. The slimming replaces eleven lines at the foot of
`cmd_wait` with one call to `announce()`. None of the brief's seven checks runs
that code: `status` and `check` never enter `cmd_wait`, and waiting on a real
agent costs an agent. So the one hunk with real risk would have shipped
unexercised, which is the shape this whole file exists to refuse.

WHAT IT DOES. It builds a THROWAWAY state directory holding one registry with a
single DEAD record, points the module at it, and runs `cmd_wait` to completion.
Then it prints the stdout and the `returns.log` line both versions wrote. The
two must match apart from the timestamp.

IT TOUCHES NO LIVE STATE. Every path is inside a temporary directory that is
removed at the end, and no agent is launched.

Usage:
    .venv/bin/python agents/tasks/LJ-1-303/probe/probe-wait-tail.py <module.py>
"""

from __future__ import annotations

import importlib.util
import io
import json
import shutil
import sys
import tempfile
from contextlib import redirect_stdout
from pathlib import Path

ROOT = Path("/Users/alsg/Agentic/Bedrock")


def main() -> int:
    sys.path.insert(0, str(ROOT / "scripts" / "dispatch"))
    sys.path.insert(0, str(ROOT / "scripts"))
    spec = importlib.util.spec_from_file_location("D_wait", Path(sys.argv[1]))
    D = importlib.util.module_from_spec(spec)
    sys.modules["D_wait"] = D
    spec.loader.exec_module(D)

    state = Path(tempfile.mkdtemp(prefix="lj1303-wait-"))
    D.STATE = state
    D.REGISTRY = state / "registry.json"
    D.LOCKFILE = state / "registry.lock"
    D.LOGS = state / "logs"
    D.WAITER_PID = state / "waiter.pid"
    D.LOGS.mkdir(parents=True, exist_ok=True)

    # ONE CLEAN RETURN AND ONE DEATH, so both branches of the report print.
    clean_final = D.LOGS / "T-clean-final.md"
    clean_final.write_text("a real final message, long enough to be a return "
                           "and not a herdr error object. " * 8)
    dead_final = D.LOGS / "T-dead-final.md"
    dead_final.write_text("")
    (D.LOGS / "T-clean.log").write_text("log")
    (D.LOGS / "T-dead.log").write_text("log")
    # pid 1 is alive but is NOT ours: `proc_start` will not match, so `rec_alive`
    # reads FALSE, which is the returned-agent state this probe needs.
    D.REGISTRY.write_text(json.dumps({"dispatches": {
        "T-clean": {"pid": 1, "proc_start": "not-our-start-time",
                    "final": str(clean_final), "log": str(D.LOGS / "T-clean.log")},
        "T-dead": {"pid": 1, "proc_start": "not-our-start-time",
                   "final": str(dead_final), "log": str(D.LOGS / "T-dead.log")},
    }}, indent=2))

    class A:
        all = False
        timeout = 0

    # `cmd_wait` snapshots `running()` first and exits early when nothing is
    # live, so the two records must read as live for the snapshot and dead for
    # the loop. `rec_alive` is patched to answer live ONCE per task.
    seen: dict[str, int] = {}
    real_rec_alive = D.rec_alive

    def fake_rec_alive(d: dict) -> bool:
        key = str(d.get("final", ""))
        seen[key] = seen.get(key, 0) + 1
        return seen[key] == 1

    D.rec_alive = fake_rec_alive
    D.time.sleep = lambda _s: None            # no real waiting in a probe

    out = io.StringIO()
    with redirect_stdout(out):
        rc = D.cmd_wait(A())
    D.rec_alive = real_rec_alive

    print(f"rc = {rc}")
    print("--- stdout")
    print(out.getvalue().rstrip())
    print("--- returns.log")
    log = state / "returns.log"
    if log.exists():
        for line in log.read_text().splitlines():
            # Mask the timestamp: it is the wall clock and differs per run.
            print("  <STAMP>  " + line.split("  ", 1)[1])
    else:
        print("  (no returns.log written)")
    shutil.rmtree(state)
    return 0


if __name__ == "__main__":
    sys.exit(main())
