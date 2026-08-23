#!/usr/bin/env python3
"""Refuses `make check`'s typecheck while qwen's local inference server is live.

OWNER'S RULING 2026-08-23: the whole-tree typecheck (`-M16g`, C-12's orchestrator
caliber) and qwen's local inference must never run at the same time. Qwen is the
one model this repository dispatches through a LOCAL server rather than a remote
API: `dev/pod/heads.toml [legal.pi_provider]` reads `"Qwen3.8-27B-oQ4e-mtp" = "omlx"`,
commented "LOCAL, and the provider is not the model's family name here either: the
family is Qwen and the provider is `omlx`, the server that serves it." Every other
`herdr-pi` model (`glm-5.3` on `zai`, `deepseek-v4-pro` on `deepseek`) is a remote
API call through the `pi` CLI and carries no local footprint. MEASURED 2026-08-23:
the managed background daemon is a process named `omlx-server`
(`omlx --help` names `start`/`stop`/`restart` as its managed-server commands), found
alive at 27.9% CPU beside an unrelated manual qwen benchmark
(`run_experiment.py --force`, under `/Applications/oMLX.app`) -- confirming it is a
real, detectable, standing process and not something that only exists mid-request.

THE GUARD IS EXISTENCE, NOT A LOAD THRESHOLD, and that is disclosed rather than
hidden. `scripts/measure/check-ratio.py`'s `agda_blocker()` is the precedent this
copies: it refuses on any live `agda` process, never on a CPU percentage, because a
snapshot read at 0% does not guarantee the process stays idle for the sixteen
gigabytes the typecheck is about to ask for. The same reasoning applies here: this
script has no measured idle-vs-busy CPU baseline for `omlx-server` (it was not safe
to disturb the owner's own running benchmark to collect one), so a threshold would
be a guessed number, and AGENTS.md's Boundary forbids writing one the evidence does
not give. If `omlx-server` turns out to run as an always-on idle daemon that this
refuses needlessly, that is a threshold to add LATER, from a measured baseline, not
a guess to make now.

pgrep exits 0 on a match, 1 on no match, 3 on a fatal error; on a fatal error this
tries `ps` before refusing, for the same reason `agda_blocker()` does: an agent
sandbox with no `sysmond` makes pgrep exit 3 every time, and a guard nobody can ever
pass gets bypassed by hand, which is no guard at all.

Exit status: 0 clean, 1 qwen's server is live, 2 usage error.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys

PROCESS_NAME = "omlx-server"


def omlx_blocker() -> str | None:
    """The reason a run is refused, or None when no omlx-server process is live."""
    probe = subprocess.run(["pgrep", "-x", PROCESS_NAME], capture_output=True, text=True)
    if probe.returncode == 0:
        return "qwen's local inference server (omlx-server) is live"
    if probe.returncode == 1:
        return None

    for argv in (["ps", "-eo", "comm="], ["ps", "-A", "-o", "comm="]):
        alt = subprocess.run(argv, capture_output=True, text=True)
        if alt.returncode == 0 and alt.stdout:
            for line in alt.stdout.splitlines():
                if os.path.basename(line.strip()) == PROCESS_NAME:
                    return "qwen's local inference server (omlx-server) is live"
            return None

    return ("no process enumerator works here (pgrep and ps both failed), so the "
            "guard cannot see whether omlx-server is live. Confirm the machine is "
            "quiet and re-run with --assume-quiet, which records that you took the "
            "owner's 2026-08-23 ruling's call yourself")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="refuse if omlx-server is live; this is the only mode")
    parser.add_argument("--assume-quiet", action="store_true",
                        help="proceed when no process enumerator works, taking the "
                             "owner's ruling's call")
    args = parser.parse_args(argv[1:])
    if not args.check:
        print(__doc__, file=sys.stderr)
        return 2

    blocker = omlx_blocker()
    if blocker and args.assume_quiet and "no process enumerator" in blocker:
        print("check-omlx-quiet: NO PROCESS ENUMERATOR; proceeding on --assume-quiet. "
              "The owner's 2026-08-23 ruling's call was the caller's, not this tool's.",
              file=sys.stderr)
        blocker = None
    if blocker:
        print(f"check-omlx-quiet: refusing, {blocker} (owner's ruling 2026-08-23).",
              file=sys.stderr)
        print("Stop it, or wait for it to finish, before running `make check`.",
              file=sys.stderr)
        return 1

    print("check-omlx-quiet: clean (no live omlx-server)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
