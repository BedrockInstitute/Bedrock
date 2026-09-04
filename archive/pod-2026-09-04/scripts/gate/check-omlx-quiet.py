#!/usr/bin/env python3
"""Refuses `make check`'s typecheck only when qwen's server AND low memory coincide.

OWNER'S RULING 2026-08-23, RELAXED 2026-08-24. The original ruling: the whole-tree
typecheck (`-M16g`, C-12's orchestrator caliber) and qwen's local inference must
never run at the same time. Qwen is the one model this repository dispatches through
a LOCAL server rather than a remote API: `dev/pod/heads.toml [legal.pi_provider]`
reads `"Qwen3.8-27B-oQ4e-mtp" = "omlx"`, commented "LOCAL, and the provider is not
the model's family name here either: the family is Qwen and the provider is `omlx`,
the server that serves it." Every other `herdr-pi` model (`glm-5.3` on `zai`,
`deepseek-v4-pro` on `deepseek`) is a remote API call through the `pi` CLI and
carries no local footprint.

THE ORIGINAL GUARD WAS EXISTENCE, NOT A LOAD THRESHOLD, and it said so: "this script
has no measured idle-vs-busy CPU baseline for `omlx-server` ... so a threshold would
be a guessed number, and AGENTS.md's Boundary forbids writing one the evidence does
not give. If `omlx-server` turns out to run as an always-on idle daemon that this
refuses needlessly, that is a threshold to add LATER, from a measured baseline, not
a guess to make now." That baseline now exists, MEASURED 2026-08-24: the box is
64 GB; `omlx-server` held 15.7 GB RSS while a real `coder` dispatch (`[LJ-1.616]`)
was actively using it; `scripts/ops/omlx-watchdog.sh` (shipped 2026-08-24) already
bounds its idle footprint with a 24 GB restart trigger, so the worst case is a KNOWN
quantity and not an open-ended unknown. 24 GB (qwen, worst case) plus 16 GB (make
check's cap) is 40 of 64 GB, and `memory_pressure -Q` read 84% SYSTEM-WIDE FREE with
qwen already live and serving a real dispatch -- comfortable room for both at once.

THE NEW GUARD READS SYSTEM FREE MEMORY, and it is not a threshold this script
invented: it is `free_memory_pct_for_extra` (25 percent), the SAME number
`dev/pod/heads.toml [tiers.shared]` already uses to gate a THIRD or FOURTH Agda
slot, C-12's own precedent for "may I start more voluntary work right now." Refusing
under it is unchanged in spirit: it is still measured, never guessed, and it still
fails toward refusal (FM12) when the sensor cannot be read. What changed is WHICH
measurement decides: memory headroom, an emergency exit `check-omlx-quiet.py`
`main()` did not build a bypass for. **`check-omlx-quiet.py` no longer refuses
just because `omlx-server` exists**; it refuses only when `omlx-server` is live
AND free memory is short.

THIS IS ONE HALF OF THE RULING. The other direction lives in `scripts/pod/pod.py`:
the Makefile's `typecheck` target holds `.pod-state/make-check.lock` for the
whole-tree run (`trap ... EXIT INT TERM` around the Agda call, so an interrupt or a
failed typecheck still clears it), and `_omlx_excluded()` filters qwen out of a
`coder` dispatch's candidate configs while that lock exists -- the mirror image of
this script's own refusal, aimed at the opposite process, RELAXED THE SAME WAY THE
SAME DAY: it now reads the same free-memory floor instead of the bare lock.

pgrep exits 0 on a match, 1 on no match, 3 on a fatal error; on a fatal error this
tries `ps` before refusing, for the same reason `agda_blocker()` does: an agent
sandbox with no `sysmond` makes pgrep exit 3 every time, and a guard nobody can ever
pass gets bypassed by hand, which is no guard at all. `memory_pressure -Q`
unreadable is the SAME shape of failure and gets the SAME escape hatch.

Exit status: 0 clean, 1 refused (qwen live and memory short, or nothing readable), 2
usage error.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys

PROCESS_NAME = "omlx-server"

#: C-12's own number, not invented here. `dev/pod/heads.toml [tiers.shared]
#: free_memory_pct_for_extra`: the floor that already gates a voluntary THIRD or
#: FOURTH Agda slot. Reused rather than duplicated with a new value, so ONE ruling
#: answers "is there room for more voluntary work" everywhere it is asked.
FREE_PCT_FLOOR = 25.0

UNREADABLE = "UNREADABLE"


def free_memory_pct() -> float | None:
    """System free memory as a percentage, or None when it cannot be read.

    Mirrors `scripts/pod/pod.py`'s `free_memory_pct()` (same `memory_pressure -Q`
    parse) rather than importing it: every `scripts/gate/check-*.py` in this tree is
    self-contained, with no dependency on the POD's own module, so this keeps that.
    """
    try:
        out = subprocess.run(["memory_pressure", "-Q"], capture_output=True,
                             text=True, timeout=20).stdout
    except (OSError, subprocess.SubprocessError):
        return None
    for line in out.split("\n"):
        if "free percentage" in line:
            digits = "".join(c for c in line.split(":")[-1] if c.isdigit())
            return float(digits) if digits else None
    return None


def _omlx_live() -> bool | None:
    """True/False whether `omlx-server` is a live process, or None if unreadable."""
    probe = subprocess.run(["pgrep", "-x", PROCESS_NAME], capture_output=True, text=True)
    if probe.returncode == 0:
        return True
    if probe.returncode == 1:
        return False

    for argv in (["ps", "-eo", "comm="], ["ps", "-A", "-o", "comm="]):
        alt = subprocess.run(argv, capture_output=True, text=True)
        if alt.returncode == 0 and alt.stdout:
            for line in alt.stdout.splitlines():
                if os.path.basename(line.strip()) == PROCESS_NAME:
                    return True
            return False

    return None


def omlx_blocker() -> str | None:
    """The reason a run is refused, or None when it is safe to run `make check`."""
    live = _omlx_live()
    if live is False:
        return None
    if live is None:
        return (f"{UNREADABLE}: no process enumerator works here (pgrep and ps both "
                 "failed), so the guard cannot see whether omlx-server is live. "
                 "Confirm the machine is quiet and re-run with --assume-quiet, which "
                 "records that you took the owner's ruling's call yourself")

    pct = free_memory_pct()
    if pct is None:
        return (f"{UNREADABLE}: qwen's local inference server (omlx-server) is live "
                 "and system free memory could not be read (`memory_pressure -Q` gave "
                 "nothing usable), so the guard cannot confirm there is room for both. "
                 "Confirm the machine is quiet and re-run with --assume-quiet")
    if pct <= FREE_PCT_FLOOR:
        return (f"qwen's local inference server (omlx-server) is live and system free "
                 f"memory is {pct:.0f}%, at or under the {FREE_PCT_FLOOR:.0f}% floor "
                 "(`free_memory_pct_for_extra`, `dev/pod/heads.toml [tiers.shared]`)")
    return None


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="refuse if qwen is live and memory is short; the only mode")
    parser.add_argument("--assume-quiet", action="store_true",
                        help="proceed when a sensor is unreadable, taking the owner's "
                             "ruling's call yourself. Never bypasses a MEASURED refusal")
    args = parser.parse_args(argv[1:])
    if not args.check:
        print(__doc__, file=sys.stderr)
        return 2

    blocker = omlx_blocker()
    if blocker and args.assume_quiet and blocker.startswith(UNREADABLE):
        print("check-omlx-quiet: UNREADABLE; proceeding on --assume-quiet. "
              "The owner's ruling's call was the caller's, not this tool's.",
              file=sys.stderr)
        blocker = None
    if blocker:
        print(f"check-omlx-quiet: refusing, {blocker} (owner's ruling 2026-08-23, "
              "relaxed 2026-08-24).", file=sys.stderr)
        print("Stop it, wait for it to finish, or wait for memory to free up, before "
              "running `make check`.", file=sys.stderr)
        return 1

    print("check-omlx-quiet: clean (qwen quiet, or qwen live with room to spare)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
