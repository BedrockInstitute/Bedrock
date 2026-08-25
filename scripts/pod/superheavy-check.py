#!/usr/bin/env python3
"""Run one Agda typecheck at the SUPERHEAVY cap: `dev/pod/heads.toml [tiers.superheavy]`.

OWNER'S RULING 2026-08-25. WIDE (2 GB) and HEAVY (4 GB) are the two tiers a TASK may
declare (`scripts/pod/facts.py TASK_TIERS`) and the dispatch loop admits automatically.
SUPERHEAVY is neither: `[tiers.superheavy]` is deliberately absent from `TASK_TIERS`,
from `heads.py`'s tier validation and from `[tiers.shared]`'s heap-sum budget (all
three name `wide`/`heavy` by string, never a wildcard over `[tiers]`), so no brief's
`agda_tier:` line and no automatic dispatch can ever reach it. **This script is the
ONE caller**, run BY HAND by the resident maintainer, never by the loop.

WHY IT EXISTS. MEASURED 2026-08-25 on `[LJ-1.628]`: an owner-approved, 10-line,
no-new-imports addition to `src/L/Constructible.lagda.md` (`class-pred-i`) still
heap-walled the whole tree at HEAVY's `-M4g`, 166.5 s, 4.38 GiB, on a WARM interface
cache -- a real cost from a foundational file's own fan-out, not a stale-interface
artefact (`dev/LESSONS.md` P-p already ruled that out at the same site). Verifying
whether such a change fits under a larger cap is what this exists for.

THE GATE IS THE POD'S OWN DISPATCH, NEVER THE SERVER'S EXISTENCE, owner's ruling
2026-08-25 (second, same day): `omlx-server` may stay resident (the watchdog keeps
it warm on purpose) and this tool still runs, AS LONG AS the pod itself has not
dispatched a task to it. It is still not `check-omlx-quiet.py`'s 2026-08-24 memory
floor either: that gate protects a routine, frequent `make check` run against
whatever ELSE the machine is doing; this checks one specific fact, whether the
pod's OWN live state carries a RUNNING task on an omlx-provider model, by
`pi_provider` and never a hardcoded model string (`_omlx_excluded()`'s own
reasoning in `scripts/pod/pod.py`: the provider carries the local footprint, not
the model name, so a future model sharing `omlx` is caught the same way).

Usage:
  .venv/bin/python scripts/pod/superheavy-check.py <agda-target>
  .venv/bin/python scripts/pod/superheavy-check.py src/Everything.lagda.md

Exit status: 0 the typecheck passed; 1 the typecheck failed (including a heap wall
at 8 GB); 2 refused before Agda ever ran (the pod has a live qwen dispatch, a usage
error, or the state/config could not be read).
"""

from __future__ import annotations

import os
import subprocess
import sys
import time
from pathlib import Path

_HERE = Path(__file__).resolve()
sys.path.insert(0, str(_HERE.parent))
_SCRIPTS = next((p for p in _HERE.parents if (p / "repo_root.py").is_file()), None)
if _SCRIPTS is None:
    raise FileNotFoundError(
        f"no repo_root.py above {_HERE}: refusing to guess the scripts root (C-43)")
sys.path.insert(0, str(_SCRIPTS))
from repo_root import find_root  # noqa: E402

import heads as heads_mod  # noqa: E402
import pod as pod_mod  # noqa: E402

ROOT = find_root(__file__)


def _qwen_dispatched() -> bool | None:
    """True/False whether the POD has a RUNNING task on an omlx-provider model, or
    None when the config or the state cannot be read.

    Reads `dev/pod/heads.toml [legal.pi_provider]` and never a hardcoded model
    string, matching `_omlx_excluded()` in `scripts/pod/pod.py`: the PROVIDER
    carries the local footprint, not the model name, so this catches any future
    model sharing `omlx` too. `pod_mod.load_state()` never raises on a missing or
    unreadable state file; it treats one as empty, which reads here as "nothing is
    dispatched" -- a bare state read is a courtesy check, not the machine-safety
    backstop `agda-watchdog.sh`/`admits()` already are, so it fails toward letting
    the maintainer's own judgement decide rather than inventing a refusal from
    nothing.
    """
    try:
        cfg = heads_mod.load_heads()
        providers = cfg["legal"]["pi_provider"]
    except (heads_mod.HeadsError, KeyError, TypeError):
        return None
    if not isinstance(providers, dict):
        return None
    st = pod_mod.load_state()
    return any(providers.get(t.model) == "omlx" for t in st.of(pod_mod.RUNNING))


def main(argv: list[str]) -> int:
    args = [a for a in argv[1:] if not a.startswith("-")]
    if len(args) != 1:
        print(__doc__, file=sys.stderr)
        return 2
    target = args[0]
    if not (ROOT / target).is_file():
        print(f"superheavy-check: REFUSED. {target} is not a file under {ROOT}.",
              file=sys.stderr)
        return 2

    dispatched = _qwen_dispatched()
    if dispatched is None:
        print("superheavy-check: REFUSED. UNREADABLE: dev/pod/heads.toml's "
              "[legal.pi_provider] or the pod's own state could not be read, so "
              "this cannot confirm qwen is idle, and this gate has no "
              "--assume-quiet escape (owner's ruling 2026-08-25: never a guess, "
              "for an 8 GB commitment). Check `pod.py status` by hand first.",
              file=sys.stderr)
        return 2
    if dispatched:
        print("superheavy-check: REFUSED. The pod has a RUNNING task on an "
              "omlx-provider model right now. Wait for it to return, or check "
              "`pod.py status`, before running this (owner's ruling 2026-08-25, "
              "second: the server may stay resident, the pod's own dispatch may "
              "not).", file=sys.stderr)
        return 2

    try:
        cfg = heads_mod.load_heads()
        heap = cfg["tiers"]["superheavy"]["heap"]
    except (heads_mod.HeadsError, KeyError, TypeError) as exc:
        print(f"superheavy-check: REFUSED. dev/pod/heads.toml carries no readable "
              f"[tiers.superheavy].heap: {exc}", file=sys.stderr)
        return 2

    print(f"superheavy-check: GHCRTS={heap!r}, target {target}", file=sys.stderr)
    env = dict(os.environ)
    env["GHCRTS"] = heap
    started = time.monotonic()
    proc = subprocess.run(["agda", target], cwd=ROOT, env=env)
    seconds = time.monotonic() - started
    print(f"superheavy-check: exit {proc.returncode}, {seconds:.2f}s", file=sys.stderr)
    return 0 if proc.returncode == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
