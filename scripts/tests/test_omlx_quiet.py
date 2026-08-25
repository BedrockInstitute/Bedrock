#!/usr/bin/env python3
"""Regression tests for the qwen/typecheck mutual-exclusion gate.

OWNER'S RULING 2026-08-23, RELAXED 2026-08-24: `make check`'s whole-tree typecheck
(`-M16g`) and qwen's local inference server (`omlx-server`, the one `herdr-pi` model
with a local rather than remote footprint) no longer must never run at the same
time. `scripts/gate/check-omlx-quiet.py` now refuses only when `omlx-server` is live
AND system free memory (`memory_pressure -Q`) is at or under `free_memory_pct_for_
extra` (25%), C-12's own existing floor for "may I start more voluntary work now",
reused rather than a new guessed number.

Run: `python3 scripts/tests/test_omlx_quiet.py`
"""

from __future__ import annotations

import importlib.util
import subprocess
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent.parent
spec = importlib.util.spec_from_file_location(
    "check_omlx_quiet", ROOT / "scripts" / "gate" / "check-omlx-quiet.py"
)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

failures: list[str] = []


def check(name: str, condition: bool, detail: str = "") -> None:
    if condition:
        print(f"  ok    {name}")
    else:
        print(f"  FAIL  {name}{(': ' + detail) if detail else ''}")
        failures.append(name)


def cp(returncode: int, stdout: str = "") -> subprocess.CompletedProcess:
    return subprocess.CompletedProcess([], returncode, stdout=stdout, stderr="")


def fake_run(pgrep_rc, ps_stdout=None, mem_stdout=""):
    """One `subprocess.run` stub covering pgrep, ps and `memory_pressure -Q`,
    dispatched on argv[0] the way the real callers are told apart."""
    def run(argv, **kw):
        if argv[0] == "pgrep":
            return cp(pgrep_rc)
        if argv[0] == "ps":
            if ps_stdout is None:
                return cp(3)
            return cp(0, ps_stdout)
        if argv[0] == "memory_pressure":
            return cp(0, mem_stdout)
        raise AssertionError(f"unexpected argv: {argv}")
    return run


MEM_HIGH = "System-wide memory free percentage: 84%\n"
MEM_LOW = "System-wide memory free percentage: 10%\n"
MEM_AT_FLOOR = "System-wide memory free percentage: 25%\n"

# ---------------------------------------------------------------------------
# 1. omlx-server not live at all: never reaches the memory check.

with mock.patch.object(subprocess, "run", side_effect=fake_run(1)):
    check("omlx-server not live is quiet, whatever memory reads",
          mod.omlx_blocker() is None)

# ---------------------------------------------------------------------------
# 2. omlx-server live: the memory floor now decides.

with mock.patch.object(subprocess, "run", side_effect=fake_run(0, mem_stdout=MEM_LOW)):
    b = mod.omlx_blocker()
    check("live and memory short refuses", b is not None, repr(b))
    check("the refusal names omlx-server", b is not None and "omlx-server" in b)
    check("the refusal names the measured percentage", b is not None and "10" in b)

with mock.patch.object(subprocess, "run", side_effect=fake_run(0, mem_stdout=MEM_HIGH)):
    check("live and memory has room is quiet -- the whole point of the relaxation",
          mod.omlx_blocker() is None)

with mock.patch.object(subprocess, "run", side_effect=fake_run(0, mem_stdout=MEM_AT_FLOOR)):
    check("live and memory AT the floor refuses (the floor is inclusive)",
          mod.omlx_blocker() is not None)

# ---------------------------------------------------------------------------
# 3. pgrep exit 3 (fatal) falls back to ps, exactly as agda_blocker() does, and this
#    is unchanged by the relaxation: existence is still read the same way.

with mock.patch.object(subprocess, "run",
                       side_effect=fake_run(3, ps_stdout="bash\nomlx-server\nzsh\n",
                                             mem_stdout=MEM_LOW)):
    b = mod.omlx_blocker()
    check("pgrep exit 3 falls back to ps, and ps finding it still checks memory",
          b is not None and "omlx-server" in b)

with mock.patch.object(subprocess, "run",
                       side_effect=fake_run(3, ps_stdout="bash\nzsh\n")):
    check("pgrep exit 3, ps clean, is quiet", mod.omlx_blocker() is None)

# ---------------------------------------------------------------------------
# 4. Neither enumerator works: UNREADABLE, refuses, names the escape hatch.

with mock.patch.object(subprocess, "run", side_effect=fake_run(3, ps_stdout=None)):
    b = mod.omlx_blocker()
    check("no enumerator works: still refuses", b is not None)
    check("and is tagged UNREADABLE", b is not None and b.startswith(mod.UNREADABLE))

# ---------------------------------------------------------------------------
# 5. omlx-server live but memory_pressure itself unreadable: UNREADABLE too, and
#    this is the NEW fallback path the relaxation adds.

with mock.patch.object(subprocess, "run",
                       side_effect=fake_run(0, mem_stdout="nothing usable here\n")):
    b = mod.omlx_blocker()
    check("live but memory unreadable still refuses", b is not None)
    check("and is tagged UNREADABLE, not a measured refusal",
          b is not None and b.startswith(mod.UNREADABLE))

# ---------------------------------------------------------------------------
# 6. main()'s --check / --assume-quiet wiring.

with mock.patch.object(subprocess, "run", side_effect=fake_run(1)):
    check("main() with --check and no blocker exits 0",
          mod.main(["prog", "--check"]) == 0)

with mock.patch.object(subprocess, "run", side_effect=fake_run(0, mem_stdout=MEM_LOW)):
    check("main() with --check and a measured refusal exits 1",
          mod.main(["prog", "--check"]) == 1)

with mock.patch.object(subprocess, "run", side_effect=fake_run(3, ps_stdout=None)):
    check("main() with no enumerator and no --assume-quiet still exits 1 (refuses)",
          mod.main(["prog", "--check"]) == 1)
    check("main() with no enumerator and --assume-quiet exits 0",
          mod.main(["prog", "--check", "--assume-quiet"]) == 0)

with mock.patch.object(subprocess, "run", side_effect=fake_run(0, mem_stdout=MEM_LOW)):
    check("--assume-quiet NEVER bypasses a MEASURED refusal (memory genuinely short)",
          mod.main(["prog", "--check", "--assume-quiet"]) == 1)

check("main() with no mode flag at all is a usage error, not a silent pass",
      mod.main(["prog"]) == 2)

# ---------------------------------------------------------------------------

if failures:
    print(f"\nFAIL: {len(failures)} failing check(s)")
    raise SystemExit(1)
print("test_omlx_quiet: all checks passed")
