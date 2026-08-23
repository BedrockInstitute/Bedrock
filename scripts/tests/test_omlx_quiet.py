#!/usr/bin/env python3
"""Regression tests for the qwen/typecheck mutual-exclusion gate.

OWNER'S RULING 2026-08-23: `make check`'s whole-tree typecheck (`-M16g`) and qwen's
local inference server (`omlx-server`, the one `herdr-pi` model with a local rather
than remote footprint) must never run at the same time. `scripts/gate/check-omlx-
quiet.py` is `scripts/measure/check-ratio.py`'s `agda_blocker()` pattern, copied for
a different process name: refuse on EXISTENCE, never on a guessed CPU threshold,
because this script has no measured idle-vs-busy baseline for `omlx-server`.

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


# ---------------------------------------------------------------------------
# 1. pgrep's own three exit codes, the primary path.

with mock.patch.object(subprocess, "run", return_value=cp(0)):
    b = mod.omlx_blocker()
    check("pgrep exit 0 (a match) refuses", b is not None, repr(b))
    check("the refusal names omlx-server", b is not None and "omlx-server" in b)

with mock.patch.object(subprocess, "run", return_value=cp(1)):
    check("pgrep exit 1 (no match) is quiet", mod.omlx_blocker() is None)

# ---------------------------------------------------------------------------
# 2. pgrep exit 3 (fatal) falls back to ps, exactly as agda_blocker() does.

calls = []


def fake_run_ps_finds_it(argv, **kw):
    calls.append(argv)
    if argv[0] == "pgrep":
        return cp(3)
    return cp(0, "bash\nomlx-server\nzsh\n")


with mock.patch.object(subprocess, "run", side_effect=fake_run_ps_finds_it):
    b = mod.omlx_blocker()
    check("pgrep exit 3 falls back to ps, and ps finding it still refuses",
          b is not None and "omlx-server" in b)

calls.clear()


def fake_run_ps_clean(argv, **kw):
    calls.append(argv)
    if argv[0] == "pgrep":
        return cp(3)
    return cp(0, "bash\nzsh\n")


with mock.patch.object(subprocess, "run", side_effect=fake_run_ps_clean):
    check("pgrep exit 3, ps clean, is quiet", mod.omlx_blocker() is None)

# ---------------------------------------------------------------------------
# 3. Neither enumerator works: refuse, but name the escape hatch.


def fake_run_nothing_works(argv, **kw):
    return cp(3)


with mock.patch.object(subprocess, "run", side_effect=fake_run_nothing_works):
    b = mod.omlx_blocker()
    check("no enumerator works: still refuses", b is not None)
    check("and names --assume-quiet", b is not None and "--assume-quiet" in b)

# ---------------------------------------------------------------------------
# 4. main()'s --check / --assume-quiet wiring.

with mock.patch.object(subprocess, "run", return_value=cp(1)):
    check("main() with --check and no blocker exits 0",
          mod.main(["prog", "--check"]) == 0)

with mock.patch.object(subprocess, "run", return_value=cp(0)):
    check("main() with --check and a live match exits 1",
          mod.main(["prog", "--check"]) == 1)

with mock.patch.object(subprocess, "run", side_effect=fake_run_nothing_works):
    check("main() with no enumerator and no --assume-quiet still exits 1 (refuses)",
          mod.main(["prog", "--check"]) == 1)
    check("main() with no enumerator and --assume-quiet exits 0",
          mod.main(["prog", "--check", "--assume-quiet"]) == 0)

check("main() with no mode flag at all is a usage error, not a silent pass",
      mod.main(["prog"]) == 2)

# ---------------------------------------------------------------------------

if failures:
    print(f"\nFAIL: {len(failures)} failing check(s)")
    raise SystemExit(1)
print("test_omlx_quiet: all checks passed")
