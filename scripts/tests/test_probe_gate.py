#!/usr/bin/env python3
"""Regression tests for the never-commit gate, the one probe rule that survives.

WHY THIS FILE EXISTS. The rule was bought with an incident: on 2026-08-04 a single
`git add -A src/` committed 13 probe files, 3,274 lines, which had to be untracked afterwards.
`.gitignore` covered them already, which is the point: an ignore rule is a default and
`git add -f` walks past it. **The gate is the only thing that refuses.**

WHAT CHANGED, and it is why this file replaces `test_probe_lifecycle.py`. The owner ruled on
2026-08-13 that a probe pairs one-to-one with its report, lives beside it in `agents/reports/`,
is tracked, and is never deleted. `[LJ-1.138]`'s lifecycle (`--gate`, `--stale`, `--sweep`,
`--index`, the live-task trigger, the deletion floor) is RETIRED, frozen at
`archive/tooling/check-probes-lifecycle.py` with its suite. Nothing here tests a lifecycle.

The tests below pin the four things that must never silently invert:

1. **`src/` is refused absolutely.** Every shape, every depth.
2. **`agents/reports/` is accepted**, or every commit fails.
3. **An `.agdai` is refused everywhere**, exempt directory or not. It is a build output.
4. **A staged RENAME is seen.** MEASURED 2026-08-13 at `[LJ-1.141]`: 257 probe renames were
   staged and `--diff-filter=ACM` reported ZERO of them. A tracked probe can now be
   `git mv`-ed into `src/`, so the filter must carry `R`.

Run: `python3 scripts/tests/test_probe_gate.py`
"""

from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
spec = importlib.util.spec_from_file_location(
    "check_probes", ROOT / "scripts" / "check-probes.py"
)
check_probes = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check_probes)

failures: list[str] = []


def check(name: str, condition: bool, detail: str = "") -> None:
    if condition:
        print(f"  ok    {name}")
    else:
        print(f"  FAIL  {name}{(': ' + detail) if detail else ''}")
        failures.append(name)


def run(args: list[str], env: dict | None = None) -> subprocess.CompletedProcess:
    import os
    return subprocess.run([sys.executable, "scripts/check-probes.py", *args],
                          cwd=ROOT, capture_output=True, text=True,
                          env={**os.environ, **(env or {})})


# ---------------------------------------------------------------------------
# 1. src/ is refused absolutely. The 2026-08-04 incident is what pays for this.
# ---------------------------------------------------------------------------
print("src/ is refused absolutely, at every depth and every extension")

for path in ("src/ProbeX.agda", "src/L/ProbeX.agda", "src/L/Rud/ProbeX.agda",
             "src/ProbeX.md", "src/ProbeX.lagda.md"):
    check(f"{path} is refused", check_probes.classify(path) is not None)
check("the src/ message names the incident's rule",
      "src/ is forbidden absolutely" in (check_probes.classify("src/ProbeX.agda") or ""))

# ---------------------------------------------------------------------------
# 2. agents/reports/ is the ONE home, and it is a prefix rather than a word
# ---------------------------------------------------------------------------
print("agents/reports/ is accepted; every neighbouring path is not")

check("agents/reports/ProbeX.agda is accepted",
      check_probes.classify("agents/reports/ProbeX.agda") is None)
check("agents/reports/ProbeX.lagda.md is accepted",
      check_probes.classify("agents/reports/ProbeX.lagda.md") is None)
check("agents/reports/archive/ProbeX.agda is accepted (it is under the prefix)",
      check_probes.classify("agents/reports/archive/ProbeX.agda") is None)
for path in ("agents/briefs/ProbeX.agda", "agents/ProbeX.agda", "ProbeX.agda",
             "archive/src/L/ProbeX.agda", "archive/probes/ProbeX.agda",
             "probes/ProbeX.agda", "dev/ProbeX.agda"):
    check(f"{path} is refused", check_probes.classify(path) is not None)

# ---------------------------------------------------------------------------
# 3. An .agdai is a build output. It is refused in the exempt home too.
# ---------------------------------------------------------------------------
print("an .agdai is refused everywhere, exemption or not")

for path in ("agents/reports/ProbeX.agdai", "src/ProbeX.agdai",
             "agents/reports/L/Anything.agdai", "agents/reports/NotAProbe.agdai"):
    check(f"{path} is refused", check_probes.classify(path) is not None)
check("_build/anything is refused", check_probes.classify("_build/x.json") is not None)
check("a woven copy is refused", check_probes.classify("x/woven/L/Stage.lagda.md") is not None)

# ---------------------------------------------------------------------------
# 4. A NON-probe in the exempt home is untouched. The gate reads the shape.
# ---------------------------------------------------------------------------
print("the gate reads the basename shape and touches nothing else")

for path in ("agents/reports/lj-1.141-report.md", "src/L/Stage.lagda.md",
             "scripts/check-probes.py", "agents/briefs/LJ-1.141.md"):
    check(f"{path} is clean", check_probes.classify(path) is None)

# ---------------------------------------------------------------------------
# 5. THE RENAME FILTER. This is the hole [LJ-1.141] measured and closed.
# ---------------------------------------------------------------------------
print("a staged RENAME is visible to --staged")

check("the filter carries R", "R" in check_probes.STAGED_FILTER, check_probes.STAGED_FILTER)

# End to end, against a THROWAWAY index. The real index is never touched: a test that stages
# into `.git/index` competes with whatever the human or a sibling agent has staged.
import os
import shutil
import tempfile

blob = subprocess.run(["git", "hash-object", "-w", "--stdin"], cwd=ROOT, input="module P where\n",
                      capture_output=True, text=True, check=True).stdout.strip()
with tempfile.TemporaryDirectory() as td:
    ix = Path(td) / "index"
    shutil.copy(ROOT / ".git" / "index", ix)
    env = {"GIT_INDEX_FILE": str(ix)}
    # A probe that MOVES from its home into src/ is a rename, and git reports it as `R`.
    subprocess.run(["git", "update-index", "--add", "--cacheinfo",
                    f"100644,{blob},agents/reports/ProbeGateTest.agda"],
                   cwd=ROOT, env={**os.environ, **env}, check=True, capture_output=True)
    r = run(["--staged"], env)
    check("a probe staged in its home passes", r.returncode == 0, r.stderr)

    subprocess.run(["git", "update-index", "--force-remove",
                    "agents/reports/ProbeGateTest.agda"],
                   cwd=ROOT, env={**os.environ, **env}, check=True, capture_output=True)
    subprocess.run(["git", "update-index", "--add", "--cacheinfo",
                    f"100644,{blob},src/ProbeGateTest.agda"],
                   cwd=ROOT, env={**os.environ, **env}, check=True, capture_output=True)
    r = run(["--staged"], env)
    check("the same probe RENAMED into src/ is refused", r.returncode == 1, r.stdout + r.stderr)
    check("and the message names the file",
          "src/ProbeGateTest.agda" in r.stderr, r.stderr)

# ---------------------------------------------------------------------------
# 6. The CLI. The retired flags must ERROR, never no-op with a success line.
# ---------------------------------------------------------------------------
print("every retired flag is a usage error, never a silent success")

for flag in ("--gate", "--stale", "--sweep", "--index", "--archive", "--delete",
             "--floor-hours", "--nonsense"):
    r = run([flag])
    check(f"{flag} exits 2", r.returncode == 2, f"exit {r.returncode}")
    check(f"{flag} prints no success line", "check-probes: clean" not in r.stdout, r.stdout)

r = run(["--check", "--staged"])
check("two modes at once exit 2", r.returncode == 2, f"exit {r.returncode}")

r = run(["--check"])
check("--check is green on the live tree", r.returncode == 0, r.stdout + r.stderr)
r = run([])
check("no argument defaults to --check and is green", r.returncode == 0, r.stdout + r.stderr)

# ---------------------------------------------------------------------------
# 7. The tree agrees with the rule: every tracked probe is in its home
# ---------------------------------------------------------------------------
print("the live tree agrees with the rule")

tracked = subprocess.run(["git", "ls-files"], cwd=ROOT, capture_output=True,
                         text=True, check=True).stdout.split("\n")
probes = [f for f in tracked if Path(f).name.startswith("Probe") and f.endswith(".agda")]
check(f"{len(probes)} tracked probe(s), all under agents/reports/",
      probes and all(f.startswith("agents/reports/") for f in probes),
      str([f for f in probes if not f.startswith("agents/reports/")][:5]))
check("no probe is tracked under src/",
      not any(f.startswith("src/") for f in tracked
              if Path(f).name.startswith("Probe")))


print("")
if failures:
    print(f"FAIL: {len(failures)} check(s) failed")
    for f in failures:
        print(f"  - {f}")
    sys.exit(1)
print("test_probe_gate: all checks passed")
