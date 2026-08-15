#!/usr/bin/env python3
"""Regression tests for `scripts/gate/check-dd25-review-named.py`.

WHY THIS FILE EXISTS. DD25's own enforcement point is the PLAN section 11 row:
a negative return's row names the code of the adversarial review dispatched
against it. `[LJ-1.183]` measured that no negative row named a review code;
the orchestrator fixed four rows and then let four MORE negatives go
unreviewed in the same session. The gate exists because the orchestrator
forgets, and these tests pin the three things that must never silently invert:

1. A negative verdict with no review named FAILS, and the message names the
   row and says what to do.
2. A negative verdict that names a review code PASSES (the four repaired
   controls are the live evidence).
3. The escapes stay NARROW: a declared reason must carry a reason, a review
   row is exempt because it IS the review, and a non-review code cited in the
   detail cell does not satisfy the gate.

Run: `python3 scripts/tests/test_dd25_review_named.py`
"""

from __future__ import annotations

import importlib.util
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
spec = importlib.util.spec_from_file_location(
    "check_dd25_review_named", ROOT / "scripts" / "gate/check-dd25-review-named.py"
)
cd25 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cd25)

failures: list[str] = []


def check(name: str, condition: bool, detail: str = "") -> None:
    if condition:
        print(f"  ok    {name}")
    else:
        print(f"  FAIL  {name}{(': ' + detail) if detail else ''}")
        failures.append(name)


REVIEW_ROWS = [
    ("LJ-9.1", "DD25 review of LJ-9.0's NO-GO", "UPHELD", "the numbers hold"),
    ("LJ-9.2", "DD25 review of LJ-9.3's stop", "OVERTURNED", "wrong price"),
    ("LJ-9.4-R", "DD25 review of LJ-9.9's NO-GO", "UPHELD", "re-derived"),
]


def findings(*rows: tuple[str, str, str, str]) -> list[str]:
    defects, _ = cd25.check_rows(list(rows) + REVIEW_ROWS)
    return defects


def one_finding(row: tuple[str, str, str, str]) -> list[str]:
    return cd25.row_findings(
        row, cd25.review_codes([row] + REVIEW_ROWS))


# ---------------------------------------------------------------------------
# 1. THE DEFECT. A negative verdict with no review named.
# ---------------------------------------------------------------------------
print("the defect fails")

NO_REVIEW = ("LJ-9.9", "Build the widget", "NO-GO: the band does not fit",
             "the assembly typechecks, the price does not")
f = one_finding(NO_REVIEW)
check("a negative verdict with no review is a finding", bool(f))
check("the message names the row", any("LJ-9.9" in line for line in f))
check("the message quotes the verdict", any("NO-GO" in line for line in f))
check("the message says what to do",
      any("DD25 review [LJ-x.y]" in line for line in f))

check("every table token fires on its own",
      all(cd25.negative_tokens(t) == [t] for t, _, _ in cd25.NEGATIVE_VERDICT))
check("a prefix token catches its inflected form",
      cd25.negative_tokens("STOPPED; the BRIEF dominates") == ["STOP"]
      and cd25.negative_tokens("REFUTABLE, machine-checked") == ["REFUTABLE"]
      and cd25.negative_tokens("NO, WALLS AT 265 s") == ["WALL"])
check("a word token does not fire on a longer word",
      cd25.negative_tokens("ZEROED, GREEN") == []
      and cd25.negative_tokens("GOOD ENOUGH") == [])
check("a positive row with no token passes",
      not one_finding(("LJ-9.8", "Build", "DELIVERED, GREEN", "under the bar")))


# ---------------------------------------------------------------------------
# 2. THE FIX. A negative verdict that names its review's code.
# ---------------------------------------------------------------------------
print("naming the review clears")

check("bracketed citation clears",
      not one_finding(("LJ-9.9", "Build", "NO-GO. DD25 review [LJ-9.2] UPHELD",
                       "the price holds")))
check("bare -R citation clears",
      not one_finding(("LJ-9.9", "Build", "NO-GO, OVERTURNED by LJ-9.4-R",
                       "the probe was wrong")))
check("an abbreviated -R citation clears",
      not one_finding(("LJ-9.9", "Build", "NO, overturned by 9.4-R",
                       "the probe was wrong")))
check("the four repaired controls clear on the real tree", True)

PLAN = (ROOT / "dev" / "PLAN.md").read_text(encoding="utf-8")
real_rows = cd25.index_rows(PLAN)
reviews = cd25.review_codes(real_rows)
for code in ("LJ-1.162", "LJ-1.165", "LJ-1.169", "LJ-1.172"):
    row = next(r for r in real_rows if r[0] == code)
    check(f"{code} names its review and clears",
          not cd25.row_findings(row, reviews))

check("a cited code that is NOT a review does not clear",
      bool(one_finding(("LJ-9.9", "Build", "NO-GO: see [LJ-9.8]",
                        "LJ-9.8 is a build row, not a review"))))


# ---------------------------------------------------------------------------
# 3. THE ESCAPES, AND THEIR NARROWNESS.
# ---------------------------------------------------------------------------
print("the escapes stay narrow")

check("a declared reason with a reason clears",
      not one_finding(("LJ-9.9", "Build",
                       "GO AT 20 LINES, AND A NEW WALL. "
                       "DD25 review not needed: the GO is the verdict",
                       "the wall is a finding for a later task")))
check("an empty reason does not clear",
      bool(one_finding(("LJ-9.9", "Build",
                        "STOP. DD25 review not needed:",
                        "no reason at all"))))
check("a review row is exempt even when its verdict looks negative",
      not one_finding(("LJ-9.2", "DD25 review of LJ-9.3's stop",
                       "OVERTURNED: A FIXED-SHAPE NO-GO",
                       "the price was wrong")))
check("an -R row is exempt",
      not one_finding(("LJ-9.4-R", "DD25 review of LJ-9.9", "UPHOLD",
                       "the numbers hold")))


# ---------------------------------------------------------------------------
# 4. THE REAL TREE, VIA THE CLI.
# ---------------------------------------------------------------------------
print("the real tree")

PY = sys.executable
SCRIPT = str(ROOT / "scripts" / "gate/check-dd25-review-named.py")


def run(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run([PY, SCRIPT, *args], cwd=ROOT,
                          capture_output=True, text=True)


r = run()
check("the real tree exits 0 after grandfathering", r.returncode == 0,
      r.stderr[-400:])
check("the run prints the backlog count",
      f"{len(cd25.PRE_EPOCH)} frozen pre-epoch" in r.stdout, r.stdout)
check("the backlog count is the PRE_EPOCH size",
      f"{len(cd25.PRE_EPOCH)}" in r.stdout
      and "0 new defects" in r.stdout)
check("the frozen rows are reported, not failed", "LJ-1.196" in r.stdout
      and "DD25 unmet" not in r.stdout)

# A synthetic negative row inside the live index must turn the run red. The
# whole LJ-3.9 line is replaced so the new row keeps exactly four cells.
import re as _re
SYNTH = _re.sub(
    r"\| LJ-3\.9 \|.*\|.*\|.*\|\s*$",
    "| LJ-9.99 | Build the widget | NO-GO: the band does not fit | "
    "the price does not |\n"
    "| LJ-3.9 | The prose phase opens | planned | DD23 keeps the prose closed |",
    PLAN, count=1, flags=_re.M)
assert "LJ-9.99" in SYNTH and "| LJ-3.9 |" in SYNTH
with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as tf:
    tf.write(SYNTH)
    fake = Path(tf.name)
try:
    rs = subprocess.run([PY, SCRIPT, "--plan", str(fake)], cwd=ROOT,
                        capture_output=True, text=True)
    check("a synthetic negative row makes the run red", rs.returncode == 1,
          f"got {rs.returncode}: {rs.stdout} {rs.stderr}")
    check("the red names the synthetic row", "LJ-9.99" in rs.stderr
          or "LJ-9.99" in rs.stdout)
finally:
    fake.unlink(missing_ok=True)


print("")
if failures:
    print(f"FAIL: {len(failures)} check(s) failed")
    for f in failures:
        print(f"  - {f}")
    sys.exit(1)
print("test_dd25_review_named: all checks passed")
