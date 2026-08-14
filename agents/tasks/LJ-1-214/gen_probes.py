#!/usr/bin/env python3
"""LJ-1.214 probe generator: the DELETE arm.

Builds ProbeDelete.agda, which is src/L/Condensation.lagda.md at commit
c8a628b~1 (the parent of the numeral-component commit), module renamed.  This
reverts commit c8a628b ONLY: it keeps commit a01ef58's envInK ar-membership
field and removes c8a628b's numeral component (46 type sites + 25 consumer
sites).  A probe is never a master edit.

The decisive contrast:
  ProbeMinusArNum (423ea83, rung 1)  reverts a01ef58 AND c8a628b  -> 1,165 ms
  ProbeDelete     (c8a628b~1)         reverts c8a628b only         -> ???
  ProbePlain      (master, rung 3)    keeps both                   -> 9,401 ms

If ProbeDelete reads ~1,165 ms, the numeral component carries the 8.2 s.
If it reads ~9,401 ms, a01ef58's envInK field carries it.
"""
import subprocess
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent.parent
FENCE = re.compile(r"```agda\n(.*?)```", re.S)
MODDECL = re.compile(r"module L\.Condensation\b")


def main() -> int:
    out = subprocess.run(
        ["git", "show", "c8a628b~1:src/L/Condensation.lagda.md"],
        cwd=ROOT, capture_output=True, text=True)
    assert out.returncode == 0, out.stderr
    blocks = FENCE.findall(out.stdout)
    code = "\n".join(blocks)
    code = MODDECL.sub("module LJ-1-214.ProbeDelete", code, count=1)
    dest = ROOT / "agents/tasks/LJ-1-214" / "ProbeDelete.agda"
    dest.write_text(code, encoding="utf-8")
    print(f"wrote {dest} ({len(code.splitlines())} lines, {len(blocks)} blocks)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
