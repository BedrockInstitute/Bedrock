#!/usr/bin/env python3
"""LJ-1.331: rebuild every arm of the probe from the control arm.

`CondA.lagda.md` is the CONTROL: `src/L/Condensation.lagda.md` lines 1 to 3958,
which is the prefix that ends with the last line of `ForallAgree`, with the
module name changed on line 10 and the code fence closed. Every other arm is
that same file with ONE block changed around line 3849.

`arms.json` holds, for each arm, the line span of the control it replaces and
the text that replaces it. This script applies them, so the record can carry
`CondA.lagda.md` plus this script plus `arms.json`, which is 220 KB, instead of
thirteen near-identical copies of 212 KB each.

  --check   rebuild into memory and compare against the files on disk. It
            prints one line per arm and exits 1 on any difference.
  --write   write the arm files.

Run it from the repository root.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path("/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-331")


def build(name: str, spec: dict, control: list[str]) -> str:
    out = control[: spec["a_start"] - 1] + [spec["block"]] + control[spec["a_end"] :]
    out[9] = out[9].replace("LJ-1-331.CondA", "LJ-1-331." + name.split(".")[0])
    return "".join(out)


def main(argv: list[str]) -> int:
    mode = argv[1] if len(argv) > 1 else "--check"
    if mode not in ("--check", "--write"):
        print(__doc__)
        return 2
    control = (ROOT / "CondA.lagda.md").read_text(encoding="utf-8").splitlines(True)
    arms = json.loads((ROOT / "arms.json").read_text(encoding="utf-8"))
    bad = 0
    for stem, spec in sorted(arms.items()):
        name = stem.split(".")[0]
        text = build(stem, spec, control)
        target = ROOT / (name + ".lagda.md")
        if mode == "--write":
            target.write_text(text, encoding="utf-8")
            print(f"{name}: written")
            continue
        if not target.is_file():
            print(f"{name}: MISSING on disk")
            bad += 1
        elif target.read_text(encoding="utf-8") == text:
            print(f"{name}: identical")
        else:
            print(f"{name}: DIFFERS")
            bad += 1
    if mode == "--check":
        print("clean" if bad == 0 else f"{bad} arm(s) differ")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
