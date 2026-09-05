#!/usr/bin/env python3
"""LJ-1.204 probe generator: renamed copies of Condensation at a commit.

Each probe is the ```agda code of src/L/Condensation.lagda.md at a given
commit (or the working tree), with the top module renamed, written as a
plain .agda file under this task dir.

Modes:
  --commit <sha>     read the file at that commit
  --drop-last        drop the last code fence (removes THE SUPPLY / KValue / Bound)
"""
import sys
import subprocess
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent.parent
FENCE = re.compile(r"```agda\n(.*?)```", re.S)
MODDECL = re.compile(r"module L\.Condensation\b")

def code_blocks(text: str) -> list[str]:
    return FENCE.findall(text)

def main():
    args = sys.argv[1:]
    commit = None
    drop_last = False
    out_name = None
    i = 0
    while i < len(args):
        if args[i] == "--commit":
            commit = args[i + 1]; i += 2
        elif args[i] == "--drop-last":
            drop_last = True; i += 1
        elif args[i] == "--out":
            out_name = args[i + 1]; i += 2
        else:
            i += 1
    if commit:
        o = subprocess.run(["git", "show", f"{commit}:src/L/Condensation.lagda.md"],
                           cwd=ROOT, capture_output=True, text=True)
        text = o.stdout
        assert o.returncode == 0, o.stderr
    else:
        text = (ROOT / "src/L/Condensation.lagda.md").read_text(encoding="utf-8")
    blocks = code_blocks(text)
    if drop_last:
        blocks = blocks[:-1]
    code = "\n".join(blocks)
    newname = out_name or "Probe"
    code = MODDECL.sub(f"module LJ-1-204.Probe{newname}", code, count=1)
    dest = ROOT / "agents/tasks/LJ-1-204" / f"Probe{newname}.agda"
    dest.write_text(code, encoding="utf-8")
    print(f"wrote {dest} ({len(code.splitlines())} lines, {len(blocks)} blocks)")

if __name__ == "__main__":
    sys.exit(main())
