#!/usr/bin/env python3
"""[LJ-1.336] the zero, verified two ways.

Method 1, the per-block exact-run search: every copied block must appear in
the port as one contiguous run, in order.
Method 2, the whole-sequence diff `[LJ-1.308]` used: concatenate the expected
text and align it against the port with `difflib.SequenceMatcher`.  A run
search can report zero because nothing changed OR because it cannot see the
change; a whole-sequence alignment reports `delete` and `replace`.
Method 3, the gap restatement: diff each re-stated committed name against its
`src/L/Coding/` source, line for line.
"""
import difflib
import json
import sys

sys.path.insert(0, "agents/tasks/LJ-1-336")
from closure336 import read_lines, CHAP

PORT = "agents/tasks/LJ-1-336/GenDirty.agda"

chap = read_lines(CHAP)
port = read_lines(PORT)
manifest = json.load(open("agents/tasks/LJ-1-336/manifest336.json"))

# ---- method 1: exact contiguous runs, in order
expected = []
missing = []
cursor = 0
for s, e, name, ps, pe in manifest:
    body = chap[s - 1:e]
    expected.extend(body)
    # search the port for this block as a contiguous run at or after cursor
    found = -1
    for i in range(cursor, len(port) - len(body) + 1):
        if port[i:i + len(body)] == body:
            found = i
            break
    if found < 0:
        missing.append(name)
    else:
        cursor = found + len(body)
print("METHOD 1: per-block exact runs, in order")
print(f"  blocks: {len(manifest)};  NOT found as an exact ordered run: {len(missing)}")
for m in missing:
    print("   MISSING:", m)

# ---- method 2: whole-sequence diff
sm = difflib.SequenceMatcher(None, expected, port, autojunk=False)
dels = reps = ins = 0
rep_hunks = 0
for tag, i1, i2, j1, j2 in sm.get_opcodes():
    if tag == "delete":
        dels += i2 - i1
    elif tag == "replace":
        reps += i2 - i1
        rep_hunks += 1
    elif tag == "insert":
        ins += j2 - j1
print()
print("METHOD 2: whole-sequence diff, expected against port")
print(f"  expected lines: {len(expected)}  (non-blank {sum(1 for l in expected if l.strip())})")
print(f"  port lines: {len(port)}")
print(f"  delete lines: {dels}")
print(f"  replace hunks: {rep_hunks}  (lines {reps})")
print(f"  insert lines: {ins}  (non-blank "
      f"{sum(1 for tag, i1, i2, j1, j2 in sm.get_opcodes() if tag == 'insert' for l in port[j1:j2] if l.strip())})")

# ---- method 3: the gap restatement against src
GAPS = [
    ("keyArityAtL", "src/L/Coding/CodeSet.lagda.md", 135, 136),
    ("hasWitnessAt", "src/L/Coding/CodeSet.lagda.md", 240, 242),
    ("Graph Ci Ti Bi sh3", "src/L/Coding/Graph.lagda.md", 85, 92),
    ("twelveAt", "src/L/Coding/Graph.lagda.md", 94, 101),
    ("satGraphOn", "src/L/Coding/Graph.lagda.md", 103, 111),
    ("satGraphAt", "src/L/Coding/Graph.lagda.md", 203, 205),
    ("envOneAt", "src/L/Coding/Powerset.lagda.md", 128, 129),
    ("DefinesAt", "src/L/Coding/Powerset.lagda.md", 217, 220),
    ("isCodeAt", "src/L/Coding/Powerset.lagda.md", 297, 298),
    ("Powerset sh3", "src/L/Coding/Powerset.lagda.md", 433, 435),
    ("DefBody", "src/L/Coding/Powerset.lagda.md", 437, 440),
]
print()
print("METHOD 3: the gap restatement against `src/L/Coding/`")
print("  each source line, stripped of its leading indent, must appear in the")
print("  port's head region, stripped the same way")
head = [l.strip() for l in port[:200] if l.strip()]
total = same = 0
for name, path, s, e in GAPS:
    src = [l.strip() for l in read_lines(path)[s - 1:e] if l.strip()]
    hit = sum(1 for l in src if l in head)
    total += len(src)
    same += hit
    flag = "" if hit == len(src) else "   <-- MISMATCH"
    print(f"  {name:16s} {path}:{s}-{e}  {hit}/{len(src)}{flag}")
    if hit != len(src):
        for l in src:
            if l not in head:
                print("      not found:", l)
print(f"  TOTAL: {same}/{total} re-stated lines identical to the source")
