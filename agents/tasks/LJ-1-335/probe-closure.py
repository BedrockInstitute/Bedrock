#!/usr/bin/env python3
"""Read-only closure arithmetic for LJ-1.335. It writes nothing to the tree."""
import sys
from pathlib import Path

ROOT = Path("/Users/alsg/Agentic/Bedrock")
sys.path.insert(0, str(ROOT / "scripts" / "measure"))
sys.path.insert(0, str(ROOT / "scripts"))
import ledger  # noqa: E402

files = ledger.countable_masters()
sizes = {f: ledger.count(f) for f in files}
graph = ledger.import_graph(files)

AC = "src/L/Model.lagda.md"
GCH = "src/L/GCH.lagda.md"
SQL = "src/L/Ordinal/SquareLaw.lagda.md"
ABS = "src/L/Absorption.lagda.md"
INJ = "src/L/InjChain.lagda.md"
BS = "src/L/BoundedSubset.lagda.md"
SC = "src/L/StageCardinal.lagda.md"


def lines(s):
    return sum(sizes.get(f, 0) for f in s)


def show(name, s):
    print(f"  {name:34} {len(s):3} masters {lines(s):6,} lines")


ac = ledger.closure(graph, [AC])
gch = ledger.closure(graph, [GCH])
print("BASELINE")
show("AC closure", ac)
show("GCH closure", gch)
show("SHARED", ac & gch)

print()
print("MEMBERSHIP")
for m in (SQL, ABS, INJ, BS, SC):
    print(f"  {m:38} AC={m in ac} GCH={m in gch}")

print()
print("PER-MODULE CLOSURES")
for m in (SQL, ABS, INJ, BS, SC):
    show(m, ledger.closure(graph, [m]))

print()
print("HYPOTHETICAL: GCH closure that also reaches a home")
for name, extra in (
    ("+ SquareLaw", [SQL]),
    ("+ Absorption", [ABS]),
    ("+ InjChain", [INJ]),
    ("+ Absorption + InjChain", [ABS, INJ]),
    ("+ BoundedSubset", [BS]),
    ("+ BoundedSubset + Absorption", [BS, ABS]),
):
    s = ledger.closure(graph, [GCH] + extra)
    sh = ac & s
    print(f"  GCH {name:28} {len(s):3} masters {lines(s):6,} lines "
          f"| SHARED {len(sh):3} {lines(sh):6,}")

print()
print("what Absorption adds to the GCH closure, module by module")
addition = ledger.closure(graph, [ABS]) - gch
for m in sorted(addition):
    print(f"  + {m:44} {sizes.get(m,0):5} lines")
print(f"  total {len(addition)} masters, {lines(addition)} lines")

print()
print("what BoundedSubset adds to the GCH closure, module by module")
addition2 = ledger.closure(graph, [BS]) - gch
for m in sorted(addition2):
    print(f"  + {m:44} {sizes.get(m,0):5} lines")
print(f"  total {len(addition2)} masters, {lines(addition2)} lines")

print()
print("sizes of the chapters in play")
for m in (SQL, ABS, INJ, BS, SC):
    print(f"  {m:44} {sizes.get(m,0):5} lines")
