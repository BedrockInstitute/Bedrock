#!/usr/bin/env python3
"""[LJ-1.336] the NEGATIVE CONTROL.  Two deliberate breaks in the ported
file, each written to its own module, so a green run means nothing until
these two go red at the point the break sits.

Control A, LOCALITY: one projection flipped inside a copied `DomainAgree`
line.  Agda must refuse AT THAT LINE.
Control B, NON-VACUITY: the re-stated `isCodeAt` gets the wrong arity.  The
restatement is hand-copied, so if the seven's copied proofs did not really
constrain it, this would pass.  Agda must refuse INSIDE the copied proofs.
"""
import json
import sys

sys.path.insert(0, "agents/tasks/LJ-1-336")
from closure336 import read_lines

PORT = "agents/tasks/LJ-1-336/GenDirty.agda"
port = read_lines(PORT)


def emit(name, old, new, must_be_unique=True):
    hits = [i for i, l in enumerate(port) if old in l]
    if must_be_unique and len(hits) != 1:
        print(f"{name}: expected ONE site for {old!r}, found {len(hits)}: "
              f"{[h + 1 for h in hits]}")
        return None
    i = hits[0]
    body = list(port)
    body[i] = body[i].replace(old, new)
    body[0] = body[0]
    text = "\n".join(body).replace("module LJ-1-336.GenDirty ",
                                   f"module LJ-1-336.{name} ")
    path = f"agents/tasks/LJ-1-336/{name}.agda"
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(text + "\n")
    print(f"{name}: broke port line {i + 1}")
    print(f"   was: {port[i]}")
    print(f"   now: {body[i]}")
    return i + 1


sites = {}
sites["ControlA"] = emit(
    "ControlA",
    "    , ( λ hx → PT.rec squash₁",
    "    , ( λ hx → PT.rec squash₁ {- CONTROL A -}")
# the real break: flip a projection in DomainAgree's `out`
port_a = read_lines("agents/tasks/LJ-1-336/ControlA.agda")
for i, l in enumerate(port_a):
    if l.strip() == "( λ hx → h x .fst":
        port_a[i] = l.replace(".fst", ".snd")
        sites["ControlA"] = i + 1
        print(f"ControlA: real break at line {i + 1}: {port_a[i].strip()}")
        break
with open("agents/tasks/LJ-1-336/ControlA.agda", "w", encoding="utf-8") as fh:
    fh.write("\n".join(port_a) + "\n")

sites["ControlB"] = emit(
    "ControlB",
    "  isCodeAt c w = keyArityAtL c 1 ∧̇ hasWitnessAt w c",
    "  isCodeAt c w = keyArityAtL c 0 ∧̇ hasWitnessAt w c")

json.dump(sites, open("agents/tasks/LJ-1-336/control336.json", "w"))
print(sites)
