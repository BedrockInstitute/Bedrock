#!/usr/bin/env python3
"""[LJ-1.336] assemble `GenDirty.agda`: the hand-written head, then the
wave-2 blocks copied VERBATIM from the chapter, then the manifest."""
import json
import sys

sys.path.insert(0, "agents/tasks/LJ-1-336")
from closure336 import read_lines, DIRTY, CHAP

HEAD = "agents/tasks/LJ-1-336/head336.agda"
OUT = "agents/tasks/LJ-1-336/GenDirty.agda"

lines = read_lines(CHAP)
c = json.load(open("agents/tasks/LJ-1-336/closure336.json"))
spans = c["spans"]
names = c["extra"] + DIRTY

out = read_lines(HEAD)
manifest = []
for n in names:
    s, e = spans[n]
    body = lines[s - 1:e]
    out.append("")
    start_line = len(out) + 1
    out.extend(body)
    manifest.append([s, e, n, start_line, start_line + len(body) - 1])

out.append("")
out.append("-- =====================================================================")
out.append("-- MANIFEST.  Each block, its source range in")
out.append("-- src/L/Condensation.lagda.md, and its range in this file.")
out.append("-- =====================================================================")
for s, e, n, ps, pe in manifest:
    out.append(f"-- {n}: :{s}-{e}  ->  this file :{ps}-{pe}")

with open(OUT, "w", encoding="utf-8") as fh:
    fh.write("\n".join(out) + "\n")

json.dump(manifest, open("agents/tasks/LJ-1-336/manifest336.json", "w"),
          ensure_ascii=False)

nb_copied = sum(1 for s, e, n, ps, pe in manifest
                for l in lines[s - 1:e] if l.strip())
head_nb = sum(1 for l in read_lines(HEAD) if l.strip())
head_code = sum(1 for l in read_lines(HEAD)
                if l.strip() and not l.strip().startswith("--"))
print(f"blocks: {len(manifest)}")
print(f"copied non-blank lines: {nb_copied}")
print(f"head non-blank lines: {head_nb} (code {head_code}, comment {head_nb - head_code})")
print(f"port total lines: {len(out)}")
