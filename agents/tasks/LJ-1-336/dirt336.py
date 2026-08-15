#!/usr/bin/env python3
"""[LJ-1.336] the DIRT census: which COMMITTED `src/` names the wave-2 text
reaches, and whether `GenModel` delivers a generic twin.  Read only."""
import glob
import json
import sys

sys.path.insert(0, "agents/tasks/LJ-1-336")
from closure336 import read_lines, parse_blocks, strip_comments, tokens, DIRTY, CHAP

lines = read_lines(CHAP)
blocks, _ = parse_blocks(lines)
by_name = {b["name"]: b for b in blocks}
c = json.load(open("agents/tasks/LJ-1-336/closure336.json"))
extra = c["extra"]
chapter_names = set(by_name)


def top_names(path):
    """Top-level and one-level-nested declaration names of an Agda master."""
    out = set()
    src = read_lines(path)
    in_fence = path.endswith(".agda")
    for ln in src:
        if ln.startswith("```"):
            in_fence = ln.strip().startswith("```agda")
            continue
        if not in_fence:
            continue
        s = ln.strip()
        if not s or s.startswith("--") or s.startswith("{-"):
            continue
        t = s.split()
        if t[0] in ("module", "record", "data"):
            if len(t) > 1 and t[1] not in ("_",):
                out.add(t[1])
            continue
        if t[0] in ("open", "import", "private", "opaque", "where", "field",
                    "syntax", "infix", "infixl", "infixr", "renaming",
                    "using", "constructor", "{-#"):
            continue
        if ":" in s and not s.startswith("("):
            # `f x y : T`  or  `f g : T`
            head = s.split(":")[0].split()
            if head:
                out.add(head[0])
    return out


src_index = {}
for path in sorted(glob.glob("src/**/*.lagda.md", recursive=True)):
    if path == CHAP:
        continue
    for n in top_names(path):
        src_index.setdefault(n, path)

gm_names = top_names("agents/tasks/LJ-1-210/GenModel.agda")

# what the wave-2 text reaches
wave2 = extra + DIRTY
toks = set()
per_name = {}
for n in wave2:
    b = by_name[n]
    body = strip_comments(lines[b["start"] - 1:b["end"]])
    tk = tokens("\n".join(body))
    per_name[n] = tk
    toks |= tk

man = json.load(open("agents/tasks/LJ-1-306/manifest.json"))
ported = {m[2] for m in man}

# a committed reach is a token that names a src/ delivery outside the chapter
committed = sorted(t for t in toks
                   if t in src_index and t not in chapter_names and len(t) > 1)

print("COMMITTED `src/` NAMES THE WAVE-2 TEXT REACHES")
print(f"{'name':28s} {'GenModel twin':14s} home")
gm_yes = gm_no = 0
for t in committed:
    twin = "YES" if t in gm_names else "no"
    if t in gm_names:
        gm_yes += 1
    else:
        gm_no += 1
    print(f"{t:28s} {twin:14s} {src_index[t]}")
print()
print(f"total committed reaches: {len(committed)};  GenModel twin: {gm_yes};  NO twin: {gm_no}")
print()
print("THE NO-TWIN LIST, with the blocks that reach it")
for t in committed:
    if t in gm_names:
        continue
    who = [n for n in wave2 if t in per_name[n]]
    print(f"  {t:26s} {src_index[t]}")
    print(f"     reached by: {', '.join(who)}")
