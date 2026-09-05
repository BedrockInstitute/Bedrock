#!/usr/bin/env python3
"""[LJ-1.336] block parser and name-dependency closure for the dirty seven.

Re-derives the chapter's top-level blocks from the text (C-44), cross-checks
the spans against `agents/tasks/LJ-1-306/closure.json`, and computes the
closure of the seven dirty `Agree` modules.  Read only.
"""
import json
import re
import sys

CHAP = "src/L/Condensation.lagda.md"

DIRTY = [
    "DomainAgree", "WitnessAgree", "KeyAgree", "EnvOneAgree",
    "DefinesAgree", "SatGraphAgree", "LeafAgree",
]

IDENT_STOP = set(" \t\n()[]{};,\"'`")


def read_lines(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read().split("\n")


def parse_blocks(lines):
    """Return (blocks, fence_lines).

    blocks: list of dicts with name, start, end (1-based, inclusive).
    A top-level block starts at a fence line whose first character is not a
    space and is not a comment marker.
    """
    in_fence = False
    blocks = []
    fence_line = [False] * (len(lines) + 2)
    cur = None
    for i, raw in enumerate(lines, start=1):
        if raw.startswith("```"):
            if not in_fence:
                in_fence = raw.strip().startswith("```agda")
            else:
                in_fence = False
                if cur is not None:
                    cur["end"] = i - 1
                    cur = None
            continue
        if not in_fence:
            continue
        fence_line[i] = True
        if raw[:1] in ("", " ", "\t"):
            continue
        if raw.startswith("--"):
            if cur is not None:
                cur["end"] = i - 1
                cur = None
            continue
        # a new top-level declaration line
        name = decl_name(raw)
        if cur is not None:
            if cur["name"] == name:
                continue          # type signature then defining clause
            cur["end"] = i - 1
        cur = {"name": name, "start": i, "end": i, "head": raw}
        blocks.append(cur)
    return blocks, fence_line


def decl_name(raw):
    tok = raw.split()
    if not tok:
        return "?"
    if tok[0] in ("module", "private", "opaque", "record", "data", "postulate"):
        if tok[0] == "module" and len(tok) > 1:
            return tok[1]
        return tok[0] + " " + (tok[1] if len(tok) > 1 else "")
    # `f x y : T` or `f g : T` (a shared signature); take the first token
    return tok[0]


def tokens(text):
    out = set()
    cur = []
    for ch in text:
        if ch in IDENT_STOP:
            if cur:
                out.add("".join(cur))
                cur = []
        else:
            cur.append(ch)
    if cur:
        out.add("".join(cur))
    # also the dotted heads, so `SatGraphB.satGraphB` yields `SatGraphB`
    for t in list(out):
        if "." in t:
            out.add(t.split(".")[0])
    return out


def strip_comments(lines):
    """Drop `--` line comments and `{- -}` blocks inside the given text."""
    out = []
    depth = 0
    for ln in lines:
        res = []
        i = 0
        while i < len(ln):
            if ln.startswith("{-", i):
                depth += 1
                i += 2
                continue
            if ln.startswith("-}", i):
                depth = max(0, depth - 1)
                i += 2
                continue
            if depth == 0 and ln.startswith("--", i):
                break
            if depth == 0:
                res.append(ln[i])
            i += 1
        out.append("".join(res))
    return out


def main():
    lines = read_lines(CHAP)
    blocks, fence_line = parse_blocks(lines)
    by_name = {}
    for b in blocks:
        by_name.setdefault(b["name"], b)

    # cross-check against wave 1's spans
    w1 = json.load(open("agents/tasks/LJ-1-306/closure.json"))["spans"]
    agree = dis = 0
    dis_rows = []
    for name, (s, e) in w1.items():
        b = by_name.get(name)
        if b is None:
            dis += 1
            dis_rows.append((name, (s, e), None))
        elif b["start"] == s:
            agree += 1
        else:
            dis += 1
            dis_rows.append((name, (s, e), (b["start"], b["end"])))
    print(f"blocks parsed: {len(blocks)}; wave 1 spans: {len(w1)}")
    print(f"start-line agreement: {agree}; disagreement: {dis}")
    for row in dis_rows[:20]:
        print("  DISAGREE", row)

    # names defined by each block (the block head plus its inner top names is
    # too coarse; a module's own name is the reachable handle)
    defined = {b["name"] for b in blocks}

    # references
    refs = {}
    for b in blocks:
        body = strip_comments(lines[b["start"] - 1:b["end"]])
        toks = tokens("\n".join(body))
        refs[b["name"]] = {t for t in toks if t in defined and t != b["name"]}

    # closure over the dirty seven
    seen = set()
    stack = list(DIRTY)
    while stack:
        n = stack.pop()
        if n in seen:
            continue
        seen.add(n)
        for m in sorted(refs.get(n, ())):
            if m not in seen:
                stack.append(m)

    man = json.load(open("agents/tasks/LJ-1-306/manifest.json"))
    ported = {m[2] for m in man}
    ported.discard("private PairIs")

    order = [b["name"] for b in blocks]
    closure = [n for n in order if n in seen]
    extra = [n for n in closure if n not in ported and n not in DIRTY]

    print()
    print(f"closure size (blocks): {len(closure)}")
    print(f"of which wave 1 already ported: {len([n for n in closure if n in ported])}")
    print(f"the seven themselves: {len([n for n in closure if n in DIRTY])}")
    print(f"NEW blocks wave 2 must copy: {len(extra)}")
    for n in extra:
        b = by_name[n]
        nb = sum(1 for l in lines[b['start']-1:b['end']] if l.strip())
        print(f"   {b['start']:5d}-{b['end']:5d}  {nb:4d} nb  {n}")

    json.dump({
        "spans": {b["name"]: [b["start"], b["end"]] for b in blocks},
        "order": order,
        "closure": closure,
        "extra": extra,
        "refs": {k: sorted(v) for k, v in refs.items()},
    }, open("agents/tasks/LJ-1-336/closure336.json", "w"), ensure_ascii=False)


if __name__ == "__main__":
    main()
