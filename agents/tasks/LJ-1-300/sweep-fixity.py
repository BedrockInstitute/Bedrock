#!/usr/bin/env python3
"""LJ-1.300 sweep, FINAL.

Universe: every BINARY INFIX operator `_op_` declared in src/ OR in the
cubical library OR in Agda's own builtins, that carries NO fixity
declaration anywhere.  Such an operator takes Agda's default level and
binds TIGHTER than `×` (infixr 5), `⊎` and `≡`.

Shape tested, on declarations joined across continuation lines:

    A  LOOSE  B  OP  C    /    A  OP  B  LOOSE  C

with LOOSE and OP at ONE bracket depth and no `→`, `=` or `;` between
them at that depth.
"""
import re, pathlib, collections

ROOT = pathlib.Path("/Users/alsg/Agentic/Bedrock")
SRC = ROOT / "src"
CUB = pathlib.Path("/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical")

OPEN, CLOSE = "({[⟨⟪", ")}]⟩⟫"
FIX = re.compile(r"^\s*(infix|infixl|infixr)\s+(-?\d+)\s+(.*)$")
BIN = re.compile(r"^\s*(_[^\s:()_]+_)\s*:")     # _op_ : ...   (binary infix)

def code_lines(path):
    txt = path.read_text(encoding="utf-8", errors="replace").splitlines()
    if path.suffix == ".agda":
        yield from enumerate(txt, 1); return
    inside = False
    for i, l in enumerate(txt, 1):
        s = l.strip()
        if s.startswith("```agda"):
            inside = True; continue
        if s.startswith("```") and inside:
            inside = False; continue
        if inside:
            yield i, l

src_files = sorted(list(SRC.rglob("*.lagda.md")) + list(SRC.rglob("*.agda")))
lib_files = sorted(CUB.rglob("*.agda"))

fixed, binops = set(), {}
for f in src_files + lib_files:
    where = "src" if f in src_files else "lib"
    try:
        it = code_lines(f) if where == "src" else enumerate(
            f.read_text(encoding="utf-8", errors="replace").splitlines(), 1)
    except Exception:
        continue
    for n, l in it:
        m = FIX.match(l)
        if m:
            for nm in m.group(3).replace(";", " ").split():
                fixed.add(nm)
            continue
        m = BIN.match(l)
        if m:
            binops.setdefault(m.group(1), []).append((where, f, n))

import unicodedata
def symbolic(t):
    return bool(t) and not unicodedata.category(t[0]).startswith(("L","N","M"))
undeclared = {k: v for k, v in binops.items() if k not in fixed}
syms = {}
for k, v in undeclared.items():
    b = k[1:-1]
    if not symbolic(b):
        continue
    syms.setdefault(b, []).extend(v)

print("=== binary infix operators with NO fixity declaration ===")
print("   total:", len(undeclared), " distinct bare symbols:", len(syms))
syms = {b: v for b, v in syms.items() if any(w == "src" for w, _, _ in v)}
in_src = syms
print("   declared in src/:", len(in_src))
for b in sorted(in_src):
    print("     ", b, "  <-", ", ".join(
        f"{p.relative_to(ROOT) if w=='src' else p.name}:{n}" for w, p, n in in_src[b][:3]))
print()

LOOSE = ["×", "⊎", "≡"]
SEP = ["→", "=", ";"]

def depths(code):
    d = 0; out = []
    for ch in code:
        if ch in OPEN: out.append(d); d += 1
        elif ch in CLOSE: d -= 1; out.append(d)
        else: out.append(d)
    return out

def infix_pos(code, sym):
    return [m.start() for m in re.finditer(re.escape(sym), code)
            if m.start() > 0 and m.end() < len(code)
            and code[m.start()-1] == " " and code[m.end()] == " "]

hits = []
for f in src_files:
    buf = None; groups = []
    for n, l in code_lines(f):
        code = l.split("--")[0].rstrip()
        if not code.strip():
            if buf: groups.append((start, buf)); buf = None
            continue
        indent = len(code) - len(code.lstrip())
        if buf is None:
            buf, start, base = code.strip(), n, indent
        elif indent > base:
            buf += " " + code.strip()
        else:
            groups.append((start, buf)); buf, start, base = code.strip(), n, indent
    if buf: groups.append((start, buf))

    for n, code in groups:
        dep = depths(code)
        for op in syms:
            if op in LOOSE: continue
            for i_op in infix_pos(code, op):
                d = dep[i_op]
                for lo in LOOSE:
                    for i_lo in infix_pos(code, lo):
                        if dep[i_lo] != d: continue
                        a, b = sorted((i_lo, i_op))
                        if min(dep[a:b]) < d: continue
                        if any(dep[a + m2.start()] == d
                               for sp in SEP
                               for m2 in re.finditer(re.escape(sp), code[a:b])):
                            continue
                        hits.append((f, n, lo, op, "L" if i_lo < i_op else "R", code))

seen = {}
for f, n, lo, op, side, code in hits:
    seen.setdefault((f, n), (lo, op, side, code))
print("=== DEFECT-SHAPE hits:", len(hits), " distinct lines:", len(seen))
for (f, n), (lo, op, side, code) in sorted(seen.items(), key=lambda x: str(x[0])):
    print(f"{f.relative_to(ROOT)}:{n}  [{side}: {lo} ~ {op}]  {code[:150]}")
