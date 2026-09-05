#!/usr/bin/env python3
"""LJ-1.337 probe: import closure of one master, over src/ only.

It runs no Agda. It answers one question: can master X import master Y
without a cycle? It reads the `open import` and `import` lines of every
`.lagda.md` under src/ and walks the closure.
"""
from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
SRC = ROOT / "src"

IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.']+)")


def module_of(path: pathlib.Path) -> str:
    rel = path.relative_to(SRC)
    return str(rel).removesuffix(".lagda.md").replace("/", ".")


def graph() -> dict[str, set[str]]:
    g: dict[str, set[str]] = {}
    for path in sorted(SRC.rglob("*.lagda.md")):
        mod = module_of(path)
        deps: set[str] = set()
        infence = False
        for line in path.read_text(encoding="utf-8").splitlines():
            if line.startswith("```"):
                infence = not infence
                continue
            if not infence:
                continue
            m = IMPORT.match(line)
            if m:
                deps.add(m.group(1))
        g[mod] = deps
    return g


def closure(g: dict[str, set[str]], roots: list[str]) -> set[str]:
    seen: set[str] = set()
    stack = list(roots)
    while stack:
        m = stack.pop()
        if m in seen or m not in g:
            continue
        seen.add(m)
        stack.extend(g[m])
    return seen


def main() -> int:
    g = graph()
    pairs = [
        ("L.Ordinal.SquareLaw", "L.Choice.Stage"),
        ("L.Ordinal.SquareLaw", "L.Ordinal.Stages"),
        ("L.Choice.Stage", "L.Ordinal.SquareLaw"),
        ("L.Absorption", "L.Choice.Stage"),
        ("L.InjChain", "L.Choice.Stage"),
        ("L.Ordinal.SquareLaw", "L.Absorption"),
        ("L.Ordinal.SquareLaw", "L.InjChain"),
    ]
    for importer, target in pairs:
        cl = closure(g, [target])
        cycle = importer in cl
        print(f"{importer} imports {target}: "
              f"{'CYCLE' if cycle else 'LEGAL'} "
              f"(closure of {target} is {len(cl)} masters)")
    print()
    for m in ("L.Ordinal.SquareLaw", "L.Choice.Stage", "L.Absorption",
              "L.InjChain", "L.StageCardinal", "L.BoundedSubset"):
        print(f"{m}: closure {len(closure(g, [m]))} masters")
    return 0


if __name__ == "__main__":
    sys.exit(main())
