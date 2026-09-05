#!/usr/bin/env python3
"""LJ-1.204 probe: does the Deserialization rise track the interface size?

Computes the transitive import closure (bedrock masters under src/) of
src/L/Condensation.lagda.md at two commits, and sums the .agdai sizes of the
closure.  Reuses ledger.py's IMPORT_RE, FENCE and tracked_masters (C-26).

USAGE: .venv/bin/python agents/tasks/LJ-1-204/probe_closure.py COMMIT_A COMMIT_B
"""
import sys
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import ledger as L  # noqa: E402


def git_show(commit: str, path: str) -> str:
    out = subprocess.run(["git", "show", f"{commit}:{path}"], cwd=ROOT,
                         capture_output=True, text=True)
    return out.stdout if out.returncode == 0 else ""


def import_graph_at(commit: str, files: list[str]) -> dict[str, set[str]]:
    names = {f.removesuffix(".lagda.md").removeprefix("src/").replace("/", "."): f
             for f in files}
    graph: dict[str, set[str]] = {}
    for f in files:
        text = git_show(commit, f)
        graph[f] = {names[n] for n in L.IMPORT_RE.findall(text) if n in names}
    return graph


def closure(graph: dict[str, set[str]], roots: list[str]) -> set[str]:
    seen: set[str] = set()
    stack = list(roots)
    while stack:
        f = stack.pop()
        if f in seen:
            continue
        seen.add(f)
        stack.extend(graph.get(f, ()))
    return seen


def agdai_size(path: str) -> int:
    p = ROOT / "_build/2.8.0/agda" / (path.removesuffix(".lagda.md") + ".agdai")
    return p.stat().st_size if p.exists() else 0


def main() -> int:
    a, b = sys.argv[1], sys.argv[2]
    files = L.tracked_masters()
    ga = import_graph_at(a, files)
    gb = import_graph_at(b, files)
    ca = closure(ga, ["src/L/Condensation.lagda.md"])
    cb = closure(gb, ["src/L/Condensation.lagda.md"])
    print(f"commit A {a}: closure {len(ca)} masters")
    print(f"commit B {b}: closure {len(cb)} masters")
    added = sorted(cb - ca)
    removed = sorted(ca - cb)
    print("\nADDED (in B, not A):")
    for f in added:
        print(f"  + {f}  source={Path(f).stat().st_size if (ROOT/f).exists() else 0}  agdai={agdai_size(f)}")
    print("\nREMOVED (in A, not B):")
    for f in removed:
        print(f"  - {f}")
    sa = sum(agdai_size(f) for f in ca)
    sb = sum(agdai_size(f) for f in cb)
    print(f"\nsum of .agdai sizes, closure A: {sa:,} bytes ({sa/1e6:.2f} MB)")
    print(f"sum of .agdai sizes, closure B: {sb:,} bytes ({sb/1e6:.2f} MB)")
    print(f"delta: {sb-sa:+,} bytes ({(sb-sa)/1e6:+.2f} MB)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
