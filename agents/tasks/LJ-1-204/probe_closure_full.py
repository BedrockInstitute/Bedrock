#!/usr/bin/env python3
"""LJ-1.204 probe: full interface closure incl. Cubical, at two commits.

Resolves bedrock masters (src/, from git at a commit) AND cubical library
modules (pinned, read live) transitively, then sums .agdai sizes.

Reuses ledger.py's IMPORT_RE and tracked_masters (C-26).
"""
import sys
import subprocess
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import ledger as L  # noqa: E402

CUBICAL_SRC = Path("/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical")
CUBICAL_AGDAI = CUBICAL_SRC / "_build/2.8.0/agda"

# map module name -> (source-file, agdai-file)
def bedrock_index(files):
    out = {}
    for f in files:
        n = f.removesuffix(".lagda.md").removeprefix("src/").replace("/", ".")
        out[n] = (f, ROOT / "_build/2.8.0/agda" / (f.removesuffix(".lagda.md") + ".agdai"))
    return out


def cubical_index():
    out = {}
    for agdai in CUBICAL_AGDAI.rglob("*.agdai"):
        rel = agdai.relative_to(CUBICAL_AGDAI).with_suffix("")
        name = ".".join(rel.parts)
        src = CUBICAL_SRC / Path(str(rel) + ".agda")
        out[name] = (src, agdai)
    # prim modules have no file; ignore
    return out


def git_show(commit, path):
    o = subprocess.run(["git", "show", f"{commit}:{path}"], cwd=ROOT,
                       capture_output=True, text=True)
    return o.stdout if o.returncode == 0 else ""


def text_of(commit, kind, path):
    if kind == "bedrock":
        return git_show(commit, path)
    if kind == "cubical":
        try:
            return path.read_text(encoding="utf-8")
        except OSError:
            return ""
    return ""


def closure_sizes(commit):
    files = L.tracked_masters()
    bed = bedrock_index(files)
    cub = cubical_index()
    index = {n: ("bedrock", v[0], v[1]) for n, v in bed.items()}
    index.update({n: ("cubical", v[0], v[1]) for n, v in cub.items()})

    sizes = {}   # module name -> agdai bytes
    seen = set()

    def visit(name, kind, src):
        if name in seen:
            return
        seen.add(name)
        agdai = index.get(name, (None, None, None))[2]
        if isinstance(agdai, Path) and agdai.exists():
            sizes[name] = agdai.stat().st_size
        txt = text_of(commit, kind, src)
        for imp in L.IMPORT_RE.findall(txt):
            if imp in index and imp not in seen:
                k2, s2, _ = index[imp]
                visit(imp, k2, s2)

    for name, (kind, src, _) in index.items():
        # only follow from roots below, not all
        pass

    root = "L.Condensation"
    k, s, _ = index[root]
    visit(root, k, s)
    return sizes, seen


def main():
    a, b = sys.argv[1], sys.argv[2]
    sa, seena = closure_sizes(a)
    sb, seenb = closure_sizes(b)
    print(f"commit A {a}: {len(seena)} modules, {sum(sa.values()):,} bytes = {sum(sa.values())/1e6:.2f} MB")
    print(f"commit B {b}: {len(seenb)} modules, {sum(sb.values()):,} bytes = {sum(sb.values())/1e6:.2f} MB")
    print(f"delta: {sum(sb.values())-sum(sa.values()):+,} bytes = {(sum(sb.values())-sum(sa.values()))/1e6:+.2f} MB")
    added = seenb - seena
    removed = seena - seenb
    print(f"\nADDED modules ({len(added)}):")
    for n in sorted(added):
        print(f"  + {n}  {sb.get(n, 0):,} B")
    print(f"\nREMOVED modules ({len(removed)}):")
    for n in sorted(removed):
        print(f"  - {n}")


if __name__ == "__main__":
    sys.exit(main())
