"""[LJ-1.612] sweep: how many probes does the rehoming defect affect?

The property, in words (C-42: state it before writing the grep):

  A tracked .agda file under agents/tasks/ is AFFECTED by the
  rehoming defect iff its declared top-level module name does not
  spell the name its PATH gives it under the library's include root
  agents/tasks/ (bedrock.agda-lib: `include: src agents/tasks`).
  For such a file, import by the declared name through the library
  fails ([FileNotFound], runs/w3-1.out:5-16), and import by the path
  name is refused ([ModuleNameUnexpected], runs/dot-1.out:6-8). The
  defect is in the declaration, measured at the one site
  agents/tasks/LJ-1-136/ProbeLJ1136B.agda:35.

Operationalization: the first column-0 `module NAME ...` line of the
file is its top-level declaration (a file without one is importable
by its path name and is NOT affected). The path name is the file's
path relative to agents/tasks/ with / mapped to . and .agda dropped.
Affected = declared != path name.

Weaker filter (for the blind-spot report, C-53/C-42 style): every
file whose top-level declaration is a single component (no dot),
whether or not that single component is actually the path name (the
latter only happens at the include roots themselves).
"""

import re
import sys
from pathlib import Path

root = Path(sys.argv[1]).resolve()
tasks = root / "agents" / "tasks"

MOD = re.compile(r"^module\s+([A-Za-z][A-Za-z0-9-]*(?:\.[A-Za-z][A-Za-z0-9-]*)*)")
ALIAS = re.compile(r"^module\s+[A-Za-z][A-Za-z0-9-]*(?:\.[A-Za-z][A-Za-z0-9-]*)*\s*=\s")

affected = []
weaker = []
scanned = 0
for p in sorted(tasks.rglob("*.agda")):
    rel = p.relative_to(tasks)
    scanned += 1
    path_name = ".".join(rel.with_suffix("").parts)
    decl = None
    for line in p.read_text(encoding="utf-8").splitlines():
        if ALIAS.match(line):
            continue  # module X = alias: not a top-level declaration
        m = MOD.match(line)
        if m:
            decl = m.group(1)
            break
    if decl is None:
        continue
    if "." not in decl:
        weaker.append((str(rel), decl))
    if decl != path_name:
        affected.append((str(rel), decl, path_name))

live = [a for a in affected if not a[0].startswith("archive/")]
arch = [a for a in affected if a[0].startswith("archive/")]

print(f"scanned files: {scanned}")
print(f"affected (declared != path name): {len(affected)}")
print(f"  live:  {len(live)}")
print(f"  archive: {len(arch)}")
print("affected files:")
for rel, decl, path_name in affected:
    print(f"  {rel}: declares {decl}, path names it {path_name}")
w_live = [w for w in weaker if not w[0].startswith("archive/")]
w_arch = [w for w in weaker if w[0].startswith("archive/")]
print(f"weaker filter (single-component declaration): {len(weaker)}")
print(f"  live: {len(w_live)}  archive: {len(w_arch)}")
print("weaker-filter-only files (blind spot of the main filter):")
main = {a[0] for a in affected}
for rel, decl in weaker:
    if rel not in main:
        print(f"  {rel}: declares {decl}")
