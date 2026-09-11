#!/usr/bin/env python3
"""Check that every source definition is transitively consumed by Milestones.

The check deliberately works on Agda's source-module graph rather than on prose
or generated HTML.  A source definition is consumed when its owning module is in
the transitive local-import closure of ``src/Milestones.lagda.md``.  External
Cubical modules are leaves of this graph and are not part of the source set.

This is a push/CI gate.  It is intentionally not part of ``make lint`` or the
pre-commit hook, because an intermediate commit may temporarily leave a module
outside the final milestone closure.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path


AGDA_SUFFIX = ".lagda.md"
IMPORT_RE = re.compile(r"^(?:open\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)")

# These declarations are enough to identify top-level definitions for useful
# diagnostics.  The graph check remains authoritative even for syntax we do not
# classify here.
DECL_RE = re.compile(
    r"^(?:(?:private|instance)\s+)*(?:data|record|postulate|primitive|pattern)\s+([^\s(:=]+)"
)
NAME_RE = re.compile(r"^([^\s:]+)\s*:")


@dataclass(frozen=True)
class Definition:
    module: str
    path: Path
    line: int
    name: str


def module_name(path: Path, src: Path) -> str:
    return path.relative_to(src).as_posix()[: -len(AGDA_SUFFIX)].replace("/", ".")


def code_lines(path: Path):
    """Yield (line number, line) for Agda fences in a literate source file."""
    in_fence = False
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        stripped = line.strip()
        if stripped.startswith("```agda"):
            in_fence = True
            continue
        if in_fence and stripped.startswith("```"):
            in_fence = False
            continue
        if in_fence:
            yield number, line


def source_modules(src: Path) -> dict[str, Path]:
    return {module_name(path, src): path for path in src.rglob(f"*{AGDA_SUFFIX}")}


def graph(src: Path, modules: dict[str, Path]) -> dict[str, set[str]]:
    result = {name: set() for name in modules}
    for name, path in modules.items():
        for _, line in code_lines(path):
            match = IMPORT_RE.match(line.strip())
            if match and match.group(1) in modules:
                result[name].add(match.group(1))
    return result


def reachable(graph_data: dict[str, set[str]], root: str) -> set[str]:
    seen: set[str] = set()
    todo = [root]
    while todo:
        current = todo.pop()
        if current in seen:
            continue
        seen.add(current)
        todo.extend(graph_data.get(current, ()) - seen)
    return seen


def definitions(src: Path, modules: dict[str, Path]) -> list[Definition]:
    found: list[Definition] = []
    for module, path in modules.items():
        for line_number, line in code_lines(path):
            if line[:1].isspace():
                continue
            text = line.strip()
            if not text or text.startswith("--") or text.startswith("module "):
                continue
            match = DECL_RE.match(text) or NAME_RE.match(text)
            if match:
                found.append(Definition(module, path, line_number, match.group(1)))
    return found


def check(src: Path, root: str = "Milestones") -> list[str]:
    modules = source_modules(src)
    problems: list[str] = []
    if root not in modules:
        return [f"missing milestone root: {src / (root.replace('.', '/') + AGDA_SUFFIX)}"]

    graph_data = graph(src, modules)
    consumed = reachable(graph_data, root)
    missing_modules = sorted(set(modules) - consumed - {root})
    if not missing_modules:
        return []

    defs_by_module: dict[str, list[Definition]] = {name: [] for name in missing_modules}
    for definition in definitions(src, modules):
        if definition.module in defs_by_module:
            defs_by_module[definition.module].append(definition)
    for module in missing_modules:
        entries = defs_by_module[module]
        if entries:
            for definition in entries:
                problems.append(
                    f"{definition.path}:{definition.line}: definition "
                    f"{definition.name} is not transitively consumed by {root}"
                )
        else:
            problems.append(f"{modules[module]}: module is not transitively consumed by {root}")
    return problems


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--src", type=Path, default=Path("src"))
    parser.add_argument("--root", default="Milestones")
    args = parser.parse_args(argv)
    problems = check(args.src, args.root)
    if problems:
        for problem in problems:
            print(f"check-milestone-consumption: {problem}", file=sys.stderr)
        print(f"check-milestone-consumption: {len(problems)} violation(s)", file=sys.stderr)
        return 1
    count = len(source_modules(args.src)) - 1
    print(f"check-milestone-consumption: clean ({count} source modules consumed by {args.root})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
