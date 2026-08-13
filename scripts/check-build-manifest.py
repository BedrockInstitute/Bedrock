#!/usr/bin/env python3
"""Check that every file in `_build/` declares a lifecycle, and regenerate `_build/README.md`.

THE OWNER'S RULING, 2026-08-13: `_build` must not be a temporary folder and a
rubbish bin at the same time. Every temporary file declares its lifecycle when it
is created. `dev/build-manifest.toml` is that declaration; this script is its
enforcement point.

WHAT THIS CHECKER CAN DO. It compares the files on disk against the globs in the
manifest and names the ones that match nothing.

WHAT IT CANNOT DO, AND THE LIMIT IS THE POINT. It cannot tell evidence from
exhaust. Both are text files; the difference is whether re-running a command
reproduces them, and only the agent who ran the command knows that. It therefore
never deletes, never moves, and NEVER FAILS A GATE. `AGENTS.md` warns that a rule
claiming more than its checker delivers turns into false safety. This checker
claims one thing: that an undeclared file gets NAMED. That is all it delivers.

    check-build-manifest.py            list undeclared files; exit 0 always
    check-build-manifest.py --check    same, but exit 1 if any file is undeclared
    check-build-manifest.py --readme   regenerate _build/README.md from the manifest
"""

import argparse
import fnmatch
import pathlib
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "dev" / "build-manifest.toml"
BUILD = ROOT / "_build"
README = BUILD / "README.md"

# Never reported: the README this script writes, and macOS clutter that
# `.gitignore:12` already handles everywhere in the tree.
IGNORED = ("README.md", ".DS_Store")


def load() -> dict:
    if not MANIFEST.is_file():
        sys.exit(f"missing manifest: {MANIFEST.relative_to(ROOT)}")
    return tomllib.loads(MANIFEST.read_text(encoding="utf-8"))


def matches(rel: str, glob: str) -> bool:
    """Match `rel` against `glob`, where a trailing `/**` also matches the directory itself."""
    if fnmatch.fnmatch(rel, glob):
        return True
    if glob.endswith("/**"):
        return fnmatch.fnmatch(rel, glob[:-3]) or rel.startswith(glob[:-2])
    return False


def scan(data: dict) -> tuple[list[str], dict[str, int]]:
    """Return the undeclared paths, and a count of declared files per class."""
    entries = data.get("entries", [])
    undeclared: list[str] = []
    counts: dict[str, int] = {}
    if not BUILD.is_dir():
        return undeclared, counts
    for path in sorted(BUILD.rglob("*")):
        if not path.is_file():
            continue
        rel = str(path.relative_to(BUILD))
        if rel in IGNORED or path.name in IGNORED:
            continue
        hit = next((e for e in entries if matches(rel, e["glob"])), None)
        if hit is None:
            undeclared.append(rel)
        else:
            counts[hit["class"]] = counts.get(hit["class"], 0) + 1
    return undeclared, counts


def render_readme(data: dict) -> str:
    """Build `_build/README.md` from the manifest. Derived, never transcribed."""
    out = [
        "# `_build/`: the lifecycle regime",
        "",
        "**GENERATED. Do not edit.** The source is `dev/build-manifest.toml`.",
        "Regenerate with `.venv/bin/python scripts/check-build-manifest.py --readme`.",
        "",
        "This file is not tracked, because `.gitignore:2` ignores `_build/` and",
        "`scripts/check-probes.py --check` fails on any tracked file here. If",
        "`make clean` removes it, one command brings it back.",
        "",
        "## The rule",
        "",
        "**The owner's ruling, 2026-08-13.** `_build` must not be a temporary folder",
        "and a rubbish bin at the same time. **Every temporary file declares its",
        "lifecycle when it is created**: under what condition it may be deleted, and",
        "under what condition it moves somewhere permanent.",
        "",
        "**Before you write a file here, add its entry to `dev/build-manifest.toml`.**",
        "One glob, one class. If no class fits, say so in your report and stop; do not",
        "leave the file undeclared.",
        "",
        "## The classes",
        "",
    ]
    for name, c in data.get("classes", {}).items():
        out.append(f"### `{name}`")
        out.append("")
        out.append(c["what"].strip())
        out.append("")
        out.append(f"- **Delete when:** {c['delete_when'].strip()}")
        out.append(f"- **Moves out when:** {c['promote_when'].strip()}")
        out.append("")
    out += [
        "## The entries",
        "",
        "| Path glob | Class | Why |",
        "|---|---|---|",
    ]
    for e in data.get("entries", []):
        note = " ".join(e.get("note", "").split())
        out.append(f"| `{e['glob']}` | `{e['class']}` | {note} |")
    out += [
        "",
        "## Where the permanent homes are",
        "",
        "| Kind | Home |",
        "|---|---|",
        "| Measurement a LIVE document cites | `dev/measurements/` |",
        "| Measurement only historical documents cite | `archive/measurements/` |",
        "| Probe | `agents/tasks/<TASK>/`, beside its report |",
        "| Code or prose written, measured, not landed | `archive/kits/` |",
        "| Retired script | `archive/tooling/` |",
        "| Agent report or brief | `agents/tasks/`, `agents/tasks/` |",
        "",
        "## What the checker does and does not do",
        "",
        "`scripts/check-build-manifest.py` names any file here that matches no entry.",
        "**It is advisory. It never deletes, never moves, and never fails a gate.**",
        "It cannot tell evidence from exhaust: both are text files, and the difference",
        "is whether re-running a command reproduces them. Only the agent who ran the",
        "command knows that. So the declaration is the agent's job; the checker only",
        "notices when nobody made one.",
        "",
    ]
    return "\n".join(out)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true", help="exit 1 if a file is undeclared")
    ap.add_argument("--readme", action="store_true", help="regenerate _build/README.md")
    args = ap.parse_args()

    data = load()

    if args.readme:
        BUILD.mkdir(parents=True, exist_ok=True)
        README.write_text(render_readme(data), encoding="utf-8")
        print(f"wrote {README.relative_to(ROOT)}")

    undeclared, counts = scan(data)
    for name in sorted(counts):
        print(f"  {counts[name]:>6} declared  {name}")
    if undeclared:
        print(f"\nUNDECLARED, {len(undeclared)} file(s). Add an entry to "
              f"dev/build-manifest.toml, or move the file to a permanent home:")
        for rel in undeclared:
            print(f"  _build/{rel}")
        print("\nAdvisory only. This is not a gate.")
        return 1 if args.check else 0
    print("\nevery file in _build/ declares a lifecycle.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
