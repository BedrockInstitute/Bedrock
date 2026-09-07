#!/usr/bin/env python3
"""Check catalog coverage and chapter prerequisites in literate Agda sources."""

import argparse
from collections import Counter
from pathlib import Path
import re


FENCE = re.compile(r"^```agda\s*\n(.*?)^```\s*$", re.M | re.S)
IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+([\w.]+)", re.M)
PREVIEWS = frozenset({"Landmarks"})


def imports(text):
    return [name for block in FENCE.findall(text) for name in IMPORT.findall(block)]


def defects(sources):
    if "Everything" not in sources:
        return ["missing Everything catalog"]
    order = imports(sources["Everything"])
    expected = set(sources) - {"Everything"}
    actual = set(order)
    errors = [f"missing chapter: {name}" for name in sorted(expected - actual)]
    errors += [f"unknown catalog chapter: {name}" for name in sorted(actual - expected)]
    errors += [f"duplicate chapter: {name}" for name, n in Counter(order).items() if n > 1]
    position = {name: i for i, name in enumerate(order)}
    for name in order:
        if name in PREVIEWS or name not in expected:
            continue
        for dependency in dict.fromkeys(imports(sources[name])):
            if dependency not in expected:
                continue
            if dependency in PREVIEWS:
                errors.append(f"{name} depends on preview {dependency}, not its proving chapter")
            elif dependency in position and position[dependency] >= position[name]:
                errors.append(f"{name} precedes prerequisite {dependency}")
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--src", type=Path,
                        default=Path(__file__).resolve().parents[2] / "src")
    args = parser.parse_args()
    sources = {str(p.relative_to(args.src))[:-len(".lagda.md")].replace("/", "."):
               p.read_text() for p in sorted(args.src.rglob("*.lagda.md"))}
    errors = defects(sources)
    for error in errors:
        print(f"check-reading-order: {error}")
    if errors:
        return 1
    print(f"check-reading-order: clean ({len(sources) - 1} chapters; Landmarks preview)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
