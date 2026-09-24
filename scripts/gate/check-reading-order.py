#!/usr/bin/env python3
"""Check the external reading catalog against literate Agda sources."""

import argparse
from collections import Counter
import json
from pathlib import Path
import re


FENCE = re.compile(r"^```agda\s*\n(.*?)^```\s*$", re.M | re.S)
IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+([\w.]+)", re.M)
PREVIEWS = frozenset({"Origin"})
CATALOG = Path(__file__).resolve().parents[2] / "dev" / "reading-catalog.json"


import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'site'))
from source_syntax import imports
from reading_order import reading_order_errors


def defects(sources, catalog_path=CATALOG):
    try:
        catalog = json.loads(Path(catalog_path).read_text(encoding='utf-8'))
        return reading_order_errors(sources, catalog, previews=PREVIEWS)
    except (OSError, KeyError, TypeError, json.JSONDecodeError):
        return ['missing or invalid reading catalog']


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
    print(f"check-reading-order: clean ({len(sources)} chapters; Origin preview)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
