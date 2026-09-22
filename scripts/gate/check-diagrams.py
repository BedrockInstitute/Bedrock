#!/usr/bin/env python3
"""Enforce the shared textbook diagram contract in all chapters."""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'site'))
from diagram_style import check_sources

if __name__ == '__main__':
    paths = [Path(p) for p in sys.argv[1:]] or sorted(Path('src').rglob('*.lagda.md'))
    errors = check_sources(paths)
    for error in errors:
        print(error, file=sys.stderr)
    if not errors:
        print(f'Diagram style: {len(paths)} chapters checked')
    raise SystemExit(bool(errors))
