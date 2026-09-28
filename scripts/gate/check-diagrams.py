#!/usr/bin/env python3
"""Enforce the shared textbook diagram contract in all chapters."""
from pathlib import Path
import sys

from outcrop.core.diagram_style import check_sources

if __name__ == '__main__':
    paths = [Path(p) for p in sys.argv[1:]] or sorted(Path('src').rglob('*.lagda.md'))
    import outcrop.site
    resources = Path(outcrop.site.__file__).resolve().parent / 'resources/static'
    errors = check_sources(paths, stylesheets=sorted(resources.glob('*.css')))
    for error in errors:
        print(error, file=sys.stderr)
    if not errors:
        print(f'Diagram style: {len(paths)} chapters checked')
    raise SystemExit(bool(errors))
