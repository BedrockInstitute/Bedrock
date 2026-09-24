#!/usr/bin/env python3
"""Check the external reading catalog against literate Agda sources."""

import argparse
import json
from pathlib import Path


from outcrop.site import SiteConfig

PREVIEWS = frozenset({"Origin"})
ROOT = Path(__file__).resolve().parents[2]
CONFIG = SiteConfig.load(ROOT / 'site/project.json', root=ROOT)
CATALOG = CONFIG.path(CONFIG.catalog)



from outcrop.core.reading_order import reading_order_errors
from outcrop.site.site_inputs import source_paths


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
    sources = {module: path.read_text(encoding='utf-8')
               for module, path in source_paths(args.src, '.lagda.md').items()}
    errors = defects(sources)
    for error in errors:
        print(f"check-reading-order: {error}")
    if errors:
        return 1
    print(f"check-reading-order: clean ({len(sources)} chapters; Origin preview)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
