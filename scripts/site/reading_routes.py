#!/usr/bin/env python3
"""Validate Bedrock's configured reading catalog with Outcrop Site."""
import argparse
import json
from pathlib import Path
from outcrop.site import SiteConfig
from outcrop.site.reading_routes import build_reading_data


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--src')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args(argv)
    root = Path(__file__).resolve().parents[2]
    config = SiteConfig.load(root / 'site/project.json', root=root)
    try:
        data = build_reading_data(args.src or config.path(config.sources), config.path(config.catalog),
            extension=config.source_extension, previews={config.landing_module},
            prerequisites=config.values.get('prerequisites'))
    except ValueError as error:
        print('reading-routes: ERROR: ' + str(error).replace('\n', '; '))
        return 1
    if args.check:
        print(f"reading-routes: clean ({len(data['routes'])} routes; {len(data['nodes'])} chapters)")
    else:
        print(json.dumps(data, ensure_ascii=False, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
