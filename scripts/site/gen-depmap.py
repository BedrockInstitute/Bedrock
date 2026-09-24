#!/usr/bin/env python3
"""Compatibility CLI for the shared dependency-graph publisher."""
import argparse
from pathlib import Path
from dependency_graph import *
from site_config import SiteConfig
from reading_routes import build_reading_data

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--src')
    parser.add_argument('--out', default='_build/site')
    parser.add_argument('--langs')
    parser.add_argument('--config', default=str(Path(__file__).resolve().parents[2] / 'site/project.json'))
    parser.add_argument('--project-root', default=str(Path(__file__).resolve().parents[2]))
    args = parser.parse_args(argv)
    config = SiteConfig.load(args.config, root=args.project_root)
    src = args.src or config.path(config.sources)
    reading = build_reading_data(src, config.path(config.catalog), extension=config.source_extension,
        previews={config.landing_module}, prerequisites=config.values.get('prerequisites'))
    return render_graph(config, reading, masters(src, config.source_extension), args.out,
                        args.langs.split(',') if args.langs else config.languages)

if __name__ == '__main__':
    raise SystemExit(main())
