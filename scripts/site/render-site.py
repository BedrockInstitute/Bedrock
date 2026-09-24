#!/usr/bin/env python3
"""Bedrock CLI adapter for the shared Outcrop Site builder.

Explicit --config/--project-root selects another instance without reading Bedrock
configuration. Remaining build options are owned by website.build_site.
"""
import argparse
from pathlib import Path
from outcrop.site.site_config import SiteConfig
from outcrop.site.website import build_site


def main(argv=None):
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', type=Path)
    parser.add_argument('--project-root', type=Path)
    args, options = parser.parse_known_args(argv)
    project_root = args.project_root or (args.config.resolve().parent if args.config else root)
    config = SiteConfig.load(args.config or root / 'site/project.json', root=project_root)
    return build_site(config, options)


if __name__ == '__main__':
    raise SystemExit(main())
