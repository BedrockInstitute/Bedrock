#!/usr/bin/env python3
"""Bedrock's source discovery and Agda-library settings for Outcrop weaving."""
from pathlib import Path
import re
import sys
from outcrop.adapters.weave import main as weave_main
from outcrop.site import SiteConfig

ROOT = Path(__file__).resolve().parents[2]


def woven_library(language):
    source = ROOT / 'bedrock.agda-lib'
    text = source.read_text(encoding='utf-8')
    text = re.sub(r'^name: (.+)$', lambda match: 'name: ' + match[1] + '-woven-' + language,
                  text, flags=re.M)
    text = re.sub(r'^include:.*$', 'include: .', text, flags=re.M)
    return source.name, text


def main(argv=None):
    config = SiteConfig.load(ROOT / 'site/project.json', root=ROOT)
    return weave_main(argv, default_root=config.path(config.sources),
        default_extension=config.source_extension, default_languages=config.languages,
        library_for_language=woven_library, excluded_roots=(ROOT / 'archive',))


if __name__ == '__main__':
    raise SystemExit(main(sys.argv[1:]))
