#!/usr/bin/env python3
"""Build same-origin alternate instances and the raw core page for CUA tests."""
import argparse
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts/site'))
from document_renderer import MarkdownDocument
from site_config import SiteConfig
from website import build_site


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    example = ROOT / 'examples/renderer'
    config = SiteConfig.load(example / 'project.json', root=example)
    build_site(config, ['--out', str(args.out / 'academy')])
    prism = config.with_overrides(name='Prism Reader', publisher='Prism Workshop',
        storage_namespace='prism-reader', canonical='https://prism.example/prism', base_url='/prism')
    build_site(prism, ['--out', str(args.out / 'prism')])
    body = MarkdownDocument((example / 'plain.md').read_text()).render('en').body
    (args.out / 'plain.html').write_text('<!doctype html><meta charset="utf-8">'
        '<title>Project-free Markdown core</title><article>' + body + '</article>', encoding='utf-8')
    shutil.copyfile(ROOT / 'scripts/tests/browser-renderer.html', args.out / 'renderer-regression.html')


if __name__ == '__main__':
    main()
