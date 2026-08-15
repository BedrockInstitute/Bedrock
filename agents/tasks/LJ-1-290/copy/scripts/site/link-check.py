#!/usr/bin/env python3
"""Check that relative links in the built site resolve.

Verifies the renderer's link rewriting: every relative href/src (cross-module
`Module.html#pos`, the `../<lang>/Module.html` switcher, index links) points at a file that
exists, and every same-page `#anchor` has a matching id. Absolute (/base-rooted) asset and
brand links and external http(s) links are skipped (they are static and base-dependent).

Usage: link-check.py [SITE_DIR]   (default _build/site); exit 1 on any broken link.
"""

import glob
import os
import re
import sys

HREF_RE = re.compile(r'(?:href|src)="([^"]+)"')
ID_RE = re.compile(r'\bid="([^"]+)"')


def main(argv):
    site = argv[0] if argv else "_build/site"
    pages = glob.glob(os.path.join(site, "**", "*.html"), recursive=True)
    broken = 0
    checked = 0
    for page in pages:
        text = open(page, encoding="utf-8").read()
        ids = set(ID_RE.findall(text))
        page_dir = os.path.dirname(page)
        for target in HREF_RE.findall(text):
            if target.startswith(("http://", "https://", "//", "mailto:", "data:", "/")):
                continue
            checked += 1
            path, _, anchor = target.partition("#")
            if path == "":                       # same-page anchor
                if anchor and anchor not in ids:
                    print(f"{page}: missing anchor #{anchor}")
                    broken += 1
                continue
            dest = os.path.normpath(os.path.join(page_dir, path))
            if not os.path.exists(dest):
                print(f"{page}: dead link -> {target}")
                broken += 1
    print(f"link-check: {checked} relative link(s) across {len(pages)} page(s), "
          f"{broken} broken", file=sys.stderr)
    return 1 if broken else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
