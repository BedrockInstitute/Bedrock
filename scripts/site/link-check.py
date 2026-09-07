#!/usr/bin/env python3
"""Check that relative links in the built site resolve.

Verifies the renderer's link rewriting: every relative href/src (cross-module
`Module.html#pos`, the `../<lang>/Module.html` switcher, index links) points at a file that
exists, and every fragment on an HTML link has a matching id. Absolute (/base-rooted)
asset and brand links and external http(s) links are skipped (they are static and
base-dependent).

Usage: link-check.py [SITE_DIR]   (default _build/site); exit 1 on any broken link.
"""

import glob
from html.parser import HTMLParser
import os
import sys
from urllib.parse import unquote, urlsplit


class PageParser(HTMLParser):
    """Collect decoded link attributes and ids from one HTML page."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.targets = []
        self.ids = set()

    def handle_starttag(self, _tag, attrs):
        for name, value in attrs:
            if value is None:
                continue
            if name == "id":
                self.ids.add(value)
            elif name in ("href", "src"):
                self.targets.append(value)

    handle_startendtag = handle_starttag


def parse_page(path, cache):
    """Return a page's targets and ids, reading each HTML file at most once."""
    path = os.path.normpath(path)
    if path not in cache:
        parser = PageParser()
        with open(path, encoding="utf-8") as source:
            parser.feed(source.read())
        parser.close()
        cache[path] = parser.targets, parser.ids
    return cache[path]


def skipped(target):
    return target.startswith(("http://", "https://", "//", "mailto:", "data:", "/"))


def check_site(site):
    pages = glob.glob(os.path.join(site, "**", "*.html"), recursive=True)
    cache = {}
    broken = 0
    checked = 0
    for page in pages:
        targets, ids = parse_page(page, cache)
        page_dir = os.path.dirname(page)
        for target in targets:
            if skipped(target):
                continue
            checked += 1
            try:
                parts = urlsplit(target)
            except ValueError:
                parts = None
            if parts is None:
                path, _, anchor = target.partition("#")
            else:
                path, anchor = parts.path, parts.fragment
            path = unquote(path)
            anchor = unquote(anchor)
            if path == "":
                if anchor and anchor not in ids:
                    print(f"{page}: missing anchor #{anchor}")
                    broken += 1
                continue
            dest = os.path.normpath(os.path.join(page_dir, path))
            if not os.path.exists(dest):
                print(f"{page}: dead link -> {target}")
                broken += 1
                continue
            if anchor and dest.endswith(".html"):
                _, dest_ids = parse_page(dest, cache)
                if anchor not in dest_ids:
                    print(f"{page}: missing anchor #{anchor} -> {target}")
                    broken += 1
    print(f"link-check: {checked} relative link(s) across {len(pages)} page(s), "
          f"{broken} broken", file=sys.stderr)
    return 1 if broken else 0


def main(argv):
    site = argv[0] if argv else "_build/site"
    return check_site(site)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
