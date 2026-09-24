#!/usr/bin/env python3
"""Audit every full-text search destination in a rendered trilingual site."""
from collections import Counter
from html import unescape
import json
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit


def main():
    root = Path(sys.argv[1] if len(sys.argv) > 1 else "_build/site")
    entries = json.loads((root / "search-content.json").read_text())
    targets = set()
    for entry in entries:
        for language in ("en", "zh", "ja") if entry["lang"] == "*" else (entry["lang"],):
            link = urlsplit(entry["href"])
            targets.add((language, unquote(link.path), unquote(link.fragment)))
    cache, errors = {}, []
    for language, name, anchor in sorted(targets):
        path = root / language / name
        if path not in cache:
            cache[path] = (set(unescape(x) for x in re.findall(r'\bid="([^"]+)"', path.read_text()))
                           if path.is_file() else None)
        if cache[path] is None or (anchor and anchor not in cache[path]):
            errors.append(f"{language}/{name}#{anchor}")
    print(f"Search: {len(entries)} entries; {len(targets)} destinations; {len(errors)} broken")
    print(dict(Counter(entry["kind"] for entry in entries)))
    for error in errors[:30]:
        print(error)
    return bool(errors)


if __name__ == "__main__":
    sys.exit(main())
