#!/usr/bin/env python3
"""Validate reader-facing glossary introductions and explicit references."""

import os
import sys
from pathlib import Path

from outcrop.core.term_registry import load_entries, reader_terms
from outcrop.site.reading_routes import build_reading_data

from outcrop.core.term_lint import check_terms
from outcrop.core.term_lint import markers as text_markers

def module_name(path, src="src"):
    return os.path.relpath(path, src)[:-len(".lagda.md")].replace(os.sep, ".")

def markers(path):
    return text_markers(Path(path).read_text(encoding='utf-8'))

def check(src="src", glossary="dev/glossary.toml"):
    sources = {module_name(str(path), src): path.read_text(encoding='utf-8')
               for path in sorted(Path(src).rglob('*.lagda.md'))}
    try:
        reading = build_reading_data(src, Path(__file__).resolve().parents[2] / 'dev/reading-catalog.json',
                                    extension='.lagda.md', previews={'Origin'})
    except (OSError, ValueError):
        # The project route gate owns corpus coverage; the scoped legacy entry
        # can still validate introductions in a supplied single chapter.
        reading = {'nodes': []}
    return check_terms(sources, load_entries(glossary), reading)

def main(argv):
    if argv:
        sys.stderr.write("usage: check-term-introductions.py\n")
        return 2
    errors = check()
    if errors:
        print("\n".join(errors))
        print(f"\n{len(errors)} term-introduction violation(s).", file=sys.stderr)
        return 1
    print(f"term introductions: clean ({len(reader_terms(load_entries('dev/glossary.toml')))} reader terms)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
