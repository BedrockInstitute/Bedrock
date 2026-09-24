#!/usr/bin/env python3
"""Check the trilingual chapter outline without requiring full prose translation."""
import argparse
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'site'))
from i18n_markers import LANGS, parse
from chapter_structure import opening_errors

from outline_lint import outline_errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files', nargs='*', type=Path)
    args = parser.parse_args()
    files = args.files or sorted(Path('src').rglob('*.lagda.md'))
    failures, count = 0, 0
    source_root = Path('src').resolve()
    internal = {str(p.resolve().relative_to(source_root))[:-9].replace('/', '.')
                for p in Path('src').rglob('*.lagda.md')}
    for path in files:
        errors, headings = outline_errors(path.read_text())
        module = str(path.resolve().relative_to(source_root))[:-9].replace('/', '.')
        errors.extend(opening_errors(path.read_text(), module, internal,
                                     visible_import_chapters={'Origin'}))
        count += headings
        if headings == 0:
            errors.append('missing chapter title')
        for error in errors:
            print(f'{path}: {error}')
        failures += len(errors)
    print(f'chapter-framework: {len(files)} chapters, {count} titles, {failures} errors')
    return bool(failures)


if __name__ == '__main__':
    sys.exit(main())
