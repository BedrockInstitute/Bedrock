#!/usr/bin/env python3
"""Emit an apply_patch migration; never write files directly.

Promote leading module declarations from a private layout block to individually
private modules, retaining a private block for every non-module sibling. Process
the actual code stream across literate fences. Verify all non-private tokens are
preserved. Multiline alias arguments remain indented past the private layout
column; module-body headers are flattened to activate Agda's passive layout rule.
"""
import difflib
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
from outcrop.core.submodule_structure import code_lines, FENCE_RE


def indent(text):
    return len(text) - len(text.lstrip(' '))


def migrate(source):
    original = source
    while True:
        lines = code_lines(source)
        found = None
        for index, line in enumerate(lines):
            if line.text.strip() != 'private':
                continue
            next_line = next((i for i in range(index + 1, len(lines)) if lines[i].text.strip()), None)
            if next_line is not None and lines[next_line].text.lstrip().startswith('module '):
                found = index, next_line
                break
        if found is None:
            break
        first, cursor = found
        base, member = indent(lines[first].text), indent(lines[cursor].text)
        assert member > base, 'invalid private layout'
        end = next((i for i in range(cursor + 1, len(lines))
                    if lines[i].text.strip() and indent(lines[i].text) <= base), len(lines))
        edits = [(lines[first].start, lines[first].end + 1, '')]
        while cursor < end:
            if not lines[cursor].text.strip():
                cursor += 1
                continue
            if not lines[cursor].text.lstrip().startswith('module '):
                edits.append((lines[cursor].start, lines[cursor].start, ' ' * base + 'private\n'))
                break
            statement_end = next((i for i in range(cursor + 1, end)
                                  if lines[i].text.strip() and indent(lines[i].text) <= member), end)
            where = next((i for i in range(cursor, statement_end)
                          if re.search(r'\bwhere\s*$', lines[i].text)), None)
            # A leading alias '=' wins over any local where in its arguments.
            alias = '=' in lines[cursor].text and not re.search(r'\bwhere\s*$', lines[cursor].text)
            if where is not None and not alias:
                header = ' '.join(lines[i].text.strip() for i in range(cursor, where + 1))
                edits.append((lines[cursor].start, lines[cursor].end, ' ' * base + 'private ' + header))
                for i in range(cursor + 1, where + 1):
                    edits.append((lines[i].start, lines[i].end + 1, ''))
                for i in range(where + 1, statement_end):
                    if lines[i].text.strip():
                        edits.append((lines[i].start, lines[i].end, lines[i].text[member - base:]))
            else:
                edits.append((lines[cursor].start, lines[cursor].end,
                              ' ' * base + 'private ' + lines[cursor].text.lstrip()))
                for i in range(cursor + 1, statement_end):
                    if lines[i].text.strip():
                        shift = base + len('private ') - member
                        text = ' ' * shift + lines[i].text if shift >= 0 else lines[i].text[-shift:]
                        edits.append((lines[i].start, lines[i].end, text))
            cursor = statement_end
        for start, end, replacement in sorted(edits, reverse=True):
            source = source[:start] + replacement + source[end:]
        def clean_fence(match):
            code = match.group('code').rstrip()
            return '```agda\n' + code + '\n```' if code else ''
        source = FENCE_RE.sub(clean_fence, source)
    def tokens(text):
        code = '\n'.join(line.text for line in code_lines(text))
        return re.sub(r'\s+', '', re.sub(r'(?<!\S)private(?!\S)', '', code))
    assert tokens(source) == tokens(original), 'migration changed a non-private token'
    return source


if __name__ == '__main__':
    print('*** Begin Patch')
    for path in sorted((ROOT / 'src').rglob('*.lagda.md')):
        before = path.read_text()
        after = migrate(before)
        if before != after:
            print('*** Update File: ' + str(path))
            diff = list(difflib.unified_diff(before.splitlines(), after.splitlines(), n=3))
            for line in diff[2:]:
                print('@@' if line.startswith('@@') else line)
    print('*** End Patch')
