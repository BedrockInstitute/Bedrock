"""Read Agda module scopes from the code stream of one literate chapter.

Module aliases have no body and are excluded. The chapter's first declaration is
its root module; every later `module … where` is a submodule. Agda's layout
indentation determines the end of each body, even when code fences interrupt it.
"""

from dataclasses import dataclass
import re


FENCE_RE = re.compile(r'(?ms)^```agda\n(?P<code>.*?)^```[ \t]*$')
MODULE_START_RE = re.compile(r'^[ \t]*(?:private[ \t]+)?module\s+')
WHERE_RE = re.compile(r'\bwhere\s*$')


def module_header_line(code):
    """Locate a declaration; private must share the module's first line."""
    lines = list(re.finditer(r'(?m)^[ \t]*\S[^\n]*$', code))
    if not lines:
        return None
    first = lines[0]
    return first if MODULE_START_RE.match(first[0]) else None


@dataclass
class CodeLine:
    start: int
    end: int
    text: str
    fence_start: int
    fence_end: int


@dataclass
class Submodule:
    start: int
    header_end: int
    body_end: int
    depth: int
    indent: int
    header_lines: int
    line: int


def code_lines(source):
    lines = []
    for fence in FENCE_RE.finditer(source):
        offset = fence.start('code')
        for line in fence.group('code').splitlines(keepends=True):
            bare = line.rstrip('\r\n')
            lines.append(CodeLine(offset, offset + len(bare), bare,
                                  fence.start(), fence.end()))
            offset += len(line)
    return lines


def submodules(source):
    lines = code_lines(source)
    starts = {}
    continuations = set()
    for index, item in enumerate(lines):
        if not MODULE_START_RE.match(item.text):
            continue
        # A module alias (`module M = N`) contributes no local body.
        if '=' in item.text and not WHERE_RE.search(item.text):
            continue
        end = index
        while end < len(lines) and not WHERE_RE.search(lines[end].text):
            end += 1
            if end >= len(lines) or MODULE_START_RE.match(lines[end].text):
                raise ValueError(f"unfinished module declaration at line "
                                 f"{source.count(chr(10), 0, item.start) + 1}")
            if re.match(r'^\s*=', lines[end].text):
                end = -1  # multiline module alias
                break
        if end < 0:
            continue
        starts[index] = end
        continuations.update(range(index + 1, end + 1))

    if not starts:
        return []
    root = min(starts)
    records = {}
    stack = []
    for index, item in enumerate(lines):
        if index in continuations or not item.text.strip():
            continue
        indent = len(item.text) - len(item.text.lstrip(' '))
        while stack and indent <= records[stack[-1]].indent:
            stack.pop()
        if index in starts and index != root:
            record = Submodule(
                item.start, lines[starts[index]].end,
                lines[starts[index]].end, len(stack) + 1, indent,
                starts[index] - index + 1,
                source.count('\n', 0, item.start) + 1,
            )
            records[index] = record
            stack.append(index)
        for active in stack:
            if index >= starts[active]:
                records[active].body_end = item.end
    return list(records.values())
