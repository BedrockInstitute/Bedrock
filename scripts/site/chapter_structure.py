"""One source of truth for chapter boilerplate and its source ranges.

Keep source offsets: the renderer uses the compiler's highlighted versions, never
an independently highlighted copy of a declaration or import.
"""
from dataclasses import dataclass
import re

OPTIONS = '{-# OPTIONS --cubical --safe --guardedness #-}'
FENCE = re.compile(r'^```agda\n(?P<code>.*?)^```[ \t]*$', re.M | re.S)
IMPORT = re.compile(r'^(?:open\s+)?import\s+(\S+)')
# A result registry teaches through its public re-exports, not hidden setup.
VISIBLE_IMPORT_CHAPTERS = frozenset({'Origin'})


@dataclass
class Statement:
    text: str
    start: int
    end: int


def statements(text):
    """Top-level declarations; indented continuation lines stay attached."""
    lines = []
    for fence in FENCE.finditer(text):
        offset = fence.start('code')
        for line in fence['code'].splitlines(keepends=True):
            lines.append((line, offset))
            offset += len(line)
    result = []
    for line, offset in lines:
        if not line.strip():
            continue
        if not line[0].isspace() or not result:
            result.append(Statement(line.rstrip(), offset, offset + len(line)))
        else:
            result[-1].text += '\n' + line.rstrip()
            result[-1].end = offset + len(line)
    return result


def chapter_parts(text, module, internal):
    items = statements(text)
    declaration = next(s for s in items if re.match(
        r'module\s+' + re.escape(module) + r'(?:\s|$)', s.text))
    imports = [s for s in items if IMPORT.match(s.text)]
    before = [s for s in imports if s.start < declaration.start]
    # Scope resolution belongs to Agda, not a vocabulary heuristic. Whole-module
    # imports, aliases and re-exports can all supply telescope names. Preserve the
    # explicit pre-module region for parameterized modules; lint checks its
    # placement, while typechecking validates the actual parameter dependencies.
    needed = before if parameterized(declaration, module) else []
    project = [s for s in imports if IMPORT.match(s.text)[1] in internal and s not in needed]
    options = next(s for s in items if s.text == OPTIONS)
    return options, declaration, needed, project


def boilerplate_ranges(text, module, internal):
    options, declaration, needed, project = chapter_parts(text, module, internal)
    setup = [options, *needed, *(project if module not in VISIBLE_IMPORT_CHAPTERS else [])]
    if not parameterized(declaration, module):
        setup.append(declaration)
    return [(item.start, item.end) for item in setup]


def parameterized(declaration, module):
    return declaration.text[len('module ' + module):].strip() != 'where'


def fence(items):
    return '```agda\n' + '\n'.join(s.text for s in items) + '\n```\n\n' if items else ''


def opening_errors(text, module, internal):
    try:
        options, declaration, needed, project = chapter_parts(text, module, internal)
    except (StopIteration, ValueError):
        return ['missing exact OPTIONS pragma or chapter module declaration']
    has_parameters = parameterized(declaration, module)
    expected = fence([options] if has_parameters else [options, declaration])
    if not text.startswith(expected):
        return ['chapter must begin with OPTIONS (and the module declaration only when unparameterized)']
    tail = text[len(expected):]
    title = re.match(r'<!--en-->\n# [^\n]+\n<!--zh-->\n# [^\n]+\n<!--ja-->\n# [^\n]+\n<!--/-->\n', tail)
    if not title:
        return ['chapter header must be followed immediately by a title-only en/zh/ja group']
    tail = tail[title.end():].lstrip('\n')
    if has_parameters:
        if needed:
            expected_imports = fence(needed)
            if not tail.startswith(expected_imports):
                return ['necessary telescope imports must immediately follow the title']
            tail = tail[len(expected_imports):]
        explanation = re.match(r'<!--en-->\n(.+?)\n<!--zh-->\n(.+?)\n<!--ja-->\n(.+?)\n<!--/-->\n\n', tail, re.S)
        if not explanation or any(not part.strip() or re.search(r'^#|```|<!--(?:en|zh|ja|/)-->', part, re.M)
                                  for part in explanation.groups()):
            return ['parameterized module needs complete en/zh/ja parameter exposition before its declaration']
        tail = tail[explanation.end():]
        expected_declaration = fence([declaration])
        if not tail.startswith(expected_declaration):
            return ['parameter exposition must be followed by the complete module declaration alone']
        tail = tail[len(expected_declaration):]
    if module in VISIBLE_IMPORT_CHAPTERS:
        body_items = [s for s in statements(text) if s.start > declaration.end]
        if not body_items or any(not re.fullmatch(
                r'open import (\S+) public using \( [^()]+ \)', s.text)
                or IMPORT.match(s.text)[1] not in internal for s in body_items):
            return ['result registry body must contain only explicit public project re-exports']
        return []
    if project:
        expected_imports = '```agda\n' + '\n'.join(s.text for s in project) + '\n```'
        if not tail.startswith(expected_imports):
            return ['all remaining project imports must form one block after the title or parameter declaration; no Cubical imports']
    return []
