"""Move compiler-highlighted chapter setup into shared hover payloads."""
import html
import re
from html.parser import HTMLParser
from chapter_structure import IMPORT, OPTIONS, VISIBLE_IMPORT_CHAPTERS

PRE = re.compile(r'<pre class="Agda">(.*?)</pre>', re.S)


def plain(markup):
    return html.unescape(re.sub('<[^>]*>', '', markup))


def chunks(code):
    result = []
    for line in code.splitlines():
        text = plain(line)
        if not text.strip():
            continue
        if not text[0].isspace() or not result:
            result.append(line)
        else:
            result[-1] += '\n' + line
    return result


def popup_code(code, module):
    """Adapt source ranges to the shared popup surface, without parsing Agda.

    Source ranges use file offsets; popup gestures use visible Unicode offsets.
    Preserve compiler expression identities, and derive only their presentation
    offsets from the cloned DOM. No new semantic nodes are invented.
    """
    class Adapter(HTMLParser):
        def __init__(self):
            super().__init__(convert_charrefs=False)
            self.parts, self.stack, self.position = [], [], 0

        def handle_starttag(self, tag, attrs):
            attrs = dict(attrs)
            raw = re.sub(r'\s+id="[^"]*"', '', self.get_starttag_text())
            index = None
            if tag == 'span' and 'expr-node' in attrs.get('class', '').split():
                raw = raw.replace('expr-node', 'type-node')
                raw = re.sub(r' data-expr-(?:start|end)="[^"]*"', '', raw)
                raw = raw[:-1] + (f' data-expression-type="{module}#{attrs["data-expr-id"]}"'
                                  f' data-expr-start="{self.position}">')
                index = len(self.parts)
            self.parts.append(raw)
            if tag == 'span':
                self.stack.append(index)

        def handle_endtag(self, tag):
            if tag == 'span' and self.stack:
                index = self.stack.pop()
                if index is not None:
                    self.parts[index] = self.parts[index][:-1] + f' data-expr-end="{self.position}">'
            self.parts.append(f'</{tag}>')

        def handle_data(self, data):
            self.parts.append(data)
            self.position += len(data)

        def handle_entityref(self, name):
            self.handle_reference('&' + name + ';')

        def handle_charref(self, name):
            self.handle_reference('&#' + name + ';')

        def handle_reference(self, reference):
            self.parts.append(reference)
            self.position += len(html.unescape(reference))
    adapter = Adapter()
    adapter.feed(code)
    return ''.join(adapter.parts)


def mirror_boilerplate(body, module, internal):
    blocks = list(PRE.finditer(body))
    if not blocks or not plain(blocks[0][1]).startswith(OPTIONS):
        return body
    header = chunks(blocks[0][1])
    declarations = [block for block in blocks if any(plain(part).startswith('module ' + module + ' ')
                                                    for part in chunks(block[1]))]
    if not declarations:
        return body
    imports, title_code, removed = {}, [], [blocks[0]]
    for part in header:
        match = IMPORT.match(plain(part))
        if match:
            imports.setdefault(match[1], []).append(part)
        else:
            title_code.append(part)
    for block in blocks[1:]:
        parts = chunks(block[1])
        if parts and all((m := IMPORT.match(plain(part))) and m[1] in internal for part in parts):
            if module not in VISIBLE_IMPORT_CHAPTERS:
                removed.append(block)
            for part in parts:
                imports.setdefault(IMPORT.match(plain(part))[1], []).append(part)
    templates = []
    def template(key, code, imported=''):
        code = popup_code(code, module)
        templates.append(f'<template id="{key}" data-boilerplate-module="{imported}">{code}</template>')
        return key
    key = template('boilerplate-header-' + module, '\n'.join(title_code))
    for imported, parts in imports.items():
        template('boilerplate-import-' + module + '-' + imported, '\n'.join(parts), imported)
    ids = [identifier for block in removed for identifier in re.findall(r'\bid="([^"]+)"', block[0])]
    anchors = ''.join(f'<span id="{identifier}" class="boilerplate-anchor"></span>' for identifier in ids)
    for block in reversed(removed):
        body = body[:block.start()] + body[block.end():]
    body = re.sub(r'(<h1\b[^>]*>)(.*?)(</h1>)',
                  lambda m: m[1] + anchors + '<button type="button" class="boilerplate-hover" '
                  f'data-hover-template="{key}" aria-haspopup="dialog">' + m[2] + '</button>' + m[3],
                  body, count=1, flags=re.S)
    return body + ''.join(templates)
