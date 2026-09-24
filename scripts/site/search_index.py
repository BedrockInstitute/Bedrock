"""A shared, trilingual passage index built from the same HTML readers see."""
from html.parser import HTMLParser
import re


class PassageIndex(HTMLParser):
    EXCLUDE = {'script', 'style', 'nav', 'noscript'}
    BLOCKS = {'p', 'li', 'dt', 'dd', 'td', 'th', 'figcaption', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6'}

    def __init__(self, module, title, lang, page):
        super().__init__(convert_charrefs=True)
        self.module, self.title, self.lang, self.page = module, title, lang, page
        self.records, self.blocks, self.excluded = [], [], []
        self.section, self.anchor = title, ''
        self.code, self.lines, self.line, self.line_anchor = False, [], '', ''

    def record(self, name, text, anchor, kind, lang):
        text = re.sub(r'\s+', ' ', text).strip()
        if not text:
            return
        self.records.append({'name': name, 'text': text, 'module': self.module,
                             'lang': lang, 'kind': kind,
                             'href': self.page + ('#' + anchor if anchor else '')})

    def handle_starttag(self, tag, attributes):
        attrs = dict(attributes)
        if tag in self.EXCLUDE:
            self.excluded.append(tag)
        if self.excluded:
            return
        if tag == 'pre':
            self.code, self.lines, self.line, self.line_anchor = True, [], '', ''
        if self.code:
            if attrs.get('id') and not self.line.strip() and not self.line_anchor:
                self.line_anchor = attrs['id']
            return
        if tag in self.BLOCKS:
            anchor = attrs.get('id', self.blocks[-1][1] if self.blocks else self.anchor)
            self.blocks.append([tag, anchor, []])
            if tag.startswith('h') and tag[1:].isdigit():
                self.anchor = anchor

    def handle_data(self, text):
        if self.excluded:
            return
        if self.code:
            parts = text.split('\n')
            for i, part in enumerate(parts):
                self.line += part
                if i < len(parts) - 1:
                    self.lines.append((self.line_anchor, self.line))
                    self.line, self.line_anchor = '', ''
        elif self.blocks:
            self.blocks[-1][2].append(text)

    def handle_endtag(self, tag):
        if self.excluded:
            if tag == self.excluded[-1]:
                self.excluded.pop()
            return
        if tag == 'pre' and self.code:
            self.lines.append((self.line_anchor, self.line))
            # Overlap windows so a query can cross a line or window boundary.
            for start in range(0, len(self.lines), 6):
                window = self.lines[start:start + 8]
                anchor = next((anchor for anchor, _ in window if anchor), self.anchor)
                self.record(self.section, '\n'.join(line for _, line in window), anchor, 'code', '*')
            self.code = False
        elif not self.code and self.blocks and tag == self.blocks[-1][0]:
            tag, anchor, fragments = self.blocks.pop()
            text = ''.join(fragments)
            heading = tag.startswith('h') and tag[1:].isdigit()
            if heading:
                self.section = text
            self.record(text if heading else self.section, text, anchor,
                        'heading' if heading else 'prose', self.lang)


def passages(body, module, title, lang, page):
    parser = PassageIndex(module, title, lang, page)
    parser.feed(body)
    return parser.records
