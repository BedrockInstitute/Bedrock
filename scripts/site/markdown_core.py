"""Reusable Markdown/HTML transformations. All inputs are explicit text/data.

This module reads no repository paths, catalogs, compiler output or branding.
The supported input dialect is documented in dev/RENDERER-MARKDOWN.md.
"""
import html as htmllib
from html.parser import HTMLParser
import re
from html_contract import *
from statement_structure import LABEL_RE, PROOF_LABELS
from submodule_structure import module_header_line
from term_registry import TERM_MARK_RE, localized_forms, localized_abbreviation

def dedent_submodule_code(body):
    """Hide module-scope indentation in HTML without changing Agda source offsets.

    Agda's highlighter leaves leading spaces as text before each token anchor. Only
    that whitespace is removed; links, token ids, hover ranges and the Markdown
    mirror continue to refer to the original source.
    """
    details = []
    heading = None
    parts = []
    previous = 0
    for match in SUBMODULE_HTML_TOKEN_RE.finditer(body):
        token = match.group(0)
        replacement = token
        if token.startswith('<details'):
            details.append({'fold': bool(re.search(
                r'\bclass="[^"]*\bsubmodule-fold\b', token)), 'indent': None})
        elif token.startswith('</details'):
            if details:
                details.pop()
        elif token.startswith('<summary'):
            heading = details[-1] if (details and details[-1]['fold'] and
                re.search(r'\bclass="[^"]*\bsubmodule-fold-heading\b', token)) else None
        elif token.startswith('</summary'):
            heading = None
        elif token.startswith('<pre'):
            if heading is not None:
                code = plain_code(token)
                module_line = module_header_line(code)
                declaration = module_line[0] if module_line else ''
                heading['indent'] = len(declaration) - len(declaration.lstrip(' '))
                # Keep private's relative indentation in the declaration itself.
                strip = min((len(line) - len(line.lstrip(' '))
                             for line in code.splitlines() if line.strip()), default=0)
            else:
                enclosing = next((item for item in reversed(details)
                                  if item['fold'] and item['indent'] is not None), None)
                strip = enclosing['indent'] + 2 if enclosing else 0
            if strip:
                opening = '<pre class="Agda">'
                lines = token[len(opening):-len('</pre>')].splitlines(keepends=True)
                replacement = opening + ''.join(
                    line[min(strip, len(line) - len(line.lstrip(' '))):]
                    for line in lines
                ) + '</pre>'
        parts.extend((body[previous:match.start()], replacement))
        previous = match.end()
    parts.append(body[previous:])
    return ''.join(parts)


def _slug(n):
    return f"sec-{n}"


def _inline(s):
    # Code spans are stashed as protected placeholders first, so emphasis may span
    # them (`**bold with `code` inside**`); the emphasis regexes then run over the
    # whole string, in which placeholders are inert (no `*`, nothing escapable).
    stash = {}

    # Store an annotation's rendered body on its inline target. This keeps the
    # generated HTML valid even inside emphasis and list items; JavaScript moves
    # the body into the article's margin-note layer after parsing.
    def _annotation(m):
        key = f"{NUL}A{len(stash)}{NUL}"
        note_source = m.group("note")
        note_links = []

        def _note_link(link_match):
            link_key = f"{NUL}H{len(note_links)}{NUL}"
            note_links.append(link_match.group(0))
            return link_key

        note_source = re.sub(r'<a\b[^>]*>.*?</a>', _note_link, note_source,
                             flags=re.DOTALL)
        note_html = _inline(note_source)
        for index, link in enumerate(note_links):
            note_html = note_html.replace(f"{NUL}H{index}{NUL}", link)
        stash[key] = (
            '<span class="prose-annotation-target">' + m.group("target") + '</span>'
            '<template class="prose-annotation-template">' + note_html + '</template>'
        )
        return key

    s = re.sub(r'<span class="prose-annotation-target">(?P<target>.*?)</span>'
               r'<aside class="prose-annotation-note">(?P<note>.*?)</aside>',
               _annotation, s, flags=re.DOTALL)

    def _code(m):
        key = f"{NUL}C{len(stash)}{NUL}"
        stash[key] = f"<code>{htmllib.escape(m.group(1))}</code>"
        return key

    s = re.sub(r'`([^`]+)`', _code, s)
    out = []
    for seg in re.split(r'(' + NUL + r'[A-Z]+\d+' + NUL + r')', s):
        if _PLACEHOLDER.fullmatch(seg):    # protected span: leave verbatim
            out.append(seg)
        else:
            out.append(htmllib.escape(seg, quote=False))
    p = "".join(out)
    p = re.sub(r'\[([^\]]+)\]\(([^)]+)\)', r'<a href="\2">\1</a>', p)
    p = re.sub(r'\*\*([^*]+)\*\*', r'<strong>\1</strong>', p)
    p = re.sub(r'(?<!\*)\*([^*\s][^*]*?)\*(?!\*)', r'<em>\1</em>', p)
    for key, val in stash.items():
        p = p.replace(key, val)
    return p


def render_summary_inline(text):
    """Render Markdown inline syntax in summaries that contain Agda references."""
    ref_placeholder = re.compile(NUL + r"REF\d+" + NUL)

    def render(match):
        attrs, inner = match.groups()
        if not ref_placeholder.search(inner):
            return match.group(0)
        inline = " ".join(part.strip() for part in inner.splitlines() if part.strip())
        return f"<summary{attrs}>{_inline(inline)}</summary>"

    return SUMMARY_RE.sub(render, text)


def _is_block_start(line):
    s = line.lstrip()
    return (not s or s.startswith("#") or s.startswith(">") or s.startswith("|")
            or re.match(r'^([-*+]|\d+\.)\s', s) or re.match(r'^(```|~~~)', s)
            or re.match(r'^([-*_])(\s*\1){2,}\s*$', s.strip())
            or s.startswith("<") or _BLOCK_PLACEHOLDER.fullmatch(s.strip()))


def _is_table_sep(line):
    s = line.strip()
    return bool(s) and set(s) <= set("|:- ") and "-" in s


def md_to_html(text):
    """Return (html, toc) where toc is a list of (level, id, text) for h2..h6."""
    lines = text.split("\n")
    out, toc = [], []
    i, n = 0, len(lines)
    hcount = 0
    while i < n:
        line = lines[i]
        if not line.strip():
            i += 1
            continue
        m = re.match(r'^(#{1,6})\s+(.*)$', line)
        if m:
            level = len(m.group(1))
            text_in = m.group(2).strip()
            hid = _slug(hcount); hcount += 1
            if level >= 2:
                toc.append((level, hid, re.sub(r'`([^`]+)`', r'\1', text_in)))
            out.append(f'<h{level} id="{hid}">{_inline(text_in)}</h{level}>')
            i += 1
            continue
        if re.match(r'^([-*_])(\s*\1){2,}\s*$', line.strip()):
            out.append("<hr/>"); i += 1; continue
        mf = re.match(r'^\s*(```|~~~)(.*)$', line)
        if mf:
            fence = mf.group(1); body = []
            i += 1
            while i < n and not lines[i].lstrip().startswith(fence):
                body.append(lines[i]); i += 1
            i += 1
            out.append('<pre class="sourceCode"><code>'
                       + htmllib.escape("\n".join(body)) + "</code></pre>")
            continue
        if _BLOCK_PLACEHOLDER.fullmatch(line.strip()):
            out.append(line.strip()); i += 1; continue
        if line.lstrip().startswith("<"):
            block = []
            while (i < n and lines[i].strip()
                   and not re.match(r'^\s*#{1,6}\s+', lines[i])):
                block.append(lines[i]); i += 1
            out.append("\n".join(block)); continue
        if re.match(r'^\s*([-*+]|\d+\.)\s+', line):
            ordered = bool(re.match(r'^\s*\d+\.\s+', line))
            items = []
            while i < n and re.match(r'^\s*([-*+]|\d+\.)\s+', lines[i]):
                item = re.sub(r'^\s*([-*+]|\d+\.)\s+', '', lines[i]); i += 1
                cont = []
                while i < n and lines[i].strip() and not re.match(r'^\s*([-*+]|\d+\.)\s+', lines[i]) \
                        and not _is_block_start(lines[i]):
                    cont.append(lines[i].strip()); i += 1
                items.append("<li>" + _inline(" ".join([item] + cont)) + "</li>")
            tag = "ol" if ordered else "ul"
            out.append(f"<{tag}>" + "".join(items) + f"</{tag}>")
            continue
        if line.lstrip().startswith(">"):
            block = []
            while i < n and lines[i].lstrip().startswith(">"):
                block.append(re.sub(r'^\s*>\s?', '', lines[i])); i += 1
            inner, _ = md_to_html("\n".join(block))
            out.append("<blockquote>" + inner + "</blockquote>")
            continue
        if line.lstrip().startswith("|") and i + 1 < n and _is_table_sep(lines[i + 1]):
            def _cells(s):
                return [c.strip() for c in s.strip().strip("|").split("|")]
            header = _cells(line)
            i += 2
            body = []
            while i < n and lines[i].lstrip().startswith("|") and not _is_table_sep(lines[i]):
                body.append(_cells(lines[i])); i += 1
            rows = ["<thead><tr>" + "".join(f"<th>{_inline(c)}</th>" for c in header)
                    + "</tr></thead><tbody>"]
            for r in body:
                rows.append("<tr>" + "".join(f"<td>{_inline(c)}</td>" for c in r) + "</tr>")
            out.append('<div class="prose-table-scroll"><table>' + "".join(rows)
                       + "</tbody></table></div>")
            continue
        para = [line]; i += 1
        while i < n and lines[i].strip() and not _is_block_start(lines[i]):
            para.append(lines[i]); i += 1
        label = LABEL_RE.match(line)
        role = ('proof' if label[1] in PROOF_LABELS else 'statement') if label else None
        attrs = f' class="prose-{role}"' if role else ''
        out.append("<p" + attrs + ">" + _inline(" ".join(s.strip() for s in para)) + "</p>")
    return "\n".join(out), toc


def render_statement_endings(body, lang):
    """Keep the QED outside the final pre, never across a fold boundary.

    Code anchors, hover descendants and horizontal scrolling remain untouched.
    The layout wrapper reserves a separate column for the mark on narrow screens.
    """
    label = {'en': 'End of statement', 'zh': '陈述结束', 'ja': '記述の終わり'}[lang]
    def ending(match):
        identifier = re.search(r'\bid="[^"]*"', match[2] or '')
        anchor = (' ' + identifier[0]) if identifier else ''
        return ('<div class="statement-ending">' + match[1]
                + '<span class="statement-qed"' + anchor
                + ' role="img" aria-label="' + label + '">∎</span></div>')
    return re.sub(
        r'(<pre class="Agda">(?:(?!<pre\b).)*?</pre>)\s*<p(\s+[^>]*)?>\s*∎\s*</p>',
        ending,
        body, flags=re.DOTALL)


def render_code_scroll_content(body):
    """Scroll code inside a padded frame, preserving tokens and anchors.

    Fold declarations retain their original compact summary presentation.
    """
    opening = '<pre class="Agda">'
    wrapper = '<span class="agda-code-content">'

    in_declaration = False

    def wrap(match):
        nonlocal in_declaration
        block = match.group(0)
        if block.startswith('<summary'):
            in_declaration = bool(re.search(r'\bclass="[^"]*\bsubmodule-fold-heading\b', block))
            return block
        if block.startswith('</summary'):
            in_declaration = False
            return block
        inner = block[len(opening):-len('</pre>')]
        if in_declaration:
            if inner.startswith(wrapper) and inner.endswith('</span>'):
                return opening + inner[len(wrapper):-len('</span>')] + '</pre>'
            return block
        if inner.startswith(wrapper):
            return block
        return opening + wrapper + inner + '</span></pre>'

    return re.sub(r'<summary\b[^>]*>|</summary\s*>|' + PRE_RE.pattern,
                  wrap, body, flags=re.DOTALL)


def restore_toc_labels(toc, store):
    """Replace protected inline markup in TOC labels with its visible plain text."""
    clean = []
    for level, anchor, title in toc:
        for key, value in store.items():
            title = title.replace(key, re.sub(r"<[^>]+>", "", value))
        clean.append((level, anchor, htmllib.unescape(title)))
    return clean


def anchor_prose_blocks(body):
    """Give every top-level prose block a stable id (`p-1`, `p-2`, ...).

    Numbering follows document order and counts paragraphs, list items, block quotes
    and tables alike, so one anchor names one block of prose whatever markup carries
    it. A block nested inside another (a paragraph inside a block quote, a paragraph
    inside a list item) is not numbered separately: the outermost block is the
    addressable unit. `pre` is absent because the renderer escapes everything inside a
    code block, so no prose tag can occur there; a displayed Agda block is addressed
    instead by the token anchors Agda's own highlighter emits.
    """
    out = []
    index = 0
    depth = 0
    pos = 0
    for match in BLOCK_RE.finditer(body):
        if match.group(1):
            depth = max(0, depth - 1)
            continue
        if depth == 0:
            index += 1
            attributes = body[match.end():body.find('>', match.end())]
            if not re.search(r'(?:^|\s)id\s*=', attributes):
                out.append(body[pos:match.end()])
                out.append(f' id="p-{index}"')
                pos = match.end()
        depth += 1
    out.append(body[pos:])
    return "".join(out)


def markdown_body(woven, code_blocks):
    """Ready-to-use Markdown body, independent of site metadata/publication."""
    text = TERM_MARK_RE.sub(lambda m: m.group(1), woven)
    text = INLINE_AGDA_LINK_RE.sub(
        lambda m: f"[{m.group(1)}]({m.group(2)}.html#{m.group(3)})", text)
    text = INLINE_AGDA_RE.sub(lambda m: "`" + m.group(1) + "`", text)
    for index, block in enumerate(code_blocks):
        text = text.replace(f"{NUL}CODE{index}{NUL}",
                            "\n\n```agda\n" + plain_code(block) + "\n```\n\n")
    return re.sub(r"\n{3,}", "\n\n", text)


def plain_code(block):
    """Recover the Agda source from one highlighted `<pre class="Agda">` block."""
    inner = re.sub(r'^<pre class="Agda">', "", block.strip())
    inner = re.sub(r"</pre>$", "", inner)
    return htmllib.unescape(re.sub(r"<[^>]+>", "", inner)).strip("\n")


class _TermLinker(HTMLParser):
    """Add term links to text nodes without entering code, math, or existing links."""

    EXCLUDED_TAGS = {"a", "code", "dfn", "pre", "script", "style", "textarea"}
    VOID_TAGS = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link",
                 "meta", "param", "source", "track", "wbr"}

    def __init__(self, annotate):
        super().__init__(convert_charrefs=False)
        self.annotate = annotate
        self.parts = []
        self.excluded = []

    def handle_starttag(self, tag, attrs):
        raw = self.get_starttag_text()
        classes = next((value for name, value in attrs if name == "class"), "") or ""
        blocked = tag in self.EXCLUDED_TAGS or "math" in classes.split() or "Agda" in classes.split()
        if tag not in self.VOID_TAGS:
            self.excluded.append(blocked or any(self.excluded))
        self.parts.append(raw)

    def handle_startendtag(self, tag, attrs):
        self.parts.append(self.get_starttag_text())

    def handle_endtag(self, tag):
        self.parts.append(f"</{tag}>")
        if self.excluded:
            self.excluded.pop()

    def handle_data(self, data):
        self.parts.append(data if any(self.excluded) else self.annotate(data))

    def handle_entityref(self, name):
        self.parts.append(f"&{name};")

    def handle_charref(self, name):
        self.parts.append(f"&#{name};")

    def handle_comment(self, data):
        self.parts.append(f"<!--{data}-->")

    def handle_decl(self, decl):
        self.parts.append(f"<!{decl}>")


def auto_link_terms(body, lang, module, terms):
    """Link audited unambiguous glossary forms in rendered prose, longest first."""
    forms = {}
    for entry in terms:
        if entry.get("matching", "explicit") != "auto":
            continue
        for form in localized_forms(entry, lang):
            key = form.casefold() if lang == "en" else form
            if key in forms and forms[key]["id"] != entry["id"]:
                raise ValueError(f"ambiguous automatic term form {form!r} ({lang})")
            forms[key] = entry
    if not forms:
        return body
    haystack = body.casefold() if lang == "en" else body
    if not any(form in haystack for form in forms):
        return body
    alternatives = sorted((re.escape(form) for form in forms), key=len, reverse=True)
    if lang == "en":
        pattern = re.compile(r"(?<![A-Za-z])(?:" + "|".join(alternatives) + r")(?![A-Za-z])", re.I)
    else:
        pattern = re.compile("|".join(alternatives))

    def annotate(text):
        def replace(match):
            shown = match.group(0)
            key = shown.casefold() if lang == "en" else shown
            entry = forms[key]
            href = f'{entry["introduced_in"]}.html#term-{entry["id"]}'
            return (f'<a class="term-ref" data-term="{entry["id"]}" '
                    f'href="{href}">{shown}</a>')
        return pattern.sub(replace, text)

    parser = _TermLinker(annotate)
    parser.feed(body)
    parser.close()
    return "".join(parser.parts)


def fill_template(tpl, **kw):
    out = tpl
    for k, v in kw.items():
        out = out.replace(f"%%{k}%%", v)
    return out


__all__ = ['dedent_submodule_code', '_slug', '_inline', 'render_summary_inline', '_is_block_start', '_is_table_sep', 'md_to_html', 'render_statement_endings', 'render_code_scroll_content', 'restore_toc_labels', 'anchor_prose_blocks', 'markdown_body', 'plain_code', '_TermLinker', 'auto_link_terms', 'fill_template']
