"""Reusable document API for the textbook Markdown dialect.

No filesystem, project discovery, branding or site output is involved. A checked
compiler package is optional; plain code gets lexical syntax help but no types,
definition links, or expression nodes are inferred from its spelling.
"""
from dataclasses import dataclass, field
import html as htmllib
import re
from html_contract import *
from markdown_core import *
from i18n_markers import weave_for_site, group_languages
from agda_help import annotate_inline_code, annotate_keywords
from agda_semantics import (AgdaSemantics, inline_ref_link, annotate_expression_nodes,
                            annotate_unlinked_bound_types)
from boilerplate import mirror_boilerplate
from term_registry import TERM_MARK_RE


@dataclass
class CodeContext:
    """Compiler evidence and scope, shared across a book's code surfaces."""
    semantics: AgdaSemantics = field(default_factory=AgdaSemantics)
    internal: set = field(default_factory=set)
    rendered: set = field(default_factory=set)
    names: dict = field(default_factory=dict)
    canonical_names: dict = field(default_factory=dict)
    types: dict = field(default_factory=dict)
    expressions: dict = field(default_factory=dict)
    vocabulary: dict = field(default_factory=dict)
    aspects: dict = field(default_factory=dict)


@dataclass(frozen=True)
class RenderedDocument:
    body: str
    toc: list
    mirror: str
    code_blocks: tuple


class MarkdownDocument:
    def __init__(self, text, *, module='', code=None, terms=(), formal_setup=False,
                 visible_import_chapters=(), overview=False):
        self.module = module
        self.code = code or CodeContext()
        self.terms = terms
        self.formal_setup = formal_setup
        self.visible_import_chapters = visible_import_chapters
        self.languages = group_languages(text)
        self.blocks = []

        def plain_fence(match):
            # This is lexical rendering only. Compiler-highlighted blocks never
            # pass through it and keep all their original anchors and ranges.
            body = htmllib.escape(match.group(1), quote=False)
            return '<pre class="Agda">' + annotate_inline_code(
                '<code class="Agda">' + body + '</code>') + '</pre>'

        text = re.sub(r'^```agda[ \t]*\n(.*?)^```[ \t]*$', plain_fence, text, flags=re.M | re.S)
        def lift(match):
            self.blocks.append(match.group(0))
            return f'{NUL}CODE{len(self.blocks)-1}{NUL}'
        self.text = PRE_RE.sub(lift, text)
        self.local_refs = {}
        for block in self.blocks:
            for attrs, label in A_TAG_RE.findall(block):
                href = HREF_RE.search(attrs)
                if href:
                    aspect = CLASS_RE.search(attrs)
                    self.local_refs.setdefault(htmllib.unescape(label),
                        (href.group(1), aspect.group(1) if aspect else ''))
        if overview:
            for name, target in self.code.vocabulary.get('origin_vocabulary', {}).items():
                self.local_refs.setdefault(name, target)
        nodes = [node for node in self.code.expressions.get(module, [])
                 if node.get('kind') not in ('definition', 'binding', 'variable', 'binder')]
        self.blocks = [annotate_unlinked_bound_types(annotate_expression_nodes(block, nodes),
                       module, self.code.types.get(module, {})) for block in self.blocks]

    def render(self, lang):
        woven = weave_for_site(self.text, lang)
        mirror = markdown_body(woven, self.blocks)
        store = {}
        def stash(kind, payload):
            key = f'{NUL}{kind}{len(store)}{NUL}'
            store[key] = payload
            return key
        terms = {entry['id']: entry for entry in self.terms}
        def term_marker(match):
            label, kind, term_id = match.groups()
            entry = terms.get(term_id)
            if not entry:
                raise ValueError(f'unknown term id {term_id!r} in {self.module}')
            label = htmllib.escape(label)
            if kind == 'intro':
                return stash('TERM', f'<dfn id="term-{term_id}" class="term-intro" '
                             f'data-term="{term_id}" tabindex="0">{label}</dfn>')
            href = self.code.semantics.chapter_href(entry['introduced_in'], '#term-' + term_id)
            return stash('TERM', f'<a class="term-ref" data-term="{term_id}" '
                         f'href="{htmllib.escape(href, quote=True)}">{label}</a>')
        woven = TERM_MARK_RE.sub(term_marker, woven)
        woven = re.sub(r'\$\$(.+?)\$\$', lambda m: stash('DMATH',
            '<div class="math display">$$' + htmllib.escape(m[1]) + '$$</div>'), woven, flags=re.S)
        woven = re.sub(r'\$(.+?)\$', lambda m: stash('IMATH',
            '<span class="math inline">$' + htmllib.escape(m[1]) + '$</span>'), woven)
        woven = INLINE_AGDA_LINK_RE.sub(lambda m: stash('REF', inline_ref_link(
            m[1], m[2], m[3], self.code.names)), woven)
        woven = INLINE_AGDA_RE.sub(lambda m: stash('REF', self.code.semantics.inline_ref(
            m[1], self.code.internal, self.code.names, self.local_refs,
            self.module, self.code.vocabulary)), woven)
        body, toc = md_to_html(render_summary_inline(woven))
        body = re.sub(r'<p>\s*(' + NUL + r'(?:CODE|DMATH)\d+' + NUL + r')\s*</p>', r'\1', body)
        body = anchor_prose_blocks(body)
        for key, value in store.items():
            body = body.replace(key, value)
        toc = restore_toc_labels(toc, store)
        for index, block in enumerate(self.blocks):
            body = body.replace(f'{NUL}CODE{index}{NUL}', block)
        body = annotate_inline_code(body, self.code.semantics.inline_reference_resolver(
            self.local_refs, self.module, self.code.vocabulary))
        if self.code.rendered:
            body = self.code.semantics.rewrite_links(body, self.code.rendered, self.code.types,
                self.code.canonical_names, self.module, self.code.vocabulary)
        body = dedent_submodule_code(body)
        body = render_statement_endings(body, lang)
        body = annotate_keywords(body, lang)
        if self.formal_setup:
            body = mirror_boilerplate(body, self.module, self.code.internal,
                                     visible_import_chapters=self.visible_import_chapters)
        body = auto_link_terms(body, lang, self.module, self.terms)
        return RenderedDocument(render_code_scroll_content(body), toc, mirror, tuple(self.blocks))
