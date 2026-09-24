#!/usr/bin/env python3
"""Render the multilingual, hyperlinked Bedrock site from the masters.

Inputs (produced by the Makefile before this runs):
  _build/html/<Module>.md   from `agda --html --html-highlight=code` on src/Origin
  _build/types.json         from scripts/site/extract-types.py
  _build/expression-types.json from scripts/site/extract-expression-types.py
  site/template.html        the page shell
  site/vendor/1lab/...      vendored front-end assets (M2c builds CSS/JS into the site)

For each enabled language it weaves the prose by markers, splices the language-neutral
highlighted code, resolves inline `name`{.Agda} references, protects math for client-side
KaTeX, rewrites links (+ data-type for hover), and writes _build/site/<lang>/<Module>.html.
It also emits per-module types/<Module>.json (pos -> abbreviated, hyperlinked type) and a
per-language search.json, a per-language index, and a root language-redirect + 404.

Usage:
  render-site.py [--html-dir _build/html] [--types _build/types.json] [--src src]
                 [--expression-types _build/expression-types.json]
                 [--template site/template.html] [--out _build/site]
                 [--langs en,zh,ja] [--base-url ""] [--site Bedrock]
"""

import glob
import hashlib
import html as htmllib
from html.parser import HTMLParser
import json
import os
import re
import shutil
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from i18n_markers import weave_for_site, group_languages  # noqa: E402
from statement_structure import LABEL_RE, PROOF_LABELS
from submodule_structure import module_header_line
from diagram_style import check_sources as check_diagrams  # noqa: E402
from reading_routes import GUIDE_PANEL, build_reading_data, own_page, twin_of  # noqa: E402
from agda_help import HELP, annotate_inline_code, annotate_keywords, help_html, inline_syntax_ranges
from boilerplate import mirror_boilerplate
from search_index import passages
from term_registry import (TERM_MARK_RE, load_entries, reader_terms, schema_errors,
                           localized_forms, localized_abbreviation)  # noqa: E402

LANG_LABELS = {"en": "English", "zh": "中文", "ja": "日本語"}

UI = {
    "en": {"search": "Search…", "theme": "Toggle theme", "contents": "On this page",
           "menu": "Menu", "close": "Close",
           "untranslated": "This page is not yet translated; showing English.",
           "modules": "Modules", "source": "Source", "overview": "Overview",
           "depmap": "Dependency graph", "routes": "Reading routes",
           "current_route": "Current route",
           "guide": "Interactive contents", "catalog": "Chapter catalog",
           "landmark": "Origin", "terms": "Glossary",
           "prev": "Previous chapter", "next": "Next chapter",
           "license": "content licensed CC BY-NC-SA 4.0",
           "markdown": "Markdown", "agents": "llms.txt",
           "mdtitle": "This page as plain Markdown, for AI agents and scripts",
           "agentstitle": "How an AI agent should read this site",
           "credit": 'Rendered with a generator adapted from '
                     '<a href="https://1lab.dev">the 1lab</a> (AGPL-3.0).',
           "external": "You are viewing the Cubical library.",
           "back": "Back to Bedrock"},
    "zh": {"search": "搜索…", "theme": "切换主题", "contents": "本页内容",
           "menu": "菜单", "close": "关闭",
           "untranslated": "本页尚未翻译，此处显示英文。",
           "modules": "模块", "source": "源码", "overview": "概览",
           "depmap": "依赖图", "routes": "阅读路线",
           "current_route": "当前路线",
           "guide": "交互式目录", "catalog": "章节目录",
           "landmark": "原点", "terms": "术语表",
           "prev": "上一章", "next": "下一章",
           "license": "内容以 CC BY-NC-SA 4.0 许可",
           "markdown": "Markdown", "agents": "llms.txt",
           "mdtitle": "本页的纯 Markdown 版本，供 AI 与脚本读取",
           "agentstitle": "AI 应当如何阅读本站",
           "credit": '使用改编自 <a href="https://1lab.dev">1lab</a> 的生成器渲染 '
                     '(AGPL-3.0)',
           "external": "您正在浏览 Cubical 库。",
           "back": "返回 Bedrock"},
    "ja": {"search": "検索…", "theme": "テーマ切替", "contents": "このページの内容",
           "menu": "メニュー", "close": "閉じる",
           "untranslated": "このページは未翻訳です。英語を表示しています。",
           "modules": "モジュール", "source": "ソース", "overview": "概要",
           "depmap": "依存グラフ", "routes": "学習ルート",
           "current_route": "現在のルート",
           "guide": "対話型目次", "catalog": "章の目次",
           "landmark": "原点", "terms": "用語集",
           "prev": "前の章", "next": "次の章",
           "license": "コンテンツは CC BY-NC-SA 4.0 ライセンス",
           "markdown": "Markdown", "agents": "llms.txt",
           "mdtitle": "このページの純 Markdown 版。AI とスクリプト向け",
           "agentstitle": "AI エージェントのための読み方",
           "credit": '<a href="https://1lab.dev">1lab</a> を改変した'
                     'ジェネレータでレンダリング (AGPL-3.0)。',
           "external": "Cubical ライブラリを閲覧しています。",
           "back": "Bedrock に戻る"},
}
SOURCE_URL = "https://github.com/BedrockInstitute/Bedrock"
SOURCE_TREE = SOURCE_URL + "/blob/main/src"   # a chapter's master, for a reader who wants the source
SITE_URL = "https://bedrock.institute"        # canonical deployment (.github/workflows/ci.yml)
LANDING = "Origin"  # preview chapter also supplies the generated reading-guide index
CHAPTER_TITLES = {}
# module -> {"description": {lang: str}, "stage": {lang: str}, "order": int,
#            "prerequisites": [module], "routes": [route id]}. Filled from the reading
# catalog, and read by the per-page description, the JSON-LD graph, the Markdown mirror
# and llms.txt, so all four say the same thing about a chapter.
CHAPTER_META = {}
SEARCH_PASSAGES = []


def chapter_title(module, lang):
    titles = CHAPTER_TITLES.get(module, {})
    return titles.get(lang, titles.get("en", module))


def chapter_href(module, anchor=""):
    """Where a chapter is read, as the reading catalog says.

    `scripts/site/reading_routes.py` decides a chapter's address and puts it on the
    node as `page` and `anchor`; this function only assembles them, so the renderer,
    the route explorer and the dependency map cannot disagree about where a chapter
    lives. A preview chapter has no page of its own and resolves to a panel of the
    reading guide, which embeds its whole body, so an anchor the chapter defines still
    resolves; an explicit anchor therefore wins over the panel's own.

    A module with no catalog entry is a library page rendered for reference, not a
    chapter, and is addressed by its own name.
    """
    meta = CHAPTER_META.get(module)
    if not meta:
        return own_page(module) + anchor
    return meta["page"] + (anchor or meta["anchor"])


def chapter_field(module, field, lang, default=""):
    """One localized field of a chapter's catalog entry ('description' or 'stage')."""
    values = CHAPTER_META.get(module, {}).get(field, {})
    return values.get(lang, values.get("en", default))


SITE_BLURB = {
    "en": "A machine-checked development of set theory in Cubical Agda. The constructible "
          "universe L is proved to model ZFC and to satisfy GCH.",
    "zh": "用 Cubical Agda 完成的机器验证集合论。已经证明可构造宇宙 L 是 ZFC 的模型并满足 GCH。",
    "ja": "Cubical Agda による機械検証された集合論。構成可能宇宙 L が ZFC のモデルであり "
          "GCH を満たすことを証明済みです。",
}


def page_description(module, lang, is_landing, is_external):
    """The page's own <meta name=description>, never the bare site name."""
    if is_external:
        return {
            "en": f"{module}, a module of the Cubical standard library, rendered for reference "
                  "inside the Bedrock textbook.",
            "zh": f"{module}：Cubical 标准库的一个模块，在 Bedrock 教科书中渲染以供查阅。",
            "ja": f"{module}：Cubical 標準ライブラリのモジュール。Bedrock の教科書内に参照用として"
                  "描画したものです。",
        }[lang]
    if is_landing:
        return SITE_BLURB[lang]
    title = chapter_title(module, lang)
    described = chapter_field(module, "description", lang, title)
    if described.rstrip(".") != title.rstrip("."):
        return described
    # Several catalog entries describe a chapter by restating its title. Repeating that
    # as the page description would leave a search engine and an agent with one fact
    # twice over, so place the chapter instead.
    meta = CHAPTER_META.get(module, {})
    stage = chapter_field(module, "stage", lang)
    position, total = meta.get("order", 0), len(CHAPTER_META)
    shape = {
        "en": f"{title}. Chapter {position} of {total} of the Bedrock textbook, in the "
              f"{stage} stage, developed as the Agda module {module}.",
        "zh": f"{title}。Bedrock 教科书第 {position} 章，全书共 {total} 章，"
              f"属于{stage}阶段，对应 Agda 模块 {module}。",
        "ja": f"{title}。Bedrock 教科書の第 {position} 章（全 {total} 章）、{stage}段階、"
              f"Agda モジュール {module} として展開します。",
    }
    return shape.get(lang, shape["en"])

PRE_RE = re.compile(r'<pre class="Agda">.*?</pre>', re.DOTALL)
SUBMODULE_HTML_TOKEN_RE = re.compile(
    r'<pre class="Agda">.*?</pre>|</?details\b[^>]*>|</?summary\b[^>]*>',
    re.DOTALL,
)


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
# Definition site: <a id="NAME"></a><a id="POS" ... class="ASPECT" ...>token</a>
DEF_RE = re.compile(r'<a id="([^"]+)"></a><a id="(\d+)"[^>]*class="([^"]*)"')
# Renamed imports have no named definition anchor, but later occurrences link
# to the unlinked token following ``to``.  Index that token as the declaration
# site so the imported type can be attached there and reused by every link.
RENAMED_RE = re.compile(
    r'<a id="\d+" class="Symbol">to</a>[ \t]*'
    r'<a id="(\d+)" class="([^"]+)">([^<]+)</a>'
)
# Agda does not expose declarations nested in a `where` block through
# Cmd_show_module_contents_toplevel. Its checked HTML still identifies the
# declaration site and renders the declared type on the same line.
LOCAL_SIGNATURE_RE = re.compile(
    r'(?m)^(?:<pre\b[^>]*>)?[ \t]*(?:<a id="[^"]+"></a>)?'
    r'<a id="(?P<pos>\d+)" href="(?P<module>[^"]+)\.html#(?P=pos)" '
    r'class="(?P<aspect>[^"]*)">(?P<name>[^<]+)</a>[ \t]*'
    r'<a id="\d+" class="Symbol">:</a>[ \t]*(?P<type>[^\n]+)'
)
LOCAL_DECL_RE = re.compile(
    r'<a id="(?P<pos>\d+)" href="(?P<module>[^"]+)\.html#(?P=pos)" '
    r'class="(?P<aspect>[^"]*)">(?P<name>[^<]+)</a>'
)
TYPE_COLON_RE = re.compile(r'<a id="\d+" class="Symbol">:</a>[ \t]*')
# Any cross-reference link inside highlighted code (optional self-id, optional #position).
LINK_RE = re.compile(r'<a (id="\d+" )?href="([^"#]+)\.html(#\d+)?"([^>]*)>')
INLINE_AGDA_RE = re.compile(r'`([^`]+)`\{\.Agda\}')
INLINE_AGDA_LINK_RE = re.compile(r'\[([^\]]+)\]\(([\w.]+)\.html#([^\s)]+)\)\{\.Agda\}')
SUMMARY_RE = re.compile(r'<summary([^>]*)>(.*?)</summary>', re.DOTALL)
A_TAG_RE  = re.compile(r'<a\b([^>]*)>([^<]+)</a>')
TOKEN_RE = re.compile(r'<a\b[^>]*\bid="(\d+)"[^>]*>(.*?)</a>', re.DOTALL)
HREF_RE   = re.compile(r'\bhref="([^"]+\.html(?:#\d+)?)"')
CLASS_RE  = re.compile(r'\bclass="([^"]*)"')
ID_RE = re.compile(r'\bid="(\d+)"')
PRELUDE_MODULE = "Base.Prelude"


def ref_link(href, aspect, label, extra_class=""):
    """An inline-ref anchor; hover data only when the href has a position."""
    mod, _, pos = href.rpartition(".html#")
    dt = f' data-type="{mod}#{pos}"' if mod and pos.isdigit() else ""
    cls = (extra_class + (" " + aspect if aspect else "")).strip()
    cls = f' class="{cls}"' if cls else ""
    return f'<a href="{href}"{cls}{dt}>{label}</a>'
NUL = "\x00"


# ---- small stdlib Markdown renderer (the prose subset Bedrock uses) ----------

def _slug(n):
    return f"sec-{n}"


_PLACEHOLDER = re.compile(NUL + r'[A-Z]+\d+' + NUL)
_BLOCK_PLACEHOLDER = re.compile(NUL + r'(?:CODE|DMATH)\d+' + NUL)


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


def render_review_status(body, module, lang):
    """Human editorial review is catalog metadata, not inferred from CI success."""
    reviewed = CHAPTER_META.get(module, {}).get('human_reviewed', False)
    label = {
        'en': ('Human-reviewed', 'Not yet human-reviewed'),
        'zh': ('已人工校阅', '未人工校阅'),
        'ja': ('人手による校閲済み', '人手による校閲は未実施'),
    }[lang][0 if reviewed else 1]
    icon = ('<path d="M12 3 20 6v6c0 5-8 9-8 9s-8-4-8-9V6Z"/>'
            '<path d="m8 12 3 3 5-6"/>' if reviewed else
            '<path d="m12 3 10 18H2Z"/><path d="M12 9v5m0 3v.1"/>')
    badge = (f'<span class="chapter-review {"is-reviewed" if reviewed else "is-unreviewed"}" '
             f'role="img" tabindex="0" aria-label="{label}" data-label="{label}">'
             '<svg viewBox="0 0 24 24" aria-hidden="true" focusable="false">'
             + icon + '</svg></span>')
    return re.sub(r'<h1\b[^>]*>.*?</h1>',
                  lambda match: '<div class="chapter-heading-row">' + match[0]
                  + badge + '</div>', body, count=1, flags=re.S)


def restore_toc_labels(toc, store):
    """Replace protected inline markup in TOC labels with its visible plain text."""
    clean = []
    for level, anchor, title in toc:
        for key, value in store.items():
            title = title.replace(key, re.sub(r"<[^>]+>", "", value))
        clean.append((level, anchor, htmllib.unescape(title)))
    return clean


# ---- code-block index (names, positions, types) ------------------------------

def source_file(html_dir, module):
    """agda --html emits <Module>.md for literate sources (prose + <pre class=Agda> code) and
    <Module>.html for library modules (bare highlighted code, no <pre>). Returns (path,
    is_literate)."""
    md = os.path.join(html_dir, module + ".md")
    if os.path.exists(md):
        return md, True
    return os.path.join(html_dir, module + ".html"), False


def index_definitions(code_html, module, name2pos, pos_aspect):
    """Record (module-local name -> pos) and (pos -> aspect) from highlighted code."""
    for name, pos, aspect in DEF_RE.findall(code_html):
        name2pos.setdefault(module, {})[name] = pos
        pos_aspect.setdefault(module, {})[pos] = aspect.split()[-1] if aspect else ""
    for pos, aspect, name in RENAMED_RE.findall(code_html):
        if aspect == "Keyword" or aspect == "Module":
            continue
        name = htmllib.unescape(name)
        name2pos.setdefault(module, {}).setdefault(name, pos)
        pos_aspect.setdefault(module, {}).setdefault(
            pos, aspect.split()[-1] if aspect else ""
        )


def qualified_name_pattern(internal_q):
    """Compile one longest-first matcher instead of scanning every known name."""
    alternatives = sorted(internal_q, key=len, reverse=True)
    # A module prefix or a renamed field such as `s` must not consume part of
    # an unknown qualified name such as Helpers.isContr or Isomorphism.section.
    return re.compile(r"(?<![^\s(){};])(?:" + "|".join(map(re.escape, alternatives))
                      + r")(?![^\s(){};])") if alternatives else None


def add_prelude_qualified_names(internal_q, prelude_reexports):
    """Make Prelude's public vocabulary available to type rendering.

    Re-export anchors are not declarations, so Agda's ordinary definition index
    does not contain qualified names such as ``Base.Prelude.Type``.  They are
    nevertheless the canonical reader-facing targets used by source blocks.
    Index them alongside declarations so a name remains the same interactive
    leaf when it occurs inside a rendered hover type.
    """
    for shown, (module, position, _aspect, _label) in (
            prelude_reexports.get("by_name", {}).items()):
        internal_q.setdefault(f"{module}.{shown}", (module, position))


TYPE_NODE_TAG_RE = re.compile(r'<span class="type-node"[^>]*>|</span>')


def wrap_expression_ranges(block, nodes, by_start, by_end, opening_for,
                           split_multiline=False):
    """Wrap compiler-backed ranges using one nesting algorithm on every surface."""
    usable = [node for node in nodes
              if node["start"] in by_start and node["end"] in by_end]
    if not usable:
        return block

    # Count containing ranges in O(n log n). The wrapper is shared by source
    # blocks and hover types, so their nesting levels and event ordering cannot
    # drift apart.
    unique_ranges = sorted(
        {(node["start"], node["end"]) for node in usable},
        key=lambda interval: (interval[0], -interval[1]),
    )
    ends = sorted({end for _, end in unique_ranges})
    end_index = {end: index + 1 for index, end in enumerate(ends)}
    tree = [0] * (len(ends) + 1)

    def add(index):
        while index < len(tree):
            tree[index] += 1
            index += index & -index

    def prefix(index):
        total = 0
        while index:
            total += tree[index]
            index -= index & -index
        return total

    depth_by_range = {}
    inserted = 0
    for start, end in unique_ranges:
        before_end = prefix(end_index[end] - 1)
        depth_by_range[(start, end)] = inserted - before_end
        add(end_index[end])
        inserted += 1

    openings, closings = {}, {}
    for node in usable:
        start, end = node["start"], node["end"]
        depth = depth_by_range[(start, end)]
        opening = opening_for(node, depth)
        openings.setdefault(by_start[start], []).append((end, opening))
        closings.setdefault(by_end[end], []).append((start, "</span>"))
    events = {}
    for position in set(openings) | set(closings):
        closing = "".join(text for _, text in sorted(
            closings.get(position, []), reverse=True
        ))
        opening = "".join(text for _, text in sorted(
            openings.get(position, []), reverse=True
        ))
        events[position] = closing + opening
    for position in sorted(events, reverse=True):
        block = block[:position] + events[position] + block[position:]
    return split_multiline_expression_nodes(block) if split_multiline else block


def semantic_type_index(nodes):
    """Index unambiguous compiler nodes by a short source prefix."""
    candidates = {}
    ambiguous = set()
    for node in nodes:
        source = " ".join(node.get("source", "").split())
        if node.get("kind") != "application" or not source:
            continue
        signature = node.get("type", "")
        previous = candidates.get(source)
        if previous and previous.get("type") != signature:
            ambiguous.add(source)
        else:
            candidates[source] = node
    for source in ambiguous:
        candidates.pop(source, None)
    prefixes = {}
    for source, node in candidates.items():
        prefix = source[:min(4, len(source))]
        prefixes.setdefault(prefix, []).append((source, node))
    for bucket in prefixes.values():
        bucket.sort(key=lambda item: len(item[0]), reverse=True)
    return prefixes


def is_universe_type_text(text):
    """Whether reader-facing source text is exactly one universe application."""
    normalized = " ".join((text or "").split())
    if re.fullmatch(r"Type(?:ω|[₀-₉]+)?", normalized):
        return True
    if not normalized.startswith("Type "):
        return False
    return not re.search(r"[→,:{}\[\]=≃×]", normalized[5:])


def is_universe_former_signature(text):
    """Whether a type is the polymorphic universe former's own signature."""
    normalized = " ".join((text or "").split())
    normalized = re.sub(r"(?:[A-Za-z][\w']*\.)+", "", normalized)
    match = re.fullmatch(
        r"\(\s*([^():{}\[\],→\s]+)\s*:\s*Level\s*\)\s*→\s*"
        r"(?:Type|Set)\s+([^()\s→,:{}\[\]=≃×]+)",
        normalized,
    )
    return bool(match and match.group(1) == match.group(2))


def decorate_type_nodes(type_html, semantic_nodes=None, module=""):
    """Add only compiler-backed source-expression ranges to a rendered type.

    Agda does not emit an AST trace for the separately rendered type sidecar.
    We may reuse an application range when its exact source text occurs in the
    type, but punctuation and balanced delimiters are not evidence of a node.
    Consequently every emitted type node has a real expression payload and can
    open another hover. Terminal universe applications keep their linked names
    but have no structural wrapper to colour or select.
    """
    pairs = {"(": ")", "[": "]", "{": "}"}

    semantic_index = (semantic_nodes if isinstance(semantic_nodes, dict)
                      else semantic_type_index(semantic_nodes or []))
    if not semantic_index:
        return type_html

    def split_delimiter_token(match):
        opening, inner = match.group(1), match.group(2)
        if "<" in inner:
            return match.group(0)
        label = htmllib.unescape(inner)
        pieces, plain = [], []

        def flush_plain():
            if plain:
                pieces.append("".join(plain))
                plain.clear()

        for character in label:
            if character in pairs or character in pairs.values():
                flush_plain()
                pieces.append(character)
            else:
                plain.append(character)
        flush_plain()
        if len(pieces) <= 1:
            return match.group(0)
        return "".join(opening + htmllib.escape(piece, quote=False) + "</a>"
                       for piece in pieces)

    # Agda sometimes colours adjacent delimiters as one token, for example
    # ``((``.  A structural boundary can fall between them.  Split only that
    # token, preserving every link attribute, just as source-expression
    # annotation splits punctuation tokens at exact AST boundaries.
    type_html = re.sub(r'(<a\b[^>]*>)(.*?)</a>', split_delimiter_token,
                       type_html, flags=re.DOTALL)
    units = []
    visible = []
    for match in re.finditer(r'<[^>]+>|&(?:#\d+|#x[0-9a-fA-F]+|\w+);|.',
                             type_html, re.DOTALL):
        token = match.group(0)
        if token.startswith("<"):
            continue
        decoded = htmllib.unescape(token)
        for character in decoded:
            visible.append(character)
            units.append((match.start(), match.end()))
    visible_text = "".join(visible)

    def token_boundary(position):
        # Exact text is insufficient inside a longer identifier: neither
        # Resizing in ΩResizing nor ℓ in ℓ₁ is the traced token.
        if position == 0 or position == len(visible_text):
            return True
        left, right = visible_text[position - 1:position + 1]
        return (left.isspace() or right.isspace()
                or left in "(){};" or right in "(){};")

    # The compiler trace already gives real application nodes and their types.
    # Reuse those nodes when their exact source occurs in a rendered type.  The
    # resulting data key resolves through the same $expressions sidecar used by
    # source Agda blocks, so a node in a hover can open another hover indefinitely.
    visible_ranges = []
    for start in range(len(visible_text)):
        if not token_boundary(start):
            continue
        for prefix_length in range(min(4, len(visible_text) - start), 0, -1):
            bucket = semantic_index.get(
                visible_text[start:start + prefix_length], []
            )
            for source, node in bucket:
                if (visible_text.startswith(source, start)
                        and token_boundary(start + len(source))):
                    if not is_universe_type_text(source):
                        visible_ranges.append((
                            start, start + len(source), f'{module}#{node["id"]}',
                        ))

    # After delimiter tokens have been split, semantic spans can expand to
    # complete anchors without swallowing a neighbouring delimiter.
    anchors = [(match.start(), match.end())
               for match in re.finditer(r"<a\b[^>]*>.*?</a>", type_html, re.DOTALL)]

    def outside_start(position):
        return next((start for start, end in anchors if start < position < end), position)

    def outside_end(position):
        return next((end for start, end in anchors if start < position < end), position)

    ranges = {(start, end): expression_key
              for start, end, expression_key in visible_ranges
              if start < end and end <= len(units)}

    # Matches borrowed from other source occurrences must still form the same
    # laminar range tree as Agda's own source trace. A crossing pair cannot be
    # an AST nesting relation, so neither is shown as a node.
    crossing = set()
    intervals = sorted(ranges)
    for index, (left_start, left_end) in enumerate(intervals):
        for right_start, right_end in intervals[index + 1:]:
            if right_start >= left_end:
                break
            if left_start < right_start < left_end < right_end:
                crossing.update(((left_start, left_end), (right_start, right_end)))
    nodes = [{"start": start, "end": end,
              "expressionKey": ranges[(start, end)]}
             for start, end in intervals if (start, end) not in crossing]
    by_start = {node["start"]: outside_start(units[node["start"]][0])
                for node in nodes}
    by_end = {node["end"]: outside_end(units[node["end"] - 1][1])
              for node in nodes}

    def type_opening(node, depth):
        return (f'<span class="type-node" '
                f'data-expression-type="{node["expressionKey"]}" '
                f'data-expr-start="{node["start"]}" '
                f'data-expr-end="{node["end"]}" '
                f'style="--expr-level:{depth % 6}">')

    return wrap_expression_ranges(
        type_html, nodes, by_start, by_end, type_opening
    )


def render_type(term, internal_q, name_pattern=None, pos_aspect=None,
                current_module="", prelude_reexports=None):
    """Abbreviate and link an Agda type string."""
    universe_former = is_universe_former_signature(term)
    s = htmllib.escape(term.replace("\n", " "), quote=False)
    links, level_names = [], []
    def protect_level_name(match):
        token = f"{NUL}V{len(level_names)}{NUL}"
        level_names.append(match.group(0))
        return token
    # Agda disambiguates independently quantified universe levels as A.ℓ and
    # B.ℓ. They are binder names rather than module qualification and must
    # survive the qualifier abbreviation below.
    s = re.sub(r"\b[A-Z][A-Za-z0-9_']*\.ℓ[\w']*\b", protect_level_name, s)
    if name_pattern:
        def protect_link(match):
            q = match.group(0)
            mod, pos = internal_q[q]
            tok = f"{NUL}L{len(links)}{NUL}"
            last = q.split(".")[-1]
            bridge = ((prelude_reexports or {}).get("by_href", {}).get(
                f"{mod}.html#{pos}"
            ) if current_module != PRELUDE_MODULE else None)
            target_mod, target_pos, target_name = mod, pos, last
            if bridge:
                target_mod, target_pos, _, target_name = bridge
            aspect = (pos_aspect or {}).get(target_mod, {}).get(target_pos, "")
            class_ = f' class="{aspect}"' if aspect else ""
            primitive_stop = (aspect == "Primitive"
                              and target_name in NON_HOVER_PRIMITIVE_SORTS)
            type_data = ("" if primitive_stop
                         else f' data-type="{target_mod}#{target_pos}"')
            if primitive_stop:
                hover_stop = ' data-hover-stop="primitive-sort"'
            elif universe_former and target_name in {"Type", "Set"}:
                hover_stop = ' data-hover-stop="universe-former"'
            else:
                hover_stop = ""
            links.append(
                f'<a href="{chapter_href(target_mod, "#" + target_pos)}"'
                f'{type_data}'
                f'{hover_stop}'
                f' data-name="{htmllib.escape(target_name, quote=True)}"'
                f'{class_}>{htmllib.escape(last)}</a>'
            )
            return tok
        s = name_pattern.sub(protect_link, s)
    s = re.sub(r"(?:[A-Za-z][\w']*\.)+", "", s)        # strip remaining (external) qualifiers
    # A sort without its own hover payload remains ordinary code text. Agda
    # prints universes as Set, Set₁, Setω, and so on; use the cubical name.
    s = re.sub(r"\bSet(?=$|[₀-₉ω]|[^\w'])", "Type", s)
    for i, level_name in enumerate(level_names):
        s = s.replace(f"{NUL}V{i}{NUL}", level_name)
    for i, link in enumerate(links):
        s = s.replace(f"{NUL}L{i}{NUL}", link)
    # Hover signatures use the same lexical syntax pass as prose code, while
    # preserving the compiler-derived definition links already inserted above.
    prefix, suffix = '<span class="Agda">', '</span>'
    s = annotate_inline_code(prefix + s + suffix)[len(prefix):-len(suffix)]
    return decorate_type_nodes(s)


# ---- per-page rendering ------------------------------------------------------

def lang_nav(out_name, lang, langs):
    """Language switcher; `out_name` is this page's filename (index.html for the landing)."""
    bits = []
    for L in langs:
        if L == lang:
            bits.append(f'<span class="cur">{LANG_LABELS[L]}</span>')
        else:
            bits.append(f'<a href="../{L}/{out_name}">{LANG_LABELS[L]}</a>')
    return " · ".join(bits)


def hreflang_links(out_name, langs, base):
    return "\n".join(
        f'  <link rel="alternate" hreflang="{L}" href="{base}/{L}/{out_name}" />'
        for L in langs)


def toc_html(toc, lang):
    """The 'On this page' sidebar section (empty when the page has no sub-headings)."""
    if not toc:
        return ""
    roots, stack = [], []
    for level, anchor, title in toc:
        node = {"level": level, "anchor": anchor, "title": title, "children": []}
        while stack and stack[-1]["level"] >= level:
            stack.pop()
        (stack[-1]["children"] if stack else roots).append(node)
        stack.append(node)

    def item(node):
        anchor = htmllib.escape(node["anchor"], quote=True)
        link = f'<a href="#{anchor}">{htmllib.escape(node["title"])}</a>'
        if node["children"]:
            children = "".join(item(child) for child in node["children"])
            link = (f'<details class="toc-branch" data-heading="{anchor}">'
                    f'<summary>{link}</summary><ul>{children}</ul></details>')
        return f'<li class="toc-l{node["level"]}">{link}</li>'

    items = "".join(item(node) for node in roots)
    return (f'<details class="navsec" open><summary class="nav-title">'
            f'{UI[lang]["contents"]}</summary>'
            f'<ul class="toc">{items}</ul></details>')


def modules_nav(current, mods, lang, reading_data):
    """Contents and the current route; the graph owns namespace browsing."""

    guide = "".join(
        f'<li><a href="index.html#{target}">{UI[lang][key]}</a></li>'
        for target, key in ((GUIDE_PANEL, "landmark"),
                            ("reading-explorer", "routes"),
                            ("dependency-map", "depmap"),
                            ("term-glossary", "terms")))
    routes = reading_data["routes"]
    route = next((item for item in routes if current in item["chapters"]), routes[0])
    route_title = htmllib.escape(route["title"][lang])
    def route_link(module):
        active = ' aria-current="page"' if module == current else ""
        return (f'<li><a href="{chapter_href(module)}" data-chapter="{module}"{active}>'
                f'{htmllib.escape(chapter_title(module, lang))}</a></li>')
    route_links = "".join(route_link(module) for module in route["chapters"])
    return (f'<details class="navsec reading-guide"><summary class="nav-title">'
            f'{UI[lang]["guide"]}</summary><ul class="guide-nav">{guide}</ul></details>'
            f'<details class="navsec current-route" open data-current="{current}" '
            f'data-lang="{lang}"><summary class="nav-title">'
            f'{UI[lang]["current_route"]}<span class="current-route-name">{route_title}</span>'
            f'</summary><ul class="route-nav" data-route="{route["id"]}">'
            f'{route_links}</ul></details>')


def chapter_navigation(body, module, modules, lang):
    """Identical, compact top/bottom navigation for chapters and Origin."""
    if module not in modules:
        return body
    index = modules.index(module)
    links = []
    for direction, offset, path in (('prev', -1, 'm14 5-7 7 7 7'),
                                     ('next', 1, 'm10 5 7 7-7 7')):
        target = index + offset
        if not 0 <= target < len(modules):
            continue
        title = chapter_title(modules[target], lang)
        label = htmllib.escape(f'{UI[lang][direction]}: {title}', quote=True)
        icon = (f'<svg class="chapnav-icon" viewBox="0 0 24 24" aria-hidden="true" '
                f'focusable="false" fill="none" stroke="currentColor" stroke-width="1.7" '
                f'stroke-linecap="round" stroke-linejoin="round"><path d="{path}"/></svg>')
        text = f'<span class="chapnav-title">{htmllib.escape(title)}</span>'
        content = icon + text if direction == 'prev' else text + icon
        links.append(f'<a class="chapnav-{direction}" rel="{direction}" '
                     f'aria-label="{label}" href="{chapter_href(modules[target])}">{content}</a>')
    if not links:
        return body
    label = {'en': 'Chapter navigation', 'zh': '章节导航', 'ja': '章のナビゲーション'}[lang]
    nav = f'<nav class="chapnav" aria-label="{label}">{"".join(links)}</nav>'
    end = body.find('</h1>')
    split = end + len('</h1>') if end >= 0 else 0
    return body[:split] + nav.replace('class="chapnav"', 'class="chapnav chapnav-top"', 1) + body[split:] + nav


def learning_home(body, mount, lang, terms):
    labels = {
        "en": ("Explore the book", "Reading routes", "Dependency graph", "Origin", "Glossary"),
        "zh": ("浏览本书", "阅读路线", "依赖图", "原点", "术语表"),
        "ja": ("本書を読む", "学習ルート", "依存グラフ", "原点", "用語集"),
    }[lang]
    heading_pattern = r'<div class="chapter-heading-row">.*?</div>|<h1\b[^>]*>.*?</h1>'
    heading_match = re.search(heading_pattern, body, re.DOTALL)
    heading = heading_match.group(0) if heading_match else ""
    # The guide is a shell, not a replacement for the embedded chapter.
    # Preserve the chapter's hover trigger, source anchors and review badge.
    milestone_heading = (re.sub(r'<(/?)h1\b', r'<\1h2', heading)
                         if heading else f'<h2>{labels[3]}</h2>')
    guide_heading = f'<h1 id="reading-guide-title">{htmllib.escape(UI[lang]["guide"])}</h1>'
    milestone_body = re.sub(heading_pattern, "", body, count=1, flags=re.DOTALL)
    # Keep the embedded chapter's sections beneath its h2 without changing ids.
    milestone_body = re.sub(r'<(/?)h([2-5])\b',
                            lambda m: f'<{m[1]}h{int(m[2]) + 1}', milestone_body)
    intro_text = {
        "en": "Begin with the main theorems, then choose a reading route or inspect their prerequisites.",
        "zh": "先看本书要证明的主要定理，再选择阅读路线或查看它们的先修关系。",
        "ja": "まず本書の主要定理を見てから、学習ルートやその前提関係を確かめます。",
    }[lang]
    ids = (GUIDE_PANEL, "reading-explorer", "dependency-map", "term-glossary")
    tabs = ''.join(f'<a id="tab-{key}" href="#{key}" data-panel="{key}">{label}</a>'
                   for key, label in zip(ids, (labels[3], labels[1], labels[2], labels[4])))
    glossary_rows = []
    glossary_copy = {
        "en": "The terms are ordered by their first appearance in the book. Select a term to revisit its introduction.",
        "zh": "术语按它们在全书中的首次出现顺序排列。选择术语即可回到首次引入的位置。",
        "ja": "用語は本書で最初に現れる順に並んでいます。用語を選ぶと、最初の導入箇所を振り返れます。",
    }[lang]
    glossary_search = {
        "en": "Filter terms",
        "zh": "筛选术语",
        "ja": "用語を絞り込む",
    }[lang]
    glossary_empty = {
        "en": "No matching terms.",
        "zh": "没有匹配的术语。",
        "ja": "一致する用語がありません。",
    }[lang]
    for index, entry in enumerate(terms, 1):
        label = glossary_label_html(entry, lang)
        recap = htmllib.escape(entry[f"recap_{lang}"])
        href = chapter_href(entry["introduced_in"], f'#term-{entry["id"]}')
        search_text = htmllib.escape(
            f'{" ".join(localized_forms(entry, lang))} {entry[f"recap_{lang}"]}', quote=True)
        glossary_rows.append(
            f'<div class="term-entry" data-term-entry data-term-search="{search_text}">'
            f'<span class="term-index" aria-hidden="true">{index}</span>'
            f'<dt><a href="{href}">{label}</a></dt><dd>{recap}</dd></div>')
    glossary = ''.join(glossary_rows)
    return (f'<header class="book-intro">{guide_heading}</header>'
            f'<p class="book-intro-lead">{intro_text}</p>'
            f'<nav class="book-tabs" aria-label="{labels[0]}">{tabs}</nav>'
            f'<div class="book-panels"><section id="{GUIDE_PANEL}" '
            f'class="book-panel guide-landmark">{milestone_heading}'
            f'{milestone_body}</section>'
            f'{mount}'
            f'<section id="dependency-map" class="book-panel">'
            '<!-- DEPENDENCY_MAP --></section>'
            f'<section id="term-glossary" class="book-panel term-glossary-panel"><h2>{labels[4]}</h2>'
            f'<div class="term-glossary-head"><p>{glossary_copy}</p>'
            f'<label class="term-glossary-search"><span class="sr-only">{glossary_search}</span>'
            f'<input type="search" data-term-search-input aria-controls="term-glossary-list" '
            f'placeholder="{glossary_search}" autocomplete="off"></label></div>'
            f'<dl id="term-glossary-list" class="term-glossary-list">{glossary}</dl>'
            f'<p class="term-glossary-empty" data-term-empty hidden>{glossary_empty}</p></section></div>')


def glossary_label_html(entry, lang):
    """Display the full term and its registered abbreviation together."""
    label = htmllib.escape(entry[lang])
    abbreviation = localized_abbreviation(entry, lang)
    if abbreviation:
        label += (f' <span class="term-abbreviation">'
                  f'({htmllib.escape(abbreviation)})</span>')
    return label


def sort_reader_terms(terms, reading_data, src):
    """Order terms by their first marked introduction in the reading order."""
    chapter_order = {node["id"]: node["order"] for node in reading_data["nodes"]}
    positions = {}
    for entry in terms:
        path = os.path.join(src, entry["introduced_in"].replace(".", os.sep) + ".lagda.md")
        try:
            text = open(path, encoding="utf-8").read()
        except OSError:
            text = ""
        match = next((m for m in TERM_MARK_RE.finditer(text)
                      if m.group(2) == "intro" and m.group(3) == entry["id"]), None)
        positions[entry["id"]] = (chapter_order.get(entry["introduced_in"], 10**9),
                                   match.start() if match else 10**9)
    return sorted(terms, key=lambda entry: positions[entry["id"]])


def ext_banner(lang):
    """Prominent header marking a page as external to Bedrock (links home)."""
    s = UI[lang]
    return (f'<div class="ext-banner">⚠ {htmllib.escape(s["external"])} '
            f'<a href="index.html">{htmllib.escape(s["back"])}</a></div>')


def footer_html(lang, base, md_href):
    """The footer also publishes the page's machine-readable forms.

    The Vercel agent-readability measurements found that agents reach a resource by
    following a link from a page they already have, far more often than by guessing a
    path, so the Markdown twin and llms.txt are linked and not merely declared in the
    head."""
    s = UI[lang]
    source = f'<a href="{SOURCE_URL}">{s["source"]}</a>'
    formats = [f'<a href="{base}/llms.txt" title="{htmllib.escape(s["agentstitle"])}">'
               f'{s["agents"]}</a>']
    if md_href:
        formats.insert(0, f'<a href="{md_href}" title="{htmllib.escape(s["mdtitle"])}" '
                          f'type="text/markdown">{s["markdown"]}</a>')
    links = " · ".join([source, *formats])
    copyright_ = f'© 2026 Bedrock Institute · {s["license"]} · {links}'
    return (f'<div class="footer-credit">{s["credit"]}</div>'
            f'<div class="footer-copyright">{copyright_}</div>')


def prelude_reexport_index(content):
    """Index names explicitly re-exported by ``Base.Prelude``.

    Agda quite correctly links an imported occurrence to the library declaration.
    The textbook needs one extra hop: later chapters first lead readers to the
    explanatory import in Base.Prelude, while that import keeps Agda's original
    library link.  The index is derived from highlighted ``public using`` blocks,
    so adding a name to the foundational vocabulary automatically adds the hop.
    """
    by_href, by_name = {}, {}
    public_using = re.compile(
        r'<a id="\d+" class="Keyword">public</a>.*?'
        r'<a id="\d+" class="Keyword">using</a>(?P<body>[^\n]*)',
        re.DOTALL,
    )
    for block in PRE_RE.findall(content):
        for match in public_using.finditer(block):
            for attrs, shown in A_TAG_RE.findall(match.group("body")):
                href = HREF_RE.search(attrs)
                pos = ID_RE.search(attrs)
                if not href or not pos:
                    continue
                cls = CLASS_RE.search(attrs)
                entry = (PRELUDE_MODULE, pos.group(1), cls.group(1) if cls else "",
                         htmllib.unescape(shown))
                by_href.setdefault(href.group(1), entry)
                by_name.setdefault(entry[3], entry)
    return {"by_href": by_href, "by_name": by_name}


def type_reference_attribute(module, position, types_global):
    """Source and hover surfaces advertise only an available type payload."""
    payload = types_global.get(module, {}).get(position)
    if not payload:
        return ""
    # This is a compiler type judgement, not a naming convention (i, j, α and
    # ℓ may all be levels). LevelUniv is the *sort of Level*, not a level value.
    plain = htmllib.unescape(re.sub(r'<[^>]+>', '', payload)).strip()
    level = bool(re.fullmatch(r'\(?\s*(?:(?:Agda\.Primitive|Cubical\.Core\.Primitives)\.)?Level\s*\)?', plain))
    return f' data-type="{module}#{position}"' + (' data-universe-level="true"' if level else '')


def resolve_type_hover_links(type_html, types_global):
    # Type rendering precedes completion of the global type map. Resolve its
    # provisional references only after all local and traced types are present.
    return re.sub(r' data-type="([^"#]+)#([^"#]+)"',
                  lambda match: type_reference_attribute(
                      match.group(1), match.group(2), types_global),
                  re.sub(r' data-universe-level="[^"]*"', '', type_html))


def compiler_reference_scope(content):
    """Only unambiguous definition targets actually resolved by Agda in this module."""
    candidates = {}
    for attrs, label in A_TAG_RE.findall(content):
        href, aspect = HREF_RE.search(attrs), CLASS_RE.search(attrs)
        if not href or not aspect or not _BARE_REFERENCE_ASPECTS.intersection(aspect[1].split()):
            continue
        if '.html#' not in href[1]:
            continue
        candidates.setdefault(htmllib.unescape(label), set()).add((href[1], aspect[1]))
    return {name: next(iter(values)) for name, values in candidates.items() if len(values) == 1}


def add_instantiated_type_aliases(internal_q, types_raw, scopes):
    """Agda prints instance-qualified names absent from declaration anchors.

    Resolve V.Model.Model.isZFModel through V.Model's compiler-resolved links,
    before qualifiers are abbreviated. Never guess from a global short name.
    """
    for definitions in types_raw.values():
        for term in definitions.values():
            for match in re.finditer(r"(?:[A-Za-z][\w']*\.)+[^\s(){}:;,]+", term):
                name = match[0]
                if name in internal_q:
                    continue
                parts = name.split('.')
                owner = next(('.'.join(parts[:i]) for i in range(len(parts) - 1, 0, -1)
                              if '.'.join(parts[:i]) in scopes), None)
                target = scopes.get(owner, {}).get(parts[-1])
                if target:
                    module, _, position = target[0].rpartition('.html#')
                    internal_q[name] = (module, position)


def rewrite_links(body, rendered, types_global, canonical_names=None,
                  current_module="", prelude_reexports=None):
    """Keep links to any rendered module (internal or external), tagging data-type when the
    TARGET has a type (drives hover, including on cubical identifiers). Links to a module we
    did not render lose their dead href (the <a> element stays so the </a> still matches).

    `types_global` is {module: {pos: type-html}} across ALL rendered modules."""
    def repl(m):
        idpart, mod, anchor, rest = m.group(1) or "", m.group(2), m.group(3) or "", m.group(4)
        if "://" in mod:
            return m.group(0)
        rest = re.sub(r' data-(?:type|universe-level)="[^"]*"', '', rest)
        original_href = f"{mod}.html{anchor}"
        bridge = ((prelude_reexports or {}).get("by_href", {}).get(original_href)
                  if current_module != PRELUDE_MODULE else None)
        if bridge:
            bridge_module, bridge_pos, _, bridge_name = bridge
            extra = f' data-name="{htmllib.escape(bridge_name, quote=True)}"'
            extra += type_reference_attribute(bridge_module, bridge_pos, types_global)
            return (f'<a {idpart}href="{chapter_href(bridge_module, "#" + bridge_pos)}"'
                    f'{rest}{extra}>')
        if mod in rendered:
            pos = anchor[1:] if anchor else ""
            extra = type_reference_attribute(mod, pos, types_global)
            canonical = (canonical_names or {}).get(mod, {}).get(pos, "")
            if canonical:
                extra += f' data-name="{htmllib.escape(canonical, quote=True)}"'
            return f'<a {idpart}href="{chapter_href(mod, anchor)}"{rest}{extra}>'
        return f'<a{rest}>'                          # not rendered: drop the dead href
    return LINK_RE.sub(repl, body)


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


NON_HOVER_PRIMITIVE_SORTS = {
    "Prop", "Set", "SSet", "Propω", "Setω", "SSetω", "LevelUniv",
}


def build_types(modules, name2pos, types_raw, internal_q, pos_aspect,
                prelude_reexports=None):
    """Global {module: {pos: abbreviated/hyperlinked type-html}} for hover + sidecars."""
    g = {}
    name_pattern = qualified_name_pattern(internal_q)
    for m in modules:
        g[m] = {}
        for name, pos in name2pos.get(m, {}).items():
            if (pos_aspect.get(m, {}).get(pos) == "Primitive"
                    and name in NON_HOVER_PRIMITIVE_SORTS):
                continue
            t = (types_raw.get(m, {}).get(name)
                 or types_raw.get(m, {}).get(name.split(".")[-1]))
            if t:
                g[m][pos] = render_type(t, internal_q, name_pattern,
                                        pos_aspect, m, prelude_reexports)
    return g


def add_prelude_reexport_types(types_by_module, types_raw, reexports,
                               internal_q, pos_aspect):
    """Give Prelude's explanatory import anchors the imported names' types."""
    prelude = types_by_module.setdefault(PRELUDE_MODULE, {})
    name_pattern = qualified_name_pattern(internal_q)
    for original_href, (_, position, _, shown) in reexports["by_href"].items():
        if shown == "Type":
            # Agda's extractor reports the sort occupied by the imported
            # primitive itself (Set₁).  The reader-facing Type is the
            # level-indexed universe former used throughout this book.
            prelude[position] = render_type(
                "(ℓ : Base.Prelude.Level) → Base.Prelude.Type ℓ",
                internal_q, name_pattern, pos_aspect, PRELUDE_MODULE, reexports,
            )
            continue
        if position in prelude:
            continue
        raw_type = types_raw.get(PRELUDE_MODULE, {}).get(shown)
        if raw_type:
            prelude[position] = render_type(raw_type, internal_q, name_pattern,
                                            pos_aspect, PRELUDE_MODULE, reexports)
            continue
        module, _, original_position = original_href.rpartition(".html#")
        original_type = types_by_module.get(module, {}).get(original_position)
        if original_type:
            prelude[position] = original_type


def local_signature_types(code_html, module):
    """Names and checked signatures at declaration sites without named anchors."""
    result = {}
    declaration_aspects = {
        "Function", "Record", "Datatype", "Postulate", "Primitive", "Field",
        "InductiveConstructor",
    }
    for match in LOCAL_SIGNATURE_RE.finditer(code_html):
        if match.group("module") != module:
            continue
        if not declaration_aspects.intersection(match.group("aspect").split()):
            continue
        # Sidecars are inserted into the live page, so source-position ids from
        # the highlighted declaration must not be duplicated in the popup.
        type_html = re.sub(r'\s+id="\d+"', "", match.group("type")).strip()
        result[match.group("pos")] = {
            "name": htmllib.unescape(match.group("name")),
            "type": type_html,
        }
    # Agda permits several declarations to share one signature (``A P : V``)
    # and may place the colon on the following line.  The narrow expression
    # above intentionally handles the common case; this line-oriented pass
    # supplies every declaration preceding the shared colon.
    pending = ""
    for line in code_html.splitlines():
        colon = TYPE_COLON_RE.search(line)
        if colon:
            prefix = line[:colon.start()]
            declarations = list(LOCAL_DECL_RE.finditer(prefix))
            if not declarations and pending:
                declarations = list(LOCAL_DECL_RE.finditer(pending + prefix))
            type_html = re.sub(r'\s+id="\d+"', "", line[colon.end():]).strip()
            for declaration in declarations:
                aspects = declaration.group("aspect").split()
                if (declaration.group("module") == module
                        and declaration_aspects.intersection(aspects)
                        and type_html):
                    result.setdefault(declaration.group("pos"), {
                        "name": htmllib.unescape(declaration.group("name")),
                        "type": type_html,
                    })
            pending = ""
        elif ("class=\"Symbol\">=</a>" not in line
              and LOCAL_DECL_RE.search(line)):
            pending = line
        else:
            pending = ""
    return result


def build_expression_types(raw, internal_q, pos_aspect, prelude_reexports=None):
    """Render application and local-definition types with their source ranges."""
    result = {}
    name_pattern = qualified_name_pattern(internal_q)
    type_cache = {}
    for module, nodes in raw.items():
        rendered = []
        for node in nodes:
            if not node.get("type"):
                continue
            type_ = node["type"]
            cache_key = (module, type_)
            if cache_key not in type_cache:
                type_cache[cache_key] = render_type(
                    type_, internal_q, name_pattern, pos_aspect, module,
                    prelude_reexports
                )
            rendered.append({**node, "type": type_cache[cache_key]})
        result[module] = rendered
    return result


def names_by_position(module, name2pos):
    """Invert Agda's definition anchors for canonical hover labels."""
    return {str(position): name
            for name, position in name2pos.get(module, {}).items()}


SPAN_EVENT_RE = re.compile(r'<span\b[^>]*>|</span>|\n[ \t]*')


def split_multiline_expression_nodes(block):
    """Split visual expression spans at newlines without splitting the AST node.

    A single inline span continued across a preformatted newline paints the
    continuation indentation as part of the expression.  Close and reopen the
    active span stack around each newline instead.  Reopened expression spans
    retain their ``data-expr-id``, so the browser can treat all line fragments
    as one logical source node while leaving indentation unpainted.
    """
    output = []
    stack = []
    cursor = 0
    for match in SPAN_EVENT_RE.finditer(block):
        output.append(block[cursor:match.start()])
        token = match.group(0)
        if token.startswith("<span"):
            stack.append(token)
            output.append(token)
        elif token == "</span>":
            if stack:
                stack.pop()
            output.append(token)
        elif stack and any('class="expr-node"' in opening for opening in stack):
            output.append("</span>" * len(stack))
            output.append(token)
            output.extend(stack)
        else:
            output.append(token)
        cursor = match.end()
    output.append(block[cursor:])
    return "".join(output)


def annotate_expression_nodes(block, nodes):
    """Wrap source-range application nodes around Agda's highlighted token anchors."""
    boundaries = {node[position] for node in nodes for position in ("start", "end")}

    def split_token(match):
        start = int(match.group(1))
        inner = match.group(2)
        label = htmllib.unescape(inner)
        cuts = sorted(boundary - start for boundary in boundaries
                      if start < boundary < start + len(label))
        if not cuts:
            return match.group(0)
        opening = match.group(0)[:match.group(0).find(">") + 1]
        pieces = []
        offsets = [0, *cuts, len(label)]
        for left, right in zip(offsets, offsets[1:]):
            piece_opening = re.sub(
                r'\bid="\d+"', f'id="{start + left}"', opening, count=1
            )
            pieces.append(piece_opening + htmllib.escape(label[left:right], quote=False)
                          + "</a>")
        return "".join(pieces)

    # Agda may highlight adjacent punctuation as one anchor, for example `_))`.
    # Split such an anchor when an AST node ends between the two closing
    # parentheses, so expression spans can remain properly nested HTML.
    block = TOKEN_RE.sub(split_token, block)
    tokens = []
    for match in TOKEN_RE.finditer(block):
        start = int(match.group(1))
        label = htmllib.unescape(re.sub(r"<[^>]+>", "", match.group(2)))
        tokens.append((start, start + len(label), match.start(), match.end()))
    by_start = {start: html_start for start, _, html_start, _ in tokens}
    by_end = {end: html_end for _, end, _, html_end in tokens}

    def source_opening(node, depth):
        return (f'<span class="expr-node" data-expr-id="{node["id"]}" '
                f'data-expr-start="{node["start"]}" '
                f'data-expr-end="{node["end"]}" '
                f'style="--expr-level:{depth % 6}">')

    return wrap_expression_ranges(
        block, nodes, by_start, by_end, source_opening, split_multiline=True
    )


def annotate_unlinked_bound_types(block, module, module_types):
    """Attach occurrence types to Bound tokens for which Agda emitted no href."""
    def annotate(match):
        token = match.group(0)
        position = match.group(1)
        opening_end = token.find(">")
        opening = token[:opening_end]
        if ("href=" in opening or "data-type=" in opening
                or not re.search(r'\bclass="[^"]*\bBound\b', opening)
                or position not in module_types):
            return token
        return (opening + type_reference_attribute(module, position, {module: module_types})
                + token[opening_end:])
    return TOKEN_RE.sub(annotate, block)


def write_type_sidecar(module, langs, out_dir, types_global, name2pos,
                       expression_types):
    """Write the hover payload independently of rendering the module page."""
    sidecar_data = dict(types_global.get(module, {}))
    sidecar_data["$names"] = names_by_position(module, name2pos)
    sidecar_data["$expressions"] = {
        str(node["id"]): {key: node[key]
                          for key in ("type", "source", "start", "end", "kind")}
        for node in expression_types.get(module, [])
        if node.get("kind") not in ("definition", "binding", "variable", "binder")
    }
    for lang in langs:
        localized = {key: annotate_keywords(value, lang) if isinstance(value, str) else value
                     for key, value in sidecar_data.items()}
        localized['$expressions'] = {key: dict(value, type=annotate_keywords(value['type'], lang))
                                      for key, value in sidecar_data['$expressions'].items()}
        sidecar = json.dumps(localized, ensure_ascii=False)
        tdir = os.path.join(out_dir, lang, "types")
        os.makedirs(tdir, exist_ok=True)
        with open(os.path.join(tdir, module + ".json"), "w", encoding="utf-8") as output:
            output.write(sidecar)


def referenced_type_modules(path, rendered):
    """Rendered modules whose sidecars a selected-page preview can fetch."""
    with open(path, encoding="utf-8") as source:
        html = source.read()
    referenced = set(re.findall(r'href="([^"#]+)\.html(?:#[^"]*)?"', html))
    return referenced.intersection(rendered)


def referenced_module_closure(selected, html_dir, rendered):
    """All highlighted pages reachable from a selected preview.

    Definition modals fetch the target HTML page, not only its hover sidecar.
    Follow links transitively so a fast ``--module`` preview has the same
    unbounded modal navigation as a complete site build.
    """
    closure = set(selected)
    pending = list(selected)
    while pending:
        module = pending.pop()
        path, _ = source_file(html_dir, module)
        for dependency in referenced_type_modules(path, rendered) - closure:
            closure.add(dependency)
            pending.append(dependency)
    return closure


def fill_template(tpl, **kw):
    out = tpl
    for k, v in kw.items():
        out = out.replace(f"%%{k}%%", v)
    return out


def render_module(module, html_dir, langs, internal, rendered, modnav_list,
                  name2pos, canonical_names, types_global, expression_types, terms,
                  tpl, out_dir, base, site, prelude_reexports, reading_data):
    path, literate = source_file(html_dir, module)
    raw = open(path, encoding="utf-8").read()

    is_external = module not in internal
    is_landing = module == LANDING
    out_name = "index.html" if is_landing else module + ".html"
    current = "" if (is_external or is_landing) else module  # highlight in the modules nav
    langs_present = group_languages(raw) if literate else set()

    if literate:
        # lift the highlighted code blocks out (language-neutral, shared across languages)
        code_blocks = []
        def lift(m):
            code_blocks.append(m.group(0))
            return f"{NUL}CODE{len(code_blocks)-1}{NUL}"
        text = PRE_RE.sub(lift, raw)
        text = re.sub(r"<!--\s*bedrock-routes\b.*?-->", "", text, flags=re.DOTALL)
        # links agda already resolved in this module's own code (imports included):
        # name -> (href, aspect classes). The href lets prose reference library
        # identifiers; the aspect paints an inline ref like its code tokens.
        local_refs = {}
        for blk in code_blocks:
            for attrs, txt in A_TAG_RE.findall(blk):
                href = HREF_RE.search(attrs)
                if not href:
                    continue
                cls = CLASS_RE.search(attrs)
                local_refs.setdefault(htmllib.unescape(txt),
                                      (href.group(1), cls.group(1) if cls else ""))
        if is_landing:
            # Origin summarizes the whole book rather than one imported scope.
            # Only unique real declarations enter its special prose vocabulary.
            for name, target in prelude_reexports.get('origin_vocabulary', {}).items():
                local_refs.setdefault(name, target)
        application_nodes = [node for node in expression_types.get(module, [])
                             if node.get("kind") not in ("definition", "binding", "variable", "binder")]
        code_blocks = [annotate_expression_nodes(blk, application_nodes)
                       for blk in code_blocks]
        code_blocks = [annotate_unlinked_bound_types(
            blk, module, types_global.get(module, {})
        ) for blk in code_blocks]

    def page_body(lang):
        if not literate:
            # a library page is bare highlighted code: wrap it and resolve its links
            code = rewrite_links('<pre class="Agda">' + raw + '</pre>', rendered,
                                 types_global, canonical_names, module)
            return annotate_keywords(code, lang), [], None
        woven = weave_for_site(text, lang)
        mirror = woven
        store = {}
        def stash(kind, payload):
            key = f"{NUL}{kind}{len(store)}{NUL}"
            store[key] = payload
            return key
        term_by_id = {entry["id"]: entry for entry in terms}
        def term_marker(match):
            label, kind, term_id = match.groups()
            entry = term_by_id.get(term_id)
            if not entry:
                raise ValueError(f"unknown term id {term_id!r} in {module}")
            shown = htmllib.escape(label)
            if kind == "intro":
                return stash("TERM", f'<dfn id="term-{term_id}" class="term-intro" '
                             f'data-term="{term_id}" tabindex="0">{shown}</dfn>')
            href = f'{entry["introduced_in"]}.html#term-{term_id}'
            return stash("TERM", f'<a class="term-ref" data-term="{term_id}" '
                         f'href="{href}">{shown}</a>')
        woven = TERM_MARK_RE.sub(term_marker, woven)
        woven = re.sub(r'\$\$(.+?)\$\$',
                       lambda m: stash("DMATH", '<div class="math display">$$'
                                       + htmllib.escape(m.group(1)) + '$$</div>'),
                       woven, flags=re.DOTALL)
        woven = re.sub(r'\$(.+?)\$',
                       lambda m: stash("IMATH", '<span class="math inline">$'
                                       + htmllib.escape(m.group(1)) + '$</span>'),
                       woven)
        woven = INLINE_AGDA_LINK_RE.sub(lambda m: stash("REF", inline_ref_link(
            m.group(1), m.group(2), m.group(3), name2pos
        )), woven)
        woven = INLINE_AGDA_RE.sub(lambda m: stash("REF", inline_ref(
            m.group(1), internal, name2pos, local_refs, module, prelude_reexports
        )), woven)
        woven = render_summary_inline(woven)
        body, toc = md_to_html(woven)
        body = re.sub(r'<p>\s*(' + NUL + r'CODE\d+' + NUL + r')\s*</p>', r'\1', body)
        body = re.sub(r'<p>\s*(' + NUL + r'DMATH\d+' + NUL + r')\s*</p>', r'\1', body)
        body = anchor_prose_blocks(body)
        for key, val in store.items():
            body = body.replace(key, val)
        # A formal introduction may live in a section title. The HTML body keeps
        # the interactive marker, while the sidebar needs only its plain label.
        toc = restore_toc_labels(toc, store)
        for j, blk in enumerate(code_blocks):
            body = body.replace(f"{NUL}CODE{j}{NUL}", blk)
        body = annotate_inline_code(body, inline_reference_resolver(
            local_refs, module, prelude_reexports))
        body = rewrite_links(body, rendered, types_global, canonical_names, module,
                             prelude_reexports if module in internal else None)
        body = dedent_submodule_code(body)
        body = render_statement_endings(body, lang)
        body = annotate_keywords(body, lang)
        if module in internal:
            body = mirror_boilerplate(body, module, internal)
        body = auto_link_terms(body, lang, module, terms)
        return render_code_scroll_content(body), toc, mirror

    for lang in langs:
        body, toc, mirror = page_body(lang)
        SEARCH_PASSAGES.extend(passages(body, module, chapter_title(module, lang), lang, out_name))
        if not is_external:
            body = chapter_navigation(body, module, modnav_list, lang)
        chapter_body = body

        if not is_external:
            fallback = {
                "en": "Choose a topic, compare routes, or continue from completed prerequisites.",
                "zh": "按主题阅读、并排比较路线，或从已完成的先修继续。",
                "ja": "主題を選び、ルートを比較し、修了した前提から進めます。",
            }
            if not is_landing:
                fallback = {
                    "en": "Read this chapter directly, or use the interactive contents and dependency graph to choose another route.",
                    "zh": "可以直接阅读本章，也可以通过交互式目录和依赖图选择其他路线。",
                    "ja": "この章を読むか、対話型目次と依存グラフで別のルートを選べます。",
                }
            route_current = "" if is_landing else module
            mount = (f'<section id="reading-explorer" data-current="{route_current}" '
                     f'data-lang="{lang}" data-source="reading-routes.json" '
                     f'aria-label="{UI[lang]["routes"]}">'
                     f'<p>{fallback.get(lang, fallback["en"])}</p>'
                     f'<a href="index.html#reading-explorer">{UI[lang]["guide"]}</a>'
                     f' · <a href="index.html#dependency-map">{UI[lang]["depmap"]}</a></section>')
            if is_landing:
                body = learning_home(render_review_status(body, module, lang), mount, lang, terms)
                heading_end = chapter_body.find('</h1>')
                if heading_end >= 0:
                    split = heading_end + len('</h1>')
                    chapter_body = chapter_body[:split] + mount + chapter_body[split:]
                else:
                    chapter_body = mount + chapter_body
            else:
                heading_end = body.find('</h1>')
                if heading_end >= 0:
                    split = heading_end + len('</h1>')
                    body = body[:split] + mount + body[split:]
                else:
                    body = mount + body

        if not is_external and not is_landing:
            body = render_review_status(body, module, lang)
            chapter_body = render_review_status(chapter_body, module, lang)

        banner = ""
        if langs_present and lang not in langs_present:
            banner = f'<div class="banner">{UI[lang]["untranslated"]}</div>'

        title = UI[lang]["guide"] if is_landing else chapter_title(module, lang)
        has_mirror = mirror is not None

        def shell(page_name, page_title, page_body_html, page_toc, body_class, module_slot):
            """One rendered page, with everything a machine reads about it filled in."""
            md_name = twin_of(page_name) if has_mirror else ""
            return fill_template(
                tpl, LANG=lang, TITLE=htmllib.escape(page_title), SITE=site,
                DESC=htmllib.escape(page_description(module, lang, is_landing, is_external),
                                    quote=True),
                BASEURL=base, MODULE=module_slot,
                CANONICAL=f'  <link rel="canonical" href="{SITE_URL}/{lang}/{page_name}" />',
                ALTMD=(f'  <link rel="alternate" type="text/markdown" href="{md_name}" />'
                       if has_mirror else ""),
                JSONLD=json_ld(module, lang, page_name, langs, is_landing, is_external,
                               has_mirror),
                CONFIG=page_config(module, lang, page_name, md_name, base, site,
                                   is_landing, is_external),
                BODYCLASS=body_class,
                EXTBANNER=ext_banner(lang) if is_external else "",
                HREFLANG=hreflang_links(page_name, langs, base),
                LANGNAV=lang_nav(page_name, lang, langs),
                MODNAV=modules_nav(current if page_name == out_name else module,
                                   modnav_list, lang, reading_data),
                TOC=page_toc, BANNER=banner, BODY=page_body_html,
                FOOTER=footer_html(lang, base, md_name),
                S_SEARCH=UI[lang]["search"], S_THEME=UI[lang]["theme"],
                S_MENU=UI[lang]["menu"], S_CLOSE=UI[lang]["close"],
                S_CONTENT=UI[lang]["contents"])

        page = shell(out_name, title, body,
                     "" if is_landing else toc_html(toc, lang),
                     "text-page external" if is_external else
                     "text-page learning-home" if is_landing else "text-page",
                     "guide" if is_landing else module)
        dest = os.path.join(out_dir, lang, out_name)
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        open(dest, "w", encoding="utf-8").write(page)

        if has_mirror:
            twin = markdown_mirror(mirror, code_blocks, module, lang, out_name, langs)
            md_path = os.path.join(out_dir, lang, twin_of(out_name))
            open(md_path, "w", encoding="utf-8").write(twin)

    # Per-module hover payload. Selected-page builds also refresh dependency
    # sidecars below without paying the cost of rendering their full pages.
    write_type_sidecar(module, langs, out_dir, types_global, name2pos, expression_types)


def inline_ref_link(label, module, name, name2pos):
    """Render an Agda-styled label for a specified internal declaration."""
    position = name2pos.get(module, {}).get(name)
    if position is None:
        raise ValueError(f"unknown Agda reference {module}.{name}")
    href = f"{module}.html#{position}"
    return ('<span class="Agda">'
            + ref_link(href, "", htmllib.escape(label), "inline-ref") + '</span>')


_BARE_REFERENCE_ASPECTS = {
    "Function", "Datatype", "Record", "Primitive", "PrimitiveType", "Field",
    "Module", "Macro", "Postulate", "InductiveConstructor", "CoinductiveConstructor",
}


def linked_inline_ref(href, aspect, label, defined):
    """Only a standalone link to a declaration may appear without a code box."""
    if defined:
        return ('<span class="Agda">'
                + ref_link(href, aspect, label, "inline-ref") + '</span>')
    return ('<span class="Agda inline-ref inline-code">'
            + ref_link(href, aspect, label) + '</span>')


def syntax_notations(content):
    """Read notation parts from compiler-classified syntax declarations."""
    declarations = []
    for line in content.splitlines():
        if not re.search(r'class="Keyword">syntax</a>', line):
            continue
        target = re.search(r'href="([^"]+)"[^>]*>([^<]+)</a>', line)
        if not target:
            continue
        rhs = re.split(r'<a\b[^>]*class="Symbol">=</a>', line)[-1]
        parts = [htmllib.unescape(text) for aspect, text in
                 re.findall(r'<a\b[^>]*class="([^"]+)"[^>]*>([^<]+)</a>', rhs)
                 if _BARE_REFERENCE_ASPECTS.intersection(aspect.split())]
        if parts:
            declarations.append((htmllib.unescape(target[1]), parts))
    return declarations


def inline_reference_resolver(local_refs, current_module, prelude_reexports=None):
    """Use real Prelude exports and compiler links, including mixfix spellings."""
    prelude = prelude_reexports or {}
    references = dict(prelude.get('inline', {}))
    if 'inline' not in prelude:
        for name, (module, position, aspect, _) in prelude.get('by_name', {}).items():
            references.setdefault(name, (f'{module}.html#{position}', aspect))
    for name, (href, aspect) in local_refs.items():
        if name in references:
            # Prelude is the vocabulary authority, including renamed imports.
            # A real chapter-local declaration may shadow it, a borrowed token
            # (or a coincidentally named local binder) may not.
            if current_module == PRELUDE_MODULE or not href.startswith(current_module + '.html#'):
                continue
        if not _BARE_REFERENCE_ASPECTS.intersection(aspect.split()):
            continue
        bridge = prelude.get('by_href', {}).get(href)
        references[name] = ((f'{bridge[0]}.html#{bridge[1]}', bridge[2])
                            if bridge else (href, aspect))
    aliases, openings = {}, {}
    for name in references:
        parts = [part for part in name.split('_') if part]
        if len(parts) == 1 and parts[0] == name:
            continue
        if len(parts) == 1:
            aliases.setdefault(parts[0], set()).add(references[name])
        elif parts:
            openings.setdefault(parts[0], []).append((name, parts))
    for name, parts in prelude.get('syntax', []):
        if name in references and parts:
            openings.setdefault(parts[0], []).append((name, parts))

    cached_tokens, matched = None, {}

    def match_parts(tokens):
        """Pair actual mixfix parts, respecting nesting and alternative endings."""
        stack, matches = [], {}
        for index, (_, _, token, syntax) in enumerate(tokens):
            if stack:
                candidates, positions = stack[-1]
                narrowed = [(name, parts) for name, parts in candidates
                            if len(parts) > len(positions) and parts[len(positions)] == token]
                if narrowed:
                    positions = positions + [index]
                    complete = [(name, parts) for name, parts in narrowed if len(parts) == len(positions)]
                    if complete:
                        options = {references[name] for name, _ in complete}
                        if len(options) == 1:
                            for position in positions:
                                matches[position] = next(iter(options))
                        stack.pop()
                    else:
                        stack[-1] = (narrowed, positions)
                    continue
            if token in openings:
                stack.append((openings[token], [index]))
            elif syntax and token in ('=', ';'):
                stack.clear()
        return matches

    def resolve(token, tokens, index):
        nonlocal cached_tokens, matched
        if tokens is not cached_tokens:
            cached_tokens, matched = tokens, match_parts(tokens)
        info = matched.get(index) or references.get(token)
        if info is None and token.startswith(PRELUDE_MODULE + '.'):
            info = references.get(token[len(PRELUDE_MODULE) + 1:])
        if info is None:
            unique = set(aliases.get(token, ()))
            if len(unique) == 1:
                info = unique.pop()
        return ref_link(info[0], info[1], htmllib.escape(token)) if info else None
    return resolve


def inline_ref(name, internal, name2pos, local_refs, current_module="",
               prelude_reexports=None):
    """Render Agda prose, linking declarations but not temporary variables."""
    href_aspect = local_refs.get(name)
    label = htmllib.escape(name)
    if any(inline_syntax_ranges(name)) and name in HELP:
        return annotate_inline_code(f'<code class="Agda inline-ref">{label}</code>')
    if href_aspect and not _BARE_REFERENCE_ASPECTS.intersection(href_aspect[1].split()):
        return f'<code class="Agda inline-ref">{label}</code>'
    exported = (prelude_reexports or {}).get('inline', {}).get(name)
    if exported and (current_module == PRELUDE_MODULE or not href_aspect
                     or not href_aspect[0].startswith(current_module + '.html#')):
        return linked_inline_ref(*exported, label, True)
    bridge = None
    if prelude_reexports:
        if href_aspect:
            bridge = (prelude_reexports or {}).get("by_href", {}).get(href_aspect[0])
        else:
            local_name = name.rpartition(".")[2]
            bridge = (prelude_reexports or {}).get("by_name", {}).get(local_name)
    if bridge:
        mod, pos, bridge_aspect, _ = bridge
        aspect = href_aspect[1] if href_aspect else bridge_aspect
        defined = not aspect or bool(_BARE_REFERENCE_ASPECTS.intersection(aspect.split()))
        return linked_inline_ref(f"{mod}.html#{pos}", aspect, label, defined)
    target = None
    if "." in name:
        mod, _, local = name.rpartition(".")
        if mod in internal and local in name2pos.get(mod, {}):
            target = (mod, name2pos[mod][local])
    if target is None and name in name2pos.get(current_module, {}):
        target = (current_module, name2pos[current_module][name])
    if target:
        mod, pos = target
        # reuse the aspect of the module's own code tokens, and wrap in a
        # span.Agda so the .Agda .<Aspect> colour rules apply to prose refs too
        aspect = href_aspect[1] if href_aspect else ""
        defined = not aspect or bool(_BARE_REFERENCE_ASPECTS.intersection(aspect.split()))
        return linked_inline_ref(f"{mod}.html#{pos}", aspect, label, defined)
    if href_aspect:
        # a link agda already resolved in this module's own code; this is how
        # prose references library identifiers (Type, refl, ...) and modules
        aspect = href_aspect[1]
        defined = bool(_BARE_REFERENCE_ASPECTS.intersection(aspect.split()))
        return linked_inline_ref(href_aspect[0], aspect, label, defined)
    return annotate_inline_code(f'<code class="Agda inline-ref">{label}</code>',
                                inline_reference_resolver(local_refs, current_module, prelude_reexports))


# ---- agent-readable layer ----------------------------------------------------
# A passage on this site has to be addressable. A reader who selects a sentence and
# asks an assistant about it, and an agent that follows the resulting link, both need
# a stable name for the block they are looking at; a heading anchor alone is too
# coarse for a chapter whose sections run to a dozen paragraphs. So every prose block
# gets an id, every page gets a plain-Markdown twin, and the site gets one index that
# tells an agent what is fetchable. See site/README.md.

BLOCK_RE = re.compile(r'<(/?)(p|li|blockquote|table)\b')


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


def plain_code(block):
    """Recover the Agda source from one highlighted `<pre class="Agda">` block."""
    inner = re.sub(r'^<pre class="Agda">', "", block.strip())
    inner = re.sub(r"</pre>$", "", inner)
    return htmllib.unescape(re.sub(r"<[^>]+>", "", inner)).strip("\n")


def markdown_mirror(woven, code_blocks, module, lang, out_name, langs):
    """The same chapter as plain Markdown: front matter, prose, fenced Agda.

    An agent that follows a link from this site pays for the page it fetches. The HTML
    carries a navigation sidebar, a type sidecar hook and a highlighted token per
    identifier; the Markdown carries the chapter. Both are generated from one master,
    so the mirror cannot drift from the page it mirrors.
    """
    meta = CHAPTER_META.get(module, {})
    text = TERM_MARK_RE.sub(lambda m: m.group(1), woven)
    text = INLINE_AGDA_LINK_RE.sub(
        lambda m: f"[{m.group(1)}]({m.group(2)}.html#{m.group(3)})", text)
    text = INLINE_AGDA_RE.sub(lambda m: "`" + m.group(1) + "`", text)
    for index, block in enumerate(code_blocks):
        text = text.replace(f"{NUL}CODE{index}{NUL}",
                            "\n\n```agda\n" + plain_code(block) + "\n```\n\n")
    text = re.sub(r"\n{3,}", "\n\n", text)

    def quote(value):
        return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'

    front = [
        "---",
        f"title: {quote(chapter_title(module, lang))}",
        f"module: {module}",
        f"lang: {lang}",
        f"site: {quote('Bedrock')}",
        f"description: {quote(chapter_field(module, 'description', lang))}",
        f"stage: {quote(chapter_field(module, 'stage', lang))}",
        f"reading_order: {meta.get('order', 0)}",
        f"canonical: {SITE_URL}/{lang}/{out_name}",
        f"html: {chapter_href(module)}",
        f"agda_source: {SOURCE_TREE}/{module.replace('.', '/')}.lagda.md",
        "prerequisites: [" + ", ".join(meta.get("prerequisites", [])) + "]",
        "routes: [" + ", ".join(meta.get("routes", [])) + "]",
        "translations: [" + ", ".join(
            f"{SITE_URL}/{other}/{twin_of(out_name)}"
            for other in langs if other != lang) + "]",
        "agent_guide: /llms.txt",
        "license: CC-BY-NC-SA-4.0",
        "---",
        "",
    ]
    return "\n".join(front) + text.rstrip("\n") + "\n"


def json_ld(module, lang, out_name, langs, is_landing, is_external, has_mirror):
    """One schema.org graph per page: this chapter, and the book it is a chapter of."""
    url = f"{SITE_URL}/{lang}/{out_name}"
    book = {
        "@type": "Book",
        "@id": f"{SITE_URL}/#book",
        "name": "Bedrock",
        "url": SITE_URL + "/",
        "inLanguage": list(langs),
        "description": SITE_BLURB.get(lang, SITE_BLURB["en"]),
        "about": ["Set theory", "Constructible universe", "Generalized continuum hypothesis",
                  "Cubical type theory", "Formalized mathematics"],
        "license": "https://creativecommons.org/licenses/by-nc-sa/4.0/",
        "author": {"@type": "Organization", "name": "Bedrock Institute", "url": SOURCE_URL},
        "isAccessibleForFree": True,
    }
    page = {
        "@type": "TechArticle",
        "@id": url,
        "url": url,
        "name": chapter_title(module, lang) if not is_landing else "Bedrock",
        "headline": chapter_title(module, lang),
        "description": page_description(module, lang, is_landing, is_external),
        "inLanguage": lang,
        "isPartOf": {"@id": f"{SITE_URL}/#book"},
        "license": "https://creativecommons.org/licenses/by-nc-sa/4.0/",
        "programmingLanguage": {"@type": "ComputerLanguage", "name": "Cubical Agda",
                                "url": "https://github.com/agda/cubical"},
        "isAccessibleForFree": True,
    }
    if not is_external:
        page["identifier"] = module
        position = CHAPTER_META.get(module, {}).get("order")
        if position:
            page["position"] = position
        page["codeRepository"] = f"{SOURCE_TREE}/{module.replace('.', '/')}.lagda.md"
    if has_mirror:
        # the twin of this page, which for a preview chapter is the guide's twin
        page["encoding"] = {"@type": "MediaObject", "encodingFormat": "text/markdown",
                            "contentUrl": f"{SITE_URL}/{lang}/{twin_of(out_name)}"}
    graph = {"@context": "https://schema.org", "@graph": [page, book]}
    payload = json.dumps(graph, ensure_ascii=False, separators=(",", ":"))
    return ('  <script type="application/ld+json">'
            + payload.replace("<", "\\u003c") + "</script>")


AGENT_GUIDE_HEAD = """# Bedrock

> {blurb}

Bedrock is a machine-checked development, in Cubical Agda, of the set theory behind
contemporary questions about the universe of sets. Two results are proved and both are
stated in the chapter `Origin`: `L⊨ZFC` and `L⊨GCH`, the constructible universe
as a model of ZFC and as a model in which the generalized continuum hypothesis holds.
Each rests on one hypothesis, excluded middle at `LEM (ℓ-suc ℓ)`, and on nothing else.
The long-term aim is forcing, set-theoretic geology, the definability of ground models
and the mantle.

The project is host-language maximalist: every set-theoretic notion is rebuilt in
type-theory-native idiom rather than transcribed from the textbook ZF axioms, and the
deeply embedded first-order `Formula` is used only where syntax is itself the object of
study. Every file typechecks under Agda 2.8.0 with the cubical 0.9 library and the
`--safe` flag, so nothing here is postulated.

This site is the development published as a trilingual mathematics textbook. One chapter
is one Agda module. The displayed Agda is the formal content; the prose around it is the
exposition, written in English, Chinese and Japanese from a single master. The reading
order is a dependency order: a chapter's prerequisites are the modules it imports.

## How to read this site

- Every chapter is at `/<lang>/<Module>.html`, with `<lang>` one of `en`, `zh`, `ja`.
  The three editions share filenames, so swapping the language segment of any URL
  reaches the same chapter in another language. The one exception is the preview
  chapter `Origin`, which has no page of its own: the reading guide embeds its
  whole body, so it is read at `/<lang>/index.html#milestones`. The chapter list below
  gives every chapter's address, and `/<lang>/reading-routes.json` gives it as data.
- **Every chapter page has a plain-Markdown twin at the same path with a `.md`
  extension.** It carries the same prose and the same Agda in fenced blocks, with the
  chapter's stage, prerequisites and source in YAML front matter, and it is a fraction
  of the size of the HTML. Prefer it. Each HTML page advertises its own mirror with
  `<link rel="alternate" type="text/markdown">`.
- Pages are static HTML and need no JavaScript: the prose and the Agda are both in the
  initial response.
- Anchors are stable and are the way to cite a passage. `#sec-0` is a chapter's title
  and `#sec-1`, `#sec-2`, ... its headings in document order. `#p-1`, `#p-2`, ... name
  its prose blocks, paragraphs and list items alike, in document order, so `#p-7` is
  the seventh block of prose on the page whatever section it falls in. Inside a
  displayed Agda block every
  token carries the character offset Agda's highlighter assigned it, as `#1234`, and
  every definition additionally carries its own Agda identifier as a named anchor, so
  `/<lang>/V.Model.html#V⊨ZF` opens the page at that definition.
- `/<lang>/index.html` is the reading guide: routes, the dependency map, the milestone
  theorems and the glossary.

## Machine-readable endpoints

Every one of these is static JSON, served with `Access-Control-Allow-Origin: *`.

"""


def page_config(module, lang, page_name, md_name, base, site, is_landing, is_external):
    """`window.bedrock`: what the page's own scripts are allowed to assume about it.

    The ask-an-assistant handover is assembled in the browser from these fields, so
    whatever it says about a chapter (its title, its stage, its place in the reading
    order, where its Agda master lives) is the same thing llms.txt and the Markdown
    twin say. Nothing here is derived from the DOM."""
    meta = CHAPTER_META.get(module, {})
    config = {
        "baseUrl": base,
        "lang": lang,
        "module": "guide" if is_landing else module,
        "site": site,
        "canonical": f"{SITE_URL}/{lang}/{page_name}",
        "chapter": module,
        "title": chapter_title(module, lang),
        "stage": chapter_field(module, "stage", lang),
        "order": meta.get("order", 0),
        "chapters": len(CHAPTER_META),
        "prerequisites": meta.get("prerequisites", []),
        "markdown": md_name,
        "guide": f"{base}/llms.txt",
        "repository": SOURCE_URL,
        "external": is_external,
    }
    if not is_external:
        config["agdaSource"] = f"{SOURCE_TREE}/{module.replace('.', '/')}.lagda.md"
    payload = json.dumps(config, ensure_ascii=False, separators=(",", ":"))
    return payload.replace("<", "\\u003c")


def agent_guide(langs, modnav_list):
    """llms.txt: what the site is, how it is addressed, and what an agent can fetch."""
    lang = langs[0]
    lines = [AGENT_GUIDE_HEAD.format(blurb=SITE_BLURB["en"])]
    endpoints = [
        (f"/{lang}/reading-routes.json",
         "the chapter graph: every chapter's localized title, learning stage, "
         "prerequisites, reading-order position, route memberships, and the `page` and "
         "`anchor` it is read at. This file decides those addresses; every link on the "
         "site is built from it."),
        (f"/{lang}/terms.json",
         "the reader-facing glossary: each term's label in this language, a one-sentence "
         "recap, and the chapter that introduces it."),
        (f"/{lang}/search.json",
         "every Agda identifier Bedrock defines, with its module, its anchor on that "
         "module's page, its syntactic aspect and its type."),
        (f"/{lang}/types/<Module>.json",
         "the elaborated type of every token of one chapter, keyed by the anchor that "
         "token carries in that chapter's URL."),
        ("/sitemap.xml", "every page, in every language, with hreflang alternates."),
        ("/robots.txt", "crawl policy. Nothing on this site is disallowed."),
    ]
    for path, what in endpoints:
        lines.append(f"- [{path}]({SITE_URL}{path}): {what}")
    lines.append("")
    lines.append("## Source")
    lines.append("")
    lines.append(f"- [{SOURCE_URL}]({SOURCE_URL}): the repository. A chapter is one literate "
                 "Agda master at `src/<Module path>.lagda.md`, and the site is generated "
                 "from those masters by `scripts/site/render-site.py`.")
    lines.append(f"- [{SOURCE_URL}/blob/main/README.md]({SOURCE_URL}/blob/main/README.md): "
                 "the project README, with the current measured size and build figures.")
    lines.append(f"- [{SOURCE_URL}/blob/main/docs/en/CHARTER.md]"
                 f"({SOURCE_URL}/blob/main/docs/en/CHARTER.md): the charter, the full "
                 "methodological statement behind host-language maximalism.")
    lines.append("")
    lines.append("## Chapters, in reading order")
    lines.append("")
    lines.append("Links point at the Markdown mirrors. Replace `/en/` with `/zh/` or `/ja/` "
                 "for the Chinese or Japanese edition, and `.md` with `.html` for the page a "
                 "human reads. A chapter that is not read at the page its own name gives "
                 "says where it is read.")
    lines.append("")
    for module in modnav_list:
        meta = CHAPTER_META.get(module, {})
        stage = chapter_field(module, "stage", lang)
        title = chapter_title(module, lang)
        desc = chapter_field(module, "description", lang)
        position = meta.get("order", 0)
        page = meta["page"]
        entry = (f"- [{position}. {title}]({SITE_URL}/{lang}/{twin_of(page)}) "
                 f"(`{module}`, {stage})")
        # Nearly every chapter is read at the page its own name gives, and saying so
        # 121 times would be noise. A chapter that is read somewhere else says where.
        if page != own_page(module):
            entry += f", read at {SITE_URL}/{lang}/{chapter_href(module)}"
        if desc.rstrip(".") != title.rstrip("."):
            entry += f": {desc}"
        lines.append(entry)
    lines.append("")
    lines.append("## Other editions")
    lines.append("")
    for other in langs[1:]:
        lines.append(f"- [{LANG_LABELS[other]}]({SITE_URL}/{other}/index.html): the same "
                     f"book. Chapter mirrors are at `/{other}/<Module>.md`.")
    lines.append("")
    return "\n".join(lines)


def write_agent_files(out_dir, langs, base, modnav_list):
    """robots.txt, sitemap.xml, llms.txt and the Cloudflare header rules."""
    guide = agent_guide(langs, modnav_list)
    open(os.path.join(out_dir, "llms.txt"), "w", encoding="utf-8").write(guide)
    well_known = os.path.join(out_dir, ".well-known")
    os.makedirs(well_known, exist_ok=True)
    open(os.path.join(well_known, "llms.txt"), "w", encoding="utf-8").write(guide)

    open(os.path.join(out_dir, "robots.txt"), "w", encoding="utf-8").write(
        "# Bedrock. Everything here is public and nothing is disallowed, to crawlers and\n"
        "# to AI agents alike. /llms.txt is the guide written for an agent; every chapter\n"
        "# page also has a plain-Markdown twin at the same path with a .md extension.\n"
        "User-agent: *\n"
        "Allow: /\n"
        "\n"
        f"Sitemap: {SITE_URL}/sitemap.xml\n")

    # One entry per page that exists, in reading order after the guide. A preview
    # chapter shares the guide's page and is not a second URL for a crawler to weigh
    # against it, so the dedupe is what keeps it out.
    pages = list(dict.fromkeys(
        ["index.html"] + [CHAPTER_META[m]["page"] for m in modnav_list]))
    urls = []
    for lang in langs:
        for page in pages:
            alternates = "".join(
                f'\n    <xhtml:link rel="alternate" hreflang="{other}" '
                f'href="{SITE_URL}/{other}/{page}" />' for other in langs)
            urls.append(f"  <url>\n    <loc>{SITE_URL}/{lang}/{page}</loc>{alternates}\n  </url>")
    open(os.path.join(out_dir, "sitemap.xml"), "w", encoding="utf-8").write(
        '<?xml version="1.0" encoding="UTF-8"?>\n'
        '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9"\n'
        '        xmlns:xhtml="http://www.w3.org/1999/xhtml">\n'
        + "\n".join(urls) + "\n</urlset>\n")

    # Cloudflare Pages reads `_headers` from the deployed root. Without it a .md twin
    # arrives as a download rather than as text an agent can read, and a fetch from
    # another origin cannot reach the JSON endpoints at all.
    open(os.path.join(out_dir, "_headers"), "w", encoding="utf-8").write(
        "/*.md\n"
        "  Content-Type: text/markdown; charset=utf-8\n"
        "  Access-Control-Allow-Origin: *\n"
        "/llms.txt\n"
        "  Content-Type: text/markdown; charset=utf-8\n"
        "  Access-Control-Allow-Origin: *\n"
        "/.well-known/llms.txt\n"
        "  Content-Type: text/markdown; charset=utf-8\n"
        "  Access-Control-Allow-Origin: *\n"
        "/*.json\n"
        "  Access-Control-Allow-Origin: *\n")


# ---- site-level outputs ------------------------------------------------------

def write_search(out_dir, lang, modules, name2pos, pos_aspect, types_by_module):
    entries = []
    for m in modules:
        entries.append({"name": chapter_title(m, lang), "module": m,
                        "kind": "chapter", "type": chapter_field(m, "description", lang),
                        "href": chapter_href(m)})
        for name, pos in name2pos.get(m, {}).items():
            t = types_by_module.get(m, {}).get(pos, "")
            entries.append({"name": name, "module": m, "anchor": pos,
                            "chapter": chapter_title(m, lang), "kind": "definition",
                            "aspect": pos_aspect.get(m, {}).get(pos, ""),
                            "type": re.sub(r"<[^>]+>", "", t),
                            "href": chapter_href(m, f"#{pos}")})
    open(os.path.join(out_dir, lang, "search.json"), "w", encoding="utf-8").write(
        json.dumps(entries, ensure_ascii=False))


def write_terms(out_dir, lang, terms):
    payload = {}
    for entry in terms:
        module = entry["introduced_in"]
        payload[entry["id"]] = {
            "label": entry[lang],
            "recap": entry[f"recap_{lang}"],
            "chapter": chapter_title(module, lang),
            "href": chapter_href(module, f'#term-{entry["id"]}'),
        }
        abbreviation = localized_abbreviation(entry, lang)
        if abbreviation:
            payload[entry["id"]]["abbreviation"] = abbreviation
    with open(os.path.join(out_dir, lang, "terms.json"), "w", encoding="utf-8") as target:
        json.dump(payload, target, ensure_ascii=False)


def write_root(out_dir, langs, base):
    """The site root and the 404 page.

    A browser is sent straight to its own language. A fetch-only client that runs no
    JavaScript, which is what an agent usually is, still gets a page that says what this
    is and links every edition and the agent guide, rather than an empty redirect shell.
    """
    default = langs[0]
    links = "\n".join(
        f'    <li><a lang="{L}" hreflang="{L}" href="{base}/{L}/index.html">'
        f'{LANG_LABELS[L]}</a>: {htmllib.escape(SITE_BLURB[L])}</li>' for L in langs)
    page = f"""<!DOCTYPE html>
<html lang="{default}">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1.0" />
  <title>Bedrock</title>
  <meta name="description" content="{htmllib.escape(SITE_BLURB[default], quote=True)}" />
  <link rel="canonical" href="{SITE_URL}/" />
  <link rel="help" type="text/markdown" href="{base}/llms.txt" title="Site guide for AI agents" />
{hreflang_links("index.html", langs, base)}
  <link rel="icon" href="{base}/static/assets/favicon.svg" />
  <script>
    var ls = {json.dumps(langs)};
    var want = (navigator.language || "en").slice(0, 2);
    var to = ls.indexOf(want) >= 0 ? want : "{default}";
    location.replace("{base}/" + to + "/index.html");
  </script>
  <meta http-equiv="refresh" content="0; url={base}/{default}/index.html" />
</head>
<body>
  <main>
    <h1>Bedrock</h1>
    <p>{htmllib.escape(SITE_BLURB[default])}</p>
    <ul>
{links}
    </ul>
    <p>Reading this as a program? <a href="{base}/llms.txt">/llms.txt</a> is the guide
    written for you: it lists every chapter, every machine-readable endpoint, and the
    plain-Markdown twin each chapter page carries.</p>
  </main>
</body>
</html>
"""
    open(os.path.join(out_dir, "index.html"), "w", encoding="utf-8").write(page)
    open(os.path.join(out_dir, "404.html"), "w", encoding="utf-8").write(page)


def main(argv):
    html_dir, types_path, src = "_build/html", "_build/types.json", "src"
    expression_types_path = "_build/expression-types.json"
    tpl_path, out_dir = "site/template.html", "_build/site"
    static_dir = "site/static"
    langs, base, site = ["en", "zh", "ja"], "", "Bedrock"
    selected_modules = set()
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--html-dir": i += 1; html_dir = argv[i]
        elif a == "--types": i += 1; types_path = argv[i]
        elif a == "--expression-types": i += 1; expression_types_path = argv[i]
        elif a == "--src": i += 1; src = argv[i]
        elif a == "--template": i += 1; tpl_path = argv[i]
        elif a == "--out": i += 1; out_dir = argv[i]
        elif a == "--static": i += 1; static_dir = argv[i]
        elif a == "--langs": i += 1; langs = [x for x in argv[i].split(",") if x]
        elif a == "--base-url": i += 1; base = argv[i].rstrip("/")
        elif a == "--site": i += 1; site = argv[i]
        elif a == "--module":
            i += 1
            selected_modules.update(x for x in argv[i].split(",") if x)
        else: sys.stderr.write(f"unknown option: {a}\n"); return 2
        i += 1

    diagram_errors = check_diagrams(sorted(glob.glob(os.path.join(src, "**", "*.lagda.md"), recursive=True)))
    if diagram_errors:
        sys.stderr.write("\n".join(diagram_errors) + "\n")
        return 1

    internal = set(
        os.path.relpath(p, src)[:-len(".lagda.md")].replace(os.sep, ".")
        for p in glob.glob(os.path.join(src, "**", "*.lagda.md"), recursive=True))

    # the full reachable set = every module agda --html emitted (Bedrock .md + library .html)
    rendered = sorted(set(
        os.path.basename(p).rsplit(".", 1)[0]
        for p in glob.glob(os.path.join(html_dir, "*.md"))
        + glob.glob(os.path.join(html_dir, "*.html"))))
    if LANDING in rendered:
        rendered = sorted(referenced_module_closure({LANDING}, html_dir, set(rendered)))
    rendered_set = set(rendered)
    if not rendered:
        sys.stderr.write(f"no highlighted output in {html_dir}; run `agda --html` first\n")
        return 1
    # Validate author-maintained routes before producing any reader-facing pages.
    reading_data = build_reading_data(src)
    order = {node["id"]: node["order"] for node in reading_data["nodes"]}
    modnav_list = sorted(internal, key=lambda m: (order.get(m, len(order) + 1), m))
    CHAPTER_TITLES.clear()
    SEARCH_PASSAGES.clear()
    CHAPTER_TITLES.update({node["id"]: node["title"] for node in reading_data["nodes"]})
    CHAPTER_META.clear()
    CHAPTER_META.update({
        node["id"]: {"description": node["description"], "stage": node["stage"],
                     "order": node["order"], "prerequisites": node["prerequisites"],
                     "routes": node["routes"], "page": node["page"],
                     "human_reviewed": node["human_reviewed"],
                     "anchor": node["anchor"]}
        for node in reading_data["nodes"]})
    glossary_entries = load_entries()
    term_errors = schema_errors(glossary_entries)
    if term_errors:
        raise ValueError("\n".join(term_errors))
    terms = sort_reader_terms(reader_terms(glossary_entries), reading_data, src)
    types_raw = json.load(open(types_path, encoding="utf-8")) if os.path.exists(types_path) else {}
    expression_types_raw = (json.load(open(expression_types_path, encoding="utf-8"))
                            if os.path.exists(expression_types_path) else {})
    tpl = open(tpl_path, encoding="utf-8").read()
    # cache-bust: stamp ?v=<hash> on the CSS/JS so browsers always pick up changes
    def _ver(name):
        p = os.path.join(static_dir, name)
        try:
            return hashlib.sha1(open(p, "rb").read()).hexdigest()[:8]
        except OSError:
            return "0"
    tpl = tpl.replace("%%CSSVER%%", _ver("bedrock.css")).replace("%%JSVER%%", _ver("bedrock.js"))

    tpl = tpl.replace("%%ROUTECSSVER%%", _ver("reading-routes.css")).replace(
        "%%ROUTEJSVER%%", _ver("reading-routes.js"))
    tpl = tpl.replace("%%ASKCSSVER%%", _ver("ask-ai.css")).replace(
        "%%ASKJSVER%%", _ver("ask-ai.js"))
    tpl = tpl.replace("%%APPEARANCECSSVER%%", _ver("appearance.css")).replace(
        "%%APPEARANCEJSVER%%", _ver("appearance.js"))
    tpl = tpl.replace("%%LEVELJSVER%%", _ver("universe-levels.js"))

    # first pass: index every definition (names, positions, aspects) across ALL rendered modules
    name2pos, pos_aspect, local_types = {}, {}, {}
    notations = []
    compiler_scopes = {}
    prelude_reexports = {"by_href": {}, "by_name": {}}
    for m in rendered:
        path, literate = source_file(html_dir, m)
        content = open(path, encoding="utf-8").read()
        compiler_scopes[m] = compiler_reference_scope(content)
        notations.extend(syntax_notations(content))
        if literate:
            if m == PRELUDE_MODULE:
                prelude_reexports = prelude_reexport_index(content)
            for blk in PRE_RE.findall(content):
                index_definitions(blk, m, name2pos, pos_aspect)
                local_types.setdefault(m, {}).update(local_signature_types(blk, m))
        else:
            index_definitions(content, m, name2pos, pos_aspect)   # whole .html is code
            local_types[m] = local_signature_types(content, m)
    internal_q = {f"{m}.{n}": (m, p) for m in name2pos for n, p in name2pos[m].items()}
    add_instantiated_type_aliases(internal_q, types_raw, compiler_scopes)
    vocabulary = {}
    for m in internal:
        for name, position in name2pos.get(m, {}).items():
            aspect = pos_aspect.get(m, {}).get(position, '')
            if _BARE_REFERENCE_ASPECTS.intersection(aspect.split()):
                vocabulary.setdefault(name, set()).add((f'{m}.html#{position}', aspect))
    prelude_reexports['origin_vocabulary'] = {
        name: next(iter(targets)) for name, targets in vocabulary.items() if len(targets) == 1}
    # Actual exported vocabulary includes locally defined and renamed names.
    # Exclude pre-renaming spellings that are not in Prelude's public scope.
    exported = types_raw.get(PRELUDE_MODULE, {})
    prelude_reexports['inline'] = {
        name: (f'{PRELUDE_MODULE}.html#{position}', aspect)
        for name, (_, position, aspect, _) in prelude_reexports['by_name'].items()
        if name in exported
    }
    for name, position in name2pos.get(PRELUDE_MODULE, {}).items():
        if name in exported:
            prelude_reexports['inline'][name] = (
                f'{PRELUDE_MODULE}.html#{position}', pos_aspect[PRELUDE_MODULE].get(position, ''))
    prelude_reexports['syntax'] = []
    for href, parts in notations:
        bridge = prelude_reexports['by_href'].get(href)
        if bridge and bridge[3] in prelude_reexports['inline']:
            prelude_reexports['syntax'].append((bridge[3], parts))
    add_prelude_qualified_names(internal_q, prelude_reexports)
    types_by_module = build_types(rendered, name2pos, types_raw, internal_q,
                                  pos_aspect, prelude_reexports)
    add_prelude_reexport_types(types_by_module, types_raw, prelude_reexports,
                               internal_q, pos_aspect)
    name_pattern = qualified_name_pattern(internal_q)
    canonical_names = {module: names_by_position(module, name2pos)
                       for module in rendered}
    for name, (href, _) in prelude_reexports['inline'].items():
        canonical_names.setdefault(PRELUDE_MODULE, {})[href.rsplit('#', 1)[1]] = name
    highlighted_local_types = []
    for module, declarations in local_types.items():
        for position, declaration in declarations.items():
            full_type = types_raw.get(module, {}).get(declaration["name"])
            if full_type:
                type_html = render_type(full_type, internal_q, name_pattern,
                                        pos_aspect, module, prelude_reexports)
            else:
                type_html = declaration["type"]
                highlighted_local_types.append((module, position, type_html))
            types_by_module.setdefault(module, {}).setdefault(position, type_html)
    # Every local target is now present, so links between two declarations whose
    # types came only from highlighted HTML can both receive hover payloads.
    for module, position, type_html in highlighted_local_types:
        types_by_module[module][position] = decorate_type_nodes(rewrite_links(
            type_html, rendered_set, types_by_module, canonical_names, module,
            prelude_reexports
        ))
    expression_types = build_expression_types(
        expression_types_raw, internal_q, pos_aspect, prelude_reexports
    )
    for module, nodes in expression_types.items():
        for node in nodes:
            if node.get("kind") == "definition":
                types_by_module.setdefault(module, {}).setdefault(
                    str(node["start"]), node["type"]
                )
            elif node.get("kind") in ("binding", "variable", "binder"):
                types_by_module.setdefault(node["targetModule"], {}).setdefault(
                    str(node["target"]), node["type"]
                )

    # Hovered types are code surfaces too. Rebuild their ranges solely from the
    # compiler-traced application nodes used by source blocks. Balanced
    # delimiters are not nodes. Every visible range points into $expressions,
    # so every coloured node can open another typed hover.
    for module, nodes in expression_types.items():
        semantic_nodes = [dict(node) for node in nodes]
        semantic_index = semantic_type_index(semantic_nodes)
        module_types = types_by_module.get(module, {})
        for position, type_html in list(module_types.items()):
            module_types[position] = decorate_type_nodes(
                TYPE_NODE_TAG_RE.sub("", type_html), semantic_index, module
            )
        for node in nodes:
            node["type"] = decorate_type_nodes(
                TYPE_NODE_TAG_RE.sub("", node["type"]), semantic_index, module
            )

    for module_types in types_by_module.values():
        for position, type_html in module_types.items():
            module_types[position] = resolve_type_hover_links(type_html, types_by_module)
    for nodes in expression_types.values():
        for node in nodes:
            node["type"] = resolve_type_hover_links(node["type"], types_by_module)

    if selected_modules:
        unknown = selected_modules - rendered_set
        if unknown:
            sys.stderr.write(f"unknown rendered module(s): {', '.join(sorted(unknown))}\n")
            return 2
        preview_modules = referenced_module_closure(
            selected_modules, html_dir, rendered_set
        )
        modules_to_render = [m for m in rendered if m in preview_modules]
    else:
        modules_to_render = rendered

    # second pass: render every reachable module (externals get the "left Bedrock" banner;
    # the Origin preview also supplies the generated reading-guide index)
    for m in modules_to_render:
        render_module(m, html_dir, langs, internal, rendered_set, modnav_list,
                      name2pos, canonical_names, types_by_module, expression_types,
                      terms, tpl, out_dir, base, site, prelude_reexports, reading_data)

    # A selected-module rebuild is also the fast preview path used while the
    # renderer is being refined.  Publish changed CSS/JS before returning so
    # the cache-busted URL in the rebuilt page always names the served asset.
    if os.path.isdir(static_dir):
        shutil.copytree(static_dir, os.path.join(out_dir, "static"), dirs_exist_ok=True)

    for lang in langs:
        directory = os.path.join(out_dir, lang, 'types')
        os.makedirs(directory, exist_ok=True)
        with open(os.path.join(directory, '$syntax.json'), 'w', encoding='utf-8') as output:
            json.dump({key: help_html(key, lang) for key in HELP}, output, ensure_ascii=False)

    if selected_modules:
        print(f"rendered {len(selected_modules)} selected module(s) and "
              f"{len(modules_to_render) - len(selected_modules)} reachable page(s) "
              f"x {len(langs)} "
              f"language(s) -> {out_dir}", file=sys.stderr)
        return 0

    search_mods = sorted(internal)                   # search indexes Bedrock identifiers only
    for lang in langs:
        os.makedirs(os.path.join(out_dir, lang), exist_ok=True)
        write_search(out_dir, lang, search_mods, name2pos, pos_aspect, types_by_module)
        write_terms(out_dir, lang, terms)
        with open(os.path.join(out_dir, lang, "reading-routes.json"), "w", encoding="utf-8") as route_file:
            json.dump(reading_data, route_file, ensure_ascii=False)
        # Keep old inbound chapter URLs usable after the source/module rename.
        legacy = ('<!DOCTYPE html><html lang="' + lang + '"><meta charset="utf-8">'
                  '<meta http-equiv="refresh" content="0;url=index.html#milestones">'
                  '<link rel="canonical" href="index.html#milestones">'
                  '<title>' + UI[lang]['landmark'] + '</title>'
                  '<a href="index.html#milestones">' + UI[lang]['landmark'] + '</a>'
                  '<script>location.replace("index.html#milestones")</script></html>')
        with open(os.path.join(out_dir, lang, 'Milestones.html'), 'w', encoding='utf-8') as output:
            output.write(legacy)
    write_root(out_dir, langs, base)
    write_agent_files(out_dir, langs, base, modnav_list)
    # One cross-language index; shared Agda code is indexed once, not once per edition.
    search_entries, seen = [], set()
    for lang in langs:
        for module in rendered:
            search_entries.append({'name': chapter_title(module, lang), 'module': module,
                'lang': lang, 'kind': 'chapter', 'text': chapter_field(module, 'description', lang),
                'href': chapter_href(module)})
        for term in terms:
            search_entries.append({'name': ' · '.join(localized_forms(term, lang)),
                'module': term['introduced_in'], 'lang': lang, 'kind': 'term',
                'text': term[f'recap_{lang}'],
                'href': chapter_href(term['introduced_in'], '#term-' + term['id'])})
    for module in rendered:
        for name, position in name2pos.get(module, {}).items():
            search_entries.append({'name': name, 'module': module, 'lang': '*',
                'kind': 'definition', 'text': plain_code(types_by_module.get(module, {}).get(position, '')),
                'href': chapter_href(module, '#' + position)})
    for entry in SEARCH_PASSAGES:
        key = (entry['lang'], entry['href'], entry['kind'], entry['text'])
        if key not in seen:
            seen.add(key); search_entries.append(entry)
    with open(os.path.join(out_dir, 'search-content.json'), 'w', encoding='utf-8') as output:
        json.dump(search_entries, output, ensure_ascii=False, separators=(',', ':'))

    print(f"rendered {len(rendered)} module(s) ({len(internal)} internal) "
          f"x {len(langs)} language(s) -> {out_dir}", file=sys.stderr)
    print(f"agent layer: {len(internal) * len(langs)} Markdown twin(s), llms.txt, "
          f"sitemap.xml, robots.txt, _headers", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
