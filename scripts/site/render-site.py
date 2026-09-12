#!/usr/bin/env python3
"""Render the multilingual, hyperlinked Bedrock site from the masters.

Inputs (produced by the Makefile before this runs):
  _build/html/<Module>.md   from `agda --html --html-highlight=code` on src/Milestones
  _build/types.json         from scripts/site/extract-types.py
  site/template.html        the page shell
  site/vendor/1lab/...      vendored front-end assets (M2c builds CSS/JS into the site)

For each enabled language it weaves the prose by markers, splices the language-neutral
highlighted code, resolves inline `name`{.Agda} references, protects math for client-side
KaTeX, rewrites links (+ data-type for hover), and writes _build/site/<lang>/<Module>.html.
It also emits per-module types/<Module>.json (pos -> abbreviated, hyperlinked type) and a
per-language search.json, a per-language index, and a root language-redirect + 404.

Usage:
  render-site.py [--html-dir _build/html] [--types _build/types.json] [--src src]
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
from reading_routes import build_reading_data  # noqa: E402
from term_registry import TERM_MARK_RE, load_entries, reader_terms, schema_errors, localized_forms  # noqa: E402

LANG_LABELS = {"en": "English", "zh": "中文", "ja": "日本語"}

UI = {
    "en": {"search": "Search…", "theme": "Toggle theme", "contents": "On this page",
           "menu": "Menu", "close": "Close",
           "untranslated": "This page is not yet translated; showing English.",
           "modules": "Modules", "source": "Source", "overview": "Overview",
           "depmap": "Dependency map", "routes": "Reading routes",
           "guide": "Reading guide", "catalog": "Chapter catalog",
           "landmark": "Milestones", "terms": "Glossary",
           "prev": "Example route: previous", "next": "Example route: next",
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
           "depmap": "依赖地图", "routes": "阅读路线",
           "guide": "阅读指南", "catalog": "章节目录",
           "landmark": "里程碑", "terms": "术语表",
           "prev": "示例路线：上一章", "next": "示例路线：下一章",
           "license": "内容以 CC BY-NC-SA 4.0 许可",
           "markdown": "Markdown", "agents": "llms.txt",
           "mdtitle": "本页的纯 Markdown 版本，供 AI 与脚本读取",
           "agentstitle": "AI 应当如何阅读本站",
           "credit": '使用改编自 <a href="https://1lab.dev">1lab</a> 的生成器渲染 '
                     '(AGPL-3.0)。',
           "external": "您正在浏览 Cubical 库。",
           "back": "返回 Bedrock"},
    "ja": {"search": "検索…", "theme": "テーマ切替", "contents": "このページの内容",
           "menu": "メニュー", "close": "閉じる",
           "untranslated": "このページは未翻訳です。英語を表示しています。",
           "modules": "モジュール", "source": "ソース", "overview": "概要",
           "depmap": "依存マップ", "routes": "学習ルート",
           "guide": "読書案内", "catalog": "章の目次",
           "landmark": "マイルストーン", "terms": "用語集",
           "prev": "例示ルート：前の章", "next": "例示ルート：次の章",
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
SITE_URL = "https://bedrock.institute"        # the canonical deployment (.github/workflows/cloudflare.yml)
LANDING = "Milestones"  # preview chapter also supplies the generated reading-guide index
CHAPTER_TITLES = {}
# module -> {"description": {lang: str}, "stage": {lang: str}, "order": int,
#            "prerequisites": [module], "routes": [route id]}. Filled from the reading
# catalog, and read by the per-page description, the JSON-LD graph, the Markdown mirror
# and llms.txt, so all four say the same thing about a chapter.
CHAPTER_META = {}


def chapter_title(module, lang):
    titles = CHAPTER_TITLES.get(module, {})
    return titles.get(lang, titles.get("en", module))


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
# Definition site: <a id="NAME"></a><a id="POS" ... class="ASPECT" ...>token</a>
DEF_RE = re.compile(r'<a id="([^"]+)"></a><a id="(\d+)"[^>]*class="([^"]*)"')
# Any cross-reference link inside highlighted code (optional self-id, optional #position).
LINK_RE = re.compile(r'<a (id="\d+" )?href="([^"#]+)\.html(#\d+)?"([^>]*)>')
INLINE_AGDA_RE = re.compile(r'`([^`]+)`\{\.Agda\}')
A_TAG_RE  = re.compile(r'<a\b([^>]*)>([^<]+)</a>')
HREF_RE   = re.compile(r'\bhref="([^"]+\.html(?:#\d+)?)"')
CLASS_RE  = re.compile(r'\bclass="([^"]*)"')


def ref_link(href, aspect, label, extra_class=""):
    """An inline-ref anchor; hover data only when the href has a position."""
    mod, _, pos = href.rpartition(".html#")
    dt = f' data-type="{mod}#{pos}"' if mod and pos.isdigit() else ""
    cls = (extra_class + (" " + aspect if aspect else "")).strip()
    cls = f' class="{cls}"' if cls else ""
    return f'<a{cls} href="{href}"{dt}>{label}</a>'
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
            out.append("<table>" + "".join(rows) + "</tbody></table>")
            continue
        para = [line]; i += 1
        while i < n and lines[i].strip() and not _is_block_start(lines[i]):
            para.append(lines[i]); i += 1
        out.append("<p>" + _inline(" ".join(s.strip() for s in para)) + "</p>")
    return "\n".join(out), toc


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


def render_type(term, internal_q):
    """Abbreviate module qualifiers and hyperlink internal identifiers in a type string."""
    s = htmllib.escape(term.replace("\n", " "), quote=False)
    links = []
    for q in sorted(internal_q, key=len, reverse=True):
        if q in s:
            mod, pos = internal_q[q]
            tok = f"{NUL}L{len(links)}{NUL}"
            last = q.split(".")[-1]
            links.append(f'<a href="{mod}.html#{pos}">{htmllib.escape(last)}</a>')
            s = s.replace(q, tok)
    s = re.sub(r"(?:[A-Za-z][\w']*\.)+", "", s)        # strip remaining (external) qualifiers
    s = re.sub(r"\bSet\b", "Type", s)                  # cubical display
    for i, link in enumerate(links):
        s = s.replace(f"{NUL}L{i}{NUL}", link)
    return s


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
    items = "".join(f'<li class="toc-l{lvl}"><a href="#{hid}">{htmllib.escape(t)}</a></li>'
                    for lvl, hid, t in toc)
    return (f'<details class="navsec" open><summary class="nav-title">'
            f'{UI[lang]["contents"]}</summary>'
            f'<ul class="toc">{items}</ul></details>')


def modules_nav(current, mods, lang):
    """The 'Modules' sidebar section: the structural catalog. A namespace tree is
    derived from the module list (never hand-maintained): children of every
    level, leaves and subgroups alike, ordered by first appearance in the
    reading order; leaf labels use localized chapter titles. Namespace groups are
    disclosure sections, collapsed by default, with the current page's
    ancestor chain opened."""
    root = []          # entries: ("leaf", module) | ("group", name, children)

    def insert(children, parts, mod):
        if len(parts) == 1:
            children.append(("leaf", mod))
            return
        for entry in children:
            if entry[0] == "group" and entry[1] == parts[0]:
                insert(entry[2], parts[1:], mod)
                return
        group = ("group", parts[0], [])
        children.append(group)
        insert(group[2], parts[1:], mod)

    # Milestones is the reading-guide preview and has its own guide entry. Keep
    # it out of the structural module list so the sidebar does not duplicate it.
    for m in mods:
        if m == LANDING:
            continue
        insert(root, m.split("."), m)

    def render(children, prefix):
        out = []
        for entry in children:
            if entry[0] == "leaf":
                m = entry[1]
                cur = ' class="modleaf cur"' if m == current else ' class="modleaf"'
                label = htmllib.escape(chapter_title(m, lang))
                active = ' aria-current="page"' if m == current else ""
                out.append(f'<li{cur}><a href="{m}.html" title="{m}"{active}>{label}</a></li>')
            else:
                name = entry[1]
                path = f"{prefix}{name}."
                is_open = " open" if current.startswith(path) else ""
                out.append(f'<li class="modgrp"><details{is_open}>'
                           f'<summary class="modgroup">{name}</summary>'
                           f'<ul>{"".join(render(entry[2], path))}</ul>'
                           f'</details></li>')
        return out

    guide = "".join(
        f'<li><a href="index.html#{target}">{UI[lang][key]}</a></li>'
        for target, key in (("reading-explorer", "routes"),
                            ("dependency-map", "depmap"),
                            ("milestones", "landmark"),
                            ("term-glossary", "terms")))
    return (f'<details class="navsec reading-guide" open><summary class="nav-title">'
            f'{UI[lang]["guide"]}</summary><ul class="guide-nav">{guide}</ul></details>'
            f'<details class="navsec"><summary class="nav-title">'
            f'{UI[lang]["modules"]}</summary>'
            f'<ul class="modnav">{"".join(render(root, ""))}</ul></details>')


def learning_home(body, mount, lang, terms):
    labels = {
        "en": ("Explore the book", "Reading routes", "Dependency map", "Milestones", "Glossary"),
        "zh": ("浏览本书", "阅读路线", "依赖图", "里程碑", "术语表"),
        "ja": ("本書を読む", "学習ルート", "依存マップ", "マイルストーン", "用語集"),
    }[lang]
    heading_match = re.search(r"<h1\b[^>]*>.*?</h1>", body, re.DOTALL)
    heading = heading_match.group(0) if heading_match else ""
    if heading:
        heading = re.sub(r"(<h1\b[^>]*>).*?(</h1>)",
                         rf"\1{htmllib.escape(UI[lang]['guide'])}\2",
                         heading, count=1, flags=re.DOTALL)
    milestone_body = re.sub(r"<h1\b[^>]*>.*?</h1>", "", body, count=1, flags=re.DOTALL)
    intro_text = {
        "en": "Choose a route, inspect the prerequisite structure, or review the book's main theorems and terminology.",
        "zh": "选择一条阅读路线，查看先修关系，或集中回顾本书的里程碑与术语。",
        "ja": "学習ルートを選び、前提関係を確認し、マイルストーンと用語を振り返ります。",
    }[lang]
    ids = ("reading-explorer", "dependency-map", "milestones", "term-glossary")
    tabs = ''.join(f'<a id="tab-{key}" href="#{key}" data-panel="{key}">{label}</a>'
                   for key, label in zip(ids, labels[1:]))
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
        label = htmllib.escape(entry[lang])
        recap = htmllib.escape(entry[f"recap_{lang}"])
        href = f'{entry["introduced_in"]}.html#term-{entry["id"]}'
        search_text = htmllib.escape(f'{entry[lang]} {entry[f"recap_{lang}"]}', quote=True)
        glossary_rows.append(
            f'<div class="term-entry" data-term-entry data-term-search="{search_text}">'
            f'<span class="term-index" aria-hidden="true">{index}</span>'
            f'<dt><a href="{href}">{label}</a></dt><dd>{recap}</dd></div>')
    glossary = ''.join(glossary_rows)
    return (f'<header class="book-intro">{heading}</header>'
            f'<p class="book-intro-lead">{intro_text}</p>'
            f'<nav class="book-tabs" aria-label="{labels[0]}">{tabs}</nav>'
            f'<div class="book-panels">{mount}'
            f'<section id="dependency-map" class="book-panel">'
            '<!-- DEPENDENCY_MAP --></section>'
            f'<section id="milestones" class="book-panel guide-landmark"><h2>{labels[3]}</h2>'
            f'{milestone_body}</section>'
            f'<section id="term-glossary" class="book-panel term-glossary-panel"><h2>{labels[4]}</h2>'
            f'<div class="term-glossary-head"><p>{glossary_copy}</p>'
            f'<label class="term-glossary-search"><span class="sr-only">{glossary_search}</span>'
            f'<input type="search" data-term-search-input aria-controls="term-glossary-list" '
            f'placeholder="{glossary_search}" autocomplete="off"></label></div>'
            f'<dl id="term-glossary-list" class="term-glossary-list">{glossary}</dl>'
            f'<p class="term-glossary-empty" data-term-empty hidden>{glossary_empty}</p></section></div>')


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
    copyright_ = f'© 2026 Bedrock Institute · {s["license"]} · {source}'
    formats = [f'<a href="{base}/llms.txt" title="{htmllib.escape(s["agentstitle"])}">'
               f'{s["agents"]}</a>']
    if md_href:
        formats.insert(0, f'<a href="{md_href}" title="{htmllib.escape(s["mdtitle"])}" '
                          f'type="text/markdown">{s["markdown"]}</a>')
    return (f'<div class="footer-credit">{s["credit"]}</div>'
            f'<div class="footer-formats">{" · ".join(formats)}</div>'
            f'<div class="footer-copyright">{copyright_}</div>')


def rewrite_links(body, rendered, types_global):
    """Keep links to any rendered module (internal or external), tagging data-type when the
    TARGET has a type (drives hover, including on cubical identifiers). Links to a module we
    did not render lose their dead href (the <a> element stays so the </a> still matches).

    `types_global` is {module: {pos: type-html}} across ALL rendered modules."""
    def repl(m):
        idpart, mod, anchor, rest = m.group(1) or "", m.group(2), m.group(3) or "", m.group(4)
        if "://" in mod:
            return m.group(0)
        if mod in rendered:
            pos = anchor[1:] if anchor else ""
            extra = f' data-type="{mod}#{pos}"' if pos and pos in types_global.get(mod, {}) else ""
            target = f"{mod}.html"
            return f'<a {idpart}href="{target}{anchor}"{rest}{extra}>'
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


def build_types(modules, name2pos, types_raw, internal_q):
    """Global {module: {pos: abbreviated/hyperlinked type-html}} for hover + sidecars."""
    g = {}
    for m in modules:
        g[m] = {}
        for name, pos in name2pos.get(m, {}).items():
            t = types_raw.get(m, {}).get(name.split(".")[-1])
            if t:
                g[m][pos] = render_type(t, internal_q)
    return g


def fill_template(tpl, **kw):
    out = tpl
    for k, v in kw.items():
        out = out.replace(f"%%{k}%%", v)
    return out


def render_module(module, html_dir, langs, internal, rendered, modnav_list,
                  name2pos, types_global, terms, tpl, out_dir, base, site):
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

    def page_body(lang):
        if not literate:
            # a library page is bare highlighted code: wrap it and resolve its links
            code = rewrite_links('<pre class="Agda">' + raw + '</pre>', rendered, types_global)
            return code, [], None
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
        woven = INLINE_AGDA_RE.sub(lambda m: stash("REF", inline_ref(m.group(1),
                                   internal, name2pos, local_refs)), woven)
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
        body = rewrite_links(body, rendered, types_global)
        return auto_link_terms(body, lang, module, terms), toc, mirror

    for lang in langs:
        body, toc, mirror = page_body(lang)
        chapter_body = body

        if not is_external:
            fallback = {
                "en": "Choose a topic, compare routes, or continue from completed prerequisites.",
                "zh": "按主题阅读、并排比较路线，或从已完成的先修继续。",
                "ja": "主題を選び、ルートを比較し、修了した前提から進めます。",
            }
            if not is_landing:
                fallback = {
                    "en": "Read this chapter directly, or use the reading guide and dependency map to choose another route.",
                    "zh": "可以直接阅读本章，也可以通过阅读指南和依赖地图选择其他路线。",
                    "ja": "この章を読むか、読書案内と依存マップで別のルートを選べます。",
                }
            route_current = "" if is_landing else module
            mount = (f'<section id="reading-explorer" data-current="{route_current}" '
                     f'data-lang="{lang}" data-source="reading-routes.json" '
                     f'aria-label="{UI[lang]["routes"]}">'
                     f'<p>{fallback.get(lang, fallback["en"])}</p>'
                     f'<a href="index.html#reading-explorer">{UI[lang]["guide"]}</a>'
                     f' · <a href="index.html#dependency-map">{UI[lang]["depmap"]}</a></section>')
            if is_landing:
                body = learning_home(body, mount, lang, terms)
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

        # previous/next links along the reading order (the reading catalog)
        if not is_external and not is_landing and module in modnav_list:
            i = modnav_list.index(module)
            parts = []
            if i > 0:
                parts.append(f'<a class="chapnav-prev" href="{modnav_list[i - 1]}.html">'
                             f'&larr; {UI[lang]["prev"]} · {htmllib.escape(chapter_title(modnav_list[i - 1], lang))}</a>')
            if i + 1 < len(modnav_list):
                parts.append(f'<a class="chapnav-next" href="{modnav_list[i + 1]}.html">'
                             f'{UI[lang]["next"]} · {htmllib.escape(chapter_title(modnav_list[i + 1], lang))} &rarr;</a>')
            body += '<nav class="chapnav">' + "".join(parts) + "</nav>"

        banner = ""
        if langs_present and lang not in langs_present:
            banner = f'<div class="banner">{UI[lang]["untranslated"]}</div>'

        title = UI[lang]["overview"] if is_landing else chapter_title(module, lang)
        has_mirror = mirror is not None

        def shell(page_name, page_title, page_body_html, page_toc, body_class, module_slot):
            """One rendered page, with everything a machine reads about it filled in."""
            md_name = (page_name[:-len(".html")] + ".md") if has_mirror else ""
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
                                   modnav_list, lang),
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

        if is_landing:
            chapter_page = shell(module + ".html", chapter_title(module, lang), chapter_body,
                                 toc_html(toc, lang), "text-page", module)
            open(os.path.join(out_dir, lang, module + ".html"), "w", encoding="utf-8").write(chapter_page)

        # The landing page and the chapter page show the same master, so each gets a
        # twin under its own name; a `.md` beside any page URL then always resolves.
        if has_mirror:
            for page_name in [out_name] + ([module + ".html"] if is_landing else []):
                twin = markdown_mirror(mirror, code_blocks, module, lang, page_name, langs)
                md_path = os.path.join(out_dir, lang, page_name[:-len(".html")] + ".md")
                open(md_path, "w", encoding="utf-8").write(twin)

    # per-module type sidecar (keyed by the real module name; hover fetches types/<mod>.json)
    sidecar = json.dumps(types_global.get(module, {}), ensure_ascii=False)
    for lang in langs:
        tdir = os.path.join(out_dir, lang, "types")
        os.makedirs(tdir, exist_ok=True)
        open(os.path.join(tdir, module + ".json"), "w", encoding="utf-8").write(sidecar)


def inline_ref(name, internal, name2pos, local_refs):
    """Render `name`{.Agda} as a highlighted, hyperlinked span if the identifier is known."""
    target = None
    if "." in name:
        mod, _, local = name.rpartition(".")
        if mod in internal and local in name2pos.get(mod, {}):
            target = (mod, name2pos[mod][local])
    if target is None:
        for mod in internal:
            if name in name2pos.get(mod, {}):
                target = (mod, name2pos[mod][name]); break
    label = htmllib.escape(name)
    href_aspect = local_refs.get(name)
    if target:
        mod, pos = target
        # reuse the aspect of the module's own code tokens, and wrap in a
        # span.Agda so the .Agda .<Aspect> colour rules apply to prose refs too
        aspect = href_aspect[1] if href_aspect else ""
        return ('<span class="Agda">'
                + ref_link(f"{mod}.html#{pos}", aspect, label, "inline-ref")
                + "</span>")
    if href_aspect:
        # a link agda already resolved in this module's own code; this is how
        # prose references library identifiers (Type, refl, ...) and modules
        return ('<span class="Agda">'
                + ref_link(href_aspect[0], href_aspect[1], label, "inline-ref")
                + "</span>")
    # not a single known identifier: render as an expression, token by token,
    # reusing the module's own links (keywords, brackets, and bound variables
    # stay plain; identifiers get their code aspect and hyperlink)
    parts, linked = [], 0
    for tok in re.split(r"([\s(){};]+)", name):
        info = local_refs.get(tok)
        if tok.strip() and info and "Bound" not in info[1]:
            parts.append(ref_link(info[0], info[1], htmllib.escape(tok)))
            linked += 1
        else:
            parts.append(htmllib.escape(tok))
    if linked:
        return '<span class="Agda inline-ref">' + "".join(parts) + "</span>"
    return f'<code class="Agda inline-ref">{label}</code>'


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
        f"html: {out_name}",
        f"agda_source: {SOURCE_TREE}/{module.replace('.', '/')}.lagda.md",
        "prerequisites: [" + ", ".join(meta.get("prerequisites", [])) + "]",
        "routes: [" + ", ".join(meta.get("routes", [])) + "]",
        "translations: [" + ", ".join(
            f"{SITE_URL}/{other}/{module}.md" for other in langs if other != lang) + "]",
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
        page["encoding"] = {"@type": "MediaObject", "encodingFormat": "text/markdown",
                            "contentUrl": f"{SITE_URL}/{lang}/{module}.md"}
    graph = {"@context": "https://schema.org", "@graph": [page, book]}
    payload = json.dumps(graph, ensure_ascii=False, separators=(",", ":"))
    return ('  <script type="application/ld+json">'
            + payload.replace("<", "\\u003c") + "</script>")


AGENT_GUIDE_HEAD = """# Bedrock

> {blurb}

Bedrock is a machine-checked development, in Cubical Agda, of the set theory behind
contemporary questions about the universe of sets. Two results are proved and both are
stated in the chapter `Milestones`: `L⊨ZFC` and `L⊨GCH`, the constructible universe
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
  reaches the same chapter in another language.
- **Every chapter page has a plain-Markdown twin at `/<lang>/<Module>.md`.** It carries
  the same prose and the same Agda in fenced blocks, with the chapter's stage,
  prerequisites and source in YAML front matter, and it is a fraction of the size of
  the HTML. Prefer it. Each HTML page advertises its own mirror with
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
         "prerequisites, reading-order position and route memberships."),
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
                 "human reads.")
    lines.append("")
    for module in modnav_list:
        meta = CHAPTER_META.get(module, {})
        stage = chapter_field(module, "stage", lang)
        title = chapter_title(module, lang)
        desc = chapter_field(module, "description", lang)
        position = meta.get("order", 0)
        entry = (f"- [{position}. {title}]({SITE_URL}/{lang}/{module}.md) "
                 f"(`{module}`, {stage})")
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

    pages = ["index.html"] + [f"{m}.html" for m in modnav_list]
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
        for name, pos in name2pos.get(m, {}).items():
            t = types_by_module.get(m, {}).get(pos, "")
            entries.append({"name": name, "module": m, "anchor": pos,
                            "aspect": pos_aspect.get(m, {}).get(pos, ""),
                            "type": re.sub(r"<[^>]+>", "", t),
                            "href": f"{m}.html#{pos}"})
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
            "href": f'{module}.html#term-{entry["id"]}',
        }
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
    tpl_path, out_dir = "site/template.html", "_build/site"
    static_dir = "site/static"
    langs, base, site = ["en", "zh", "ja"], "", "Bedrock"
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--html-dir": i += 1; html_dir = argv[i]
        elif a == "--types": i += 1; types_path = argv[i]
        elif a == "--src": i += 1; src = argv[i]
        elif a == "--template": i += 1; tpl_path = argv[i]
        elif a == "--out": i += 1; out_dir = argv[i]
        elif a == "--static": i += 1; static_dir = argv[i]
        elif a == "--langs": i += 1; langs = [x for x in argv[i].split(",") if x]
        elif a == "--base-url": i += 1; base = argv[i].rstrip("/")
        elif a == "--site": i += 1; site = argv[i]
        else: sys.stderr.write(f"unknown option: {a}\n"); return 2
        i += 1

    internal = set(
        os.path.relpath(p, src)[:-len(".lagda.md")].replace(os.sep, ".")
        for p in glob.glob(os.path.join(src, "**", "*.lagda.md"), recursive=True))

    # the full reachable set = every module agda --html emitted (Bedrock .md + library .html)
    rendered = sorted(set(
        os.path.basename(p).rsplit(".", 1)[0]
        for p in glob.glob(os.path.join(html_dir, "*.md"))
        + glob.glob(os.path.join(html_dir, "*.html"))))
    rendered_set = set(rendered)
    if not rendered:
        sys.stderr.write(f"no highlighted output in {html_dir}; run `agda --html` first\n")
        return 1
    # Validate author-maintained routes before producing any reader-facing pages.
    reading_data = build_reading_data(src)
    order = {node["id"]: node["order"] for node in reading_data["nodes"]}
    modnav_list = sorted(internal, key=lambda m: (order.get(m, len(order) + 1), m))
    CHAPTER_TITLES.clear()
    CHAPTER_TITLES.update({node["id"]: node["title"] for node in reading_data["nodes"]})
    CHAPTER_META.clear()
    CHAPTER_META.update({
        node["id"]: {"description": node["description"], "stage": node["stage"],
                     "order": node["order"], "prerequisites": node["prerequisites"],
                     "routes": node["routes"]}
        for node in reading_data["nodes"]})
    glossary_entries = load_entries()
    term_errors = schema_errors(glossary_entries)
    if term_errors:
        raise ValueError("\n".join(term_errors))
    terms = sort_reader_terms(reader_terms(glossary_entries), reading_data, src)
    types_raw = json.load(open(types_path, encoding="utf-8")) if os.path.exists(types_path) else {}
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

    # first pass: index every definition (names, positions, aspects) across ALL rendered modules
    name2pos, pos_aspect = {}, {}
    for m in rendered:
        path, literate = source_file(html_dir, m)
        content = open(path, encoding="utf-8").read()
        if literate:
            for blk in PRE_RE.findall(content):
                index_definitions(blk, m, name2pos, pos_aspect)
        else:
            index_definitions(content, m, name2pos, pos_aspect)   # whole .html is code
    internal_q = {f"{m}.{n}": (m, p) for m in name2pos for n, p in name2pos[m].items()}
    types_by_module = build_types(rendered, name2pos, types_raw, internal_q)

    # second pass: render every reachable module (externals get the "left Bedrock" banner;
    # the Milestones preview also supplies the generated reading-guide index)
    for m in rendered:
        render_module(m, html_dir, langs, internal, rendered_set, modnav_list,
                      name2pos, types_by_module, terms, tpl, out_dir, base, site)

    search_mods = sorted(internal)                   # search indexes Bedrock identifiers only
    for lang in langs:
        os.makedirs(os.path.join(out_dir, lang), exist_ok=True)
        write_search(out_dir, lang, search_mods, name2pos, pos_aspect, types_by_module)
        write_terms(out_dir, lang, terms)
        with open(os.path.join(out_dir, lang, "reading-routes.json"), "w", encoding="utf-8") as route_file:
            json.dump(reading_data, route_file, ensure_ascii=False)
    write_root(out_dir, langs, base)
    write_agent_files(out_dir, langs, base, modnav_list)

    if os.path.isdir(static_dir):                    # committed CSS/JS/favicon
        shutil.copytree(static_dir, os.path.join(out_dir, "static"), dirs_exist_ok=True)

    print(f"rendered {len(rendered)} module(s) ({len(internal)} internal) "
          f"x {len(langs)} language(s) -> {out_dir}", file=sys.stderr)
    print(f"agent layer: {len(internal) * len(langs)} Markdown twin(s), llms.txt, "
          f"sitemap.xml, robots.txt, _headers", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
