from pathlib import Path
"""The complete interactive textbook page shell, shared by project instances."""
import html as htmllib
import json
import os
import re
from html_contract import *
from markdown_core import *
from site_localization import LANG_LABELS, interface_copy, lang_nav, hreflang_links
from reading_routes import GUIDE_PANEL, own_page, twin_of
from term_registry import TERM_MARK_RE, localized_forms, localized_abbreviation

from i18n_markers import group_languages, weave_for_site
from agda_help import annotate_inline_code, annotate_keywords
from agda_semantics import *
from boilerplate import mirror_boilerplate
from search_index import passages
from site_inputs import source_file
from document_renderer import MarkdownDocument, CodeContext

class PageRenderer:
    def __init__(self, config, book, code, publication):
        self.config = config
        self.book = book
        self.publication = publication
        self.ui = interface_copy(config, book)
        self.search_passages = []

    def render_review_status(self, body, module, lang):
        """Human editorial review is catalog metadata, not inferred from CI success."""
        reviewed = self.book.meta.get(module, {}).get('human_reviewed', False)
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


    def toc_html(self, toc, lang):
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
                f'{self.ui[lang]["contents"]}</summary>'
                f'<ul class="toc">{items}</ul></details>')


    def modules_nav(self, current, mods, lang, reading_data):
        """Contents and the current route; the graph owns namespace browsing."""

        guide = "".join(
            f'<li><a href="index.html#{target}">{self.ui[lang][key]}</a></li>'
            for target, key in ((GUIDE_PANEL, "landmark"),
                                ("reading-explorer", "routes"),
                                ("dependency-map", "depmap"),
                                ("term-glossary", "terms")))
        routes = reading_data["routes"]
        route = next((item for item in routes if current in item["chapters"]), routes[0])
        route_title = htmllib.escape(route["title"][lang])
        def route_link(module):
            active = ' aria-current="page"' if module == current else ""
            return (f'<li><a href="{self.book.href(module)}" data-chapter="{module}"{active}>'
                    f'{htmllib.escape(self.book.title(module, lang))}</a></li>')
        route_links = "".join(route_link(module) for module in route["chapters"])
        return (f'<details class="navsec reading-guide"><summary class="nav-title">'
                f'{self.ui[lang]["guide"]}</summary><ul class="guide-nav">{guide}</ul></details>'
                f'<details class="navsec current-route" open data-current="{current}" '
                f'data-lang="{lang}"><summary class="nav-title">'
                f'{self.ui[lang]["current_route"]}<span class="current-route-name">{route_title}</span>'
                f'</summary><ul class="route-nav" data-route="{route["id"]}">'
                f'{route_links}</ul></details>')


    def chapter_navigation(self, body, module, modules, lang):
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
            title = self.book.title(modules[target], lang)
            label = htmllib.escape(f'{self.ui[lang][direction]}: {title}', quote=True)
            icon = (f'<svg class="chapnav-icon" viewBox="0 0 24 24" aria-hidden="true" '
                    f'focusable="false" fill="none" stroke="currentColor" stroke-width="1.7" '
                    f'stroke-linecap="round" stroke-linejoin="round"><path d="{path}"/></svg>')
            text = f'<span class="chapnav-title">{htmllib.escape(title)}</span>'
            content = icon + text if direction == 'prev' else text + icon
            links.append(f'<a class="chapnav-{direction}" rel="{direction}" '
                         f'aria-label="{label}" href="{self.book.href(modules[target])}">{content}</a>')
        if not links:
            return body
        label = {'en': 'Chapter navigation', 'zh': '章节导航', 'ja': '章のナビゲーション'}[lang]
        nav = f'<nav class="chapnav" aria-label="{label}">{"".join(links)}</nav>'
        end = body.find('</h1>')
        split = end + len('</h1>') if end >= 0 else 0
        return body[:split] + nav.replace('class="chapnav"', 'class="chapnav chapnav-top"', 1) + body[split:] + nav


    def learning_home(self, body, mount, lang, terms):
        labels = {
            "en": ("Explore the book", "Reading routes", "Dependency graph", self.book.title(self.config.landing_module, lang), "Glossary"),
            "zh": ("浏览本书", "阅读路线", "依赖图", self.book.title(self.config.landing_module, lang), "术语表"),
            "ja": ("本書を読む", "学習ルート", "依存グラフ", self.book.title(self.config.landing_module, lang), "用語集"),
        }[lang]
        heading_pattern = r'<div class="chapter-heading-row">.*?</div>|<h1\b[^>]*>.*?</h1>'
        heading_match = re.search(heading_pattern, body, re.DOTALL)
        heading = heading_match.group(0) if heading_match else ""
        # The guide is a shell, not a replacement for the embedded chapter.
        # Preserve the chapter's hover trigger, source anchors and review badge.
        milestone_heading = (re.sub(r'<(/?)h1\b', r'<\1h2', heading)
                             if heading else f'<h2>{labels[3]}</h2>')
        guide_heading = f'<h1 id="reading-guide-title">{htmllib.escape(self.ui[lang]["guide"])}</h1>'
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
            label = self.glossary_label_html(entry, lang)
            recap = htmllib.escape(entry[f"recap_{lang}"])
            href = self.book.href(entry["introduced_in"], f'#term-{entry["id"]}')
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


    def glossary_label_html(self, entry, lang):
        """Display the full term and its registered abbreviation together."""
        label = htmllib.escape(entry[lang])
        abbreviation = localized_abbreviation(entry, lang)
        if abbreviation:
            label += (f' <span class="term-abbreviation">'
                      f'({htmllib.escape(abbreviation)})</span>')
        return label


    def ext_banner(self, lang):
        """Prominent header marking a page as external to Bedrock (links home)."""
        s = self.ui[lang]
        return (f'<div class="ext-banner">⚠ {htmllib.escape(s["external"])} '
                f'<a href="index.html">{htmllib.escape(s["back"])}</a></div>')


    def render_module(self, module, corpus, *, code, terms, template, out_dir, reading):
        raw, literate = corpus.read(module)
        internal, rendered = code.internal, code.rendered
        langs, base, site = self.config.languages, self.config.base_url, self.config.name
        modnav_list = [node['id'] for node in sorted(reading['nodes'], key=lambda node: node['order'])]
        reading_data, tpl = reading, template

        is_external = module not in internal
        is_landing = module == self.config.landing_module
        out_name = "index.html" if is_landing else module + ".html"
        current = "" if (is_external or is_landing) else module  # highlight in the modules nav
        langs_present = group_languages(raw) if literate else set()

        document = MarkdownDocument(raw, module=module,
            code=code,
            terms=terms, formal_setup=module in internal and self.config.policies.get('formal_setup', True),
            visible_import_chapters=self.config.values.get('visible_import_chapters', []),
            overview=is_landing) if literate else None
        code_blocks = document.blocks if document else []

        def page_body(lang):
            if not document:
                markup = code.semantics.rewrite_links('<pre class="Agda">' + raw + '</pre>', rendered,
                    code.types, code.canonical_names, module)
                return annotate_keywords(markup, lang), [], None
            result = document.render(lang)
            return result.body, result.toc, result.mirror

        for lang in langs:
            body, toc, mirror = page_body(lang)
            self.search_passages.extend(passages(body, module, self.book.title(module, lang), lang, out_name))
            if not is_external:
                body = self.chapter_navigation(body, module, modnav_list, lang)

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
                         f'aria-label="{self.ui[lang]["routes"]}">'
                         f'<p>{fallback.get(lang, fallback["en"])}</p>'
                         f'<a href="index.html#reading-explorer">{self.ui[lang]["guide"]}</a>'
                         f' · <a href="index.html#dependency-map">{self.ui[lang]["depmap"]}</a></section>')
                if is_landing:
                    body = self.learning_home(self.render_review_status(body, module, lang), mount, lang, terms)
                else:
                    heading_end = body.find('</h1>')
                    if heading_end >= 0:
                        split = heading_end + len('</h1>')
                        body = body[:split] + mount + body[split:]
                    else:
                        body = mount + body

            if not is_external and not is_landing:
                body = self.render_review_status(body, module, lang)

            banner = ""
            if langs_present and lang not in langs_present:
                banner = f'<div class="banner">{self.ui[lang]["untranslated"]}</div>'

            title = self.ui[lang]["guide"] if is_landing else self.book.title(module, lang)
            has_mirror = mirror is not None

            def shell(page_name, page_title, page_body_html, page_toc, body_class, module_slot):
                """One rendered page, with everything a machine reads about it filled in."""
                md_name = twin_of(page_name) if has_mirror else ""
                return fill_template(
                    tpl, LANG=lang, TITLE=htmllib.escape(page_title), SITE=htmllib.escape(site),
                    DESC=htmllib.escape(self.publication.page_description(module, lang, is_landing, is_external),
                                        quote=True),
                    BASEURL=base, MODULE=module_slot,
                    CANONICAL=f'  <link rel="canonical" href="{self.config.canonical}/{lang}/{page_name}" />',
                    ALTMD=(f'  <link rel="alternate" type="text/markdown" href="{md_name}" />'
                           if has_mirror else ""),
                    JSONLD=self.publication.json_ld(module, lang, page_name, langs, is_landing, is_external,
                                   has_mirror),
                    CONFIG=self.publication.page_config(module, lang, page_name, md_name, base, site,
                                       is_landing, is_external),
                    BODYCLASS=body_class,
                    EXTBANNER=self.ext_banner(lang) if is_external else "",
                    HREFLANG=hreflang_links(page_name, langs, base),
                    LANGNAV=lang_nav(page_name, lang, langs),
                    MODNAV=self.modules_nav(current if page_name == out_name else module,
                                       modnav_list, lang, reading_data),
                    TOC=page_toc, BANNER=banner, BODY=page_body_html,
                    FOOTER=self.publication.footer_html(lang, base, md_name),
                    S_SEARCH=self.ui[lang]["search"], S_THEME=self.ui[lang]["theme"],
                    S_MENU=self.ui[lang]["menu"], S_CLOSE=self.ui[lang]["close"],
                    S_CONTENT=self.ui[lang]["contents"])

            page = shell(out_name, title, body,
                         "" if is_landing else self.toc_html(toc, lang),
                         "text-page external" if is_external else
                         "text-page learning-home" if is_landing else "text-page",
                         "guide" if is_landing else module)
            dest = os.path.join(out_dir, lang, out_name)
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            Path(dest).write_text(page, encoding='utf-8')

            if has_mirror:
                twin = self.publication.publish_markdown(mirror, module, lang, out_name, langs)
                md_path = os.path.join(out_dir, lang, twin_of(out_name))
                Path(md_path).write_text(twin, encoding='utf-8')

        # Per-module hover payload. Selected-page builds also refresh dependency
        # sidecars below without paying the cost of rendering their full pages.
        write_type_sidecar(module, langs, out_dir, code.types, code.names, code.expressions)
