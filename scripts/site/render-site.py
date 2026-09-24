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
from assets import AssetBundle
from term_registry import (TERM_MARK_RE, load_entries, reader_terms, schema_errors,
                           localized_forms, localized_abbreviation)  # noqa: E402

from html_contract import *
from markdown_core import *
from agda_semantics import *


from pathlib import Path
from site_config import SiteConfig, BookCatalog
from site_localization import LANG_LABELS, lang_nav, hreflang_links
from site_inputs import *
from publication import Publication
from page_renderer import PageRenderer

# Legacy callers get a lazy Bedrock facade. Importing or invoking an explicit
# project never reads the Bedrock instance. New code uses the classes above.
_LEGACY = None
_LEGACY_NAMES = {'chapter_href', 'inline_ref', 'prelude_reexport_index', 'json_ld', 'LANDING', 'glossary_label_html', 'inline_reference_resolver', 'SOURCE_TREE', 'render_review_status', 'SITE_BLURB', 'write_search', 'write_terms', 'add_prelude_reexport_types', 'page_config', 'BOOK', 'SEARCH_PASSAGES', 'UI', 'SITE_URL', 'page_description', 'CHAPTER_TITLES', 'build_expression_types', 'learning_home', 'ext_banner', 'render_module', 'footer_html', 'agent_guide', 'write_root', 'PROJECT', 'markdown_mirror', 'PAGES', 'chapter_field', 'SEMANTICS', 'render_type', 'build_types', 'toc_html', 'SOURCE_URL', 'CHAPTER_META', 'chapter_navigation', 'chapter_title', 'PUBLICATION', 'modules_nav', 'rewrite_links', 'PRELUDE_MODULE', 'write_agent_files'}

def __getattr__(name):
    global _LEGACY
    if name not in _LEGACY_NAMES:
        raise AttributeError(name)
    if _LEGACY is None:
        PROJECT = SiteConfig.load(Path(__file__).resolve().parents[2] / "site/project.json",
                                  root=Path(__file__).resolve().parents[2])
        BOOK = BookCatalog()
        SEMANTICS = AgdaSemantics(prelude_module=PROJECT.prelude_module, chapter_href=BOOK.href)
        PUBLICATION = Publication(PROJECT, BOOK)
        PAGES = PageRenderer(PROJECT, BOOK, SEMANTICS, PUBLICATION)
        CHAPTER_META, CHAPTER_TITLES = BOOK.meta, BOOK.titles
        SEARCH_PASSAGES = PAGES.search_passages
        chapter_title, chapter_href, chapter_field = BOOK.title, BOOK.href, BOOK.field
        UI = PAGES.ui
        SOURCE_URL, SOURCE_TREE, SITE_URL = PROJECT.repository, PROJECT.source_tree, PROJECT.canonical
        SITE_BLURB, LANDING, PRELUDE_MODULE = PROJECT.descriptions, PROJECT.landing_module, PROJECT.prelude_module
        render_type = SEMANTICS.render_type
        prelude_reexport_index = SEMANTICS.prelude_reexport_index
        rewrite_links = SEMANTICS.rewrite_links
        build_types = SEMANTICS.build_types
        add_prelude_reexport_types = SEMANTICS.add_prelude_reexport_types
        build_expression_types = SEMANTICS.build_expression_types
        inline_reference_resolver = SEMANTICS.inline_reference_resolver
        inline_ref = SEMANTICS.inline_ref
        page_description = PUBLICATION.page_description
        footer_html = PUBLICATION.footer_html
        markdown_mirror = PUBLICATION.markdown_mirror
        json_ld = PUBLICATION.json_ld
        page_config = PUBLICATION.page_config
        agent_guide = PUBLICATION.agent_guide
        write_agent_files = PUBLICATION.write_agent_files
        write_search = PUBLICATION.write_search
        write_terms = PUBLICATION.write_terms
        write_root = PUBLICATION.write_root
        render_review_status = PAGES.render_review_status
        toc_html = PAGES.toc_html
        modules_nav = PAGES.modules_nav
        chapter_navigation = PAGES.chapter_navigation
        learning_home = PAGES.learning_home
        glossary_label_html = PAGES.glossary_label_html
        ext_banner = PAGES.ext_banner
        render_module = PAGES.render_module
        _LEGACY = {key: value for key, value in locals().items() if key in _LEGACY_NAMES}
    return _LEGACY[name]

def main(argv):
    from website import build_site
    args = list(argv)
    config = None
    if '--config' in args:
        index = args.index('--config')
        filename = args[index + 1]
        del args[index:index + 2]
        project_root = Path(filename).resolve().parent
        if '--project-root' in args:
            index = args.index('--project-root')
            project_root = Path(args[index + 1]).resolve()
            del args[index:index + 2]
        config = SiteConfig.load(filename, root=project_root)
    if config is None:
        config = __getattr__("PROJECT")
    return build_site(config, args)


if __name__ == '__main__':
    raise SystemExit(main(sys.argv[1:]))
