"""Reusable complete textbook-site build entry point.

Every project input comes from SiteConfig. The packaged template and browser
assets are shared website resources, not content belonging to an instance.
"""
from pathlib import Path
import glob
import html as htmllib
import json
import os
import sys
from agda_semantics import AgdaSemantics
from compiler_index import build_code_context
from site_config import SiteConfig, BookCatalog
from site_inputs import SourceCorpus, sort_reader_terms
from site_localization import interface_copy
from page_renderer import PageRenderer
from publication import Publication
from assets import AssetBundle
from dependency_graph import render_graph
from diagram_style import check_sources as check_diagrams
from reading_routes import build_reading_data
from agda_help import HELP, help_html
from markdown_core import plain_code
from term_registry import load_entries, reader_terms, schema_errors, localized_forms

def build_site(config, argv=()):
    # Resolve all overrides before constructing consumers. A build has exactly
    # one effective project identity, language set and deployment prefix.
    overrides, remaining = {}, []
    i = 0
    config_options = {'--site': 'name', '--langs': 'languages', '--base-url': 'base_url'}
    while i < len(argv):
        option = argv[i]
        if option in config_options:
            if i + 1 == len(argv):
                raise ValueError(f'{option}: missing value')
            value = argv[i + 1]
            overrides[config_options[option]] = value.split(',') if option == '--langs' else value
            i += 2
        else:
            remaining.append(option)
            i += 1
    config = config.with_overrides(**overrides)
    argv = remaining
    resource_root = Path(__file__).resolve().parents[2] / 'site'
    html_dir = str(config.path(config.highlighted)) if config.highlighted else None
    types_path = str(config.path(config.types)) if config.types else ''
    expression_types_path = str(config.path(config.expression_types)) if config.expression_types else ''
    src = str(config.path(config.sources))
    tpl_path, out_dir = str(resource_root / 'template.html'), '_build/site'
    static_dir = str(resource_root / 'static')
    langs, base, site = list(config.languages), config.base_url, config.name
    book = BookCatalog()
    semantics = AgdaSemantics(prelude_module=config.prelude_module, chapter_href=book.href)
    publication = Publication(config, book)
    pages = PageRenderer(config, book, semantics, publication)
    chapter_title, chapter_href, chapter_field = book.title, book.href, book.field
    SEARCH_PASSAGES = pages.search_passages
    render_module = pages.render_module
    write_root, write_agent_files = publication.write_root, publication.write_agent_files
    write_search, write_terms = publication.write_search, publication.write_terms
    LANDING = config.landing_module
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
        elif a == "--module":
            i += 1
            selected_modules.update(x for x in argv[i].split(",") if x)
        else: sys.stderr.write(f"unknown option: {a}\n"); return 2
        i += 1

    diagram_errors = check_diagrams(sorted(glob.glob(os.path.join(src, "**", "*" + config.source_extension), recursive=True)))
    if diagram_errors:
        sys.stderr.write("\n".join(diagram_errors) + "\n")
        return 1

    internal = set(
        os.path.relpath(p, src)[:-len(config.source_extension)].replace(os.sep, ".")
        for p in glob.glob(os.path.join(src, "**", "*" + config.source_extension), recursive=True))
    config.validate_references(internal)

    corpus = SourceCorpus(config, source_dir=src, highlighted_dir=html_dir)
    rendered = sorted(corpus.documents)
    if LANDING in rendered and html_dir:
        rendered = sorted(corpus.closure({LANDING}))
    rendered_set = set(rendered)
    if not rendered:
        sys.stderr.write(f"no highlighted output in {html_dir}; run `agda --html` first\n")
        return 1
    # Validate author-maintained routes before producing any reader-facing pages.
    reading_data = build_reading_data(src, config.path(config.catalog),
        extension=config.source_extension, previews={LANDING} if LANDING else set(),
        prerequisites=config.values.get('prerequisites'))
    order = {node["id"]: node["order"] for node in reading_data["nodes"]}
    modnav_list = sorted(internal, key=lambda m: (order.get(m, len(order) + 1), m))
    book.replace(reading_data['nodes'])
    pages.ui = interface_copy(config, book)
    publication.ui = interface_copy(config, book)
    glossary_entries = load_entries(config.path(config.glossary)) if config.glossary else []
    term_errors = schema_errors(glossary_entries)
    if term_errors:
        raise ValueError("\n".join(term_errors))
    terms = sort_reader_terms(reader_terms(glossary_entries), reading_data, src, config.source_extension)
    types_raw = json.loads(Path(types_path).read_text(encoding='utf-8')) if os.path.exists(types_path) else {}
    expression_types_raw = (json.loads(Path(expression_types_path).read_text(encoding='utf-8'))
                            if os.path.exists(expression_types_path) else {})
    tpl = Path(tpl_path).read_text(encoding='utf-8')
    project_assets = {}
    for name, path in (('favicon', config.favicon), ('logo', config.logo or config.favicon)):
        if path:
            project_assets[f'assets/{name}.svg'] = config.path(path).read_bytes()
    assets = AssetBundle(static_dir, project_assets=project_assets)
    tpl = assets.template(tpl)

    code = build_code_context(corpus, internal, rendered, semantics, types_raw, expression_types_raw)
    name2pos = code.names
    types_by_module = code.types
    pos_aspect = code.aspects

    if selected_modules:
        unknown = selected_modules - rendered_set
        if unknown:
            sys.stderr.write(f"unknown rendered module(s): {', '.join(sorted(unknown))}\n")
            return 2
        preview_modules = corpus.closure(selected_modules)
        modules_to_render = [m for m in rendered if m in preview_modules]
    else:
        modules_to_render = rendered

    # Render reachable modules; the configured overview supplies the contents page.
    for m in modules_to_render:
        render_module(m, corpus, code=code, terms=terms, template=tpl,
                      out_dir=out_dir, reading=reading_data)

    # A selected-module rebuild is also the fast preview path used while the
    # renderer is being refined.  Publish changed CSS/JS before returning so
    # the cache-busted URL in the rebuilt page always names the served asset.
    if os.path.isdir(static_dir):
        assets.publish(os.path.join(out_dir, "static"))

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

    search_mods = sorted(internal)                   # legacy per-language identifier index for project chapters
    for lang in langs:
        os.makedirs(os.path.join(out_dir, lang), exist_ok=True)
        write_search(out_dir, lang, search_mods, name2pos, pos_aspect, types_by_module)
        write_terms(out_dir, lang, terms)
        with open(os.path.join(out_dir, lang, "reading-routes.json"), "w", encoding="utf-8") as route_file:
            json.dump(reading_data, route_file, ensure_ascii=False)
        # Keep old inbound chapter URLs usable after the source/module rename.
        for old_page, target in config.values.get('legacy_pages', {}).items():
            safe_target = htmllib.escape(target, quote=True)
            legacy = ('<!DOCTYPE html><html lang="' + lang + '"><meta charset="utf-8">'
                      '<meta http-equiv="refresh" content="0;url=' + safe_target + '">'
                      '<link rel="canonical" href="' + safe_target + '">'
                      '<title>' + htmllib.escape(config.name) + '</title>'
                      '<a href="' + safe_target + '">' + htmllib.escape(config.name) + '</a>'
                      '<script>location.replace(' + json.dumps(target).replace('<', '\\u003c') + ')</script></html>')
            with open(os.path.join(out_dir, lang, old_page), 'w', encoding='utf-8') as output:
                output.write(legacy)
    write_root(out_dir, langs, base)
    write_agent_files(out_dir, langs, base, modnav_list)
    graph_result = render_graph(config, reading_data,
        {module: path.read_text(encoding='utf-8') for module, path in corpus.sources.items()}, out_dir, langs)
    if graph_result:
        return graph_result
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


def main(argv=None):
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--project-root', type=Path, required=True)
    args, options = parser.parse_known_args(argv)
    return build_site(SiteConfig.load(args.config, root=args.project_root), options)


if __name__ == '__main__':
    raise SystemExit(main())
