from pathlib import Path
"""Project-configured metadata and machine-readable publication."""
import html as htmllib
import json
import os
import re
from html_contract import *
from markdown_core import *
from site_localization import LANG_LABELS, interface_copy, lang_nav, hreflang_links
from reading_routes import GUIDE_PANEL, own_page, twin_of
from term_registry import TERM_MARK_RE, localized_forms, localized_abbreviation


class Publication:
    def __init__(self, config, book):
        self.config = config
        self.book = book
        self.ui = interface_copy(config, book)

    def page_description(self, module, lang, is_landing, is_external):
        """The page's own <meta name=description>, never the bare site name."""
        if is_external:
            return {
                "en": f"{module}, a module of the Cubical standard library, rendered for reference "
                      f"inside the {self.config.name} textbook.",
                "zh": f"{module}：Cubical 标准库的一个模块，在 {self.config.name} 教科书中渲染以供查阅。",
                "ja": f"{module}：Cubical 標準ライブラリのモジュール。{self.config.name} の教科書内に参照用として"
                      "描画したものです。",
            }[lang]
        if is_landing:
            return self.config.descriptions[lang]
        title = self.book.title(module, lang)
        described = self.book.field(module, "description", lang, title)
        if described.rstrip(".") != title.rstrip("."):
            return described
        # Several catalog entries describe a chapter by restating its title. Repeating that
        # as the page description would leave a search engine and an agent with one fact
        # twice over, so place the chapter instead.
        meta = self.book.meta.get(module, {})
        stage = self.book.field(module, "stage", lang)
        position, total = meta.get("order", 0), len(self.book.meta)
        shape = {
            "en": f"{title}. Chapter {position} of {total} of the {self.config.name} textbook, in the "
                  f"{stage} stage, developed as the Agda module {module}.",
            "zh": f"{title}。{self.config.name} 教科书第 {position} 章，全书共 {total} 章，"
                  f"属于{stage}阶段，对应 Agda 模块 {module}。",
            "ja": f"{title}。{self.config.name} 教科書の第 {position} 章（全 {total} 章）、{stage}段階、"
                  f"Agda モジュール {module} として展開します。",
        }
        return shape.get(lang, shape["en"])


    def footer_html(self, lang, base, md_href):
        """The footer also publishes the page's machine-readable forms.

        The Vercel agent-readability measurements found that agents reach a resource by
        following a link from a page they already have, far more often than by guessing a
        path, so the Markdown twin and llms.txt are linked and not merely declared in the
        head."""
        s = self.ui[lang]
        source = f'<a href="{htmllib.escape(self.config.repository, quote=True)}">{s["source"]}</a>'
        formats = [f'<a href="{base}/llms.txt" title="{htmllib.escape(s["agentstitle"])}">'
                   f'{s["agents"]}</a>']
        if md_href:
            formats.insert(0, f'<a href="{md_href}" title="{htmllib.escape(s["mdtitle"])}" '
                              f'type="text/markdown">{s["markdown"]}</a>')
        links = " · ".join([source, *formats])
        copyright_ = f'© 2026 {htmllib.escape(self.config.publisher)} · {s["license"]} · {links}'
        return (f'<div class="footer-credit">{s["credit"]}</div>'
                f'<div class="footer-copyright">{copyright_}</div>')


    def markdown_mirror(self, woven, code_blocks, module, lang, out_name, langs):
        """The same chapter as plain Markdown: front matter, prose, fenced Agda.

        An agent that follows a link from this site pays for the page it fetches. The HTML
        carries a navigation sidebar, a type sidecar hook and a highlighted token per
        identifier; the Markdown carries the chapter. Both are generated from one master,
        so the mirror cannot drift from the page it mirrors.
        """
        return self.publish_markdown(markdown_body(woven, code_blocks), module, lang, out_name, langs)

    def publish_markdown(self, text, module, lang, out_name, langs):
        """Add site metadata to a complete core Markdown body; do not parse it."""
        meta = self.book.meta.get(module, {})

        def quote(value):
            return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'

        front = [
            "---",
            f"title: {quote(self.book.title(module, lang))}",
            f"module: {module}",
            f"lang: {lang}",
            f"site: {quote(self.config.name)}",
            f"description: {quote(self.book.field(module, 'description', lang))}",
            f"stage: {quote(self.book.field(module, 'stage', lang))}",
            f"reading_order: {meta.get('order', 0)}",
            f"canonical: {self.config.canonical}/{lang}/{out_name}",
            f"html: {self.book.href(module)}",
            f"agda_source: {self.config.source_url(module)}",
            "prerequisites: [" + ", ".join(meta.get("prerequisites", [])) + "]",
            "routes: [" + ", ".join(meta.get("routes", [])) + "]",
            "translations: [" + ", ".join(
                f"{self.config.canonical}/{other}/{twin_of(out_name)}"
                for other in langs if other != lang) + "]",
            f"agent_guide: {self.config.base_url}/llms.txt",
            f"license: {quote(self.config.license['name'])}",
            "---",
            "",
        ]
        return "\n".join(front) + text.rstrip("\n") + "\n"


    def json_ld(self, module, lang, out_name, langs, is_landing, is_external, has_mirror):
        """One schema.org graph per page: this chapter, and the book it is a chapter of."""
        url = f"{self.config.canonical}/{lang}/{out_name}"
        book = {
            "@type": "Book",
            "@id": f"{self.config.canonical}/#book",
            "name": self.config.name,
            "url": self.config.canonical + "/",
            "inLanguage": list(langs),
            "description": self.config.descriptions.get(lang, self.config.descriptions["en"]),
            "about": self.config.topics,
            "license": self.config.license['url'],
            "author": {"@type": "Organization", "name": self.config.publisher, "url": self.config.repository},
            "isAccessibleForFree": True,
        }
        page = {
            "@type": "TechArticle",
            "@id": url,
            "url": url,
            "name": self.book.title(module, lang) if not is_landing else self.config.name,
            "headline": self.book.title(module, lang),
            "description": self.page_description(module, lang, is_landing, is_external),
            "inLanguage": lang,
            "isPartOf": {"@id": f"{self.config.canonical}/#book"},
            "license": self.config.license['url'],
            "programmingLanguage": {"@type": "ComputerLanguage", "name": "Cubical Agda",
                                    "url": "https://github.com/agda/cubical"},
            "isAccessibleForFree": True,
        }
        if not is_external:
            page["identifier"] = module
            position = self.book.meta.get(module, {}).get("order")
            if position:
                page["position"] = position
            page["codeRepository"] = self.config.source_url(module)
        if has_mirror:
            # the twin of this page, which for a preview chapter is the guide's twin
            page["encoding"] = {"@type": "MediaObject", "encodingFormat": "text/markdown",
                                "contentUrl": f"{self.config.canonical}/{lang}/{twin_of(out_name)}"}
        graph = {"@context": "https://schema.org", "@graph": [page, book]}
        payload = json.dumps(graph, ensure_ascii=False, separators=(",", ":"))
        return ('  <script type="application/ld+json">'
                + payload.replace("<", "\\u003c") + "</script>")


    def page_config(self, module, lang, page_name, md_name, base, site, is_landing, is_external):
        """`window.bedrock`: what the page's own scripts are allowed to assume about it.

        The ask-an-assistant handover is assembled in the browser from these fields, so
        whatever it says about a chapter (its title, its stage, its place in the reading
        order, where its Agda master lives) is the same thing llms.txt and the Markdown
        twin say. Nothing here is derived from the DOM."""
        meta = self.book.meta.get(module, {})
        config = {
            "baseUrl": base,
            "lang": lang,
            "module": "guide" if is_landing else module,
            "site": site,
            "description": self.config.descriptions[lang],
            "canonical": f"{self.config.canonical}/{lang}/{page_name}",
            "chapter": module,
            "title": self.book.title(module, lang),
            "stage": self.book.field(module, "stage", lang),
            "order": meta.get("order", 0),
            "chapters": len(self.book.meta),
            "prerequisites": meta.get("prerequisites", []),
            "markdown": md_name,
            "guide": f"{base}/llms.txt",
            "repository": self.config.repository,
            "external": is_external,
            "storageNamespace": self.config.storage_namespace,
            "agentCopy": self.config.agent.get('translations', {}).get(lang, {}),
        }
        if not is_external:
            config["agdaSource"] = self.config.source_url(module)
        payload = json.dumps(config, ensure_ascii=False, separators=(",", ":"))
        return payload.replace("<", "\\u003c")


    def agent_guide(self, langs, modnav_list):
        """llms.txt: what the site is, how it is addressed, and what an agent can fetch."""
        lang = langs[0]
        lines = [self.config.agent.get("guide", "# {site}\n\n{blurb}\n").format(
            site=self.config.name, blurb=self.config.descriptions.get('en', self.config.descriptions[lang]))]
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
             "every Agda identifier this project defines, with its module, its anchor on that "
             "module's page, its syntactic aspect and its type."),
            (f"/{lang}/types/<Module>.json",
             "the elaborated type of every token of one chapter, keyed by the anchor that "
             "token carries in that chapter's URL."),
            ("/sitemap.xml", "every page, in every language, with hreflang alternates."),
            ("/robots.txt", "crawl policy. Nothing on this site is disallowed."),
        ]
        for path, what in endpoints:
            lines.append(f"- [{path}]({self.config.canonical}{path}): {what}")
        lines.append("")
        lines.append("## Source")
        lines.append("")
        lines.append(f"- [{self.config.repository}]({self.config.repository}): the repository. "
                     f"A chapter master is at `{self.config.sources}/<Module path>{self.config.source_extension}`.")
        for link in self.config.values.get('source_links', []):
            url = link['url']
            lines.append(f"- [{url}]({url}): {link['description']}")
        lines.append("")
        lines.append("## Chapters, in reading order")
        lines.append("")
        lines.append("Links point at the Markdown mirrors. Replace `/en/` with `/zh/` or `/ja/` "
                     "for the Chinese or Japanese edition, and `.md` with `.html` for the page a "
                     "human reads. A chapter that is not read at the page its own name gives "
                     "says where it is read.")
        lines.append("")
        for module in modnav_list:
            meta = self.book.meta.get(module, {})
            stage = self.book.field(module, "stage", lang)
            title = self.book.title(module, lang)
            desc = self.book.field(module, "description", lang)
            position = meta.get("order", 0)
            page = meta["page"]
            entry = (f"- [{position}. {title}]({self.config.canonical}/{lang}/{twin_of(page)}) "
                     f"(`{module}`, {stage})")
            # Nearly every chapter is read at the page its own name gives, and saying so
            # 121 times would be noise. A chapter that is read somewhere else says where.
            if page != own_page(module):
                entry += f", read at {self.config.canonical}/{lang}/{self.book.href(module)}"
            if desc.rstrip(".") != title.rstrip("."):
                entry += f": {desc}"
            lines.append(entry)
        lines.append("")
        lines.append("## Other editions")
        lines.append("")
        for other in langs[1:]:
            lines.append(f"- [{LANG_LABELS[other]}]({self.config.canonical}/{other}/index.html): the same "
                         f"book. Chapter mirrors are at `/{other}/<Module>.md`.")
        lines.append("")
        return "\n".join(lines)


    def write_agent_files(self, out_dir, langs, base, modnav_list):
        """robots.txt, sitemap.xml, llms.txt and the Cloudflare header rules."""
        guide = self.agent_guide(langs, modnav_list)
        Path(os.path.join(out_dir, "llms.txt")).write_text(guide, encoding='utf-8')
        well_known = os.path.join(out_dir, ".well-known")
        os.makedirs(well_known, exist_ok=True)
        Path(os.path.join(well_known, "llms.txt")).write_text(guide, encoding='utf-8')

        Path(os.path.join(out_dir, "robots.txt")).write_text(f"# {self.config.name}. Everything here is public and nothing is disallowed, to crawlers and\n"
            "# to AI agents alike. /llms.txt is the guide written for an agent; every chapter\n"
            "# page also has a plain-Markdown twin at the same path with a .md extension.\n"
            "User-agent: *\n"
            "Allow: /\n"
            "\n"
            f"Sitemap: {self.config.canonical}/sitemap.xml\n", encoding='utf-8')

        # One entry per page that exists, in reading order after the guide. A preview
        # chapter shares the guide's page and is not a second URL for a crawler to weigh
        # against it, so the dedupe is what keeps it out.
        pages = list(dict.fromkeys(
            ["index.html"] + [self.book.meta[m]["page"] for m in modnav_list]))
        urls = []
        for lang in langs:
            for page in pages:
                alternates = "".join(
                    f'\n    <xhtml:link rel="alternate" hreflang="{other}" '
                    f'href="{self.config.canonical}/{other}/{page}" />' for other in langs)
                urls.append(f"  <url>\n    <loc>{self.config.canonical}/{lang}/{page}</loc>{alternates}\n  </url>")
        Path(os.path.join(out_dir, "sitemap.xml")).write_text('<?xml version="1.0" encoding="UTF-8"?>\n'
            '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9"\n'
            '        xmlns:xhtml="http://www.w3.org/1999/xhtml">\n'
            + "\n".join(urls) + "\n</urlset>\n", encoding='utf-8')

        # Cloudflare Pages reads `_headers` from the deployed root. Without it a .md twin
        # arrives as a download rather than as text an agent can read, and a fetch from
        # another origin cannot reach the JSON endpoints at all.
        Path(os.path.join(out_dir, "_headers")).write_text("/*.md\n"
            "  Content-Type: text/markdown; charset=utf-8\n"
            "  Access-Control-Allow-Origin: *\n"
            "/llms.txt\n"
            "  Content-Type: text/markdown; charset=utf-8\n"
            "  Access-Control-Allow-Origin: *\n"
            "/.well-known/llms.txt\n"
            "  Content-Type: text/markdown; charset=utf-8\n"
            "  Access-Control-Allow-Origin: *\n"
            "/*.json\n"
            "  Access-Control-Allow-Origin: *\n", encoding='utf-8')


    def write_search(self, out_dir, lang, modules, name2pos, pos_aspect, types_by_module):
        entries = []
        for m in modules:
            entries.append({"name": self.book.title(m, lang), "module": m,
                            "kind": "chapter", "type": self.book.field(m, "description", lang),
                            "href": self.book.href(m)})
            for name, pos in name2pos.get(m, {}).items():
                t = types_by_module.get(m, {}).get(pos, "")
                entries.append({"name": name, "module": m, "anchor": pos,
                                "chapter": self.book.title(m, lang), "kind": "definition",
                                "aspect": pos_aspect.get(m, {}).get(pos, ""),
                                "type": re.sub(r"<[^>]+>", "", t),
                                "href": self.book.href(m, f"#{pos}")})
        Path(os.path.join(out_dir, lang, "search.json")).write_text(json.dumps(entries, ensure_ascii=False), encoding='utf-8')


    def write_terms(self, out_dir, lang, terms):
        payload = {}
        for entry in terms:
            module = entry["introduced_in"]
            payload[entry["id"]] = {
                "label": entry[lang],
                "recap": entry[f"recap_{lang}"],
                "chapter": self.book.title(module, lang),
                "href": self.book.href(module, f'#term-{entry["id"]}'),
            }
            abbreviation = localized_abbreviation(entry, lang)
            if abbreviation:
                payload[entry["id"]]["abbreviation"] = abbreviation
        with open(os.path.join(out_dir, lang, "terms.json"), "w", encoding="utf-8") as target:
            json.dump(payload, target, ensure_ascii=False)


    def write_root(self, out_dir, langs, base):
        """The site root and the 404 page.

        A browser is sent straight to its own language. A fetch-only client that runs no
        JavaScript, which is what an agent usually is, still gets a page that says what this
        is and links every edition and the agent guide, rather than an empty redirect shell.
        """
        default = langs[0]
        links = "\n".join(
            f'    <li><a lang="{L}" hreflang="{L}" href="{base}/{L}/index.html">'
            f'{LANG_LABELS[L]}</a>: {htmllib.escape(self.config.descriptions[L])}</li>' for L in langs)
        page = f"""<!DOCTYPE html>
    <html lang="{default}">
    <head>
      <meta charset="utf-8" />
      <meta name="viewport" content="width=device-width, initial-scale=1.0" />
      <title>{htmllib.escape(self.config.name)}</title>
      <meta name="description" content="{htmllib.escape(self.config.descriptions[default], quote=True)}" />
      <link rel="canonical" href="{self.config.canonical}/" />
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
        <h1>{htmllib.escape(self.config.name)}</h1>
        <p>{htmllib.escape(self.config.descriptions[default])}</p>
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
        Path(os.path.join(out_dir, "index.html")).write_text(page, encoding='utf-8')
        Path(os.path.join(out_dir, "404.html")).write_text(page, encoding='utf-8')
