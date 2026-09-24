# Textbook site configuration, version 1

There are two reusable layers: `MarkdownDocument` renders an in-memory document;
`website.build_site(SiteConfig, argv)` builds the entire interactive textbook.
Bedrock is an instance described by `site/project.json`. Another Agda textbook
uses the same templates, modules, styles, graph, lint and publication code. It
does not copy a Bedrock-specific shell.

## Independent build

```sh
.venv/bin/python scripts/site/website.py \
  --config examples/renderer/project.json --project-root examples/renderer \
  --out _build/renderer-fixture/academy
.venv/bin/python scripts/site/site_lint.py \
  --config examples/renderer/project.json --project-root examples/renderer
```

Serve `_build/renderer-fixture` and open `/academy/en/index.html`. This example is
Lantern Notes, three ordinary `.md` chapters with a different icon, source path,
module vocabulary, license, canonical origin and storage namespace. Its checked
Agda semantic package is committed as fixture data, so these commands need no
Agda installation. The tiny code demonstrates only a marker datatype and identity
applications, not unverified category-theoretic claims. To refresh its compiler
package use `examples/renderer/refresh_semantics.py --help`; refreshing is a
separate optional adapter step, not a hidden build dependency.

`website.py` is the generic CLI. `render-site.py` retains the existing Bedrock CLI
and lazily initializes its legacy Python facade only when requested. Passing
`--config ... --project-root ...` works through either CLI without a Bedrock
configuration file. The tests copy the distribution without `src`, `dev` or
`site/project.json`, set `PATH=/no-toolchain`, and build/lint the example there.

## Data and validation

All input paths are relative POSIX paths confined to the explicit project root,
including resolved symlinks. `..`, absolute paths, URL-like input paths and NUL
are rejected. Configuration cannot request Python imports or arbitrary executable
providers. URLs are HTTP(S), without embedded credentials. Brand labels are text,
not HTML. Trusted authored Markdown/SVG remain trusted content; configuration is
not a sandbox for executing untrusted authors' documents.

| Field | Meaning |
| --- | --- |
| `version` | Required integer `1` |
| `name`, `publisher` | Visible site and copyright identity |
| `storage_namespace` | Preference isolation; Bedrock explicitly retains `bedrock` |
| `languages` | Nonempty unique subset of `en`, `zh`, `ja` |
| `canonical` | Public origin plus optional deployment path, no trailing slash |
| `base_url` | Local absolute path prefix, e.g. `/academy`, or empty |
| `repository`, `source_tree` | Optional source repository and chapter source-root URLs |
| `sources`, `source_extension` | Source root and `.md` (default) or `.lagda.md` |
| `catalog` | Complete chapter, stage and reading-route JSON |
| `glossary` | Optional glossary TOML; absent means no project terminology |
| `highlighted`, `types`, `expression_types` | Optional compiler package paths |
| `favicon`, `logo` | Required project SVG favicon; optional logo defaults to that explicit asset |
| `landing_module` | Overview chapter embedded in the interactive contents |
| `prelude_module` | Optional teaching-vocabulary reexport point; empty disables forwarding |
| `hubs` | Graph hub modules, explicitly validated against the corpus |
| `visible_import_chapters` | Explicit formal-setup exceptions for visible theorem imports |
| `prerequisites` | Optional per-chapter overrides; omitted chapters keep their inferred imports |
| `descriptions` | Text for each enabled language |
| `topics` | Site-level metadata keywords |
| `license` | Required `name` and HTTP(S) `url` |
| `legacy_pages` | Flat old `.html` filenames mapped to local target pages/anchors |
| `source_links` | Extra agent-guide references: `url`, `description` |
| `agent.guide` | Project-specific AI reading guidance |
| `agent.translations` | Optional localized `docTitle`, `intro`, `hProject`, `fLibrary`, `project`, `want` copy |
| `policies` | Explicit `formal_setup` and `trilingual` booleans, strict by default |
| `agda_policy` | Required options, bare-open hubs, prelude public-name data, empty-family and projection conventions |
| `variable_legacy` | Optional versioned exact legacy inline-variable allowances |
| `numbered_theorems` | Explicit chapter-to-number-list allowances |

Catalog entries retain stable module IDs separately from localized titles. They
include order, stage, titles/descriptions, routes and human-review status. Routes
may overlap, but cannot repeat a chapter within one route. All ordinary chapters
must be covered. Prerequisites come from fenced imports unless explicitly
supplied. A configured overview has no readiness prerequisites; no chapter name
receives that exception implicitly. `reading_routes.validate_metadata` and
`SiteConfig.validate_references` are callable without initializing a project.

`--site`, `--langs` and `--base-url` overrides produce a single effective config
before any renderer, graph or publisher is constructed. `--base-url` changes local
deployment paths, not the independently declared public `canonical` origin.
Supply a matching canonical when moving a published site. `--module` is a scoped
preview build, not a complete publish; it includes compiler dependencies and
refreshes assets/type sidecars. The Makefile's `site` target remains Bedrock's
backend-plus-website adapter.

## Isolation and compatibility

Each build owns `BookCatalog`, `Publication`, `PageRenderer`, `CodeContext` and
`AssetBundle`; no mutable book metadata is reused by another build. Browser keys
are namespace-prefixed. This includes theme, light/dark palettes, language,
completion and selected route. Existing Bedrock preference keys are unchanged.
The fixture tests build Lantern, Prism, then Lantern in one Python process and
check brand, source URLs, canonical metadata, agent output, assets and storage.

The internal `window.bedrock` transport name, legacy CSS classes and modal query
keys remain for compatibility. They are protocol identifiers, not a hidden brand
or source-discovery dependency. The visible brand, icon, copyright, source URLs,
module exceptions and Ask AI project text are supplied by configuration.

## Lint and publication

`site_lint.lint_site(config)` returns structured diagnostics. Its strict shared
rules cover language grammar, parallel outlines, statements/QED, folds, syntax
safety/style, glossary forms, term introductions, prerequisite order, chapter
setup, figures and fence boundaries. Project mathematical policies are additional
gates, not silently disabled generic rules; the complete original gate mapping is
in [SITE-ARCHITECTURE.md](SITE-ARCHITECTURE.md). Neither rendering nor lint runs
Agda automatically. A project's proof gate invokes its selected compiler itself.

The output is ordinary static files. The shared publisher emits relative
language links, canonical/JSON-LD metadata, source links, Markdown mirrors,
`llms.txt`, sitemap, robots, `_headers` and redirects. Hosting credentials and
deployment commands belong to the instance's build/deployment workflow. This
refactor does not deploy or change Bedrock's host, nor require a new server.
