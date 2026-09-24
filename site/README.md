# Bedrock website instance

This directory contains Bedrock's website configuration and brand assets, not the
reusable renderer or browser implementation. The framework is
[Outcrop](https://github.com/BedrockInstitute/Outcrop), pinned as the `outcrop/`
Git submodule. Follow [AGENTS.md](../AGENTS.md) and the current write scope.

## Responsibilities

| Bedrock owns | Outcrop owns |
| --- | --- |
| `site/project.json`, `site/static/assets/` | Outcrop Core: Markdown, multilingual structure, optional compiler semantics and pure lint engines |
| `src/`, `dev/reading-catalog.json`, `dev/glossary.toml` | Outcrop Site: complete page shell, routes, graph, search, appearance, hover/modal, notes, diagrams, Ask AI and publication |
| Compiler installation, trace/cache workflow, mathematical gates and deployment | Installed templates, browser resources, compiler-data adapters and generic site lint |

The public API is `from outcrop.core import MarkdownDocument, CodeContext` and
`from outcrop.site import SiteConfig, build_site`. Shared source lives under
`outcrop/src/outcrop/`; resources are in `outcrop/src/outcrop/site/resources/`,
with `static/outcrop.js`, `static/outcrop.css`, templates, fonts and vendor assets.
Do not add a second implementation under this directory.

Framework references:

- [Architecture and interaction contracts](../outcrop/docs/ARCHITECTURE.md)
- [Markdown input and optional compiler evidence](../outcrop/docs/RENDERER-MARKDOWN.md)
- [Reusable authoring recipes](../outcrop/docs/RENDERER-RECIPES.md)
- [Configuration, CLI and independent project](../outcrop/docs/SITE-CONFIG.md)

## Install and build

From the Bedrock repository root:

```sh
git submodule update --init --recursive
make venv
make site
make serve
```

`make venv` installs the pinned developer requirements and the local Outcrop
package in editable mode. An existing environment can install it explicitly with
`.venv/bin/python -m pip install -e ./outcrop`. Reinitialize submodules after a
fresh clone and update them to the revision recorded by the consuming commit;
do not silently track an unpinned framework branch.

`make site` builds highlighted Agda and semantic data, then renders all editions
into `_build/site`. `make site-render SITE_OUT=...` only renders existing backend
data and is appropriate for a renderer-only change. It does not replace compiler
regeneration when source or trace contracts change. `LANGS`, `BASE_URL` and
`SITE_OUT` remain the instance's Make overrides.

The thin commands in `scripts/site/` supply Bedrock-specific paths and policies.
The common tools are package commands:

```sh
.venv/bin/python -m outcrop lint --config site/project.json --project-root .
.venv/bin/python -m outcrop check-links _build/site
.venv/bin/python scripts/tests/check-search-index.py _build/site
```

## Instance policy

`site/project.json` supplies the visible name, publisher, icons, source/canonical
URLs, deployment prefix, licenses, agent text and storage namespace. Bedrock
retains `storage_namespace: "bedrock"`, preserving existing theme, palette, route,
language and completion preferences. The shared browser transport is now
`window.outcrop`; its name does not determine preference keys.

The source corpus remains `.lagda.md`. `Base.Prelude` is the explicit teaching
vocabulary forwarding point. `Origin` is the configured overview embedded at
`index.html#milestones`; definition fragments still resolve to their own anchors
within that page. Its numbered results and visible public re-exports are explicit
instance exceptions. The chapter catalog owns translated titles, routes, order
and human-review status. Never set review badges merely because a test passes.

`policies.level_name_convention: true` records the book-wide convention that `ℓ`
with its supported suffixes denotes a universe-level parameter. Outcrop defaults
this policy to false. Primitive shortening still needs semantic evidence; the
convention does not authorize guessed AST nodes or change the original code.

Statements retain the same Markdown and lint rules. Visually, the exact `∎` is a
semi-transparent mark inside the final code frame; code occupies the full width
of its containing column without an external QED gutter or left outdent. Folded
submodules retain their own indented columns and compact declaration headers.
See the shared recipes rather than adding chapter-specific layout fixes.

## Acceptance and historical evidence

`make check` includes reusable and instance lint plus both test suites, but does
not browser-test the website. `make milestone-lint` remains the additional Origin
closure gate. A website change also needs fresh rendering, link/search validation
and actual browser interaction against that output.

Bedrock's content-dependent browser fixtures remain under `scripts/tests/`.
Serve them with `scripts/tests/serve-boilerplate-regression.py --site <output>`;
redirect server stdout/stderr to a task log. Run fixtures sequentially with the
tested tab active, and record the production runtime hash. Outcrop's independent
example and browser fixture live under `outcrop/examples/renderer/` and
`outcrop/tests/`; its fixture builder is
`outcrop/scripts/build-renderer-fixtures.py`.

[The Bedrock architecture record](../dev/SITE-ARCHITECTURE.md) retains the previous
refactor's exact parity, Chrome and incomplete Safari evidence. Those dated runs
are historical results, not acceptance of the Outcrop extraction or subsequent
QED, mobile code-reading, search and hover changes. New UI acceptance must be
recorded separately. Narrow desktop Chrome and synthetic touch events do not
establish real iPhone Safari behavior.

Bedrock brand/content licensing remains in [REUSE.toml](../REUSE.toml) and
[NOTICE](../NOTICE); Outcrop maintains its own inherited software, font and vendor
attributions. Moving an implementation does not relicense it.
