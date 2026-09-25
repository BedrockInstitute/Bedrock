# Bedrock website instance

This directory owns Bedrock's durable book/site configuration, authoring
specifications, editorial metadata and brand assets, not reusable implementation.
It is not limited to static assets. Temporary development work belongs in
`dev/` and must be cleaned up when finished. The framework is
[Outcrop](https://github.com/BedrockInstitute/Outcrop), pinned as the `outcrop/`
Git submodule. Follow [AGENTS.md](../AGENTS.md) and the current write scope.

## Responsibilities

| Bedrock owns | Outcrop owns |
| --- | --- |
| `site/project.json`, `site/static/assets/` | Outcrop Core: Markdown, multilingual structure, optional compiler semantics and pure lint engines |
| `src/`, `site/reading-catalog.json`, `site/glossary.toml` | Outcrop Site: complete page shell, routes, graph, search, appearance, hover/modal, notes, diagrams, Ask AI and publication |
| Library lock, entry/options, resource/cache policy, mathematical gates and deployment | Optional Agda toolchain/trace producer, weaving, metrics, templates, browser resources and generic site lint |

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

## Persistent instance files

| Files | Purpose |
| --- | --- |
| `project.json`, `static/assets/` | Website identity, framework inputs and branding |
| `reading-catalog.json`, `TEACHING.md` | Chapters, routes, review status and teaching architecture |
| `glossary.toml`, `GLOSSARY.md` | Canonical terminology and its maintenance contract |
| `STYLE-agda.md`, `STYLE-i18n.md` | Formal-code and trilingual authoring rules |
| `agda-libraries.json`, `AGDA-ENVIRONMENT.md` | Dependency lock and compiler/build policy |
| `host-lem-inventory.json`, `inline-agda-legacy.json` | Proof classification and narrowly scoped lint allowances |
| `inline-latex-approvals.json` | Explicit occurrence approvals and temporary allowances ending at human review; no automatic legacy exemptions |
| `ARCHITECTURE.md` | Instance boundaries, gate mapping and verification requirements |
| `ci-docs.json` | Conservative CI documentation-only allowlist; unknown changes retain full checks |

The proof and prose gates consume these same files even when no website is built.
Directory ownership does not make configuration dependent on running a renderer.

Inline LaTeX is otherwise restricted to standalone displays, figures and
figure-explanation paragraphs using `图中的` / `in the figure` / `図中の`.
This mechanical allowance is local to the paragraph, not a human approval. The
active inventory is [dev/INLINE-LATEX-REVIEW.md](../dev/INLINE-LATEX-REVIEW.md);
unreviewed occurrences fail lint unless an explicit temporary allowance is active
while the chapter's catalog flag is `human_reviewed: false`. Text edits and bulk
replacements are allowed; changing that flag to true ends the allowance. The
first four chapters remain strict. See [STYLE-i18n.md](STYLE-i18n.md)
for the authoring rule and the Outcrop configuration contract for review keys.

## Install and build

From the Bedrock repository root:

```sh
git submodule update --init --recursive
make bootstrap
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

On a fresh machine, install GHC/Cabal, `make`, `patch` and Python 3.11+ first.
`make bootstrap` includes `make venv` and installs the local compiler/libraries;
the separate `make venv` is useful when only updating Python dependencies.

The thin commands in `scripts/site/` supply Bedrock-specific paths and policies;
the [scripts index](../scripts/README.md) maps them to gates and browser fixtures.
The common tools are package commands:

```sh
.venv/bin/python -m outcrop lint --config site/project.json --project-root .
.venv/bin/python -m outcrop check-links _build/site
.venv/bin/python -m outcrop check-search _build/site
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
The preface uses mathematical `V` in the broad foundational sense, without an
Agda link or code styling. The milestones' formal model `V` retains its semantic
links and definition inspection.

On compact screens, explicit language and search icon buttons reveal their
controls; scrolling never toggles the search field. A code-block touch commits
AST highlighting and its help only on a completed tap or stationary hold, not
at touch-down when the gesture might become native scrolling.

`policies.level_name_convention: true` records the book-wide convention that `ℓ`
with its supported suffixes denotes a universe-level parameter. Outcrop defaults
this policy to false. Primitive shortening still needs semantic evidence; the
convention does not authorize guessed AST nodes or change the original code.

Statements and proofs retain their labels and code requirements, but Markdown
contains no standalone QED marks. Compiler-certified signature/equation
definitions receive the exact `∎` at their final code line, including definitions
in submodules but excluding where-local helpers. The semi-transparent overlay
reserves no line or padding and has fixed opacity 0.25, even over code. Proof
prose stays close to its associated code through ordinary structural CSS; code occupies the full width
of its containing column without an external QED gutter or left outdent.
Code frames grow vertically and scroll only horizontally. Folded
submodules retain their own indented columns and compact declaration headers.
See the shared recipes rather than adding chapter-specific layout fixes.

## Verification

`make check` includes pure Agda typechecking, reusable and instance lint, and both test suites, but does
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

[The Bedrock architecture guide](ARCHITECTURE.md) defines the gate
mapping and browser acceptance matrix. Record fresh results with each change;
past runs do not certify new code. Narrow desktop Chrome and synthetic touch
events do not establish real iPhone Safari behavior.

CI keeps lint, tests and the Origin closure check on every push/PR. Confirmed
documentation-only changes skip Agda and deployment; source, configuration,
assets, workflow or unknown changes take the full path. Manual dispatch always
runs fully. This does not change local Make targets; see the
[workflow guide](../.github/workflows/README.md) for comparison and cache rules.

Bedrock brand/content licensing remains in [REUSE.toml](../REUSE.toml) and
[NOTICE](../NOTICE); Outcrop maintains its own inherited software, font and vendor
attributions. Moving an implementation does not relicense it.
