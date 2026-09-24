# Bedrock website architecture

Bedrock is an instance of [Outcrop](../outcrop/docs/ARCHITECTURE.md), pinned in
the `outcrop/` submodule. Outcrop Core and Outcrop Site own reusable implementation;
this document defines Bedrock's adapter/gate mapping and verification requirements.
The [instance guide](README.md) describes local installation and operation.

## Current ownership

| Boundary | Owner | Inputs and lifetime |
| --- | --- | --- |
| Outcrop Core | `outcrop.core.MarkdownDocument`, `CodeContext`; pure structure, semantic and lint modules | Explicit text and optional compiler evidence; no project discovery or Site dependency |
| Semantic package integration | `outcrop.site.site_inputs.SourceCorpus`, `compiler_index.build_code_context` | Explicit source/highlighted documents, signatures and Unicode ranges; one join per build |
| Optional Agda producer | `outcrop.adapters.agda` | Compiler overlay/version lock/build, explicit library installer and parallel trace scheduler; never invoked by ordinary render/lint |
| Outcrop Site | `outcrop.site.SiteConfig`, `build_site`, catalog/page/publication/route/graph owners | Validated instance state; identical complete website features for each project |
| Packaged browser resources | `outcrop/src/outcrop/site/resources/` | Templates, `outcrop.js`, `outcrop.css`, feature modules, fonts and vendor files |
| Asset publication | `outcrop.site.assets.AssetBundle` | Captured byte snapshot; one immutable runtime generation |
| Bedrock instance | `site/project.json`, `site/static/assets/`, `src/`, catalog/glossary, Makefile and gate adapters | Brand, content, mathematical policies, compiler/cache workflow and deployment |

Core returns usable HTML, outline and Markdown. PageRenderer consumes one explicit
CodeContext; Publication adds metadata rather than reinterpreting source Markdown.
The browser features share semantic targets, hover branches, definition history,
coordinate transforms and preferences. See Outcrop's architecture for the full
owner and interaction contracts instead of maintaining a second framework guide here.

The old private `render-site.py` Python facade is removed. The remaining Bedrock
command is a small configuration adapter; genuine callers import the installed
package. Independent tests/examples are under `outcrop/tests/` and
`outcrop/examples/renderer/`; Bedrock-content tests remain under `scripts/tests/`.

## Gate mapping

`make check` exercises the reusable
`site-lint-gate`. The ordinary and supplemental gates have different scopes:

| Existing gate | Shared implementation | Instance policy / invocation |
| --- | --- | --- |
| `typecheck` | Agda adapter/build workflow, not Markdown lint | Bedrock entry `src/Origin.lagda.md`, Cubical/version/safety and memory budget remain in Makefile |
| `lint-prose-gate` | `prose_lint`, `statement_structure`, `submodule_structure` | Master-vs-development-document scope, exact legacy lines and allowed Origin theorem numbers injected by adapter |
| `lint-agda-gate` | `agda_lint.AgdaPolicy`, `lint_text` | OPTIONS, prelude names, hub/empty-family/projection conventions from config |
| `host-lem-gate` | Not a general Markdown rule | Bedrock's classified mathematical inventory remains `check-host-lem.py`, still called by `make check` |
| `glossary-gate` | `glossary_lint`, `term_registry` | Explicit glossary forms and exact prose discovery scope |
| `term-gate` | `term_lint.check_terms` | Configured catalog, glossary and source map; forward explicit references preserve their exception |
| `fences-gate` | `fence_lint` | Source discovery remains instance-specific; shared code never discovers `src` |
| `diagrams-gate` | `diagram_style` | Shared semantic CSS/figure rules, no project mathematics |
| `reading-order-gate` | `reading_order`, `source_syntax` | Explicit catalog and overview chapters |
| `routes-gate` | `reading_routes` | Explicit catalog, source extension, overview and prerequisite overrides |
| `chapters-gate` | `outline_lint`, `chapter_structure` | Formal setup policy and explicit visible-import exceptions |
| `i18n-gate` | `i18n_markers.lint_markers` | Instance source discovery only |
| `test` | Python and Node contract tests | Existing behavior retained; behavioral contracts listed below |
| `milestone-lint` (push/CI) | Source reachability algorithm | Bedrock's entry-closure requirement remains `check-milestone-consumption.py --root Origin` |
| Literary exposition audit (supplemental) | `literary_lint.analyze_text`; generic `python -m outcrop lint --literary` | Exact source setup and configured module set; not silently promoted to a whole-tree gate while the prose project is incomplete |

Generic `lint_site(config, project_checks=...)` also accepts explicit callable
project checks returning diagnostics. Configuration cannot execute arbitrary
commands. Bedrock continues to call its mathematical gates directly from Makefile;
another project supplies its own domain checks without editing the shared rules.
The optional literary audit preserves per-language counts and 1..5-line structural
checks; counts are not evidence of mathematical correctness.

The generated `outcrop/examples/renderer/semantic/` package is compiler output, not
authored Markdown. Bedrock prose discovery does not traverse the independent submodule;
the corresponding `outcrop/examples/renderer/chapters/` masters remain checked by the
strict reusable lint and independent build tests.

## Test ownership

Outcrop owns synthetic rule and interaction tests. Bedrock tests cover its actual
catalog, corpus, editorial exceptions and mathematical gates. Permanent lint
checks enforce chapter openings and same-line `private module` declarations;
completed migration scripts are not part of the build or test workflow.

## Acceptance matrix

| Area | Retained contract | Verification |
| --- | --- | --- |
| Code surfaces | one target identity, real compiler ranges, leaves, syntax, recursive help, stop rules | unit contracts; boilerplate/universe browser fixtures; direct interactions |
| Hover | ancestor delays, downward positioning, persistent touch, smaller/larger nodes, cleanup | lifecycle contracts; sequential browser fixtures |
| Definitions | full page, target history, redirect identity, block alignment, loading cancellation, theme, normal links | modal contracts; browser regression and manual navigation |
| Navigation | sidebar/sticky tree hit regions, drawer focus, routes, completion, tabs, languages | directory fixture and direct keyboard/click tests |
| Content | terms, notes, QED, folds, gutters, source text, Unicode fonts, diagrams | existing renderer gates; padding/fonts fixtures; direct animations |
| Search | cross-language prose/terms/sections/all Agda and Cubical, worker, empty/error states | index checker; direct multilingual/code search |
| Appearance | prepaint, all palettes, independent light/dark preference, dynamic/modal inheritance | appearance fixture; direct toggle |
| Agent layer | Ask AI, selection, passage anchors, Markdown, llms, sitemap, redirects | unit contracts; direct Ask AI and generated-link verification |
| Dependency graph | all layouts/edge modes, selection, keyboard, drag/zoom/fullscreen | graph tests and direct browser actions |
| Reusable renderer | ordinary .md, alternate brand/icon/paths, optional semantics, no project leakage | independent fixture build and browser interactions |
| Publication | static host, base path, immutable dependent assets, redirects and licenses | asset tests, full build, link check |
| Mathematical source | unchanged Agda and literate source | diff scope; make check; milestone-lint |

New browser acceptance must name browser, viewport or fixture width, language and
actions. Simulated touch and narrow embedded frames are not iPhone Safari evidence.
