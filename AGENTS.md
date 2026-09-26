# AGENTS.md

This is the shared instruction file for agents working in this repository.
Follow the current user request; do not resume an old writing, proof-reduction or
website task merely because a historical report names a restart point.

## Project and sources of truth

Bedrock is a trilingual mathematics textbook and a machine-checked development
of set theory in Cubical Agda. The constructible universe satisfies ZFC and GCH:
`L⊨ZFC` in `src/L/Model.lagda.md` and `L⊨GCH` in
`src/L/GCH/Theorem.lagda.md` each require only `LEM (ℓ-suc ℓ)`, besides
their universe parameter. Both are re-exported by `src/Origin.lagda.md`.
Preserve their statements, assumptions, safety and opacity boundaries.

The interactive website uses Outcrop, pinned in the `outcrop/` Git submodule.
Outcrop Core is the reusable document engine; Outcrop Site is the complete
interactive textbook framework. Bedrock's content and branding are one instance,
not implicit defaults for either layer.

`site/` owns durable instance configuration, authoring specifications and editorial
metadata, including the policies used by non-website proof/prose checks. `dev/`
is a working area for research and active investigations, not a permanent config
store. Promote lasting decisions into `site/` or the source book, then remove
completed one-off scripts and reports. Preserve referenced research evidence.

Read the relevant specifications before changing an area:

| Area | Source of truth |
| --- | --- |
| Mathematical modules and dependencies | Actual definitions and imports under `src/`; `site/TEACHING.md` for the parallel teaching architecture |
| Agda conventions and notation | `site/STYLE-agda.md`, `src/README.md` |
| Trilingual literary exposition | `site/STYLE-i18n.md` |
| Terminology and reader introductions | `site/glossary.toml`, `site/GLOSSARY.md` |
| Chapter order, routes, titles and review status | `site/reading-catalog.json` |
| Markdown contract and reusable markup | `outcrop/docs/RENDERER-MARKDOWN.md`, `outcrop/docs/RENDERER-RECIPES.md` |
| Website architecture and verification | `outcrop/docs/ARCHITECTURE.md`, `site/ARCHITECTURE.md`, `site/README.md` |
| Site instance configuration | `site/project.json`, `outcrop/docs/SITE-CONFIG.md` |
| Compiler instrumentation and environment | `outcrop/docs/AGDA.md`, `site/AGDA-ENVIRONMENT.md`, `site/agda-libraries.json` |
| Checks, caches and deployment | `Makefile`, `.github/workflows/ci.yml`, `.github/workflows/README.md` |
| Licensing | `REUSE.toml`, `NOTICE`, `LICENSES/` |

Developer documentation is English. Reader-facing exposition and interface copy
are English, Chinese and Japanese. Do not infer present progress from dated
counts in READMEs or reports. Old POD goal codes, archived process files and past authoring schedules
are not a requirement to restart those processes.

## Scope and collaboration

- Inspect the worktree before editing. Preserve unrelated or concurrent changes.
  Ask before expanding a mathematical, deployment or destructive task.
- A diagnosis or review is read-only unless the user also requests a fix.
  A refactor must preserve behavior, not introduce an unrequested redesign.
- Delegate only when authorized. Give each dispatched agent explicit writable
  paths, relevant specifications, acceptance criteria and resource limits.
  Dispatched agents must not commit, push or change Git state.
- A prose-drafting brief is read-only unless explicitly given an editing scope.
  Supply the complete chapter, exact code range, relevant real dependencies and
  glossary; the coordinator validates and applies returned prose.
- Follow an explicitly requested model/effort. Do not prescribe obsolete model
  choices or external drafting services as a repository prerequisite.
- Report commands, exit codes, inspected browser/version or limitations, and
  remaining failures. An old successful run is not evidence for a newer change.
- Commit, push, deploy, remove branches or clean worktrees only within the current
  authorization. Do not bypass hooks or weaken gates to obtain a green result.
  For changes spanning Outcrop and Bedrock, commit Outcrop first, then record its
  submodule pointer in Bedrock. A commit-only request leaves both commits local;
  it does not authorize either repository's push or a deployment.

## Toolchain, resources and checks

The pinned environment currently uses Agda 2.8.0, cubical 0.9 and Python 3.11+.
Use the repository compiler `_build/outcrop-agda/bin/outcrop-agda`, not an unrelated global
Agda binary. `make bootstrap` installs the local toolchain and library registry;
it must not modify the user's global Agda configuration.

Keep `GHCRTS="-A64m -I0 -M8g"` for Agda. At most two Agda processes may run on
this machine, including other agents' jobs; check and coordinate before starting.
Do not increase `AGDA_JOBS` or the heap budget without approval. A scoped agent
must not check the complete Origin closure unless its brief authorizes it.
Prefer Make targets, which set the compiler, local `AGDA_DIR` and cache mode.

Common commands, from the repository root:

```sh
git submodule update --init --recursive
make bootstrap
make check
make milestone-lint
make site
make serve
```

- `make check` runs pure typechecking, source/prose/terminology/figure/route/
  chapter/i18n gates, reusable site lint and unit tests. It does not build or
  browser-test the website.
- `make milestone-lint` additionally verifies the Origin import closure. It runs
  in pre-push/CI, not as part of the ordinary pre-commit gate.
- `make site` produces compiler highlighting and semantic data, then the full
  trilingual site. `make site-render SITE_OUT=...` only rerenders from existing
  backend data; it is insufficient after a change that invalidates that data.
  `make site-backend` prepares the same content-aware backend without rendering.
  CI consumes that artifact with `make site-render RENDER_INCREMENTAL=1`; keep
  the shared content-fingerprint validation, artifact contract and host-specific
  output separation. A restored archive is only a candidate, never proof that
  compiler evidence is compatible. Do not hash unrelated Make/docs/lint inputs
  into semantic compatibility keys or trust a broad restore without validation.
  `make` defaults to help. Raw `_types`/`types-local-*` stages require a prepared
  backend; use `make types` when compiler freshness must also be checked.
- `make serve SITE_OUT=... PORT=...` previews that output. The default output is
  `_build/site`; use the actual directory for every subsequent check.
- Run `.venv/bin/python -m outcrop check-links <output>` after a full site
  build. Also validate search targets and run the relevant browser regressions.
- `make hooks` installs the repository hooks. Respect per-file licenses and run
  the REUSE checks when changing assets, dependencies or licensed file coverage.

Pure-check interfaces live under `_build/typecheck`; HTML/trace interfaces are
separate. Never mix them to make a build appear warm: a pure interface can skip
the elaboration events needed for semantic hover data. Generated sites, compiler
binaries, dependencies, interfaces, logs and screenshots belong under ignored
`_build/` or task-specific temporary paths, not in a commit. The small, intentional
`outcrop/examples/renderer/semantic/` test package is a documented fixture exception.

Initialize the pinned submodule before `make venv` or `make bootstrap`.
`make venv` installs Outcrop through `requirements-dev.txt`; an existing virtual
environment can run `.venv/bin/python -m pip install -e ./outcrop` explicitly.
Shared changes belong in the Outcrop repository, which has its own instructions,
tests and licenses. Updating the parent submodule pointer requires the same Git
authorization as any other repository change.

Outcrop also owns optional Agda instrumentation, compiler/library installation,
parallel scheduling, semantic extraction, weaving and source metrics. These are
Core integration tools, not a third product layer or mandatory render dependency.
Bedrock supplies its library lock, entry, flags, resource/cache choices and proof
gates; do not bring generic mechanism copies back into `tools/` or `scripts/`.

For comparable performance use `make typecheck-cold`: one process, pure Agda,
Cubical interfaces retained. `typecheck-cold-parallel` is an operational measure,
not that baseline. `html-cold` also produces highlighting and expression traces.
Distinguish toolchain installation, dependency caches, typechecking, extraction
and rendering when investigating CI duration. Do not compare total job time to a
local pure-check baseline or clear another agent's active cache.

## Mathematical and literary changes

Read the actual definition whenever an explanation depends on it, and inspect
real consumers before changing an interface. Existing prose is not proof.
Keep `--safe`; never introduce postulates, termination bypasses, `trustMe`,
unsolved metas or holes into work reported as complete. Preserve classical
assumptions as explicit parameters, never new ambient axioms.

A prose-only edit preserves the concatenated Agda code lines, including
indentation. Split fences only at valid boundaries. A specifically authorized
legacy-comment migration records exact removed comment suffixes and verifies
that no Agda tokens changed. Keep only the machine-readable exceptions explicitly
allowed by the Agda style guide; ordinary comments belong in surrounding prose.

The established conventions include:

- A parameter-free chapter begins with the exact OPTIONS pragma and module
  declaration, then its title-only language group and local prerequisite imports.
  Cubical imports belong with body exposition, not mixed into that import block.
- A parameterized chapter keeps OPTIONS first, then the title, required
  pre-declaration imports, trilingual parameter explanation, complete declaration
  and remaining local imports. Pre-declaration imports count as prerequisites.
  Origin's visible theorem re-exports are an explicit instance exception.
- Write `private module` on one line, including aliases. Preserve the privacy of
  other declarations when reorganizing a private block. Submodule folds use the
  shared markup and retain their own indentation and compact declaration surface.
- Prose leads its code. Develop questions, intuition, definitions and arguments,
  not a file-order inventory. Aim for meaningful exposition per 1–5 code lines;
  document indivisible exceptions, and never compress proofs or add filler merely
  to improve a numerical ratio.
- Language groups stay outside shared Agda fences. Preserve matched trilingual
  chapter/section structure. Japanese uses plain style; follow the repository's
  punctuation rules and do not use em dashes in authored prose.
- Statements require code, also inside folds. Proofs require code after their
  label. Do not author standalone `∎` in Markdown: the compiler supplies function
  definition boundaries independently of prose labels and fence boundaries.
  Related parallel definitions use one named Construction and ordered bullets,
  not several empty parallel statement labels.
- Use complete `{.Agda}` expressions for inline and single-line Agda, not manually
  annotated individual tokens. Only a single defined name may be an unboxed link.
- LaTeX belongs in standalone display blocks or figures. Figure-explanation
  paragraphs may also use inline LaTeX when their prose contains the localized
  fixed wording `图中的` / `in the figure` / `図中の`; the allowance applies only
  to that paragraph, not neighboring paragraphs or a whole section. Do not use
  this wording for unrelated prose to bypass lint. Other inline LaTeX requires
  explicit human approval recorded in `site/inline-latex-approvals.json` against
  its exact source-context fingerprint. Do not automatically approve old usage.
  The first four chapters remain strict. Explicit `temporary` records for later
  chapters apply only while the catalog's `human_reviewed` flag is false. Text
  edits and bulk replacements remain allowed; changing the flag to true ends
  the allowance. Resolve the inline LaTeX or obtain explicit approvals before
  marking the chapter reviewed, then remove its temporary record. Never unset
  review status merely to bypass lint.
- Centralize terminology in the glossary and research changes before adopting
  them. Explicit `term-ref` links may point forward; unmarked terminology must
  still respect its introduction and prerequisites. Do not invent parallel
  translations or duplicate tooltip text in individual chapters.
- Figures follow the shared recipes. A direct `div.diagram-framed` encloses only
  diagram content; its sibling caption remains outside. Do not place an Agda
  fence immediately after a figure. Mathematical arrows use diagram tokens,
  never inherited link colors.

Preserve the parallel reading routes. Do not rename or restructure mathematical
modules merely to simplify website implementation. Human-review badges are
changed only on explicit human editorial approval, not after automated checks.

The detailed literary audit is supplemental, not a declaration that the book is
finished. Recompute it when resuming literary work:

```sh
.venv/bin/python scripts/gate/check-literary-exposition.py --json
.venv/bin/python scripts/gate/check-literary-exposition.py --check src/Some/Chapter.lagda.md
```

A report without `--check` is an inventory and can exit successfully with findings.
Inspect its findings; do not convert that exit status into a completeness claim.

## Reusable website architecture

Maintain two layers, with Bedrock as their configured instance:

1. **Outcrop Core**: `from outcrop.core import MarkdownDocument, CodeContext`, Markdown
   structure, multilingual prose, terms and optional compiler semantics.
   Accept ordinary `.md`, not only `.lagda.md`. Return usable HTML, outline and
   Markdown; do not implicitly discover a project, glossary, catalog or compiler.
2. **Outcrop Site**: `from outcrop.site import SiteConfig, build_site`, catalog, page shell,
   publication, routes, dependency graph, search, appearance, interaction and
   reusable lint. Another project gets the same features, not a reduced demo.

Keep brand, icons, URLs, storage namespace, chapter exceptions, vocabulary and
mathematical policies explicit in configuration. Domain-specific proof gates
remain instance checks. Shared lint and the legacy Bedrock adapters must use the
same rule engines, with explicit, narrow policy exceptions.

Implementation lives in `outcrop/src/outcrop/{core,site,adapters}`. Browser
resources live in `outcrop/src/outcrop/site/resources/`, with `static/outcrop.js`
and `static/outcrop.css` as the reader entries. `scripts/site/` holds only real
Bedrock command adapters. Do not restore a legacy private-function facade or
add `sys.path` hacks to import framework modules. Use the installed package.
`window.outcrop` is the browser transport; Bedrock's `storage_namespace` remains
`bedrock`. Its explicit `policies.level_name_convention` enables the book's `ℓ`
naming convention; the generic default is false.

The reader footer credit is exactly "Powered by Outcrop", linked to
`https://github.com/BedrockInstitute/Outcrop`. Keep the separate copyright notice;
do not repeat Bedrock in the credit or restore a 1lab footer credit. Upstream
attribution belongs in Outcrop's licensing and acknowledgments.

Browser entry points compose features; state belongs to small cohesive owners.
Share semantic targets, hover lifecycle, positioning, definition history,
preferences and route loading. Do not reimplement behavior for each code surface
or replace a monolith with a single giant context passed to every module.
Publish modules and workers from one immutable `AssetBundle` runtime generation;
the tested page and its modal documents must use that same generation.

Keep the independent fixture runnable without Bedrock content or an Agda toolchain:

```sh
.venv/bin/python -m outcrop build --config outcrop/examples/renderer/project.json --project-root outcrop/examples/renderer --out _build/renderer-fixture/academy
.venv/bin/python -m outcrop lint --config outcrop/examples/renderer/project.json --project-root outcrop/examples/renderer
```

Retain tests for isolated distribution, ordinary Markdown, optional semantic
packages, multiple projects in one process, configuration validation and
namespace isolation. Update the public Markdown/configuration contracts together
with their implementation. Raw authored HTML/SVG is trusted input, not a
sanitization boundary for untrusted uploads.

## Interaction invariants and browser acceptance

Read `site/README.md` and the architecture acceptance matrix before changing UI.
Use the UI skill when available, but preserve the established hierarchy and
interaction rather than applying a new design indiscriminately.

- Code blocks, inline code, source/type popups and modal content share semantic
  behavior. Compiler ranges use Unicode code-point offsets. Do not invent AST
  nodes, types or links by guessing from popup text; missing data creates no
  misleading node highlight. Preserve infix/mixfix and Prelude forwarding.
- Desktop popups extend downward and retain per-branch disappearance delays;
  descendants keep ancestors alive, and the whole branch eventually closes.
  Touch first opens a persistent hover, not a modal. Its explicit action opens
  the modal; node changes/outside touches/navigation dismiss it, not a timer.
- Touch node gestures must return to the leaf as well as ancestors, clearing the
  previous leaf background. Recursive hover has no arbitrary depth cap; precise
  universe/primitive stop rules prevent meaningless type ladders without
  suppressing unrelated names. Internal compiler Dummy diagnostics never appear.
- Definition inspection is one full-body modal with target-based back/forward,
  lazy loading, explicit/outside close and an enter-page action. Keep sticky
  contents and scroll controls, but omit the outer header/footer. History anchors
  target's code block or prose container, not the user's later scroll position.
  In-body same-origin content links use the modal; structural navigation, search
  results and external links navigate normally. Revisiting the current definition
  in its body also navigates. Preserve dark/light loading and cancellation,
  including Safari layout.
- Preserve automatic syntax help, glossary links, boilerplate source popups,
  universe notation and selective dotted-operator fonts without changing copied
  code. Share palettes across every code surface. Code spans the full containing
  column without an outdent or external QED gutter. The exact rectangular `∎`
  is an absolute, noninteractive overlay at each compiler-certified definition's
  final line, at fixed opacity `.25`, even over code. Definitions need an explicit
  type signature and equation clauses; include submodule definitions but exclude
  where-local definitions. Reserve no row, height or extra padding. Preserve the
  tight prose-proof/code spacing without a special QED frame. Agda frames grow
  vertically to their full content and scroll
  only horizontally; the page, modal or fullscreen reading plane may scroll
  vertically. Keep submodules independently indented, declaration headers
  compact, and right-end scroll padding intact without clipping code or inline
  fragments.
- Mobile landscape code reading moves the existing DOM and preserves IDs/AST
  identity. Share transformed coordinates with hover and touch selection, restore
  the original surface before opening a modal, and test focus/scroll restoration.
  Keep `text-size-adjust: 100%` and its WebKit equivalent scoped to code frames
  and fullscreen reading; do not disable user zoom. Verify actual rendered glyph
  size as well as computed font size when checking mobile text autosizing.
- Search all supported editions regardless of the current language, including
  prose, headings, glossary and internal/external Agda. Preserve worker errors,
  retry, IME and keyboard behavior. Results are native navigation links, not
  definition-modal targets. Dismiss on outside click or outside `focusin`, not
  input `focusout` with a null `relatedTarget`: Safari can emit that blur before
  a result's click, and hiding results then prevents navigation.
- Preserve interactive contents, routes/completion, graph layouts and filters,
  gesture/keyboard pan and zoom, full-screen/focus restoration, sidebar title
  versus disclosure hit regions, appearance persistence and Ask AI copying.

Use actual computer-use browser actions for every affected interaction, alongside
unit and fixture tests. Test desktop and narrow widths, both themes, language
switches, loading/error paths and keyboard use as relevant. Sequentially run the
browser fixtures served by `scripts/tests/serve-boilerplate-regression.py` against
the freshly built production runtime, not stale or unversioned test scripts.
Record URLs, build/runtime identity, actions and results.
Independent framework tests live in `outcrop/tests`; Bedrock-content integration
tests remain in `scripts/tests`. Historical results in the architecture record
do not establish acceptance of a newly extracted package or changed interaction.

A narrow Chrome viewport, dispatched touch events and desktop Safari are not
real iPhone Safari evidence. State unavailable coverage honestly. For renderer
refactors also compare generated body/code text, Markdown mirrors, type data,
routes and search indices with a known baseline. Do not delete assertions merely
because implementation ownership or names changed.
Attribute user-reported real-device acceptance to the user and the revision they
tested; it does not automatically cover subsequent changes. Keep dated release
and acceptance snapshots in working notes, not as permanent proof of success.
