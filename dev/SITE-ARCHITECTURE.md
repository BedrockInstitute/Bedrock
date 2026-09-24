# Bedrock website architecture and acceptance record

Bedrock is an instance of [Outcrop](../outcrop/docs/ARCHITECTURE.md), pinned in
the `outcrop/` submodule. Outcrop Core and Outcrop Site own reusable implementation;
this document records Bedrock's adapter/gate mapping and dated acceptance evidence.
The [instance guide](../site/README.md) describes local installation and operation.

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

## Extraction and cleanup, 2026-09-24

The cleanup began at `956682cb`, after the previous refactor below. Production
Python across the former site/gate scope measured 9,881 lines. Removing test-only
compatibility and duplicated implementation reduced it to 9,663; adding the real
package API/CLI and explicit instance adapters brought the equivalent scope to
9,700. This count excludes tests and the new browser-fixture builder. It is a cost
record, not evidence of correctness or a target for mathematical code reduction.

Removed consumers and shared replacements:

- Tests now call MarkdownDocument, AgdaSemantics, Publication and PageRenderer,
  not a lazy renderer facade. The unused Publication Markdown-mirror bridge is gone.
- SourceCorpus owns the production document closure; the old standalone closure
  and related test-only lookup helpers are removed.
- Source discovery and exact filename suffix handling are shared by rendering,
  routes, graph and site lint. Prerequisite-order checks use one rule engine.
- Route-annotation stripping and Unicode import parsing are shared by applicable
  render/lint consumers; the graph no longer uses a separate ASCII-only import rule.
- Unused aliases, star imports and framework `sys.path` shims are removed. Build
  CLI and API options share one parser. Core has no dependency on Site or its CSS.

At the Python handoff, 129 Outcrop tests passed (123 migrated, six new contracts),
strict independent-example lint and `make lint` exited 0. The wheel contained 152
files with templates, modules, worker, fonts and vendor resources. Of 256 Bedrock
tests, 253 passed and three old hover scenarios required adaptation to the concurrent
UI changes; that handoff is not an all-tests-passed claim. Evidence logs are
`/private/tmp/outcrop-package-final.log`, `/private/tmp/outcrop-python-lint-final.log`,
`/private/tmp/outcrop-wheel.log` and `/private/tmp/bedrock-package-tests.log`.

The completed extraction pins Outcrop `923c4fb6df29c58ac58885c4e7851b6ef2ae7ec1`.
Its [acceptance record](../outcrop/docs/ACCEPTANCE.md) supersedes that intermediate
handoff: all 256 Bedrock and 130 Outcrop tests pass, as do `make check`, the Origin
closure gate, both REUSE audits and the independently installed package build.
The full three-language build renders 282 modules, with zero broken relative
links or search targets. Chrome browser acceptance includes the original six
suites, the independent two-brand fixture, and 25 new mobile-simulation checks.
Runtime generation: `f0e5481f2e1a2907`. Native iPhone Safari remains explicitly
unverified; the available Safari automation window could not be acquired.
Outcrop's first public CI run also passed:
[run 35991153159](https://github.com/BedrockInstitute/Outcrop/actions/runs/35991153159).

During migration, after adapting those hover scenarios, the coordinator reported both suites
passing: 129 Outcrop tests and 256 Bedrock tests. This is unit-test evidence only;
the earlier handoff failure is retained above rather than silently relabeled.

The frame-internal QED, full-width code, compact portrait landscape reader,
search visibility and hover-loading changes are covered by the separate extraction
acceptance linked above. None of the older historical results below certifies them.

## Producer boundary correction, 2026-09-24

The initial extraction left the semantic producer and several synthetic tests
with the consumer. The follow-up moves the Agda overlay, version patch, compiler
builder, library installer, DAG scheduler, weaving, search-target audit and source
metrics into Outcrop. Generic tests move with their owners; Bedrock keeps its
actual corpus, glossary/catalog policy, proof gates, library lock, resource/cache
choices and deployment workflow. No mathematical source changes are involved.

The producer is optional Core integration, not a third product layer. Ordinary
Markdown builds still need no Agda toolchain. `dev/AGDA-ENVIRONMENT.md` documents the
consumer commands; `outcrop/docs/AGDA.md` documents reusable installation and
evidence contracts. Compiler identities are installation-path independent.
Library locks and shared import syntax now invalidate the appropriate backend
caches. Warm checks preserve valid trace evidence; failed HTML generation does
not replace it. Plain `.agda` and literate sources share extraction without
silently discarding the former's records.

The previous Bedrock push's [CI run 35991401805](https://github.com/BedrockInstitute/Bedrock/actions/runs/35991401805)
failed because Outcrop was installed before switching to the job's final Python
interpreter. All jobs now select Python before package installation. This is a
local correction, not evidence that a new remote CI run has passed.

The published footer uses the configured site name followed by `powered by
Outcrop`, linking to the framework repository. 1lab attribution remains in
Outcrop's README, NOTICE and license records, not the reader footer. Duplicate
parent OFL license files were removed after confirming the complete copies remain
in Outcrop; both repositories pass REUSE independently.

Final local acceptance: `make check`, the Origin closure gate, a fresh complete
120-module compiler traversal and the 282-module trilingual site build all exit
0. Relative-link and search-target audits report no broken targets. The 44,808
search records match the previous release exactly. The installed-package and
browser evidence, including physical-device limitations, is recorded in
[Outcrop acceptance](../outcrop/docs/ACCEPTANCE.md#producer-boundary-audit-2026-09-24).

## Complete gate mapping

No original gate was removed. `make check` additionally exercises the reusable
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

### Test migration traceability

The subsequent boundary audit moved synthetic rule and reader tests into
`outcrop/tests/`: expression hover and its support module, chapter boilerplate and
outlines, navigation, publication/agent mirrors, terms, reading order/routes,
fences, prose/Agda rules, glossary rules and source metrics. Bedrock retains only
the actual catalog/whole-corpus checks, precise legacy prose exceptions, scoped
documentation discovery, mathematical gates and its one-time source migration.
Historical module names used as explicit test data do not imply loading this
repository. Shared tests no longer import a Bedrock gate to reach a Core function.

`test_site_lint_contract` covers the previously consumer-only diagram stylesheet
gate, shared marker-aware CJK diagnostics and a non-Cubical `--safe` project's
lint and real site output. Batch weaving now lives in `outcrop.adapters.weave`;
the root adapter supplies configured sources, archive exclusion and the existing
`bedrock.agda-lib` metadata. Source metrics similarly use Core with a root-only
source-discovery adapter. These checks are Python/API evidence, not a new browser
acceptance claim.

| Former monolith test | Current evidence |
| --- | --- |
| `test_hover_lifecycle` extracted timer closures | Same clock/enter/leave/mobile scenarios against the real `HoverBranch` class |
| Expression gesture and Unicode-range tests | Same scenario expectations using actual `code-targets` functions; legacy DOM stubs locate named owner modules |
| Hover/history array spelling and hardcoded positions | `test_reader_state`: 120-depth branches/history, forward truncation, generation cancellation, idempotent release, common downward/clamped geometry |
| Modal geometry/canonical redirect helpers | Same numeric/scroller/redirect scenarios against `definition-layout` |
| Appearance `_ver` source spelling | `AssetBundle.template` output and full captured-dependency generation tests |
| Origin implicit-default tests | Explicit instance policy supplied; generic functions no longer receive an Origin exception |
| Existing DOM/CSS wiring assertions | Retained against responsible modules, plus actual browser fixture assertions |
| New reusable boundaries | `test_renderer_library`: plain core, isolated distribution/no toolchain, dual-instance isolation, strict fixture lint, safe configuration and partial prerequisite overrides |

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

## Historical verification: the pre-Outcrop extraction refactor

Everything in this section belongs to the earlier refactor, starting at
`22e5e983` and delivered before the Outcrop extraction at `956682cb`. Its staged
and final results are retained verbatim in substance for traceability. They are
not results for the current package or UI generation. Temporary evidence paths
describe that local run and are not durable distributed artifacts.

| Stage | Result / evidence |
| --- | --- |
| Independent compiler fixture | Real Agda check and type extraction exit 0; `/private/tmp/lantern-compiler.log` |
| Independent shared build and lint | 4 compiler modules, 3 authored chapters, 3 languages, 9 Markdown mirrors; lint 0; `/private/tmp/lantern-build-final.log`, `/private/tmp/lantern-lint.log` |
| Isolated distribution and same-process builds | Copies omit `src`, `dev`, `site/project.json`; `PATH=/no-toolchain`; generic and compatibility explicit-config CLIs work; Lantern → Prism → Lantern does not leak metadata |
| First post-extraction full site | 282 modules × 3, 360 Markdown mirrors; `/private/tmp/bedrock-render-refactor-4.log` |
| Independent baseline parity | Parent built exact `22e5e983` into `/private/tmp/bedrock-render-baseline.WtD6iQ/output`: 845/846 article bodies byte-identical; sole difference is Japanese graph labels localized from `Origin` to `原点`; all 360 Markdown bodies identical, full mirrors identical after YAML license quoting normalization |
| Unit migration | 377 tests passed before the latest added configuration cases; `/private/tmp/all-tests-fourth.log` |
| Full ordinary gate | `GHCRTS='-A64m -I0 -M8g' make check`, exit 0; `/private/tmp/bedrock-refactor-check-2.log` |
| Entry-closure gate | `make milestone-lint`, exit 0; `/private/tmp/bedrock-refactor-milestone.log` |

Pre-freeze actual Chrome session (own tab, sequential active fixtures at
`http://127.0.0.1:18767`): `/regression` 132/132, `/directory-regression` 90/90,
`/padding-regression` 28/28, `/appearance-regression` 136/136,
`/universe-regression` 65/65. The first fixture used the current unversioned test
entry while iframe documents retained the earlier coherent production hash;
these staged results were superseded by the final historical run below. The new dedicated
server at port 18769 reads the built page's runtime hash and serves every fixture
entry from that same production generation. Simulated touch/Safari gesture events
and embedded narrow frames do not establish real iPhone Safari behavior.

The explicit Chrome viewport API was verified with `innerWidth=1100` and
`innerHeight=850`. Independent Lantern manual actions already verified routes,
comparison, marking the input chapter complete, and the resulting next-ready
chapter. The completed historical width/theme/language and production-entry evidence
is recorded below.

### Historical final acceptance, 2026-09-24, before Outcrop extraction

That run used production JavaScript generation `24535ca6aa993b17`. The dedicated
regression server reads this generation from the built page, so fixture entry
scripts, imported reader modules, workers and modal iframe pages use the same
snapshot. There were no runtime changes during the final browser sweep.

| Final gate | Result and log |
| --- | --- |
| `make site SITE_OUT=_build/site-directory` | Exit 0, 282 modules × 3 languages, 120 internal chapters and 360 mirrors, `/private/tmp/bedrock-refactor-site-final.log` |
| Final render after the core mirror correction | Exit 0, `/private/tmp/bedrock-refactor-render-final.log` |
| `GHCRTS='-A64m -I0 -M8g' make check` | Exit 0, 379 tests, all ordinary gates, `/private/tmp/bedrock-refactor-check-final-2.log` |
| `make milestone-lint` | Exit 0, 119 source modules consumed, `/private/tmp/bedrock-refactor-milestone.log` |
| Final link checker | Exit 0, 1,116,324 links across 854 pages, zero broken, `/private/tmp/bedrock-refactor-links-final.log` |
| Final search checker | Exit 0, 44,808 entries and 80,016 destinations, zero broken, `/private/tmp/bedrock-refactor-search-final.log` |
| Independent fixture | Strict lint zero errors, real Agda semantic package, isolated distribution without a toolchain, same-process dual-project tests, and browser checks below |
| Source scope | No changes in `src/**` or `tools/bedrock-agda/**`, `git diff --check` clean |

After the final render, the independent baseline comparison again found
845/846 article bodies byte-identical, with only the two intended Japanese graph
label localizations differing. All 360 Markdown bodies and full mirrors match
(normalizing only YAML license quoting). All 849 type sidecars, three reading
route files, three legacy search files, three term files and the cross-language
search index are byte-identical. The final deployment-prefix correction changes
only configured subpath projects: Bedrock's empty prefix still yields the exact
existing `agent_guide: /llms.txt`. The independent fixture was rebuilt and its
`/academy/llms.txt` metadata checked in unit tests and the browser.

The supplementary literary audit was independently compared with the exact old
`22e5e983` auditor and its old dependencies against unchanged source. Both return
84/120 passing chapters and 329 findings, with no result differences:
`/private/tmp/literary-audit-parity.log`. This audit is not a claim of completed
literary exposition and is not newly imposed by the ordinary gate.

#### Actual browser fixture runs

All rows below were opened and observed through computer use, sequentially in
one owned Chrome tab. They are browser-executed assertions, not manual pointer
tests. Touch, pinch and Safari gesture events in these fixtures are synthesized.

| URL on `http://127.0.0.1:18769` | Final result |
| --- | --- |
| `/regression` | 132/132, hover chains, leaf selection, syntax, stop rules, modal history/loading/alignment and simulated touch |
| `/directory-regression` | 90/90, three languages, 1100/375px directory frames, 390px graph, search, hit regions, graph gestures/fullscreen |
| `/padding-regression` | 28/28, 390/900px frames, nested submodule right scroll padding |
| `/appearance-regression` | 136/136, light/dark palettes, inheritance, dynamic/modal surfaces and preferences |
| `/universe-regression` | 65/65, source identity, Unicode ranges, dynamic text, raw hover and formatting |
| `/fonts-regression` | 15/15, exact two dotted clusters, original text, dynamic nodes and link contrast |
| `http://127.0.0.1:18768/renderer-regression.html` | 22/22, 390px frame, Lantern/Prism brand, paths, compiler semantics, theme/palette/completion isolation, mirror, agent and index contracts |

The first final directory run timed out waiting for the Japanese page's reader
initialization after 73 successful assertions. No new script exception was
reported. A foreground reload passed all 90 without product changes, timing
changes or weakened assertions. This intermittent loading timeout remains part
of the evidence rather than being omitted. Server requests and the modal
regression report are logged at `/private/tmp/bedrock-final-browser-server.log`.

#### Direct computer-use actions

These actions used real clicks, typing, keyboard and selection through the
documented browser interface, independently of the fixture event synthesis.

| Page and actual Chrome viewport | Actions and observed result |
| --- | --- |
| Lantern index, 1100×850 | Reading-route comparison, mark input complete, next chapter becomes ready, state persists |
| Lantern English index | Typed Chinese `标记`, then `keep`, then an absent query: cross-language prose/terms/code results and explicit empty state, ArrowDown/Enter opens a real definition |
| Lantern definition page, 1100×850 | Click definition to load whole-page modal, click nested definition, use history controls, ordinary next-chapter link navigates the parent page instead of opening a code error |
| Lantern modal | Definition's entire code block top measured at 43.90625px against sticky content boundary 44px, error 0.094px; header/footer removed while scroll controls and content retained |
| Lantern chapter, 375×812 dark | Drag-select paragraph, open Ask AI, inspect branded canonical/source/prerequisite context, click Copy and read matching clipboard text; no external service submission |
| Lantern chapter, 320×812 light/GitHub | Actual appearance controls, screenshot and DOM measurement: document and body width both 320px, no page overflow or clipped title |
| Plain core `/plain.html` | Visibly rendered ordinary Markdown, table, link and unknown Agda code without invented semantic links |
| Bedrock Prelude, 768×900 | Click fibre contraction, observe animation and contracted state, Enter reverses it, final geometry/state restored; keyboard opens note, explicit close hides it |
| Bedrock Impredicativity, 390×844 | Click path-space unfolding, observe active then completed animation, document width 390px; open drawer, Escape restores background, switch to Japanese chapter |
| Lantern dependency graph, 390×844 | Click Expand graph, observe full-screen exit control, Escape restores original graph control |

Chrome's temporary viewport override was reset after testing. Narrow desktop
Chrome retains a fine pointer: a first definition click there is a desktop click,
not an iPhone tap. Real iPhone/iPad Safari, physical multi-touch/pointer-capture
and trackpad pinch hardware were not available and are not claimed as covered.
The browser's content-export API was unavailable, so the evidence consists of
the tool-visible DOM/screenshots, exact assertion results and logs above rather
than an invented exported screenshot path.

#### macOS Safari attempt and remaining limitation

A newly created, owned Safari tab opened the final `/regression` URL through
native computer use. No existing user tab was navigated, and no settings or
permissions were changed. The server recorded 20 passing checks followed by a
failure of `route expansion restores natural height`. The next accessibility
observation reported that the window was unavailable, so testing stopped rather
than switching to a different user window.

The relevant `enhanceDisclosure` function body is byte-for-byte the same as
`22e5e983`, apart from replacing the window export with an ES module export.
The old fixture also used the same fixed 250ms wait for the 160ms animation.
This rules out a changed animation implementation at that boundary, but does not
establish whether the observed Safari failure was animation scheduling, a lost
foreground window, or an existing browser issue. No assertion or timing was
relaxed. This Safari run is **not passed** and needs a future foreground Safari
rerun with an available owned window. Real-device Safari remains unverified.
A single bounded recovery through Safari's known application identifier returned
the same unavailable-window error. No further keyboard actions were sent.
