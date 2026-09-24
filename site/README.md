# site

The static-site **front-end assets** consumed by
[scripts/site/render-site.py](../scripts/site/render-site.py). These are committed source; the rendered
site they produce is generated into `_build/site/` (git-ignored). English developer doc; the
rule set is [AGENTS.md](../AGENTS.md).

**Read this file when your write scope names a path under `site/`.**

**The publishing pipeline runs outside `make check`:** `scripts/site/extract-types.py`,
`gen-depmap.py`, `link-check.py`, `render-site.py`, `weave-i18n.py`, `i18n_markers.py` and
`depmap-template.html`. `make html`, `make types`, `make site`, `make serve` and the two deploy
workflows run them. The one exception is `weave-i18n.py --check`, which `make lint` does run,
because a broken language marker is a defect in a master rather than in the site.

The dependency map derives its graph from fenced source imports and its learning
stages from `dev/reading-catalog.json`. Compact, learning-stage and namespace
layouts share the same nodes and edges; skeleton mode preserves reachability.
Origin appears at the bottom as a dependency endpoint, although readers meet
its theorem statements first as a preview. The root URL leads to the language-specific
interactive contents, which opens on the Origin tab. The sidebar keeps Interactive contents
folded and Current route open; the old namespace tree is removed. A route chosen in the contents is remembered across chapters.
In both the sidebar contents tree and the article's contents menu, a branch title
links only over its text; the remaining row whitespace and right-hand chevron toggle
its children. A branch paints its hover/current background once, on the whole row,
never again on its nested link. Keyboard disclosure and mobile touch height remain
available independently of title navigation.
The dependency graph defaults to namespace layout. Layout/search/zoom/full-screen
controls remain visible; edge modes, legend, instructions and pan buttons share a
disclosure. Chapter details appear on selection. A single SVG camera handles touch
drag/pinch, trackpad pan/Ctrl-wheel zoom, Safari gesture events, buttons and keyboard.
Gestures are scoped to the canvas. Full-screen uses a viewport-sized native dialog,
with Escape, focus containment, an explicit exit and restoration of the graph state.
UI UX Pro Max informed progressive disclosure, touch targets, keyboard alternatives
and semantic light/dark surfaces; no graph data or layout mode is removed.

Search always queries all three editions, independent of the page language.
`search_index.py` emits `search-content.json` with localized titles, sections,
addressable prose, glossary entries, definitions and all rendered project/Cubical
code. Shared code windows overlap and are deduplicated across editions. The worker
`search-worker.js` lazily loads, normalizes and ranks this index off the UI thread.
Results identify their language; shared Agda opens in the current edition.
The search control supports IME, keyboard selection, explicit empty/error feedback
and retry. Per-language `search.json` remains available for existing machine readers.
On phone-width screens, the search row recedes while scrolling down and returns
while scrolling up or using search.

## Contents

- `template.html`: the page shell. The renderer fills `%%...%%` slots (content, navigation, the
  external-library banner, cache-busting `?v=` asset versions, the canonical link, the
  JSON-LD graph, the `window.bedrock` page config, and so on).
- `static/`: assets copied verbatim to the site root.
  - `bedrock.css`: styles (the palette and Agda token colours are **adapted from the 1lab**).
  - `bedrock.js`: theme toggle, KaTeX, type-on-hover, search control, language switch.
  - `ask-ai.js` / `ask-ai.css`: select a passage, get a handover text for an assistant.
  - `assets/`: the brand marks (`favicon.svg`, `brand.svg`, `banner.png`). `brand.svg` is a
    bottom-padded variant of the favicon mark, for inline use beside heading text in the READMEs;
    `banner.png` is the README/social hero card.
  - `fonts/`: self-hosted woff2 (EB Garamond, Inria Sans, JuliaMono); no runtime font CDN.
    `BedrockDottedOperators-Regular.woff2` is an OFL JuliaMono derivative containing
    only U+21D2, U+00AC and U+0307, with mark attachment for `⇒̇` and `¬̇`.
    Rebuild with `scripts/site/build-dotted-operator-font.py` (its docstring gives
    the optional font-tool command). It keeps the original outlines and cell width
    and has its own family name, respecting JuliaMono's reserved font name.
    A shared text-node decorator selects only these two complete clusters, also
    in dynamically inserted hover/search/modal content. Plain `⇒`, `¬`, other
    dotted symbols, source/copy text, links and math-renderer output stay unchanged.
    See `scripts/tests/browser-fonts.html` for the visual and DOM regression page.
  - Ordinary navigation uses the rose `--link-color` token (light `#a53268`, dark
    `#ed9fbd`), independently of interface `--primary` and Agda semantic colours.
- `vendor/1lab/`: **vendored upstream 1lab assets** kept under their own license, with the
  upstream font and icon license texts under `vendor/1lab/static/licenses/`.

## Definition previews

Chapter openings are validated by `scripts/site/chapter_structure.py`. Plain
modules start with OPTIONS and their declaration, then a title-only trilingual
group and project imports. Parameterized modules start with OPTIONS alone, then
the title, necessary telescope imports, trilingual parameter exposition, the
complete declaration and remaining project imports. `boilerplate.py` moves
the compiler-highlighted setup into inert templates, preserving all canonical
source anchors at the chapter title. Popup copies omit duplicate ids. A title
exposes OPTIONS and its unparameterized declaration. Parameterized declarations
and their exposition remain in the body; direct prerequisites expose
the actual imports, including those before the module declaration. Markdown twins
keep the full setup. `agda_help.py` centralizes trilingual syntax help and links to
the official Agda 2.8 manual. No separate popup manager is used: `data-hover-html`
and `data-hover-template` are payload sources for the same recursive hover stack.
`data-hover-help` resolves through the cached, per-language `types/$syntax.json`,
so repeated keywords never duplicate their explanatory payload throughout the book.
Inline and single-line code use the same help payloads automatically. The lexical
pass recognizes whole Agda tokens, excluding strings, comments and existing links.
Prelude's actual exports (including renamed and locally defined vocabulary) supply
definition links even within Prelude itself. Infix parts resolve to underscored
names; nested mixfix parts are paired before linking, with ambiguous cases left
unlinked. Compiler-highlighted `syntax` declarations supply additional notations,
without a manually maintained per-symbol table. Formal code is never re-tokenized.
Only type popups neutralize non-hoverable primitive names; source code retains
the ordinary identifier color, including `Type`.
Reserved symbolic tokens (`∀`, `:`, `=`, `→`, `λ`, standalone `_`, etc.) share the soft amber
`--code-symbol` color and `.syntax-symbol` class across formal blocks, inline
code, single-line displays and hover signatures. English-word keywords retain
their separate keyword palette. Both palettes have light/dark variants.
Braces `{` and `}` and semicolons `;` have the same syntax-help interaction but retain ordinary
punctuation color, including grouped double braces in compiler output.
The dashed code cue is distinct from terminology; amber highlights denote syntax
help, not a mathematical AST node. Keyboard focus and touch use the same payloads.
Boilerplate templates alone receive the `boilerplate-hover-popup` shell: the
article's code-block background and border, a muted primary-color left edge,
roomier padding and a floating shadow. Code tokens and nested type/syntax popups
keep their existing styles. The surface uses shared light/dark theme variables.
On desktop, leaving a nested popup re-arms the disappearance delay for all its
ancestors; hovering any descendant keeps that branch alive. Touch popups retain
their existing persistent behavior and never acquire an automatic close timer.

Formal statement endings use `.statement-ending` and `.statement-qed`: the final
Agda block retains all its anchors and hover behavior; a separate grid column
holds ∎ outside its right edge. The grid reserves room on mobile and provides
extra spacing below. The same HTML and CSS are used in modal mirrors. Definitions,
constructions, lemmas, facts, theorems, corollaries and standalone proofs all
require code and an immediate ending, including within folded submodules.
A statement paragraph immediately followed by its proof uses a compact `.45em`
gap instead of the ordinary `.95em` paragraph gap. Both facing margins are set
to account for margin collapse; intervening prose/code and QED endings retain
their normal spacing. This is language-independent and also applies in folds
and modal mirrors through the same stylesheet.
Ordinary Agda blocks use .5rem before and 1.6rem after, keeping each block closer
to its preceding explanation. The immediately preceding prose margin is also
reduced so margin collapse cannot cancel this spacing. Statement endings retain their larger trailing
gap; fold declaration headers retain zero outer margins.
Ordinary blocks reserve the same right-hand QED gutter and leftward inset as
statement endings, so code edges align without an empty visible mark. QED retains
the original rectangular Unicode ∎ glyph; its line box aligns to the final code
border, preserving the font's natural bottom whitespace without compensation.
Width and gutter tokens are shared at each breakpoint. Each folded submodule
retains its own indented column and outer frame. Its body code aligns within that
column, not with code outside the submodule. The declaration keeps its separate
compact summary style: full summary width, no QED gutter or body-code outdent.
Agda blocks retain fixed padding on their outer frame; only the inner
`.agda-code-content` scrolls. Both gutters remain visible throughout scrolling,
including at the end of long lines inside submodules. Fold declaration lines
are excluded from this body-code wrapper and retain their original padding.
Inline code uses cloned box decoration on wrapped lines, so each fragment retains
its border, rounded corners and horizontal padding, including in modal mirrors.

Compact learning routes share `bedrockEnhanceDisclosure` with submodule folds,
but use a short 160ms transition. Repeated activation reverses from the current
height, reduced-motion skips animation, and the completion control stays at the
right end of the summary row without toggling the fold. Group labels have no top
margin and .55rem below; the group grid begins .55rem below the summary.
Prerequisite titles open a modal on desktop (including Enter). On touch,
the title first reveals its import; the popup's shared modal-window action then
opens the prerequisite chapter in the same modal used for definitions.
The modal's enter-page icon, immediately left of Close, navigates to the current
history entry's original definition anchor, independent of manual scrolling.

Every chapter entry in `dev/reading-catalog.json` requires a boolean
`human_reviewed`. Change it only after explicit human editorial review, never
because typechecking or automated tests pass. The first four teaching chapters
(Base.Prelude, Base.Impredicativity, Base.Classical, Base.Choice) start as reviewed.
Origin is also explicitly human-reviewed; all remaining entries are unreviewed.
Its chapter heading, boilerplate hover, anchors and badge stay together inside
the guide's Origin panel, separate from the reading-guide heading.
Origin retains Theorems 0–4 with their visible public import blocks and QED
marks. These result-registry imports are an explicit chapter-layout exception,
not hidden boilerplate; its OPTIONS/module declaration still lives in title hover.
Its Preface precedes the Milestones subsection. Origin's prose may resolve unique
project definitions beyond its immediate imports. Everywhere, compiler-resolved
scope links also resolve instantiated module aliases in hover signatures before
qualification is shortened (for example V.Model.Model.isZFModel).
The title row displays a green shield/check or an amber warning triangle, with
localized accessible text and a hover/focus hint. The badge is a sibling of h1,
so definition modal titles and chapter-name extraction do not include its label.

Source blocks and hover types share the renderer's `wrap_expression_ranges` nesting
logic. Hover ranges must resolve to compiler-backed `$expressions` payloads, and both
range matching and qualified-name linking respect complete Agda token boundaries.
Touch selection shares `gestureCandidates` and `clearHighlight` across both surfaces;
CSS `:hover` highlights are restricted to fine, hover-capable pointers.

A definition modal loads the original page on demand in a same-origin iframe with
`bedrock-modal=1`. Only the reading body is shown, retaining its section navigation
and page-edge controls. `#main-content` is the explicit scroll container on every
device. History stores definition targets, not a reader's later scroll position.
Canonical `.html` redirects must identify the same page before sizing and alignment.
On touch devices, tapping a name opens its hover; only the hover's modal action opens
the modal. Its noninteractive title combines the localized chapter title with the
definition name styled as Agda code. Only revisiting the current definition from
inside the modal body navigates to its page; the title is never a link.
Each navigation keeps a theme-aware loading surface visible while the iframe
loads and aligns its definition. The frame remains laid out but transparent and
inert until ready, preventing a white initial canvas in dark mode. The loading
status is localized; its code-mark spinner and the content fade respect reduced
motion. Failed loads replace the spinner with the existing localized error,
and stale loads cannot replace a newer history entry or reopen a closed modal.

Run the interaction and renderer regressions with
`python3.11 -m unittest scripts.tests.test_expression_hover scripts.tests.test_site_navigation scripts.tests.test_hover_lifecycle scripts.tests.test_chapter_boilerplate`.
After a full trilingual build, run
`python3.11 scripts/tests/serve-boilerplate-regression.py --site _build/site`
and open `http://127.0.0.1:18764/regression` in Safari. The fixture exercises the
real generated chapter/import payloads, nested syntax help, simulated touch
activation, full-page modals and a 390px embedded viewport. Simulated touch is
not a substitute for testing on an actual iPhone.
Add `--modal-delay 0.6` to exercise loading, history, failure and close-during-load
states under a deliberate local response delay (never part of the published site).

## The agent-readable layer

A reader who selects a sentence and asks an assistant about it, and the assistant that
then follows the link, need the same thing: a stable name for the block, and a cheap way
to read the rest. `make site` therefore emits, beside the pages:

- `/<lang>/<Module>.md`, a plain-Markdown twin of every chapter: the same prose, the same
  Agda in fenced blocks, and YAML front matter giving the chapter's stage, reading-order
  position, prerequisites, canonical URL and Agda master. Each page advertises its own
  twin with `<link rel="alternate" type="text/markdown">` and links it in the footer.
- `/llms.txt` (copied to `/.well-known/llms.txt`), the guide an agent reads first: what
  Bedrock is, how the site is addressed, what is fetchable, and every chapter in reading
  order. Generated from the reading catalog, so it cannot drift from the book.
- `/robots.txt` and `/sitemap.xml`, with hreflang alternates for the three editions.
- `_headers`, the Cloudflare Pages rules that serve `.md` as `text/markdown` and open the
  JSON endpoints to cross-origin fetches. GitHub Pages ignores this file; Cloudflare is
  the canonical deployment.

Anchors are the citable part. `sec-0` is a chapter's title and `sec-1`, `sec-2`, ... its
headings; `p-1`, `p-2`, ... number the prose blocks (paragraphs, list items, block quotes
and tables) in document order, the outermost block being the addressable unit. Inside a
displayed Agda block, Agda's own highlighter has already named every token by character
offset and every definition by its identifier, so code needs no scheme of Bedrock's.
`scripts/tests/test_agent_layer.py` pins all of this.

## Where a chapter lives

**One rule, in one place.** [scripts/site/reading_routes.py](../scripts/site/reading_routes.py)
decides a chapter's address and puts it on the catalog node as `page` and `anchor`. Every
consumer links through those two fields and none of them builds a filename from a module
name: the renderer (`chapter_href`), the reading-route explorer, the dependency map, the
search index, the glossary, the sitemap, the Markdown twins and llms.txt.

The rule exists because a preview chapter has **no page of its own**. The reading guide
embeds its entire body, so `Origin` is read at `index.html#milestones` and no
`Origin.html` is written. Because the guide embeds the whole chapter, every anchor
the chapter defines still resolves there, which is why an explicit anchor beats the
panel's own: `chapter_href("Origin", "#1354")` is `index.html#1354`.
Origin has the same top and bottom chapter navigation as every other chapter,
inside its own guide panel. Links show a direction chevron and chapter title;
previous/next wording remains in accessible labels, not the visible text.

A module with no catalog entry is a Cubical library page rendered for reference, not a
chapter, and keeps its own filename.

The ask-an-assistant dialog is built entirely in the browser from `window.bedrock` and
the selection. It sends nothing anywhere: it produces text the reader copies into
whatever assistant they already use. Its three language editions live in `ask-ai.js`,
because the reader reads the handover before pasting it.

## Reader appearance and universe notation

The existing top-right half-circle opens **Appearance** (`appearance.js` and
`appearance.css`). Page mode is system/light/dark; the light and dark code
palettes are saved independently in `bedrock-code-palettes`. The previous
`bedrock-theme` preference remains compatible. Storage failure falls back to
session-only changes; unknown palette names fall back to the unchanged default.
The synchronous head script applies preferences before paint. System changes,
other tabs and existing/new definition-modal frames share the same state.

Default Agda token colours are preserved. Four additional families have both
light and dark adaptations:

- [GitHub](https://github.com/primer/github-vscode-theme): restrained neutral surfaces.
- [Solarized](https://ethanschoonover.com/solarized/): warm light / blue-green dark surfaces.
- [Catppuccin](https://github.com/catppuccin/palette): Latte and Mocha.
- [Gruvbox](https://github.com/morhetz/gruvbox): warm, muted retro colours.

These are Bedrock semantic adaptations, not copies of editor token grammars.
Definitions, constructors, modules, fields, word keywords and amber symbolic
keywords map to the existing `--code-*` tokens. Selected low-contrast original
colours are adjusted: new text colours meet 4.5:1 on their code surface and on
the corresponding page surface. Type/boilerplate popups, inline and single-line
code, prose definition references and modal code use the same variables.
Non-code UI uses separate surface, separator, focus and elevation tokens;
changing a code palette does not recolour navigation, tables or reading routes.
UI polish retains reading widths, code gutters, QED alignment and interactions.
The final child of a submodule, including a QED ending, has no paragraph-after
margin; the folded container supplies its small bottom padding instead.

`universe-levels.js` is a presentation-only mathematical lens. It recognizes
linked universe primitives `ℓ-zero`, `ℓ-suc`, `ℓ-max`, recursively rendering
`(ℓ-max ℓ-zero (ℓ-suc ℓ))` as `0 ⊔ ℓ⁺`. Joins under successors retain parentheses;
no algebraic simplification is performed. Quiet mathematical lettering and a
subtle dotted underline identify the source-reveal interaction, without a box,
coloured background or double border. The original
Agda text, anchors, semantic links and Unicode offsets remain in a clipped,
inert source span. A CSS-generated label changes only presentation. The existing
`data-hover-html` boilerplate popup displays the original highlighted fragment,
with the same nested hover, gestures and modal engine; its raw source is exempt
from expression rewriting. Inline, block, dynamically loaded hover and modal code all
use this one decorator. Unknown, incomplete, import/renaming and multiline
expressions retain their original presentation. Plain `0`, `⊔`, `⁺` and
same-spelled local functions are never interpreted as universe operations.

All `ℓ` names (including trailing primes and numeric subscripts/superscripts)
share this quiet lettering throughout the rendered document, including prose
and raw-source popups. This is an explicit book-wide naming convention, not
inference from a name's shape. Other names use compiler `Level` type metadata
(`data-universe-level`) or explicit `Level` binders in type signatures. Links,
source text and hover targets remain intact; operator names such as `ℓ-max`
are not mistaken for parameters. Dynamic popups use the same decoration pass.

Level lettering uses a self-hosted subset of Noto Sans Math 3.000, at normal
size and weight, without changing its muted colour. The regular sans-serif
shape was compared with JuliaMono, STIX Two Math and the former enlarged serif
stack in both modes. `scripts/site/build-universe-font.py` verifies the upstream
TTF checksum, preserves OFL metadata, and renames the subset
to Bedrock Universe Levels. The font applies only to level parameters and
rewritten level expressions, not other code, prose or dotted operators.
Noto omits Unicode sub/superscript digits; the subset derives these from its
own digits using its MATH scaling and baseline constants, avoiding mixed-font
suffixes. Other retained glyph outlines are unchanged.
Upstream: <https://github.com/notofonts/math/releases/tag/NotoSansMath-v3.000>.

The reader glossary automatically links record type / 记录类型 / レコード型
to their introduction in Base.Prelude. Moving between levels is a subsection
of Universe levels. Sidebar content-tree expanders use trailing down/up
chevrons without changing their heading hierarchy or link targets.

Module applications in `open`/`import` declarations are not term applications.
Agda's telescope checker uses a dummy result type for them; the compiler trace
overlay rejects internal `Dummy` nodes, and the normalizer cleans legacy trace
payloads too. Such module-application ranges have no type hover or node colour;
their arguments retain ordinary hover help. Never display `__DUMMY_TYPE__`
or its internal call stack as a purported mathematical type.

Tests: `make test`, plus `/appearance-regression` and `/universe-regression`
from `scripts/tests/serve-boilerplate-regression.py`. The latter checks source
and anchor preservation, precedence, recursive hover, persistent simulated-touch
popups and modal opening. Keep the existing `/regression`, `/padding-regression`
and `/directory-regression` checks for shared interaction/layout changes.

## Licensing

All first-party code here (`template.html`, `static/bedrock.css`, `static/bedrock.js`,
`static/ask-ai.js`, `static/ask-ai.css`, and the
renderer) is **AGPL-3.0-only**, the repository's default; that folds in the front-end assets
adapted from [the 1lab](https://1lab.dev) and the vendored 1lab tree under `vendor/1lab/` (also
AGPL-3.0). The self-hosted fonts under `static/fonts/` are **OFL-1.1**, and the brand assets
under `static/assets/` are **CC BY-NC-SA 4.0** (the project content
license). Per-file terms are
declared in [`REUSE.toml`](../REUSE.toml) and verified by `reuse lint`; attributions and the
AGPL section 13 source statement are in [NOTICE](../NOTICE).
