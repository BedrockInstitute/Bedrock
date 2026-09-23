# Multilingual literate Agda: the marker convention

> Developer documentation (English only). See [AGENTS.md](../AGENTS.md) for the
> full rulebook and the user/developer doc split.

Bedrock keeps **one master `.lagda.md` per module** as the single source of truth: the
Agda code appears exactly once, and prose for every language lives in the same file, wrapped
in invisible HTML-comment markers. Agda reads only ` ```agda ` blocks and ignores all prose,
so the code can never drift between languages. A weaver (`scripts/site/weave-i18n.py`) and the
site renderer (`scripts/site/render-site.py`) both read these markers; the linter
(`scripts/gate/lint-prose.py`) validates them.

## Grammar

```text
<!--en-->
English prose.
<!--zh-->
中文文稿。
<!--ja-->
日本語の文章。
<!--/-->
```

- `<!--en-->`, `<!--zh-->`, `<!--ja-->` open a **language group** and switch the current
  prose language. `<!--/-->` closes the group.
- Prose **outside** any group is **shared**: copied to every language verbatim. Use it for
  language-neutral notation, figures and code. Chapter and subsection headings
  belong in matched language groups.
- For language `L`, a tool keeps the shared prose plus only the `<!--L-->` sub-block of each
  group. If a group has no `<!--L-->` sub-block, the renderer falls back to English (or the
  first present language). A page with no group in the requested language gets a
  "not yet translated" banner. On the website, untranslated English narrative
  remains available in closed, locally labelled disclosures; code and shared
  mathematical notation stay visible. The plain-text weaver retains its original
  fallback behavior.
- Adding a language = adding a marker. The mechanism is N-language by construction.
  The current writing phase completes all chapter prose in all three languages;
  fallback remains available while unfinished passages are being migrated.

## Rules (enforced)

1. **Markers sit on their own line**, matching `^\s*<!--(en|zh|ja|/)-->\s*$`. Nothing else
   on the line.
2. **Markers appear only in prose, never inside a ` ```agda ` fence.** Code is
   language-neutral and shared across all languages; conditionalising code per language is
   forbidden (it would break cross-language anchor stability). Close the language
   group before opening any Agda fence: placing an entire code block inside one
   language also hides the proof from the other editions. The marker linter rejects it.
3. **Groups are balanced and non-overlapping:** every opener is eventually closed by
   `<!--/-->`; a new opener stays part of the same group until `<!--/-->`. Do not nest
   groups.
4. Only the known language codes `en`, `zh`, `ja` may appear.

## Prose conventions

Write titles, introductions and detailed explanations in `en`, `zh` and `ja`.
Each language must retain the mathematical substance of the whole passage;
adding a short Japanese summary to a long bilingual group would hide the rest
of that passage in the Japanese book. The chapter-framework gate checks matching
heading levels and an opening paragraph before code. The glossary gate also
checks opt-in terms within each explicitly translated group.

Interleave a complete trilingual explanation before each group of one to five
nonempty physical Agda lines. Split long definitions into meaningful steps,
including within signatures and local blocks, while preserving every original
code line and its indentation. Write a mathematics textbook: develop the chapter's
question through definitions, intuition, useful examples and justified arguments.
The paragraphs must form a continuous explanation even when the code is hidden;
the code supplies the corresponding formal expression. Do not turn each chunk
into an independent annotation of imports, declarations or implementation steps.
Explain Agda syntax where the learner needs it, without repeating language-setup
lessons in every chapter. Read the complete module and the actual definitions of relevant
dependencies before writing; existing prose is not evidence that a mathematical
claim is correct. Chapter introductions and local explanations should complement
each other rather than repeat the same facts.

Review the whole subsection before checking individual prose/code pairs. A
reader should be able to identify the question, the relevant assumptions, the
reasoning and the result. Hiding code is a test of this narrative structure,
not a requirement to repeat every displayed formula in words. Reject a sequence
of individually accurate annotations if it never develops that structure.

Measure explicit prose relative to code separately for each language. A high
ratio should reflect useful explanations, examples and mathematical connections,
not repeated definitions, boilerplate or unsupported claims. The detailed
exposition gate is `scripts/gate/check-literary-exposition.py --check`.

CJK prose (zh and ja) follows the repository's house style enforced by
`scripts/gate/lint-prose.py`: full-width sentence punctuation `，；：！？` and corner-bracket quotes
`「」`, half-width parentheses with English-style outer spacing, no em dash, no space between
CJK characters. Japanese prose consistently uses plain style (である体). It does not use polite
です・ます forms. Agda code blocks are English-only. See the gate commands in `Makefile`.

Standalone construction, lemma, theorem and corollary labels name the corresponding Agda declaration and
contain no period: `**Lemma** (`name`{.Agda}) Text`, with `引理` or `補題` in the
parallel routes. Fact labels use the same form with `Fact`, `事实` or `事実`, and
construction labels use `Construction`, `构造` or `構成`. Corollary labels use
`Corollary`, `推论` or `系`.
Proof labels use `**Proof** Text`, `**证明** 正文` or `**証明** 本文`. An outermost
construction, fact, lemma, theorem or corollary developed through prose and code ends its proof
with a standalone `∎` after the final proof code block. Explanatory prose may follow the mark and
is then outside the proof. A construction or lemma nested inside that proof, such as one inside
its disclosure or foldable submodule, has no separate `∎`; the enclosing
proof's mark follows the closing block.

## Foldable submodules

Every first- or second-level submodule uses `details.submodule-fold`, expanded by
default. Its `summary.submodule-fold-heading` contains exactly one Agda fence
holding the complete `module … where` declaration, alone but on as many lines as
its arguments require. The declaration itself remains visible when the
reader folds the module. Put all subsequent prose, figures and Agda code in
`div.submodule-fold-content`, and close that container immediately after the
submodule's last Agda code block. Put any closing `∎` outside the fold.
Leave a blank line before the opening `<details>` when it follows an Agda fence;
otherwise Markdown treats it as inline text rather than a fold.
An inner submodule uses the same fold inside its parent's content, but folds
stop at two levels: an outer submodule and one inner submodule. Deeper Agda
modules remain unfolded and are still checked by the lint inventory. In the rendered
HTML, code in each fold loses only the indentation contributed by its enclosing
module declarations; the Agda source and Markdown mirror retain the original
indentation. The inner declaration is likewise shown without its source indent.
The header is shared code, so it needs no trilingual summary label; the surrounding
exposition remains parallel. The site animates opening and closing, including
keyboard activation. Do not add another toggle, hidden state or persisted state.
`lint-prose.py` checks the complete declaration, default-open state, code scope,
whole-tree coverage and two-level nesting limit. A long signature is indivisible,
so the literary fence-size check exempts a fold heading.

Short ancillary interface explanations may still use `details.prose-disclosure`,
as in the Prelude's compiler options. Their localized titles begin with
`Optional:`, `选读：` or `発展：`. See [renderer recipes](RENDERER-RECIPES.md)
for the canonical markup and first uses of reusable styles.

## Inline Agda references in prose

Inside prose you may reference an Agda identifier with a Pandoc attribute span:

```markdown
the addition `_+_`{.Agda} is associative
```

The renderer renders `` `_+_`{.Agda} `` highlighted and hyperlinked to its
definition. A temporary variable such as `` `x`{.Agda} `` has the same code styling
but no link. Every inline code span that uses
Agda notation carries `{.Agda}`; this includes bound variables, complete expressions,
keywords and module names. Ordinary mathematical notation belongs in inline LaTeX
instead of an unmarked code span.

When the reader-facing label differs from the declaration name, use
`[V](V.Hierarchy.html#𝒮ᵥ){.Agda}`. The link and type hover resolve to `𝒮ᵥ`, while
the prose displays `V`. The target must be an internal Agda declaration.

In every chapter, including `Milestones`, an unboxed Agda link may label only
one defined name. Put an application, type annotation, path or equation in one
complete `` `...`{.Agda} `` span, including its operators and arguments. Write
bound variables such as `` `x`{.Agda} `` as inline code too; the renderer does
not link temporary variables to unrelated same-named code tokens. The lint gate checks this
structurally in every chapter. Existing bare-variable lines outside the refined
opening chapters are recorded by exact line hash in `dev/inline-agda-legacy.json`:
new lines and edited lines must pass, and the inventory should shrink as those
chapters are revised.

## Reader-facing terminology

Every technical concept named for textbook readers is registered with
`audience = "reader"` in `dev/glossary.toml`. Its first formal introduction uses
`[rendering]{.term-intro #stable-id}` in each language. Later occurrences are linked
automatically only when the glossary entry sets `matching = "auto"`; ambiguous entries use
`[rendering]{.term-ref #stable-id}`. The stable identifier and localized hover recap live in
`dev/glossary.toml`. Do not duplicate that metadata in chapter-local HTML or JavaScript.

## Centered single-line code

For a short expression that should look like code but must not enter the Agda code
stream, use one complete line. Add a localized `data-note` annotation when the
expression needs an expandable explanation:

```html
<div class="single-line-code" data-note="说明这行记号的形式化程度"><code>`Type ℓ : Type (ℓ-suc ℓ)`{.Agda}</code></div>
```

Without an annotation, use the same element without `data-note`. The `data-note`
value is a reader-facing comment attached to the notation. On wide
screens it appears outside the right edge of the prose block, aligned with the
centered expression; on narrow screens the reader can tap or focus the expression to
open the note as a toast. Keep the note in the language block where it appears. The
`lint-prose.py` gate enforces this one-line form. Do not replace such displays with
LaTeX. The complete expression inside `<code>` is one `{.Agda}` span, rather than a
mixture of highlighted and plain fragments.

## Math

In the book's type-theoretic exposition, write `=` for judgmental equality and
`≡` for path equality. A defining equation uses `=` where other texts often use
`:=`; judgmental equality also covers equality by computation, so do not identify
it solely with the act of assigning a definition. A path `p : x ≡ y` is an
inhabitant of an equality type, whereas judgmental equality is a judgment of the
type system. Introduce this convention in Base.Prelude, Equality and paths.

Use bare Unicode for single symbols where possible. Reserve LaTeX for real expressions:
`$...$` inline and `$$...$$` (kept blank-line-separated) for display. Math is rendered at
build time by KaTeX; both GitHub and the standard Agda toolchain also pass it through.
Choose inline code or LaTeX by the notation used, not by whether the passage is
mathematical. Expressions following Agda conventions, such as `x ≡ y`,
`p : x ≡ y`, `refl`, and references to Agda variables, keep inline code styling.
The book's Agda-style defining `=` also keeps that styling. Use inline LaTeX for
ordinary mathematical notation being contrasted with Agda, such as `$x = y$`,
`$\mathrel{:=}$`, or a lambda expression written with a dot rather than Agda's
arrow. Do not convert a mixed passage wholesale to either format.

In diagrams, arrowheads are reserved for functions and their action on elements.
Do not use them merely to connect related objects. Use equivalence notation for
equivalences, and unarrowed dashed lines for grouping or
assembling data. This is a reader preference established on 2026-09-22.
Let the distinct objects and maps determine a commutative diagram's shape. For a
map factoring through a third type, draw a triangle; do not repeat the codomain
and add an identity map merely to fill out a square.
Draw ordinary paths as blue lines without arrowheads, with white endpoint dots. Use a blue
outline around the dots so they remain visible in a light theme. Equality signs
remain appropriate inside formulas; a diagram's path connection uses this visual
style instead. The constant path `refl` is represented by a single endpoint,
not a nontrivial loop. Higher paths such as `p ≡ q` are exempt from this visual
rule; a filled region or an equality label may express them instead.

## Shared diagram components

Every textbook figure uses `book-diagram`, a stable `fig-*` id, and a direct
`figcaption` with explicit English, Chinese and Japanese text. Its
`aria-describedby` points to `fig-id-caption`. Put the relevant explanation
and hypotheses before the figure; use the caption for a short, recognizable
takeaway. Do not introduce the next topic in a caption. Separate successive
figures with substantive prose, without adding formulaic transition paragraphs.

Keep the `figure` element itself unframed. When an enclosing frame is needed, put
`diagram-framed` on one direct child `div` containing the diagram's formulas, spaces
and labels, as in `fig-proposition-and-proof`. Put the overall description in a
following sibling `figcaption`, always outside the frame. The frame is not a type space.
`check-diagrams.py` rejects framing the figure/caption or putting the caption inside
the content wrapper. Do not imitate an older screenshot that violates this rule.
Use `diagram-panel` for neutral layout panels,
and `diagram-space` (HTML) or `diagram-space-shape` (SVG) for a mathematical
type space. Do not nest decorative panels. The homotopy-level comparison has
three panels and implication connectors, with no enclosing frame. Logical
implication symbols remain appropriate between conditions; they are not paths.

All visual tokens live in `site/static/bedrock.css`: 8px corners, 1px box
borders, shared padding and gaps, theme-aware surfaces, blue paths, and white
points. Chapter markup may set only label positions and aspect ratios inline.
Figures scroll only with the page: never introduce an internal scroll container.
Every clickable animated figure signals interactivity with a shared blue color
pulse, not just a change in line width. Pulse only the objects that animate, never
the overall background or their containing type spaces. Use
`diagram-interaction-stroke-pulse` for fibre hairs and point outlines, and
`diagram-interaction-color-pulse` for a moving path-space lens. Stop during playback
and resume whenever another activation is available, including after contraction.
Keep ordinary paths blue and their endpoint dots white. Print output is static.
Use responsive layout for narrow screens; display math inside figures keeps visible overflow.
SVG geometry uses `viewBox`; its shared role classes are `diagram-path`,
`diagram-point`, `diagram-map-line`, `diagram-map-tip`, `diagram-guide`,
`diagram-centre-ring`, `diagram-higher-path`, `diagram-path-space`, and `diagram-space-shape`.
Use `diagram-path-space` for a schematic family of fixed-endpoint paths; its
shaded area denotes the family, not an inclusion into the ambient type.
Each ordinary path's start and end must coincide with a `diagram-point`.
`refl` may be a single point; higher paths may use a shaded region.

`scripts/gate/check-diagrams.py` checks every chapter, and runs in `make lint`
(therefore `make check`) and directly in the site renderer. It rejects missing
captions, unstyled figures, ad hoc paint, missing path endpoints and nested
decorative panels. Regression tests exercise rejected examples. This enforces
the visual grammar, not the mathematical meaning of an arrow or the quality of
the surrounding argument: those still require source review and desktop/mobile
preview in all three languages. Extend the shared components when a new layout
is needed; do not bypass the gate with a figure-local style.

The 2026-09-22 styling pass used
[UI UX Pro Max](https://github.com/nextlevelbuilder/ui-ux-pro-max-skill/blob/main/.claude/skills/ui-ux-pro-max/SKILL.md),
particularly its consistency, semantic color tokens, text reflow and readable
responsive layout guidance. The book's mathematical conventions take precedence.
