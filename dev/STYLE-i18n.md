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
`scripts/gate/lint-prose.py`: full-width sentence punctuation `，；：！？`, corner-bracket quotes
`「」`, half-width parentheses with English-style outer spacing, no em dash, no space between
CJK characters. Agda code blocks are English-only. See the gate commands in `Makefile`.

## Inline Agda references in prose

Inside prose you may reference an Agda identifier with a Pandoc attribute span:

```markdown
the addition `_+_`{.Agda} is associative
```

The renderer renders `` `_+_`{.Agda} `` highlighted and hyperlinked to the identifier's
definition, the same way it appears in a code block.

## Math

Use bare Unicode for single symbols where possible. Reserve LaTeX for real expressions:
`$...$` inline and `$$...$$` (kept blank-line-separated) for display. Math is rendered at
build time by KaTeX; both GitHub and the standard Agda toolchain also pass it through.
