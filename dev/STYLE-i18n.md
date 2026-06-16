# Multilingual literate Agda: the marker convention

> Developer documentation (English only). See [AGENTS.md](../AGENTS.md) for the
> full rulebook and the user/developer doc split.

Bedrock keeps **one master `.lagda.md` per module** as the single source of truth: the
Agda code appears exactly once, and prose for every language lives in the same file, wrapped
in invisible HTML-comment markers. Agda reads only ` ```agda ` blocks and ignores all prose,
so the code can never drift between languages. A weaver (`scripts/weave-i18n.py`) and the
site renderer (`scripts/render-site.py`) both read these markers; the linter
(`scripts/lint-prose.py`) validates them.

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
  anything language-neutral (often nothing, but headings or figures can be shared).
- For language `L`, a tool keeps the shared prose plus only the `<!--L-->` sub-block of each
  group. If a group has no `<!--L-->` sub-block, the renderer falls back to English (or the
  first present language) and flags the page as "not yet translated".
- Adding a language = adding a marker. The mechanism is N-language by construction. The
  initial rollout is bilingual (`en` + `zh`); `ja` is pre-supported.

## Rules (enforced)

1. **Markers sit on their own line**, matching `^\s*<!--(en|zh|ja|/)-->\s*$`. Nothing else
   on the line.
2. **Markers appear only in prose, never inside a ` ```agda ` fence.** Code is
   language-neutral and shared across all languages; conditionalising code per language is
   forbidden (it would break cross-language anchor stability).
3. **Groups are balanced and non-overlapping:** every opener is eventually closed by
   `<!--/-->`; a new opener stays part of the same group until `<!--/-->`. Do not nest
   groups.
4. Only the known language codes `en`, `zh`, `ja` may appear.

## Prose conventions

CJK prose (zh and ja) follows the repository's house style enforced by
`scripts/lint-prose.py`: full-width sentence punctuation `，；：！？`, corner-bracket quotes
`「」`, half-width parentheses with English-style outer spacing, no em dash, no space between
CJK characters. Agda code blocks are English-only. See the `scripts/` README.

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
