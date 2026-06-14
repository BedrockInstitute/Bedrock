# scripts

Tooling for the repository. Currently one tool: a prose linter that enforces the
project's writing conventions.

## `lint-prose.py`

Checks Markdown prose (`*.md`, `*.lagda.md`; the verbatim `LICENSE` is excluded):

- Chinese sentence punctuation `, ; : ! ?` must be full-width `，；：！？` (auto-fixable).
- Chinese double quotes use the corner brackets `「」`, not `"…"` or `“…”` (auto-fixable).
- Parentheses in Chinese text stay half-width `()`, with English-style outer spacing
  (`经典原理 (LEM、AC) 是…`); no space between Chinese characters; no space after a
  full-width symbol (auto-fixable).
- Em dash (`—`, `―`, `——`) is banned everywhere; en dash `–` and hyphen `-` are allowed.
- Single quotes as Chinese quotation marks, and any quote nesting, are banned.

English apostrophes (`V's`) and English quotes (`"formal purity"`) are not in Chinese
context and are left untouched. Code spans, fenced blocks, links, and URLs are protected.

```sh
python3 scripts/lint-prose.py --check          # scan tracked files; exit 1 on any violation
python3 scripts/lint-prose.py --fix <files>    # auto-fix punctuation/quotes (dashes/nesting are manual)
python3 scripts/lint-prose.py --check --staged # only staged files (used by the hook)
```

## Pre-commit hook

`git-hooks/pre-commit` runs the linter on staged Markdown and blocks the commit on any
violation. It is version-controlled; activate it once per clone with:

```sh
git config --local core.hooksPath scripts/git-hooks
```
