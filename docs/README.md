# docs

**User-facing** documentation: the mathematics and the project itself, written for readers
rather than contributors. This is the one place **trilingual** content lives. This file itself
is an English developer-facing folder guide (the doc taxonomy is in
[AGENTS.md](../AGENTS.md)).

## Layout

One subtree per language, the same filenames in each:

- `en/`: English. Currently `CHARTER.md`. (The English project README is the repo-root
  [README.md](../README.md), not here.)
- `zh/`: Chinese. `CHARTER.md`, `README.md`.
- `ja/`: Japanese. `CHARTER.md`, `README.md`.

`README.md` is the both-audiences exception, so it follows the user (trilingual) rule: the
English original is at the repo root, and its translations are `docs/zh/README.md` and
`docs/ja/README.md`. The `CHARTER` is the full methodological and philosophical statement that
the README condenses.

## Rules

- All content here is **trilingual** (en + zh now; ja pre-supported). Add a page in every
  language, keeping the same filename across `en/`, `zh/`, and `ja/`.
- **Author in English first**, then translate the Chinese and Japanese from the English, then
  **cross-check the two translations against each other**. Confirmed term renderings are
  enforced from the canonical glossary data [dev/glossary.toml](../dev/glossary.toml).
- CJK prose conventions (full-width punctuation, `「」` quotes, no em dash, spacing) are
  machine-checked; see [AGENTS.md](../AGENTS.md) and `scripts/lint-prose.py`.
- Developer specs do **not** go here; they live in [dev/](../dev/) and are English-only.
