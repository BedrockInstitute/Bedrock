# docs

**User-facing** documentation: the mathematics and the project itself, written for readers
rather than contributors. The literate chapters under `src/` also contain trilingual
content. This file is an
English developer-facing folder guide; the rule set is [AGENTS.md](../AGENTS.md).

## Layout

One subtree per language, the same filenames in each:

- `en/`: English. Currently `CHARTER.md`. The English project README is the repo-root
  [README.md](../README.md), not here.
- `zh/`: Chinese. `CHARTER.md`, `README.md`.
- `ja/`: Japanese. `CHARTER.md`, `README.md`.

`README.md` is the both-audiences exception, so it follows the user (trilingual) rule: the
English original is at the repo root, and its translations are `docs/zh/README.md` and
`docs/ja/README.md`. The `CHARTER` is the full methodological and philosophical statement that
the README condenses.

## Rules

- All content here is **trilingual**. Add a page in every language, and keep the same filename
  across `en/`, `zh/` and `ja/`.
- **Author in English first**, then translate the Chinese and Japanese from the English, then
  **cross-check the two translations against each other**. `check-glossary.py` enforces the
  confirmed renderings from [site/glossary.toml](../site/glossary.toml).
- `lint-prose.py` machine-checks the CJK conventions: full-width punctuation, `「」` quotes, no
  em dash, and spacing.
- Durable authoring specifications and instance configuration live in
  [site/](../site/README.md), in English. [dev/](../dev/README.md) holds temporary
  development and research work, not permanent configuration.
