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

- Reader-facing content is **trilingual**; this English directory guide is not
  a translated reader page. Add a reader page in every language, and keep the same filename
  across `en/`, `zh/` and `ja/`.
- **Author in English first**, then translate the Chinese and Japanese from the English, then
  **cross-check the two translations against each other**. `check-glossary.py` enforces the
  confirmed renderings from [site/glossary.toml](../site/glossary.toml).
- `lint-prose.py` machine-checks the CJK conventions: full-width punctuation, `「」` quotes, no
  em dash, and spacing.
- Durable authoring specifications and instance configuration live in
  [site/](../site/README.md), in English. [dev/](../dev/README.md) holds temporary
  development and research work, not permanent configuration.

## Maintenance checks

Keep the three project READMEs synchronized for status badges, installation,
directory ownership and framework instructions. Dates on measurements describe
historical snapshots, not fresh acceptance. Resolve relative links from each
translation's own directory. The source book's chapter titles and review badges
come from `site/reading-catalog.json`, not these README files.

Run `make lint` after documentation changes. The
[scripts index](../scripts/README.md) explains individual checks; this gate does
not test external URLs or certify website rendering. Developer and CI guides
live in [site/](../site/README.md) and
[.github/workflows/](../.github/workflows/README.md), not in the reader translations.
