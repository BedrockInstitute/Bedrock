# scripts

Repository tooling. English-only: this is developer documentation. User-facing docs
(`docs/<lang>/`) are trilingual; developer docs are English. Developer docs include `dev/`,
the root `AGENTS.md` and `CONTRIBUTING.md`, the per-directory `README.md` files such as this
one, and anything else written for contributors. See [AGENTS.md](../AGENTS.md) for the full
rulebook and the user/developer doc split. The marker grammar these tools share is specified in
[dev/STYLE-i18n.md](../dev/STYLE-i18n.md).

## The multilingual literate-Agda pipeline

A master `.lagda.md` per module holds the Agda code once plus prose for every language,
wrapped in `<!--en--> / <!--zh--> / <!--ja--> / <!--/-->` markers. From the masters:

```
src/**/*.lagda.md ──agda──────────────► typecheck (the proof gate)
        │
        ├─ weave-i18n.py ─► _build/woven/<lang>/…  (mono-lingual .lagda.md, on demand)
        │
        └─ render-site.py ─► _build/site/<lang>/…  (the hyperlinked multilingual site)
                 ▲   uses: agda --html  +  extract-types.py  +  vendored 1lab assets
```

Everything generated lives under `_build/` (git-ignored); nothing generated is committed.

## `i18n_markers.py`

The single canonical implementation of the marker grammar (parse / weave / validate),
imported by `weave-i18n.py` and `render-site.py` so the grammar can never drift. Not a CLI.

## `weave-i18n.py`

Weaves masters into per-language mono-lingual `.lagda.md` (kept on demand for
`agda --html` compatibility, never committed), and validates marker integrity.

```sh
python3 scripts/weave-i18n.py --check                 # validate markers (exit 1 on error)
python3 scripts/weave-i18n.py --lang zh FILE          # weave one master -> stdout
python3 scripts/weave-i18n.py --gen --out _build/woven  # weave all -> _build/woven/<lang>/
```

`--gen` also drops a per-language `bedrock.agda-lib` so each woven tree type-checks and
`agda --html`-es on its own (consume it outside the source project to avoid include-path
clashes with the root `bedrock.agda-lib`).

## `extract-types.py`

Extracts per-module identifier types for type-on-hover and typed search, on stock Agda
2.8.0, by driving Agda's batch interaction protocol (`agda --interaction-json`,
`Cmd_show_module_contents_toplevel`). No Haskell, no Agda-as-a-library.

```sh
python3 scripts/extract-types.py --out _build/types.json
```

## `render-site.py`

Builds the hyperlinked multilingual static site from the masters: runs `agda --html`,
weaves prose per language, splices the (language-neutral) highlighted code, resolves inline
`` `name`{.Agda} `` references, renders math (KaTeX) and Markdown, rewrites links, emits the
per-module `types/<Module>.json` (for hover) and per-language `search.json`, and wraps each
page in the vendored 1lab-styled template.

```sh
python3 scripts/render-site.py --out _build/site [--langs en,zh] [--base-url /Bedrock]
```

See the root `Makefile` (`make site`, `make serve`) for the orchestrated build.

## `lint-prose.py`

Enforces the project's CJK writing conventions on Markdown (`*.md`, `*.lagda.md`; the
verbatim `LICENSE` is excluded):

- Chinese sentence punctuation `, ; : ! ?` must be full-width `，；：！？` (auto-fixable).
- Chinese double quotes use the corner brackets `「」`, not `"…"` / `“…”` (auto-fixable).
- Parentheses in Chinese text stay half-width `()` with English-style outer spacing; no
  space between CJK characters; no space adjacent to a full-width symbol; CJK paragraphs are
  reflowed so a soft wrap never falls between two CJK characters. All auto-fixable.
- The i18n marker lines (`<!--en|zh|ja|/-->`) are treated as hard block boundaries, so
  reflow never merges prose across a language switch.
- Inline `` `code` ``, fenced blocks, links, URLs, and math (`$...$`, `$$...$$`) are
  protected from the CJK rules.
- Em dash (`—`, `―`, `——`) is banned; en dash `–` and hyphen `-` are allowed.
- Single quotes as Chinese quotation marks, and any quote nesting, are banned.
- Inside an `agda` fenced block, Chinese and full-width symbols are banned (translate to
  English); Agda's own Unicode (`≡ ℕ λ`) is fine.

```sh
python3 scripts/lint-prose.py --check          # scan tracked files; exit 1 on any violation
python3 scripts/lint-prose.py --fix <files>    # auto-fix punctuation/quotes (dashes/nesting are manual)
python3 scripts/lint-prose.py --check --staged # only staged files (used by the hook)
```

## `check-glossary.py`

Enforces the translation glossary so term renderings cannot drift between passes. Its data source
is [dev/glossary.toml](../dev/glossary.toml), read via `tomllib` (so Python 3.11+; use the `.venv`
from `make venv`); the human-readable explanation is [dev/GLOSSARY.md](../dev/GLOSSARY.md). For each
term's `avoid` entries it scans the CJK docs (`docs/zh/`, `docs/ja/`, and the `<!--zh-->` / `<!--ja-->`
prose of masters) and reports any off-glossary rendering, pointing at the canonical one. A
`zh:`/`ja:` tag scopes an avoided term to one language; an untagged one applies to both.
Code spans, fenced blocks, links and URLs are protected (shared with `lint-prose.py`).
Report-only, like the em-dash rule: there is no `--fix`. Suppress a genuine exception with
`<!-- glossary-ignore -->` (or `<!-- glossary-ignore: charter -->`) on the line.

```sh
python3 scripts/check-glossary.py --check          # scan tracked files; exit 1 on any violation
python3 scripts/check-glossary.py --check --staged # only staged files (used by the hook)
```

## Pre-commit hook

`git-hooks/pre-commit` runs fast source checks on staged Markdown (the prose linter, marker
integrity, and the glossary check) and blocks the commit on any violation. Version-controlled;
activate it once per clone (or run `make hooks`):

```sh
git config --local core.hooksPath scripts/git-hooks
```
