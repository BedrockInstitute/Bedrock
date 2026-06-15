# Contributing to Bedrock

This guide is written primarily for **AI-agent contributors** (and humans). It collects the
project's working rules in one place.

> **This project is very early, and this guide is incomplete.** The absence of a rule here
> does **not** mean there is no rule: it may simply not be documented yet. When you are
> unsure about anything, do **not** guess. Stop and ask the repository owner explicitly, and
> wait for an answer before proceeding. Surfacing a question is always preferred over a
> confident wrong assumption.

## Documentation taxonomy (user docs vs developer docs)

Bedrock separates documentation by audience, and the two follow different language rules:

- **User-facing docs** (the mathematics and the project itself) are **trilingual** in
  English, Chinese, and Japanese, and live under `docs/<lang>/` (e.g.
  `docs/{en,zh,ja}/CHARTER.md`).
- **Developer-facing docs** (how to contribute, conventions, specs) are **English only** and
  live in `dev/` (e.g. [dev/STYLE-i18n.md](dev/STYLE-i18n.md)), plus this `CONTRIBUTING.md`
  and `scripts/README.md`. Do not translate developer docs.
- **`README.md` is the exception:** both audiences read it, so it follows the **user** rule
  and is trilingual (the English `README.md` at the repo root, with `docs/zh/README.md` and
  `docs/ja/README.md`). Any document that both audiences read is treated as a user doc.

This taxonomy is itself a rule, recorded here. If you add a document, place it by audience.

## Prose conventions (all languages)

Enforced by `scripts/lint-prose.py` and the pre-commit hook (see Tooling below):

- **No em dash** anywhere (`—` U+2014, `―` U+2015, the Chinese `——`). Rewrite with a comma,
  colon, period, or parentheses, or split the sentence. The en dash `–` (numeric ranges) and
  the hyphen `-` are allowed. The Japanese long-vowel mark `ー` is not a dash and is fine.
- Inside ` ```agda ` code blocks: **English only**, no CJK and no full-width symbols. Agda's
  own Unicode operators (`≡ ℕ λ Δ₀ →` and the like) are fine. The CJK prose rules below do
  not apply inside code blocks.

### CJK prose (Chinese and Japanese)

- **Full-width sentence punctuation.** Chinese uses `，。；：！？`; Japanese uses the
  ideographic comma and period `、。` (and full-width `；：！？` where needed). Do not use
  half-width `, ; : ! ?` in CJK context (they are fine in code, URLs, and Latin fragments
  like `Cohen (1963)`). Do not "correct" a Japanese `、` to `，`.
- **Quotes** use the corner brackets `「」`. No `"…"`, no `'…'` as quotation marks, and no
  quote nesting. English apostrophes (`V's`) are kept.
- **Parentheses stay half-width `()`** (not full-width), with English-style outer spacing:
  one space before `(` and after `)` (e.g. `经典原理 (LEM、AC) 是…`), no space just inside.
- **No space between two CJK characters**; **no space adjacent to a full-width symbol**.
  Latin-to-CJK spacing elsewhere (`V 的`, `ZF 公理`) is normal and kept.
- **Reflow long CJK paragraphs onto one line.** A hard line break between two CJK characters
  renders as a stray space in Markdown, so write CJK paragraphs as single long lines; break
  only at a Latin word boundary where the space is wanted.

Most of the above is auto-fixable: run `python3 scripts/lint-prose.py --fix <files>`. Em
dashes, single quotes, and quote nesting are reported but must be rewritten by hand.

## Literate Agda and the i18n marker grammar

- Each module is **one master `.lagda.md`** under `src/`: the Agda code appears once, prose
  for every language lives in the same file wrapped in `<!--en--> / <!--zh--> / <!--ja--> /
  <!--/-->` markers, and code blocks are language-neutral (shared). The code can never drift
  between languages because it exists once. Full grammar: [dev/STYLE-i18n.md](dev/STYLE-i18n.md).
- Markers appear only in prose, never inside a ` ```agda ` fence.
- The initial site is **bilingual (en + zh)**; Japanese is **pre-supported** (add a `<!--ja-->`
  block and enable `ja` in the build). Adding a language never touches the code.
- **Woven mono-lingual `.lagda.md` are not committed.** They are an on-demand `make gen`
  output (for `agda --html` compatibility). Everything generated lives under `_build/`
  (git-ignored); never commit generated files.

## Translation workflow

Translate from English, then **cross-check against the Chinese** (the owner's tuned
reference) for mistranslation, omission, addition, and term drift. Prefer **meaning over
literal calque**.

Confirmed term renderings live in the **canonical glossary [dev/GLOSSARY.md](dev/GLOSSARY.md)**,
which `scripts/check-glossary.py` machine-enforces via `make check` (so a wrong rendering is
caught in CI, not review). Consult it before translating, and when you confirm a new
load-bearing term, **add a row there** rather than recording it anywhere else. For a term not
yet in the glossary, choose by meaning and surface the choice to the owner.

## Tooling and the build

- **`make check` is the gate before any commit:** it typechecks the masters
  (`agda src/Everything.lagda.md`), validates i18n markers, runs the prose linter, and runs
  the glossary checker (`scripts/check-glossary.py`, against [dev/GLOSSARY.md](dev/GLOSSARY.md)).
- **`make site`** builds the multilingual hyperlinked site into `_build/site`;
  **`make serve`** previews it; **`make gen`** weaves the on-demand mono-lingual copies.
- **`make hooks`** activates the version-controlled pre-commit hook
  (`scripts/git-hooks/pre-commit`), which runs the prose linter and marker check on staged
  files. Activate it once per clone.
- The tooling is documented in [scripts/README.md](scripts/README.md). It needs only Agda
  2.8.0 + cubical 0.9 and Python 3 for `make check`; the site build also uses Node only at
  deploy time (KaTeX and fonts load from a CDN).

## Working norms for AI agents

- **Verify load-bearing assumptions cheaply before committing to heavy or hard-to-reverse
  work** (large installs, forks, multi-hour builds, framework choices). Run the cheapest
  decisive probe first and report the finding.
- **Surface genuine architecture forks to the owner** with a recommendation, rather than
  charging ahead on one interpretation.

## Licensing

Project content (everything under `src/`, `docs/`, `dev/`, and the repository's scripts) is
licensed CC BY-NC-SA 4.0. The documentation site's front-end is adapted from
[the 1lab](https://1lab.dev) and is AGPL-3.0; see [NOTICE](NOTICE). Keep the two clearly
separated and credited.

## Deployment

Deployment is automatic: on every merge to `main`, GitHub Actions builds the site and
publishes it to Cloudflare Pages (bedrock.institute) and GitHub Pages. Contributors need do
nothing and never handle deployment credentials.

The Cloudflare credentials live only as GitHub Actions encrypted repository secrets; they
are never committed, never printed in logs, and not visible to contributors. The one-time
owner setup is documented in `.github/workflows/cloudflare.yml`.
