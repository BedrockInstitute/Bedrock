# Translation glossary

This is the **canonical, machine-checked glossary** for Bedrock's trilingual docs. It exists
to stop terminology drift: when the same English term is translated again and again by
different passes (often by AI agents), the rendering tends to wander. The glossary fixes the
rendering once, and `scripts/check-glossary.py` enforces it.

The term data lives in **[`glossary.toml`](glossary.toml)**, the single source of truth the
checker reads (via `tomllib`, so Python 3.11+). This document is the human-readable
explanation: what the checks do and how to maintain an entry. There is only one copy of the
data, so nothing can fall out of sync.

## How it works

The checker runs two complementary checks, both part of `make check` (the commit gate) and the
pre-commit hook, so drift is caught in CI, not in review. Both are **report-only**: they never
rewrite text, because the right fix is a translation judgement, not a mechanical substitution.

1. **Avoid check (a denylist).** For every entry's `avoid` list it scans the CJK docs
   (`docs/zh/`, `docs/ja/`, and the `<!--zh-->` / `<!--ja-->` prose of `src/**.lagda.md`
   masters) and flags any known off-glossary rendering, pointing at the canonical one.
2. **Presence check (a safety net).** For an entry with `presence = true`, when the English
   term appears in a doc's English source but the canonical rendering is absent from the
   parallel translation, it warns. This catches wrong renderings the `avoid` list does not
   enumerate. It runs only on standalone parallel docs (`docs/en/X` vs `docs/zh/X` /
   `docs/ja/X`, and the root `README.md` for the localized READMEs), never on masters, whose
   in-file language fallback would make absence ambiguous.

## Maintaining `glossary.toml`

Each term is a `[[term]]` entry. Add one when a load-bearing term gets a confirmed rendering:

```toml
[[term]]
category = "Set theory"        # human grouping only; the checker ignores it
en = "forcing"
zh = "力迫"
ja = "強制"
avoid = ["zh:宪章", "ja:憲章"]   # optional; omit if none
presence = true                # optional; omit for an advisory-only entry
notes = "..."                  # optional; human-only, the checker ignores it
```

- **`en` / `zh` / `ja`** are required: the term and its canonical Chinese and Japanese
  renderings. Values are plain strings (TOML is not prose-linted, so no backtick wrapping is
  needed, unlike in this Markdown doc).
- **`avoid`** is a list of known wrong renderings. Tag an item with a language (`zh:宪章`,
  `ja:憲章`) to scope it to that language; an untagged item (`散文`) applies to both Chinese and
  Japanese. Omit `avoid` for an advisory-only entry (agents read the term; the Avoid check does
  not enforce it).
- **`presence = true`** enables the safety-net check. Use it for distinctive terms whose
  canonical rendering should always be present; omit it for common English words (where the
  English term may appear in prose that does not call for the term), to avoid false warnings.
- **`notes`** and **`category`** are human-only and ignored by the checker.
- **False positive?** Put `<!-- glossary-ignore -->` on the line for the Avoid check, or
  `<!-- glossary-ignore: charter -->` to suppress one term. For the Presence check, the scoped
  form anywhere in the translated doc suppresses that term's presence warning for that doc.

Renderings in `glossary.toml` are taken verbatim from the owner's tuned parallel docs (the
en/zh/ja `CHARTER.md` and `README.md`). Where Chinese and Japanese deliberately diverge (for
example `forcing` is `力迫` in zh but `強制` in ja), the `notes` say so; do not "unify" them.
