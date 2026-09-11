# Translation glossary

This is the **canonical, machine-checked glossary** for Bedrock's trilingual docs. It exists
to stop terminology drift: when the same English term is translated again and again by
different passes (often by AI agents), the rendering tends to wander. The glossary fixes the
rendering once, and `scripts/gate/check-glossary.py` enforces it.

The term data lives in **[`glossary.toml`](glossary.toml)**, the single source of truth the
checker reads (via `tomllib`, so Python 3.11+). This document is the human-readable
explanation: what the checks do and how to maintain an entry. There is only one copy of the
data, so nothing can fall out of sync.

The same registry also controls reader-facing term introductions and quick review on the
website. It does not duplicate this data in a second pedagogical glossary. The site generates
one language-local `terms.json` from `glossary.toml`; that JSON is a build artifact.

## How it works

The checker runs two complementary checks, both part of `make check` (the commit gate) and the
pre-commit hook, so drift is caught in CI, not in review. Both are **report-only**: they never
rewrite text, because the right fix is a translation judgement, not a mechanical substitution.

1. **Avoid check (a denylist).** For every entry's `avoid` list it scans language-scoped prose
   (`docs/zh/`, `docs/ja/`, and the `<!--zh-->` / `<!--ja-->` prose of `src/**.lagda.md`
   masters) and flags any known off-glossary rendering, pointing at the canonical one.
   Explicit `en:` aliases are checked in English with word boundaries; untagged
   aliases keep their existing CJK-only meaning. Code and links stay protected.
2. **Presence check (a safety net).** For an entry with `presence = true`, when the English
   term appears in a doc's English source but the canonical rendering is absent from the
   parallel translation, it warns. This catches wrong renderings the `avoid` list does not
   enumerate. It runs on standalone parallel docs and explicitly translated
   language groups in masters. Missing language blocks retain English fallback
   and are not mistaken for translations. Each translated group is checked
   separately, so a correct term elsewhere cannot hide a local mismatch.

## Maintaining `glossary.toml`

Each term is a `[[term]]` entry. Under the owner's 2026-09-07 instruction, the
coordinator audits existing terms as well as new ones and makes the final
terminology decisions. Dispatches gather literature evidence, not independent
vocabularies. Search online for the actual mathematical sense in English,
Chinese and Japanese. Adopt an attested term when appropriate; if no suitable
term is found, record the queries and form a descriptive expression from
attested terminology. A negative search is not proof that a term never occurs.
Record supporting URLs and distinguish direct attestation from a composed
expression. Update the canonical table before agents resume dependent prose.
This owner instruction replaces the former approval protocol. An entry has this shape:

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
- **`avoid`** is a list of known wrong renderings. Tag an item with a language (`en:...`, `zh:宪章`,
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

## Reader-facing terms

Every technical concept named for textbook readers must use the reader-facing extension.
Entries that exist only to guide editors, route labels or development prose do not. This
distinction is semantic and therefore reviewed with the prose rather than guessed from word
frequency:

```toml
id = "host-environment"
audience = "reader"
introduced_in = "Base.Prelude"
matching = "auto"
recap_en = "The Cubical Agda environment that supports the formalisation of the object theory."
recap_zh = "承载对象理论形式化的 Cubical Agda 环境。"
recap_ja = "対象理論の形式化を支える Cubical Agda の環境。"
```

`id` is a stable concept identifier and must not be derived anew when a rendering changes.
`introduced_in` names the chapter containing the formal introduction. The three `recap_*`
fields contain the short, language-local review shown on hover or focus. Keep literature and
editorial evidence in `notes`; it is not reader-facing copy.

Use `matching = "auto"` only when every occurrence of the canonical rendering has the same
technical meaning. The renderer links those later occurrences automatically, preferring longer
forms. Use `matching = "explicit"` for short or ambiguous forms such as Chinese 层. Such an
occurrence must use an explicit term-reference marker. Optional `forms_en`, `forms_zh` and
`forms_ja` arrays list audited inflected or alternate surface forms.

The first introduction is marked in each language with the same stable identifier:

```markdown
[host]{.term-intro #host-environment}
[宿主]{.term-intro #host-environment}
[ホスト]{.term-intro #host-environment}
```

For an explicitly matched later occurrence, replace `term-intro` with `term-ref`. The
`check-term-introductions.py` gate requires exactly one introduction in every language, checks
the declared module and rendering, and rejects unknown identifiers.
