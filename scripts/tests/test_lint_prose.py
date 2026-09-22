"""Focused tests for prose conventions enforced by lint-prose.py."""

import importlib.util
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "lint_prose", Path(__file__).resolve().parents[1] / "gate/lint-prose.py")
lint_prose = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(lint_prose)


class TheoremLabelTests(unittest.TestCase):
    def violations(self, text):
        return lint_prose.theorem_label_violations(text)

    def test_named_statements_and_proofs_accept_canonical_format(self):
        valid = "\n".join([
            "**Lemma** (`helper`{.Agda}) Text.",
            "**引理** (`helper`{.Agda}) 正文。",
            "**補題** (`helper`{.Agda}) 本文。",
            "**Fact** (`property`{.Agda}) Text.",
            "**事实** (`property`{.Agda}) 正文。",
            "**事実** (`property`{.Agda}) 本文。",
            "**Theorem** (`result`{.Agda}) Text.",
            "**定理** (`result`{.Agda}) 正文。",
            "**Corollary** (`consequence`{.Agda}) Text.",
            "**推论** (`consequence`{.Agda}) 正文。",
            "**系** (`consequence`{.Agda}) 本文。",
            "**Proof** Text.",
            "**证明** 正文。",
            "**証明** 本文。",
        ])
        self.assertEqual(self.violations(valid), [])

    def test_period_and_missing_statement_name_are_rejected(self):
        invalid = "\n".join([
            "**Lemma.** Text.",
            "**定理。**正文。",
            "**Theorem** Text.",
            "**证明。**正文。",
        ])
        self.assertEqual(len(self.violations(invalid)), 4)

    def test_numbered_milestone_heading_is_outside_named_statement_rule(self):
        self.assertEqual(self.violations("**Theorem 1.** Text."), [])

    def test_labels_inside_agda_fences_are_ignored(self):
        self.assertEqual(self.violations("```agda\n**Lemma.**\n```"), [])


class QedTests(unittest.TestCase):
    def test_default_open_optional_block_scopes_helpers_and_requires_outer_qed(self):
        text = '''**Theorem** (`result`{.Agda}) Text.
```agda
result = helper
```
<details open class="optional-reading" aria-labelledby="helper-title">
**Lemma** (`helper`{.Agda}) Text.
```agda
helper = proof
```
</details>
'''
        self.assertEqual(lint_prose.qed_violations(text + '∎\n'), [])
        self.assertEqual(len(lint_prose.qed_violations(text)), 1)

    def test_margin_note_does_not_make_following_statement_nested(self):
        text = '''**Theorem** (`result`{.Agda}) Text.
<aside class="prose-annotation-note">Note.</aside>
```agda
result = proof
```
∎
**Lemma** (`next`{.Agda}) Text.
```agda
next = proof
```
'''
        self.assertEqual(len(lint_prose.qed_violations(text)), 1)

    def test_top_level_construction_and_lemma_end_after_final_code_block(self):
        text = """**Construction** (`make`{.Agda}) Text.
<!--zh-->
**构造** (`make`{.Agda}) 正文。
<!--ja-->
**構成** (`make`{.Agda}) 本文。
<!--/-->
```agda
make = value
```

∎

<!--en-->
**Lemma** (`law`{.Agda}) Text.
<!--zh-->
**引理** (`law`{.Agda}) 正文。
<!--ja-->
**補題** (`law`{.Agda}) 本文。
<!--/-->
```agda
law = proof
```

∎
"""
        self.assertEqual(lint_prose.qed_violations(text), [])

    def test_only_outer_theorem_needs_qed_when_helpers_are_nested(self):
        text = """## Result
**Theorem** (`result`{.Agda}) Text.
```agda
result = helper
```
<details>
**Construction** (`value`{.Agda}) Text.
```agda
value = item
```
**Lemma** (`helper`{.Agda}) Text.
```agda
helper = proof
```
</details>

∎
"""
        self.assertEqual(lint_prose.qed_violations(text), [])

    def test_missing_outer_qed_is_rejected_despite_nested_statements(self):
        text = """## Result
**Theorem** (`result`{.Agda}) Text.
```agda
result = helper
```
<details>
**Lemma** (`helper`{.Agda}) Text.
```agda
helper = proof
```
</details>
"""
        violations = lint_prose.qed_violations(text)
        self.assertEqual(len(violations), 1)

    def test_missing_qed_is_rejected(self):
        text = """**Lemma** (`law`{.Agda}) Text.
```agda
law = proof
```
</details>
"""
        violations = lint_prose.qed_violations(text)
        self.assertEqual(len(violations), 1)

    def test_fact_requires_qed(self):
        text = """**Fact** (`property`{.Agda}) Text.
```agda
property = proof
```
"""
        violations = lint_prose.qed_violations(text)
        self.assertEqual(len(violations), 1)

    def test_corollary_requires_qed(self):
        text = """**Corollary** (`consequence`{.Agda}) Text.
```agda
consequence = proof
```
"""
        violations = lint_prose.qed_violations(text)
        self.assertEqual(len(violations), 1)

    def test_explanation_may_follow_completed_proof(self):
        text = """**Lemma** (`helper`{.Agda}) Text.
```agda
helper = proof
```
∎

The result has this broader interpretation.

**Theorem** (`result`{.Agda}) Text.
```agda
result = helper
```
∎
"""
        self.assertEqual(lint_prose.qed_violations(text), [])


class OptionalSummaryTests(unittest.TestCase):
    def test_mathematical_optional_blocks_must_be_collapsible_and_default_open(self):
        self.assertEqual(self.violations('<details open class="optional-reading">'), [])
        self.assertEqual(self.violations('<details class="optional-reading" open>'), [])
        self.assertEqual(len(self.violations('<details class="optional-reading">')), 1)
        self.assertEqual(len(self.violations('<aside class="optional-reading">')), 1)
        self.assertEqual(len(self.violations('<details class="optional-reading" title="open">')), 1)
        self.assertEqual(self.violations('<details class="prose-disclosure">'), [])

    def test_optional_summaries_with_attributes_use_localized_markers(self):
        for lang, prefix in [('en', 'Optional:'), ('zh', '选读：'), ('ja', '発展：')]:
            title = '<summary class="optional-reading-title" id="test-title">'
            self.assertEqual(self.violations(f'<!--{lang}-->\n{title}{prefix} Details</summary>\n<!--/-->'), [])
            self.assertEqual(len(self.violations(f'<!--{lang}-->\n{title}Details</summary>\n<!--/-->')), 1)
            self.assertEqual(len(self.violations(f'{title}{prefix} Details</summary>')), 1)

    def violations(self, text):
        return lint_prose.optional_summary_violations(text)

    def test_localized_optional_markers_are_accepted(self):
        text = """<!--en-->
<details><summary>Optional: details</summary></details>
<!--zh-->
<details><summary>选读：说明</summary></details>
<!--ja-->
<details><summary>発展：説明</summary></details>
<!--/-->
"""
        self.assertEqual(self.violations(text), [])

    def test_missing_or_wrong_language_marker_is_rejected(self):
        text = """<!--en-->
<summary>Details</summary>
<!--zh-->
<summary>Optional: 说明</summary>
<!--/-->
"""
        self.assertEqual(len(self.violations(text)), 2)

    def test_summary_outside_language_group_is_rejected(self):
        self.assertEqual(len(self.violations("<summary>Optional: details</summary>")), 1)


class JapanesePlainStyleTests(unittest.TestCase):
    def violations(self, text):
        return lint_prose.japanese_polite_violations(text)

    def test_polite_forms_in_japanese_prose_are_rejected(self):
        text = """<!--ja-->
これは命題です。写像を返しますが、まだ終わりません。
<!--/-->
"""
        self.assertEqual(len(self.violations(text)), 3)

    def test_plain_style_and_lexical_masumasu_are_accepted(self):
        text = """<!--ja-->
これは命題である。包んですぐ戻る。段階ですでに成立する。これですべてである。これはますます重要である。
<!--/-->
"""
        self.assertEqual(self.violations(text), [])

    def test_polite_forms_before_connectives_are_rejected(self):
        text = """<!--ja-->
これは命題ですが、証明は後である。値を返しますので、場合分けできる。
<!--/-->
"""
        self.assertEqual(len(self.violations(text)), 2)

    def test_other_languages_and_protected_regions_are_ignored(self):
        text = """<!--en-->
です ます
<!--ja-->
`です` [参照](https://example.test/ます) <span title="です">常体である。</span>
```text
これは例です。
```
<!--/-->
"""
        self.assertEqual(self.violations(text), [])


if __name__ == "__main__":
    unittest.main()
