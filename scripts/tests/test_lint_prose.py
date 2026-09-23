"""Focused tests for prose conventions enforced by lint-prose.py."""

import importlib.util
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "lint_prose", Path(__file__).resolve().parents[1] / "gate/lint-prose.py")
lint_prose = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(lint_prose)


class InlineAgdaTests(unittest.TestCase):
    def test_standalone_link_and_complete_expression(self):
        text = ('[refl](Cubical.Foundations.Prelude.html#123){.Agda} '
                'and `f x ≡ g x`{.Agda}\n')
        self.assertEqual(lint_prose.inline_agda_violations(text), [])

    def test_split_expressions_and_unboxed_table_notation(self):
        text = ('[refl x](Cubical.Foundations.Prelude.html#123){.Agda}\n'
                '`f x`{.Agda} ≡ `g x`{.Agda}\n'
                '| ∥ B x ∥₁ | explanation |\n')
        self.assertGreaterEqual(len(lint_prose.inline_agda_violations(text)), 3)

    def test_milestones_has_no_exemption(self):
        text = '[LEM x](Base.Classical.html#123){.Agda}\n'
        self.assertTrue(lint_prose.analyze(text, 'src/Milestones.lagda.md')[2])

    def test_plain_variables_are_caught_in_refined_chapters(self):
        text = ('If f x ≡ g x, then f ≡ g.\n'
                '对 A 中的元素。\n'
                'A type is given.\n'
                'For `x`{.Agda}, [V](V.Hierarchy.html#𝒮ᵥ){.Agda} is named.\n'
                '```agda\nf x = x\n```\n')
        hits = lint_prose.bare_variable_violations(text)
        self.assertEqual({text[hit.index] for hit in hits}, {'f', 'x', 'g', 'A'})

    def test_later_chapter_new_prose_is_checked_too(self):
        text = '对 x 中的元素。\n'
        hits = lint_prose.analyze(text, 'src/L/Ordinal/SquareLaw.lagda.md')[2]
        self.assertTrue(any('bare Agda variable' in hit.message for hit in hits))

    def test_legacy_inventory_matches_exact_old_line_only(self):
        chapter = 'V/CantorBernstein.lagda.md'
        original = (Path(__file__).resolve().parents[2] / 'src' / chapter).read_text()
        line = next(line for line in original.splitlines()
                    if 'the statement that x lies in the image of g' in line)
        self.assertEqual(lint_prose.new_bare_variable_violations(line, chapter), [])
        self.assertTrue(lint_prose.new_bare_variable_violations(line + '\n' + line, chapter))
        changed = line.replace('the statement that x', 'the mathematical statement that x')
        self.assertTrue(lint_prose.new_bare_variable_violations(changed, chapter))


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
    def test_submodule_fold_scopes_helpers_and_requires_outer_qed(self):
        text = '''**Theorem** (`result`{.Agda}) Text.
```agda
result = helper
```
<details open class="submodule-fold"><summary class="submodule-fold-heading">Helper</summary>
<div class="submodule-fold-content">
**Lemma** (`helper`{.Agda}) Text.
```agda
helper = proof
```
</div>
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


class DisclosureSummaryTests(unittest.TestCase):
    def test_prose_disclosure_summaries_with_attributes_use_localized_markers(self):
        for lang, prefix in [('en', 'Optional:'), ('zh', '选读：'), ('ja', '発展：')]:
            title = '<summary class="prose-disclosure-title" id="test-title">'
            self.assertEqual(self.violations(f'<!--{lang}-->\n{title}{prefix} Details</summary>\n<!--/-->'), [])
            self.assertEqual(len(self.violations(f'<!--{lang}-->\n{title}Details</summary>\n<!--/-->')), 1)
            self.assertEqual(len(self.violations(f'{title}{prefix} Details</summary>')), 1)

    def violations(self, text):
        return lint_prose.disclosure_summary_violations(text)

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


class SubmoduleFoldTests(unittest.TestCase):
    VALID = '''<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Helper where
```
</summary>
<div class="submodule-fold-content">
<!--en-->
The helper supplies a value.
<!--zh-->
辅助模块给出一个值。
<!--ja-->
補助モジュールが値を与える。
<!--/-->
```agda
  value = result
```
</div>
</details>
```agda
result = Helper.value
```
'''

    def test_valid_fold_and_scope(self):
        self.assertEqual(lint_prose.submodule_fold_violations(self.VALID), [])

    def test_multiline_declaration_is_allowed_but_body_code_is_not(self):
        text = self.VALID.replace('module Helper where\n', 'module Helper\n  where\n')
        self.assertEqual(lint_prose.submodule_fold_violations(text), [])
        text = self.VALID.replace('module Helper where\n', 'module Helper where\n  value = result\n')
        self.assertTrue(lint_prose.submodule_fold_violations(text))
        text = self.VALID.replace('module Helper where\n',
                                  'module Helper where\n  module Extra where\n')
        self.assertTrue(lint_prose.submodule_fold_violations(text, check_all=True))

    def test_default_open_and_complete_body_are_required(self):
        self.assertTrue(lint_prose.submodule_fold_violations(
            self.VALID.replace('<details open class=', '<details class=')))
        self.assertTrue(lint_prose.submodule_fold_violations(
            self.VALID.replace('</div>\n</details>', 'More prose.\n</div>\n</details>')))
        self.assertTrue(lint_prose.submodule_fold_violations(
            self.VALID.replace('result = Helper.value', '  more = value')))

    def test_old_optional_style_is_rejected(self):
        self.assertTrue(lint_prose.submodule_fold_violations(
            '<details open class="optional-reading">'))

    def test_fold_after_code_needs_a_blank_line_for_markdown(self):
        text = '```agda\nprior = value\n```\n' + self.VALID
        self.assertTrue(any('blank line' in hit.message
                            for hit in lint_prose.submodule_fold_violations(text)))

    def test_one_nested_submodule_with_figure_div_is_valid(self):
        nested = '''<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Outer where
```
</summary>
<div class="submodule-fold-content">
```agda
  outer = value
```
<figure><div class="diagram-framed"><div>picture</div></div></figure>
<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module Inner where
```
</summary>
<div class="submodule-fold-content">
```agda
    inner = outer
```
</div>
</details>
```agda
  after = Inner.inner
```
</div>
</details>
```agda
result = Outer.after
```
'''
        self.assertEqual(lint_prose.submodule_fold_violations(nested), [])

    def test_third_submodule_fold_level_is_rejected(self):
        third = '''<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
    module Deep where
```
</summary>
<div class="submodule-fold-content">
```agda
      value = result
```
</div>
</details>
'''
        nested = self.VALID.replace('```agda\n  value = result\n```',
            '''<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module Inner where
```
</summary>
<div class="submodule-fold-content">
''' + third + '''
</div>
</details>''')
        hits = lint_prose.submodule_fold_violations(nested)
        self.assertTrue(any('maximum depth 2' in hit.message for hit in hits))


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
