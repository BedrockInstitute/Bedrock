"""Focused tests for prose conventions enforced by lint-prose.py."""

import importlib.util
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "lint_prose", Path(__file__).resolve().parents[1] / "gate/lint-prose.py")
lint_prose = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(lint_prose)
from outcrop.core import prose_lint as prose_rules
class InlineAgdaTests(unittest.TestCase):
    def test_standalone_link_and_complete_expression(self):
        text = ('[refl](Cubical.Foundations.Prelude.html#123){.Agda} '
                'and `f x ≡ g x`{.Agda}\n')
        self.assertEqual(prose_rules.inline_agda_violations(text), [])

    def test_split_expressions_and_unboxed_table_notation(self):
        text = ('[refl x](Cubical.Foundations.Prelude.html#123){.Agda}\n'
                '`f x`{.Agda} ≡ `g x`{.Agda}\n'
                '| ∥ B x ∥₁ | explanation |\n')
        self.assertGreaterEqual(len(prose_rules.inline_agda_violations(text)), 3)

    def test_milestones_has_no_exemption(self):
        text = '[LEM x](Base.Classical.html#123){.Agda}\n'
        self.assertTrue(lint_prose.analyze(text, 'src/Origin.lagda.md')[2])

    def test_plain_variables_are_caught_in_refined_chapters(self):
        text = ('If f x ≡ g x, then f ≡ g.\n'
                '对 A 中的元素。\n'
                'A type is given.\n'
                'For `x`{.Agda}, [V](V.Hierarchy.html#𝒮ᵥ){.Agda} is named.\n'
                '```agda\nf x = x\n```\n')
        hits = prose_rules.bare_variable_violations(text)
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

    def test_numbered_statement_cannot_bypass_the_rule(self):
        self.assertTrue(self.violations("**Theorem 1.** Text."))
        self.assertTrue(prose_rules.qed_violations("**Theorem 1.** Text."))

    def test_numbered_registry_labels_are_scoped_and_still_require_code_and_qed(self):
        text = '**Theorem 0** Text.\n\n```agda\nopen import Base.Choice public using ( SetChoice→LEM )\n```\n\n∎\n'
        self.assertEqual(lint_prose.theorem_label_violations(text, 'src/Origin.lagda.md'), [])
        self.assertTrue(lint_prose.theorem_label_violations(text, 'src/Base/Choice.lagda.md'))
        self.assertEqual(prose_rules.qed_violations(text), [])
        self.assertTrue(prose_rules.qed_violations(text.replace('∎', '')))
        self.assertTrue(lint_prose.theorem_label_violations(text.replace('Theorem', 'Lemma'), 'src/Origin.lagda.md'))

    def test_labels_inside_agda_fences_are_ignored(self):
        self.assertEqual(self.violations("```agda\n**Lemma.**\n```"), [])


class QedTests(unittest.TestCase):
    def test_each_fold_statement_closes_before_leaving_its_scope(self):
        text = '''**Theorem** (`result`{.Agda}) Text.
```agda
result = helper
```
∎
<details open class="submodule-fold"><summary class="submodule-fold-heading">Helper</summary>
<div class="submodule-fold-content">
**Lemma** (`helper`{.Agda}) Text.
```agda
helper = proof
```
∎
</div>
</details>
'''
        self.assertEqual(prose_rules.qed_violations(text), [])
        self.assertTrue(prose_rules.qed_violations(text.replace('∎\n</div>', '</div>') + '∎\n'))

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
        self.assertEqual(len(prose_rules.qed_violations(text)), 1)

    def test_top_level_construction_and_lemma_end_after_final_code_block(self):
        text = """<!--en-->
**Construction** (`make`{.Agda}) Text.
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
        self.assertEqual(prose_rules.qed_violations(text), [])

    def test_outer_qed_cannot_replace_nested_statement_endings(self):
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
        self.assertTrue(prose_rules.qed_violations(text))

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
        violations = prose_rules.qed_violations(text)
        self.assertEqual(len(violations), 2)

    def test_missing_qed_is_rejected(self):
        text = """**Lemma** (`law`{.Agda}) Text.
```agda
law = proof
```
</details>
"""
        violations = prose_rules.qed_violations(text)
        self.assertEqual(len(violations), 1)

    def test_fact_requires_qed(self):
        text = """**Fact** (`property`{.Agda}) Text.
```agda
property = proof
```
"""
        violations = prose_rules.qed_violations(text)
        self.assertEqual(len(violations), 1)

    def test_corollary_requires_qed(self):
        text = """**Corollary** (`consequence`{.Agda}) Text.
```agda
consequence = proof
```
"""
        violations = prose_rules.qed_violations(text)
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
        self.assertEqual(prose_rules.qed_violations(text), [])

    def test_definitions_and_standalone_proofs_need_code_and_qed(self):
        for label in ('Definition', '定义', '定義', 'Proof', '证明', '証明'):
            prefix = f'**{label}** (`x`{{.Agda}}) Text.\n'
            self.assertTrue(prose_rules.qed_violations(prefix))
            self.assertTrue(prose_rules.qed_violations(prefix + '∎\n'))
            self.assertTrue(prose_rules.qed_violations(prefix + '```agda\n\n```\n∎\n'))
            self.assertEqual(prose_rules.qed_violations(prefix + '```agda\nx = y\n```\n∎\n'), [])

    def test_mark_must_follow_agda_not_prose_or_another_language(self):
        prefix = '**Definition** (`x`{.Agda}) Text.\n```agda\nx = y\n```\n'
        self.assertTrue(prose_rules.qed_violations(prefix + 'More prose.\n∎\n'))
        self.assertTrue(prose_rules.qed_violations(prefix.replace('```agda', '```text') + '∎\n'))
        self.assertTrue(prose_rules.qed_violations(prefix + '∎\n∎\n'))

    def test_parallel_statements_cannot_share_a_mark(self):
        text = '**Construction** (`x`{.Agda}) First.\n\n**Construction** (`y`{.Agda}) Second.\n```agda\nx = y\n```\n∎\n'
        self.assertTrue(prose_rules.qed_violations(text))

    def test_proof_requires_code_after_its_label(self):
        text = '**Lemma** (`x`{.Agda}) Text.\n```agda\nx = y\n```\n**Proof** Words only.\n∎\n'
        self.assertTrue(prose_rules.qed_violations(text))

    def test_all_translated_routes_are_checked(self):
        text = '<!--en-->\n**Definition** (`x`{.Agda}) Text.\n<!--zh-->\n**定义** (`x`{.Agda}) 正文。\n**定义** (`y`{.Agda}) 多余。\n<!--ja-->\n**定義** (`x`{.Agda}) 本文。\n<!--/-->\n```agda\nx = y\n```\n∎\n'
        self.assertTrue(prose_rules.qed_violations(text))

    def test_grouped_construction_has_named_bullets(self):
        prefix = '**Construction** (`x`{.Agda} `y`{.Agda})\n\n'
        bullets = '- `x`{.Agda} First.\n- `y`{.Agda} Second.\n'
        self.assertEqual(lint_prose.theorem_label_violations(prefix + bullets), [])
        self.assertTrue(lint_prose.theorem_label_violations(prefix))
        self.assertTrue(lint_prose.theorem_label_violations((prefix + bullets).replace('Construction', 'Lemma')))
        self.assertTrue(lint_prose.theorem_label_violations(prefix + bullets.replace('- `y`', '- `z`')))



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
        self.assertEqual(prose_rules.submodule_fold_violations(self.VALID), [])

    def test_private_module_modifier_stays_with_its_declaration(self):
        text = ('```agda\nmodule Example where\n```\n\n' + self.VALID
                .replace('module Helper where', 'private module Helper where'))
        self.assertEqual(prose_rules.submodule_fold_violations(text, check_all=True), [])
        self.assertTrue(prose_rules.submodule_fold_violations(
            text.replace('  value = result', 'value = result'), check_all=True))
        self.assertTrue(prose_rules.submodule_fold_violations(
            text.replace('private module', 'private\n  module'), check_all=True))

    def test_multiline_declaration_is_allowed_but_body_code_is_not(self):
        text = self.VALID.replace('module Helper where\n', 'module Helper\n  where\n')
        self.assertEqual(prose_rules.submodule_fold_violations(text), [])
        text = self.VALID.replace('module Helper where\n', 'module Helper where\n  value = result\n')
        self.assertTrue(prose_rules.submodule_fold_violations(text))
        text = self.VALID.replace('module Helper where\n',
                                  'module Helper where\n  module Extra where\n')
        self.assertTrue(prose_rules.submodule_fold_violations(text, check_all=True))

    def test_default_open_and_complete_body_are_required(self):
        self.assertTrue(prose_rules.submodule_fold_violations(
            self.VALID.replace('<details open class=', '<details class=')))
        self.assertTrue(prose_rules.submodule_fold_violations(
            self.VALID.replace('</div>\n</details>', 'More prose.\n</div>\n</details>')))
        self.assertTrue(prose_rules.submodule_fold_violations(
            self.VALID.replace('result = Helper.value', '  more = value')))

    def test_old_optional_style_is_rejected(self):
        self.assertTrue(prose_rules.submodule_fold_violations(
            '<details open class="optional-reading">'))

    def test_fold_after_code_needs_a_blank_line_for_markdown(self):
        text = '```agda\nprior = value\n```\n' + self.VALID
        self.assertTrue(any('blank line' in hit.message
                            for hit in prose_rules.submodule_fold_violations(text)))

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
        self.assertEqual(prose_rules.submodule_fold_violations(nested), [])

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
        hits = prose_rules.submodule_fold_violations(nested)
        self.assertTrue(any('maximum depth 2' in hit.message for hit in hits))


class JapanesePlainStyleTests(unittest.TestCase):
    def violations(self, text):
        return prose_rules.japanese_polite_violations(text)

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
