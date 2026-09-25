"""Focused tests for prose conventions enforced by lint-prose.py."""

import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch


SPEC = importlib.util.spec_from_file_location(
    "lint_prose", Path(__file__).resolve().parents[1] / "gate/lint-prose.py")
lint_prose = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(lint_prose)
from outcrop.core import prose_lint as prose_rules
from outcrop.core.math_lint import inline_math


class BedrockProsePolicyTests(unittest.TestCase):
    def test_opening_chapters_math_uses_figure_convention_or_explicit_approval(self):
        root = Path(__file__).resolve().parents[2]
        figure_count = approved_count = 0
        for name in ('Prelude', 'Impredicativity', 'Classical', 'Choice'):
            chapter = f'Base/{name}.lagda.md'
            path = root / 'src' / chapter
            text = path.read_text()
            with self.subTest(chapter=chapter):
                self.assertNotIn(chapter, lint_prose._MATH_TEMPORARY)
                self.assertFalse(any('inline LaTeX' in hit.message for hit in lint_prose.analyze(text, path)[2]))
                for item in inline_math(text):
                    if item.figure_reference:
                        figure_count += 1
                    else:
                        self.assertIn(item.fingerprint, lint_prose._MATH_APPROVALS.get(chapter, ()))
                        approved_count += 1
        self.assertEqual((figure_count, approved_count), (27, 9))

    def test_inline_math_deferrals_end_on_human_review_not_content_edits(self):
        root = Path(__file__).resolve().parents[2]
        strict = {'Base/Prelude.lagda.md', 'Base/Impredicativity.lagda.md',
                  'Base/Classical.lagda.md', 'Base/Choice.lagda.md'}
        self.assertFalse(strict.intersection(lint_prose._MATH_TEMPORARY))
        for chapter in lint_prose._MATH_TEMPORARY:
            with self.subTest(chapter=chapter):
                path = root / 'src' / chapter
                text = path.read_text()
                self.assertFalse(any('inline LaTeX' in hit.message for hit in lint_prose.analyze(text, path)[2]))
                self.assertFalse(any('inline LaTeX' in hit.message for hit in lint_prose.analyze(text + '\n', path)[2]))
                with patch.dict(lint_prose._MATH_TEMPORARY, {chapter: False}):
                    self.assertTrue(any('allowance expired' in hit.message for hit in lint_prose.analyze(text, path)[2]))
        # Even an unchanged opening chapter cannot inherit a later chapter's deferral.
        text = 'Compare $x$.\n'
        self.assertTrue(any('inline LaTeX' in hit.message for hit in lint_prose.analyze(text, root / 'src/Base/Prelude.lagda.md')[2]))

    def test_legacy_inventory_matches_exact_old_line_only(self):
        chapter = 'V/CantorBernstein.lagda.md'
        original = (Path(__file__).resolve().parents[2] / 'src' / chapter).read_text()
        line = next(line for line in original.splitlines()
                    if 'the statement that x lies in the image of g' in line)
        self.assertEqual(lint_prose.new_bare_variable_violations(line, chapter), [])
        self.assertTrue(lint_prose.new_bare_variable_violations(line + '\n' + line, chapter))
        changed = line.replace('the statement that x', 'the mathematical statement that x')
        self.assertTrue(lint_prose.new_bare_variable_violations(changed, chapter))


    def test_numbered_registry_labels_are_scoped_and_still_require_code_and_qed(self):
        text = '**Theorem 0** Text.\n\n```agda\nopen import Base.Choice public using ( SetChoice→LEM )\n```\n\n∎\n'
        self.assertEqual(lint_prose.theorem_label_violations(text, 'src/Origin.lagda.md'), [])
        self.assertTrue(lint_prose.theorem_label_violations(text, 'src/Base/Choice.lagda.md'))
        self.assertEqual(prose_rules.qed_violations(text), [])
        self.assertTrue(prose_rules.qed_violations(text.replace('∎', '')))
        self.assertTrue(lint_prose.theorem_label_violations(text.replace('Theorem', 'Lemma'), 'src/Origin.lagda.md'))
