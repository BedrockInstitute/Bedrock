"""Focused tests for prose conventions enforced by lint-prose.py."""

import importlib.util
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "lint_prose", Path(__file__).resolve().parents[1] / "gate/lint-prose.py")
lint_prose = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(lint_prose)
from outcrop.core import prose_lint as prose_rules


class BedrockProsePolicyTests(unittest.TestCase):
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
