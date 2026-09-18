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
            "**Theorem** (`result`{.Agda}) Text.",
            "**定理** (`result`{.Agda}) 正文。",
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


if __name__ == "__main__":
    unittest.main()
