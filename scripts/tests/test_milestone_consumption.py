"""Tests for the final-tree Milestones consumption gate."""

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "check_milestone_consumption", HERE.parent / "gate" / "check-milestone-consumption.py"
)
CHECK = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = CHECK
SPEC.loader.exec_module(CHECK)


def write(root: Path, name: str, body: str) -> None:
    path = root / (name.replace(".", "/") + ".lagda.md")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("```agda\n" + body + "\n```\n", encoding="utf-8")


class MilestoneConsumptionTests(unittest.TestCase):
    def test_transitive_modules_are_consumed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            write(root, "Milestones", "open import A")
            write(root, "A", "open import B")
            write(root, "B", "b : Set\nb = Set")
            self.assertEqual(CHECK.check(root), [])

    def test_definition_in_unreachable_module_is_reported(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            write(root, "Milestones", "open import A")
            write(root, "A", "a : Set\na = Set")
            write(root, "Orphan", "orphan : Set\norphan = Set")
            problems = CHECK.check(root)
            self.assertEqual(len(problems), 1)
            self.assertIn("orphan", problems[0])

    def test_missing_root_is_reported(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            write(root, "A", "a : Set\na = Set")
            problems = CHECK.check(root)
            self.assertEqual(len(problems), 1)
            self.assertIn("missing milestone root", problems[0])


if __name__ == "__main__":
    unittest.main()
