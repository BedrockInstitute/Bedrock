"""The reading catalog must teach prerequisites before their consumers."""

import importlib.util
from pathlib import Path
import unittest


spec = importlib.util.spec_from_file_location(
    "reading_order", Path(__file__).resolve().parents[1] / "gate/check-reading-order.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


def chapter(*dependencies):
    return "```agda\n" + "\n".join("import " + d for d in dependencies) + "\n```\n"


class ReadingOrderTests(unittest.TestCase):
    def test_preview_is_not_an_instructional_prerequisite(self):
        sources = {"Everything": chapter("Landmarks", "A", "B"),
                   "Landmarks": chapter("B"), "A": chapter(), "B": chapter("A")}
        self.assertEqual(checker.defects(sources), [])
        sources["A"] = chapter("Landmarks")
        self.assertTrue(any("depends on preview" in e for e in checker.defects(sources)))

    def test_backward_dependency_is_rejected(self):
        sources = {"Everything": chapter("B", "A"),
                   "A": chapter(), "B": chapter("A", "Cubical.Data.Nat")}
        self.assertEqual(checker.defects(sources), ["B precedes prerequisite A"])

    def test_catalog_requires_exactly_one_entry_per_master(self):
        sources = {"Everything": chapter("A", "A", "Missing"),
                   "A": chapter(), "B": chapter()}
        self.assertEqual(set(checker.defects(sources)),
                         {"missing chapter: B", "duplicate chapter: A",
                          "unknown catalog chapter: Missing"})

    def test_prose_and_other_fences_are_not_imports(self):
        text = "import Ghost\n```text\nimport Ghost\n```\n" + chapter("A")
        self.assertEqual(checker.imports(text), ["A"])


if __name__ == "__main__":
    unittest.main()
