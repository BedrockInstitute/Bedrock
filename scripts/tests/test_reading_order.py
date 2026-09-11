"""The reading catalog must teach prerequisites before their consumers."""

import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


spec = importlib.util.spec_from_file_location(
    "reading_order", Path(__file__).resolve().parents[1] / "gate/check-reading-order.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


def chapter(*dependencies):
    return "```agda\n" + "\n".join("import " + d for d in dependencies) + "\n```\n"


class ReadingOrderTests(unittest.TestCase):
    def check(self, sources, order):
        chapters = []
        for name in order:
            chapters.append({"id": name,
                             "title": {"en": name, "zh": name, "ja": name},
                             "stage": {"en": "Stage", "zh": "阶段", "ja": "段階"},
                             "description": {"en": name, "zh": name, "ja": name}})
        catalog = {"version": 1, "routes": [{"id": "route",
                    "title": {"en": "Route", "zh": "路线", "ja": "ルート"},
                    "description": {"en": "Route", "zh": "路线", "ja": "ルート"},
                    "chapters": [n for n in order if n != "Milestones"]}],
                   "chapters": chapters}
        with tempfile.NamedTemporaryFile(mode="w", suffix=".json", encoding="utf-8") as fh:
            json.dump(catalog, fh); fh.flush()
            return checker.defects(sources, fh.name)

    def test_preview_is_not_an_instructional_prerequisite(self):
        sources = {"Milestones": chapter("B"), "A": chapter(), "B": chapter("A")}
        self.assertEqual(self.check(sources, ["Milestones", "A", "B"]), [])
        sources["A"] = chapter("Milestones")
        self.assertTrue(any("depends on preview" in e
                            for e in self.check(sources, ["Milestones", "A", "B"])))

    def test_backward_dependency_is_rejected(self):
        sources = {"A": chapter(), "B": chapter("A", "Cubical.Data.Nat")}
        self.assertEqual(self.check(sources, ["B", "A"]), ["B precedes prerequisite A"])

    def test_catalog_requires_exactly_one_entry_per_master(self):
        sources = {"A": chapter(), "B": chapter()}
        self.assertEqual(set(self.check(sources, ["A", "A", "Missing"])),
                         {"missing chapter: B", "duplicate chapter: A",
                          "unknown catalog chapter: Missing"})

    def test_prose_and_other_fences_are_not_imports(self):
        text = "import Ghost\n```text\nimport Ghost\n```\n" + chapter("A")
        self.assertEqual(checker.imports(text), ["A"])


if __name__ == "__main__":
    unittest.main()
