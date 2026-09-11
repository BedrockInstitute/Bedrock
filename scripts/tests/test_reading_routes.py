"""Tests for route metadata and dependency-derived readiness."""

import importlib.util
import contextlib
import io
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    "reading_routes", Path(__file__).resolve().parents[1] / "site/reading_routes.py")
routes = importlib.util.module_from_spec(spec); spec.loader.exec_module(routes)
lint_spec = importlib.util.spec_from_file_location(
    "lint_prose", Path(__file__).resolve().parents[1] / "gate/lint-prose.py")
lint_prose = importlib.util.module_from_spec(lint_spec); lint_spec.loader.exec_module(lint_prose)


def metadata(chapters=("A", "B")):
    return {"version": 1, "routes": [{"id": "route",
            "title": {"en": "Route", "zh": "路线", "ja": "ルート"},
            "description": {"en": "Description", "zh": "说明", "ja": "説明"},
            "chapters": list(chapters)}]}


class ValidationTests(unittest.TestCase):
    def test_metadata_routes_ids_and_members_have_stable_types(self):
        bad_values = [
            (None, "metadata must be an object"),
            ({"version": 1, "routes": [{"id": [], "title": {}, "description": {},
                                          "chapters": ["A"]}]}, "string id"),
            ({"version": 1, "routes": [{"id": "Bad_Id", "title": {}, "description": {},
                                          "chapters": ["A"]}]}, "lowercase slug"),
            ({"version": 1, "routes": [{"id": "empty", "title": {}, "description": {},
                                          "chapters": []}]}, "must not be empty"),
            ({"version": 1, "routes": [{"id": "bad-member", "title": {},
                                          "description": {}, "chapters": [[]]}]},
             "non-empty strings"),
        ]
        for value, message in bad_values:
            with self.subTest(message=message), self.assertRaisesRegex(ValueError, message):
                routes.validate_metadata(value, {"Milestones", "A"})

    def test_route_titles_and_descriptions_require_japanese(self):
        for field in ("title", "description"):
            value = metadata()
            del value["routes"][0][field]["ja"]
            with self.assertRaisesRegex(ValueError, field + r"\.ja"):
                routes.validate_metadata(value, {"A", "B"})

    def test_unknown_graph_nodes_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "unknown graph node: Ghost"):
            routes.validate_metadata(metadata(), {"Milestones", "A", "B"},
                                     {"Milestones": [], "A": [], "B": [], "Ghost": []})

    def test_overlap_is_valid_but_repetition_within_one_route_is_not(self):
        value = metadata(); value["routes"].append({"id": "second",
            "title": {"en": "Second", "zh": "第二", "ja": "第二"},
            "description": {"en": "Shared", "zh": "共享", "ja": "共有"}, "chapters": ["B"]})
        routes.validate_metadata(value, {"Milestones", "A", "B"})
        value["routes"][1]["chapters"] = ["B", "B"]
        with self.assertRaisesRegex(ValueError, "repeats chapter: B"):
            routes.validate_metadata(value, {"Milestones", "A", "B"})

    def test_bad_id_language_unknown_and_uncovered_are_rejected(self):
        value = metadata(("A", "Ghost")); value["routes"].append({"id": "route",
            "title": {"en": "Again"}, "description": {"en": "Again", "zh": "再来"},
            "chapters": []})
        with self.assertRaises(ValueError) as caught:
            routes.validate_metadata(value, {"Milestones", "A", "B"})
        for expected in ("duplicate route id", "unknown chapter: Ghost",
                         "not covered by a route: B", "title.en and title.zh"):
            self.assertIn(expected, str(caught.exception))

    def test_cycles_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "prerequisite cycle"):
            routes.validate_metadata(metadata(), {"Milestones", "A", "B"},
                                     {"Milestones": [], "A": ["B"], "B": ["A"]})


class BuildTests(unittest.TestCase):
    def test_navigation_title_removes_prose_markup(self):
        self.assertEqual(routes.plain_title("The order in `L`{.Agda}"), "The order in L")
        self.assertEqual(routes.plain_title("[Codes](Codes.html) and **sets**"), "Codes and sets")

    def test_japanese_catalog_is_not_appended_to_chinese_description(self):
        text = ("<!--en-->\n## Logic\n- `A`{.Agda}: First.\n<!--zh-->\n"
                "## 逻辑\n- `A`{.Agda}：第一。\n<!--ja-->\n"
                "## 論理\n- `A`{.Agda}：最初。\n<!--/-->")
        catalog = routes._catalog(text)
        self.assertEqual(catalog["A"]["title"],
                         {"en": "First.", "zh": "第一。", "ja": "最初。"})
        self.assertEqual(catalog["A"]["stage"]["ja"], "論理")

    def test_strip_metadata_preserves_offsets_and_newlines(self):
        text = 'before\n<!-- bedrock-routes {"title":"中文"} -->\nafter'
        stripped = routes.strip_metadata(text)
        self.assertEqual(len(stripped), len(text))
        self.assertEqual(stripped.count("\n"), text.count("\n"))
        self.assertNotIn("中文", stripped)
        lint_stripped = lint_prose.strip_route_metadata(text)
        self.assertEqual(len(lint_stripped), len(text))
        self.assertEqual(lint_stripped.count("\n"), text.count("\n"))
        self.assertEqual(lint_prose.analyze(text)[1:], ([], []))
        visible_error = text + "\n中文,错误"
        self.assertTrue(lint_prose.analyze(visible_error)[1])

    def test_cli_reports_validation_errors(self):
        with tempfile.TemporaryDirectory() as directory:
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                result = routes.main(["--src", directory, "--check"])
        self.assertEqual(result, 1)
        self.assertIn("reading catalog must cover every chapter exactly once", output.getvalue())

    def test_catalog_text_order_and_fenced_direct_imports_are_authoritative(self):
        catalog = {"version": 1, "routes": metadata()["routes"], "chapters": [
            {"id": "Milestones", "title": {"en": "Endpoint", "zh": "终点", "ja": "終点"},
             "stage": {"en": "Preview", "zh": "预览", "ja": "プレビュー"},
             "description": {"en": "Endpoint.", "zh": "终点。", "ja": "終点。"}},
            {"id": "A", "title": {"en": "First", "zh": "第一", "ja": "最初"},
             "stage": {"en": "Lessons", "zh": "课程", "ja": "授業"},
             "description": {"en": "First.", "zh": "第一。", "ja": "最初。"}},
            {"id": "B", "title": {"en": "Second", "zh": "第二", "ja": "次"},
             "stage": {"en": "Lessons", "zh": "课程", "ja": "授業"},
             "description": {"en": "Second.", "zh": "第二。", "ja": "次。"}},
        ]}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "reading-catalog.json").write_text(routes.json.dumps(catalog), encoding="utf-8")
            (root / "Milestones.lagda.md").write_text("```agda\nimport B\n```")
            (root / "A.lagda.md").write_text(
                "<!--en-->\n# First chapter\n<!--zh-->\n# 第一章\n<!--ja-->\n# 最初の章\n<!--/-->\n"
                "import Ghost\n```agda\nmodule A where\n```")
            (root / "B.lagda.md").write_text("```agda\nopen import A using ()\n```")
            data = routes.build_reading_data(root, root / "reading-catalog.json")
        nodes = {node["id"]: node for node in data["nodes"]}
        self.assertEqual(nodes["A"]["title"]["en"], "First chapter")
        self.assertEqual(nodes["A"]["title"]["ja"], "最初の章")
        self.assertEqual(nodes["A"]["description"]["en"], "First.")
        self.assertEqual(nodes["B"]["stage"]["zh"], "课程")
        self.assertEqual(nodes["B"]["prerequisites"], ["A"])
        self.assertEqual(nodes["B"]["order"], 3)
        self.assertEqual(nodes["Milestones"]["prerequisites"], [])
        self.assertEqual(nodes["Milestones"]["routes"], [])
        self.assertTrue(nodes["Milestones"]["preview"])


if __name__ == "__main__":
    unittest.main()
