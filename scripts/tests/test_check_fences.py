"""Regression tests for fenced Agda detection around route metadata."""
import importlib.util
from pathlib import Path
import tempfile
import unittest


spec = importlib.util.spec_from_file_location(
    "check_fences", Path(__file__).resolve().parents[1] / "gate/check-fences.py")
check_fences = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check_fences)


class CheckFencesTests(unittest.TestCase):
    def suspects(self, text):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Master.lagda.md"
            path.write_text(text)
            return check_fences.suspects(path, 3)

    def test_valid_route_metadata_is_ignored_and_lines_are_preserved(self):
        text = """<!-- bedrock-routes
{
  "version": 1,
  "routes": []
}
-->

Prose.
"""
        self.assertEqual(self.suspects(text), [])
        stripped = check_fences.strip_metadata(text)
        self.assertEqual(stripped.count("\n"), text.count("\n"))
        self.assertEqual(len(stripped), len(text))

    def test_unfenced_agda_after_metadata_is_reported_at_original_lines(self):
        text = """<!-- bedrock-routes {"version": 1, "routes": []} -->
f : A
f x = x
g : B
"""
        self.assertEqual([line for line, _ in self.suspects(text)], [2, 3, 4])

    def test_other_html_comment_does_not_hide_unfenced_agda(self):
        text = """<!-- ordinary comment -->
f : A
f x = x
g : B
"""
        self.assertEqual([line for line, _ in self.suspects(text)], [2, 3, 4])


if __name__ == "__main__":
    unittest.main()
