"""The refactoring metric excludes prose and counts every Agda code fence."""

import importlib.util
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


spec = importlib.util.spec_from_file_location(
    "count_agda", Path(__file__).resolve().parents[1] / "gate/count-agda.py")
counter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(counter)


class CountAgdaTests(unittest.TestCase):
    def count(self, text):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Example.lagda.md"
            path.write_text(text, encoding="utf-8")
            return counter.count(path)

    def test_multiple_fences_and_blank_lines(self):
        result = self.count("# Prose\n```agda\nf : A\n \n```\n中文\n"
                            " ```agda\nf = a\n ```\n")
        self.assertEqual(result, {"nonblank_code": 2, "code": 3, "physical": 9})

    def test_prose_and_other_languages_do_not_count(self):
        result = self.count("GCH is proved.\n```python\nprint('text')\n```\n")
        self.assertEqual(result["nonblank_code"], 0)
        self.assertEqual(result["code"], 0)

    def test_header_and_final_line_count(self):
        result = self.count("```agda\n{-# OPTIONS --safe #-}\nmodule A where\n```")
        self.assertEqual(result, {"nonblank_code": 2, "code": 2, "physical": 4})

    def test_empty_source_is_an_error_not_a_zero_line_result(self):
        with tempfile.TemporaryDirectory() as directory:
            result = subprocess.run(
                [sys.executable, counter.__file__, "--src", directory],
                capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertEqual(result.stdout, "")


if __name__ == "__main__":
    unittest.main()
