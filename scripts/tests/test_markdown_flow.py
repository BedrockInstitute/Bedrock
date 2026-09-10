"""Soft source wraps must not turn inline math or references into blocks."""

import importlib.util
from pathlib import Path
import unittest


spec = importlib.util.spec_from_file_location(
    "bedrock_renderer", Path(__file__).resolve().parents[1] / "site/render-site.py"
)
renderer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(renderer)


class MarkdownFlowTests(unittest.TestCase):
    def test_soft_wraps_around_inline_content_stay_in_one_paragraph(self):
        for kind in ("REF", "IMATH"):
            token = f"\x00{kind}0\x00"
            for before, after in (("We use", "here."), ("这里使用", "说明结论。"),
                                  ("ここでは", "を使います。")):
                with self.subTest(kind=kind, language=before):
                    actual, _ = renderer.md_to_html(f"{before}\n{token}\n{after}")
                    self.assertEqual(actual, f"<p>{before} {token} {after}</p>")

    def test_paragraph_starting_with_inline_content_remains_a_paragraph(self):
        actual, _ = renderer.md_to_html("\x00REF0\x00\nprovides the proof.")
        self.assertEqual(actual, "<p>\x00REF0\x00 provides the proof.</p>")

    def test_inline_content_does_not_split_list_continuation(self):
        actual, _ = renderer.md_to_html("- We use\n  \x00REF0\x00 here.")
        self.assertEqual(actual, "<ul><li>We use \x00REF0\x00 here.</li></ul>")

    def test_inline_content_does_not_split_blockquote_paragraph(self):
        actual, _ = renderer.md_to_html("> We use\n> \x00IMATH0\x00 here.")
        self.assertEqual(actual, "<blockquote><p>We use \x00IMATH0\x00 here.</p></blockquote>")

    def test_code_and_display_math_still_interrupt_paragraphs(self):
        for kind in ("CODE", "DMATH"):
            token = f"\x00{kind}0\x00"
            with self.subTest(kind=kind):
                actual, _ = renderer.md_to_html(f"Before.\n{token}\nAfter.")
                self.assertEqual(actual, f"<p>Before.</p>\n{token}\n<p>After.</p>")

    def test_blank_line_still_separates_paragraphs(self):
        actual, _ = renderer.md_to_html("Before.\n\n\x00REF0\x00 after.")
        self.assertEqual(actual, "<p>Before.</p>\n<p>\x00REF0\x00 after.</p>")


if __name__ == "__main__":
    unittest.main()
