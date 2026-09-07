"""Protect partial translation: outlines complete, later prose may stay English."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('chapter_framework',
    Path(__file__).resolve().parents[1] / 'gate/check-chapter-framework.py')
framework = importlib.util.module_from_spec(spec)
spec.loader.exec_module(framework)


def group(en, zh, ja):
    return f'<!--en-->\n{en}\n<!--zh-->\n{zh}\n<!--ja-->\n{ja}\n<!--/-->\n'


class FrameworkTests(unittest.TestCase):
    def test_partial_translation_with_separate_opening_group(self):
        text = group('# Title', '# 标题', '# 題名')
        text += group('A first paragraph.', '第一段。', '最初の段落。')
        text += '\nLater English scaffold.\n```agda\nf = 0\n```\n'
        self.assertEqual(framework.outline_errors(text), ([], 1))

    def test_english_fallback_cannot_hide_missing_japanese_heading(self):
        text = '<!--en-->\n# Title\n\nOpening.\n<!--zh-->\n# 标题\n\n开篇。\n<!--/-->'
        self.assertTrue(framework.outline_errors(text)[0])

    def test_heading_followed_by_code_or_next_heading_is_not_an_opening(self):
        for rest in ('```agda\nf = 0\n```', '## Next\n\nOpening.'):
            text = group('# Title', '# 标题', '# 題名') + rest
            self.assertTrue(framework.outline_errors(text)[0])

    def test_subsection_levels_must_match(self):
        text = group('## A\n\nFirst.', '### 甲\n\n第一。', '## 甲\n\n最初。')
        self.assertTrue(framework.outline_errors(text)[0])

    def test_shared_code_and_route_metadata_are_not_headings(self):
        text = '<!-- bedrock-routes {"title":"# metadata"} -->\n```agda\n# symbol\n```'
        self.assertEqual(framework.outline_errors(text), ([], 0))
