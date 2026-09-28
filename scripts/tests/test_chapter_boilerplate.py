"""Bedrock content complies with the shared chapter setup contract."""
from pathlib import Path
import unittest
from outcrop.core.chapter_structure import opening_errors


class BedrockChapterTests(unittest.TestCase):
    def test_all_real_chapters_conform(self):
        root = Path(__file__).resolve().parents[2] / 'src'
        paths = list(root.rglob('*.lagda.md'))
        modules = {str(p.relative_to(root))[:-9].replace('/', '.') for p in paths}
        for path in paths:
            with self.subTest(path=path):
                self.assertEqual(opening_errors(path.read_text(), str(path.relative_to(root))[:-9].replace('/', '.'), modules, visible_import_chapters={'Origin'}), [])
