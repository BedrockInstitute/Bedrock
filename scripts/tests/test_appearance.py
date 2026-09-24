"""Shared palette contracts, legibility, and pre-paint integration."""
import json
from pathlib import Path
import re
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[2]


class AppearanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not shutil.which('node'):
            raise unittest.SkipTest('Node is required to check the browser palette data')
        source = (ROOT / 'site/static/appearance.js').read_text()
        literal = re.search(r'var palettes = (\{[\s\S]*?\n  \});', source)[1]
        cls.palettes = json.loads(subprocess.check_output(
            ['node', '-e', 'console.log(JSON.stringify((' + literal + ')))'], text=True))

    def test_four_complete_dual_mode_palettes(self):
        self.assertEqual(set(self.palettes), {'github', 'solarized', 'catppuccin', 'gruvbox'})
        for modes in self.palettes.values():
            self.assertEqual(set(modes), {'light', 'dark'})
            for values in modes.values():
                self.assertEqual(len(values), 13)
                self.assertTrue(all(re.fullmatch(r'#[0-9a-f]{6}', value) for value in values))

    def test_new_palette_text_contrast(self):
        def luminance(color):
            rgb = [int(color[i:i + 2], 16) / 255 for i in (1, 3, 5)]
            rgb = [x / 12.92 if x <= .04045 else ((x + .055) / 1.055) ** 2.4 for x in rgb]
            return sum(x * weight for x, weight in zip(rgb, (.2126, .7152, .0722)))

        for name, modes in self.palettes.items():
            for mode, values in modes.items():
                backgrounds = [values[0], '#fcfcfd' if mode == 'light' else '#191d25']
                for index, color in enumerate(values):
                    if index in (0, 2):  # background and decorative border, not text
                        continue
                    for background in backgrounds:
                        a, b = sorted((luminance(color), luminance(background)))
                        with self.subTest(theme=name, mode=mode, token=index, background=background):
                            self.assertGreaterEqual((b + .05) / (a + .05), 4.5)

    def test_symbols_and_word_keywords_remain_distinct(self):
        for modes in self.palettes.values():
            for values in modes.values():
                self.assertNotEqual(values[4], values[5])
                self.assertNotIn(values[5], (values[1], values[11], values[12]))

    def test_prepaint_script_and_cache_busting(self):
        template = (ROOT / 'site/template.html').read_text()
        self.assertRegex(template, r'<script src="[^"\n]+/appearance.js\?v=%%APPEARANCEJSVER%%"></script>')
        self.assertLess(template.index('/appearance.js'), template.index('<body'))
        renderer = (ROOT / 'scripts/site/render-site.py').read_text()
        for extension in ('js', 'css'):
            self.assertIn('_ver("appearance.' + extension + '")', renderer)


if __name__ == '__main__':
    unittest.main()
