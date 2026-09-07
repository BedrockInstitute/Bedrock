#!/usr/bin/env python3
"""Tests for folding untranslated prose in localized site pages."""

import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "site"))
from i18n_markers import weave, weave_for_site  # noqa: E402


class ProseFallbackTests(unittest.TestCase):
    def test_missing_japanese_branch_folds_english_fallback(self):
        master = "<!--en-->\nAn untranslated explanation remains available.\n<!--zh-->\n中文。\n<!--/-->\n"
        out = weave_for_site(master, "ja")
        self.assertIn('<details class="localized-fallback" lang="en">', out)
        self.assertIn('<summary lang="ja">英語原文</summary>', out)
        self.assertIn("An untranslated explanation remains available.", out)

    def test_shared_english_is_folded_but_shared_math_is_not(self):
        master = "A shared English scaffold paragraph.\n\n$$x \\in L$$\n"
        out = weave_for_site(master, "zh")
        self.assertIn('<summary lang="zh">英文原文</summary>', out)
        self.assertIn("A shared English scaffold paragraph.", out)
        self.assertNotIn("<details", out[out.index("$$x"):])
        self.assertIn("$$x \\in L$$", out)

    def test_english_table_inside_japanese_branch_is_folded(self):
        master = """<!--en-->
English.
<!--ja-->
日本語の導入段落です。

| Name | Meaning |
| --- | --- |
| code | a formula code |
<!--/-->
"""
        out = weave_for_site(master, "ja")
        self.assertTrue(out.index("日本語の導入段落です。") < out.index("<details"))
        self.assertIn("| Name | Meaning |", out)
        self.assertIn('<summary lang="ja">英語原文</summary>', out)

    def test_english_with_quoted_chinese_term_is_folded(self):
        master = """<!--ja-->
The relation is called “满足关系” when it agrees with the recursive clauses.
<!--/-->
"""
        out = weave_for_site(master, "ja")
        self.assertIn('<summary lang="ja">英語原文</summary>', out)
        self.assertIn("满足关系", out)

    def test_symbol_and_technical_name_lists_stay_expanded(self):
        master = "x y\n\nMostowski collapse\n\n`foo` `bar`\n"
        out = weave_for_site(master, "ja")
        self.assertNotIn("<details", out)

    def test_single_line_display_math_does_not_consume_following_prose(self):
        master = "$$A=B$$\n\nFollowing English explanation.\n"
        out = weave_for_site(master, "ja")
        self.assertLess(out.index("$$A=B$$"), out.index("<details"))
        self.assertNotIn("$$A=B$$", out[out.index("<details"):])
        self.assertIn("Following English explanation.", out)

    def test_shared_code_stays_visible_and_outside_details(self):
        master = """Shared English explanation.

```agda
module M where
x = 1
```

More English explanation.
"""
        out = weave_for_site(master, "ja")
        code = out[out.index("```agda"):out.index("```", out.index("```agda") + 3) + 3]
        self.assertIn("module M where", code)
        self.assertNotIn("<details", code)
        self.assertLess(out.index("</details>"), out.index("```agda"))

    def test_renderer_code_placeholder_stays_outside_details(self):
        token = "\x00CODE0\x00"
        master = f"English before code.\n\n{token}\n\nEnglish after code.\n"
        out = weave_for_site(master, "zh")
        self.assertIn(token, out)
        before, after = out.split(token)
        self.assertEqual(before.count("<details"), before.count("</details>"))
        self.assertEqual(after.count("<details"), after.count("</details>"))

    def test_japanese_opening_remains_expanded(self):
        master = "<!--en-->\nEnglish opening paragraph.\n<!--ja-->\n日本語の導入段落です。\n<!--/-->\n"
        out = weave_for_site(master, "ja")
        self.assertIn("日本語の導入段落です。", out)
        self.assertNotIn("<details", out)

    def test_english_edition_is_complete_and_unchanged(self):
        master = "Shared English.\n\n<!--en-->\nEnglish branch.\n<!--ja-->\n日本語。\n<!--/-->\n"
        self.assertEqual(weave_for_site(master, "en"), weave(master, "en"))


if __name__ == "__main__":
    unittest.main(verbosity=2)
