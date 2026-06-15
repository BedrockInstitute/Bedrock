#!/usr/bin/env python3
"""Golden tests for the i18n marker grammar shared by the weaver, renderer and linter.

Run: python3 scripts/tests/test_i18n.py   (or: make test)
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from i18n_markers import weave, lint_markers, group_languages  # noqa: E402

MASTER = """# Title

Shared intro.

<!--en-->
English body.
<!--zh-->
中文正文。
<!--/-->

```agda
module M where
x = 1
```

<!--en-->
Only English here.
<!--/-->
"""


class WeaveTests(unittest.TestCase):
    def test_en_keeps_english_and_code_and_shared(self):
        out = weave(MASTER, "en")
        self.assertIn("Shared intro.", out)
        self.assertIn("English body.", out)
        self.assertIn("Only English here.", out)
        self.assertNotIn("中文正文。", out)
        self.assertIn("module M where", out)
        self.assertIn("x = 1", out)

    def test_zh_keeps_chinese_and_code(self):
        out = weave(MASTER, "zh")
        self.assertIn("中文正文。", out)
        self.assertNotIn("English body.", out)
        self.assertIn("module M where", out)        # code is language-neutral
        self.assertIn("Shared intro.", out)         # shared prose copied

    def test_zh_falls_back_to_english_when_absent(self):
        # the second group has only <!--en-->; zh must fall back to it
        self.assertIn("Only English here.", weave(MASTER, "zh"))

    def test_code_identical_across_languages(self):
        def code(out):
            return out[out.index("```agda"):out.index("```\n", out.index("```agda") + 3)]
        self.assertEqual(code(weave(MASTER, "en")), code(weave(MASTER, "zh")))

    def test_group_languages(self):
        self.assertEqual(group_languages(MASTER), {"en", "zh"})


class MarkerLintTests(unittest.TestCase):
    def test_good_master_is_clean(self):
        self.assertEqual(lint_markers(MASTER), [])

    def test_unterminated_group(self):
        self.assertTrue(lint_markers("<!--en-->\nhi\n"))

    def test_stray_close(self):
        self.assertTrue(lint_markers("text\n<!--/-->\n"))

    def test_marker_inside_code_fence(self):
        bad = "```agda\n<!--en-->\n```\n"
        self.assertTrue(any("code fence" in m for _, m in lint_markers(bad)))

    def test_unknown_language_code(self):
        bad = "<!--fr-->\nbonjour\n<!--/-->\n"
        self.assertTrue(any("known language" in m for _, m in lint_markers(bad)))


if __name__ == "__main__":
    unittest.main(verbosity=2)
