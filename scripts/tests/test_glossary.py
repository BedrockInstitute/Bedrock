#!/usr/bin/env python3
"""Golden tests for the glossary checker (scripts/check-glossary.py).

Run: python3 scripts/tests/test_glossary.py   (or: make test)
"""

import importlib.util
import os
import sys
import tempfile
import unittest

SCRIPTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")


def _load(modname, filename):
    spec = importlib.util.spec_from_file_location(modname, os.path.join(SCRIPTS, filename))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


cg = _load("check_glossary", "check-glossary.py")  # noqa: E402

# Golden glossary rows (term, zh, ja, avoid), exercising tagged and untagged avoids.
ROWS = [
    ("charter", "纲领", "綱領", "zh:宪章; ja:憲章"),
    ("prose", "文稿", "文章", "散文"),
]
CHECKS = cg.build_checks(ROWS)


def write(tmp, rel, content):
    path = os.path.join(tmp, rel)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(content)
    return path


def msgs(violations):
    return [m for _ln, _idx, m in violations]


class GlossaryTableTests(unittest.TestCase):
    def test_build_checks_expands_tagged_and_untagged(self):
        forb = {(f, lang) for f, lang, _t, _c in CHECKS}
        self.assertIn(("宪章", "zh"), forb)
        self.assertIn(("憲章", "ja"), forb)
        self.assertNotIn(("宪章", "ja"), forb)   # zh-tagged is not checked in ja
        self.assertIn(("散文", "zh"), forb)       # untagged applies to both
        self.assertIn(("散文", "ja"), forb)

    def test_load_glossary_strips_backticks_and_reads_presence(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = write(tmp, "GLOSSARY.md",
                      "# t\n\n| Term | zh | ja | Avoid | Presence | Notes |\n"
                      "|---|---|---|---|---|---|\n"
                      "| charter | `纲领` | `綱領` | `zh:宪章` | yes | n |\n"
                      "| prose | `文稿` | `文章` | `散文` |  | n |\n")
            rows = cg.load_glossary(p)
            self.assertEqual(rows[0], ("charter", "纲领", "綱領", "zh:宪章", True))
            self.assertEqual(rows[1], ("prose", "文稿", "文章", "散文", False))

    def test_load_glossary_reads_multiple_category_tables(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = write(tmp, "GLOSSARY.md",
                      "# t\n\n## Set theory\n\n| Term | zh | ja | Avoid | Presence | Notes |\n"
                      "|---|---|---|---|---|---|\n| forcing | `力迫` | `強制` | | yes | n |\n\n"
                      "## Other\n\n| Term | zh | ja | Avoid | Presence | Notes |\n"
                      "|---|---|---|---|---|---|\n| charter | `纲领` | `綱領` | `zh:宪章` | yes | n |\n")
            rows = cg.load_glossary(p)
            terms = [r[0] for r in rows]
            self.assertEqual(terms, ["forcing", "charter"])  # both tables, no header rows leaked

    def test_build_presence_selects_opted_in_rows(self):
        rows = [("charter", "纲领", "綱領", "", True), ("prose", "文稿", "文章", "散文", False)]
        self.assertEqual(cg.build_presence(rows), [("charter", "纲领", "綱領")])


class FileCheckTests(unittest.TestCase):
    def test_zh_doc_flags_avoided_term(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = write(tmp, "docs/zh/CHARTER.md", "# Bedrock 宪章\n")
            v = cg.check_file(p, CHECKS)
            self.assertEqual(len(v), 1)
            self.assertIn("use 纲领 (zh)", msgs(v)[0])

    def test_ja_doc_flags_japanese_term(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = write(tmp, "docs/ja/CHARTER.md", "# Bedrock 憲章\n")
            self.assertIn("use 綱領 (ja)", msgs(cg.check_file(p, CHECKS))[0])

    def test_simplified_term_not_flagged_in_japanese(self):
        # 宪章 is zh-tagged; it must not fire in a ja-scoped file.
        with tempfile.TemporaryDirectory() as tmp:
            p = write(tmp, "docs/ja/X.md", "宪章\n")
            self.assertEqual(cg.check_file(p, CHECKS), [])

    def test_canonical_rendering_is_clean(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = write(tmp, "docs/zh/CHARTER.md", "# Bedrock 纲领\n")
            self.assertEqual(cg.check_file(p, CHECKS), [])

    def test_english_doc_is_not_checked(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = write(tmp, "docs/en/X.md", "宪章\n")  # nonsense, but en scope skips it
            self.assertEqual(cg.check_file(p, CHECKS), [])

    def test_untagged_term_fires_in_both_languages(self):
        with tempfile.TemporaryDirectory() as tmp:
            zh = write(tmp, "docs/zh/X.md", "这是 散文 风格。\n")
            ja = write(tmp, "docs/ja/X.md", "これは 散文 です。\n")
            self.assertIn("use 文稿 (zh)", msgs(cg.check_file(zh, CHECKS))[0])
            self.assertIn("use 文章 (ja)", msgs(cg.check_file(ja, CHECKS))[0])

    def test_protected_region_is_skipped(self):
        with tempfile.TemporaryDirectory() as tmp:
            inline = write(tmp, "docs/zh/X.md", "见 `宪章` 一词。\n")
            fenced = write(tmp, "docs/zh/Y.md", "```\n宪章\n```\n")
            self.assertEqual(cg.check_file(inline, CHECKS), [])
            self.assertEqual(cg.check_file(fenced, CHECKS), [])

    def test_inline_ignore_suppresses_line(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = write(tmp, "docs/zh/X.md", "联合国宪章 <!-- glossary-ignore -->\n")
            self.assertEqual(cg.check_file(p, CHECKS), [])

    def test_scoped_ignore_suppresses_only_named_term(self):
        with tempfile.TemporaryDirectory() as tmp:
            ok = write(tmp, "docs/zh/X.md", "宪章 <!-- glossary-ignore: charter -->\n")
            other = write(tmp, "docs/zh/Y.md", "散文 <!-- glossary-ignore: charter -->\n")
            self.assertEqual(cg.check_file(ok, CHECKS), [])
            self.assertEqual(len(cg.check_file(other, CHECKS)), 1)  # prose still flagged


class MasterScopeTests(unittest.TestCase):
    MASTER = ("# T\n\n<!--zh-->\n这是 宪章 块。\n<!--ja-->\n憲章 ブロック。\n<!--/-->\n\n"
              "<!--en-->\nThe 宪章 here is shared-ish English.\n<!--/-->\n")

    def test_zh_group_flagged_ja_group_flagged_en_group_clean(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = write(tmp, "src/M.lagda.md", self.MASTER)
            v = cg.check_file(p, CHECKS)
            self.assertEqual(len(v), 2)  # the zh 宪章 and the ja 憲章; the en-group 宪章 is ignored
            joined = " ".join(msgs(v))
            self.assertIn("use 纲领 (zh)", joined)
            self.assertIn("use 綱領 (ja)", joined)


PRESENCE = [("charter", "纲领", "綱領")]


class PresenceTests(unittest.TestCase):
    EN = "# Bedrock Charter\n\nThe full treatment is in the Charter.\n"

    def test_warns_when_canonical_rendering_absent(self):
        v = cg.presence_violations("docs/zh/CHARTER.md", "zh", self.EN, "# 文档\n标题。\n", PRESENCE)
        self.assertEqual(len(v), 1)
        self.assertIn("纲领", v[0][1])

    def test_clean_when_canonical_present(self):
        v = cg.presence_violations("docs/zh/CHARTER.md", "zh", self.EN, "# Bedrock 纲领\n", PRESENCE)
        self.assertEqual(v, [])

    def test_no_warning_when_term_absent_in_english(self):
        v = cg.presence_violations("docs/zh/X.md", "zh", "# Intro\nNothing here.\n", "标题。\n", PRESENCE)
        self.assertEqual(v, [])

    def test_english_term_only_in_protected_region_does_not_count(self):
        en = "See `charter` and [x](charter.md)\n"  # inline code + link dest, both protected
        v = cg.presence_violations("docs/zh/X.md", "zh", en, "标题。\n", PRESENCE)
        self.assertEqual(v, [])

    def test_japanese_uses_ja_rendering(self):
        v = cg.presence_violations("docs/ja/CHARTER.md", "ja", self.EN, "# Bedrock タイトル\n", PRESENCE)
        self.assertIn("綱領", v[0][1])

    def test_scoped_ignore_in_target_suppresses(self):
        tgt = "# 文档\n<!-- glossary-ignore: charter -->\n"
        v = cg.presence_violations("docs/zh/X.md", "zh", self.EN, tgt, PRESENCE)
        self.assertEqual(v, [])


if __name__ == "__main__":
    unittest.main(verbosity=2)
