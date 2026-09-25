#!/usr/bin/env python3
"""Golden tests for the glossary checker (scripts/gate/check-glossary.py).

Run: python3 scripts/tests/test_glossary.py   (or: make test)
"""

import importlib.util
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

SCRIPTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")


def _load(modname, filename):
    spec = importlib.util.spec_from_file_location(modname, os.path.join(SCRIPTS, filename))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


cg = _load("check_glossary", "gate/check-glossary.py")  # noqa: E402

from outcrop.core import glossary_lint as glossary_rules
# Golden glossary rows (term, zh, ja, avoid-list, presence), exercising tagged and untagged avoids.
ROWS = [
    ("charter", "纲领", "綱領", ["zh:宪章", "ja:憲章"], True),
    ("prose", "文稿", "文章", ["散文"], False),
]
CHECKS = glossary_rules.build_checks(ROWS)


def write(tmp, rel, content):
    path = os.path.join(tmp, rel)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(content)
    return path


def msgs(violations):
    return [m for _ln, _idx, m in violations]


class FileCheckTests(unittest.TestCase):
    def test_extras_only_preserves_route_metadata_and_doc_presence(self):
        master = str(Path(__file__).resolve().parents[2] / 'src/Base/Prelude.lagda.md')
        with patch.object(cg, 'target_files', return_value=[master]), \
                patch.object(cg, 'check_file') as text, \
                patch.object(cg, 'master_presence_violations') as master_presence, \
                patch.object(cg, 'route_metadata_violations', return_value=['bad route translation']) as metadata, \
                patch.object(cg, 'build_presence', return_value=['required']), \
                patch.object(cg, 'discover_presence_targets', return_value=[(master, 'zh', master)]), \
                patch.object(cg, 'presence_violations', return_value=[]) as docs:
            self.assertEqual(cg.main(['--extras-only']), 1)
            text.assert_not_called(); master_presence.assert_not_called()
            metadata.assert_called_once(); docs.assert_called_once()

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
