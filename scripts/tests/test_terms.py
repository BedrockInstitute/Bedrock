#!/usr/bin/env python3
"""Tests for reader-facing terminology metadata, markers, and rendering."""

import importlib.util
import os
import tempfile
import unittest

SCRIPTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")


def load(name, relative):
    spec = importlib.util.spec_from_file_location(name, os.path.join(SCRIPTS, relative))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


terms = load("term_registry", "site/term_registry.py")
renderer = load("render_site_terms", "site/render-site.py")
gate = load("check_term_introductions", "gate/check-term-introductions.py")


def entry(**changes):
    value = {
        "id": "host-environment", "audience": "reader", "category": "Type theory",
        "en": "host", "zh": "宿主", "ja": "ホスト", "introduced_in": "Base.Prelude",
        "matching": "auto", "recap_en": "The ambient environment.",
        "recap_zh": "承载形式化的环境。", "recap_ja": "形式化を支える環境。",
    }
    value.update(changes)
    return value


class SchemaTests(unittest.TestCase):
    def test_reader_entry_is_complete(self):
        self.assertEqual(terms.schema_errors([entry()]), [])

    def test_duplicate_auto_form_is_rejected(self):
        other = entry(id="other", en="ambient", introduced_in="Base.Other")
        self.assertTrue(any("ambiguous automatic zh form" in error
                            for error in terms.schema_errors([entry(), other])))

    def test_reader_entry_must_choose_matching_policy(self):
        value = entry()
        value.pop("matching")
        self.assertTrue(any("requires matching" in error
                            for error in terms.schema_errors([value])))


class RenderingTests(unittest.TestCase):
    def test_auto_links_prose_but_not_code_or_introduction(self):
        body = ('<p>The <dfn id="term-host-environment" data-term="host-environment">host</dfn> '
                'contains another host.</p><pre><code>host</code></pre>')
        rendered = renderer.auto_link_terms(body, "en", "Base.Prelude", [entry()])
        self.assertEqual(rendered.count('class="term-ref"'), 1)
        self.assertIn('<code>host</code>', rendered)
        self.assertIn('<dfn id="term-host-environment"', rendered)

    def test_english_matching_uses_word_boundaries(self):
        rendered = renderer.auto_link_terms("<p>host hosting host-level</p>", "en", "M", [entry()])
        self.assertEqual(rendered.count('class="term-ref"'), 2)

    def test_explicit_term_is_not_automatically_linked(self):
        rendered = renderer.auto_link_terms("<p>host</p>", "en", "M",
                                            [entry(matching="explicit")])
        self.assertEqual(rendered, "<p>host</p>")

    def test_void_element_does_not_protect_following_prose(self):
        rendered = renderer.auto_link_terms("<p><br>host</p>", "en", "M", [entry()])
        self.assertEqual(rendered.count('class="term-ref"'), 1)

    def test_heading_marker_keeps_plain_toc_label(self):
        marked = renderer.TERM_MARK_RE.sub(
            lambda match: "\x00TERM0\x00", "## [host]{.term-intro #host-environment}")
        body, toc = renderer.md_to_html(marked)
        store = {"\x00TERM0\x00": '<dfn id="term-host-environment">host</dfn>'}
        for key, value in store.items():
            body = body.replace(key, value)
        clean = renderer.restore_toc_labels(toc, store)
        self.assertIn('<dfn id="term-host-environment">host</dfn>', body)
        self.assertEqual(clean, [(2, "sec-0", "host")])


class IntroductionGateTests(unittest.TestCase):
    MASTER = """<!--en-->
[host]{.term-intro #host-environment}
<!--zh-->
[宿主]{.term-intro #host-environment}
<!--ja-->
[ホスト]{.term-intro #host-environment}
<!--/-->
"""

    def test_one_trilingual_introduction_passes(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src", "Base")
            os.makedirs(src)
            with open(os.path.join(src, "Prelude.lagda.md"), "w", encoding="utf-8") as target:
                target.write(self.MASTER)
            glossary = os.path.join(tmp, "glossary.toml")
            with open(glossary, "w", encoding="utf-8") as target:
                target.write('[[term]]\nid="host-environment"\naudience="reader"\n'
                             'en="host"\nzh="宿主"\nja="ホスト"\nintroduced_in="Base.Prelude"\n'
                             'matching="auto"\nrecap_en="x"\nrecap_zh="x"\nrecap_ja="x"\n')
            self.assertEqual(gate.check(os.path.join(tmp, "src"), glossary), [])

    def test_missing_language_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            os.makedirs(os.path.join(tmp, "src", "Base"))
            master = self.MASTER.replace("[ホスト]{.term-intro #host-environment}", "ホスト")
            with open(os.path.join(tmp, "src", "Base", "Prelude.lagda.md"), "w", encoding="utf-8") as target:
                target.write(master)
            glossary = os.path.join(tmp, "glossary.toml")
            with open(glossary, "w", encoding="utf-8") as target:
                target.write('[[term]]\nid="host-environment"\naudience="reader"\n'
                             'en="host"\nzh="宿主"\nja="ホスト"\nintroduced_in="Base.Prelude"\n'
                             'recap_en="x"\nrecap_zh="x"\nrecap_ja="x"\n')
            self.assertTrue(any("expected one ja introduction" in error
                                for error in gate.check(os.path.join(tmp, "src"), glossary)))


if __name__ == "__main__":
    unittest.main(verbosity=2)
