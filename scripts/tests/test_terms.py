#!/usr/bin/env python3
"""Tests for reader-facing terminology metadata, markers, and rendering."""

import importlib.util
import json
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

    def test_structured_abbreviation_is_an_audited_form_in_each_language(self):
        value = entry(abbreviations={"en": "HIT", "zh": "HIT", "ja": "HIT"})
        self.assertEqual(terms.schema_errors([value]), [])
        for lang in ("en", "zh", "ja"):
            self.assertIn("HIT", terms.localized_forms(value, lang))

    def test_abbreviation_schema_rejects_unknown_language_and_full_name(self):
        self.assertTrue(any("abbreviations must map" in error for error in
                            terms.schema_errors([entry(abbreviations={"fr": "HIT"})])))
        self.assertTrue(any("must differ" in error for error in
                            terms.schema_errors([entry(abbreviations={"en": "host"})])))
        self.assertTrue(any("only in abbreviations" in error for error in
                            terms.schema_errors([entry(abbreviations={"en": "HIT"},
                                                       forms_en=["HIT"])])))

    def test_abbreviation_collision_with_another_full_term_is_rejected(self):
        other = entry(id="other", en="HIT", zh="別", ja="別", introduced_in="Base.Other")
        self.assertTrue(any("ambiguous automatic en form" in error for error in
                            terms.schema_errors([entry(abbreviations={"en": "HIT"}), other])))


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

    def test_abbreviation_links_and_appears_in_glossary_outputs(self):
        value = entry(abbreviations={"en": "HIT", "zh": "HIT"})
        rendered = renderer.auto_link_terms("<p>A HIT is a host.</p>", "en", "M", [value])
        self.assertEqual(rendered.count('class="term-ref"'), 2)
        self.assertIn('data-term="host-environment" href="Base.Prelude.html#term-host-environment">HIT</a>',
                      rendered)
        self.assertIn('class="term-abbreviation">(HIT)</span>',
                      renderer.glossary_label_html(value, "en"))
        with tempfile.TemporaryDirectory() as tmp:
            os.mkdir(os.path.join(tmp, "en"))
            renderer.write_terms(tmp, "en", [value])
            with open(os.path.join(tmp, "en", "terms.json"), encoding="utf-8") as source:
                payload = json.load(source)
            self.assertEqual(payload["host-environment"]["abbreviation"], "HIT")

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
    def test_abbreviation_use_has_the_same_prerequisite_rule_as_full_name(self):
        value = entry(abbreviations={"en": "HIT"})
        self.assertEqual(len(gate.prerequisite_occurrences("A HIT appears.", value, "en", "Other")), 1)

    def test_explicit_sense_does_not_trigger_an_overlapping_concept(self):
        text = '[host]{.term-ref #other-concept}'
        self.assertEqual(gate.prerequisite_occurrences(text, entry(), 'en', 'Other'), [])

    def test_explicit_cross_chapter_lookup_does_not_require_proof_import(self):
        text = '[host]{.term-ref #host-environment}'
        self.assertEqual(gate.prerequisite_occurrences(text, entry(), 'en', 'Other'), [])

    def test_bare_use_still_requires_prerequisite_after_a_lookup(self):
        text = '[host]{.term-ref #host-environment} and host'
        self.assertEqual(len(gate.prerequisite_occurrences(text, entry(), 'en', 'Other')), 1)

    def test_explicit_lookup_can_point_forward_within_same_chapter(self):
        for language, label in (('en', 'host'), ('zh', '宿主'), ('ja', 'ホスト')):
            text = '[' + label + ']{.term-ref #host-environment}'
            self.assertEqual(gate.prerequisite_occurrences(text, entry(), language, 'Base.Prelude'), [])

    def test_forward_lookup_does_not_exempt_bare_same_chapter_uses(self):
        text = '[host]{.term-ref #host-environment} and host'
        self.assertEqual(len(gate.prerequisite_occurrences(text, entry(), 'en', 'Base.Prelude')), 1)

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
