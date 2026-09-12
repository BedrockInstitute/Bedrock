"""The addressable, machine-readable layer the site publishes beside its pages.

A passage has to be citable: a reader who selects a sentence and hands it to an
assistant, and the assistant that then follows the link, both need the anchor to name
the same block on the next visit. These tests pin the anchoring rule, the Markdown
twin and the shape of the guide an agent reads first.
"""

import importlib.util
from pathlib import Path
import re
import unittest


spec = importlib.util.spec_from_file_location(
    "bedrock_renderer", Path(__file__).resolve().parents[1] / "site/render-site.py"
)
renderer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(renderer)


class ProseAnchorTests(unittest.TestCase):
    def test_paragraphs_are_numbered_in_document_order(self):
        body, _ = renderer.md_to_html("First one.\n\nSecond one.\n\nThird one.")
        anchored = renderer.anchor_prose_blocks(body)
        self.assertEqual(re.findall(r'id="(p-\d+)"', anchored), ["p-1", "p-2", "p-3"])

    def test_list_items_are_addressable_too(self):
        body, _ = renderer.md_to_html("Lead in.\n\n- one\n- two")
        anchored = renderer.anchor_prose_blocks(body)
        self.assertEqual(re.findall(r'id="(p-\d+)"', anchored), ["p-1", "p-2", "p-3"])

    def test_a_nested_block_is_not_numbered_separately(self):
        """The outermost block is the addressable unit, so a quoted paragraph shares
        its quotation's anchor rather than claiming one of its own."""
        body, _ = renderer.md_to_html("> quoted prose\n\nAfter.")
        anchored = renderer.anchor_prose_blocks(body)
        self.assertEqual(re.findall(r'id="(p-\d+)"', anchored), ["p-1", "p-2"])
        self.assertIn('<blockquote id="p-1">', anchored)
        self.assertIn("<blockquote id=\"p-1\"><p>quoted prose</p></blockquote>", anchored)

    def test_headings_keep_their_own_scheme(self):
        body, _ = renderer.md_to_html("# Title\n\nProse.\n\n## Section\n\nMore.")
        anchored = renderer.anchor_prose_blocks(body)
        self.assertEqual(re.findall(r'id="(sec-\d+)"', anchored), ["sec-0", "sec-1"])
        self.assertEqual(re.findall(r'id="(p-\d+)"', anchored), ["p-1", "p-2"])

    def test_an_agda_block_is_left_to_its_own_token_anchors(self):
        body = '<p>Before.</p>\n<pre class="Agda"><a id="17">x</a></pre>\n<p>After.</p>'
        anchored = renderer.anchor_prose_blocks(body)
        self.assertEqual(re.findall(r'id="(p-\d+)"', anchored), ["p-1", "p-2"])
        self.assertIn('<pre class="Agda"><a id="17">', anchored)

    def test_numbering_does_not_depend_on_the_language(self):
        """The three editions share anchors because they share block structure, which is
        what lets a handover in one language cite a passage another reader can open."""
        shapes = ("One.\n\nTwo.\n\n- a\n- b", "一。\n\n二。\n\n- 甲\n- 乙",
                  "一つ。\n\n二つ。\n\n- あ\n- い")
        counts = set()
        for text in shapes:
            body, _ = renderer.md_to_html(text)
            counts.add(tuple(re.findall(r'id="(p-\d+)"', renderer.anchor_prose_blocks(body))))
        self.assertEqual(len(counts), 1, counts)


class PlainCodeTests(unittest.TestCase):
    def test_highlighting_is_stripped_back_to_the_agda_source(self):
        block = ('<pre class="Agda"><a id="1" class="Keyword">open</a> '
                 '<a id="2" class="Keyword">import</a> '
                 '<a id="3" href="Base.Prelude.html" class="Module">Base.Prelude</a>\n</pre>')
        self.assertEqual(renderer.plain_code(block), "open import Base.Prelude")

    def test_escaped_source_characters_come_back_unescaped(self):
        block = '<pre class="Agda"><a id="4">x</a> &lt;&gt; &amp; y</pre>'
        self.assertEqual(renderer.plain_code(block), "x <> & y")


class MarkdownTwinTests(unittest.TestCase):
    def setUp(self):
        renderer.CHAPTER_TITLES.clear()
        renderer.CHAPTER_TITLES.update({"V.Hierarchy": {"en": "The cumulative hierarchy"}})
        renderer.CHAPTER_META.clear()
        renderer.CHAPTER_META.update({"V.Hierarchy": {
            "description": {"en": "The ambient hierarchy V as a higher inductive type."},
            "stage": {"en": "The ambient hierarchy"}, "order": 21,
            "prerequisites": ["Base.Prelude"], "routes": ["common-foundations"]}})

    def twin(self, woven, blocks):
        return renderer.markdown_mirror(woven, blocks, "V.Hierarchy", "en",
                                        "V.Hierarchy.html", ["en", "zh", "ja"])

    def test_front_matter_states_where_the_chapter_sits(self):
        text = self.twin("# Title\n\nProse.\n", [])
        head = text.split("---")[1]
        self.assertIn("module: V.Hierarchy", head)
        self.assertIn("lang: en", head)
        self.assertIn("reading_order: 21", head)
        self.assertIn('stage: "The ambient hierarchy"', head)
        self.assertIn("prerequisites: [Base.Prelude]", head)
        self.assertIn("canonical: https://bedrock.institute/en/V.Hierarchy.html", head)
        self.assertIn("agda_source: https://github.com/BedrockInstitute/Bedrock"
                      "/blob/main/src/V/Hierarchy.lagda.md", head)

    def test_translations_name_the_other_editions_and_not_this_one(self):
        head = self.twin("# Title\n", []).split("---")[1]
        line = next(l for l in head.splitlines() if l.startswith("translations:"))
        self.assertIn("https://bedrock.institute/zh/V.Hierarchy.md", line)
        self.assertIn("https://bedrock.institute/ja/V.Hierarchy.md", line)
        self.assertNotIn("/en/", line)

    def test_a_displayed_block_becomes_a_fence_that_stands_alone(self):
        block = '<pre class="Agda"><a id="1" class="Keyword">module</a> M\n</pre>'
        text = self.twin("Lead in.\n\x00CODE0\x00\nAfter.\n", [block])
        self.assertIn("Lead in.\n\n```agda\nmodule M\n```\n\nAfter.", text)
        # a closing fence is always followed by a blank line, so the prose after a
        # displayed block cannot be swallowed into it
        self.assertEqual(re.findall(r"^```\n(?=\S)", text, re.M), [])

    def test_reader_markup_is_reduced_to_what_it_says(self):
        text = self.twin("A [transitive set]{.term-intro #transitive-set} and "
                         "`V`{.Agda} appear here.\n", [])
        self.assertIn("A transitive set and `V` appear here.", text)


class AgentGuideTests(unittest.TestCase):
    def setUp(self):
        renderer.CHAPTER_TITLES.clear()
        renderer.CHAPTER_TITLES.update({"Milestones": {"en": "Milestones"},
                                        "Base.Prelude": {"en": "Prelude"}})
        renderer.CHAPTER_META.clear()
        renderer.CHAPTER_META.update({
            "Milestones": {"description": {"en": "The proved endpoints."},
                           "stage": {"en": "Preview"}, "order": 1,
                           "prerequisites": [], "routes": []},
            "Base.Prelude": {"description": {"en": "Prelude"}, "stage": {"en": "Foundations"},
                             "order": 2, "prerequisites": [], "routes": []}})

    def test_the_guide_names_every_chapter_and_its_markdown_twin(self):
        guide = renderer.agent_guide(["en", "zh", "ja"], ["Milestones", "Base.Prelude"])
        self.assertIn("(https://bedrock.institute/en/Milestones.md)", guide)
        self.assertIn("(https://bedrock.institute/en/Base.Prelude.md)", guide)
        self.assertIn("/en/reading-routes.json", guide)
        self.assertIn("/en/search.json", guide)
        self.assertIn("/en/terms.json", guide)

    def test_a_description_that_only_restates_the_title_is_dropped(self):
        """Repeating the chapter title as its description costs an agent tokens and
        tells it nothing, so the index omits it rather than saying it twice."""
        guide = renderer.agent_guide(["en"], ["Milestones", "Base.Prelude"])
        self.assertIn("2. Prelude](https://bedrock.institute/en/Base.Prelude.md) "
                      "(`Base.Prelude`, Foundations)\n", guide)
        self.assertIn("(`Milestones`, Preview): The proved endpoints.", guide)

    def test_the_page_description_places_a_chapter_the_catalog_does_not_describe(self):
        described = renderer.page_description("Base.Prelude", "en", False, False)
        self.assertIn("Chapter 2 of 2", described)
        self.assertIn("Foundations", described)
        self.assertNotEqual(described, "Prelude")

    def test_the_page_config_carries_what_the_handover_needs(self):
        import json
        config = json.loads(renderer.page_config(
            "Base.Prelude", "en", "Base.Prelude.html", "Base.Prelude.md", "", "Bedrock",
            False, False))
        self.assertEqual(config["chapter"], "Base.Prelude")
        self.assertEqual(config["title"], "Prelude")
        self.assertEqual(config["order"], 2)
        self.assertEqual(config["markdown"], "Base.Prelude.md")
        self.assertEqual(config["canonical"],
                         "https://bedrock.institute/en/Base.Prelude.html")
        self.assertFalse(config["external"])

    def test_a_library_page_is_not_claimed_as_a_chapter(self):
        import json
        config = json.loads(renderer.page_config(
            "Cubical.Data.Nat", "en", "Cubical.Data.Nat.html", "", "", "Bedrock",
            False, True))
        self.assertTrue(config["external"])
        self.assertNotIn("agdaSource", config)


if __name__ == "__main__":
    unittest.main()
