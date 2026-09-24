"""The addressable, machine-readable layer the site publishes beside its pages.

A passage has to be citable: a reader who selects a sentence and hands it to an
assistant, and the assistant that then follows the link, both need the anchor to name
the same block on the next visit. These tests pin the anchoring rule, the Markdown
twin and the shape of the guide an agent reads first.
"""

from pathlib import Path
import re
import unittest


import sys

from outcrop.site import reading_routes
from outcrop.core.markdown_core import anchor_prose_blocks, md_to_html, plain_code
from outcrop.site.site_config import SiteConfig, BookCatalog
from outcrop.site.page_renderer import PageRenderer
from outcrop.site.publication import Publication
from outcrop.core.document_renderer import MarkdownDocument


def catalog_entry(module, preview=False, **fields):
    """A catalog entry shaped the way `build_reading_data` shapes one.

    The address is not restated here. It is read from the same constants the catalog
    builds it from, so a test cannot quietly disagree with the site about where a
    chapter lives.
    """
    entry = {"page": reading_routes.GUIDE_PAGE if preview else f"{module}.html",
             "anchor": f"#{reading_routes.GUIDE_PANEL}" if preview else "",
             "prerequisites": [], "routes": [], "order": 0}
    entry.update(fields)
    return entry



class PublicationCase(unittest.TestCase):
    def setUp(self):
        self.config = SiteConfig.load(Path(__file__).resolve().parents[2] / 'site/project.json',
                                      root=Path(__file__).resolve().parents[2])
        self.book = BookCatalog()
        self.publication = Publication(self.config, self.book)
        self.pages = PageRenderer(self.config, self.book, self.publication)


class FooterTests(PublicationCase):
    def test_machine_links_follow_source_on_the_second_line(self):
        footer = self.publication.footer_html("zh", "", "Base.Impredicativity.md")
        self.assertEqual(footer.count("<div"), 2)
        self.assertIn("(AGPL-3.0)</div>", footer)
        self.assertNotIn("(AGPL-3.0)。", footer)
        source = footer.index(">源码</a>")
        markdown = footer.index(">Markdown</a>")
        agents = footer.index(">llms.txt</a>")
        self.assertLess(source, markdown)
        self.assertLess(markdown, agents)
        self.assertIn(">源码</a> · <a", footer)
        self.assertIn(">Markdown</a> · <a", footer)


class ProseAnchorTests(PublicationCase):
    def test_existing_accessible_title_id_is_preserved(self):
        body = '<p class="ancillary-title" id="construction-title">Details</p><p>Next</p>'
        anchored = anchor_prose_blocks(body)
        self.assertEqual(re.findall(r'id="([^"]+)"', anchored), ['construction-title', 'p-2'])

    def test_paragraphs_are_numbered_in_document_order(self):
        body, _ = md_to_html("First one.\n\nSecond one.\n\nThird one.")
        anchored = anchor_prose_blocks(body)
        self.assertEqual(re.findall(r'id="(p-\d+)"', anchored), ["p-1", "p-2", "p-3"])

    def test_list_items_are_addressable_too(self):
        body, _ = md_to_html("Lead in.\n\n- one\n- two")
        anchored = anchor_prose_blocks(body)
        self.assertEqual(re.findall(r'id="(p-\d+)"', anchored), ["p-1", "p-2", "p-3"])

    def test_a_nested_block_is_not_numbered_separately(self):
        """The outermost block is the addressable unit, so a quoted paragraph shares
        its quotation's anchor rather than claiming one of its own."""
        body, _ = md_to_html("> quoted prose\n\nAfter.")
        anchored = anchor_prose_blocks(body)
        self.assertEqual(re.findall(r'id="(p-\d+)"', anchored), ["p-1", "p-2"])
        self.assertIn('<blockquote id="p-1">', anchored)
        self.assertIn("<blockquote id=\"p-1\"><p>quoted prose</p></blockquote>", anchored)

    def test_headings_keep_their_own_scheme(self):
        body, _ = md_to_html("# Title\n\nProse.\n\n## Section\n\nMore.")
        anchored = anchor_prose_blocks(body)
        self.assertEqual(re.findall(r'id="(sec-\d+)"', anchored), ["sec-0", "sec-1"])
        self.assertEqual(re.findall(r'id="(p-\d+)"', anchored), ["p-1", "p-2"])

    def test_an_agda_block_is_left_to_its_own_token_anchors(self):
        body = '<p>Before.</p>\n<pre class="Agda"><a id="17">x</a></pre>\n<p>After.</p>'
        anchored = anchor_prose_blocks(body)
        self.assertEqual(re.findall(r'id="(p-\d+)"', anchored), ["p-1", "p-2"])
        self.assertIn('<pre class="Agda"><a id="17">', anchored)

    def test_numbering_does_not_depend_on_the_language(self):
        """The three editions share anchors because they share block structure, which is
        what lets a handover in one language cite a passage another reader can open."""
        shapes = ("One.\n\nTwo.\n\n- a\n- b", "一。\n\n二。\n\n- 甲\n- 乙",
                  "一つ。\n\n二つ。\n\n- あ\n- い")
        counts = set()
        for text in shapes:
            body, _ = md_to_html(text)
            counts.add(tuple(re.findall(r'id="(p-\d+)"', anchor_prose_blocks(body))))
        self.assertEqual(len(counts), 1, counts)


class ChapterAddressTests(PublicationCase):
    """One rule decides where a chapter is read, and every consumer reads it.

    The rule lives on the catalog node as `page` and `anchor`. These tests hold the
    renderer to it, so a second opinion about a chapter's URL cannot be introduced
    without failing here.
    """

    def setUp(self):
        super().setUp()
        self.book.meta.clear()
        self.book.meta.update({
            "Origin": catalog_entry("Origin", preview=True),
            "Base.Prelude": catalog_entry("Base.Prelude")})

    def test_the_catalog_gives_a_preview_chapter_the_guide_panel(self):
        data = reading_routes.build_reading_data("src", "dev/reading-catalog.json",
                                               extension='.lagda.md', previews={'Origin'})
        node = next(n for n in data["nodes"] if n["id"] == "Origin")
        self.assertTrue(node["preview"])
        self.assertEqual(node["page"], reading_routes.GUIDE_PAGE)
        self.assertEqual(node["anchor"], f"#{reading_routes.GUIDE_PANEL}")

    def test_the_catalog_gives_every_other_chapter_its_own_page(self):
        data = reading_routes.build_reading_data("src", "dev/reading-catalog.json",
                                               extension='.lagda.md', previews={'Origin'})
        for node in data["nodes"]:
            if node["preview"]:
                continue
            with self.subTest(chapter=node["id"]):
                self.assertEqual(node["page"], f"{node['id']}.html")
                self.assertEqual(node["anchor"], "")

    def test_a_plain_link_to_a_preview_chapter_goes_to_the_panel(self):
        self.assertEqual(self.book.href("Origin"), "index.html#milestones")
        self.assertEqual(self.book.href("Base.Prelude"), "Base.Prelude.html")

    def test_an_explicit_anchor_wins_over_the_panel(self):
        """The guide embeds the chapter's whole body, so an anchor the chapter defines
        resolves there; a reader who asked for it must land on it, not on the panel."""
        self.assertEqual(self.book.href("Origin", "#1354"), "index.html#1354")
        self.assertEqual(self.book.href("Origin", "#term-transitive-set"),
                         "index.html#term-transitive-set")

    def test_a_library_page_is_addressed_by_its_own_name(self):
        """A module with no catalog entry is rendered for reference, not as a chapter."""
        self.assertEqual(self.book.href("Cubical.Data.Nat.Base", "#973"),
                         "Cubical.Data.Nat.Base.html#973")

    def test_the_guide_panel_id_is_the_anchor_the_catalog_hands_out(self):
        body, _ = md_to_html("# Origin\n\nThe endpoints.")
        home = self.pages.learning_home(body, "", "en", [])
        self.assertIn(f'<section id="{reading_routes.GUIDE_PANEL}"', home)
        self.assertIn(self.book.href("Origin").split("#")[1], home)


class PlainCodeTests(PublicationCase):
    def test_highlighting_is_stripped_back_to_the_agda_source(self):
        block = ('<pre class="Agda"><a id="1" class="Keyword">open</a> '
                 '<a id="2" class="Keyword">import</a> '
                 '<a id="3" href="Base.Prelude.html" class="Module">Base.Prelude</a>\n</pre>')
        self.assertEqual(plain_code(block), "open import Base.Prelude")

    def test_escaped_source_characters_come_back_unescaped(self):
        block = '<pre class="Agda"><a id="4">x</a> &lt;&gt; &amp; y</pre>'
        self.assertEqual(plain_code(block), "x <> & y")


class MarkdownTwinTests(PublicationCase):
    def setUp(self):
        super().setUp()
        self.book.titles.clear()
        self.book.titles.update({"V.Hierarchy": {"en": "The cumulative hierarchy"}})
        self.book.meta.clear()
        self.book.meta.update({"V.Hierarchy": catalog_entry(
            "V.Hierarchy",
            description={"en": "The ambient hierarchy V as a higher inductive type."},
            stage={"en": "The ambient hierarchy"}, order=21,
            prerequisites=["Base.Prelude"], routes=["common-foundations"])})

    def twin(self, text):
        rendered = MarkdownDocument(text, terms=[{
            'id': 'transitive-set', 'introduced_in': 'V.Hierarchy'}]).render('en')
        return self.publication.publish_markdown(rendered.mirror, "V.Hierarchy", "en",
                                                 "V.Hierarchy.html", ["en", "zh", "ja"])

    def test_front_matter_states_where_the_chapter_sits(self):
        text = self.twin("# Title\n\nProse.\n")
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
        head = self.twin("# Title\n").split("---")[1]
        line = next(l for l in head.splitlines() if l.startswith("translations:"))
        self.assertIn("https://bedrock.institute/zh/V.Hierarchy.md", line)
        self.assertIn("https://bedrock.institute/ja/V.Hierarchy.md", line)
        self.assertNotIn("/en/", line)

    def test_a_displayed_block_becomes_a_fence_that_stands_alone(self):
        block = '<pre class="Agda"><a id="1" class="Keyword">module</a> M\n</pre>'
        text = self.twin("Lead in.\n" + block + "\nAfter.\n")
        self.assertIn("Lead in.\n\n```agda\nmodule M\n```\n\nAfter.", text)
        # a closing fence is always followed by a blank line, so the prose after a
        # displayed block cannot be swallowed into it
        self.assertEqual(re.findall(r"^```\n(?=\S)", text, re.M), [])

    def test_reader_markup_is_reduced_to_what_it_says(self):
        text = self.twin("A [transitive set]{.term-intro #transitive-set} and "
                         "`V`{.Agda} appear here.\n")
        self.assertIn("A transitive set and `V` appear here.", text)


class AgentGuideTests(PublicationCase):
    def setUp(self):
        super().setUp()
        self.book.titles.clear()
        self.book.titles.update({"Origin": {"en": "Origin"},
                                        "Base.Prelude": {"en": "Prelude"}})
        self.book.meta.clear()
        self.book.meta.update({
            "Origin": catalog_entry("Origin", preview=True,
                                        description={"en": "The proved endpoints."},
                                        stage={"en": "Preview"}, order=1),
            "Base.Prelude": catalog_entry("Base.Prelude",
                                          description={"en": "Prelude"},
                                          stage={"en": "Foundations"}, order=2)})

    def test_the_guide_names_every_chapter_and_its_markdown_twin(self):
        guide = self.publication.agent_guide(["en", "zh", "ja"], ["Origin", "Base.Prelude"])
        self.assertIn("(https://bedrock.institute/en/Base.Prelude.md)", guide)
        self.assertIn("/en/reading-routes.json", guide)
        self.assertIn("/en/search.json", guide)
        self.assertIn("/en/terms.json", guide)

    def test_a_description_that_only_restates_the_title_is_dropped(self):
        """Repeating the chapter title as its description costs an agent tokens and
        tells it nothing, so the index omits it rather than saying it twice."""
        guide = self.publication.agent_guide(["en"], ["Origin", "Base.Prelude"])
        self.assertIn("2. Prelude](https://bedrock.institute/en/Base.Prelude.md) "
                      "(`Base.Prelude`, Foundations)\n", guide)
        self.assertIn("The proved endpoints.", guide)

    def test_a_chapter_read_elsewhere_says_where(self):
        """The preview chapter has no page of its own, so the index gives the guide
        panel it is read at rather than a filename that would 404."""
        guide = self.publication.agent_guide(["en"], ["Origin", "Base.Prelude"])
        self.assertIn("[1. Origin](https://bedrock.institute/en/index.md)", guide)
        self.assertIn("read at https://bedrock.institute/en/index.html#milestones", guide)
        self.assertNotIn("Origin.md", guide)
        self.assertNotIn("Origin.html", guide)
        # a chapter that is read where its name says stays quiet about it
        self.assertNotIn("read at https://bedrock.institute/en/Base.Prelude.html", guide)

    def test_the_page_description_places_a_chapter_the_catalog_does_not_describe(self):
        described = self.publication.page_description("Base.Prelude", "en", False, False)
        self.assertIn("Chapter 2 of 2", described)
        self.assertIn("Foundations", described)
        self.assertNotEqual(described, "Prelude")

    def test_the_page_config_carries_what_the_handover_needs(self):
        import json
        config = json.loads(self.publication.page_config(
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
        config = json.loads(self.publication.page_config(
            "Cubical.Data.Nat", "en", "Cubical.Data.Nat.html", "", "", "Bedrock",
            False, True))
        self.assertTrue(config["external"])
        self.assertNotIn("agdaSource", config)


if __name__ == "__main__":
    unittest.main()
