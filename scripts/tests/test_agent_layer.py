"""Bedrock catalog addresses agree with the shared website publisher."""
import unittest
from pathlib import Path
from outcrop.site import reading_routes

ROOT = Path(__file__).resolve().parents[2]


class BedrockCatalogTests(unittest.TestCase):
    def test_the_catalog_gives_a_preview_chapter_the_guide_panel(self):
        data = reading_routes.build_reading_data(ROOT / "src", ROOT / "dev/reading-catalog.json",
                                               extension='.lagda.md', previews={'Origin'})
        node = next(n for n in data["nodes"] if n["id"] == "Origin")
        self.assertTrue(node["preview"])
        self.assertEqual(node["page"], reading_routes.GUIDE_PAGE)
        self.assertEqual(node["anchor"], f"#{reading_routes.GUIDE_PANEL}")


    def test_the_catalog_gives_every_other_chapter_its_own_page(self):
        data = reading_routes.build_reading_data(ROOT / "src", ROOT / "dev/reading-catalog.json",
                                               extension='.lagda.md', previews={'Origin'})
        for node in data["nodes"]:
            if node["preview"]:
                continue
            with self.subTest(chapter=node["id"]):
                self.assertEqual(node["page"], f"{node['id']}.html")
                self.assertEqual(node["anchor"], "")
