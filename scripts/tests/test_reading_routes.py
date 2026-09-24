"""Bedrock reading-catalog adapter and actual editorial metadata."""
import importlib.util
import contextlib
import io
import tempfile
import unittest
from pathlib import Path
from outcrop.site import reading_routes as routes
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('bedrock_reading_routes', ROOT / 'scripts/site/reading_routes.py')
route_cli = importlib.util.module_from_spec(spec); spec.loader.exec_module(route_cli)


class BedrockRoutesTests(unittest.TestCase):
    def test_actual_catalog_review_status_is_explicit(self):
        _, catalog = routes._load_catalog(ROOT / 'site/reading-catalog.json')
        self.assertTrue(all(type(item['human_reviewed']) is bool for item in catalog.values()))

    def test_cli_reports_validation_errors(self):
        with tempfile.TemporaryDirectory() as directory:
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                result = route_cli.main(["--src", directory, "--check"])
        self.assertEqual(result, 1)
        self.assertIn("reading catalog must cover every chapter exactly once", output.getvalue())
