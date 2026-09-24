"""The consumer supplies source discovery and its actual library metadata."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('bedrock_weave', ROOT / 'scripts/site/weave-i18n.py')
adapter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(adapter)


class BedrockWeaveTests(unittest.TestCase):
    def test_library_configuration_preserves_dependencies_and_flags(self):
        actual = (ROOT / 'bedrock.agda-lib').read_text().splitlines()
        for language in ('en', 'zh', 'ja'):
            name, text = adapter.woven_library(language)
            self.assertEqual(name, 'bedrock.agda-lib')
            self.assertIn('name: bedrock-woven-' + language, text)
            self.assertIn('include: .', text)
            self.assertEqual([line for line in text.splitlines() if not line.startswith(('name:', 'include:'))],
                             [line for line in actual if not line.startswith(('name:', 'include:'))])
