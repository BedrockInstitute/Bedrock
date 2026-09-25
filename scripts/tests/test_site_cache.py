"""The local site cache may reuse highlighted code only with identical code."""
import importlib.util
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


SCRIPT = Path(__file__).resolve().parents[1] / 'site/site-cache.py'
spec = importlib.util.spec_from_file_location('bedrock_site_cache', SCRIPT)
cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache)


class SiteCacheTests(unittest.TestCase):
    def test_render_key_uses_content_not_artifact_timestamps(self):
        with tempfile.TemporaryDirectory() as folder:
            files = (Path(folder) / 'types.json', Path(folder) / 'expressions.json')
            for path in files:
                path.write_text('{}')
            current = {'Sample': {'source': 'prose-1', 'blocks': ['code-1']}}
            with patch.object(cache, 'TYPES', files), patch.object(cache, 'render_identity', return_value='renderer'):
                first = cache.render_build_key(current, {'producer': 'compiler'}, ['en'], '')
                for path in files:
                    os.utime(path, None)
                self.assertEqual(first, cache.render_build_key(current, {'producer': 'compiler'}, ['en'], ''))
                current['Sample']['source'] = 'prose-2'
                self.assertEqual(first, cache.render_build_key(current, {'producer': 'compiler'}, ['en'], ''))
                current['Sample']['blocks'] = ['code-2']
                self.assertNotEqual(first, cache.render_build_key(current, {'producer': 'compiler'}, ['en'], ''))

    def test_reweave_preserves_certified_code_and_updates_prose(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            master = root / 'Sample.lagda.md'
            output = root / 'Sample.md'
            output.write_text('<pre class="Agda"><a id="42" class="Function">x</a> = 1\n'
                              '</pre>\n\nOld explanation.\n')
            master.write_text('```agda\nx = 1\n```\n\nNew explanation.\n')
            with patch.object(cache, 'highlighted_path', return_value=output):
                woven = cache.reweave('Sample', master)
                self.assertIn('New explanation.', woven)
                self.assertNotIn('Old explanation.', woven)
                self.assertIn('id="42"', woven)
                master.write_text('```agda\nx = 2\n```\n\nNew explanation.\n')
                self.assertIsNone(cache.reweave('Sample', master))


if __name__ == '__main__':
    unittest.main()
