"""Public renderer boundaries, isolated distribution, and project-state isolation."""
from pathlib import Path
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts/site'))
from assets import AssetBundle
from document_renderer import MarkdownDocument
from site_config import SiteConfig
from site_lint import lint_site
from website import build_site

EXAMPLE = ROOT / 'examples/renderer'


class RendererLibraryTests(unittest.TestCase):
    def test_plain_markdown_needs_no_project_or_semantics(self):
        result = MarkdownDocument((EXAMPLE / 'plain.md').read_text()).render('en')
        self.assertIn('A renderer without a project', result.body)
        self.assertIn('href="chapter.html#detail"', result.body)
        self.assertIn('unknown value', result.body)
        self.assertNotIn('data-type=', result.body)
        self.assertNotIn('expr-node', result.body)
        self.assertNotIn('Bedrock', result.body)
        self.assertNotIn('\x00', result.mirror)
        self.assertIn('```agda\nunknown value = value\n```', result.mirror)

    def test_asset_snapshot_is_a_single_generation(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            source = root / 'source'; source.mkdir()
            (source / 'entry.js').write_text('import "./leaf.js";')
            (source / 'leaf.js').write_text('export const value = 1;')
            first = AssetBundle(source)
            (source / 'leaf.js').write_text('export const value = 2;')
            second = AssetBundle(source)
            self.assertNotEqual(first.runtime, second.runtime)
            first.publish(root / 'output')
            self.assertEqual((root / 'output' / first.runtime / 'leaf.js').read_text(),
                             'export const value = 1;')
            self.assertIn(first.runtime, first.template('%%RUNTIME%%'))

    def test_config_rejects_unsafe_paths_types_and_references(self):
        values = json.loads((EXAMPLE / 'project.json').read_text())
        for update in ({'sources': '../secret'}, {'sources': 'https:chapter'},
                       {'base_url': '/bad path'}, {'base_url': '/bad\npath'},
                       {'favicon': []}, {'favicon': ''}, {'languages': [{}]}, {'base_url': '//outside'},
                       {'canonical': 'javascript:alert(1)'}, {'agent': {'translations': {'en': {'fetch': 'code'}}}},
                       {'legacy_pages': {'../old.html': 'index.html'}}, {'agda_policy': {'options': 'not-list'}}):
            with self.subTest(update=update), self.assertRaises(ValueError):
                SiteConfig({**values, **update}, root=EXAMPLE)
        config = SiteConfig(values, root=EXAMPLE)
        with self.assertRaises(ValueError):
            config.validate_references({'Unrelated'})

    def test_strict_lint_of_independent_project(self):
        config = SiteConfig.load(EXAMPLE / 'project.json', root=EXAMPLE)
        self.assertEqual(lint_site(config), [])

    def test_partial_prerequisites_override_only_named_chapters(self):
        from reading_routes import build_reading_data
        reading = build_reading_data(EXAMPLE / 'chapters', EXAMPLE / 'catalog.json',
            previews={'Welcome'}, prerequisites={'Sample.Seed': []})
        nodes = {node['id']: node for node in reading['nodes']}
        self.assertEqual(nodes['Sample.Seed']['prerequisites'], [])
        self.assertEqual(nodes['Sample.Use']['prerequisites'], ['Sample.Seed'])

    def test_configuration_is_an_owned_snapshot(self):
        values = json.loads((EXAMPLE / 'project.json').read_text())
        config = SiteConfig(values, root=EXAMPLE)
        values['languages'].clear()
        values['descriptions']['en'] = 'mutated'
        self.assertEqual(config.languages, ['en', 'zh', 'ja'])
        self.assertNotEqual(config.descriptions['en'], 'mutated')

    def test_two_instances_in_one_process(self):
        first = SiteConfig.load(EXAMPLE / 'project.json', root=EXAMPLE)
        second = first.with_overrides(name='Prism Lessons', publisher='Prism Group',
            storage_namespace='prism', canonical='https://prism.example/course', base_url='/course')
        with tempfile.TemporaryDirectory() as folder:
            for index, config in enumerate((first, second, first)):
                output = Path(folder) / str(index)
                self.assertEqual(build_site(config, ['--out', str(output)]), 0)
                page = (output / 'en/Sample.Use.html').read_text()
                self.assertIn(config.name, page)
                self.assertIn('"storageNamespace":"' + config.storage_namespace + '"', page)
                self.assertIn(config.canonical + '/en/Sample.Use.html', page)
                for forbidden in ('Bedrock Institute', 'bedrock.institute', 'Base.Prelude', 'L⊨ZFC', 'src/'):
                    self.assertNotIn(forbidden, page)
                self.assertIn(config.name, (output / 'llms.txt').read_text())
                self.assertIn(f'agent_guide: {config.base_url}/llms.txt\n',
                              (output / 'en/Sample.Use.md').read_text())
                self.assertIn('CC0-1.0', page)
                self.assertEqual((output / 'static/assets/logo.svg').read_bytes(), (EXAMPLE / 'lantern.svg').read_bytes())

    def test_isolated_distribution_has_no_instance_or_toolchain(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            shutil.copytree(ROOT / 'scripts/site', root / 'scripts/site',
                            ignore=shutil.ignore_patterns('__pycache__'))
            shutil.copytree(ROOT / 'site/static', root / 'site/static',
                            ignore=shutil.ignore_patterns('assets'))
            shutil.copy2(ROOT / 'site/template.html', root / 'site/template.html')
            shutil.copytree(EXAMPLE, root / 'book')
            self.assertFalse((root / 'site/project.json').exists())
            self.assertFalse((root / 'src').exists())
            self.assertFalse((root / 'dev').exists())
            environment = {**os.environ, 'PATH': '/no-toolchain'}
            result = subprocess.run([sys.executable, str(root / 'scripts/site/website.py'),
                '--config', str(root / 'book/project.json'), '--project-root', str(root / 'book'),
                '--out', str(root / 'output')], cwd=root, env=environment, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertTrue((root / 'output/en/index.html').exists())
            result = subprocess.run([sys.executable, str(root / 'scripts/site/render-site.py'),
                '--config', str(root / 'book/project.json'), '--project-root', str(root / 'book'),
                '--out', str(root / 'compatibility-output')], cwd=root, env=environment,
                capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            result = subprocess.run([sys.executable, str(root / 'scripts/site/site_lint.py'),
                '--config', str(root / 'book/project.json'), '--project-root', str(root / 'book')],
                cwd=root, env=environment, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
