"""The local site cache may reuse highlighted code only with identical code."""
import importlib.util
import hashlib
from contextlib import ExitStack
import json
import os
from pathlib import Path
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch


SCRIPT = Path(__file__).resolve().parents[1] / 'site/site-cache.py'
spec = importlib.util.spec_from_file_location('bedrock_site_cache', SCRIPT)
cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache)


class SiteCacheTests(unittest.TestCase):
    def test_fingerprints_follow_real_stage_dependencies(self):
        # Perturb input bytes in memory, never edit the checked-out project.
        baseline = (cache.backend_identity(), cache.extractor_identity(), cache.render_identity())
        self.assertTrue(all(baseline))
        cases = {
            'Makefile': (False, False, False),
            'scripts/site/site-cache.py': (False, False, False),
            'site/README.md': (False, False, False),
            'site/inline-latex-approvals.json': (False, False, False),
            'site/host-lem-inventory.json': (False, False, False),
            'outcrop/src/outcrop/site/site_lint.py': (False, False, False),
            'outcrop/src/outcrop/core/prose_lint.py': (False, False, False),
            'outcrop/src/outcrop/adapters/source_stage.py': (False, False, False),
            'outcrop/src/outcrop/adapters/extract_types.py': (False, True, False),
            'site/agda-libraries.json': (True, False, False),
            'outcrop/src/outcrop/adapters/agda/parallel.py': (True, False, False),
            'outcrop/src/outcrop/site/page_renderer.py': (False, False, True),
            'outcrop/src/outcrop/core/diagram_style.py': (False, False, True),
            'outcrop/src/outcrop/site/resources/static/outcrop.css': (False, False, True),
            'site/reading-catalog.json': (False, False, True),
            'site/glossary.toml': (False, False, True),
            'site/static/assets/favicon.svg': (False, False, True),
        }
        for relative, expected in cases.items():
            changed = cache.ROOT / relative
            def modified_digest(path):
                return hashlib.sha256(path.read_bytes() + (b'changed' if path == changed else b'')).hexdigest()
            with self.subTest(path=relative), patch.object(cache, 'digest', side_effect=modified_digest):
                actual = (cache.backend_identity(), cache.extractor_identity(), cache.render_identity())
                self.assertEqual(tuple(a != b for a, b in zip(actual, baseline)), expected)

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


class CacheWorkflowTests(unittest.TestCase):
    """Freeze the recently introduced cache contract while changing Make wiring."""

    def setUp(self):
        stack = ExitStack()
        self.addCleanup(stack.close)
        root = Path(stack.enter_context(tempfile.TemporaryDirectory())).resolve()
        build = root / '_build'
        values = dict(ROOT=root, BUILD=build, HTML=build / 'html',
                      STAMP=build / 'html/.bedrock-checked', TRACE=build / 'trace.jsonl',
                      CACHE=build / 'cache', BACKEND_STATE=build / 'cache/site-backend.json',
                      TYPES=(build / 'types.json', build / 'expressions.json'),
                      INTERFACES=build / 'interfaces', AGDA_HOME=build / 'agda-home')
        for name, value in values.items():
            stack.enter_context(patch.object(cache, name, value))
        for name, value in [('backend_identity', 'compiler'), ('extractor_identity', 'extractor'),
                            ('render_identity', 'renderer')]:
            stack.enter_context(patch.object(cache, name, return_value=value))
        stack.enter_context(patch.object(cache, 'adopt_backend', return_value=False))
        self.run = stack.enter_context(patch.object(cache, 'run', side_effect=self.produce))
        self.source = root / 'src/Sample.lagda.md'
        self.source.parent.mkdir(parents=True)
        self.source.write_text('```agda\nx = 1\n```\n\nOld prose.\n')
        cache.HTML.mkdir(parents=True)
        (cache.HTML / 'Sample.md').write_text('<pre class="Agda"><a id="42">x</a> = 1\n</pre>\n\nOld prose.\n')
        cache.STAMP.touch(); cache.TRACE.write_text('trace')
        for path in cache.TYPES:
            path.write_text('{}')
        current = cache.source_inventory(cache.source_paths())
        self.backend = dict(schema=1, producer='compiler', extractor='extractor', sources=current,
                            compile_stamp=cache.STAMP.stat().st_mtime_ns,
                            stamp=cache.STAMP.stat().st_mtime_ns)
        cache.write_state(cache.BACKEND_STATE, self.backend)
        self.args = SimpleNamespace(site_out=str(build / 'site'), langs='en,zh,ja', base_url='',
                                    py='python', make='make', agda_jobs='2', local_parallel='1',
                                    render_only=False, backend_only=False, cold=False)

    def produce(self, command):
        if command[1] in ('html', 'html-cold-parallel'):
            cache.STAMP.touch()
        elif command[1] == '_types':
            for path in cache.TYPES:
                path.write_text('{"fresh": true}')
        else:
            out = Path(command[command.index('--out') + 1])
            for lang in self.args.langs.split(','):
                (out / lang).mkdir(parents=True, exist_ok=True)
                (out / lang / 'index.html').write_text('rendered')
            (out / 'search-content.json').write_text('[]')

    def warm(self):
        cache.build(self.args)
        self.run.reset_mock()

    def edit_prose(self):
        self.source.write_text(self.source.read_text().replace('Old prose.', 'New prose.'))

    def test_unchanged_build_does_not_compile_extract_or_render(self):
        self.warm()
        cache.build(self.args)
        self.run.assert_not_called()

    def test_prose_only_updates_chapter_overview_and_search_without_compiler(self):
        self.warm(); self.edit_prose()
        before = [path.read_bytes() for path in cache.TYPES]
        cache.build(self.args)
        self.assertEqual(self.run.call_count, 1)
        command = self.run.call_args.args[0]
        self.assertEqual(command[1], 'scripts/site/render-site.py')
        self.assertIn('--incremental', command)
        self.assertEqual([command[i+1] for i, value in enumerate(command) if value == '--module'], ['Origin', 'Sample'])
        self.assertEqual(before, [path.read_bytes() for path in cache.TYPES])
        self.assertIn('<a id="42">x</a>', (cache.HTML / 'Sample.md').read_text())
        self.assertIn('New prose.', (cache.HTML / 'Sample.md').read_text())

    def test_prose_plus_extractor_change_does_not_recompile_from_timestamps(self):
        self.edit_prose()
        with patch.object(cache, 'extractor_identity', return_value='extractor-2'):
            cache.build(self.args)
        self.assertEqual([call.args[0][1] for call in self.run.call_args_list],
                         ['_types', 'scripts/site/render-site.py'])

    def test_code_and_compiler_changes_rebuild_evidence(self):
        self.source.write_text(self.source.read_text().replace('x = 1', 'x = 2'))
        self.args.backend_only = True
        cache.build(self.args)
        self.assertEqual([call.args[0][1] for call in self.run.call_args_list], ['html', '_types'])
        self.run.reset_mock()
        with patch.object(cache, 'backend_identity', return_value='compiler-2'):
            cache.build(self.args)
        self.assertEqual([call.args[0][1] for call in self.run.call_args_list], ['html', '_types'])

    def test_missing_type_artifact_extracts_without_recompiling(self):
        cache.TYPES[0].unlink()
        self.args.backend_only = True
        cache.build(self.args)
        self.assertEqual(self.run.call_args.args[0][1], '_types')
        self.assertEqual(self.run.call_count, 1)

    def test_failed_extraction_is_not_cached_as_success(self):
        self.args.backend_only = True
        self.source.write_text(self.source.read_text().replace('x = 1', 'x = 2'))
        def fail(command):
            if command[1] == '_types':
                raise RuntimeError('extractor failed')
            self.produce(command)
        self.run.side_effect = fail
        with self.assertRaises(RuntimeError):
            cache.build(self.args)
        self.assertIsNone(cache.read_state(cache.BACKEND_STATE)['extractor'])
        self.run.reset_mock(); self.run.side_effect = self.produce
        cache.build(self.args)
        self.assertEqual([call.args[0][1] for call in self.run.call_args_list], ['_types'])

    def test_cold_backend_runs_once_then_extracts_once(self):
        self.args.cold = True; self.args.backend_only = True
        cache.build(self.args)
        self.assertEqual([call.args[0][1] for call in self.run.call_args_list], ['html-cold-parallel', '_types'])

    def test_render_only_reuses_artifact_without_local_compiler(self):
        self.warm(); self.args.render_only = True
        with patch.object(cache, 'backend_identity', side_effect=AssertionError('no compiler needed')):
            cache.build(self.args)
            self.run.assert_not_called()
            self.args.base_url = '/Bedrock'
            cache.build(self.args)
        self.assertEqual(self.run.call_args.args[0][1], 'scripts/site/render-site.py')
        self.assertNotIn('--incremental', self.run.call_args.args[0])

    def test_render_only_rejects_mismatched_source(self):
        self.args.render_only = True; self.edit_prose()
        with self.assertRaisesRegex(RuntimeError, 'does not match source'):
            cache.build(self.args)
        self.run.assert_not_called()

    def test_render_only_rejects_failed_or_stale_extraction(self):
        self.args.render_only = True
        for extractor in (None, 'old-extractor'):
            with self.subTest(extractor=extractor):
                cache.write_state(cache.BACKEND_STATE, {**self.backend, 'extractor': extractor})
                with self.assertRaisesRegex(RuntimeError, 'source/extractor'):
                    cache.build(self.args)
        self.run.assert_not_called()

    def test_archive_keys_match_local_identities_without_mutation(self):
        self.args.cache_keys = 'backend'
        first = cache.archive_keys(self.args)
        self.assertEqual(first['backend'], 'compiler')
        self.assertEqual(first['extractor'], 'extractor')
        self.args.cache_keys = 'render'
        render = cache.archive_keys(self.args)
        self.assertEqual(render['render'], cache.key_digest(cache.render_build_key(
            cache.source_inventory(cache.source_paths()), self.backend, ['en', 'zh', 'ja'], '')))
        self.edit_prose()
        self.args.cache_keys = 'backend'
        second = cache.archive_keys(self.args)
        self.assertNotEqual(first['source'], second['source'])
        self.assertEqual(first['backend'], second['backend'])
        self.assertEqual(first['extractor'], second['extractor'])
        self.assertEqual(cache.read_state(cache.BACKEND_STATE), self.backend)
        self.run.assert_not_called()

    def test_legacy_backend_receipt_reuses_evidence_despite_checkout_timestamps(self):
        self.args.backend_only = True
        os.utime(self.source, (2000000000, 2000000000))
        cache.build(self.args)
        self.run.assert_not_called()

    def test_incompatible_fallback_discards_interfaces_and_trace_before_compiling(self):
        self.args.backend_only = True
        cache.INTERFACES.mkdir()
        interface = cache.INTERFACES / 'Sample.agdai'
        interface.write_text('incompatible')
        cache.write_state(cache.BACKEND_STATE, {**self.backend, 'producer': 'old-compiler'})
        def inspect(command):
            if command[1] == 'html':
                self.assertFalse(interface.exists())
                self.assertFalse(cache.TRACE.exists())
            self.produce(command)
        self.run.side_effect = inspect
        cache.build(self.args)
        self.assertEqual([call.args[0][1] for call in self.run.call_args_list], ['html', '_types'])

    def test_ci_fallback_without_receipt_cannot_be_adopted_by_timestamps(self):
        self.args.backend_only = True
        cache.BACKEND_STATE.unlink()
        with patch.dict(os.environ, CI='true'), patch.object(cache, 'adopt_backend',
                side_effect=AssertionError('CI must validate recorded content identities')):
            cache.build(self.args)
        self.assertEqual([call.args[0][1] for call in self.run.call_args_list], ['html', '_types'])

    def test_compatible_fallback_keeps_unchanged_interfaces_and_refreshes_trace(self):
        self.args.backend_only = True
        cache.INTERFACES.mkdir()
        changed = cache.INTERFACES / 'Sample.agdai'
        unchanged = cache.INTERFACES / 'Untouched.agdai'
        changed.write_text('old code'); unchanged.write_text('compatible')
        os.utime(cache.TRACE, (1, 1))
        self.source.write_text(self.source.read_text().replace('x = 1', 'x = 2'))
        def inspect(command):
            if command[1] == 'html':
                self.assertFalse(changed.exists())
                self.assertEqual(unchanged.read_text(), 'compatible')
                self.assertEqual(cache.TRACE.read_text(), 'trace')
                self.assertGreater(cache.TRACE.stat().st_mtime, 1)
            self.produce(command)
        self.run.side_effect = inspect
        cache.build(self.args)

    def test_renderer_change_only_renders_and_keeps_backend_bytes(self):
        self.warm()
        before = [path.read_bytes() for path in (*cache.TYPES, cache.TRACE, cache.BACKEND_STATE)]
        with patch.object(cache, 'render_identity', return_value='renderer-2'):
            cache.build(self.args)
        self.assertEqual([call.args[0][1] for call in self.run.call_args_list], ['scripts/site/render-site.py'])
        self.assertNotIn('--incremental', self.run.call_args.args[0])
        self.assertEqual(before, [path.read_bytes() for path in (*cache.TYPES, cache.TRACE, cache.BACKEND_STATE)])

    def test_custom_paths_cross_make_boundary(self):
        command = cache.make_command(self.args, '_types')
        for name, path in [('HTML_DIR', cache.HTML), ('AGDA_TRACE', cache.TRACE),
                           ('AGDA_DIR', cache.AGDA_HOME), ('SITE_IFACES', cache.INTERFACES)]:
            self.assertIn(f'{name}={path}', command)

    def test_explicit_force_render_needs_no_backend_and_invalidates_only_its_receipt(self):
        self.warm()
        cache.BACKEND_STATE.unlink()
        self.args.render_only = True; self.args.force_render = True
        other = cache.site_state_path(Path(self.args.site_out).parent / 'other-site')
        cache.write_state(other, {'schema': 1})
        cache.build(self.args)
        self.assertEqual(self.run.call_count, 1)
        self.assertNotIn('--incremental', self.run.call_args.args[0])
        self.assertNotIn('--code-cache', self.run.call_args.args[0])
        self.assertFalse(cache.site_state_path(Path(self.args.site_out)).exists())
        self.assertTrue(other.exists())


if __name__ == '__main__':
    unittest.main()
