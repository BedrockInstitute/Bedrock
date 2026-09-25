"""Exercise Make orchestration without invoking a compiler or changing caches."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class MakeContractTests(unittest.TestCase):
    def run_make(self, *arguments, ci=''):
        result = subprocess.run(
            ['make', '--no-print-directory', 'LOCAL_JOBS=2', *arguments],
            cwd=ROOT, env={**os.environ, 'CI': ci}, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_default_is_help_and_removed_aliases_are_not_targets(self):
        output = self.run_make()
        self.assertIn('Setup:', output)
        self.assertNotIn('pip install', output)
        makefile = (ROOT / 'Makefile').read_text()
        for name in ('types-refresh', 'site-ci', 'site-backend-ci'):
            self.assertNotRegex(makefile, rf'(?m)^{name}:')

    def test_local_and_ci_share_site_command_with_explicit_resources(self):
        local = self.run_make('-n', 'site', 'LOCAL_PARALLEL=1')
        ci = self.run_make('-n', 'site', 'LOCAL_PARALLEL=1', ci='1')
        self.assertEqual(local, ci)
        self.assertEqual(local.count('scripts/site/site-cache.py'), 1)
        self.assertIn('--agda-jobs "2"', local)

    def test_raw_extraction_does_not_reenter_html(self):
        output = self.run_make('-n', '_types', f'PY={sys.executable}')
        self.assertEqual(output.count('scripts/site/extract-types.py'), 1)
        self.assertEqual(output.count('scripts/site/extract-expression-types.py'), 1)
        self.assertNotIn('agda-check', output)
        self.assertNotIn('--html-dir=_build/html', output)
        self.assertNotIn('src/Origin.lagda.md', output)

    def test_parallel_bootstrap_invokes_venv_before_toolchain(self):
        with tempfile.TemporaryDirectory() as folder:
            recorder = Path(folder) / 'record.py'
            log = Path(folder) / 'order'
            recorder.write_text(
                'import pathlib, sys\n'
                f'with pathlib.Path({str(log)!r}).open("a") as output:\n'
                '    output.write(sys.argv[-1] + "\\n")\n')
            self.run_make('-j2', 'bootstrap', f'MAKE={sys.executable} {recorder}')
            self.assertEqual(log.read_text().splitlines(), ['venv', 'toolchain'])

    def test_hooks_use_git_resolved_location(self):
        output = self.run_make('-n', 'hooks')
        self.assertIn('git rev-parse --git-path hooks', output)
        self.assertNotIn('.git/hooks/', output)
        self.assertNotIn('--no-verify', output)
