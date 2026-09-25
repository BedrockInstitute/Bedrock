"""Bedrock's documentation allowlist and workflow gate wiring."""
from pathlib import Path
import re
import unittest

from outcrop.adapters.ci_scope import documentation, read_policy

ROOT = Path(__file__).resolve().parents[2]


class BedrockCIScopeTests(unittest.TestCase):
    def test_documentation_policy_does_not_exempt_website_inputs(self):
        policy = read_policy(ROOT / 'site/ci-docs.json')
        for path in ('README.md', 'src/README.md', 'scripts/README.md',
                     '.github/workflows/README.md', 'site/STYLE-i18n.md',
                     'docs/zh/README.md', 'dev/literature/digest.md'):
            self.assertTrue(documentation(path, policy), path)
        for path in ('src/Base/Prelude.lagda.md', 'dev/Probe.lagda.md',
                     'site/project.json', 'site/reading-catalog.json',
                     'site/glossary.toml', 'site/static/assets/banner.png',
                     'site/ci-docs.json', '.github/workflows/ci.yml',
                     'Makefile', 'scripts/site/render-site.py', 'unknown.md'):
            self.assertFalse(documentation(path, policy), path)
        self.assertEqual(policy['submodules'], {'outcrop': '.github/docs-only.json'})

    def test_expensive_steps_scoped_but_existing_required_gate_remains(self):
        workflow = (ROOT / '.github/workflows/ci.yml').read_text()
        job = workflow.split('  typecheck:\n', 1)[1].split('  site-backend:\n')[0]
        self.assertNotIn('    if:', job.split('    steps:\n')[0])
        self.assertIn('fetch-depth: 0', job)
        for step in re.split(r'^      - name: ', job, flags=re.M)[1:]:
            name = step.splitlines()[0]
            if name in {'Checkout', 'Set up Python 3.11', 'Install Outcrop',
                        'Classify changes', 'Lint and test', 'Check milestone consumption'}:
                self.assertNotIn('        if:', step, name)
            else:
                self.assertIn("steps.scope.outputs.full == 'true'", step, name)
        backend = workflow.split('  site-backend:\n', 1)[1].split('    steps:\n')[0]
        self.assertIn("needs.typecheck.outputs.full == 'true'", backend)
        self.assertIn("github.ref == 'refs/heads/main'", backend)
        self.assertIn("github.event_name == 'workflow_dispatch'", backend)
