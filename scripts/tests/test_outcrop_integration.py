"""Only Bedrock's wiring belongs here; generic mechanisms are tested in Outcrop."""
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[2]


class OutcropIntegrationTests(unittest.TestCase):
    def test_durable_configuration_lives_in_site_not_dev(self):
        config = json.loads((ROOT / 'site/project.json').read_text())
        for key in ('catalog', 'glossary', 'variable_legacy'):
            self.assertTrue(config[key].startswith('site/'), key)
            self.assertTrue((ROOT / config[key]).is_file())
        self.assertFalse(list((ROOT / 'dev').glob('*.json')))
        self.assertFalse(list((ROOT / 'dev').glob('*.toml')))
        for name in ('STYLE-agda.md', 'STYLE-i18n.md', 'TEACHING.md',
                     'GLOSSARY.md', 'AGDA-ENVIRONMENT.md', 'ARCHITECTURE.md'):
            self.assertTrue((ROOT / 'site' / name).is_file(), name)

    def test_bedrock_library_policy_stays_explicit(self):
        from outcrop.adapters.agda.libraries import read_lock
        libraries = read_lock(ROOT / 'site/agda-libraries.json')
        self.assertEqual([(item['name'], item['version']) for item in libraries], [('cubical', '0.9')])
        config = json.loads((ROOT / 'site/project.json').read_text())
        self.assertEqual(config['landing_module'], 'Origin')
        self.assertEqual(config['programming_language']['name'], 'Cubical Agda')

    def test_every_ci_job_installs_into_its_final_python_environment(self):
        workflow = (ROOT / '.github/workflows/ci.yml').read_text()
        jobs = re.split(r'^  [\w-]+:\n', workflow.split('\njobs:\n', 1)[1], flags=re.M)[1:]
        self.assertEqual(len(jobs), 4)
        for job in jobs:
            setup = job.index('uses: actions/setup-python@')
            install = job.index('python3 -m pip install ./outcrop')
            self.assertLess(setup, install)
            self.assertNotIn('uses: actions/setup-python@', job[install:])
            self.assertIn('submodules: recursive', job)

    def test_build_consumes_shared_producers_not_private_copies(self):
        make = (ROOT / 'Makefile').read_text()
        for command in ('agda-build', 'agda-libraries', 'agda-check'):
            self.assertIn('-m outcrop ' + command, make)
        self.assertFalse((ROOT / 'tools/bedrock-agda/build.py').exists())
        self.assertFalse((ROOT / 'scripts/agda-parallel.py').exists())

    def test_library_policy_invalidates_the_complete_semantic_backend(self):
        make = (ROOT / 'Makefile').read_text()
        self.assertIn('AGDA_ENV_INPUTS := site/agda-libraries.json', make)
        self.assertIn('$(AGDA_ENV_STAMP): $(AGDA_ENV_INPUTS)', make)
        self.assertIn('$(AGDA_STAMP): $(OUTCROP_AGDA) $(AGDA_ENV_STAMP)', make)
        self.assertIn('[ $(AGDA_ENV_STAMP) -nt $(AGDA_TRACE) ]', make)
        workflow = (ROOT / '.github/workflows/ci.yml').read_text()
        for line in workflow.splitlines():
            if 'hashFiles(' in line and 'bedrock.agda-lib' in line:
                self.assertIn('site/agda-libraries.json', line)


if __name__ == '__main__':
    unittest.main()
