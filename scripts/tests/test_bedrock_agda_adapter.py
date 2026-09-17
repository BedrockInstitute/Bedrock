import json
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[2]
TOOL = ROOT / "tools" / "bedrock-agda"


class BedrockAgdaAdapterTests(unittest.TestCase):
    def setUp(self):
        self.manifest = json.loads((TOOL / "manifest.json").read_text())
        self.environment = json.loads((TOOL / "environment.json").read_text())
        self.adapter = TOOL / self.manifest["adapter"]
        self.patch = self.adapter.read_text()

    def test_version_lock_names_an_existing_thin_adapter(self):
        self.assertEqual(self.manifest["agda_version"], "2.8.0")
        self.assertTrue(self.adapter.is_file())
        self.assertTrue((TOOL / "src/Bedrock/Agda/TypeTrace.hs").is_file())

    def test_environment_lock_pins_cubical_and_host_versions(self):
        self.assertEqual(self.environment["cubical_version"], "0.9")
        self.assertEqual(len(self.environment["cubical_sha256"]), 64)
        self.assertEqual(self.environment["minimum_python_version"], "3.11")

    def test_adapter_only_touches_declared_semantic_hook_files(self):
        touched = {
            line.removeprefix("+++ b/")
            for line in self.patch.splitlines()
            if line.startswith("+++ b/")
        }
        self.assertEqual(touched, {
            "Agda.cabal",
            "src/full/Agda/Main.hs",
            "src/full/Agda/Interaction/Imports.hs",
            "src/full/Agda/TypeChecking/Rules/Application.hs",
            "src/full/Agda/TypeChecking/Rules/LHS.hs",
            "src/full/Agda/TypeChecking/Rules/Term.hs",
        })

    def test_adapter_contains_calls_but_no_tracing_implementation(self):
        additions = [
            line for line in self.patch.splitlines()
            if line.startswith("+") and not line.startswith("+++")
        ]
        self.assertLessEqual(len(additions), 80)
        self.assertIn("Bedrock.Agda.TypeTrace", self.patch)
        self.assertNotIn("module Bedrock.", self.patch)
        self.assertNotIn("x-revision:", self.patch)
        self.assertNotIn("aeson                >=", self.patch)


if __name__ == "__main__":
    unittest.main()
