import importlib.util
from pathlib import Path
import subprocess
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "site" / "extract-types.py"


def load_script():
    spec = importlib.util.spec_from_file_location("bedrock_extract_types", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


extract_types = load_script()


class ExtractTypesTests(unittest.TestCase):
    def test_run_agda_uses_the_selected_executable(self):
        completed = subprocess.CompletedProcess([], 0, stdout="", stderr="")
        with mock.patch.object(extract_types.subprocess, "run", return_value=completed) as run:
            extract_types.run_agda("commands", "/project/_build/bin/bedrock-agda")
        self.assertEqual(
            run.call_args.args[0],
            ["/project/_build/bin/bedrock-agda", "--interaction-json"],
        )

    def test_main_forwards_agda_option(self):
        with mock.patch.object(extract_types, "extract", return_value={}) as extract, \
             mock.patch("builtins.print"):
            self.assertEqual(
                extract_types.main(["--agda", "/tmp/bedrock-agda"]),
                0,
            )
        extract.assert_called_once_with("_build/html", "src", "/tmp/bedrock-agda")


if __name__ == "__main__":
    unittest.main()
