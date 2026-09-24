import importlib.util
from pathlib import Path
import subprocess
import tempfile
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
        extract.assert_called_once_with("_build/html", "src", "/tmp/bedrock-agda", entry="Origin", libraries=["cubical"])

    def test_definition_names_include_pattern_synonyms(self):
        with tempfile.TemporaryDirectory() as directory:
            html = Path(directory) / "Demo.html"
            html.write_text(
                '<a id="tt*"></a><a id="245" href="Demo.html#245" '
                'class="InductiveConstructor">tt*</a> '
                '<a id="250" class="Symbol">to</a> '
                '<a id="253" class="Function">map₁</a>',
                encoding="utf-8",
            )
            self.assertEqual(
                extract_types.definition_names(directory, ["Demo"]),
                {"Demo": [("tt*", "InductiveConstructor"), ("map₁", "Function")]},
            )

    def test_query_missing_recovers_inferred_types_and_skips_errors(self):
        output = "\n".join([
            '{"kind":"DisplayInfo","info":{"kind":"InferredType",'
            '"expr":"Lift Unit"}}',
            '{"kind":"DisplayInfo","info":{"kind":"NormalForm",'
            '"expr":"\\"BEDROCK-TYPE-MARK-0\\""}}',
            '{"kind":"DisplayInfo","info":{"kind":"Error"}}',
            '{"kind":"DisplayInfo","info":{"kind":"NormalForm",'
            '"expr":"\\"BEDROCK-TYPE-MARK-1\\""}}',
        ])
        with mock.patch.object(extract_types, "run_agda", return_value=output) as run:
            result = extract_types.query_missing(
                "/project/types-loader.agda",
                [("Cubical.Data.Unit.Base", "tt*"), ("Demo", "private")],
                "agda",
            )
        self.assertEqual(result, {"Cubical.Data.Unit.Base": {"tt*": "Lift Unit"}})
        commands = run.call_args.args[0]
        self.assertIn("Cmd_infer_toplevel Simplified", commands)
        self.assertIn('"Cubical.Data.Unit.Base.tt*"', commands)
        self.assertIn("Cmd_compute_toplevel DefaultCompute", commands)


if __name__ == "__main__":
    unittest.main()
