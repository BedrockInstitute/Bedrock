import importlib.util
import os
from pathlib import Path
import tempfile
import textwrap
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "agda-parallel.py"
SPEC = importlib.util.spec_from_file_location("agda_parallel", SCRIPT)
agda_parallel = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(agda_parallel)


def module(*dependencies):
    imports = "\n".join(f"import {dependency}" for dependency in dependencies)
    return f"```agda\n{imports}\n```\n"


class ParallelAgdaTests(unittest.TestCase):
    def test_graph_uses_only_imports_in_agda_fences(self):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "src"
            src.mkdir()
            (src / "A.lagda.md").write_text(module())
            (src / "B.lagda.md").write_text(
                "import Ghost\n```text\nimport Ghost\n```\n" + module("A", "External.X"))
            _, graph = agda_parallel.local_graph(src)
            self.assertEqual(graph, {"A": set(), "B": {"A"}})

    def test_parallel_scheduler_respects_dependencies_and_merges_traces(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            src = root / "src"
            src.mkdir()
            for name, dependencies in {
                "A": ("External.X",), "B": ("A",), "C": ("A",),
                "Root": ("B", "C")
            }.items():
                (src / f"{name}.lagda.md").write_text(module(*dependencies))

            fake = root / "fake-agda.py"
            fake.write_text(textwrap.dedent("""\
                #!/usr/bin/env python3
                import json, os
                from pathlib import Path
                import sys, time

                source = Path(sys.argv[-1])
                state = Path(os.environ['FAKE_AGDA_STATE'])
                state.mkdir(exist_ok=True)
                if source.suffix == '.agda':
                    (state / 'external').write_text(source.read_text())
                    raise SystemExit(0)
                if not (state / 'external').exists():
                    raise SystemExit(5)
                name = source.name.removesuffix('.lagda.md')
                dependencies = {'A': [], 'B': ['A'], 'C': ['A'], 'Root': ['B', 'C']}
                if any(not (state / dependency).exists() for dependency in dependencies[name]):
                    raise SystemExit(3)
                if name in {'B', 'C'}:
                    (state / f'ready-{name}').touch()
                    peer = state / ('ready-C' if name == 'B' else 'ready-B')
                    deadline = time.monotonic() + 2
                    while not peer.exists() and time.monotonic() < deadline:
                        time.sleep(0.01)
                    if not peer.exists():
                        raise SystemExit(4)
                (state / name).touch()
                trace = os.environ.get('BEDROCK_AGDA_TYPES')
                if trace:
                    Path(trace).write_text(json.dumps({'module': name}) + '\\n')
                """))
            fake.chmod(0o755)
            trace_dir = root / "trace-parts"
            trace_dir.mkdir()
            old_state = os.environ.get("FAKE_AGDA_STATE")
            os.environ["FAKE_AGDA_STATE"] = str(root / "state")
            try:
                completed = agda_parallel.parallel_check(
                    project_root=root,
                    source_root=src,
                    root="Root",
                    agda=fake,
                    jobs=2,
                    trace_dir=trace_dir,
                )
            finally:
                if old_state is None:
                    os.environ.pop("FAKE_AGDA_STATE", None)
                else:
                    os.environ["FAKE_AGDA_STATE"] = old_state

            self.assertEqual(set(completed), {"A", "B", "C", "Root"})
            self.assertIn(
                "import External.X", (root / "state" / "external").read_text()
            )
            self.assertLess(completed.index("A"), completed.index("B"))
            self.assertLess(completed.index("A"), completed.index("C"))
            self.assertEqual(completed[-1], "Root")
            output = root / "trace.jsonl"
            agda_parallel.merge_traces(trace_dir, output)
            self.assertEqual(len(output.read_text().splitlines()), 4)

    def test_cycle_is_rejected_before_any_process_starts(self):
        with self.assertRaisesRegex(ValueError, "A -> B -> A"):
            agda_parallel.closure({"A": {"B"}, "B": {"A"}}, "A")

    def test_incremental_schedule_includes_only_stale_modules_and_dependants(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "src"
            interfaces = root / "interfaces"
            source.mkdir()
            interfaces.mkdir()
            graph = {"A": set(), "B": {"A"}, "C": {"A"},
                     "Root": {"B", "C"}}
            paths = {}
            for name in graph:
                paths[name] = source / f"{name}.lagda.md"
                paths[name].write_text(module(*graph[name]))
                interface = interfaces / f"{name}.agdai"
                interface.touch()
                os.utime(paths[name], ns=(1_000_000_000, 1_000_000_000))
                os.utime(interface, ns=(2_000_000_000, 2_000_000_000))
            modules = set(graph)
            self.assertEqual(agda_parallel.stale_modules(paths, graph, modules, interfaces), set())
            os.utime(paths["B"], ns=(3_000_000_000, 3_000_000_000))
            self.assertEqual(agda_parallel.stale_modules(paths, graph, modules, interfaces),
                             {"B", "Root"})
            os.utime(interfaces / "B.agdai", ns=(4_000_000_000, 4_000_000_000))
            self.assertEqual(agda_parallel.stale_modules(paths, graph, modules, interfaces),
                             {"Root"})

    def test_incremental_trace_preserves_old_records_and_appends_html_last(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            parts = root / "parts"
            parts.mkdir()
            output = root / "types.jsonl"
            output.write_text("old\n")
            (parts / "B.jsonl").write_text("module\n")
            html = parts / "html.jsonl"
            html.write_text("html\n")
            agda_parallel.merge_traces(parts, output, preserve_existing=True,
                                       final_trace=html)
            self.assertEqual(output.read_text(), "old\nmodule\nhtml\n")


if __name__ == "__main__":
    unittest.main()
