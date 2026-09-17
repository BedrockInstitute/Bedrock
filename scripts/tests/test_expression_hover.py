import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


renderer = load("bedrock_expression_renderer", "site/render-site.py")
extractor = load("bedrock_expression_extractor", "site/extract-expression-types.py")


class ExpressionHoverTests(unittest.TestCase):
    def test_nested_source_ranges_wrap_highlighted_tokens(self):
        block = ('<pre class="Agda"><a id="10">f</a> '
                 '<a id="12">g</a> <a id="14">x</a></pre>')
        nodes = [
            {"id": 1, "start": 10, "end": 15, "type": "T", "source": "f g x"},
            {"id": 2, "start": 12, "end": 15, "type": "U", "source": "g x"},
        ]
        rendered = renderer.annotate_expression_nodes(block, nodes)
        self.assertIn('<span class="expr-node" data-expr-id="1"', rendered)
        self.assertIn('<span class="expr-node" data-expr-id="2"', rendered)
        self.assertLess(rendered.index('data-expr-id="1"'), rendered.index('data-expr-id="2"'))
        self.assertIn('<a id="14">x</a></span></span>', rendered)

    def test_unmatched_ranges_are_not_rendered(self):
        block = '<pre class="Agda"><a id="10">f</a></pre>'
        node = {"id": 1, "start": 10, "end": 99, "type": "T", "source": "f"}
        self.assertEqual(renderer.annotate_expression_nodes(block, [node]), block)

    def test_unlinked_bound_token_gets_its_occurrence_type(self):
        block = '<pre class="Agda"><a id="10" class="Bound">x</a></pre>'
        rendered = renderer.annotate_unlinked_bound_types(block, "Demo", {"10": "A"})
        self.assertIn('data-type="Demo#10"', rendered)

    def test_mixfix_hover_uses_canonical_definition_name(self):
        names = {"Base.Prelude": {"⟨_⟩isProp": "39997"}}
        self.assertEqual(renderer.names_by_position("Base.Prelude", names),
                         {"39997": "⟨_⟩isProp"})

    def test_mixfix_reference_carries_its_canonical_name(self):
        body = ('<a id="20" href="Cubical.Foundations.Structure.html#1134" '
                'class="Function Operator">⟨</a>')
        rendered = renderer.rewrite_links(
            body,
            {"Cubical.Foundations.Structure"},
            {"Cubical.Foundations.Structure": {"1134": "Type"}},
            {"Cubical.Foundations.Structure": {"1134": "⟨_⟩"}},
        )
        self.assertIn('data-name="⟨_⟩"', rendered)

    def test_boundary_inside_highlight_token_is_split(self):
        block = ('<pre class="Agda"><a id="10">f</a> '
                 '<a id="12" class="Symbol">_))</a></pre>')
        nodes = [{"id": 1, "start": 10, "end": 14,
                  "type": "T", "source": "f _)"}]
        rendered = renderer.annotate_expression_nodes(block, nodes)
        self.assertIn('<a id="12" class="Symbol">_)</a></span>', rendered)
        self.assertIn('<a id="14" class="Symbol">)</a>', rendered)

    def test_latest_trace_run_replaces_older_records_per_module(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = (root / "Demo.lagda.md").resolve()
            path.write_text("module Demo where\n")
            trace = root / "trace.jsonl"
            records = [
                {"version": 1, "run": "old", "kind": "name", "path": str(path),
                 "sourceHash": extractor.source_hash(path),
                 "start": 1, "end": 2, "type": "Old"},
                {"version": 1, "run": "new", "kind": "name", "path": str(path),
                 "sourceHash": extractor.source_hash(path),
                 "start": 1, "end": 2, "type": "New"},
            ]
            trace.write_text("".join(json.dumps(item) + "\n" for item in records))
            latest = extractor.read_latest_trace(trace, {path})
        self.assertEqual([item["type"] for item in latest[path]], ["New"])

    def test_precise_application_record_wins_over_meta_type(self):
        old = {"kind": "application", "type": "_42"}
        new = {"kind": "application", "type": "A"}
        self.assertIs(extractor.prefer_record(old, new), new)
        self.assertTrue(extractor.imprecise_type("_42"))
        self.assertFalse(extractor.imprecise_type("⟨_⟩isProp P"))

    def test_trace_normalization_maps_bindings_and_applications(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            src = root / "src"
            html_dir = root / "html"
            src.mkdir()
            html_dir.mkdir()
            source = "module Demo where\n\n```agda\nf x = g x\n```\n"
            path = src / "Demo.lagda.md"
            path.write_text(source)
            binder = source.index("x =") + 1
            use = source.rindex("x") + 1
            app = source.index("g x") + 1
            (html_dir / "Demo.md").write_text(
                f'<a id="{binder}" class="Bound">x</a>'
                f'<a id="{use}" href="Demo.html#{binder}" class="Bound">x</a>'
            )
            trace = root / "trace.jsonl"
            records = [
                {"version": 1, "run": "one", "kind": "binding", "path": str(path),
                 "sourceHash": extractor.source_hash(path),
                 "start": binder, "end": binder + 1, "type": "A"},
                {"version": 1, "run": "one", "kind": "application", "path": str(path),
                 "sourceHash": extractor.source_hash(path),
                 "start": app, "end": app + 3, "type": "A"},
            ]
            trace.write_text("".join(json.dumps(item) + "\n" for item in records))
            data, compact = extractor.normalize(src.resolve(), html_dir.resolve(), trace)
        kinds = {node["kind"] for node in data["Demo"]}
        self.assertEqual(kinds, {"binding", "variable", "application"})
        application = next(node for node in data["Demo"] if node["kind"] == "application")
        self.assertEqual(application["source"], "g x")
        self.assertEqual(len(compact), 2)

    def test_empty_module_needs_no_type_records(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            src = root / "src"
            html_dir = root / "html"
            src.mkdir()
            html_dir.mkdir()
            (src / "Demo.lagda.md").write_text("module Demo where\n")
            (html_dir / "Demo.md").write_text("")
            trace = root / "trace.jsonl"
            trace.write_text("")
            data, compact = extractor.normalize(src.resolve(), html_dir.resolve(), trace)
            self.assertEqual(data, {"Demo": []})
            self.assertEqual(compact, [])

    def test_atomic_json_and_trace_compaction_round_trip_unicode(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "types.json"
            trace = root / "trace.jsonl"
            data = {"Demo": [{"source": "Ω", "type": "hProp ℓ"}]}
            records = [{"version": 1, "run": "一", "kind": "name", "path": "/x",
                        "sourceHash": "abc", "start": 1, "end": 2, "type": "Ω"}]
            extractor.write_json_atomic(output, data)
            extractor.compact_trace(trace, records)
            self.assertEqual(json.loads(output.read_text()), data)
            self.assertEqual(json.loads(trace.read_text()), records[0])
            self.assertFalse(output.with_name("types.json.tmp").exists())


if __name__ == "__main__":
    unittest.main()
