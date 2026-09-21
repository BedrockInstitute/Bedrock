import importlib.util
import json
import re
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


renderer = load("bedrock_expression_renderer", "site/render-site.py")
extractor = load("bedrock_expression_extractor", "site/extract-expression-types.py")


class ExpressionHoverTests(unittest.TestCase):
    def run_gesture_scenario(self, scenario):
        javascript = (ROOT / "site" / "static" / "bedrock.js").read_text()
        helper = re.search(
            r"    function gestureCandidates\(items, base, deltaX\) \{.*?"
            r"(?=    function applyLevelGesture)", javascript, re.DOTALL)
        self.assertIsNotNone(helper)
        completed = subprocess.run(
            [shutil.which("node"), "-e", helper.group(0) + scenario],
            check=True, capture_output=True, text=True, timeout=5)
        return json.loads(completed.stdout)

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_mobile_gesture_candidates_follow_expression_boundaries(self):
        scenario = r'''
var options = [
  {kind: "expression", source: "subst ⟨_⟩ (invEq (congEquiv e) q)", start: 80, end: 115},
  {kind: "expression", source: "invEq (congEquiv e) q", start: 90, end: 114},
  {kind: "expression", source: "congEquiv e", start: 100, end: 111},
  {kind: "expression", source: "subst ⟨_⟩ (invEq (congEquiv e) q) _", start: 80, end: 117},
  {kind: "expression", source: "invEq (congEquiv e)", start: 90, end: 112}
];
var base = {kind: "name", source: "congEquiv", start: 100, end: 109};
console.log(JSON.stringify({
  right: gestureCandidates(options, base, 40).map(function (item) { return item.source; }),
  left: gestureCandidates(options, base, -40).map(function (item) { return item.source; })
}));
'''
        self.assertEqual(self.run_gesture_scenario(scenario), {
            "right": [
                "congEquiv e",
                "invEq (congEquiv e)",
                "invEq (congEquiv e) q",
                "subst ⟨_⟩ (invEq (congEquiv e) q)",
                "subst ⟨_⟩ (invEq (congEquiv e) q) _",
            ],
            "left": [
                "invEq (congEquiv e) q",
                "subst ⟨_⟩ (invEq (congEquiv e) q) _",
            ],
        })

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_mobile_gesture_candidates_use_each_distinct_boundary_once(self):
        scenario = r'''
var options = [
  {kind: "expression", source: "root partial", start: 70, end: 118},
  {kind: "expression", source: "far blocked", start: 80, end: 114},
  {kind: "expression", source: "focus a", start: 100, end: 110},
  {kind: "expression", source: "near partial", start: 90, end: 113},
  {kind: "expression", source: "far partial", start: 80, end: 116},
  {kind: "expression", source: "focus a duplicate", start: 100, end: 110},
  {kind: "expression", source: "root full", start: 70, end: 120},
  {kind: "expression", source: "near full", start: 90, end: 115},
  {kind: "expression", source: "focus a b", start: 100, end: 112},
  {kind: "expression", source: "far full", start: 80, end: 118}
];
var base = {kind: "name", source: "focus", start: 100, end: 105};
function spans(deltaX) {
  return gestureCandidates(options, base, deltaX).map(function (item) {
    return [item.start, item.end];
  });
}
console.log(JSON.stringify({right: spans(40), left: spans(-40)}));
'''
        self.assertEqual(self.run_gesture_scenario(scenario), {
            "right": [
                [100, 110],
                [100, 112],
                [90, 113],
                [90, 115],
                [80, 116],
                [70, 118],
                [70, 120],
            ],
            "left": [
                [90, 115],
                [80, 118],
                [70, 120],
            ],
        })

    def test_mobile_expression_interactions_keep_highlights_exclusive(self):
        javascript = (ROOT / "site" / "static" / "bedrock.js").read_text()
        stylesheet = (ROOT / "site" / "static" / "bedrock.css").read_text()
        self.assertIn('option.nameNode.classList.add("name-active")', javascript)
        self.assertIn('option.node.classList.add("expr-active")', javascript)
        self.assertNotIn('var activeOption = option.node ? option', javascript)
        self.assertIn('function choose(index, withHapticFeedback)', javascript)
        self.assertIn('function vibrateSelection()', javascript)
        self.assertIn('withHapticFeedback && previous !== option) vibrateSelection()', javascript)
        self.assertIn('if (usesInspector(event.target)) {\n        return;', javascript)
        self.assertIn('gesture.activated = true;\n        if (gesture.block) gesture.block.classList.add("ast-level-gesture");\n        vibrateSelection();', javascript)
        self.assertIn('if (event.type === "touchend") {\n          vibrateSelection();', javascript)
        self.assertIn('choose(options.indexOf(next), true)', javascript)
        self.assertIn('zh: "按住色块左右滑动以切换AST节点"', javascript)
        self.assertIn('function setRangeBlock(block)', javascript)
        self.assertIn('swipeHint.hidden = !(compactPointer.matches && rangeBlock);', javascript)
        self.assertIn('if (rangeCapableBlock && setRangeBlock(rangeCapableBlock)) pinned = true;',
                      javascript)
        self.assertIn('if (compactBlock && setRangeBlock(compactBlock)) pinned = true;',
                      javascript)
        self.assertIn('else if (!touched && !popup.contains(event.target)', javascript)
        self.assertIn('if (codeBlock && !rangeCapableBlock) {', javascript)
        self.assertIn('function gestureCandidates(items, base, deltaX)', javascript)
        self.assertIn('var chain = [];', javascript)
        self.assertIn('item.start <= current.start && item.end >= current.end', javascript)
        self.assertIn('var boundary = movingRight ? item.end : item.start;', javascript)
        self.assertIn('if (levelGesture.released) clearLevelGesture();', javascript)
        self.assertIn('var continuesActiveBlock = block && block === rangeBlock && options.length;',
                      javascript)
        self.assertIn('if (!continuesActiveBlock && !touchesExpression) return;',
                      javascript)
        self.assertIn('if (gesture.block === rangeBlock && options.length)', javascript)
        self.assertIn('if (gesture.touchesExpression) {\n          show(gesture.target);', javascript)
        self.assertIn('.ast-swipe-hint { position: fixed;', stylesheet)
        self.assertIn('min-height: 3.75rem;', stylesheet)
        self.assertIn('font: 700 1rem/1.35 var(--sans);', stylesheet)
        self.assertNotIn('.hover-popup.has-definition-link { min-height:', stylesheet)
        self.assertIn('top: 0; right: .25rem; bottom: 0; display: grid;', stylesheet)
        self.assertIn('pre.Agda .expr-node, pre.Agda .expr-node * {', stylesheet)
        self.assertIn('user-select: none; -webkit-user-select: none;', stylesheet)
        self.assertIn('document.addEventListener("selectstart"', javascript)
        self.assertIn('if (expression) event.preventDefault()', javascript)

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

    def test_renamed_import_is_indexed_as_a_definition(self):
        block = ('<a id="10" class="Symbol">to</a> '
                 '<a id="13" class="Function">map₁</a>')
        names, aspects = {}, {}
        renderer.index_definitions(block, "Demo", names, aspects)
        self.assertEqual(names, {"Demo": {"map₁": "13"}})
        self.assertEqual(aspects, {"Demo": {"13": "Function"}})

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

    def test_checked_local_signature_supplies_missing_name_type(self):
        block = ('<pre class="Agda">  '
                 '<a id="40" href="Demo.html#40" class="Function">local</a> '
                 '<a id="46" class="Symbol">:</a> '
                 '<a id="48" href="Demo.html#10" class="Function">A</a> '
                 '<a id="50" class="Symbol">→</a> '
                 '<a id="52" href="Demo.html#20" class="Function">B</a>\n'
                 '  <a id="60" href="Demo.html#60" class="Bound">x</a> '
                 '<a id="62" class="Symbol">:</a> ignored\n</pre>')
        types = renderer.local_signature_types(block, "Demo")
        self.assertEqual(set(types), {"40"})
        self.assertEqual(types["40"]["name"], "local")
        self.assertNotIn('id="', types["40"]["type"])
        self.assertIn('href="Demo.html#10"', types["40"]["type"])
        self.assertIn('A</a> <a class="Symbol">→</a>', types["40"]["type"])

    def test_shared_local_signature_supplies_every_name(self):
        block = ('<pre class="Agda">  '
                 '<a id="40" href="Demo.html#40" class="Function">A</a> '
                 '<a id="42" href="Demo.html#42" class="Function">P</a> '
                 '<a id="44" class="Symbol">:</a> '
                 '<a id="46" href="Demo.html#10" class="Datatype">V</a>\n</pre>')
        types = renderer.local_signature_types(block, "Demo")
        self.assertEqual(set(types), {"40", "42"})
        self.assertEqual(types["40"]["type"], types["42"]["type"])

    def test_selected_preview_finds_referenced_type_sidecars(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Demo.md"
            path.write_text('<a href="Library.One.html#10">x</a>'
                            '<a href="Missing.html#20">y</a>')
            referenced = renderer.referenced_type_modules(
                path, {"Demo", "Library.One"}
            )
        self.assertEqual(referenced, {"Library.One"})

    def test_type_rendering_preserves_disambiguated_level_binders(self):
        rendered = renderer.render_type(
            "{A.ℓ : Agda.Primitive.Level} {B.ℓ : Agda.Primitive.Level} → Set A.ℓ",
            {},
        )
        self.assertEqual(
            rendered,
            "{A.ℓ : Level} {B.ℓ : Level} → Type A.ℓ",
        )

    def test_type_links_reuse_agda_syntax_aspects(self):
        rendered = renderer.render_type(
            "Demo.f",
            {"Demo.f": ("Demo", "10")},
            renderer.qualified_name_pattern({"Demo.f": ("Demo", "10")}),
            {"Demo": {"10": "Function"}},
        )
        self.assertEqual(
            rendered,
            '<a href="Demo.html#10" class="Function">f</a>',
        )

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

    def test_application_range_absorbs_its_closing_parenthesis(self):
        source = "f (g x) y"
        start = source.index("f") + 1
        before_close = source.index(")") + 1
        self.assertEqual(
            extractor.include_closing_parentheses(source, start, before_close),
            before_close + 1,
        )

    def test_closing_parenthesis_deduplicates_the_same_application(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            src = root / "src"
            html_dir = root / "html"
            src.mkdir()
            html_dir.mkdir()
            source = "module Demo where\n\n```agda\nf x = h (g x)\n```\n"
            path = src / "Demo.lagda.md"
            path.write_text(source)
            start = source.index("h (g x") + 1
            before_close = source.index(")", start - 1) + 1
            (html_dir / "Demo.md").write_text("")
            trace = root / "trace.jsonl"
            base = {
                "version": 1, "run": "one", "kind": "application",
                "path": str(path.resolve()),
                "sourceHash": extractor.source_hash(path), "start": start,
                "type": "A",
            }
            trace.write_text("".join(json.dumps(item) + "\n" for item in [
                {**base, "end": before_close},
                {**base, "end": before_close + 1},
            ]))
            data, _ = extractor.normalize(src.resolve(), html_dir.resolve(), trace)
        applications = [node for node in data["Demo"] if node["kind"] == "application"]
        self.assertEqual(len(applications), 1)
        self.assertEqual(applications[0]["source"], "h (g x)")

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

    def test_name_trace_supplies_definition_target_type(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            src, html_dir = root / "src", root / "html"
            src.mkdir(); html_dir.mkdir()
            source = "module Demo where\n\n```agda\nf = f\n```\n"
            path = src / "Demo.lagda.md"
            path.write_text(source)
            start = source.index("f =") + 1
            (html_dir / "Demo.md").write_text(
                f'<a id="{start}" href="Demo.html#{start}" class="Function">f</a>'
            )
            trace = root / "trace.jsonl"
            trace.write_text(json.dumps({
                "version": 1, "run": "one", "kind": "name",
                "path": str(path.resolve()), "sourceHash": extractor.source_hash(path),
                "start": start, "end": start + 1, "type": "A",
            }) + "\n")
            data, _ = extractor.normalize(src.resolve(), html_dir.resolve(), trace)
        self.assertEqual(data["Demo"][0]["kind"], "definition")
        self.assertEqual(data["Demo"][0]["target"], start)

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
