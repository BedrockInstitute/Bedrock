import importlib.util
import inspect
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
    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_mobile_expression_links_keep_definition_action_without_type_data(self):
        javascript = (ROOT / "site" / "static" / "bedrock.js").read_text()
        helper = re.search(
            r"    function show\(target\) \{.*?(?=    function hide\(\))",
            javascript.split("  function initHover() {", 1)[1], re.DOTALL)
        self.assertIsNotNone(helper)
        scenario = r'''
var compactPointer = {matches: true};
var cfg = {chapter: "Demo"};
var request = 0;
var levelGesture = null;
var hideName = function () {};
var cancelHide = function () {};
var escapedCodeName = function (name) { return name; };
var fetchTypes = function () { return Promise.resolve({}); };
var expressionOptions = function () { return []; };
var results = [];
var render = function (items, target, preferred) {
  results.push({href: preferred.href, source: preferred.source});
};
function target(type, href) {
  var link = {
    id: "10", textContent: "mapDec", href: href,
    getAttribute: function (key) { return key === "data-type" ? type : null; },
    hasAttribute: function (key) { return key === "href" && !!href; }
  };
  return {
    isConnected: true,
    closest: function (selector) {
      if (selector === "a[data-type]") return type ? link : null;
      if (selector === "a[href]") return href ? link : null;
      if (selector === ".expr-node") return {};
      return null;
    }
  };
}
(async function () {
  show(target(null, "Base.Prelude.html#43"));
  await new Promise(setImmediate);
  show(target("Base.Prelude#43", "Base.Prelude.html#43"));
  await new Promise(setImmediate);
  show(target(null, null));
  await new Promise(setImmediate);
  console.log(JSON.stringify(results));
})();
'''
        completed = subprocess.run(
            [shutil.which("node"), "-e", helper.group(0) + scenario],
            capture_output=True, text=True, timeout=5)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(json.loads(completed.stdout), [
            {"href": "Base.Prelude.html#43", "source": "mapDec"},
            {"href": "Base.Prelude.html#43", "source": "mapDec"},
        ])

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_mobile_inline_link_keeps_definition_action_without_type_data(self):
        javascript = (ROOT / "site" / "static" / "bedrock.js").read_text()
        helper = re.search(
            r"    function showName\(name\) \{.*?(?=    var popup = document.createElement)",
            javascript.split("  function initHover() {", 1)[1], re.DOTALL)
        self.assertIsNotNone(helper)
        scenario = r'''
var compactPointer = {matches: true};
var nameRequest = 0, namePopups = [];
var levelGesture = null;
var clearLeafNameHighlight = function () {};
var hoverIdentity = function (name) { return name.getAttribute("data-type"); };
var markTerminalHoverStops = function () {};
var isUniverseFormerSignature = function () { return false; };
var isTerminalPrimitiveSortText = function () { return false; };
var namePopupEntry = function () { return null; };
var removeNamePopupsFrom = function () {};
var cancelNameClose = function () {};
var positionNameEntry = function () {};
var rangeCapableScope = function () { return null; };
var setRangeScope = function () {};
var isUniverseTypeText = function () { return false; };
var fetchTypes = function () { return Promise.resolve({}); };
var definitionAction = function (href, name) { return {href: href, name: name}; };
var document = {
  createElement: function () {
    return {children: [], dataset: {}, isConnected: true,
      classList: {add: function () {}},
      setAttribute: function () {},
      appendChild: function (child) { this.children.push(child); },
      addEventListener: function () {}};
  },
  body: {appendChild: function () {}}
};
var link = {
  href: "Base.Prelude.html#43", textContent: "mapDec", isConnected: true,
  classList: {contains: function () { return false; }},
  getAttribute: function () { return null; },
  hasAttribute: function (key) { return key === "href"; }
};
showName(link);
setImmediate(function () {
  var namePopup = namePopups[0].popup;
  var ordinary = {
    label: namePopup.children[0].textContent,
    href: namePopup.children[1].href,
    name: namePopup.children[1].name
  };
  var primitive = {
    href: "Agda.Primitive.html#388", textContent: "Type", isConnected: true,
    classList: {contains: function (name) { return name === "Primitive"; }},
    getAttribute: function (key) { return key === "data-name" ? "Set" : null; },
    hasAttribute: function (key) { return key === "href"; }
  };
  showName(primitive);
  setImmediate(function () {
    var typeLabel = namePopups[1].popup.children[0].textContent;
    var typeMarkup = Boolean(namePopups[1].popup.children[0].innerHTML);
    var levelUniv = {
      href: "Agda.Primitive.html#595", textContent: "LevelUniv", isConnected: true,
      classList: primitive.classList,
      getAttribute: function () { return null; },
      hasAttribute: primitive.hasAttribute
    };
    showName(levelUniv);
    setImmediate(function () {
      console.log(JSON.stringify({ordinary: ordinary, primitive: typeLabel,
        primitiveMarkup: typeMarkup,
        levelUniv: namePopups[2].popup.children[0].textContent,
        levelUnivMarkup: Boolean(namePopups[2].popup.children[0].innerHTML)}));
    });
  });
});
'''
        completed = subprocess.run(
            [shutil.which("node"), "-e", helper.group(0) + scenario],
            capture_output=True, text=True, timeout=5)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(json.loads(completed.stdout), {
            "ordinary": {"label": "mapDec", "href": "Base.Prelude.html#43",
                         "name": "mapDec"},
            "primitive": "Type", "primitiveMarkup": False,
            "levelUniv": "LevelUniv", "levelUnivMarkup": False,
        })

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

    def run_containing_expression_scenario(self, scenario):
        javascript = (ROOT / "site" / "static" / "bedrock.js").read_text()
        helper = re.search(
            r"    function containingExpressionData\(expressionData, start, end\) \{.*?"
            r"(?=    function expressionOptions)", javascript, re.DOTALL)
        self.assertIsNotNone(helper)
        completed = subprocess.run(
            [shutil.which("node"), "-e", helper.group(0) + scenario],
            check=True, capture_output=True, text=True, timeout=5)
        return json.loads(completed.stdout)

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_hover_type_gesture_switches_to_a_containing_node(self):
        javascript = (ROOT / "site" / "static" / "bedrock.js").read_text()
        helper = re.search(
            r"    function gestureIndex\(deltaX\) \{.*?"
            r"(?=    function setPopupWidth)", javascript, re.DOTALL)
        self.assertIsNotNone(helper)
        scenario = r'''
var events = [];
var inner = {id: "inner"}, outer = {id: "outer"};
var base = {kind: "expression", node: inner, start: 4, end: 8};
var parent = {kind: "expression", node: outer, start: 2, end: 10};
var levelGesture = {
  kind: "type", activated: true, baseOption: base, lastOption: base,
  items: [base, parent], deltaX: 20, released: false
};
var activateTypeGestureItem = function (item) {
  events.push(["active", item.node.id], ["hover", item.node.id]);
};
var vibrateSelection = function () { events.push(["vibrate"]); };
var clearLevelGesture = function () {};
var options = [], request = 0, renderedRequest = 0;
var selected = null;
var choose = function () {};
applyLevelGesture();
console.log(JSON.stringify(events));
'''
        completed = subprocess.run(
            [shutil.which("node"), "-e", helper.group(0) + scenario],
            check=True, capture_output=True, text=True, timeout=5)
        self.assertEqual(json.loads(completed.stdout), [
            ["active", "outer"], ["hover", "outer"], ["vibrate"],
        ])

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_hover_type_gesture_can_return_to_its_leaf_name(self):
        javascript = (ROOT / "site/static/bedrock.js").read_text()
        helper = re.search(
            r"    function gestureIndex\(deltaX\) \{.*?"
            r"(?=    function setPopupWidth)", javascript, re.DOTALL)
        self.assertIsNotNone(helper)
        scenario = r'''
var leaf = {kind: "name", node: {id: "b"}, start: 4, end: 5};
var inner = {kind: "expression", node: {id: "(b c)"}, start: 4, end: 9};
var outer = {kind: "expression", node: {id: "((b c) d)"}, start: 3, end: 12};
var seen = [];
var levelGesture = {kind: "type", activated: true, baseOption: leaf,
  lastOption: leaf, items: [leaf, inner, outer], deltaX: 20, released: false};
var activateTypeGestureItem = function (item) { seen.push(item.node.id); };
var vibrateSelection = function () {};
var clearLevelGesture = function () {};
var options = [], request = 0, renderedRequest = 0;
var selected = null, choose = function () {};
applyLevelGesture();
levelGesture.deltaX = 45;
applyLevelGesture();
levelGesture.deltaX = 0;
applyLevelGesture();
console.log(JSON.stringify(seen));
'''
        completed = subprocess.run(
            [shutil.which("node"), "-e", helper.group(0) + scenario],
            text=True, capture_output=True, check=True)
        self.assertEqual(json.loads(completed.stdout), ["(b c)", "((b c) d)", "b"])

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_hover_type_gesture_starts_at_the_touched_leaf(self):
        javascript = (ROOT / "site/static/bedrock.js").read_text()
        helper = re.search(
            r"    function typeGestureState\(target\) \{.*?\n    \}",
            javascript, re.DOTALL)
        self.assertIsNotNone(helper)
        scenario = r'''
var popup = {classList: {contains: function () { return false; }}};
var name = {textContent: "b", hasAttribute: function () { return false; }};
var value = {contains: function (node) { return node === name; },
  querySelectorAll: function () { return [direct, outer]; }};
var direct = {dataset: {exprStart: "4", exprEnd: "9"},
  hasAttribute: function () { return false; },
  closest: function (selector) { return selector === ".type-value" ? value : popup; }};
var outer = {dataset: {exprStart: "3", exprEnd: "12"}};
var target = {closest: function (selector) {
  return selector.includes("a[data-type]") ? name : direct;
}};
var document = {createRange: function () { return {
  setStart: function () {}, setEndBefore: function () {},
  toString: function () { return "a (("; }
}; }};
var state = typeGestureState(target);
console.log(JSON.stringify({kind: state.base.kind, start: state.base.start,
  end: state.base.end, parents: state.items.length}));
'''
        completed = subprocess.run(
            [shutil.which("node"), "-e", helper.group(0) + scenario],
            text=True, capture_output=True, check=True)
        self.assertEqual(json.loads(completed.stdout), {
            "kind": "name", "start": 4, "end": 5, "parents": 3,
        })

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_hover_type_node_switch_has_only_one_active_node_per_popup(self):
        javascript = (ROOT / "site" / "static" / "bedrock.js").read_text()
        helper = re.search(
            r"    function activateTypeNode\(target\) \{.*?\n    \}",
            javascript, re.DOTALL)
        self.assertIsNotNone(helper)
        scenario = r'''
function classes(initial) {
  var values = new Set(initial || []);
  return {
    add: function (value) { values.add(value); },
    remove: function (value) { values.delete(value); },
    contains: function (value) { return values.has(value); }
  };
}
var oldNode = {classList: classes(["type-active"])};
var newNode = {classList: classes()};
var shell = {querySelectorAll: function () { return [oldNode, newNode]; }};
newNode.closest = function (selector) {
  return selector === ".type-value .type-node" ? newNode : shell;
};
activateTypeNode(newNode);
console.log(JSON.stringify({
  oldActive: oldNode.classList.contains("type-active"),
  newActive: newNode.classList.contains("type-active")
}));
'''
        completed = subprocess.run(
            [shutil.which("node"), "-e", helper.group(0) + scenario],
            check=True, capture_output=True, text=True, timeout=5)
        self.assertEqual(json.loads(completed.stdout), {
            "oldActive": False, "newActive": True,
        })
        self.assertNotIn(
            'entry.activeNode && !entry.activeNode.matches(":hover")',
            javascript,
        )

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_mobile_hover_never_schedules_or_inherits_an_auto_close(self):
        javascript = (ROOT / "site" / "static" / "bedrock.js").read_text()
        helper = re.search(
            r"    function scheduleHoverClose\(callback\) \{.*?"
            r"(?=    var namePopups)", javascript, re.DOTALL)
        self.assertIsNotNone(helper)
        scenario = r'''
var timers = [], calls = 0;
var compactPointer = {matches: true};
var hoverCloseDelay = 360;
var window = {setTimeout: function (callback) {
  timers.push(callback);
  return timers.length;
}};
var first = scheduleHoverClose(function () { calls++; });
compactPointer.matches = false;
scheduleHoverClose(function () { calls++; });
compactPointer.matches = true;
timers[0]();
compactPointer.matches = false;
scheduleHoverClose(function () { calls++; });
timers[1]();
console.log(JSON.stringify({first: first, timers: timers.length, calls: calls}));
'''
        completed = subprocess.run(
            [shutil.which("node"), "-e", helper.group(0) + scenario],
            check=True, capture_output=True, text=True, timeout=5)
        self.assertEqual(json.loads(completed.stdout), {
            "first": None, "timers": 2, "calls": 1,
        })

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_universe_type_is_a_semantic_hover_terminal(self):
        javascript = (ROOT / "site" / "static" / "bedrock.js").read_text()
        helper = re.search(
            r"  function isUniverseTypeText\(text\) \{.*?\n  \}",
            javascript,
            re.DOTALL,
        )
        self.assertIsNotNone(helper)
        scenario = r'''
var samples = [
  "Type", "Type ℓ", "Type (ℓ-suc ℓ)", "Type (ℓ ⊔ ℓ')", "Typeω", "Type₀",
  "Type ℓ → Type ℓ", "(A : Type ℓ) → Type ℓ", "TypeWithStr ℓ",
  "Type ℓ × Type ℓ"
];
console.log(JSON.stringify(samples.map(isUniverseTypeText)));
'''
        completed = subprocess.run(
            [shutil.which("node"), "-e", helper.group(0) + scenario],
            check=True, capture_output=True, text=True, timeout=5)
        self.assertEqual(json.loads(completed.stdout), [
            True, True, True, True, True, True,
            False, False, False, False,
        ])
        self.assertNotIn(
            'candidate.closest(".hover-popup.hover-terminal .type-value")',
            javascript,
        )
        self.assertIn(
            'popup.classList.toggle("hover-terminal", '
            'isUniverseTypeText(value.textContent))',
            javascript,
        )
        self.assertIn(
            'if (isUniverseTypeText(nameValue.textContent))',
            javascript,
        )
        self.assertIn('leafActiveName.classList.add("name-active")', javascript)
        self.assertIn('return entry.identity === identity;', javascript)
        self.assertIn('markTerminalHoverStops(nameValue, identity);', javascript)
        self.assertNotIn(
            'if (html && isUniverseFormerSignature(nameValue.textContent))',
            javascript,
        )
        self.assertIn(
            'markTerminalHoverStops(value, hoverIdentity(anchor));',
            javascript,
        )
        self.assertIn(
            'name.getAttribute("data-hover-stop")',
            javascript,
        )
        self.assertIn(
            'if (codeBlock && !rangeCapableBlock && !target)',
            javascript,
        )
        self.assertIn('node.replaceWith.apply(node, Array.from(node.childNodes));', javascript)
        self.assertNotIn('activateTypeNode(name);', javascript)
        stylesheet = (ROOT / "site" / "static" / "bedrock.css").read_text()
        self.assertNotIn(
            '.hover-popup.hover-terminal .type-value :is(a[href], .type-node)',
            stylesheet,
        )

    def test_primitive_sorts_are_shared_hover_terminals(self):
        internal = {
            "Agda.Primitive.LevelUniv": ("Agda.Primitive", "595"),
        }
        rendered = renderer.render_type(
            "Agda.Primitive.LevelUniv", internal,
            renderer.qualified_name_pattern(internal),
            {"Agda.Primitive": {"595": "Primitive"}}, "Demo",
        )
        self.assertIn('data-hover-stop="primitive-sort"', rendered)
        self.assertNotIn('data-type=', rendered)

    def test_universe_former_signature_always_stops_its_type_leaf(self):
        internal = {
            "Base.Prelude.Level": ("Base.Prelude", "10104"),
            "Base.Prelude.Type": ("Base.Prelude", "10098"),
        }
        rendered = renderer.render_type(
            "(ℓ : Base.Prelude.Level) → Base.Prelude.Type ℓ", internal,
            renderer.qualified_name_pattern(internal),
            {"Base.Prelude": {"10104": "Primitive", "10098": "Primitive"}},
            "Base.Prelude",
        )
        self.assertRegex(
            rendered,
            r'data-type="Base\.Prelude#10098" '
            r'data-hover-stop="universe-former"[^>]*>Type</a>',
        )
        self.assertNotRegex(
            rendered,
            r'data-name="Level"[^>]*data-hover-stop=',
        )
        self.assertTrue(renderer.is_universe_former_signature(
            "(x : Level) → Type x"
        ))
        self.assertFalse(renderer.is_universe_former_signature(
            "(x : Level) → Type (ℓ-suc x)"
        ))

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

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_multiline_gesture_recovers_logical_ancestors_from_source_ranges(self):
        scenario = r'''
var expressionData = {
  333: {source: "mapDec ... (lem ...)", start: 10, end: 100},
  332: {source: "mapDec ...", start: 10, end: 40},
  341: {source: "lem ...", start: 50, end: 99},
  344: {source: "Lift P , proof", start: 55, end: 98}
};
console.log(JSON.stringify(
  containingExpressionData(expressionData, 50, 99).map(function (entry) {
    return [entry.id, entry.data.start, entry.data.end];
  })
));
'''
        self.assertEqual(self.run_containing_expression_scenario(scenario), [
            ["333", 10, 100],
            ["341", 50, 99],
        ])

    def test_mobile_expression_interactions_keep_highlights_exclusive(self):
        javascript = (ROOT / "site" / "static" / "bedrock.js").read_text()
        stylesheet = (ROOT / "site" / "static" / "bedrock.css").read_text()
        self.assertIn('option.nameNode.classList.add("name-active")', javascript)
        self.assertIn('node.classList.add("expr-active")', javascript)
        self.assertIn('node.dataset.exprId === expressionId', javascript)
        self.assertNotIn('var activeOption = option.node ? option', javascript)
        self.assertIn('function choose(index, withHapticFeedback)', javascript)
        self.assertIn('function vibrateSelection()', javascript)
        self.assertIn('withHapticFeedback && previous !== option) vibrateSelection()', javascript)
        self.assertIn('if (usesInspector(event.target)) {\n        return;', javascript)
        self.assertIn('gesture.activated = true;\n        if (gesture.scope) gesture.scope.classList.add("ast-level-gesture");\n        vibrateSelection();', javascript)
        self.assertIn('if (event.type === "touchend" && gesture.kind === "source") {\n          vibrateSelection();', javascript)
        self.assertIn('choose(options.indexOf(next), true)', javascript)
        self.assertIn('zh: "按住色块左右滑动以切换AST节点"', javascript)
        self.assertIn('function setRangeScope(scope)', javascript)
        self.assertIn('swipeHint.hidden = !(compactPointer.matches && rangeScope);', javascript)
        self.assertIn('if (rangeCapableBlock && setRangeScope(rangeCapableBlock)) pinned = true;',
                      javascript)
        self.assertIn('if (compactBlock && setRangeScope(compactBlock)) pinned = true;',
                      javascript)
        self.assertIn(
            'else if (!touched && !activeHoverChainContains(event.target))',
            javascript,
        )
        self.assertIn('if (codeBlock && !rangeCapableBlock && !target) {', javascript)
        self.assertIn('function gestureCandidates(items, base, deltaX)', javascript)
        self.assertIn('function containingExpressionData(expressionData, start, end)', javascript)
        self.assertIn('var items = expressionOptions(expressionData, directNode);', javascript)
        self.assertIn('var chain = [];', javascript)
        self.assertIn('item.start <= current.start && item.end >= current.end', javascript)
        self.assertIn('var boundary = movingRight ? item.end : item.start;', javascript)
        self.assertIn('if (levelGesture.released) clearLevelGesture();', javascript)
        self.assertIn('var continuesActiveBlock = block && block === rangeScope && options.length;',
                      javascript)
        self.assertIn(
            'if (!continuesActiveBlock && !touchesExpression && !typeGesture) return;',
            javascript,
        )
        self.assertIn('if (gesture.block === rangeScope && options.length)', javascript)
        self.assertIn('if (gesture.touchesExpression) {\n          show(gesture.target);', javascript)
        self.assertIn('.ast-swipe-hint { position: fixed;', stylesheet)
        self.assertIn('min-height: 3.75rem;', stylesheet)
        self.assertIn('font: 700 1rem/1.35 var(--sans);', stylesheet)
        self.assertNotIn('.hover-popup.has-definition-link { min-height:', stylesheet)
        self.assertIn('top: 0; right: .25rem; bottom: 0; display: grid;', stylesheet)
        self.assertIn('en: "Open definition in a modal"', javascript)
        self.assertIn('zh: "在弹窗中打开定义"', javascript)
        self.assertIn('ja: "モーダルで定義を開く"', javascript)
        self.assertIn('var definitionActionIcon =', javascript)
        self.assertEqual(javascript.count('innerHTML = definitionActionIcon;'), 2)
        self.assertIn('function definitionAction(href, name, isModule)', javascript)
        self.assertIn('if (name) link.setAttribute("data-name", name);', javascript)
        self.assertIn('definitionLink.setAttribute("data-name", option.source);', javascript)
        self.assertIn('definitionLink.removeAttribute("data-name");', javascript)
        self.assertIn('<rect x="7" y="11" width="10" height="6" rx="1"/>',
                      javascript)
        self.assertNotIn('M4 12h13m-5-5 5 5-5 5M20 5v14', javascript)
        self.assertIn('pre.Agda .expr-node, pre.Agda .expr-node *,', stylesheet)
        self.assertIn('user-select: none; -webkit-user-select: none;', stylesheet)
        self.assertIn('document.addEventListener("selectstart"', javascript)
        self.assertIn('if (expression) event.preventDefault()', javascript)
        self.assertIn('function typeGestureState(target)', javascript)
        self.assertIn('if (levelGesture.kind === "type") {', javascript)
        self.assertIn('activateTypeGestureItem(typeNext);', javascript)
        self.assertIn('setRangeScope(typeGesture.scope);', javascript)
        self.assertIn(
            '.hover-popup.ast-ranges-visible .type-value '
            '.type-node:not([data-single-name]) {',
            stylesheet,
        )
        self.assertIn('function scheduleHoverClose(callback)', javascript)
        self.assertIn('if (compactPointer.matches) return null;', javascript)
        self.assertIn('if (!compactPointer.matches) callback();', javascript)
        self.assertIn('function activeHoverChainContains(target)', javascript)
        self.assertIn('function hoverPopupContains(target)', javascript)
        self.assertIn(
            'if (hasActiveHover && !activeHoverChainContains(event.target))',
            javascript,
        )
        self.assertIn(
            'if (!insideHoverPopup && !popup.hidden) hide();',
            javascript,
        )
        self.assertNotIn(
            'pinned = false;\n        if (!popup.hidden) hide();\n        showName(target);',
            javascript,
        )

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

    def test_multiline_range_reuses_one_node_without_painting_indentation(self):
        block = ('<pre class="Agda"><a id="10">f</a> <a id="12">x</a>\n'
                 '    <a id="20">y</a></pre>')
        nodes = [
            {"id": 7, "start": 10, "end": 21, "type": "T", "source": "f x y"},
        ]
        rendered = renderer.annotate_expression_nodes(block, nodes)
        opening = ('<span class="expr-node" data-expr-id="7" '
                   'data-expr-start="10" data-expr-end="21"')
        self.assertEqual(rendered.count(opening), 2)
        self.assertIn('</span>\n    <span class="expr-node" data-expr-id="7"', rendered)
        self.assertNotIn('\n<span class="expr-node" data-expr-id="7">    ', rendered)

    def test_all_visual_fragments_of_selected_expression_are_highlighted(self):
        javascript = (ROOT / "site/static/bedrock.js").read_text()
        self.assertIn('var expressionId = option.node.dataset.exprId;', javascript)
        self.assertIn('if (node.dataset.exprId === expressionId)', javascript)

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

    def test_selected_preview_renders_transitive_definition_pages(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Book.md").write_text(
                '<a href="Library.One.html#10">one</a>'
            )
            (root / "Library.One.html").write_text(
                '<a href="Library.Two.html#20">two</a>'
                '<a href="Book.html#1">cycle</a>'
            )
            (root / "Library.Two.html").write_text("done")
            closure = renderer.referenced_module_closure(
                {"Book"}, directory, {"Book", "Library.One", "Library.Two"}
            )
        self.assertEqual(closure, {"Book", "Library.One", "Library.Two"})

    def test_type_rendering_preserves_disambiguated_level_binders(self):
        rendered = renderer.render_type(
            "{A.ℓ : Agda.Primitive.Level} {B.ℓ : Agda.Primitive.Level} → Set A.ℓ",
            {},
        )
        self.assertEqual(re.sub(r"<[^>]+>", "", rendered),
                         "{A.ℓ : Level} {B.ℓ : Level} → Type A.ℓ")
        self.assertNotIn('class="type-node"', rendered)

    def test_type_rendering_uses_cubical_names_for_indexed_universes(self):
        self.assertEqual(renderer.render_type("Set₁", {}), "Type₁")
        self.assertEqual(renderer.render_type("Setω", {}), "Typeω")
        self.assertEqual(renderer.render_type("Set (ℓ-suc ℓ)", {}),
                         "Type (ℓ-suc ℓ)")
        self.assertEqual(re.sub(r'<[^>]+>', '', renderer.render_type("LevelUniv → Prop → SSet₁", {})),
                         "LevelUniv → Prop → SSet₁")
        self.assertEqual(re.sub(r'<[^>]+>', '', renderer.render_type("TypeWithStr → isProp", {})),
                         "TypeWithStr → isProp")

    def test_primitive_sorts_do_not_receive_hover_payloads(self):
        rendered = renderer.build_types(
            ["Agda.Primitive"],
            {"Agda.Primitive": {"LevelUniv": "595", "lzero": "915"}},
            {"Agda.Primitive": {"LevelUniv": "Set₁", "lzero": "Level"}},
            {},
            {"Agda.Primitive": {"595": "Primitive", "915": "Primitive"}},
        )
        self.assertNotIn("595", rendered["Agda.Primitive"])
        self.assertIn("915", rendered["Agda.Primitive"])
        linked = renderer.render_type(
            "Agda.Primitive.LevelUniv",
            {"Agda.Primitive.LevelUniv": ("Agda.Primitive", "595")},
            renderer.qualified_name_pattern({
                "Agda.Primitive.LevelUniv": ("Agda.Primitive", "595")
            }),
            {"Agda.Primitive": {"595": "Primitive"}},
        )
        self.assertIn('href="Agda.Primitive.html#595"', linked)
        self.assertNotIn('data-type="Agda.Primitive#595"', linked)

    def test_prelude_type_hover_uses_the_universe_former_signature(self):
        types = {"Base.Prelude": {"10098": "Type₁"}}
        internal = {}
        reexports = {"by_href": {
            "Agda.Primitive.html#388": (
                "Base.Prelude", "10098", "Primitive", "Type"
            ),
        }, "by_name": {
            "Level": ("Base.Prelude", "10104", "Postulate", "Level"),
            "Type": ("Base.Prelude", "10098", "Primitive", "Type"),
        }}
        renderer.add_prelude_qualified_names(internal, reexports)
        renderer.add_prelude_reexport_types(
            types, {}, reexports, internal,
            {"Base.Prelude": {"10098": "Primitive", "10104": "Postulate"}},
        )
        self.assertEqual(re.sub(r"<[^>]+>", "", types["Base.Prelude"]["10098"]),
                         "(ℓ : Level) → Type ℓ")
        self.assertIn('data-type="Base.Prelude#10098"',
                      types["Base.Prelude"]["10098"])
        self.assertIn('data-type="Base.Prelude#10104"',
                      types["Base.Prelude"]["10098"])

    def test_type_links_reuse_agda_syntax_aspects(self):
        rendered = renderer.render_type(
            "Demo.f",
            {"Demo.f": ("Demo", "10")},
            renderer.qualified_name_pattern({"Demo.f": ("Demo", "10")}),
            {"Demo": {"10": "Function"}},
        )
        self.assertIn(
            '<a href="Demo.html#10" data-type="Demo#10" data-name="f" '
            'class="Function">f</a>', rendered,
        )
        self.assertNotIn('class="type-node"', rendered)

    def test_type_links_route_through_prelude_before_the_library(self):
        internal = {"Cubical.Demo.f": ("Cubical.Demo", "10")}
        reexports = {"by_href": {
            "Cubical.Demo.html#10": ("Base.Prelude", "43", "Function", "f")
        }}
        later = renderer.render_type(
            "Cubical.Demo.f", internal, renderer.qualified_name_pattern(internal),
            {"Base.Prelude": {"43": "Function"}}, "Demo", reexports,
        )
        self.assertIn('href="Base.Prelude.html#43"', later)
        self.assertIn('data-type="Base.Prelude#43"', later)
        prelude = renderer.render_type(
            "Cubical.Demo.f", internal, renderer.qualified_name_pattern(internal),
            {"Cubical.Demo": {"10": "Function"}}, "Base.Prelude", reexports,
        )
        self.assertIn('href="Cubical.Demo.html#10"', prelude)

    def test_untraced_type_delimiters_do_not_create_nodes(self):
        highlighted = ('<a class="Symbol">(</a>'
                       '<a href="Demo.html#10" class="Function">f</a>'
                       '<a class="Symbol">)</a>')
        rendered = renderer.decorate_type_nodes(highlighted)
        self.assertEqual(rendered, highlighted)
        self.assertNotIn('class="type-node"', rendered)

    def test_untraced_arrow_type_does_not_join_its_sides_as_a_node(self):
        highlighted = ('<a class="Symbol">((</a>x : Glued'
                       '<a class="Symbol">)</a> → Pick x'
                       '<a class="Symbol">)</a>')
        rendered = renderer.decorate_type_nodes(highlighted)
        self.assertEqual(rendered, highlighted)
        self.assertNotIn('class="type-node"', rendered)

    def test_untraced_single_name_uses_name_highlight_not_a_fake_node(self):
        rendered = renderer.decorate_type_nodes(
            '<a href="Demo.html#10" class="Function">f</a>'
        )
        self.assertNotIn('class="type-node"', rendered)
        self.assertIn('href="Demo.html#10"', rendered)

    def test_compiler_traced_type_node_can_open_another_hover(self):
        highlighted = ('<a href="Demo.html#10" class="Function">Pick</a> x'
                       ' → Result')
        rendered = renderer.decorate_type_nodes(highlighted, [{
            "id": 7, "kind": "application", "source": "Pick x",
            "type": "Type ℓ",
        }], "Demo")
        self.assertIn('data-expression-type="Demo#7"', rendered)
        self.assertIn('<a href="Demo.html#10" class="Function">Pick</a> x</span>',
                      rendered)
        self.assertEqual(rendered.count('class="type-node"'), 1)
        self.assertNotRegex(rendered, r'class="type-node"[^>]*>[^<]*→')

    def test_universe_type_has_no_structural_hover_node(self):
        rendered = renderer.decorate_type_nodes(
            '<a href="Prelude.html#1" data-type="Prelude#1">Type</a> ℓ', [{
            "id": 7, "kind": "application", "source": "Type ℓ",
            "type": "Type (ℓ-suc ℓ)",
        }], "Demo")
        self.assertNotIn('class="type-node"', rendered)
        self.assertNotIn('data-expression-type=', rendered)
        self.assertIn('data-type="Prelude#1"', rendered)

        ordinary = renderer.decorate_type_nodes("Maybe A", [{
            "id": 8, "kind": "application", "source": "Maybe A",
            "type": "Type ℓ",
        }], "Demo")
        self.assertIn('data-expression-type="Demo#8"', ordinary)
        self.assertNotIn('data-hover-stop=', ordinary)

    def test_hover_ranges_never_match_a_prefix_or_suffix_of_a_name(self):
        for text, source in (("ΩResizing ℓ₁", "Resizing ℓ₁"),
                             ("hProp ℓ₁", "hProp ℓ")):
            nodes = [{"id": "1", "kind": "application", "source": source,
                      "type": "Type"}]
            for highlighted in (text, " ".join(
                    f'<a href="Demo.html#1">{word}</a>' for word in text.split())):
                with self.subTest(text=text, highlighted=highlighted):
                    self.assertNotIn('class="type-node"',
                                     renderer.decorate_type_nodes(highlighted, nodes, "Demo"))
            with self.subTest(source=source):
                self.assertIn('data-expression-type="Demo#1"',
                              renderer.decorate_type_nodes(f"({source})", nodes, "Demo"))

    def test_qualified_type_links_do_not_match_identifier_or_module_prefixes(self):
        internal = {"Demo.s": ("Demo", "1"), "Demo.Helpers": ("Demo", "2")}
        pattern = renderer.qualified_name_pattern(internal)
        for term in ("Demo.section f g", "Demo.Helpers.isContr A", "Demo.s₁"):
            with self.subTest(term=term):
                self.assertNotIn('<a ', renderer.render_type(term, internal, pattern))
        self.assertEqual(renderer.render_type("Demo.s (Demo.s)", internal, pattern)
                         .count('data-type="Demo#1"'), 2)

    def test_missing_type_payloads_keep_links_without_advertising_a_hover(self):
        types = {"Demo": {"1": "Type"}}
        html = ('<a href="Demo.html#1" data-type="Demo#1">known</a> '
                '<a href="Demo.html#2" data-type="Demo#2">private</a>')
        rendered = renderer.resolve_type_hover_links(html, types)
        self.assertIn('data-type="Demo#1"', rendered)
        self.assertNotIn('data-type="Demo#2"', rendered)
        self.assertIn('href="Demo.html#2">private</a>', rendered)
        source = renderer.rewrite_links(
            '<a href="Demo.html#2">private</a>', {"Demo"}, types)
        self.assertEqual(source, '<a href="Demo.html#2">private</a>')

    def test_source_and_hover_nodes_share_the_range_wrapper(self):
        source_annotator = inspect.getsource(renderer.annotate_expression_nodes)
        hover_annotator = inspect.getsource(renderer.decorate_type_nodes)
        self.assertIn("wrap_expression_ranges(", source_annotator)
        self.assertIn("wrap_expression_ranges(", hover_annotator)

    def test_hover_stack_and_definition_modal_history_have_no_depth_cap(self):
        javascript = (ROOT / "site/static/bedrock.js").read_text()
        stylesheet = (ROOT / "site/static/bedrock.css").read_text()
        self.assertIn("var namePopups = [], nameRequest = 0;", javascript)
        self.assertIn("namePopups.push(entry);", javascript)
        self.assertIn("var history = [], historyIndex = -1", javascript)
        self.assertIn("history.push({ target: target", javascript)
        self.assertNotRegex(javascript, r"namePopups\.length\s*[>=]=?\s*\d")
        self.assertNotRegex(javascript, r"history\.length\s*[>=]=?\s*\d")
        self.assertIn("var hoverCloseDelay = 360;", javascript)
        self.assertIn("if (parent) cancelNameClose(parent);", javascript)
        self.assertIn("nameBranchHovered(entry)", javascript)
        self.assertIn('entry.popup.style.top = (window.scrollY + rect.bottom) + "px";',
                      javascript)
        self.assertIn('popup.style.top = (window.scrollY + rect.bottom) + "px";', javascript)
        self.assertIn('.type-inspector { position: absolute;', stylesheet)
        self.assertIn('.type-value .type-node.type-active:not([data-single-name]) {',
                      stylesheet)
        self.assertIn('.type-value .type-node[data-single-name] {', stylesheet)
        self.assertIn(
            '.type-value .type-node[data-single-name].type-active {\n'
            '  background: var(--occ-bg); border-radius: 3px;', stylesheet)
        self.assertIn('margin-inline: 0; padding: 0; background: transparent;',
                      stylesheet)
        self.assertIn('body.definition-modal-open { overflow: hidden; }', stylesheet)
        self.assertIn('if (event.target === backdrop) close();', javascript)
        self.assertIn('closeButton.addEventListener("click", close);', javascript)
        modal_javascript = javascript.split("function initDefinitionModals()", 1)[1]
        self.assertNotIn('var close = document.createElement("button");', modal_javascript)
        self.assertIn('back.className = "definition-modal-history-button"', javascript)
        self.assertIn('forward.className = "definition-modal-history-button"', javascript)
        self.assertIn("history.splice(historyIndex + 1);", javascript)
        self.assertIn('target.module + "." + name', javascript)
        self.assertIn('view.title.textContent = entry.label;', javascript)
        self.assertIn('.type-node[data-expression-type]', javascript)
        self.assertIn('types.$expressions[spec[1]]', javascript)
        self.assertIn('nodeOwnsOpenHover(typeNode)', javascript)
        self.assertIn('".Agda a[href]"', javascript)
        self.assertIn('activeName.classList.add("name-active")', javascript)
        self.assertIn('.Agda a.name-active {', stylesheet)
        self.assertIn('@media (hover: hover) and (pointer: fine) {\n'
                      '  .type-value a[href]:not([data-hover-stop]):hover,', stylesheet)
        self.assertNotIn('pre.Agda a.name-active {', stylesheet)
        self.assertNotIn('className = "definition-modal-navigate"', javascript)
        self.assertIn('title.className = "definition-modal-title";', javascript)
        self.assertIn('header.appendChild(historyActions);\n'
                      '      header.appendChild(title);', javascript)
        self.assertIn('frame.className = "definition-modal-frame";', javascript)
        self.assertIn('frameUrl.searchParams.set("bedrock-modal", "1");', javascript)
        self.assertIn('classList.add("definition-modal-document")', javascript)
        self.assertIn('#site-header, #nav-backdrop, .skip-link, #toc, #sidenote-container,',
                      stylesheet)
        self.assertIn('#site-footer\n) { display: none !important; }', stylesheet)
        self.assertNotIn('#site-footer, .page-scroll', stylesheet)
        self.assertIn('html.definition-modal-document #section-sticky { top: 0; }',
                      stylesheet)
        self.assertIn(
            'padding-bottom: calc(3rem + var(--definition-modal-anchor-room, 0px));',
            stylesheet,
        )
        self.assertIn('var targetBlock = target.closest("pre.Agda, h1") || target;',
                      javascript)
        self.assertIn(
            'function alignModalDefinition(frameDocument, targetBlock)',
            javascript)
        self.assertIn(
            'return alignModalDefinition(frameDocument, targetBlock);',
            javascript,
        )
        self.assertIn('frame.contentWindow.requestAnimationFrame(function () {', javascript)
        self.assertIn('settle(remaining - 1);', javascript)
        self.assertNotIn('targetBlock.scrollIntoView(', javascript)
        self.assertIn('frameUrl.hash = "";', javascript)
        self.assertIn('scroller.scrollTop = desiredTop;', javascript)
        self.assertIn('sizeModalReadingScroller(frameDocument, view.body);', javascript)
        self.assertIn('view.frameSizeObserver.observe(view.body);', javascript)
        self.assertIn('height: 100%; overflow: auto; overscroll-behavior: contain;',
                      stylesheet)
        self.assertIn(
            'if (location.hash && !isReload && !isDefinitionModalDocument)',
            javascript,
        )
        self.assertIn('type: "bedrock-definition-open"', javascript)
        self.assertIn('type: "bedrock-page-navigate"', javascript)
        self.assertIn('location.href = pageUrl.href;', javascript)
        self.assertIn('location.href = targetUrl.href;', javascript)
        self.assertIn('definitionPageKey(loadedUrl) !== definitionPageKey(entry.target.url)', javascript)
        self.assertIn('height: 82dvh;', stylesheet)
        self.assertIn('.definition-modal-frame {', stylesheet)
        self.assertNotIn('raw.charAt(0) === "#"', modal_javascript)
        self.assertIn('url.searchParams.delete("bedrock-modal");', modal_javascript)

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_modal_reading_scroller_uses_explicit_viewport_height(self):
        javascript = (ROOT / "site/static/bedrock.js").read_text()
        helper = re.search(
            r"  function sizeModalReadingScroller\(frameDocument, modalBody\) \{.*?\n  \}",
            javascript, re.DOTALL)
        self.assertIsNotNone(helper)
        scenario = r'''
var root = {style: {height: ""}};
var body = {style: {height: ""}};
var scroller = {style: {height: ""}, clientHeight: 9000};
var frameDocument = {documentElement: root, body: body,
  getElementById: function () { return scroller; }};
sizeModalReadingScroller(frameDocument, {clientHeight: 624});
console.log(JSON.stringify({root: root.style.height, body: body.style.height,
  scroller: scroller.style.height}));
'''
        completed = subprocess.run(
            [shutil.which("node"), "-e", helper.group(0) + scenario],
            text=True, capture_output=True, check=True)
        self.assertEqual(json.loads(completed.stdout), {
            "root": "624px", "body": "624px", "scroller": "624px",
        })

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_modal_accepts_canonical_redirects_without_accepting_another_page(self):
        javascript = (ROOT / "site/static/bedrock.js").read_text()
        helper = re.search(
            r"  function definitionPageKey\(url\) \{.*?\n  \}",
            javascript, re.DOTALL)
        self.assertIsNotNone(helper)
        scenario = r'''
function key(path) { return definitionPageKey(new URL(path, "https://book.example")); }
console.log(JSON.stringify({
  redirected: key("/zh/Base.Choice.html#123") === key("/zh/Base.Choice?bedrock-modal=1"),
  legacy: key("/zh/Base.Choice.html") === key("/zh/Base.Choice?bedrock-modal=1&bedrock-modal-scroll=outer"),
  index: key("/zh/index.html") === key("/zh/"),
  queryOrder: key("/zh/Base.Choice.html?b=2&a=1") === key("/zh/Base.Choice?a=1&b=2&bedrock-modal=1"),
  wrongModule: key("/zh/Base.Choice.html") !== key("/zh/Base.Classical"),
  wrongOrigin: key("/zh/Base.Choice.html") !== key("https://other.example/zh/Base.Choice"),
  wrongQuery: key("/zh/Base.Choice.html?a=1") !== key("/zh/Base.Choice?a=2")
}));
'''
        completed = subprocess.run(
            [shutil.which("node"), "-e", helper.group(0) + scenario],
            text=True, capture_output=True, check=True)
        self.assertEqual(json.loads(completed.stdout), {
            "redirected": True, "legacy": True, "index": True, "queryOrder": True,
            "wrongModule": True, "wrongOrigin": True, "wrongQuery": True,
        })

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_hover_gesture_clears_leaf_background_before_selecting_parent(self):
        javascript = (ROOT / "site/static/bedrock.js").read_text()
        helpers = "\n".join(re.search(
            r"    function " + name + r"\([^)]*\) \{.*?\n    \}",
            javascript, re.DOTALL).group(0)
            for name in ("clearHighlight", "activateTypeGestureItem"))
        scenario = r'''
function node(classes) {
  var state = new Set(classes);
  return {state: state, classList: {
    remove: function (...names) { names.forEach(n => state.delete(n)); },
    add: function (name) { state.add(name); }
  }, closest: function () { return scope; }};
}
var leaf = node(["name-active", "occ"]), parent = node([]);
var scope = {querySelectorAll: function () { return [leaf, parent]; }};
var leafActiveName = null; // Async showName owns the old leaf, not this variable.
function showName() { if (leafActiveName) leafActiveName.classList.remove("name-active"); }
function activateTypeNode(target) { target.classList.add("type-active"); }
activateTypeGestureItem({kind: "expression", node: parent});
var afterParent = {leaf: [...leaf.state], parent: [...parent.state]};
activateTypeGestureItem({kind: "name", node: leaf});
console.log(JSON.stringify({afterParent: afterParent,
  afterLeaf: {leaf: [...leaf.state], parent: [...parent.state]}}));
'''
        completed = subprocess.run(
            [shutil.which("node"), "-e", helpers + scenario],
            text=True, capture_output=True, check=True)
        self.assertEqual(json.loads(completed.stdout), {
            "afterParent": {"leaf": [], "parent": ["type-active"]},
            "afterLeaf": {"leaf": ["name-active"], "parent": []},
        })

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_modal_anchor_uses_the_reading_scroller_not_iframe_viewport(self):
        javascript = (ROOT / "site/static/bedrock.js").read_text()
        helper = re.search(
            r"  function alignModalDefinition\(frameDocument, targetBlock\) \{.*?\n  \}",
            javascript, re.DOTALL)
        self.assertIsNotNone(helper)
        scenario = r'''
var room = 0;
var style = {
  getPropertyValue: function () { return room ? room + "px" : ""; },
  setProperty: function (_, value) { room = parseFloat(value); scroller.scrollHeight = 9246 + room; }
};
var root = {style: style};
var scroller = {scrollTop: 8516, scrollHeight: 9246, clientHeight: 730,
  getBoundingClientRect: function () { return {top: 12}; }};
var bar = {getBoundingClientRect: function () { return {bottom: 56}; }};
var targetBlock = {getBoundingClientRect: function () {
  return {top: 12 + 8755 - scroller.scrollTop};
}};
var frameDocument = {
  documentElement: root,
  getElementById: function (id) { return id === "main-content" ? scroller : bar; }
};
alignModalDefinition(frameDocument, targetBlock);
console.log(JSON.stringify({room: room, scrollTop: scroller.scrollTop,
  blockTop: targetBlock.getBoundingClientRect().top}));
'''
        completed = subprocess.run(
            [shutil.which("node"), "-e", helper.group(0) + scenario],
            text=True, capture_output=True, check=True)
        self.assertEqual(json.loads(completed.stdout), {
            "room": 196, "scrollTop": 8711, "blockTop": 56,
        })

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_modal_anchor_is_not_repositioned_when_already_aligned(self):
        javascript = (ROOT / "site/static/bedrock.js").read_text()
        helper = re.search(
            r"  function alignModalDefinition\(frameDocument, targetBlock\) \{.*?\n  \}",
            javascript, re.DOTALL)
        self.assertIsNotNone(helper)
        scenario = r'''
var scroller = {scrollTop: 8711, scrollHeight: 9442, clientHeight: 730,
  getBoundingClientRect: function () { return {top: 12}; }};
var bar = {getBoundingClientRect: function () { return {bottom: 56}; }};
var frameDocument = {
  documentElement: {style: {getPropertyValue: function () { return "196px"; }}},
  getElementById: function (id) { return id === "main-content" ? scroller : bar; }
};
var targetBlock = {getBoundingClientRect: function () { return {top: 56}; }};
console.log(JSON.stringify({moved: alignModalDefinition(frameDocument, targetBlock),
  scrollTop: scroller.scrollTop}));
'''
        completed = subprocess.run(
            [shutil.which("node"), "-e", helper.group(0) + scenario],
            text=True, capture_output=True, check=True)
        self.assertEqual(json.loads(completed.stdout), {
            "moved": False,
            "scrollTop": 8711,
        })

    def test_mobile_definition_click_requires_the_hover_action(self):
        javascript = (ROOT / "site/static/bedrock.js").read_text()
        self.assertIn(
            '"[data-hover-help], [data-hover-html], [data-hover-template], a[data-type], .type-node[data-expression-type], .expr-node, '
            '.Agda a[href]"',
            javascript,
        )
        self.assertIn(
            'return candidate && !candidate.matches('
            '".type-definition-link, .syntax-doc-link")',
            javascript,
        )
        self.assertIn(
            'if (compactPointer.matches && !isDefinitionPopupAction('
            'definitionLink))',
            javascript,
        )
        self.assertIn(
            'target.matches("[data-hover-help], [data-hover-html], [data-hover-template], a[href], .type-node[data-expression-type]")',
            javascript,
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

    def test_module_dummy_codomain_does_not_become_a_hover_node(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            src, html_dir = root / 'src', root / 'html'
            src.mkdir()
            html_dir.mkdir()
            source = '```agda\nmodule Demo where\nvalue Ω e = f Ω\n  where open CodedTruth Ω e\n```\n'
            path = src / 'Demo.lagda.md'
            path.write_text(source)
            (html_dir / 'Demo.md').write_text('')
            trace = root / 'trace.jsonl'
            diagnostic = '"dummyType: __DUMMY_TYPE__, called at src/full/Agda/TypeChecking/Rules/Application.hs:923:52"'
            records = []
            for text, type_ in [('CodedTruth Ω', 'Equiv → ' + diagnostic),
                                ('CodedTruth Ω e', diagnostic), ('f Ω', 'A')]:
                start = source.index(text) + 1
                records.append({'version': 1, 'run': 'one', 'kind': 'application',
                                'path': str(path.resolve()), 'sourceHash': extractor.source_hash(path),
                                'start': start, 'end': start + len(text), 'type': type_})
            trace.write_text(''.join(json.dumps(record) + '\n' for record in records))
            data, compact = extractor.normalize(src.resolve(), html_dir.resolve(), trace)
        self.assertEqual([node['source'] for node in data['Demo']], ['f Ω'])
        self.assertEqual([record['type'] for record in compact], ['A'])

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
