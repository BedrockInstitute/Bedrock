import json
import importlib.util
from html.parser import HTMLParser
import re
import shutil
import subprocess
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("navigation_renderer", ROOT / "scripts/site/render-site.py")
renderer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(renderer)


class TocParser(HTMLParser):
    def __init__(self):
        super().__init__()
        self.details = []
        self.branches = []
        self.links = []

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == "details":
            self.details.append(attrs)
            if attrs.get("class") == "toc-branch":
                self.branches.append(attrs)
        elif tag == "a":
            self.links.append((attrs["href"], [d["data-heading"] for d in self.details
                                              if "data-heading" in d]))

    def handle_endtag(self, tag):
        if tag == "details":
            self.details.pop()


class SiteNavigationTests(unittest.TestCase):
    def test_heading_tree_is_nested_and_initially_collapsed(self):
        toc = [(2, "logic", "Logic & operations"), (3, "truth", "Truth"),
               (5, "witness", "Witness"), (3, "false", "Falsity"), (2, "next", "Next")]
        html = renderer.toc_html(toc, "en")
        parser = TocParser()
        parser.feed(html)
        self.assertEqual(parser.links, [
            ("#logic", ["logic"]), ("#truth", ["logic", "truth"]),
            ("#witness", ["logic", "truth"]), ("#false", ["logic"]), ("#next", []),
        ])
        self.assertEqual(len(parser.branches), 2)
        self.assertTrue(all("open" not in branch for branch in parser.branches))
        self.assertIn("Logic &amp; operations", html)
        self.assertEqual(renderer.toc_html([], "en"), "")

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_reading_position_opens_ancestors_and_closes_departed_sections(self):
        javascript = (ROOT / "site/static/bedrock.js").read_text()
        helper = re.search(r"    function syncTocBranches\(activeLink\) \{.*?\n    \}\n",
                           javascript, re.DOTALL)
        self.assertIsNotNone(helper)
        scenario = r'''
function branch(links) {
  return {open: false, contains: function (link) { return links.includes(link); }};
}
var tocBranches = [branch(["logic", "truth", "witness", "false"]),
                   branch(["truth", "witness"]), branch(["other", "child"])];
var states = [];
[null, "logic", "witness", "false", "child", "witness", "next", null].forEach(function (link) {
  syncTocBranches(link);
  states.push(tocBranches.map(function (branch) { return branch.open; }));
});
console.log(JSON.stringify(states));
'''
        completed = subprocess.run([shutil.which("node"), "-e", helper.group(0) + scenario],
                                   check=True, capture_output=True, text=True, timeout=5)
        self.assertEqual(json.loads(completed.stdout), [
            [False, False, False], [True, False, False], [True, True, False],
            [True, False, False], [False, False, True], [True, True, False],
            [False, False, False], [False, False, False],
        ])

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_active_section_link_stays_inside_sidebar_viewport(self):
        javascript = (ROOT / "site" / "static" / "bedrock.js").read_text()
        helper = re.search(
            r"    function revealTocLink\(link\) \{.*?\n    \}\n",
            javascript,
            re.DOTALL,
        )
        self.assertIsNotNone(helper)
        scenario = r'''
var toc = {
  scrollTop: 100,
  getBoundingClientRect: function () { return {top: 10, bottom: 110}; }
};
var document = {getElementById: function () { return toc; }};
function show(top, bottom) {
  toc.scrollTop = 100;
  revealTocLink({getBoundingClientRect: function () { return {top: top, bottom: bottom}; }});
  return toc.scrollTop;
}
console.log(JSON.stringify({above: show(-5, 5), visible: show(30, 50), below: show(120, 140)}));
'''
        completed = subprocess.run(
            [shutil.which("node"), "-e", helper.group(0) + scenario],
            check=True,
            capture_output=True,
            text=True,
            timeout=5,
        )
        self.assertEqual(json.loads(completed.stdout), {
            "above": 77,
            "visible": 100,
            "below": 138,
        })


class PreludeReferenceTests(unittest.TestCase):
    PRELUDE = '''<pre class="Agda"><a id="1" class="Keyword">open</a>
<a id="2" class="Keyword">import</a>
<a id="3" href="Cubical.Relation.Nullary.html" class="Module">Cubical.Relation.Nullary</a>
<a id="4" class="Keyword">public</a>
<a id="5" class="Keyword">using</a> <a id="42" class="Symbol">(</a> <a id="43" href="Cubical.Relation.Nullary.Properties.html#2891" class="Function">mapDec</a>
<a id="50" class="Symbol">)</a></pre>'''

    def test_later_code_links_visit_prelude_before_library(self):
        bridge = renderer.prelude_reexport_index(self.PRELUDE)
        later = ('<a id="90" href="Cubical.Relation.Nullary.Properties.html#2891" '
                 'class="Function">mapDec</a>')
        rewritten = renderer.rewrite_links(
            later,
            {"Base.Prelude", "Cubical.Relation.Nullary.Properties"},
            {},
            current_module="Base.Choice",
            prelude_reexports=bridge,
        )
        self.assertIn('href="Base.Prelude.html#43"', rewritten)
        self.assertNotIn('href="Cubical.Relation.Nullary.Properties.html#2891"', rewritten)

    def test_prelude_keeps_the_original_library_link(self):
        bridge = renderer.prelude_reexport_index(self.PRELUDE)
        original = ('<a id="43" href="Cubical.Relation.Nullary.Properties.html#2891" '
                    'class="Function">mapDec</a>')
        rewritten = renderer.rewrite_links(
            original,
            {"Base.Prelude", "Cubical.Relation.Nullary.Properties"},
            {},
            current_module="Base.Prelude",
            prelude_reexports=bridge,
        )
        self.assertIn('href="Cubical.Relation.Nullary.Properties.html#2891"', rewritten)

    def test_later_inline_reference_uses_the_same_intermediate_hop(self):
        bridge = renderer.prelude_reexport_index(self.PRELUDE)
        rendered = renderer.inline_ref(
            "mapDec",
            {"Base.Prelude", "Base.Choice"},
            {},
            {"mapDec": ("Cubical.Relation.Nullary.Properties.html#2891", "Function")},
            "Base.Choice",
            bridge,
        )
        self.assertIn('href="Base.Prelude.html#43"', rendered)


if __name__ == "__main__":
    unittest.main()
