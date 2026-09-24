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
    def test_milestones_and_chapters_share_compact_top_bottom_navigation(self):
        modules = ['Origin', 'Base.Prelude', 'Base.Choice']
        for lang in ('en', 'zh', 'ja'):
            body = renderer.chapter_navigation('<h1>Origin</h1><p>Proofs</p>', 'Origin', modules, lang)
            home = renderer.learning_home(body, '<section id="reading-explorer"></section>', lang, [])
            panel = home.split('class="book-panel guide-landmark">', 1)[1].split('</section>', 1)[0]
            self.assertEqual(panel.count('class="chapnav-next"'), 2)
            self.assertEqual(panel.count('href="Base.Prelude.html"'), 2)
            self.assertNotIn('class="chapnav-prev"', home)
            self.assertIn('aria-hidden="true"', panel)
            chapter = renderer.chapter_navigation('<h1>Prelude</h1>', 'Base.Prelude', modules, lang)
            self.assertEqual(chapter.count('class="chapnav-prev"'), 2)
            self.assertEqual(chapter.count('class="chapnav-next"'), 2)
            visible = renderer.plain_code(chapter)
            self.assertNotIn(renderer.UI[lang]['prev'], visible)
            self.assertNotIn(renderer.UI[lang]['next'], visible)

    def test_private_submodule_keeps_inline_modifier_and_body_alignment(self):
        body = ('<details open class="submodule-fold"><summary class="submodule-fold-heading">'
                '<pre class="Agda">private module BooleanCodes where\n</pre></summary>'
                '<div class="submodule-fold-content"><pre class="Agda">'
                '  <a id="50">encodeB</a> = value\n    continued\n</pre></div></details>')
        output = renderer.dedent_submodule_code(body)
        self.assertIn('private module BooleanCodes where', output)
        self.assertIn('<pre class="Agda"><a id="50">encodeB</a> = value\n  continued\n</pre>', output)

    def test_code_scroll_padding_wrap_preserves_tokens_and_anchors(self):
        inner = '<a id="123" href="A.html#123">x</a> = y\n  z\n'
        code = '<pre class="Agda">' + inner + '</pre>'
        body = '<details><summary class="submodule-fold-heading">' + code + '</summary><div>' + code + '</div></details>'
        rendered = renderer.render_code_scroll_content(body)
        self.assertEqual(rendered.count('<span class="agda-code-content">' + inner + '</span>'), 1)
        self.assertIn('<summary class="submodule-fold-heading">' + code + '</summary>', rendered)
        self.assertEqual(renderer.render_code_scroll_content(rendered), rendered)
        self.assertEqual(renderer.plain_code(code), renderer.plain_code(renderer.render_code_scroll_content(code)))
        legacy = body.replace(code, '<pre class="Agda"><span class="agda-code-content">' + inner + '</span></pre>')
        self.assertEqual(renderer.render_code_scroll_content(legacy), rendered)

    def test_statement_ending_preserves_code_and_stays_inside_fold(self):
        code = '<pre class="Agda"><a id="123" href="A.html#123">x</a> = y</pre>'
        body = '<details><div>' + code + '\n<p id="p-1">∎</p></div></details>'
        rendered = renderer.render_statement_endings(body, 'zh')
        self.assertIn(code, rendered)
        self.assertIn('class="statement-ending"', rendered)
        self.assertIn('aria-label="陈述结束"', rendered)
        self.assertIn('id="p-1"', rendered)
        self.assertLess(rendered.index('statement-qed'), rendered.index('</details>'))
        invalid = code + '</details><p>∎</p>'
        self.assertEqual(renderer.render_statement_endings(invalid, 'en'), invalid)
        prose = code + '<p>Explanation</p><p>∎</p>'
        self.assertEqual(renderer.render_statement_endings(prose, 'en'), prose)

    def test_formal_labels_have_shared_semantic_classes(self):
        body, _ = renderer.md_to_html('**定义** (`x`) Text.\n\n**证明** Reason.')
        self.assertIn('class="prose-statement"', body)
        self.assertIn('class="prose-proof"', body)

    def test_review_status_is_outside_heading_and_localized(self):
        previous = dict(renderer.CHAPTER_META)
        try:
            renderer.CHAPTER_META['A'] = {'human_reviewed': True}
            body = renderer.render_review_status('<h1 id="sec-0">Title</h1>', 'A', 'zh')
            self.assertIn('is-reviewed', body)
            self.assertIn('已人工校阅', body)
            self.assertIn('<h1 id="sec-0">Title</h1>', body)
            self.assertGreater(body.index('chapter-review '), body.index('</h1>'))
            renderer.CHAPTER_META['A']['human_reviewed'] = False
            self.assertIn('未人工校阅', renderer.render_review_status('<h1>Title</h1>', 'A', 'zh'))
            home = renderer.learning_home(body, '<section id="reading-explorer"></section>', 'zh', [])
            self.assertEqual(home.count('class="chapter-review '), 1)
        finally:
            renderer.CHAPTER_META.clear()
            renderer.CHAPTER_META.update(previous)

    def test_nested_submodule_code_dedents_only_rendered_scope(self):
        body = '''<details open class="submodule-fold">
<summary class="submodule-fold-heading"><pre class="Agda">module Outer where\n</pre></summary>
<div class="submodule-fold-content">
<pre class="Agda">  <a id="1">outer</a> = value\n    continuation\n</pre>
<details open class="submodule-fold">
<summary class="submodule-fold-heading"><pre class="Agda">  module Inner\n    (x : A) where\n</pre></summary>
<div class="submodule-fold-content">
<pre class="Agda">    <a id="2">inner</a> = outer\n      continuation\n</pre>
</div></details>
<pre class="Agda">  after = Inner.inner\n</pre>
</div></details>
<pre class="Agda">  outside = value\n</pre>'''
        rendered = renderer.dedent_submodule_code(body)
        self.assertIn('<pre class="Agda"><a id="1">outer</a> = value\n'
                      '  continuation\n</pre>', rendered)
        self.assertIn('<pre class="Agda">module Inner\n  (x : A) where\n</pre>', rendered)
        self.assertIn('<pre class="Agda"><a id="2">inner</a> = outer\n'
                      '  continuation\n</pre>', rendered)
        self.assertIn('<pre class="Agda">after = Inner.inner\n</pre>', rendered)
        self.assertIn('<pre class="Agda">  outside = value\n</pre>', rendered)

    def test_home_starts_with_milestones(self):
        home = renderer.learning_home('<h1 id="sec-0">Origin</h1><p>Proofs</p>',
                                      '<section id="reading-explorer"></section>', "en", [])
        self.assertLess(home.index('id="tab-milestones"'), home.index('id="tab-reading-explorer"'))
        self.assertLess(home.index('<section id="milestones"'),
                        home.index('<section id="reading-explorer"'))

    def test_milestones_preserves_chapter_heading_hover_anchors_and_review(self):
        previous = dict(renderer.CHAPTER_META)
        try:
            renderer.CHAPTER_META['Origin'] = {'human_reviewed': True}
            for lang, title in [('en', 'Origin'), ('zh', '里程碑'), ('ja', 'マイルストーン')]:
                body = ('<h1 id="sec-0"><span id="123" class="boilerplate-anchor"></span>'
                        '<button class="boilerplate-hover" data-hover-template="setup">'
                        + title + '</button></h1><p>Content</p>'
                        '<template id="setup">module Origin where</template>')
                reviewed = renderer.render_review_status(body, 'Origin', lang)
                home = renderer.learning_home(reviewed, '<section id="reading-explorer"></section>', lang, [])
                intro, panel = home.split('<section id="milestones"', 1)
                self.assertNotIn('chapter-review', intro)
                self.assertNotIn('data-hover-template', intro)
                self.assertIn('<h1 id="reading-guide-title">', intro)
                self.assertIn('<h2 id="sec-0"><span id="123"', panel)
                self.assertIn('data-hover-template="setup">' + title, panel)
                self.assertIn('chapter-review is-reviewed', panel)
                self.assertEqual(home.count('id="123"'), 1)
                self.assertEqual(home.count('id="setup"'), 1)
        finally:
            renderer.CHAPTER_META.clear()
            renderer.CHAPTER_META.update(previous)

    def test_sidebar_folds_guide_and_opens_current_route(self):
        data = {"routes": [{"id": "foundation", "title": {"en": "Foundations"},
                            "chapters": ["A.One", "A.Two"]}]}
        nav = renderer.modules_nav("A.Two", ["A.One", "A.Two"], "en", data)
        self.assertIn('<details class="navsec reading-guide"><summary', nav)
        self.assertIn('<details class="navsec current-route" open', nav)
        self.assertIn('data-route="foundation"', nav)
        self.assertIn('data-chapter="A.Two" aria-current="page"', nav)
        self.assertNotIn('modnav', nav)
        self.assertNotIn('modgroup', nav)
        self.assertIn('Interactive contents', nav)

    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_sticky_directory_nests_all_chapter_headings(self):
        javascript = (ROOT / "site/static/reader/navigation.js").read_text()
        helper = re.search(r"  function sectionOutline\(headings\) \{.*?\n  \}\n",
                           javascript, re.DOTALL)
        self.assertIsNotNone(helper)
        scenario = r'''
var headings = ["H2:a", "H3:b", "H4:c", "H2:d", "H3:e"].map(function (item) {
  var parts = item.split(":");
  return {tagName: parts[0], id: parts[1]};
});
function shape(nodes) {
  return nodes.map(function (node) { return [node.heading.id, shape(node.children)]; });
}
console.log(JSON.stringify(shape(sectionOutline(headings))));
'''
        completed = subprocess.run([shutil.which("node"), "-e", helper.group(0) + scenario],
                                   check=True, capture_output=True, text=True, timeout=5)
        self.assertEqual(json.loads(completed.stdout),
                         [["a", [["b", [["c", []]]]]], ["d", [["e", []]]]])

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
        javascript = (ROOT / "site/static/reader/navigation.js").read_text()
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
        javascript = (ROOT / "site/static/reader/navigation.js").read_text()
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

    def test_prelude_hop_keeps_hover_payload_when_its_type_exists(self):
        bridge = renderer.prelude_reexport_index(self.PRELUDE)
        later = ('<a id="90" href="Cubical.Relation.Nullary.Properties.html#2891" '
                 'class="Function">mapDec</a>')
        rewritten = renderer.rewrite_links(
            later,
            {"Base.Prelude", "Cubical.Relation.Nullary.Properties"},
            {"Base.Prelude": {"43": "type"}},
            current_module="Base.Choice",
            prelude_reexports=bridge,
        )
        self.assertIn('href="Base.Prelude.html#43"', rewritten)
        self.assertIn('data-type="Base.Prelude#43"', rewritten)

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

    def test_aliased_inline_reference_uses_target_declaration_for_hover(self):
        rendered = renderer.inline_ref_link(
            "V", "V.Hierarchy", "𝒮ᵥ", {"V.Hierarchy": {"𝒮ᵥ": "97"}})
        rewritten = renderer.rewrite_links(
            rendered, {"V.Hierarchy"}, {"V.Hierarchy": {"97": "type"}})
        self.assertIn('href="V.Hierarchy.html#97"', rewritten)
        self.assertIn('data-type="V.Hierarchy#97"', rewritten)
        self.assertIn('>V</a>', rewritten)

    def test_bound_variable_is_unlinked_but_standalone_declaration_may_be_bare(self):
        bound = renderer.inline_ref(
            "x", {"Base.Prelude"}, {},
            {"x": ("Base.Prelude.html#10", "Bound")}, "Base.Prelude")
        declaration = renderer.inline_ref(
            "refl", {"Base.Prelude"}, {},
            {"refl": ("Cubical.Foundations.Prelude.html#20", "Function")},
            "Base.Prelude")
        self.assertEqual(bound, '<code class="Agda inline-ref">x</code>')
        self.assertNotIn('inline-code', declaration)

    def test_unqualified_name_cannot_link_to_unrelated_module(self):
        rendered = renderer.inline_ref(
            "A", {"Base.Prelude", "Elsewhere"},
            {"Elsewhere": {"A": "42"}}, {}, "Base.Prelude")
        self.assertEqual(rendered, '<code class="Agda inline-ref">A</code>')

    def test_expression_links_declaration_but_not_its_local_arguments(self):
        rendered = renderer.inline_ref(
            "cong f p", {"Base.Prelude"}, {},
            {"cong": ("Cubical.Foundations.Prelude.html#30", "Function"),
             "f": ("Base.Prelude.html#31", "Bound"),
             "p": ("Base.Prelude.html#32", "Bound")}, "Base.Prelude")
        self.assertIn('>cong</a> f p', rendered)
        self.assertNotIn('>f</a>', rendered)
        self.assertNotIn('>p</a>', rendered)

    def test_prelude_import_anchor_has_hover_type(self):
        types = {"Base.Prelude": {}}
        reexports = {"by_href": {
            "Cubical.HITs.PropositionalTruncation.Base.html#226":
                ("Base.Prelude", "102913", "Datatype Operator", "∥_∥₁")}}
        renderer.add_prelude_reexport_types(
            types, {"Base.Prelude": {"∥_∥₁": "Type → Type"}},
            reexports, {}, {})
        self.assertEqual(re.sub(r"<[^>]+>", "", types["Base.Prelude"]["102913"]),
                         "Type → Type")


if __name__ == "__main__":
    unittest.main()
