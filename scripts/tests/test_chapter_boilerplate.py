from reader_test_support import source
"""Source layout and presentation use the same actual chapter setup."""
from pathlib import Path
from outcrop import site as site_package
RESOURCES = Path(site_package.__file__).resolve().parent / "resources"
import re
import sys
import unittest

from outcrop.core.chapter_structure import OPTIONS, chapter_parts, opening_errors, boilerplate_ranges
from outcrop.core.boilerplate import mirror_boilerplate, popup_code
from outcrop.core.agda_help import HELP, annotate_keywords, help_html

TITLE = '<!--en-->\n# Title\n<!--zh-->\n# 标题\n<!--ja-->\n# 題名\n<!--/-->\n'


def opening(header='module Test where', imports='open import Base.Prelude'):
    return f'```agda\n{OPTIONS}\n{header}\n```\n\n{TITLE}\n```agda\n{imports}\n```\n\nBody.\n'


def parameter_opening():
    return (f'```agda\n{OPTIONS}\n```\n\n{TITLE}\n'
            '```agda\nopen import Base.Prelude\n```\n\n'
            '<!--en-->\nFix a level.\n<!--zh-->\n固定层级。\n<!--ja-->\nレベルを固定する。\n<!--/-->\n\n'
            '```agda\nmodule Test {ℓ : Level} where\n```\n\n'
            '```agda\nimport Project\n```\n\nBody.\n')


class OpeningTests(unittest.TestCase):
    def test_valid_plain_and_parameterized_openings(self):
        self.assertEqual(opening_errors(opening(), 'Test', {'Test', 'Base.Prelude'}), [])
        text = parameter_opening()
        self.assertEqual(opening_errors(text, 'Test', {'Test', 'Base.Prelude', 'Project'}), [])
        _, declaration, needed, project = chapter_parts(text, 'Test', {'Test', 'Base.Prelude', 'Project'})
        self.assertIn('{ℓ : Level}', declaration.text)
        self.assertEqual([s.text for s in needed], ['open import Base.Prelude'])
        self.assertEqual([s.text for s in project], ['import Project'])

    def test_parameters_require_their_visible_trilingual_exposition(self):
        text = parameter_opening().replace('<!--ja-->\nレベルを固定する。\n', '')
        self.assertTrue(opening_errors(text, 'Test', {'Test', 'Base.Prelude', 'Project'}))
        text = text.replace('<!--/-->\n\n```agda\nmodule',
                            '<!--/-->\n<!--en-->\nOther.\n<!--zh-->\n另段。\n<!--ja-->\n別の段落。\n<!--/-->\n\n```agda\nmodule')
        self.assertTrue(opening_errors(text, 'Test', {'Test', 'Base.Prelude', 'Project'}))

    def test_mixed_external_import_and_late_project_import_fail(self):
        for imports in ('open import Base.Prelude\nimport Cubical.Data.Nat',
                        'import Cubical.Data.Nat\nopen import Base.Prelude'):
            self.assertTrue(opening_errors(opening(imports=imports), 'Test', {'Test', 'Base.Prelude'}))
        text = opening() + '\n```agda\nimport Project\n```\n'
        self.assertTrue(opening_errors(text, 'Test', {'Test', 'Base.Prelude', 'Project'}))

    def test_unnecessary_premodule_import_fails(self):
        text = opening('import Project\nmodule Test where')
        self.assertTrue(opening_errors(text, 'Test', {'Test', 'Base.Prelude', 'Project'}))

    def test_multiline_selection_stays_complete(self):
        text = opening(imports='open import Base.Prelude\n  using ( Type\n        ; Level )')
        self.assertEqual(opening_errors(text, 'Test', {'Test', 'Base.Prelude'}), [])

    def test_parameter_imports_do_not_depend_on_a_hardcoded_vocabulary(self):
        text = parameter_opening().replace('open import Base.Prelude', 'open import Vocabulary')
        text = text.replace('{ℓ : Level}', '(structure : Structure)')
        self.assertEqual(opening_errors(text, 'Test', {'Test', 'Vocabulary', 'Project'}), [])

    def test_all_real_chapters_conform(self):
        root = Path(__file__).resolve().parents[2] / 'src'
        paths = list(root.rglob('*.lagda.md'))
        modules = {str(p.relative_to(root))[:-9].replace('/', '.') for p in paths}
        for path in paths:
            with self.subTest(path=path):
                self.assertEqual(opening_errors(path.read_text(), str(path.relative_to(root))[:-9].replace('/', '.'), modules, visible_import_chapters={'Origin'}), [])

    def test_milestone_reexports_are_body_code_not_hidden_setup(self):
        text = opening('module Origin where', 'open import Base.Prelude public using ( Result )')
        text = text.replace('```agda\nopen import', 'A theorem.\n\n```agda\nopen import')
        modules = {'Origin', 'Base.Prelude'}
        self.assertEqual(opening_errors(text, 'Origin', modules, visible_import_chapters={'Origin'}), [])
        self.assertTrue(opening_errors(text.replace('public ', ''), 'Origin', modules, visible_import_chapters={'Origin'}))
        self.assertTrue(opening_errors(text + '\n```agda\nf = x\n```', 'Origin', modules, visible_import_chapters={'Origin'}))
        self.assertFalse(any(start <= text.index('open import') < end
                             for start, end in boilerplate_ranges(text, 'Origin', modules, visible_import_chapters={'Origin'})))


class BoilerplateTests(unittest.TestCase):
    def test_milestone_statement_imports_remain_visible_with_their_qed(self):
        code = '<pre class="Agda">open import Base.Prelude public using ( <a id="90">Result</a> )</pre>'
        body = (f'<pre class="Agda">{OPTIONS}\nmodule Origin where</pre><h1>Title</h1>'
                '<p><strong>Theorem 0</strong> Result.</p><div class="statement-ending">'
                + code + '<span class="statement-qed">∎</span></div>')
        output = mirror_boilerplate(body, 'Origin', {'Origin', 'Base.Prelude'}, visible_import_chapters={'Origin'})
        self.assertIn(code, output)
        self.assertIn('boilerplate-header-Origin', output)
        self.assertIn('boilerplate-import-Origin-Base.Prelude', output)
        self.assertEqual(output.count('id="90"'), 1)
        self.assertIn('<span class="statement-qed">∎</span>', output)

    def test_boilerplate_shell_is_scoped_to_source_templates(self):
        root = Path(__file__).resolve().parents[2]
        javascript = source('hover', 'code-targets', 'type-store', 'hover-branch', 'definition-modal')
        self.assertIn('if ((template && template.hasAttribute("data-boilerplate-module")) || name.classList.contains("universe-notation"))\n'
                      '            namePopup.classList.add("boilerplate-hover-popup");', javascript)
        css = (RESOURCES / 'static/outcrop.css').read_text()
        shell = re.search(r'\.boilerplate-hover-popup\s*\{([^}]+)\}', css)[1]
        self.assertIn('background: var(--code-bg)', shell)
        self.assertIn('border: 1px solid var(--code-border)', shell)
        self.assertIn('box-shadow:', shell)
        self.assertNotIn('font', shell)

    def test_compiler_ranges_are_rebased_for_the_shared_popup_gesture(self):
        code = ('module Test (<span class="expr-node" data-expr-id="7" '
                'data-expr-start="600" data-expr-end="608" style="--expr-level:0">'
                '<a id="600" data-type="M#1">𝒮</a> &amp; X</span>) where')
        output = popup_code(code, 'Test')
        self.assertIn('class="type-node"', output)
        self.assertIn('data-expression-type="Test#7"', output)
        self.assertIn('data-expr-start="13"', output)
        self.assertIn('data-expr-end="18"', output)
        self.assertNotIn('id="600"', output)

    def test_header_and_imports_keep_real_highlighting(self):
        body = ('<pre class="Agda">' + OPTIONS + '\n'
                '<a id="90" class="Keyword">module</a> Test where</pre>'
                '<h1 id="sec-0">Title</h1>'
                '<pre class="Agda"><a id="50" class="Keyword">open</a> import Base.Prelude\n'
                'import Project\n  using ( Thing )</pre>'
                '<p>Body.</p><pre class="Agda">import Cubical.Data.Nat</pre>')
        result = mirror_boilerplate(body, 'Test', {'Test', 'Project', 'Base.Prelude'})
        self.assertIn('boilerplate-import-Test-Base.Prelude', result)
        self.assertIn('boilerplate-import-Test-Project', result)
        self.assertIn('using ( Thing )', result)
        self.assertIn('<pre class="Agda">import Cubical.Data.Nat</pre>', result)
        header = re.search(r'<template id="boilerplate-header-Test"[^>]*>(.*?)</template>', result, re.S)[1]
        self.assertNotIn('import', header)
        self.assertIn('Test where', header)
        self.assertNotIn('id="90"', header)
        self.assertEqual(result.count('id="90"'), 1)
        self.assertIn('<a class="Keyword">module</a>', header)

    def test_unrelated_code_is_not_hidden(self):
        body = '<h1>Title</h1><pre class="Agda">f = x</pre>'
        self.assertEqual(mirror_boilerplate(body, 'Test', {'Test'}), body)

    def test_parameterized_declaration_and_prose_stay_in_the_body(self):
        body = (f'<pre class="Agda">{OPTIONS}</pre><h1>Title</h1>'
                '<pre class="Agda">open import Base.Prelude</pre>'
                '<p>Fix a level.</p><pre class="Agda">module Test {ℓ : Level} where</pre>'
                '<pre class="Agda">import Project</pre><p>Body.</p>')
        output = mirror_boilerplate(body, 'Test', {'Test', 'Base.Prelude', 'Project'})
        self.assertIn('<p>Fix a level.</p><pre class="Agda">module Test {ℓ : Level} where</pre>', output)
        header = re.search(r'<template id="boilerplate-header-Test"[^>]*>(.*?)</template>', output, re.S)[1]
        self.assertEqual(header, OPTIONS)
        self.assertIn('boilerplate-import-Test-Base.Prelude', output)
        self.assertIn('boilerplate-import-Test-Project', output)


class SyntaxHelpTests(unittest.TestCase):
    def test_all_reserved_keywords_and_requested_options_have_three_languages(self):
        words = r'= | -> → : ? \ λ ∀ .. ... abstract coinductive constructor data do eta-equality field forall hiding import in inductive infix infixl infixr instance interleaved let macro module mutual no-eta-equality opaque open overlap pattern postulate primitive private public quote quoteTerm record renaming rewrite syntax tactic unfolding unquote unquoteDecl unquoteDef using variable where with as to OPTIONS --cubical --safe --guardedness'
        self.assertFalse(set(words.split()) - HELP.keys())
        for key in words.split():
            for lang in ('en', 'zh', 'ja'):
                self.assertIn('https://agda.readthedocs.io/en/v2.8.0/', help_html(key, lang))
                self.assertTrue(HELP[key][1][lang])

    def test_only_classified_tokens_are_help_targets_and_annotation_is_idempotent(self):
        body = ('<a class="Keyword">module</a> <a class="Function">module</a>'
                '<a class="Pragma">--safe</a><a class="Keyword">moduleFoo</a>')
        output = annotate_keywords(body, 'zh')
        self.assertEqual(output.count('data-hover-help='), 2)
        self.assertIn('了解更多', help_html('module', 'zh'))
        self.assertEqual(annotate_keywords(output, 'zh'), output)

    def test_help_links_are_not_mobile_definition_targets(self):
        javascript = source('hover', 'code-targets', 'type-store', 'hover-branch', 'definition-modal')
        self.assertIn('candidate.matches(".type-definition-link, .syntax-doc-link")', javascript)
        self.assertIn('html: infoHTML ||', javascript)
        self.assertIn('if (this.persistent()) return null;', javascript)

    def test_modal_title_is_localized_code_and_never_a_link(self):
        javascript = source('hover', 'code-targets', 'type-store', 'hover-branch', 'definition-modal')
        self.assertIn('var title = document.createElement("div");', javascript)
        self.assertIn('titleName.className = "Agda";', javascript)
        self.assertIn('document.createTextNode(chapterText + " ")', javascript)
        self.assertNotIn('view.title.href', javascript)

    def test_modal_loading_preserves_layout_and_supports_reduced_motion(self):
        root = Path(__file__).resolve().parents[2]
        javascript = source('hover', 'code-targets', 'type-store', 'hover-branch', 'definition-modal')
        css = (RESOURCES / 'static/outcrop.css').read_text()
        self.assertIn('view.body.replaceChildren(loading, frame);', javascript)
        self.assertIn('if (revealed || failed || !isCurrentFrame()) return;', javascript)
        self.assertIn('else revealFrame();', javascript)
        self.assertIn('frame.setAttribute("inert", "");', javascript)
        self.assertIn('frame.removeAttribute("inert");', javascript)
        self.assertIn('frame.addEventListener("error", showMissing);', javascript)
        shell = re.search(r'\.definition-modal-frame\s*\{([^}]+)\}', css)[1]
        self.assertIn('opacity: 0', shell)
        self.assertNotIn('display: none', shell)
        self.assertIn('.definition-modal-loading-indicator::before { animation: none; }', css)
        self.assertIn('.definition-modal-frame { transition: none; }', css)

    def test_module_code_links_keep_the_two_step_modal_path_without_an_anchor(self):
        javascript = source('hover', 'code-targets', 'type-store', 'hover-branch', 'definition-modal')
        self.assertIn('if (!url.hash && !link.matches(".Module, [data-module-target]")) return null;', javascript)
        self.assertIn('if (isModule) link.setAttribute("data-module-target", "true");', javascript)
        self.assertIn('frameDocument.querySelector("article h1, h1, pre.Agda")', javascript)


if __name__ == '__main__':
    unittest.main()
