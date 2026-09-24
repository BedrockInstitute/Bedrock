"""Automatic prose-code help shares the formal-code hover pipeline."""
import html
import importlib.util
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('inline_renderer', ROOT / 'scripts/site/render-site.py')
renderer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(renderer)
from agda_help import annotate_inline_code, annotate_keywords, inline_syntax_ranges, help_html


class InlineAgdaTests(unittest.TestCase):
    def test_universe_parameters_follow_type_metadata_not_spelling(self):
        types = {'M': {'1': 'Level', '2': '<a href="Agda.Primitive.html#1">Level</a>',
                       '3': 'LevelUniv', '4': '(x : Level) → Type x', '5': 'Type'}}
        for position in ('1', '2'):
            self.assertIn('data-universe-level="true"', renderer.type_reference_attribute('M', position, types))
        for position in ('3', '4', '5'):
            self.assertNotIn('data-universe-level', renderer.type_reference_attribute('M', position, types))
        link = '<a data-type="M#1" data-universe-level="true">i</a>'
        resolved = renderer.resolve_type_hover_links(link, types)
        self.assertEqual(resolved.count('data-universe-level'), 1)
        self.assertEqual(renderer.resolve_type_hover_links(resolved, types), resolved)

    def render(self, snippet, refs=None, local=None, syntax=()):
        bridge = {'inline': refs or {}, 'syntax': syntax}
        return annotate_keywords(annotate_inline_code(
            '<code>' + html.escape(snippet) + '</code>',
            renderer.inline_reference_resolver(local or {}, 'Base.Prelude', bridge)), 'zh')

    def test_whole_syntax_tokens_only(self):
        self.assertEqual([token for _, _, token in inline_syntax_ranges('f : A → B = λ x → x')],
                         [':', '→', '=', 'λ', '→'])
        self.assertEqual(list(inline_syntax_ranges('LEM→Resizing x=y :: := "x : A → B"')), [])
        self.assertEqual(list(inline_syntax_ranges("'=' {- x : A {- → -} -} -- f = x")), [])
        self.assertEqual([t for _, _, t in inline_syntax_ranges('{-# OPTIONS --cubical --safe --guardedness #-}')],
                         ['OPTIONS', '--cubical', '--safe', '--guardedness'])

    def test_directive_words_are_contextual(self):
        self.assertEqual(list(inline_syntax_ranges('to from as')), [])
        keys = [t for _, _, t in inline_syntax_ranges('open import A as B renaming (f to g)')]
        self.assertIn('as', keys)
        self.assertIn('to', keys)

    def test_raw_single_line_and_marked_inline_share_help(self):
        for wrapper in ('<div class="single-line-code"><code>{}</code></div>',
                        '<span class="Agda inline-ref">{}</span>'):
            output = annotate_keywords(annotate_inline_code(wrapper.format('A × B = Σ (_ : A) B')), 'zh')
            self.assertIn('data-hover-help="="', output)
            self.assertIn('data-hover-help=":"', output)
            self.assertIn('Agda', output)
            self.assertEqual(annotate_keywords(annotate_inline_code(output), 'zh'), output)

    def test_protect_formal_code_links_strings_and_comments(self):
        for source in ('<pre class="Agda">x : A → B</pre>',
                       '<code><a href="explicit">x</a></code>',
                       '<code>&quot;x : <a href="explicit">A</a> → B&quot;</code>',
                       '<script>const x = "<code>x : A</code>";</script>'):
            self.assertEqual(annotate_inline_code(source), source)

    def test_infix_resolves_underscored_definition(self):
        output = self.render('x ≡ y', {'_≡_': ('Base.Prelude.html#10', 'Function Operator')})
        self.assertIn('href="Base.Prelude.html#10"', output)
        self.assertIn('>≡</a>', output)
        self.assertNotIn('>x</a>', output)

    def test_mixfix_pairs_and_alternative_endings(self):
        refs = {'⟨_⟩': ('Base.Prelude.html#1', 'Function'),
                '⟨_⟩isProp': ('Base.Prelude.html#2', 'Function'),
                '∥_∥₁': ('Base.Prelude.html#3', 'Datatype')}
        output = self.render('⟨ P ⟩ × ⟨ ⟨ Q ⟩ ⟩isProp × ∥ A ∥₁', refs)
        self.assertEqual(re.findall(r'href="[^"]+#(\d+)"', output), ['1', '1', '2', '1', '1', '2', '3', '3'])
        self.assertNotIn('<a', self.render('⟨ missing', refs))

    def test_ambiguous_operator_is_not_guessed(self):
        refs = {'_op_': ('Base.Prelude.html#1', 'Function'), 'op_': ('Base.Prelude.html#2', 'Function')}
        self.assertNotIn('<a', self.render('a op b', refs))

    def test_exported_renaming_is_authoritative_even_inside_prelude(self):
        refs = {'⊥': ('Base.Prelude.html#20', 'Function'), 'rec₁': ('Base.Prelude.html#30', 'Function')}
        output = self.render('⊥ rec₁', refs, {'⊥': ('Cubical.Empty.html#1', 'Datatype')})
        self.assertIn('href="Base.Prelude.html#20"', output)
        self.assertIn('href="Base.Prelude.html#30"', output)
        resolver = renderer.inline_reference_resolver({}, 'Other', {
            'inline': {}, 'by_name': {'old': ('Base.Prelude', '1', 'Function', 'old')}})
        self.assertEqual(annotate_inline_code('<code>old</code>', resolver), '<code>old</code>')

    def test_explicit_links_remain_authoritative(self):
        resolver = renderer.inline_reference_resolver({}, 'Base.Prelude', {
            'inline': {'_≡_': ('Base.Prelude.html#10', 'Function')}})
        source = '<code>x <a href="manual">≡</a> y</code>'
        self.assertEqual(annotate_inline_code(source, resolver), source)

    def test_generated_inline_links_use_shared_payload_validation(self):
        source = self.render('x ≡ y', {'_≡_': ('Base.Prelude.html#10', 'Function')})
        output = renderer.rewrite_links(source, {'Base.Prelude'}, {},
                                       {'Base.Prelude': {'10': '_≡_'}})
        self.assertNotIn('data-type=', output)
        self.assertIn('data-name="_≡_"', output)
        output = renderer.rewrite_links(source, {'Base.Prelude'}, {'Base.Prelude': {'10': 'type'}})
        self.assertEqual(output.count('data-type="Base.Prelude#10"'), 1)

    def test_compiler_syntax_notation_uses_its_real_declaration(self):
        source = ('<a class="Keyword">syntax</a> <a href="Library.html#10" class="Function">∀[]-syntax</a> '
                  '<a class="Bound">P</a> <a class="Symbol">=</a> '
                  '<a class="Function">∀[</a> <a class="Bound">x</a> <a class="Function">]</a>')
        self.assertEqual(renderer.syntax_notations(source), [('Library.html#10', ['∀[', ']'])])
        output = self.render('∀[ x ] P', {'∀[]-syntax': ('Base.Prelude.html#10', 'Function')},
                             syntax=[('∀[]-syntax', ['∀[', ']'])])
        self.assertEqual(output.count('href="Base.Prelude.html#10"'), 2)

    def test_equals_help_is_only_the_defining_equation(self):
        self.assertNotIn('记录表达式', help_html('=', 'zh'))
        self.assertNotIn('record expressions', help_html('=', 'en'))
        self.assertNotIn('レコード式', help_html('=', 'ja'))

    def test_symbols_share_one_category_across_all_rendering_paths(self):
        code = '∀ (x : A) → B = λ y → y'
        inline = annotate_inline_code('<code>' + code + '</code>')
        hover = renderer.render_type(code, {})
        formal = ('<pre class="Agda">' + ''.join(f'<a class="Symbol">{symbol}</a>'
                  for symbol in ('∀', ':', '→', '=', 'λ', '→')) + '</pre>')
        for lang in ('en', 'zh', 'ja'):
            for surface in (inline, hover, formal):
                output = annotate_keywords(surface, lang)
                self.assertEqual(output.count('syntax-symbol'), 6)
                self.assertEqual(output.count('data-hover-help='), 6)
                self.assertEqual(annotate_keywords(output, lang), output)
        word = annotate_keywords('<a class="Keyword">where</a>', 'zh')
        self.assertNotIn('syntax-symbol', word)
        self.assertIn('syntax-hover', word)

    def test_compiler_combined_symbols_preserve_single_source_anchor(self):
        output = annotate_keywords('<a id="123" class="Symbol">(λ</a><a class="Symbol">→)</a>', 'zh')
        self.assertEqual(output.count('id="123"'), 1)
        self.assertEqual(output.count('syntax-symbol'), 2)
        self.assertIn('data-hover-help="λ"', output)
        self.assertIn('data-hover-help="→"', output)
        self.assertEqual(renderer.plain_code(output), '(λ→)')
        self.assertEqual(annotate_keywords(output, 'zh'), output)

    def test_underscore_placeholder_is_not_a_mixfix_name_fragment(self):
        snippet = 'f _ (_ : A) {_} _≡_ _×_ name_part'
        self.assertEqual([t for _, _, t in inline_syntax_ranges(snippet)], ['_', '_', ':', '{', '_', '}'])
        for surface in (annotate_inline_code('<code>' + snippet + '</code>'),
                        renderer.render_type(snippet, {}),
                        '<pre class="Agda"><a class="Symbol">_</a></pre>'):
            output = annotate_keywords(surface, 'zh')
            self.assertIn('data-hover-help="_"', output)
            self.assertIn('syntax-symbol', output)
            self.assertNotIn('data-hover-help="_≡_"', output)
        for lang in ('en', 'zh', 'ja'):
            self.assertIn('language/implicit-arguments.html', help_html('_', lang))
        for aspect in ('Bound', 'Module', 'Function'):
            anonymous = annotate_keywords(f'<a id="9" href="M.html#9" class="{aspect}">_</a>', 'zh')
            self.assertIn('data-hover-help="_"', anonymous)
            self.assertIn('syntax-symbol', anonymous)
            self.assertIn('id="9" href="M.html#9"', anonymous)
        named = '<a href="M.html#10" class="Function Operator">_≡_</a>'
        self.assertEqual(annotate_keywords(named, 'zh'), named)

    def test_braces_have_help_but_no_symbolic_color(self):
        for surface in (annotate_inline_code('<code>{A : Type} {{instance}}</code>'),
                        renderer.render_type('{A : Type} {{instance}}', {}),
                        '<pre class="Agda"><a class="Symbol">{{</a><a class="Symbol">}}</a></pre>'):
            output = annotate_keywords(surface, 'zh')
            braces = re.findall(r'<a\b([^>]*)>([{}])</a>', output)
            self.assertGreaterEqual(len(braces), 4)
            for attrs, brace in braces:
                self.assertIn(f'data-hover-help="{brace}"', attrs)
                self.assertIn('Symbol syntax-hover', attrs)
                self.assertNotIn('syntax-symbol', attrs)
        self.assertNotIn('data-hover-help="{"', annotate_keywords(
            annotate_inline_code('<code>{- comment -}</code>'), 'zh'))
        pragma = '<a class="Symbol">{-#</a><a class="Symbol">#-}</a>'
        self.assertEqual(annotate_keywords(pragma, 'zh'), pragma)

    def test_semicolon_has_help_but_no_symbolic_color(self):
        for surface in (annotate_inline_code('<code>using (f; g)</code>'),
                        renderer.render_type('record { a = x; b = y }', {}),
                        '<pre class="Agda"><a class="Symbol">;</a></pre>'):
            output = annotate_keywords(surface, 'zh')
            attrs = re.search(r'<a\b([^>]*)>;</a>', output)[1]
            self.assertIn('data-hover-help=";"', attrs)
            self.assertIn('Symbol syntax-hover', attrs)
            self.assertNotIn('syntax-symbol', attrs)
        self.assertNotIn('data-hover-help=";"', annotate_keywords(
            annotate_inline_code('<code>&quot;;&quot;</code>'), 'zh'))


if __name__ == '__main__':
    unittest.main()
