"""A malformed future figure must fail before it reaches the rendered book."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'site'))
from diagram_style import check_text, path_endpoints, check_stylesheet

VALID = '''<figure class="book-diagram" id="fig-example" aria-describedby="fig-example-caption">
<div class="diagram-panel">
<svg viewBox="0 0 200 100" aria-hidden="true" focusable="false">
<path class="diagram-path" d="M20 50 Q100 0 180 50"/>
<circle class="diagram-point" cx="20" cy="50" r="4"/>
<circle class="diagram-point" cx="180" cy="50" r="4"/>
</svg>
</div>
<figcaption id="fig-example-caption">
<!--en-->
A path between two elements.
<!--zh-->
两个元素之间的路径。
<!--ja-->
二つの要素の間のパス。
<!--/-->
</figcaption>
</figure>'''


class DiagramStyleTests(unittest.TestCase):
    def test_diagram_relations_cannot_borrow_navigation_link_colour(self):
        for selector in ('.hlevel-link', '.book-diagram .relation', '.new-comparison-arrow'):
            self.assertTrue(check_stylesheet(selector + ' { color: var(--link-color); }',
                                            {'new-comparison-arrow'}))
        self.assertTrue(check_stylesheet('.book-diagram { --diagram-relation-color: var(--link-color); }'))
        self.assertEqual(check_stylesheet('.book-diagram .diagram-implication { color: var(--diagram-relation-color); }'), [])

    def test_actual_links_in_figures_keep_their_link_colour(self):
        for selector in ('.book-diagram a', '.book-diagram a:hover', '.book-diagram .term-ref'):
            self.assertEqual(check_stylesheet(selector + ' { color: var(--link-color); }'), [])

    def test_shared_figure_passes(self):
        self.assertEqual(check_text(VALID), [])

    def test_frame_contains_content_but_not_caption(self):
        framed = VALID.replace('class="diagram-panel"', 'class="diagram-framed"')
        self.assertEqual(check_text(framed), [])
        self.assertTrue(check_text(VALID.replace('class="book-diagram"',
                                                 'class="book-diagram diagram-framed"')))
        self.assertTrue(check_text(framed.replace('</div>\n<figcaption', '\n<figcaption')
                                   .replace('</figcaption>', '</figcaption></div>')))
        self.assertTrue(check_text(VALID.replace('<figcaption ', '<figcaption class="diagram-framed" ')))

    def test_framed_figure_has_one_content_wrapper(self):
        framed = VALID.replace('class="diagram-panel"', 'class="diagram-framed"')
        self.assertTrue(check_text(framed.replace('<figcaption', '<div>Loose content</div><figcaption')))

    def test_missing_endpoint_fails(self):
        self.assertTrue(check_text(VALID.replace('cx="180"', 'cx="179"')))

    def test_ad_hoc_appearance_and_arrowheads_fail(self):
        for attribute in ('stroke="red"', 'marker-end="url(#arrow)"',
                          'stroke-linecap="square"', 'fill-opacity="0.2"',
                          'style="border:2px solid red"', 'style="--diagram-point-fill:red"'):
            with self.subTest(attribute=attribute):
                self.assertTrue(check_text(VALID.replace('<path ', '<path '+attribute+' ')))

    def test_higher_path_does_not_require_ordinary_endpoints(self):
        self.assertEqual(check_text(VALID.replace('class="diagram-path"',
                                                 'class="diagram-higher-path"')), [])

    def test_refl_can_be_a_single_point(self):
        start = VALID.index('<path ')
        end = VALID.index('/>', start) + 2
        self.assertEqual(check_text(VALID[:start] + VALID[end:]), [])

    def test_caption_needs_all_three_languages_and_correct_reference(self):
        for broken in (VALID.replace('<!--ja-->', '<!--fr-->'),
                       VALID.replace('aria-describedby="fig-example-caption"', ''),
                       VALID.replace('class="book-diagram"', 'class="custom-figure"')):
            self.assertTrue(check_text(broken))

    def test_nested_decorative_panels_fail(self):
        self.assertTrue(check_text(VALID.replace('<svg ', '<div class="diagram-panel"><svg ')
                                  .replace('</svg>', '</svg></div>')))

    def test_adjacent_figures_need_prose(self):
        second = VALID.replace('fig-example', 'fig-second')
        self.assertTrue(check_text(VALID + '\n' + second))
        self.assertTrue(check_text(VALID + '\n$$A \\to B$$\n' + second))
        self.assertEqual(check_text(VALID + '\nThe next construction uses this path.\n' + second), [])

    def test_code_examples_are_not_live_figures(self):
        self.assertEqual(check_text('```html\n<figure>Example</figure>\n```'), [])

    def test_figure_cannot_be_followed_by_agda(self):
        for code in ('```agda\nx = y\n```', '~~~agda\nx = y\n~~~',
                     '````agda\nx = y\n````', '```{.agda}\nx = y\n```'):
            with self.subTest(code=code):
                errors = check_text(VALID + '\n\n' + code)
                self.assertEqual(sum('immediately follow a figure' in e for e in errors), 3)

    def test_comments_and_fold_wrappers_do_not_separate_figure_from_code(self):
        for gap in ('<!-- hidden -->', '</div>\n</details>\n<div>',
                    '<details open>\n<summary>\n', '::: {.wrapper}\n'):
            self.assertTrue(check_text(VALID + '\n' + gap + '\n```agda\nx = y\n```'))

    def test_figure_code_spacing_is_checked_in_each_language(self):
        gap = '\n<!--en-->\nExplanation.\n<!--zh-->\n\n<!--ja-->\n説明。\n<!--/-->\n'
        errors = check_text(VALID + gap + '```agda\nx = y\n```')
        self.assertEqual(len(errors), 1)
        self.assertIn(': zh: Agda code', errors[0])
        self.assertTrue(errors[0].startswith(str((VALID + gap).count('\n') + 1) + ':'))

    def test_explanatory_prose_or_code_before_figure_passes(self):
        code = '\n```agda\nx = y\n```\n'
        self.assertEqual(check_text(VALID + '\nExplanation of the code.\n' + code), [])
        self.assertEqual(check_text(code + VALID), [])
        self.assertEqual(check_text('```html\n</figure>\n```\n' + code), [])

    def test_line_guide_uses_the_shared_role(self):
        self.assertEqual(check_text(VALID.replace(
            '</svg>', '<line class="diagram-guide" x1="0" y1="0" x2="20" y2="20"/></svg>')), [])

    def test_caption_cannot_precede_the_diagram(self):
        start = VALID.index('<figcaption')
        end = VALID.index('</figcaption>') + len('</figcaption>')
        caption = VALID[start:end]
        source = VALID[:start] + VALID[end:]
        source = source.replace('<div class="diagram-panel">', caption + '<div class="diagram-panel">')
        self.assertTrue(check_text(source))

    def test_open_subpaths_have_independent_endpoints(self):
        self.assertEqual(path_endpoints('M0 0 H10 M20 20 Q30 40 50 60'),
                         [(0, 0), (10, 0), (20, 20), (50, 60)])
        with self.assertRaises(ValueError):
            path_endpoints('M0 0 L10 10 Z')


if __name__ == '__main__':
    unittest.main()
