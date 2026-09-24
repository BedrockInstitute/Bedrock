"""The universe lens must preserve grouping and never reinterpret ordinary syntax."""
import json
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[2]


class UniverseLevelTests(unittest.TestCase):
    def render(self, values, certify=True):
        if not shutil.which('node'):
            self.skipTest('Node is required for the universe notation parser')
        source = (ROOT / 'site/static/universe-levels.js').read_text()
        core = source[source.index('  var operations'):source.index('  function textMap')]
        script = core + '\nconsole.log(JSON.stringify(' + json.dumps(values, ensure_ascii=False) + '''.map(text => {
          const tokens = tokenize(text), result = parse(tokens, 0, () => CERTIFY, false);
          return result && result.end === tokens.length ? format(result) : null;
        })));'''.replace('CERTIFY', 'true' if certify else 'false')
        return json.loads(subprocess.check_output(['node', '-e', script], text=True))

    def test_recursive_precedence_without_algebraic_simplification(self):
        self.assertEqual(self.render([
            '(ℓ-max ℓ-zero (ℓ-suc ℓ))', '(ℓ-suc (ℓ-max ℓ₁ ℓ₂))',
            'ℓ-suc (ℓ-suc ℓ)', 'ℓ-max (ℓ-max ℓ₁ ℓ₂) ℓ₃',
            'ℓ-suc ℓ-zero', 'ℓ-max ℓ-zero ℓ-zero', '(ℓ-max α β)',
        ]), ['0 ⊔ ℓ⁺', '(ℓ₁ ⊔ ℓ₂)⁺', 'ℓ⁺⁺', 'ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃', '0⁺', '0 ⊔ 0', 'α ⊔ β'])

    def test_incomplete_or_ordinary_syntax_is_not_a_level(self):
        inputs = ['0 ⊔ ℓ⁺', 'ℓ-max ℓ', 'ℓ-suc', 'ℓ', '(ℓ-max ℓ₁ ℓ₂',
                  'ℓ-suc (A → B)', 'ℓ-max ℓ₁ ℓ₂ trailing', 'ℓ-maximal ℓ₁ ℓ₂']
        self.assertEqual(self.render(inputs), [None] * len(inputs))

    def test_operator_identity_is_required(self):
        self.assertEqual(self.render(['ℓ-max ℓ-zero (ℓ-suc ℓ)', 'ℓ-zero'], False), [None, None])

    def test_submodule_end_does_not_retain_statement_gap(self):
        css = (ROOT / 'site/static/bedrock.css').read_text()
        self.assertIn('.submodule-fold > .submodule-fold-content > :last-child { margin-bottom: 0; }', css)

    def test_level_font_is_self_hosted_and_not_enlarged(self):
        css = (ROOT / 'site/static/appearance.css').read_text()
        self.assertIn('font: 400 1em/1.15 "Bedrock Universe Levels"', css)
        self.assertNotIn('Cambria Math', css)
        self.assertIn('font-synthesis: none', css)
        font = ROOT / 'site/static/fonts/BedrockUniverseLevels-Regular.woff2'
        self.assertEqual(font.read_bytes()[:4], b'wOF2')
        self.assertLess(font.stat().st_size, 40000)

    def test_conventional_level_suffixes_and_identifier_boundaries(self):
        source = (ROOT / 'site/static/universe-levels.js').read_text()
        core = source[source.index('  function levelNamePattern'):source.index('  function markConventionalLevels')]
        values = ["ℓ ℓ' ℓ′ ℓ″ ℓ‴ ℓ⁗ ℓ1 ℓ₁₂ ℓ² ℓ₁′ ℓ'₂", 'ℓ-max ℓ-suc ℓ-zero fooℓ ℓfoo ℓ₁x']
        script = core + '\nconsole.log(JSON.stringify(' + json.dumps(values, ensure_ascii=False) + '.map(s => Array.from(s.matchAll(levelNamePattern()), m => m[0]))));'
        self.assertEqual(json.loads(subprocess.check_output(['node', '-e', script], text=True)),
                         [["ℓ", "ℓ'", 'ℓ′', 'ℓ″', 'ℓ‴', 'ℓ⁗', 'ℓ1', 'ℓ₁₂', 'ℓ²', 'ℓ₁′', "ℓ'₂"], []])


if __name__ == '__main__':
    unittest.main()
