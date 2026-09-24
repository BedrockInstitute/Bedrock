"""Formatting private modules must not publish their siblings."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('private_migration', ROOT / 'scripts/migrate-private-modules.py')
migration = importlib.util.module_from_spec(spec)
spec.loader.exec_module(migration)


class PrivateMigrationTests(unittest.TestCase):
    def test_aliases_and_private_values_keep_separate_private_scopes(self):
        source = ('```agda\nmodule Test where\nprivate\n  module A = M\n    argument\n'
                  '  module B = N\n  x = A.x\n  y = B.y\npublicResult = x\n```\n')
        result = migration.migrate(source)
        self.assertIn('private module A = M\n          argument', result)
        self.assertIn('private module B = N\nprivate\n  x = A.x\n  y = B.y', result)
        self.assertIn('\npublicResult = x\n', result)
        self.assertEqual(migration.migrate(result), result)

    def test_fold_declaration_moves_modifier_across_fences(self):
        source = ('```agda\nmodule Test where\n```\n\n```agda\nprivate\n```\n\n'
                  '<details><summary>\n```agda\n  module M\n    (A : Set) where\n```\n'
                  '</summary>\nProse.\n```agda\n    f : A → A\n    f x = x\n```\n</details>\n')
        result = migration.migrate(source)
        self.assertIn('private module M (A : Set) where', result)
        self.assertIn('```agda\n  f : A → A\n  f x = x\n```', result)
        self.assertNotIn('```agda\n```', result)
        self.assertEqual(result.count('<details>'), 1)
        self.assertEqual(migration.migrate(result), result)

    def test_ordinary_private_block_is_unchanged(self):
        source = '```agda\nmodule Test where\nprivate\n  x = y\n```\n'
        self.assertEqual(migration.migrate(source), source)

    def test_whole_library_has_completed_the_migration(self):
        for path in (ROOT / 'src').rglob('*.lagda.md'):
            text = path.read_text()
            self.assertEqual(migration.migrate(text), text, str(path))


if __name__ == '__main__':
    unittest.main()
