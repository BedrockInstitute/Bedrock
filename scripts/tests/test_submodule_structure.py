"""The fold inventory follows Agda's code stream, not prose mentions of modules."""

import importlib.util
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    'submodule_structure', ROOT / 'scripts/site/submodule_structure.py')
import sys
structure = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = structure
SPEC.loader.exec_module(structure)


class SubmoduleStructureTests(unittest.TestCase):
    def test_private_header_identifies_the_actual_module_line(self):
        code = 'private module BooleanCodes where\n'
        line = structure.module_header_line(code)
        self.assertEqual(line[0], 'private module BooleanCodes where')
        self.assertEqual(line.start(), 0)
        self.assertIsNone(structure.module_header_line('private\n  module Broken where'))
        self.assertIsNone(structure.module_header_line('private\nmodule Broken where'))
        self.assertIsNone(structure.module_header_line('private\n  value = result'))

    def test_aliases_multifence_headers_and_nesting(self):
        source = '''```agda
module Example where
module Alias = Other
module Outer (x : A)
```
Some exposition about x.
```agda
  (y : B x) where
  value = x
  module Inner where
    result = value
```
More prose.
```agda
  after = Inner.result
next = Outer.after
```
'''
        modules = structure.submodules(source)
        self.assertEqual([(m.depth, m.header_lines) for m in modules],
                         [(1, 2), (2, 1)])
        self.assertEqual(source[modules[0].start:modules[0].start + 12],
                         'module Outer')
        self.assertIn('after = Inner.result',
                      source[modules[0].start:modules[0].body_end])
        self.assertNotIn('next = Outer.after',
                         source[modules[0].start:modules[0].body_end])

if __name__ == '__main__':
    unittest.main()
