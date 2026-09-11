"""Source fidelity and layout invariants for the chapter dependency map."""

import importlib.util
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'site'))
spec = importlib.util.spec_from_file_location(
    'depmap', Path(__file__).resolve().parents[1] / 'site/gen-depmap.py')
depmap = importlib.util.module_from_spec(spec)
spec.loader.exec_module(depmap)


class DependencyMapTests(unittest.TestCase):
    def test_imports_ignore_prose_and_other_fences(self):
        source = 'import Ghost\n```text\nimport Other\n```\n```agda\nopen   import Real\n```\n'
        self.assertEqual(depmap.imports(source), ['Real'])

    def test_reduction_preserves_a_diamond(self):
        edges = [('A', 'B'), ('A', 'C'), ('B', 'D'), ('C', 'D'), ('A', 'D')]
        self.assertEqual(depmap.reduced_edges('ABCD', edges), edges[:-1])

    def test_stages_follow_catalog_language_and_code(self):
        source = ('<!--en-->\n## Beginning\n<!--zh-->\n## 开始\n<!--/-->\n'
                  'import Ghost\n```agda\nimport A\n```\n')
        stages, membership = depmap.teaching_stages(source, 'zh')
        self.assertEqual(stages, [{'key': '0', 'label': '开始'}])
        self.assertEqual(membership, {'A': '0'})

    def test_layouts_preserve_all_nodes_and_downward_edges(self):
        nodes = {'A', 'B', 'C', 'Milestones'}
        edges = [('A', 'B'), ('A', 'C'), ('B', 'Milestones'), ('C', 'Milestones')]
        order = {'Milestones': 1, 'A': 2, 'B': 3, 'C': 4}
        depth = {'A': 0, 'B': 1, 'C': 1, 'Milestones': 2}
        stages = [{'key': '0', 'label': 'Preview'}, {'key': '1', 'label': 'Proof'}]
        membership = {'Milestones': '0', 'A': '1', 'B': '1', 'C': '1'}
        diagrams = depmap.layouts(nodes, edges, order, depth, list(sorted(nodes)), stages, membership)
        for name, diagram in diagrams.items():
            positions = diagram['positions']
            self.assertEqual(set(positions), nodes, name)
            for a, b in edges:
                self.assertGreater(positions[b]['y'], positions[a]['y'] + 34, name)
            for a in nodes:
                x, y = positions[a]['x'], positions[a]['y']
                self.assertGreaterEqual(x, 0)
                self.assertLessEqual(x + 128, diagram['width'])
                self.assertLessEqual(y + 34, diagram['height'])
                for b in nodes - {a}:
                    q = positions[b]
                    self.assertTrue(abs(y - q['y']) >= 34 or abs(x - q['x']) >= 128, name)


if __name__ == '__main__':
    unittest.main()
