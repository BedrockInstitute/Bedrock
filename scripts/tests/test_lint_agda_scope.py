"""The instance SPDX rule must not cross repository/dependency boundaries."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location(
    'lint_agda_scope', Path(__file__).resolve().parents[1] / 'gate/lint-agda.py')
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)
HEADER = '-- SPDX-License' + '-Identifier: BSD-3-Clause\n'


class SpdxScopeTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.patcher = patch.object(gate, 'ROOT', self.root)
        self.patcher.start()
        self.addCleanup(self.patcher.stop)

    def write(self, name, text=HEADER):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def test_untracked_owned_files_and_hidden_config_are_checked(self):
        files = [self.write('src/New.lagda.md'), self.write('site/new.json'),
                 self.write('.github/new.yml')]
        # No Git index is needed: new source/config must not escape the gate.
        self.assertEqual(len(gate.check_spdx()), 3)
        self.assertEqual(sorted(gate.check_spdx()), sorted(gate.check_spdx(files)))

    def test_excluded_directories_at_every_depth_in_both_modes(self):
        files = []
        for directory in gate.SPDX_EXCLUDED_DIRS:
            for prefix in ('', 'dev/probe/'):
                if prefix and directory == '.git':
                    continue  # Nested repository pruning has its own test.
                files.append(self.write(prefix + directory + '/foreign.agda'))
        visited = []
        walk = gate.os.walk
        def recording_walk(*args, **kwargs):
            for row in walk(*args, **kwargs):
                visited.append(Path(row[0]))
                yield row
        with patch.object(gate.os, 'walk', recording_walk):
            self.assertEqual(list(gate.spdx_owned_files()), [])
        self.assertEqual(visited, [self.root, self.root / 'dev', self.root / 'dev/probe'])
        self.assertEqual(gate.check_spdx(files), [])
        self.assertTrue(all(path.read_text() == HEADER for path in files))

    def test_nested_repositories_and_worktrees_are_not_traversed(self):
        checkout = self.write('dev/another-name/.git/config', '')
        worktree = self.write('outcrop/.git', 'gitdir: elsewhere\n')
        foreign = [self.write(str(checkout.parent.parent.relative_to(self.root)) + '/code.agda'),
                   self.write(str(worktree.parent.relative_to(self.root)) + '/code.agda')]
        self.write('src/ours.agda')
        self.assertEqual(len(gate.check_spdx()), 1)
        self.assertEqual(gate.check_spdx(foreign), [])

    def test_symlinks_cannot_escape_or_reenter_excluded_roots(self):
        target = self.write('_build/dependencies/foreign.agda')
        directory = self.root / 'linked-dependency'
        directory.symlink_to(target.parent, target_is_directory=True)
        link = self.root / 'linked.agda'
        link.symlink_to(target)
        self.assertEqual(gate.check_spdx(), [])
        self.assertEqual(gate.check_spdx([link, directory / target.name]), [])
        self.assertEqual(gate.check_spdx([self.root.parent / 'outside.agda']), [])

    def test_reuse_metadata_is_exempt_but_header_rule_remains(self):
        self.write('REUSE.toml')
        self.write('src/not-a-header.agda', '\n' * 30 + HEADER)
        self.write('src/header.agda', '\n' * 29 + HEADER)
        hits = gate.check_spdx()
        self.assertEqual(len(hits), 1)
        self.assertTrue(hits[0].startswith('src/header.agda:'))


if __name__ == '__main__':
    unittest.main()
