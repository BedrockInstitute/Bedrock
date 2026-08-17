#!/usr/bin/env python3
"""Pins the scripts/ directory layout LJ-1.295 ruled (owner's option C, 2026-08-15).

Three mechanical answers to C-48 ("a policy that only a document states is not
enforced"), and one mechanical form of the placement rule this repository
states in scripts/README.md:

  1. The set of directories under scripts/ is pinned. A new bucket (a `misc/`
     is the shape a wrong choice hides in, C-43) cannot appear silently; it
     must edit this suite with a reason.
  2. The flat .py set is pinned to the two cross-group modules. A new flat
     script must either have importers across groups (and then it belongs in
     this list, with them named) or join a group directory.
  3. Every tracked file under scripts/ outside tests/ and git-hooks/ must be
     named in scripts/README.md by the path it actually holds, so the README
     cannot drift from the tree without this suite going red.
  4. Each flat module is IMPORTED by scripts in at least two distinct groups,
     which is the placement rule ("the shallowest directory containing every
     importer" resolves to scripts/ itself) checked by machine rather than
     asserted in prose.

The GROUP a new script belongs to stays a review decision; no checker decides
it, and scripts/README.md says so.

Run: python3 scripts/tests/test_scripts_layout.py   (or: make test)
"""

import re
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
SCRIPTS = ROOT / "scripts"

# `pod` joins the set in the same commit that creates scripts/pod/, which is cutover
# step 4 of dev/memos/L9-pod-program-design.md. The POD program is not a gate: it runs
# the route, and its files carry the six-fact recorder, the fact 3 witness meter and the
# closure check that acceptance conjunct 3 calls.
GROUPS = {"gate", "dispatch", "measure", "site", "ops", "pod"}
FIXED = {"tests", "git-hooks", "__pycache__"}
FLAT_MODULES = {"agents_tree.py", "repo_root.py"}


def rglob_all_py():
    return [p for p in SCRIPTS.rglob("*.py") if "__pycache__" not in p.parts]


class Layout(unittest.TestCase):
    def test_directory_set_is_pinned(self):
        found = {p.name for p in SCRIPTS.iterdir() if p.is_dir()}
        self.assertEqual(found, GROUPS | FIXED,
                         "a new directory under scripts/ must edit this suite "
                         "with a reason; a `misc/` bucket is C-43's shape")

    def test_flat_py_set_is_pinned(self):
        found = {p.name for p in SCRIPTS.glob("*.py")}
        self.assertEqual(found, FLAT_MODULES,
                         "a flat .py must be imported across groups; otherwise "
                         "it joins a group directory")

    def test_readme_table_matches_every_group_directory(self):
        readme = (SCRIPTS / "README.md").read_text(encoding="utf-8")
        row_re = re.compile(
            r"^\| `scripts/([a-z]*)/?`[^|]*\|[^|]*\| ([^|]*) \|$", re.M)
        documented: dict[str, set[str]] = {}
        for m in row_re.finditer(readme):
            group, members = m.group(1), m.group(2)
            documented.setdefault(group, set()).update(
                re.findall(r"`([A-Za-z0-9_.-]+\.(?:py|sh|html))`", members))
        self.assertEqual(set(documented), GROUPS | {""},
                         "the README layout table must carry one row per group "
                         "directory (and one flat row)")
        for group in GROUPS:
            on_disk = {p.name for p in (SCRIPTS / group).iterdir()
                       if p.is_file() and "__pycache__" not in p.name}
            self.assertEqual(documented[group], on_disk,
                             f"scripts/{group}/ and the README table disagree")
        flat_doc = documented.get("", set())
        self.assertEqual(flat_doc, FLAT_MODULES,
                         "the flat row must list exactly the cross-group modules")

    def test_flat_modules_have_importers_in_two_groups(self):
        for mod in sorted(FLAT_MODULES):
            stem = mod[:-3]
            groups = set()
            pattern = re.compile(rf"^\s*(import {stem}\b|from {stem} import)")
            for p in rglob_all_py():
                try:
                    text = p.read_text(encoding="utf-8")
                except OSError:
                    continue
                if p.name == mod or p.parent.name == "tests":
                    continue
                if pattern.match(text) or any(pattern.match(l)
                                              for l in text.splitlines()):
                    groups.add(p.parent.name if p.parent != SCRIPTS else "flat")
            self.assertGreaterEqual(
                len(groups - {"flat"}), 2,
                f"{mod} is flat but imported from fewer than two groups; "
                f"move it to the shallowest directory holding every importer")


if __name__ == "__main__":
    unittest.main(verbosity=2)
