# Double-negation investigation: archive and reproduction

The [root entry](../../DOUBLE-NEGATION.md) fixes the objective and current
status. [ROUTES.md](ROUTES.md) reconciles all explored approaches. This is
research evidence, not permanent application configuration or a completed
formalization of internal ZF.

## Preserved material

- `experiments/`: every original Agda experiment and its library descriptor,
  copied byte-for-byte from `_build/double-negation-investigation`.
- `reports/`: every investigation report, plus the original untracked
  `dev/DOUBLE-NEGATION.md` as `INITIAL-FEASIBILITY.md`. Seven historical
  occurrences of inverse-law terminology are normalized to the current glossary;
  original lines and hashes are retained for exact reconstruction in the manifest.
- `legacy/`: both mathematical modules from research commit `053e89ff`, stored
  as immutable `.snapshot` artifacts, not current textbook Markdown chapters.
  The complete original branch diff also preserves its reading-catalog changes.
  The old Milestones entry and internal classicality chapter are preserved
  independently of main's newer Origin and teaching layout.
- [MANIFEST.json](MANIFEST.json): SHA-256 hashes and original locations of
  all preserved artifacts, including reversible terminology edits; external
  download provenance is recorded separately.
- [EVIDENCE.md](EVIDENCE.md): exhaustive links and classification.
- [VALIDATION.md](VALIDATION.md): fresh archive checks and known limitations.

The old reports retain their original `_build/` paths, machine-specific
compiler commands, line references and historical state descriptions. Use
this guide for reproducible paths. A statement that a file was untracked or
that no source changed describes its original experiment, not this archival
commit. Historical statements about a completed relational resizing proof
have the restricted meaning explained in ROUTES.md; they do not establish
the original deep-FOL-to-generic-resizing implication.

The third-party Palmgren PDF and its text extraction remain local downloads.
Their source URL and hashes are recorded, but they are not redistributed in
this archive. Referenced papers, including other external formalizations,
were not collectively checked by Agda; source review and machine checking
are distinguished in the reports.

## Reproduce the proof evidence

Use the repository-pinned compiler and library registry described in
[the environment guide](../../site/AGDA-ENVIRONMENT.md). Initialize Outcrop and
run `make bootstrap` first if the toolchain is absent. Do not install a global
Agda configuration or increase the 8 GB heap limit.

To keep generated interfaces outside the archive, copy the preserved sources
to an ignored build directory. From the repository root:

```sh
mkdir -p _build/double-negation-replay
cp dev/double-negation/experiments/*.agda _build/double-negation-replay/
cp dev/double-negation/experiments/boundary.agda-lib _build/double-negation-replay/
```

For the deep first-order endpoint, run from the repository root:

```sh
repo_root="$PWD"
cd _build/double-negation-replay
AGDA_DIR="$repo_root/_build/agda-home" GHCRTS='-A64m -I0 -M8g' \
  "$repo_root/_build/outcrop-agda/bin/outcrop-agda" \
  -i . -i "$repo_root/src" DeepFOLOmegaTrees.agda
```

Other endpoints are compiled by replacing the last filename. To replay every
completed experiment, iterate over `*.agda` but exclude `SameLevel.agda`.
Run sequentially, and first verify that there is capacity under the repository's
maximum of two Agda processes across all worktrees.

`SameLevel.agda` is an intentionally ill-typed counterexample: expect exit 42
and a universe-sort mismatch. Its rejection establishes a fact about that
expression, not a proof that every same-level construction is impossible.
Do not include it in a module importing all successful experiments.

The deep-FOL sources have a known `UnsupportedIndexedMatch` warning in
`DeepNegativeFOL.lifted-environment`. This concerns computation on transports
for indexed Fin matching; it is not an unsolved meta, and the archive does not
suppress it. Preserve this limitation when using the experiment.

To inspect the earlier ordinary-satisfaction result, stage
`legacy/V/InternalClassicality.lagda.md.snapshot` under a separate ignored directory
with the same `V/` layout, remove the `.snapshot` suffix in that staging
directory, and include that directory before `src`. This compatibility check currently
fails on the old Sigma notation; see [VALIDATION.md](VALIDATION.md). For faithful
reproduction, stage the source tree and library descriptor from commit
`053e89ff` together and check the standalone chapter there. The full
old `Milestones.lagda.md.snapshot` is an exact historical snapshot; some old module names
were retired on main. Its reproducible original context is commit `053e89ff`.
Do not confuse compilation of the standalone chapter against current sources
with validation of the entire old textbook snapshot.

## Archive integrity

The manifest hashes preserve the distinction between original evidence and
new synthesis. This command checks every archived original:

```sh
python3 - <<'PY'
import hashlib, json
from pathlib import Path
root = Path('dev/double-negation')
manifest = json.loads((root / 'MANIFEST.json').read_text())
for entry in manifest['files']:
    path = root / entry['path']
    assert hashlib.sha256(path.read_bytes()).hexdigest() == entry['sha256'], path
    if 'terminology_edits' in entry:
        lines = path.read_text().splitlines(keepends=True)
        for edit in entry['terminology_edits']:
            assert lines[edit['line'] - 1] == edit['archived']
            lines[edit['line'] - 1] = edit['original']
        original = ''.join(lines).encode()
        assert hashlib.sha256(original).hexdigest() == entry['original_sha256']
print('All archive hashes and reconstructed original hashes match.')
PY
```

Compilation success proves the exported signatures under their explicit
parameters. It does not discharge conditional cover, support, subcountability
or small-classifier assumptions. No historical or fresh validation is evidence
that the full internal ZF migration has been achieved.
