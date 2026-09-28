# Archive validation

Date: 2026-09-28. These are checks of the archived source copies on the
back-merged research branch, not merely quotations of historical success.

## Scope and integrity

- All 59 archived artifacts match their manifest SHA-256 hashes. The original
  versions of the four terminology-normalized reports are exactly reconstructible
  from recorded line edits and match their separate original hashes.
- The manifest covers every original local `.agda`, `.md` and `.agda-lib`
  investigation artifact, plus the legacy modules, design note and original diff.
- All 152 relative links and heading anchors in the new entry, guides, route
  synthesis, evidence index and validation record resolve.
- Before the documentation gate repair, `git diff --exit-code main -- src
  site/reading-catalog.json` exited 0. The only subsequent difference there is
  a one-line table caption in `src/README.md`; all Agda chapter bytes and the
  reading catalog remain identical to main.
- The staged Outcrop pointer also matches main; no framework changes were made.

## Agda experiments

Sources were copied from `experiments/` to the ignored
`_build/double-negation-archive-check` directory. The compiler ran sequentially
with `AGDA_DIR` pointing at the repository registry and
`GHCRTS="-A64m -I0 -M8g"`. No other Agda process was found before starting.
Each invocation was:

```text
_build/outcrop-agda/bin/outcrop-agda -i . -i <repository>/src <Module.agda>
```

All 35 completed proof experiments exited 0. The deliberately invalid
`SameLevel.agda` exited 42 with the expected `UnequalSorts` diagnostic.
The three deep-FOL endpoints report the same underlying
`UnsupportedIndexedMatch` warning at `DeepNegativeFOL.lifted-environment`:
Fin matching does not compute on transports. This warning was not suppressed.
All preserved proof options retain `--safe`; conditional premises remain
explicit and have not been converted into new ambient axioms.

| File | Exit | Result |
| --- | --- | --- |
| [BooleanCompletion.agda](experiments/BooleanCompletion.agda) | 0 | Passed |
| [BooleanPower.agda](experiments/BooleanPower.agda) | 0 | Passed |
| [Boundary.agda](experiments/Boundary.agda) | 0 | Passed |
| [ConditionalImage.agda](experiments/ConditionalImage.agda) | 0 | Passed |
| [CoverObstructions.agda](experiments/CoverObstructions.agda) | 0 | Passed |
| [DeepFOLOmega.agda](experiments/DeepFOLOmega.agda) | 0 | Passed; known Fin computation warning |
| [DeepFOLOmegaTrees.agda](experiments/DeepFOLOmegaTrees.agda) | 0 | Passed; known Fin computation warning |
| [DeepNegativeFOL.agda](experiments/DeepNegativeFOL.agda) | 0 | Passed; known Fin computation warning |
| [DensePower.agda](experiments/DensePower.agda) | 0 | Passed |
| [ExtensionalityBoundary.agda](experiments/ExtensionalityBoundary.agda) | 0 | Passed |
| [FiniteFunctionObjects.agda](experiments/FiniteFunctionObjects.agda) | 0 | Passed |
| [FunctionObjectBoundary.agda](experiments/FunctionObjectBoundary.agda) | 0 | Passed |
| [FunctionPower.agda](experiments/FunctionPower.agda) | 0 | Passed |
| [HartogsRelationBoundary.agda](experiments/HartogsRelationBoundary.agda) | 0 | Passed |
| [InternalResizing.agda](experiments/InternalResizing.agda) | 0 | Passed |
| [ModalFullness.agda](experiments/ModalFullness.agda) | 0 | Passed |
| [ModalQuotient.agda](experiments/ModalQuotient.agda) | 0 | Passed |
| [ModalTrees.agda](experiments/ModalTrees.agda) | 0 | Passed |
| [QuantifierTransport.agda](experiments/QuantifierTransport.agda) | 0 | Passed |
| [RelationalClassifier.agda](experiments/RelationalClassifier.agda) | 0 | Passed |
| [RelationalExponential.agda](experiments/RelationalExponential.agda) | 0 | Passed |
| [RelationalFunctionBoundary.agda](experiments/RelationalFunctionBoundary.agda) | 0 | Passed |
| [RelationalLargeFunctions.agda](experiments/RelationalLargeFunctions.agda) | 0 | Passed |
| [RelationalOmega.agda](experiments/RelationalOmega.agda) | 0 | Passed |
| [RelationalPropUniverse.agda](experiments/RelationalPropUniverse.agda) | 0 | Passed |
| [RelationalSmallFunctionAudit.agda](experiments/RelationalSmallFunctionAudit.agda) | 0 | Passed |
| [RelationalTruth.agda](experiments/RelationalTruth.agda) | 0 | Passed |
| [SameLevel.agda](experiments/SameLevel.agda) | 42 | Expected universe-sort rejection |
| [SeparationBoundary.agda](experiments/SeparationBoundary.agda) | 0 | Passed |
| [SheafBoundary.agda](experiments/SheafBoundary.agda) | 0 | Passed |
| [StableRelations.agda](experiments/StableRelations.agda) | 0 | Passed |
| [StagePowerBoundary.agda](experiments/StagePowerBoundary.agda) | 0 | Passed |
| [SubcountableObstruction.agda](experiments/SubcountableObstruction.agda) | 0 | Passed |
| [SupportedImage.agda](experiments/SupportedImage.agda) | 0 | Passed |
| [TruthChoice.agda](experiments/TruthChoice.agda) | 0 | Passed |
| [UniqueExtraction.agda](experiments/UniqueExtraction.agda) | 0 | Passed |

## Earlier branch compatibility

The exact historical `V.InternalClassicality` snapshot was also tried against
current main dependencies. It exits 42 at line 96: its old `Σ[ s ∈ S ]`
notation no longer parses against the current Prelude interface. This is a
recorded compatibility failure, not silently repaired historical evidence.
The original Milestones snapshot also refers to the former publication layout.

The standalone chapter was then rechecked with the entire original source
dependency tree and library descriptor exported from commit `053e89ff`. This
check exited 251 while checking the historical V.Model dependency: the compiler
exhausted its 8 GB heap. The limit was not increased. Thus this archival run
does NOT freshly validate the old theorem even in its original source context;
the prior reported result and exact sources are preserved with this limitation.
The source staging directory was `_build/double-negation-legacy-original`;
the command was the repository compiler applied to
`src/V/InternalClassicality.lagda.md` from that directory, with the same local
Agda registry and `GHCRTS` limit used above.

The first attempt to stage the original Git snapshot used the system Python,
whose tarfile lacked the safe extraction filter argument; it failed before
compilation. Staging was rerun using the repository virtual environment.

## Repository checks

- `make milestone-lint`: exit 0; all 119 production source modules are consumed
  by Origin.
- `make docs-prose-gate spdx-gate`: exit 0.
- `.venv/bin/python -m reuse lint`: exit 0; no licensing errors.
- `git diff --cached --check`: exit 0.
- `sh .git/hooks/pre-commit`: exit 0 after the documented repairs; all
  installed pre-commit checks passed.

The first documentation lint found a typographic quotation in new prose and
the obsolete statement-label formatting in the historical Milestones source.
The quotation was corrected. Historical modules are stored as immutable
`.snapshot` evidence, with original bytes and hashes, rather than presented
as authored current Markdown chapters. Reproduction restores the original
source filenames in an ignored staging directory. The full-merge pre-commit run additionally found the baseline src/README
table missing its required caption; a single descriptive caption was added.
The glossary gate found seven occurrences of inverse-law terminology in four
historical reports. These were normalized to round-trip law terminology; the
manifest retains the exact original lines and hashes. The original branch patch
uses zero context so its blank context lines do not introduce whitespace-only
lines in the archive. No gate or assertion was disabled or weakened.

No full Origin typecheck or website/browser build was required for this
archive: mathematical source, public theorem statements, catalog and Outcrop
are identical to the recorded main baseline. The proof replay covers the
newly preserved research separately. No universal no-go theorem or completed
internal ZF model follows from these checks.
