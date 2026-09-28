# Evidence inventory

Every entry below is linked to its preserved source. [MANIFEST.json](MANIFEST.json)
records the original location and SHA-256 hashes, including reversible glossary
normalizations in four historical reports. See [ROUTES.md](ROUTES.md) for
the mathematical interpretation and [VALIDATION.md](VALIDATION.md) for fresh checks.

## Proof sources

These are conditional or unconditional theorems exactly as their signatures state.
A successful check does not discharge explicit premises.

| Module | Classification |
| --- | --- |
| [BooleanCompletion](experiments/BooleanCompletion.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [BooleanPower](experiments/BooleanPower.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [Boundary](experiments/Boundary.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [ConditionalImage](experiments/ConditionalImage.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [CoverObstructions](experiments/CoverObstructions.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [DeepFOLOmega](experiments/DeepFOLOmega.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [DeepFOLOmegaTrees](experiments/DeepFOLOmegaTrees.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [DeepNegativeFOL](experiments/DeepNegativeFOL.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [DensePower](experiments/DensePower.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [ExtensionalityBoundary](experiments/ExtensionalityBoundary.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [FiniteFunctionObjects](experiments/FiniteFunctionObjects.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [FunctionObjectBoundary](experiments/FunctionObjectBoundary.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [FunctionPower](experiments/FunctionPower.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [HartogsRelationBoundary](experiments/HartogsRelationBoundary.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [InternalResizing](experiments/InternalResizing.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [ModalFullness](experiments/ModalFullness.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [ModalQuotient](experiments/ModalQuotient.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [ModalTrees](experiments/ModalTrees.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [QuantifierTransport](experiments/QuantifierTransport.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [RelationalClassifier](experiments/RelationalClassifier.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [RelationalExponential](experiments/RelationalExponential.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [RelationalFunctionBoundary](experiments/RelationalFunctionBoundary.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [RelationalLargeFunctions](experiments/RelationalLargeFunctions.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [RelationalOmega](experiments/RelationalOmega.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [RelationalPropUniverse](experiments/RelationalPropUniverse.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [RelationalSmallFunctionAudit](experiments/RelationalSmallFunctionAudit.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [RelationalTruth](experiments/RelationalTruth.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [SameLevel](experiments/SameLevel.agda) | Intentional universe-sort rejection; not a completed proof |
| [SeparationBoundary](experiments/SeparationBoundary.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [SheafBoundary](experiments/SheafBoundary.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [StableRelations](experiments/StableRelations.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [StagePowerBoundary](experiments/StagePowerBoundary.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [SubcountableObstruction](experiments/SubcountableObstruction.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [SupportedImage](experiments/SupportedImage.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [TruthChoice](experiments/TruthChoice.agda) | Preserved safe Agda experiment; see signature for assumptions |
| [UniqueExtraction](experiments/UniqueExtraction.agda) | Preserved safe Agda experiment; see signature for assumptions |

## Historical reports

These are original dated records; the root entry and ROUTES.md supersede their
old goal-state labels and restart suggestions.

- [Recursive equality, quotient carriers and direct interpretation](reports/ALTERNATIVE-ROUTES.md)
- [Small Boolean completion and the stable-proposition classifier](reports/COMPLETION-BOUNDARY.md)
- [Quotients and countable candidate families](reports/COVER-OBSTRUCTIONS.md)
- [A vertex-cardinality obstruction for the modest-family universe](reports/CUBICAL-ASSEMBLY-AUDIT.md)
- [Returning to deep first-order excluded middle](reports/DEEP-FOL-OMEGA.md)
- [Arbitrary powersets and small double-negation-dense covers](reports/DENSE-POWER-AUDIT.md)
- [Function objects and modal binary Fullness](reports/FUNCTION-OBJECT-BOUNDARY.md)
- [The explicit internal-resizing rule and its consumers](reports/INTERNAL-RESIZING-INTERFACE.md)
- [Constructible power sets, stage bounds, and Hartogs](reports/L-STAGE-BOUNDARY.md)
- [Powerset audit for recursive stable equality](reports/POWERSET-AUDIT.md)
- [Boolean relation functions and modal power sets](reports/RELATIONAL-EXPONENTIAL.md)
- [Relational function rules and the remaining size obligation](reports/RELATIONAL-FUNCTION-SIZE.md)
- [A checked relational proposition universe and resizing isomorphism](reports/RELATIONAL-PROP-UNIVERSE.md)
- [Relational truth, quantifier transport, and the remaining data interface](reports/RELATIONAL-QUANTIFIERS.md)
- [Direct separation and unique witness extraction](reports/SEPARATION-AND-EXTRACTION.md)
- [Subcountability obstructs stable predicate covers](reports/SUBCOUNTABLE-OBSTRUCTION.md)
- [Replacement images without extracting individual values](reports/SUPPORTED-IMAGE.md)
- [Double-negation migration: assumption boundary and feasibility](reports/INITIAL-FEASIBILITY.md)

- [Original internal classicality design note](reports/ORIGINAL-INTERNAL-CLASSICALITY.md)

## Earlier research branch

Both snapshots are exact bytes from commit `053e89ff` and remain in the branch history.

- [legacy/Milestones.lagda.md.snapshot](legacy/Milestones.lagda.md.snapshot)
- [legacy/V/InternalClassicality.lagda.md.snapshot](legacy/V/InternalClassicality.lagda.md.snapshot)

- [Complete original branch diff, including its old reading catalog](legacy/original-branch.patch)

## Library and external-source provenance

- [Original local Agda library descriptor](experiments/boundary.agda-lib).
- Palmgren, [universe notes](https://www2.math.uu.se/~palmgren/universe.pdf):
  local download and text-extraction hashes are recorded in the manifest.
  The third-party files are not redistributed.
- Other primary sources and their exact applicable hypotheses are cited in the
  historical reports. A citation is not a machine-checked model or an imported axiom.
