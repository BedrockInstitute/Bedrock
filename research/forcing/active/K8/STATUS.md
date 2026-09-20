# K8 implementation status

Status: **complete at the isolated K8 proof-probe gate**.

The acceptance scope is the K8 combinatorial branch in
`dev/literature/cohen-implementation-roadmap-2026-09.md`: internal finite
partial functions, the uncountable delta-system lemma, actual Cohen CCC₂,
coordinate density and certified Boolean-completion CCC transfer. K9 and later
forcing/model theorems are not part of this checkpoint.

## Public endpoints

- `FullDeltaSystem.AtOmega.finite-delta`: the ground-ZFC uncountable
  delta-system theorem for internally finite subsets of an arbitrary set.
  `finite-delta-with-root` additionally returns the root's finiteness.
- `Theorem.OverZFC.cohen-ccc`: actual
  `K7.ChainConditions.CCC₂ᴵ C.carrier C.order w` for the constructed Cohen
  presentation.
- `Theorem.OverZFC.completion-ccc`: the same internal CCC₂ for the actual
  `Certificate.Nonzero` carrier of the canonical completion, with its coded
  subset order.
- `Theorem.OverZFC.certificate`, `property-transfer` and
  `property-hypotheses-inhabited`: the actual structural completion
  certificate, its separate property-transfer certificate, and an explicit
  inhabitant of the latter's named internal-Choice hypotheses.
- `Theorem.OverZFC.coordinate-dense` and `distinct-dense`: density of the
  actual coded D and E families.

The final endpoints do not take a delta-system lemma, disjoint-subfamily
theorem, pairing injection, Cohen CCC or Boolean CCC conclusion as an
assumption. Parameterized intermediate kernels remain available, with their
parameters explicitly discharged in the public composition.

## Construction and proof architecture

The finite-set layer constructs internal Kuratowski finiteness, formula-backed
induction, finite-subset sets, ambient change, unions, powersets, products,
finite enumeration bounds and countability. Finite partial functions are actual
ground-coded finite functional graphs. Their domains, ranges, restrictions,
compatible unions, singleton extensions and reverse-inclusion order have exact
membership or lookup specifications.

The Cohen carrier specializes these functions to `κ × w → two`, where
`two = {empty, {empty}}`. Both the carrier and its order are actual sets.
D asks for some assigned value at a coordinate; E asks for unequal values at
a common natural for two distinct indices. The E proof uses a natural outside
the finite second-coordinate projection, then performs two fresh extensions.

`DiagonalOrder` constructs an internal injection `w × w ↪ w` using a
definable strict order with internally finite initial segments.
`CountableZFC` supplies this witness to the bounded-Choice countable-union
construction, closing the old pairing gap.

The delta-system proof first extracts an uncountable family with a uniform
finite injection bound, then inducts on that internal natural bound. An
uncountable star is reduced by deleting its fixed element; deletion is an
actual injective ground graph, lowers the bound and permits root restoration.
If every star is countable, `OmegaRecursion` constructs a ground-coded orbit
of the neighborhood closure. Formula induction proves every stage countable;
its countable union contains the relevant connected component. Internal
Choice selects one representative from each component. The raw choice set is
explicitly intersected with the original family, so extra elements supplied by
Choice cannot enter the representative subfamily. This gives the uncountable
pairwise-disjoint branch without a host well-order or host recursion.

`DomainFamilies` handles repeated condition domains by actual finite fibers
and the countable-union theorem. `CohenCCC` applies the full delta-system
theorem to the domain family. Equal restrictions to the finite root imply
compatibility; on an antichain this makes the domain subfamily a countable
image of the internally finite family of root assignments, contradicting
uncountability. Equal domains are never asserted to imply equal conditions.

`CanonicalCertificate` constructs the actual completion certificate.
`CCCTransfer` and `CodedCCCTransfer` perform the internal-Choice selection,
ground image and antichain counting for the canonical dense embedding.
`CertifiedCCCTransfer` proves that its inhabited regular-open carrier agrees
with the actual certificate's nonzero carrier, transports the order/CCC, and
packages the result as a real `Certificate.Property.PropertyTransfer`.
The Boolean theorem consumes this certified transfer, not a second Cohen
topological argument.

## Assumptions and preservation

See `ASSUMPTIONS.md` for the precise ledger. The full endpoints use ordinary
Extensionality, Pairing, Union, PowerSet, Separation, Collection and
FoundationInduction, an explicit path realization of interpreted equality,
`LEM ℓ`, ordinary internal `ChoiceSet`, and an actual internal omega `w`.
The index set `κ` is arbitrary: no CH/GCH, continuum calculation or cardinal
arithmetic is assumed. No host Choice, global host well-order, generic filter,
fullness, resizing or additional universe axiom is introduced.

These are isolated proof probes. All 130 inherited K0-K7 Agda files are
byte-identical to the previous checkpoint. No production source, milestone,
glossary, reading route or main-worktree file was changed. Existing uncommitted
edits were preserved; the forcing worktree receives the updated K8 report and
one added roadmap completion paragraph. No commit or push was made.

## Verification

Final aggregate and serial verification: **all 62 K8 modules returned exit 0**,
including `Theorem` and `Smoke`. The serial runner returned exit 0 and ended
with `K8 ALL MODULES VERIFIED`.

Every K8 Agda source retains `--safe`. Compilation uses
`GHCRTS="-A64m -I0 -M8g"`; the serial runner checks the two-process limit
before each module. Per-module logs, aggregate output and source checksums
accompany the completed checkpoint.

The two parked negative controls reject a swapped adjunction reading and a
fresh extension with the freshness premise omitted. Their existing exit-42
evidence is retained, not relabeled as a new test execution.
Independent read-only mathematical review checked the actual formula indices,
internal recursion, component selection/clipping, delta-system branches and
finite-fiber argument. Reviews supplement, and do not replace, typechecking.

Long module-application checks were narrowed with explicit `using` lists
for the needed exports. An interrupted FullDeltaSystem check records exit 130
and is not counted as success; the narrowed version subsequently returned
exit 0. New recursion proof exports are opaque; inherited opacity boundaries
and mathematical statements were not changed. Build resources are measured
costs, not optimization targets.
