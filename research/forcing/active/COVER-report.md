# K10 countable products and definable families

K10 remains incomplete. This continuation builds on the 127-module
all-condition forced-value checkpoint. Its next two mathematical steps are
countable products and the definable construction of local value families.

## Products and ordinal initial segments

`K7/CountableProducts.agda` constructs a ground coordinatewise injection
from two given ground injections. The graph is a set obtained through the
existing formula/Separation machinery. Composing with the proved omega-square
injection gives an injection of the product of two countable sets into omega.
There is no new Choice, `MemberImage` or square-law premise for this result.

`K7/OrdinalDiagonal.agda` defines the diagonal order on an ordinal square and
its initial segments by ground formulas. For a successor-closed ordinal whose
members inject into omega, each initial segment embeds into the square of
the successor of its largest coordinate, and is therefore countable.
Ordinal membership closure, linearity, transitivity and irreflexivity are
proved rather than assumed.

This is not an injection of the whole uncountable square. The missing next
step is a ground internal order-type/rank construction and its boundedness
argument. No conclusion about general omega-two covering follows merely from
countability of all proper initial segments.

## Definable value families

`K7/DefinableFamilies.agda` builds a family inside the power set of a fixed
bound by Separation using one fixed graph formula. Formula-based ground
Choice supplies its injection into the index set.

`K7/CheckIndexedFamilies.agda` constructs that graph formula for the actual
cuts used by possible values. An existential check code makes the coordinate
vary within the formula; Extensionality identifies the resulting set with
the existing cut. `PreserveAtTracks.WithDefinableFamilies` applies it to the
actual `EB.valueBody` and `mk`, so the resulting sets are exactly
`EB.valuesOf`, not another possible-value operator.

The new route removes `MemberImage` from the value-family producer. It still
requires a check-graph formula and its reading on each ground index set.
This is a definability requirement, not a realization of arbitrary host
images, and does not discharge name-layer `MemberImage` or accessibility.
The old capability-based family route remains available.

## Preservation boundary

The larger-bound cover now feeds the exact `ProvedRange` consumed by
preservation. Its square injection remains an explicit argument. The
countable-member route instead uses the already proved omega-square bound.

The actual K6 preservation adapter supplies the forcing relation, its truth
and monotonicity laws, the all-condition functional consequence, filter and
order laws, satisfaction congruence and extension Extensionality from their
real producers. Check transfer/reflection, definability, engine supplies,
ground profile and remaining extension capabilities stay visible.

The final `PreservationAtTruth.WithDefinedFamilies` route does not take
`FamilySet`, `ValueAntichain`, a functional forcing consequence or
`MemberImage` as premises. Positivity comes from the actual filter. Inverse
inhabitance uses the checked omega or checked smaller bound, transported by
the existing membership-transfer input. Extension Pairing, Separation and
Collection remain explicit. The larger output retains `squareBound`, whose
definition is the ground injection of the actual product of the smaller
bound with itself into that bound.

The general-ground square theorem, complete concrete Cohen two-cardinal
specialization, concrete compiler supplies and Boolean non-CH endpoints
remain open. The existing conditional generic engine is not replaced by a
generic-free engine.

## Validation and provenance

On 2026-09-13 `sh verify-k10-cover.sh` exited 0: all 133 positive modules
passed, and all three negative controls failed with the expected exit 42 and
type-error signatures. Scoped prose/glossary checks and `git diff --check`
also exited 0. The final mathematical review confirmed the formula and
actual-forcing interfaces and the remaining square-bound premise.

Run `sh verify-k10-cover.sh` for the serial positive K7 through K10 regression
and three expected-failure controls. The new missing-check-reading control
ensures an arbitrary formula cannot silently replace a proved check graph.
All positive checks use `GHCRTS='-A64m -I0 -M8g'`.

This is an isolated proof checkpoint. The production-source snapshot is
unchanged; no production landmark, commit or push is modified. Build caches
are excluded from the durable archive.

Relative to the previous checkpoint, six positive modules and one negative
control are new; `K7/PreserveAtTracks.agda` is the only modified inherited
positive module. Two exploratory checks of that module and one early actual
adapter check were interrupted for namespace-expansion cost, not accepted as
proof results. Narrowing auxiliary exports and applying the deepest producer
modules directly allowed the final files to check under the unchanged 8 GiB
heap cap. The serial regression records the final checks independently.
