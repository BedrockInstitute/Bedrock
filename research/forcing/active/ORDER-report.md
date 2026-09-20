# K10 diagonal order and concrete Cohen preservation

K10 remains incomplete. This checkpoint extends the 133-positive-module
countable-product checkpoint with five proof modules and a smoke module.
All inherited proof sources and the production reference snapshot are unchanged.

## Internal diagonal order

`K7/LexicographicMinimum.agda` proves minimality for a nonempty fixed-formula
class of finite tuples bounded by a ground set. The reverse lexicographic
relation examines the tail before the head. The proof recursively minimizes
the tail, separates its possible heads, and applies ground Foundation.
For an arbitrary bound this is minimality, not a claim of total ordering.
The module uses Extensionality, equality paths, Separation, Foundation
induction and LEM; it adds no host selection function or host well-foundedness.

`K7/DiagonalMinimum.agda` applies this result to the exact existing diagonal
order on the ground product. Its tuple is `(second, first, maximum)`.
Every inhabited ground subset of that product has an element with no earlier
member. Separating counterexamples then gives induction for each ground
formula. This is formula induction, not induction for arbitrary host
predicates. The module retains the existing ordinal-diagonal telescope,
including its successor-closure and member-countability parameters.

`K7/OrderTypeUniqueness.agda` proves uniqueness of both the ordinal and the
ground isomorphism graph. Its graph relation is the canonical ground
Kuratowski-pair relation. Exact domain is derived from the existing global
injection predicate together with surjectivity, not introduced as an
independent premise. The comparison uses Foundation induction and does not
require LEM, Separation or Choice.

`K7/DiagonalOrderType.agda` constructs the actual ground graph of the diagonal
relation and proves its exact reading, including on actual initial segments.
It supplies formulas for order-type witnesses and their existence assertion.
The type containing an ordinal, its isomorphism graph and their correctness
proofs is a proposition by the proved uniqueness theorem. Consequently,
truncated existence can legitimately yield this unique witness without host
Choice. Existence itself remains an input and is not proved here.

## Concrete preservation adapter

`K10/CohenPreservation.agda` specializes the existing preservation proof to
the actual K9 Cohen conditions, completion, names, canonical checks and
generic extension. It supplies the checked membership and ordinal transfer,
arbitrary-condition checked-equality reflection, check-graph formula and
its reading, and the ground Separation constructor with its laws.

The check graph uses the already required name-layer `MemberImage` capability
on canonical checks. It does not discharge that capability or accessibility,
and it does not turn the earlier formula-based value-family result into a
theorem realizing arbitrary host images from Separation alone.

The public preservation statements concern the exact K9 extension and
canonical checked cardinal. Their residual hypotheses remain visible:
name-kernel capabilities; the actual evaluator and its laws, quotient and
translation agreements, surjectivity and semantic supply; a filter meeting
the required dense sets; an actual forcing-formula compiler and its reading;
ground Foundation and Choice; extension Pairing, Separation and Collection;
the relevant ordinal/cardinal bounds; CCC at the chosen omega; and, on the
larger-cardinal route, the square bound. These are conditional preservation
theorems, not closed Cohen two-cardinal or Boolean non-CH endpoints.

## Remaining mathematics

The next order-theoretic obligation is internal existence of ordinal
isomorphisms for the diagonal initial segments. Uniqueness and legitimate
extraction do not replace this construction. Its boundedness argument and
the resulting whole-square injection must also be supplied. The final
concrete compiler/semantic supplies and Boolean endpoints remain separate.

## Verification

On 2026-09-13 `sh verify-k10-order.sh` exited 0: 139 positive modules
passed, and all four negative controls returned the expected exit 42 and
type-error signatures. Scoped prose and glossary gates on the two updated
research notes each exited 0; `git diff --check` exited 0. Read-only
mathematical review confirmed the extraction and residual-hypothesis
boundaries above. All six new positive modules retain the safe header;
a forbidden-construct and explicit-hole scan found no matches.

Run `sh verify-k10-order.sh` for a serial K7 through K10 regression, including
the new smoke module, and four expected-failure controls. Each compiler call
uses `GHCRTS='-A64m -I0 -M8g'`; the script checks the global process count
before launching and does not run the production whole-tree closure.

`Controls/Negative/MissingOnto.agda` fails at line 30 with `[UnequalTerms]`:
the attempted argument has not supplied `OrderType.Onto f a A`. This is an
interface misuse test, not a formal independence result for surjectivity.
The previous missing-function, missing-value-function and missing-check-reading
controls remain unchanged.

The initial dependent-with version of diagonal formula induction was
interrupted because of elaboration cost. Replacing those case abstractions
with explicitly typed local eliminators made the final named file check.
An intermediate scope error was fixed before the successful check. These
exploratory runs are not counted as accepted proof results.

This is an isolated proof checkpoint, not a production chapter migration.
No production landmark, commit or push is changed. The durable archive
excludes build caches and includes source, reports and verification logs.
