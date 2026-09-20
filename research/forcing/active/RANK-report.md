# K10 internal ranks and concrete cardinal preservation

The internal rank-existence, whole-square and final concrete preservation
proofs pass their named checks and the complete serial regression:
145 positive modules and four expected-failure controls. The earlier order
checkpoint remains the immutable 139-positive-module baseline.
Full K10 remains incomplete.

## Construction and assumptions

`K7/OrdinalTypeBounds.agda` proves that an ordinal injecting into a member
of a cardinal lies below that cardinal. Ordinal comparison rules out the
equal and greater cases using cardinal minimality. The direct result does
not require the smaller set to be omega, nor Pairing or Collection. The
through-injection corollary uses those two axioms to compose ground graphs.

`K7/DiagonalOrderType.agda` now bounds actual initial-segment ordinal types.
It also supplies fixed formulas for the initial set and for the rank of a
point. The rank formula includes membership of the point in the actual
diagonal product. Uniqueness of ordinal types makes its witness fiber
contractible when existence is supplied. Ground Separation and Collection
therefore collect the ranks of a ground set without a host image capability.

`K7/OrderTypeRestriction.agda` constructs an actual restriction graph from
an ordinal isomorphism to the predecessors of an image point. It proves the
restricted ordinal type and its strict comparison with the original type.

`K7/DiagonalRankExistence.agda` applies that restriction to actual diagonal
initial segments. Restriction proves comparison and realizes every member
of an existing ordinal rank as a predecessor rank. Collected predecessor
ranks consequently form an ordinal. Their inverse-rank graph is an
isomorphism onto the initial segment. The fixed rank-existence formula can
then be proved by the existing diagonal formula induction. This argument
does not assume the conclusion as a recursion capability and uses no host
well-foundedness or arbitrary host selection function.

`K7/OrdinalSquare.agda` takes the resulting ranks in the opposite graph
direction, from the whole diagonal product into the target cardinal.
Uniqueness gives functionality, proper-initial comparison gives injectivity,
and initial-segment countability gives the ordinal bound.

The exact square theorem concerns a supplied cardinal `d` above ground
omega whose every member injects into omega. This is the first-uncountable
cardinal situation, not an arbitrary higher uncountable cardinal. Its
low-level API retains successor closure.
`K7/CountableOrdinalSuccessor.agda` discharges that closure through countable
union with a singleton, the previously proved omega-square injection,
ordinal successor and the new bound theorem. This supplier uses ground
Choice. It does not use the new uncountable-square theorem circularly.

## Actual Cohen interface

The new `AtOmega` branch in `K10/CohenPreservation.agda` supplies CCC from the
actual K8 finite-delta-system theorem for the original Cohen conditions and
the original ground omega parameter. Its countable-bound preservation
endpoint takes no CCC argument.

The `AtSuccessorCardinal` branch supplies successor closure and the new
square injection, and derives the omega inclusion injection from cardinal
transitivity. Both the square producer and the cover consumer use the same
ground-set seed, omega. The preservation conclusion is for the exact K9
extension and canonical checked target cardinal, not a replacement model.

The retained requirements include the supplied ground cardinal bounds,
name-kernel Families/Accessibility/MemberImage, actual semantic evaluator
and compiler supplies and their laws, the generic filter and its dense-set
meeting property, ground Foundation and Choice, and extension Pairing,
Separation and Collection. No existence of the supplied cardinals is proved
by the square theorem. Full K10 and the final Boolean non-CH endpoints
remain separate obligations.

## Validation and provenance

The previous WIP archive is unchanged. On resumption, the named checks of
`K7/DiagonalRankExistence.agda`, `K7/CountableOrdinalSuccessor.agda` and
`K7/OrdinalSquare.agda` exited 0. This closes the internal existence and
the first-uncountable square obligations under the stated profile.

The named checks of `K7/OrderTypeRestriction.agda` and the updated
`K7/DiagonalOrderType.agda` exited 0, including the latter's new
`OrdinalTypeBounds` dependency. Both the initial CCC-only revision and
the final square-discharge revision of `K10/CohenPreservation.agda`
exited 0. Scoped prose and glossary gates on the research note and roadmap,
and `git diff --check`, each exited 0.

On 2026-09-13 `sh verify-k10-rank.sh` exited 0. All 145 positive modules,
including `K10/RankSmoke.agda`, passed; the four negative controls returned
the expected exit 42 and type-error signatures. The forbidden-construct
and explicit-hole scan found no matches in the new and extended proof
modules. A source comparison confirmed the production reference snapshot
unchanged. Logs are in `rank-logs/`; build caches are excluded from the
durable archive.

The previously interrupted command was
`GHCRTS='-A64m -I0 -M8g' agda K7/DiagonalRankExistence.agda`; it was
interrupted with exit 130 for the global compiler limit, with no Agda error
diagnostic. The now-checked endpoint has type
`rank-exists : (p : S) → ⟨ p ∈ˢ Diagonal.P ⟩ → ⟨ hasRank p ⟩`.
That interruption was environmental, not a mathematical counterexample.

Use `sh verify-k10-rank.sh` for serial checks of all positive K7 through K10
modules and the four inherited expected-failure controls. Every Agda call
uses `GHCRTS='-A64m -I0 -M8g'`. No production whole-tree closure is run.

An initial bound check exposed a distinction between empty types and their
lifted versions; its eliminator was corrected before the successful check.
An initial rank-formula check left proposition-type implicit metas at
`rank-reading`; explicit proposition arguments resolved them. These failed
exploratory runs are not accepted proofs.

The first rank-existence check was interrupted when another workflow
started a second compiler. This task did not stop or modify those external
processes. Verification resumed after the user reported that workflow done.

Resumed checks isolated elaboration cost to nested ground Separation terms.
Imports, initial membership and individual conversion interfaces checked,
while their concrete combination caused long normalization. Limited aliases
and a sealed rank formula reduced unnecessary exposure. Sealing the actual
diagonal relation, initial set and predecessor set together with their
proved readings allowed the complete existence proof to check. No axiom,
mathematical statement or extra premise was introduced. Temporary diagnostic
copies were removed; they are not accepted modules or regression controls.

Three inherited positive files are modified: `K7/OrdinalDiagonal.agda`,
`K7/DiagonalOrderType.agda` and `K10/CohenPreservation.agda`.
Production sources and all prior archived
checkpoints are unchanged. No commit or push is performed.
