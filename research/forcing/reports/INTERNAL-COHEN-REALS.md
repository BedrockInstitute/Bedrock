# Definable Cohen real names and countable-extension assembly

`InternalCohenReals` constructs the actual Cohen real names without MemberImage.
It takes Families (ordinary Pairing, Union, Separation and Collection), ground
extensionality/equality-path realization through Core, membership accessibility,
PowerSet, and the parameters κ and w. It takes neither a generic filter nor LEM,
choice, an externally supplied recursive graph, or arbitrary-function images.

## The concrete set construction

The earlier full-weight check recursion supplies its actual internal table on
w and the ordinary definable image of check on w. A candidate real-name entry
is bounded by the Cartesian product of that image and the Cohen condition
carrier. Its separating formula states:

1. There is n ∈ w and a condition p.
2. The check table records t at n, and the candidate entry is the coded pair (t,p).
3. A coded pair c = (α,n) is assigned bit 1 by p.

All these clauses have actual first-order formulas. The table's existence and
uniqueness theorems identify t with check n. Ordered-pair uniqueness identifies
c with the actual Cohen coordinate. Both directions of `raw→target` and
`target→raw` are proved, together with the bound needed for Separation. Thus
`real-spec` has exactly the existing public membership equation, not just a
one-way sufficient condition.

The recursive table and the Cohen coordinate infrastructure use different seed
parameters for their ground set constructors. Their chosen ordered-pair codes
are propositionally unique but need not be definitionally identical. The table
membership proof therefore uses the recursion table's own ordered-pair witness;
coordinate identification uses the Cohen seed's witness. The initial named
check exposed this distinction, and it was fixed at that interface.

Hereditary validity follows from the already proved check-name validity. The
support bound is the check image of w, and `real-support` follows from entry
injectivity. A universally quantified membership equivalence supplies
`realGraph`; extensionality proves it defines `realCode` uniquely. This yields
`real-graph` and an actual ordinary definable `real-image` for the real-name
family. It is a specific family, not closure under arbitrary host functions.

## Actual consumers

`K9.RealNames` reexports this implementation of realCode, its name validity,
entry theorem, support bound, and support theorem. Its preserved layer API now
uses a singleton Cartesian product over the assignment set. The legacy wrapper
still has its existing parameter telescope for compatibility; the standalone
supplier has no MemberImage parameter.

`K9.PairNames.pairLayers m n` is now the ordinary pair of the two spread sets,
and pairCode remains their union. Its two-sided membership specification is
proved directly from Pairing and Union. This removes the previous image of an
arbitrary host function from the finite construction while preserving public
semantics. It does not remove the generic IndexedNames capability.

## K11 specialization

`K11.CountableExtension` constructs G from the given carrier enumeration using
the actual CountableCohen supplier and feeds its proved genericity directly to
`K10.CohenTheorem.AtGeneric`. The shared Cohen presentation makes the condition
and genericity types align without an additional bridge assumption. The module
exposes the resulting AtGeneric and WithPreservedCardinals interfaces.

This completes the conditional API assembly. It does not construct an externally
countable ground or discharge K10's hypotheses. Accessibility and MemberImage
remain inherited K10 parameters, and the extension PowerSet, Separation,
Collection, Choice, and checked-cardinal preservation proofs remain explicit
inputs of WithPreservedCardinals. The Boolean inner-bot supply gap also remains.

## Verification boundary

The standalone real-name construction and both migrated K9 consumers passed
named Agda checks. A scoped read-only review verified the check-table indices,
the distinction between recursive-table pairs, name entries, and coordinates,
the Separation bound, the extensional real graph, and both finite-pair cases.

The first K11 adapter check exhausted the unchanged 8 GB heap. Narrowing module
aliases to the actual supplier and forwarded endpoint modules made the named
check pass with exit 0 at that same limit. No mathematical hypothesis or result
was changed. The heap diagnostic and successful retry log are retained.

## Next mathematical obligations

The actual indexed graph uses ordered pairs of check α and realCode α. Its
vertex family needs a proved defining formula and an image construction;
IndexedNames currently still accepts arbitrary host functions. The new
real-graph supplies one constituent of that formula. Recursive name translations,
Boolean atomic-value families, the extension axioms, and preservation still need
their actual suppliers. Existing conditional theorems remain conditional.
