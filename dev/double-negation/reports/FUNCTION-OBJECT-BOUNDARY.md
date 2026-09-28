# Function objects and modal binary Fullness

Date: 2026-09-28. These experiments were checked before the user's follow-up
about L and are recorded here after that interruption. They do not complete
the original internal ZF objective.

## Necessary global-point interface

`FunctionObjectBoundary.agda` defines a deliberately minimal fragment of a
relational function object from A to Bool. It has a small carrier E, an
arbitrary relation Equal on E, evaluation, and a naming relation for every
stable double-negation-total single-valued Boolean relation on A. Names are
double-negation inhabited and unique up to Equal; evaluation respects Equal;
the interpreted application satisfies both directions of beta.

The equality and naming relations may live at arbitrary higher levels. No
native equality, actual host name selection, eta rule, dependent products,
or complete categorical structure is assumed.

The checked `function-object-to-cover` constructs `FunctionCover A` from
these conditions. For each name i of R, beta gives agreement of R with
evaluation at i; its reverse direction uses modal name existence, uniqueness,
and stability of evaluation fibers. Conversely, the existing function cover
gives this minimal interface, with equality defined by pointwise agreement.

Thus merely switching to new equality or higher-level naming relations does
not remove the cover obligation in this specific full relational semantics.
The theorem does not say that all possible interpretations of internal
functions must include all these external relations or interpret smallness
as a small host carrier.

`FiniteFunctionObjects.agda` constructs these objects for every Fin(n), using
finite double-negation shift and the small family of Boolean masks. This is
a positive finite instance, not a replacement for the infinite-domain goal.
The natural-number instance is refuted under the previously defined
`ModalAllSmallSubcountable` assumption. That assumption is not asserted for
all types of the actual compiler.

## Binary modal Fullness is equivalent to the cover obligation

`ModalFullness.agda` considers stable Boolean-valued relations R on A with
totality `∀a, ¬¬ Σb, R(a,b)`. Binary Fullness asks for a small family of such
relations cofinal under inclusion, with double-negation existence of a
refining family member for each R.

The checked constructions give both implications:

```text
BinaryFullness A  → FunctionCover A
FunctionCover A   → BinaryFullness A.
```

For the first, filter the small family by single-valuedness. A total
subrelation of a single-valued total relation agrees with it, using stability.
For the second, every total Boolean relation has a canonical stable
single-valued subrelation: choose true when R(a,true), otherwise false.
This is a relational choice, not an actual Bool selector. A function cover
therefore supplies a cofinal family for all modal-total relations.

## Exact-completion literature audit

Emmenegger and Palmgren, *Exact completion and constructive theories of
sets*, Proposition 6.5, proves the closure needed for constructive setoids
by extracting functions using type-theoretic choice from Pi-Sigma witnesses.
Theorem 4.9 then yields local cartesian closure under its stated hypotheses:
<https://arxiv.org/pdf/1710.10685>.
That proof does not provide the analogous extraction from pointwise
double-negated Sigma witnesses. Its application to the negative relational
semantics here needs a new argument; ordinary constructive Fullness cannot
simply be renamed as our BinaryFullness.

Emmenegger's *On the local cartesian closure of exact completions* also
corrects the hypotheses of an older general characterization and gives the
appropriate conditions in Theorems 2.14 and 3.6:
<https://arxiv.org/pdf/1804.08585>.
The existence of ordinary type-theoretic products alone is not a verified
construction of the desired completed internal universe.

## Validation

All three new Agda files finished with exit 0 and no warnings using the
pinned compiler and local Agda home, with the required 8 GB heap limit.
The first FunctionObjectBoundary attempt failed on record universe levels
and a module application; both were corrected. The first finite proof used
indexed Fin matching and produced a cubical computation warning. Switching
to the library's recursively defined Fin removed that warning. The final
files retain `--safe`, with no postulates or holes.

These results sharpen necessary conditions for one candidate semantics;
they are neither full internal Ω-resizing nor a universal impossibility proof.
