# Replacement images without extracting individual values

Date: 2026-09-28. Continuation of `SEPARATION-AND-EXTRACTION.md`.
Scope: isolated proof experiment; production sources remain unchanged.

## A working construction

Fix a small input index type A and an output relation
`R : A → Tree 0 → Type ℓ`. Assume R respects internal equality in its output
and is functional up to that equality. For each i, suppose we have:

```text
D_i : Type 0
¬¬ D_i
values_i : D_i → Σ y:Tree 0, R(i,y).
```

No element of D_i is selected. Form the tree whose branch type is
`Σ i:A, D_i` and whose branches are all the output values supplied by these
maps. `SupportedImage.agda` verifies exactly:

```text
Mem y image ↔ ¬¬ (Σ i:A, R(i,y)).
```

Soundness transports the stored R witness along the membership equality.
For completeness, an R(i,y) witness and double-negated inhabitation of D_i
give a candidate output internally equal to y, by functionality. All
eliminations of double negation target double-negated membership or image
membership assertions; no actual value is extracted from a modal existence.
The proof permits large R and does not assume stability of R.

This removes the generic unique-witness extraction operation as a necessary
step in this image construction. It does not remove the need to supply the
small candidate domains.

## A concrete bounded case

Suppose R itself is small-valued, there is a small candidate index B_i with
`g_i : B_i → Tree 0`, and

```text
∀i:A, ¬¬ (Σ b:B_i, R(i,g_i(b))).
```

Then take `D_i = Σ b:B_i, R(i,g_i(b))`. These are small, and all required
data follow directly. The file constructs the image from these premises,
without any choice of b and without double-negation shift, resizing, or
excluded middle.

This is a bounded image theorem, not full Replacement. An arbitrary output
is in the large tree type; enumerating all trees is not a small B_i.
If R is large-valued, even the displayed filtered domain may be too large.

## Exactness for small-valued relations

For small R with the extensionality, functionality and modal totality
premises above, the file also proves the converse. Given an actual image
`sup I g`, set

```text
D_i = Σ j:I, R(i,g(j)).
```

Modal totality and the image specification prove `¬¬D_i`. Its projection
supplies the candidate values. Therefore, for these relations, actual image
witnesses and families of small supports imply each other. Applying double
negation to both implications gives the same result for modal image
existence and modal existence of a whole supported family.

The smallness of R is essential to this converse as written. It is not
silently extended to satisfaction of arbitrary unbounded formulas.

## The remaining gap in quantifiers

For a possibly large type X, write

```text
SmallSupport X = Σ D:Type 0, (¬¬D × (D→X)).
```

The file proves `SmallSupport X → ¬¬X`. If X itself is small, the converse
holds by taking D=X. For arbitrary large X it only supplies

```text
¬¬X → ¬¬(SmallSupport X),
```

using a unit-domain support whenever an actual x is available.

Thus ordinary modal totality yields

```text
∀i:A, ¬¬ SmallSupport (Σ y:Tree 0, R(i,y)).
```

The implemented image theorem consumes a whole family of supports, or its
double negation if only modal image existence is wanted. We have not derived

```text
¬¬ (∀i:A, SmallSupport (Σ y:Tree 0, R(i,y)))
```

from that pointwise statement. No arbitrary product/double-negation exchange
has been used. Conversely, for small-valued functional relations the preceding
necessity theorem shows that the modal support-family requirement is not
merely an unnecessarily strong implementation premise: an image would supply
it. This is still not a general nonderivability theorem.

## Relation to the literature

Gambino and Aczel's [The Generalised Type-Theoretic Interpretation of
Constructive Set Theory](https://eprints.whiterose.ac.uk/113161/8/27588436.pdf),
Definition 5.2 and pp. 95–96, extends small double negation to large
propositions using small dense propositions supporting the large assertion.
Their extended operator need not agree with ordinary double negation on
large propositions. The current small-support construction uses arbitrary
small types and proof-relevant maps, so it is not asserted to be literally
their operator. The relevant shared issue is the additional small supporting
data, which bare negative existence does not visibly supply. We do not
replace the user's double-negation interpretation by their different logic.

## Status and verification

Run from `_build/double-negation-investigation`:

```sh
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home \
GHCRTS='-A64m -I0 -M8g' \
/Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda SupportedImage.agda
```

Final exit 0, no warnings, `--safe`, no postulates or holes. An intermediate
signature omitted two explicit module parameters and failed with exit 42;
the corrected final file, including the converse, was checked successfully.
The formal result concerns an input presentation A and relation R on its
indices. Connecting arbitrary first-order formula instances on the quotient
carrier still requires the appropriate input extensionality and semantic
translation; full Replacement is not claimed.

No support-family collection principle for all required relations, arbitrary
powersets, or full internal ZF model has been obtained. No production source
was modified and no whole-book gate was run.
