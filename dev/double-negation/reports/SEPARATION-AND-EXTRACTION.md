# Direct separation and unique witness extraction

Date: 2026-09-28. Isolated investigation; no production source edits.

## Separation has an exact local size requirement

Fix `a = sup A f : Tree 0` and an extensional, stable predicate
`P : Tree 0 → Type ℓ`, allowing its truth values to be larger than the tree's
branch types. For proposition-valued P, `SeparationBoundary.agda` proves
mutual implications between:

```text
Σ b:Tree 0, ∀x, Mem x b ↔ (Mem x a × P x)
Σ Q:(A → hProp 0), ∀i:A, P(f i) ↔ Q(i).
```

The implication from a separation witness uses `Q(i) = Mem (f i) b`.
The reverse constructs the cut of `a` using Q. Stability and extensionality
of P justify eliminating double-negated membership into its truth values.
The code does not need the proposition certificate of P for the mutual
implications; that certificate makes logical representatives genuine
propositional resizing witnesses.

Mapping both implications under double negation gives the corresponding
characterization of modal separation:

```text
¬¬ (Σ b:Tree 0, separation specification)
  ↔ ¬¬ (Σ Q:(A → hProp 0), ∀i:A, P(f i) ↔ Q(i)).
```

The right side requires one whole family under double negation. The
constructively provable pointwise statement

```text
∀i:A, ¬¬ (Σ Q:hProp 0, P(f i) ↔ Q)
```

does not by itself provide that family. No double-negation shift is assumed.

## Actual and modal singleton separation differ

The file proves two useful boundary facts:

* An actual separation witness for a constant proposition P on a singleton
  gives an actual small representative of P, by evaluating membership at
  the singleton's element.
* Modal separation of every stable extensional predicate on a singleton is
  constructively provable, even when P is large. Here only one
  double-negated representative is needed, obtained by double-negated
  decidability and the Unit/Empty representatives.

Consequently the actual-witness implication cannot be promoted to a claim
that internal, double-negated separation forces external resizing.

There is a further scope distinction: the theorem accepts arbitrary external
predicates. ZF Separation is a first-order formula schema with set parameters.
It does not automatically allow every external proposition as an extra
predicate symbol. For the formula schema, the family-size obligation need
only be established for its satisfaction predicates. No equivalence of the
bare first-order ZF schema and unrestricted external resizing is asserted.

## Unique existence is not a free extraction operation

`UniqueExtraction.agda` defines, for a type C, the principle that every stable
proposition-valued R on C with at most one satisfying element and
`¬¬ Σ c:C, R(c)` yields an actual satisfying element.

For a set C with stable equality, it proves mutual implications between
this extraction principle and dense extension:

```text
∀ D:hProp ℓ, ¬¬D → ∀g:D→C, Σ c:C, ∀d:D, c = g(d).
```

From dense extension, use the unique-witness proposition `Σ c, R(c)` as D.
From unique extraction, use the stable predicate
`R(c) = ∀d:D, c = g(d)`; propositionality and dense inhabitation of D establish
the required unique, double-negatively inhabited solution.

Thus unrestricted extraction of modal unique witnesses is precisely the
dense-extension capability already isolated in `SheafBoundary.agda` for
separated sets. Merely showing that the witness type is a proposition is
insufficient: propositions need not be double-negation stable.

This is a conditional theorem about all stable predicates, not a proof that
formula-specific Replacement entails such unrestricted extraction. A direct
construction of an image set might avoid extracting every value, and remains
a separate route to investigate.

## Connection to current consumers

The actual `src/V/Model.lagda.md` code gives replacement a hypothesis

```text
fc : (x:S) → x∈a → isContr (Σ y:S, satisfaction φ(y,x)).
```

Its `replaceImage` reads `fc ... .fst .fst` to obtain actual values for each
presentation index. Internal modal unique existence does not provide that
projection. Reusing this construction requires proving the conversion or
changing the image construction; a generic conversion cannot be silently
treated as a harmless adapter.

In classical set theory, suitable Replacement together with the elementary
set operations can also yield Separation: map x to its singleton when P(x)
and to the empty set otherwise, then take the union of the image. This
suggests studying genuine internal Replacement directly rather than assuming
that full Separation must always receive an independent resizing parameter.
This internal derivation has not been implemented in the experiment.

Gambino and Aczel's [The Generalised Type-Theoretic Interpretation of
Constructive Set Theory](https://eprints.whiterose.ac.uk/113161/8/27588436.pdf),
pp. 95–96, distinguishes its predicative local operator on large propositions
from ordinary double negation and notes the use of Full Separation in the
standard interpretation of Collection. It does not supply the missing direct
image construction under the current assumptions.

## Validation and remaining obligations

In `_build/double-negation-investigation`, both of the following filenames
were checked with the repository compiler:

```sh
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home \
GHCRTS='-A64m -I0 -M8g' \
/Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda SeparationBoundary.agda

AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home \
GHCRTS='-A64m -I0 -M8g' \
/Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda UniqueExtraction.agda
```

Both exit 0, no warnings, `--safe`, no postulates or holes. Production source
is unchanged; no whole-book gate was run. Arbitrary modal image construction,
the required formula-specific separation instances, and arbitrary powersets
have not been established. This investigation remains short of a ZF model
and is not a universal impossibility proof.
