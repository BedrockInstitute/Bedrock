# Small Boolean completion and the stable-proposition classifier

Date: 2026-09-28. Continuation of `COVER-OBSTRUCTIONS.md`.
All experiments are isolated from the book's import graph.

## Concrete equivalence

Let `StableProp ℓ` be the type of propositions in `Type ℓ` equipped with
double-negation elimination. It lies in `Type (suc ℓ)`.

Define the stable-partial-element completion of Bool to consist of families
`ξ : Bool → StableProp ℓ` satisfying

```text
¬¬ (Σ b:Bool, ξ(b))
∀ b c, ξ(b) → ξ(c) → b = c.
```

`BooleanCompletion.agda` proves an actual equivalence of types:

```text
BooleanCompletion ℓ ≃ StableProp ℓ.
```

The forward map evaluates at `true`. The inverse of a stable proposition `P`
has true fiber `P` and false fiber `¬P`. Constructive double-negated excluded
middle gives its dense inhabitation. For an arbitrary completed element,
uniqueness and dense inhabitation prove that its false fiber is equivalent
to the negation of its true fiber. Propositional extensionality reconstructs
the whole completed element.

Consequently the following size statements imply each other:

```text
Σ C : Type ℓ, C ≃ BooleanCompletion ℓ
Σ Ω : Type ℓ, Ω ≃ StableProp ℓ.
```

This is not a universe inference failure: complete proof terms establish the
equivalence of the size requirements. The large completion itself is
constructible without adding an axiom. Its reduction to the original level
is precisely the additional issue.

## Abstract version, independent of that representation

`SheafBoundary.agda` proves that any `C : Type ℓ` with the following explicit
properties is equivalent to `StableProp ℓ`:

1. `C` is a set with double-negation-stable equality.
2. It has distinct points `t` and `f`.
3. These points are dense: every `c` satisfies
   `¬¬ ((c = t) ⊎ (c = f))`.
4. Maps from small dense propositions extend to points: given a proposition
   `D : Type ℓ`, `¬¬D`, and `g : D → C`, there is a point `c` with
   `∀d:D, c = g(d)`.

For stable `P`, the proposition `Dec P` is dense. Extend the map that sends a
positive decision to `t` and a negative decision to `f`. This defines an
actual point `encode P : C`. Then

```text
P ↔ (encode P = t).
```

Conversely, a point `c` represents the stable proposition `c = t`. Density
of the two points and stability of equality prove that encoding this
proposition returns `c`. These two constructions form the checked type
equivalence, supplying a small stable-proposition classifier.

The experiment verifies this conditional theorem and retains every condition
as a module parameter. It does not assert the existence of such a small `C`.
It does not verify a general reflective-subuniverse implementation or prove
that every object called a completion has the listed properties.

## Meaning for the research objective

This gives a precise boundary for the proposed universe-preserving sheaf
route. A package providing the above small Boolean completion cannot be
accepted as a weaker unexplained substitute for stable-proposition resizing:
the classifier can be recovered from the package itself.

The user's boundary is **not assuming** external resizing. Deriving a
classifier from the permitted foundation would be a substantive theorem,
not a violation of that boundary. Accordingly this result is not an
impossibility theorem. It says that an unconditional construction of this
completion would simultaneously prove the corresponding external negative
Omega-resizing principle. No such construction has been supplied here.

The conclusion concerns the classifier of stable small propositions. It
does not identify it with full propositional resizing or external excluded
middle. Nor does it rule out a different first-order set model that avoids
the above completion package. The arbitrary dense-cover problem in the
recursive tree model, full Separation and Replacement remain unresolved.

## Literature cross-check

Swan, [Oracle modalities](https://arxiv.org/pdf/2406.05818), Axiom 2.16,
assumes a small classifier for stable propositions. Section 3.1 constructs
the zero-truncated sheafification using stable partial elements; for Bool,
double-negated uniqueness agrees with ordinary uniqueness because equality
of Bool is decidable. Our concrete completion follows this mathematical
description while leaving its proposition-valued predicates at their honest
universe level. The smallness equivalence and abstract conditional theorem
above were checked directly in the repository's permitted compiler.

## Validation

Run in `_build/double-negation-investigation`, using the repository compiler:

```sh
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home \
GHCRTS='-A64m -I0 -M8g' \
/Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda BooleanCompletion.agda

AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home \
GHCRTS='-A64m -I0 -M8g' \
/Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda SheafBoundary.agda
```

Both exit 0, no warnings, under `--safe`, with no postulates, holes or
termination overrides. `git diff --exit-code -- src` exits 0. No whole-book
gate was run, because the book's source and import graph remain unchanged.
