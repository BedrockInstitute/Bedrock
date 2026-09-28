# Quotients and countable candidate families

Date: 2026-09-28. Continuation of `DENSE-POWER-AUDIT.md`.
Scope: isolated investigation only; no changes to the book or its assumptions.

## Ordinary quotients cannot create predicate coverage

Fix the recursive stable equality and a presentation `f : A → Tree ℓ`.
For any index type `I`, relation `E`, and already well-defined family
`R : I / E → Predicate f`, the following covering statements imply each other:

```text
∀ P, ¬¬ Σ j : I / E, Agree P (R j)
∀ P, ¬¬ Σ i : I,     Agree P (R [i]).
```

`CoverObstructions.agda` proves both directions. Quotient induction gives
`¬¬ Σ i, [i] = j` for every quotient element. Combining this with the first
covering statement yields the second entirely within double negation.
The reverse implication just maps each original index to its quotient class.

Thus identifying existing candidate indices cannot repair missing coverage.
This statement fixes the target predicates and their interpretation. It does
not rule out changing the model's atomic equality, adding genuinely new
points through a different construction, or constructing a new larger family.
It also does not assert that every original family descends to every quotient.

## A diagonal obstruction survives double negation

Suppose `f` is injective with respect to internal equality:
`Eq (f i) (f j) → i = j`. Given any candidate family indexed by `A` itself,
`R : A → Predicate f`, form the predicate

```text
D(i) = ¬ R(i)(i).
```

It is a small stable proposition at every index, and injectivity makes it
saturated under the equality of represented elements. If `Agree D (R i)`
held, evaluating it at `i` would give `¬ R(i)(i) ↔ R(i)(i)`, a contradiction.
Consequently:

```text
¬ (Σ i:A, Agree D (R i))
¬ Covers R.
```

The purported cover yields double-negation of the first existential, which
is already refuted; therefore double negation does not avoid diagonalization.
Combining this with the quotient result rules out families indexed by `A / E`
as well.

For a concrete infinite example, define `chain 0 = empty` and
`chain (n+1) = {chain n}`. The file proves that this presentation is injective
for recursive stable equality, and forms `infiniteTree = sup Nat chain`.
No family `Nat → Predicate chain` covers all of its internal subsets. Neither
does a family indexed by a quotient of `Nat`.

This rules out an enumeration of fixed candidates by natural-number syntax
codes as a powerset of this particular infinite tree. Formulas with arbitrary
parameters from a larger carrier do not provide such a countable family;
they fall outside this obstruction and retain the parameter-size issue.

## Limits of the conclusion

`Type ℓ` includes types much larger than `Nat`, such as `Nat → Bool` at the
base level. This diagonal argument does not rule out arbitrary small covering
families or prove the impossibility of the requested ZF interpretation.
The Boolean function-space candidate remains subject to the simultaneous
decision obligation from `POWERSET-AUDIT.md`.

Ordinary quotienting and sheaf completion should not be interchanged here.
Swan's [Oracle modalities](https://arxiv.org/pdf/2406.05818), Section 3.1,
describes a completion by stable partial elements; its universe-preserving
construction uses the stable-proposition classifier assumed earlier in that
paper. It supplies no assumption-free replacement for the excluded external
size premise. The current quotient theorem is a separate local proof, not
a result attributed to Swan.

No arbitrary covering family, full Separation, Replacement or complete ZF
model has been obtained. These results eliminate two concrete proposed ways
to fill the coverage gap; they do not eliminate every alternative model.

## Validation

From `_build/double-negation-investigation`:

```sh
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home \
GHCRTS='-A64m -I0 -M8g' \
/Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda CoverObstructions.agda
```

Final exit 0, no warnings, with `--safe` and no postulates or holes. The pinned
compiler checked the final file including its explicit infinite example.
`git diff --exit-code -- src` also exits 0. No full book gate was run because
formal book sources and their import closure were unchanged.
