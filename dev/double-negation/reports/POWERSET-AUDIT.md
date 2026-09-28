# Powerset audit for recursive stable equality

Date: 2026-09-28. This continues the investigation in
`ALTERNATIVE-ROUTES.md`. No book source was modified. The objective remains a
full internal ZF model without external LEM or resizing; no additional logical
principle is assumed available.

## Verified candidate and its exact coverage condition

For `a = sup A f`, define a Boolean cut and a candidate powerset:

```text
boolCut f χ = sup (Σ i:A, χ i = true) (λ (i,_) → f i)
boolPower a = sup (A → Bool) (boolCut f).
```

Both index types live in `Type ℓ` when `A : Type ℓ`. Therefore `boolPower a`
is a tree at the same level as `a`, with no resizing used in its construction.
This is not yet a proof that the candidate is the powerset.

`BooleanPower.agda` verifies the following statements under `--safe`:

1. **Soundness.** `Mem b (boolPower a) → Subset b a`, for every `a,b`.
2. **Coverage given simultaneous decisions.** For a subset `b` of `a`,
   `¬¬ ((i:A) → Dec (Mem (f i) b))` implies `Mem b (boolPower a)`.
   In the proof, an actual family of decisions defines the Boolean mask, and
   stable bisimulation identifies the resulting cut with `b`. Double
   negation is only eliminated into the already negative membership goal.
3. **A sufficient uniform principle.** For this `A`, define `StableDecisions A`
   by

   ```text
   (P : A → Type ℓ) → (∀ i, ¬¬P i → P i) → ¬¬ (∀ i, Dec (P i)).
   ```

   This implies coverage for all internal subsets of `a`. The code proves an
   implication; it does not supply `StableDecisions A` as an axiom or theorem.
4. **Necessity for injective presentations.** If
   `Eq (f i) (f j) → i ≡ j`, coverage of all internal subsets by this Boolean
   candidate implies `StableDecisions A`. For an arbitrary stable family `P`,
   form its cut, use coverage to obtain a double-negated Boolean mask, and
   recover a decision of each `P i` from that mask. Injectivity permits
   membership at `f i` to recover the predicate at that same index.

Consequently Boolean coverage and `StableDecisions A` are equivalent for an
injective presentation. This is not a claimed equivalence with unrestricted
double-negation shift or with any external resizing axiom.

Pointwise `∀ i, ¬¬ Dec (P i)` is constructive, as `pointwise-decision` proves.
It must not be confused with the required simultaneous statement
`¬¬ (∀ i, Dec (P i))`. A suitable double-negation shift principle would bridge
them, as the separately checked conditional lemma `boolPower-from-shift`
shows. This investigation does not prove that such a principle holds for
arbitrary index types, or prove its impossibility in the full compiler.

## Canonical representation of arbitrary subsets

There is also an unconditional normalization result:

```text
Subset b a → Eq b (separate a (λ x → Mem x b)).
```

Thus every internal subset has a presentation using a small stable predicate
on the original index type. An alternative powerset construction can focus
on covering these predicates; it need not enumerate arbitrary unrelated tree
shapes. This is `canonical-subset` in the checked experiment.

The normalization does not make the collection of all such predicates small.
`hProp ℓ : Type (suc ℓ)`, so a direct index of all stable proposition-valued
families on `A` still lives one level too high. Quotienting that large index
by pointwise equivalence does not, by itself, lower its universe.

## Routes not resolved by this audit

| Candidate index | What works | What is missing |
| --- | --- | --- |
| `A → Bool` | Same-level construction and soundness | Simultaneous double-negated decisions, necessary as well as sufficient for injective presentations |
| All small stable predicates on `A` | Canonical representation of every subset | A same-level modal cover of this larger predicate collection |
| Formula codes alone | A small syntax can describe formulas | Arbitrary subsets involve parameters from the whole large carrier; syntax size does not bound parameter size |

The last row is a scope observation, not a formal impossibility theorem about
all possible coding constructions. Likewise the Boolean obstruction does not
rule out a different small covering family. General powerset existence has
not been proved or refuted by this experiment.

The next mathematical obligation is either to derive the needed simultaneous
decisions from the permitted foundation, or to construct a different small
family that covers all canonical predicates without that step. Neither a
classifier nor double-negation shift may be silently introduced as a premise
of an allegedly unconditional ZF theorem. Full Separation and Replacement
remain separate obligations even if Power Set is resolved.

## Checks

From `_build/double-negation-investigation`:

```sh
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home \
GHCRTS='-A64m -I0 -M8g' \
/Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda BooleanPower.agda
```

Final exit code: 0, no warnings. The file imports the previously checked
`ModalTrees.agda`, contains complete proof terms and no postulates, and is
outside the book's source/import graph. Conditional results are labeled as
such above and retain their premises in their checked signatures.

The full book gate was not run because no book source was changed. The
previous experiment's result is used only for its unchanged imported module,
not as evidence that this investigation has proved ZF.
