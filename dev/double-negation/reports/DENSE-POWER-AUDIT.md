# Arbitrary powersets and small double-negation-dense covers

Date: 2026-09-28. Continuation of `POWERSET-AUDIT.md`.
This is an isolated experiment, not a change to the book or a completed ZF model.

## Result checked without external logical axioms

Fix `a = sup A f` in the recursive stable-bisimulation tree model. A predicate
on this presentation consists of `P : A → Type ℓ`, with proposition-valued,
double-negation-stable fibers, respecting `Eq (f i) (f j)`.
Write `Agree P R` for pointwise logical equivalence.

`DensePower.agda` proves implications in both directions between:

1. `PowerWitness f`: a tree `p` satisfying
   `Mem b p ↔ Subset b a` for every tree `b`.
2. `DenseCover f`: an index `I : Type ℓ`, predicates `R i`, and

   ```text
   (P : Predicate f) → ¬¬ (Σ i:I, Agree P (R i)).
   ```

No injectivity assumption on `f` is used. The predicates `R i` need not be
decidable. These are mutual implications, not a claimed type equivalence
between the records of construction data.

From a cover, construct `p = sup I (λ i → cut f (R i))`. Every branch is a
subset of `a`. An arbitrary subset `b` is equal to the cut defined by
`P_b i = Mem (f i) b`; covering this predicate proves `Mem b p`.

Conversely, write a powerset witness as `sup I g` and take
`R i j = Mem (f j) (g i)`. Apply its coverage to `cut f P`. Stability and
saturation of `P` give `Mem (f j) (cut f P) ↔ P j`, yielding the required
double-negated pointwise equivalence. Soundness is not needed for this
direction: arbitrary additional branches of the candidate can be normalized
to cuts when reconstructing a powerset from its cover.

Both implications also lift under double negation:

```text
¬¬ (PowerWitness f) ↔ ¬¬ (DenseCover f).
```

This matters because a first-order negative interpretation of existence asks
only for double-negated witnesses. The characterization does not accidentally
replace that requirement by an externally chosen witness.

The file additionally constructs a powerset witness for every singleton
presentation `Unit → Tree 0`, and hence a dense cover in that case, without
any extra axiom. Only one pointwise double-negated decision is needed.
This does not resolve coverage for arbitrary index types.

## What this changes, and what it does not

The Boolean candidate's simultaneous-decision condition cannot be promoted
to a necessary condition on all powersets based on the previous audit.
The general necessary and sufficient condition above allows undecidable
stable predicates as representatives.

A dense cover is not an actual small classifier: its covering property is
`¬¬ Σ`, not `Σ` or ordinary propositional-truncated surjectivity. Taking a
quotient of its index does not supply an elimination from this double
negation. In particular, separatedness (stable equality) must not be confused
with a sheaf extension principle producing such missing elements.

We have not proved that dense covers in general follow from the permitted
foundation, that they imply an excluded external axiom, or that they cannot
exist. Stipulating their existence would be adding an unproved premise, which
does not meet the user's requested unconditional construction. Giving the
premise a new name is not a solution.

For this tree model, any alternative same-carrier powerset construction must
solve the cover problem (at least under double negation for internal
existence). Changing to an entirely different model requires a separate
analysis; the result is not a universal impossibility theorem.

Full Separation for unbounded formulas and Replacement remain outstanding
even if this powerset obligation is solved. No internal universe structure,
resizing theorem usable by all original consumers, or full ZF model has been
constructed by this experiment.

## Primary-source cross-check

Rathjen, [Constructive Zermelo-Fraenkel Set Theory, Power Set, and the Calculus
of Constructions](https://eprints.whiterose.ac.uk/id/eprint/75182/4/ML-Arbeit-Ende.pdf),
Theorem 1.1 and Sections 4 and 6, studies an additional negative power-set
axiom. His type-theoretic interpretation uses a proof-irrelevant
impredicative proposition type. This is not a derivation from the present
predicative assumptions. The paper's negative powerset collects stable
subsets with ordinary external existence; it is not identified here with
our weaker double-negation-dense cover.

Jeon and Hanson, [The Axiom of Double Complement and its
opposites](https://arxiv.org/pdf/2606.00861), Section 1, describes Powell's
classical inner model under `IZF_Rep + DCom`. The paper proves that DCom
implies Powerset over CZF and is independent of IZF. This route also supplies
extra foundational structure; changing equality alone does not justify
importing its conclusion under our assumptions. No equivalence of DCom and
the current cover condition has been asserted.

## Validation

From `_build/double-negation-investigation`:

```sh
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home \
GHCRTS='-A64m -I0 -M8g' \
/Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda DensePower.agda
```

Final exit code 0, no warnings. Uses `--safe`, the pinned compiler and Cubical
library, complete proof terms and no postulates. No book source was changed;
the full book gate was not run for these isolated experiments.
