# Recursive equality, quotient carriers and direct interpretation

Investigation date: 2026-09-28. Scope: feasibility research only. No source
chapter, theorem signature, catalog or Git reference was changed in this turn.
The requirement remains no external LEM or resizing, including no assumed
small classifier for stable propositions.

## Result

Recursive stable bisimulation provides a working alternative to the previously
rejected use of host equality on the original cumulative hierarchy. A safe,
universe-polymorphic experiment validates its equivalence laws, extensionality,
small stable separation, stable induction and negatively interpreted
foundation. Its set quotient has well-defined small stable membership,
extensionality into quotient paths, stable equality, and distinct empty and
singleton elements. This is positive evidence for a direct internal semantics.

It is not a ZF model proof. Full Separation, Power Set and Replacement remain
unproved, and no complete first-order semantics or soundness theorem has been
implemented in these experiments. No full internal type theory has been
constructed or used.

## Checked construction

Let `Tree ℓ : Type (suc ℓ)` be the W-type with constructors
`sup A f`, where `A : Type ℓ` and `f : A → Tree ℓ`. Define recursively:

```text
Eq (sup A f) (sup B g)
  = (∀ a:A, ¬¬ Σ b:B, Eq (f a) (g b))
  × (∀ b:B, ¬¬ Σ a:A, Eq (f a) (g b))

Mem x (sup A f) = ¬¬ Σ a:A, Eq x (f a).
```

Both relations have values in `Type ℓ`, despite their carrier being larger.
The experiment proves that those values are propositions and stable under
double negation. `Eq` is reflexive, symmetric and transitive. `Mem` respects
`Eq` in both arguments. Agreement of memberships implies `Eq`.

This definition inserts double negation at each matching step. It is not
defined as double negation of the old equality. No interchange of double
negation with arbitrary universal quantification is assumed.

`ModalTrees.agda` also proves:

- Separation for predicates `P : Tree ℓ → Type ℓ` which are stable and respect
  `Eq`. The index type is `Σ i:A, P (f i)`, still at level `ℓ`.
- Membership induction for stable predicates respecting `Eq`, including
  predicates living in higher universes.
- Foundation in the form
  `¬¬ Σ x, Mem x a → ¬¬ Σ x, Mem x a × (∀ y, Mem y x → ¬ Mem y a)`,
  with the first existential parenthesized as the premise. In the actual
  checked signature this is two explicit `NN (Σ ...)` expressions, so there
  is no parsing ambiguity. This is the negative reading of the first-order
  foundation axiom; it is not host `WellFounded Mem`.

`ModalQuotient.agda` forms `S = Tree ℓ / Eq` using Cubical set quotients.
The membership relation descends to `S → S → hProp ℓ`. The experiment proves
extensionality into paths of `S`, stability of those paths and of membership,
and `empty ≠ singleton-empty`. Thus the quotient does not trivialize the
carrier. The induction, separation and foundation theorems above were checked
on tree representatives; their complete descent to a quotient model interface
has not been implemented here.

## What is still missing

| Obligation | What this construction supplies | Remaining issue |
| --- | --- | --- |
| Internal equality | A small stable equivalence and its effective quotient | No remaining obstruction at this stage |
| Logical classicality | Stable atomic relations, with negative existential/disjunction available | Full syntax interpretation and soundness remain to be implemented |
| Separation | Actual subsets for small stable extensional predicates | An unbounded quantifier ranges over `Tree ℓ` or `S`, so arbitrary formula truth values may live at `suc ℓ` |
| Power Set | An individual subset can be built from each appropriate small predicate | All stable predicates on `A` form a type at `suc ℓ`; no small enumeration of all represented subsets has been constructed |
| Replacement | Images of supplied actual functions are elementary tree constructions | Internal functional relations give double-negated witnesses; uniqueness alone does not eliminate double negation or supply a bound for those witnesses |
| Foundation | Negative first-order foundation on representatives | This does not supply host accessibility for arbitrary data-producing recursion |

Quotienting changes equality, not the universe in which all small predicates
can be indexed. A set quotient has a universe at least as large as its carrier.
Likewise, being a proposition does not imply double-negation stability: the
unique witness type for an internal functional relation cannot be extracted
just because uniqueness makes it a proposition.

These are missing construction obligations, not proofs that no construction
can ever satisfy them. Formula-schema Separation is weaker than separation
for every external predicate, so a general resizing obstruction should not be
misreported as a direct impossibility proof for the formula schema.

## Literature cross-check

- Erik Palmgren, [From type theory to setoids and back](https://arxiv.org/pdf/1909.01414),
  Sections 1 and 4: iterative sets and setoid equality support an extensional
  type-theoretic interpretation, including universe constructions. The result
  is not an assumption-free classical ZF model obtained merely by quotienting.
  Its ordinary bisimulation supplies positive witnesses; those cannot be
  projected unchanged after replacing them by double-negated witnesses.
- Nicola Gambino and Peter Aczel,
  [The Generalised Type-Theoretic Interpretation of Constructive Set Theory](https://eprints.whiterose.ac.uk/113161/8/27588436.pdf),
  pages 95–96: a predicative reinterpretation uses an extension `J` of a small
  local operator, not unrestricted ordinary double negation on all large
  propositions. Preservation of Subset Collection requires set-presentability.
  Standard negative interpretation into IZF uses Full Separation in handling
  Collection. It does not fill the three missing ZF obligations above for us.
- Mario Carneiro, [CIC + EM entails Con(ZF)](https://arxiv.org/pdf/2609.23143),
  September 2026 preprint, Sections 1 and 8: its stable reading uses the same
  recursive double-negated matching pattern. It reports a remaining
  accessibility hypothesis in the no-EM development. Crucially, its metatheory
  has an impredicative `Prop`; that provides Separation and Power Set before
  the remaining issues are addressed. Therefore it is not a resizing-free
  construction in our predicative Cubical Agda setting. This is a reading of
  the paper, not an independent execution of its Lean formalization.

## Verification

From this directory:

```sh
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home \
GHCRTS='-A64m -I0 -M8g' \
/Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda ModalQuotient.agda
```

Exit 0, with no warnings in the final run. This imports and checks
`ModalTrees.agda`. Both files use `--cubical --safe --guardedness`; their
theorems have complete bodies and no postulates. The positive construction
uses no external LEM, resizing, classifier or choice premise.

`git diff --exit-code -- src` also exited 0. No whole-tree build was run,
because the experiments are outside `src` and do not modify the book.

## Next decisive research question

The useful next target is a powerset construction for an arbitrary tree in this
specific interpretation, with every indexing level explicit. A proof must
cover all internal subsets, not just those named by an externally chosen
Boolean-valued function or a bounded list of formulas. In parallel with such
a construction, formula-level Full Separation and Replacement would still
need their own proofs. Until these are provided, this remains a verified
semantic foundation for further research, not a justification for whole-library
ZF migration.
