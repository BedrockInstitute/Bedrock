# Consolidated research results

This synthesis records the state at archival, 2026-09-28. It reconciles the
historical reports without changing their mathematical claims. Seven terminology
occurrences are normalized, with exact original lines retained in the manifest. The [root entry](../../DOUBLE-NEGATION.md)
is the task boundary; the [inventory](EVIDENCE.md) links every preserved file.
No complete internal ZF model and no universal impossibility theorem were obtained.

## Original formula classicality with ordinary satisfaction

The initial research branch introduced `InternalLEMᵥ`, quantifying over the
existing `Formula S n` and environments and asserting satisfaction of
`φ ∨̇ ¬̇ φ`. Its satisfaction relation is the ordinary one on the external
HIT cumulative hierarchy, not a double-negation interpretation.

Because this disjunction is propositionally truncated and `Dec P` is a
proposition when P is, the assumption gives actual decisions of satisfaction.
Unit/empty representatives then provide formula-specific resizing for full
separation. Atomic membership decisions define actual Boolean characteristic
functions; a small function type indexes the candidate powerset. The chapter
assembles `V⊨ZF : InternalLEMᵥ → isZFModel` with the existing constructive fields.

This is a conditional theorem about that particular satisfaction relation.
It is not an assumption-free construction of the requested internal world.
Replacing truncated disjunction by double-negated disjunction invalidates the
decision-extraction step. The assumption's syntactic form alone does not
guarantee that classicality is sealed away from host data. The original design
note already observes that this assumption implies host LEM at the lower
branching level via conditional singletons; it does not thereby recover host
LEM at the next universe. This is another reason to distinguish that theorem
from the requested negative interpretation.

Evidence: [original design note](reports/ORIGINAL-INTERNAL-CLASSICALITY.md),
[complete original diff](legacy/original-branch.patch), [original chapter](legacy/V/InternalClassicality.lagda.md.snapshot),
[original milestone entry](legacy/Milestones.lagda.md.snapshot), commit `053e89ff`.
The back-merge retains main's current Origin and archives these chapters
instead of modifying the public statements of the existing book.

## Direct negative set interpretations

Keeping the original HIT-V's host equality while merely replacing membership
by double negation fails an exact test. Extensionality for this new membership
into host paths implies DNE, hence external LEM, by comparing the conditional
singleton indexed by P with the singleton of the empty set. This excludes
that particular combination of equality and membership.

A constructive alternative uses trees `sup A f` with small branching and
recursively double-negated bisimulation. Its equality is small, stable and an
equivalence; membership is small and stable and respects both arguments.
Membership agreement proves extensionality. Small stable extensional predicates
admit separation, and stable induction proves negatively interpreted foundation.
The set quotient has descended membership, stable path equality, extensionality
and distinct empty/singleton points. Not every tree theorem was descended to
the quotient, and neither version was shown to satisfy all of ZF.

This distinguishes three objects that earlier explanations risked conflating:
the original external HIT-V, raw trees equipped with internal bisimulation,
and the quotient of those trees. A proposed V must specify which it uses.

Evidence: `ExtensionalityBoundary`, `ModalTrees`, `ModalQuotient` in
[the inventory](EVIDENCE.md); [initial feasibility](reports/INITIAL-FEASIBILITY.md)
and [direct interpretations](reports/ALTERNATIVE-ROUTES.md).

## Pointwise resizing and sheaf completion

Constructively, every P has `¬¬ Dec P`. Under that double negation a decision
chooses Unit or Empty, yielding an individual small representative. Stable
goals can consume such a representative; finitely many uses compose. Neither
an actual representative for every P nor a double-negated whole family follows
without an additional argument.

The library's double-negation modality on types reflects into stable
propositions. It is not by itself a full universe-preserving sheafification
of sets. Nullification indexed by all dense small propositions raises the
universe level; `SameLevel` records the compiler rejection of assigning this
particular construction a smaller sort.

The stable partial-element completion of Bool was constructed and proved
equivalent to `StableProp ℓ`. A same-level presentation of this completion is
therefore equivalent to a small stable-proposition classifier. An abstract
theorem recovers that classifier from a small separated set with two distinct
dense points and extension of maps from dense small propositions. Such a
package cannot be assumed as a supposedly weaker way to avoid resizing.
Deriving it would be a result; assuming it violates the user's boundary.

Literature on sheafification and oracle modalities was checked for this size
premise. The cited small-classifier axioms and restricted local operators do
not provide the required unconditional construction. None of this proves that
every different first-order interpretation is impossible.

Evidence: `Boundary`, `SameLevel`, `InternalResizing`, `BooleanCompletion`,
`SheafBoundary`; [pointwise interface](reports/INTERNAL-RESIZING-INTERFACE.md),
[completion boundary](reports/COMPLETION-BOUNDARY.md),
[initial source audit](reports/INITIAL-FEASIBILITY.md).

## Powersets, predicate covers and function objects

The Boolean-mask candidate `boolPower (sup A f)` is small and sound. For an
injective presentation, its completeness is equivalent to simultaneous
double-negated decisions for all membership predicates on A. Pointwise
double-negated decisions do not supply this simultaneous statement.

Every subset has a canonical presentation by a stable predicate on the original
index. General powerset witnesses are therefore characterized by suitable
small dense covers of these predicates. Ordinary quotienting of a fixed index
family does not add coverage. Diagonalization excludes covers indexed by A
itself and, for the explicit natural-number chain, by Nat or its quotients.
This does not exclude formulas with parameters from a larger carrier.

Relational Boolean maps correspond to stable predicates. Function covers and
predicate covers imply each other; for injective presentations they also
correspond to powerset witnesses. A minimal small function object already
implies the cover requirement, even with higher-level equality and naming
relations. Binary modal Fullness is equivalent to the same cover interface.
Finite function objects were constructed using finite double-negation shift;
this does not settle the infinite case.

These are exact implications for specified interfaces. They do not identify
all possible first-order set models with a universe of arbitrary host stable
predicates. In particular they cannot be applied to a formula-restricted
interpretation without proving that it realizes those predicates.

Evidence: `BooleanPower`, `DensePower`, `CoverObstructions`, `RelationalTruth`,
`RelationalExponential`, `FunctionPower`, `FunctionObjectBoundary`,
`FiniteFunctionObjects`, `ModalFullness`;
[Boolean masks](reports/POWERSET-AUDIT.md),
[dense predicates](reports/DENSE-POWER-AUDIT.md),
[quotient/diagonal limits](reports/COVER-OBSTRUCTIONS.md),
[conditional exponentials](reports/RELATIONAL-EXPONENTIAL.md),
[minimal function objects and Fullness](reports/FUNCTION-OBJECT-BOUNDARY.md).

## Separation, replacement and small supports

For stable extensional predicates on a tree presentation, a separation witness
is equivalent to a whole family of small representatives on its indices.
The corresponding equivalence holds under double negation. Singleton modal
separation is available without providing arbitrary family collection.

Unique modal existence does not justify extracting an actual value. For
separated sets, unrestricted unique extraction corresponds to extension from
dense propositions. The original replacement implementation projects actual
values from contractible witness types, so it cannot simply consume a negative
existential instead.

A constructive supported-image theorem avoids choosing individual outputs:
small dense candidate domains with maps to valid values give the entire image
by indexing all candidates. For small-valued relations, the image also supplies
such supports. For large relations, the filtered support can be too large;
pointwise modal supports still do not supply a whole support family.

Conditional singleton/empty outputs show that a small bound on possible values
alone is not enough. An image for that relation, followed by union, yields
separation. Thus a proposed replacement solution must explain the same missing
size/collection step rather than hide it behind a bounded-output argument.

Evidence: `SeparationBoundary`, `UniqueExtraction`, `SupportedImage`,
`ConditionalImage`; [separation and extraction](reports/SEPARATION-AND-EXTRACTION.md),
[supported images](reports/SUPPORTED-IMAGE.md),
[conditional-image test](reports/INTERNAL-RESIZING-INTERFACE.md).

## Relational semantics and the internal type theory detour

This route was explored and yielded real conditional and unconditional
mathematical results, but it drifted from the required deep first-order premise.
It is preserved as auxiliary evidence, not counted as completion of that premise.

Objects consist of carriers with stable propositional equivalence relations.
Maps are stable, invariant, double-negation-total relations, single-valued up
to the target equivalence. Identity, composition, associativity, units,
congruence and isomorphism were checked. Graph and carrier levels are explicit:
composition may raise the graph level by quantifying over its middle carrier.

Stable predicates correspond to relational maps into Boolean. Predicate
pullback respects identity and composition. Predicate comprehension and
classification were constructed, but a full comprehension-category universal
property or dependent type-theory model was not supplied.

A universe of codes for small internally propositional objects was defined,
with decoding and coherent transport. Code equality corresponds to isomorphism
of decoded objects. This universe is relationally isomorphic to Boolean.
The theorem named `internal-LEM-to-prop-universe-resizing` consumes:

```text
∀ P : PropCode, ¬¬ Dec(truth P).
```

This is NOT the original deep-Formula excluded-middle premise. Its constructive
proof and the resulting relational isomorphism are valid in the stated
interpretation, but no bridge from the specified formula principle covering
the entire proposition-code domain was proved. Earlier summaries that omitted
this distinction overstated progress toward the original objective.

The function construction provides evaluation, abstraction, beta, uniqueness
and compatibility with context substitution for maps at the specified level.
Its carrier lies one level higher. Uncurrying arbitrary higher-level graphs
does not establish a small representative for every such graph; this is not
an unrestricted exponential across every universe of relations.

Even an arbitrary-level isomorphism to a small carrier cannot bypass the
existing cover obstruction if evaluation remains small. Allowing higher-level
evaluation was identified as an open semantic alternative, but the user then
explicitly restored the deep first-order task. It is not the current mainline.

Quantifier transport along dense maps and relational unique-description rules
were also investigated. An actual Boolean selector for stable truths implies
external weak excluded middle. Relational truth classification alone does not
extract that selector. The examined classical Minimalist Foundation translation
does not provide the required small proposition universe either.

Evidence: `QuantifierTransport`, `TruthChoice`, `StableRelations`,
`RelationalOmega`, `RelationalClassifier`, `RelationalPropUniverse`,
`RelationalFunctionBoundary`, `RelationalLargeFunctions`,
`RelationalSmallFunctionAudit`;
[quantifier/selector audit](reports/RELATIONAL-QUANTIFIERS.md),
[relational proposition universe](reports/RELATIONAL-PROP-UNIVERSE.md),
[function levels and strengthened obstruction](reports/RELATIONAL-FUNCTION-SIZE.md).

No complete syntax for an internal dependent type theory, small dependent
universe, interpretation of the original HIT-V in it, or full internal ZF model
was constructed. The claim that an internal type theory theorem applies to internal sets
would require proof that the logic, smallness and constructors are the same.

## Constructibility and stage bounds

The current L powerset proof really uses `V.Model.Power (LEM→ΩResizing lem)`
and separately resizes constructibility predicates. L's final theorem only
lists LEM because resizing is derived from it; resizing is not absent from
the proof.

A direct alternative would bound every constructible subset of a in one
constructible stage. Relative to stage coverage, transitivity and stage
separation, this condition and power-set existence imply each other, including
under double negation. A common bound for a designated class of stages combines
pointwise stage witnesses without selecting them simultaneously.

Existing condensation gives individual bounds; a successor cardinal would
give a common bound. The current Hartogs construction, however, encodes
relations by actual Boolean functions using external decisions. Restricting
to all stable transitive well-founded relations does not remove size costs:
height-two relations encode arbitrary stable predicates. Collecting only
order types or using more restricted relations was not ruled out.

Definability at one fixed stage does not enumerate all later constructible
subsets. In a classical ambient model of V=L, the H_(omega_1)=L_(omega_1)
example satisfies the other classical set axioms and V=L but lacks P(omega)
and a common stage containing all reals. This refutes the shortcut based on
constructibility alone, not every possible internal L construction.

This route is a local alternative for L, not a solution to generic internal
Omega-resizing. The user explicitly rejected treating it as a substitute goal.

Evidence: `StagePowerBoundary`, `HartogsRelationBoundary`;
[complete L dependency and stage audit](reports/L-STAGE-BOUNDARY.md).

## Semantic and proof-theoretic boundaries

A cover of all stable predicates on Nat cannot have a subcountable index,
even when enumeration, surjectivity and coverage are only double-negation
inhabited. Assuming pointwise modal subcountability of all small types refutes
the matching predicate cover, function object and powerset witness. That
assumption was NOT established for all permitted Agda universes.

Published CZF models with subcountable sets provide a genuine obstruction for
the corresponding principle over that base theory. A separate handwritten
vertex-cardinality argument obstructs the cover in Uemura's modest-family
universe. It is not a checked implementation of that model and does not apply
automatically to its separate predicative universes or to every Agda primitive.

Proof-theoretic arguments give another warning: a sound internal ZF model,
even obtained under double negation, gives a consistency statement. The
generic negative-consistency implication was checked. A complete deep proof
calculus, ZF soundness theorem and upper-bound analysis for all permitted
Cubical Agda features were not supplied. Restricted MLTT bounds cannot simply
be promoted to a universal impossibility theorem for this project.

The literature audit also considered sheaf models, exact completions,
inductive-recursive universes, Palmgren's classical proposition universes,
and translations with impredicative Prop. Each has a specific additional
assumption, restricted universe, closure obligation or proof-theoretic scope.
The sources and precise caveats are retained in the reports; none is recorded
as an unconditional solution to the task.

Evidence: `SubcountableObstruction`, `ExtensionalityBoundary`;
[subcountability](reports/SUBCOUNTABLE-OBSTRUCTION.md),
[modest-family vertex audit](reports/CUBICAL-ASSEMBLY-AUDIT.md),
[initial literature audit](reports/INITIAL-FEASIBILITY.md), and the literature
sections of the completion, quantifier, exact-completion and direct-set reports.

## Return to the original deep first-order premise

The latest experiment imports the actual `FOL.Syntax` and renaming functions.
It defines negative satisfaction for stable equality and membership atoms,
including both bounded and unbounded quantifiers. Satisfaction is stable and
proposition-valued; renaming and weakening are proved compatible with it.
The explicit premise is again:

```text
FormulaLEM = ∀ {n} (φ : Formula S n) γ, Sat (φ ∨̇ ¬̇ φ) γ.
```

This premise is constructively valid in the specified negative interpretation.
The resizing theorem takes it as an explicit argument and applies it to deep
formulas. It does not consume the separately defined semantic InternalLEM of
the preceding route.

Using empty e, singleton u={e}, and pair o={e,u}, the theorem proves in the
same deep syntax that o contains exactly the subsets of u. Every formula has
an o-valued truth representative, under the internal existential, unique up
to internal equality. Formula weakening under the representative's binder is
checked. The elementary set assumptions are instantiated by explicit modal
trees, without external LEM, resizing, or a classifier parameter.

This is a candidate first-order truth-class resizing interface. It covers
all formulas of the specified language with parameters, not every arbitrary
host predicate. It does not create an internal global satisfaction predicate
over all syntax codes, and it does not claim host proposition-universe resizing.

It remains to show that this interface can serve every required consumer.
Classical H_(omega_1) validates the truth-set assertions but not P(omega), so
these assertions and the other ordinary classical set axioms do not alone
give general powersets. A function-set principle supplies an additional
bridge under the appropriate background set axioms. Those principles must
be formulated and proved in the same negative first-order interpretation.

Evidence: `DeepNegativeFOL`, `DeepFOLOmega`, `DeepFOLOmegaTrees`;
[complete current result, source comparison and remaining obligations](reports/DEEP-FOL-OMEGA.md).
The known Fin indexed-match computation warning remains explicit.

## Current completion criteria

The investigation is complete only after either:

1. deriving a suitable resizing interface from the specified deep first-order
   excluded middle and validating all required set constructions and ZF schemas
   under the original assumption boundary; or
2. producing a nonderivability or impossibility result whose base theory,
   universes and permitted interpretations actually cover the original request.

Neither criterion has been met. The next first-order consumer audit must not
silently assume general exponentiation, Fullness, support collection, or an
external classifier, and must not treat the L-specific alternative or internal
type-theory detour as completion of the original goal.
