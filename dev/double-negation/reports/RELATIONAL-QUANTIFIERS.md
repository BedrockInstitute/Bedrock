# Relational truth, quantifier transport, and the remaining data interface

Date: 2026-09-28. This is research evidence, not an authorized production
migration. The complete objective remains open. The preceding clarification
turn added no mathematical evidence; this turn revalidated the worktree and
continued with two checked experiments and primary-source investigation.

## Relational classification

`RelationalTruth.agda` defines a stable relation from `StableProp ℓ` to `Bool`:
the true fiber is P, and the false fiber is its negation. It proves double
negation totality, uniqueness in both directions, and actual inverse codes for
true and false. In particular, for `code : Bool → StableProp ℓ`,

```text
∀ P, ¬¬ Σ b:Bool, P = code b.
```

This is not an ordinary host equivalence. A category of suitable relations
could treat it as an isomorphism, but its complete category, internal universes,
and dependent type structure have not been implemented or verified here.

The same file proves a precise conditional comparison: a small double-negation
cover of all relational maps A → Bool is equivalent to a small double-negation
cover of all stable predicates on A. Relational maps here mean stable,
double-negation-total, single-valued graphs. A cover is weaker than a complete
exponential universal property. Neither cover is assumed to exist.

## A checked consumer for large truth quantification

`QuantifierTransport.agda` proves the following generic facts about any map
`name : B → A` with `∀ x, ¬¬ Σ y, x = name y`.

* For proposition-valued, pointwise stable P, restriction gives an equivalence
  between `∀ x:A, P x` and `∀ y:B, P (name y)`.
* For any type-valued P, `¬¬ Σ x:A, P x` is equivalent to
  `¬¬ Σ y:B, P (name y)`.

Specializing A to `StableProp ℓ` and B to Bool gives a genuine, reusable size
reduction for quantification over stable truth values. If P takes values in
`StableProp p`, the right-hand statements have host level p, even when the
left-hand quantification has a larger level. No external LEM or resizing is
used. The universal statement requires stable fibers; the existential statement
uses double-negation existence. This is not a rule for extracting arbitrary
data or for resizing every large proposition.

The file also proves that density of Boolean masks among stable predicate
families on A is equivalent to simultaneous stable decisions:

```text
(∀ P:A→StableProp ℓ, ¬¬ Σ mask:A→Bool, ∀ x, P x = code(mask x))
  ⇔
(∀ P:A→StableProp ℓ, ¬¬ Π x:A, Dec(Holds(P x))).
```

This concerns the particular candidate family of ordinary Boolean masks. It
does not prove that every possible small relational function object requires
this decision principle. Arbitrary small covers remain a separate question.

## The exact cost of an ordinary truth selector

`TruthChoice.agda` proves, at every fixed universe level, the equivalence of:

1. selecting an actual Bool satisfying the classification relation for each
   stable proposition;
2. deciding every stable proposition;
3. weak excluded middle for all propositions, formulated as `Dec (¬ P)`.

Pointwise double-negation existence of that selector's output is proved without
these assumptions. Thus replacing the modal classifier by an ordinary host
function would derive an external weak classical principle. This is an exact
interface comparison, not a machine-checked independence theorem. It does not
exclude a genuinely internal function interpreted as a relation.

The production `Base.Classical` construction was re-inspected: `encodeB` consumes
an actual `Dec`, and `LEM→ΩResizing` assembles ordinary forward/backward functions
and their round-trip laws. A valid internal port must account for that elimination
into data as well as for the logical excluded-middle theorem.

## Primary literature: two concrete candidates

Palmgren, *On Universes in Type Theory*, Section 7, constructs a classical
proposition universe using an A-translation. Its stated closure includes
implication, conjunction, and quantification over the given small types.
Theorem 7.1 establishes stability; Theorem 7.2 gives a conservation result.
These results do not supply the full dependent universes and small function
objects needed here. The full downloaded PDF, including pp. 12–13, was read.

Source: <https://www2.math.uu.se/~palmgren/universe.pdf>.

Maietti and Sabelli, *Equiconsistency of the Minimalist Foundation with its
classical version*, Section 4, give a double-negation interpretation with
dependent types and quotients. Section 5 explicitly explains that classical
disjunction cannot eliminate into Bool. Proposition 6 proves that the
small-proposition classifier is not isomorphic to any set in this calculus;
its proof uses an external proof-theoretic upper bound. Section 6 adds resizing
rules for the impredicative extension instead of deriving them from classical
logic. Thus this particular complete translation does not meet our resizing
requirement. This is a theorem about that calculus, not a universal impossibility
result for Cubical Agda or all candidate internal interpretations.

Source: <https://arxiv.org/html/2407.09940v2#S5>.

## Validation and remaining obligation

Both new Agda files were checked with the repository compiler from this
directory, using the local Agda home and `GHCRTS='-A64m -I0 -M8g'`:

```sh
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home GHCRTS='-A64m -I0 -M8g' /Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda QuantifierTransport.agda
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home GHCRTS='-A64m -I0 -M8g' /Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda TruthChoice.agda
```

Final exits: 0, no warnings. Both use `--safe`, with no postulates or holes.
QuantifierTransport's first check exited 42 for an implicit universe parameter;
the parameter was made explicit before the successful check. No full-book gate
was run. Formal book sources were not modified.

The concrete next structural question is whether a relational interpretation
can simultaneously provide unique-description internally and a universe of
small objects closed under its dependent sums/products and set-tree formation.
The small representation of relational maps A → Bool is already a necessary
test. Neither the new quantifier interface nor the cited classical translation
settles this question. Full internal ZF and universal impossibility remain
unproved; the goal must not be marked complete.
