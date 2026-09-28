# Returning to deep first-order excluded middle

Date: 2026-09-28. The user's correction fixes the premise: excluded middle
must be expressed using the repository's deeply embedded first-order formulas.
The goal is not replaced by an independently defined semantic excluded-middle
condition on arbitrary host propositions or proposition codes. Production source
migration remains unauthorized and has not started.

## Recovered starting point

The reference branch `internal-logic-milestones`, file
`src/V/InternalClassicality.lagda.md`, defines:

```text
InternalLEMᵥ = ∀ {n} (φ : Formula S n) (γ : S ^ n), γ ⊨ (φ ∨̇ ¬̇ φ).
```

That branch uses ordinary satisfaction, whose disjunction is propositional
truncation of a sum. Its `satisfaction-decide` eliminates the truncation into
`Dec (γ ⊨ φ)`, which is a proposition. Its later Boolean characteristic
functions use these actual decisions.

The double-negation migration must distinguish syntax from interpretation:
the Formula-based excluded-middle schema is retained, but its interpretation
uses negative disjunction and existence. Eliminating a double-negated decision
into an actual host decision is not justified. The branch proof is therefore
not reusable verbatim under the new interpretation.

## Files and actual inputs

`DeepNegativeFOL.agda` IMPORTS the existing `FOL.Syntax` and syntax-renaming
operations; it does not invent an alternative formula datatype. It defines a
negative satisfaction relation for stable, proposition-valued equality and
membership atoms:

```text
Sat (φ ∨̇ ψ) γ = ¬¬ (Sat φ γ + Sat ψ γ)
Sat (∃̇ φ) γ   = ¬¬ Σ x, Sat φ (x :: γ).
```

Conjunction, implication and universal quantification use the usual negative
interpretations, and bounded quantifiers are interpreted explicitly. The file
proves satisfaction proposition-valued and stable, proves invariance under
syntax renaming with corresponding environments, and proves weakening.
It then defines the PRECISE premise consumed by the new construction:

```text
FormulaLEM = ∀ {n} (φ : Formula S n) γ, Sat (φ ∨̇ ¬̇ φ) γ.
```

`negative-formula-lem` proves this premise constructively for the defined
negative satisfaction. It is not an assumption of external LEM, and the next
file receives this Formula-based premise explicitly rather than bypassing it.

This is a semantics and theorem about satisfaction. No new deep derivation
calculus or proof of soundness for every rule of such a calculus is claimed.
The original branch likewise expressed its premise through satisfaction.

## A first-order candidate for internal truth-universe resizing

Work with empty set e, singleton u = {e}, and the pair o = {e,u}. All three
specifications are actual `Formula S 0` terms. The generic proof explicitly
assumes their satisfaction, equality congruence for membership, and
extensionality. It does not assume separation, replacement, powerset,
exponentiation, resizing, or any classifier.

`DeepFOLOmega.agda` constructs and proves these two objects of deep syntax:

```text
OmegaFormula:
  ∀p. p ∈ o ↔ ∀x. (x ∈ p → x = e)

RepresentFormula φ:
  ∃p. p ∈ o ∧ (e ∈ p ↔ φ).
```

For the second formula the code explicitly weakens φ under the new p binder;
the semantic weakening theorem checks that no variable is captured. It holds
for arbitrary arities and environments, not just closed formulas.

The first statement presents the entire internally defined class of subsets
of the singleton as an internal set. Given p in that class, apply the supplied
deep excluded middle to the ATOMIC formula `e ∈ p`. In the positive branch,
extensionality identifies p with u; in the negative branch, with e. The branches
are combined into the stable membership conclusion, without extracting an
external decision. Conversely every element of o is such a subset.

The second statement applies the supplied deep excluded middle to φ itself.
The positive branch uses u as its truth representative; the negative branch
uses e. The witnesses remain under the internal existential, as required by
the negative satisfaction clause. A further checked theorem proves that two
members of o representing the same formula are equal in the internal equality.

These are two distinct obligations: a single internal set of truth objects,
and a representation schema covering every formula of the specified language.
Together they are a candidate FIRST-ORDER truth-class resizing interface.
They are not a theorem that a host universe of all propositions has resized,
nor yet an interface proved sufficient for every original consumer.

## The elementary sets are constructed, not left as hidden assumptions

`DeepFOLOmegaTrees.agda` instantiates the above theory with the previously
constructed modal trees. The carrier is `Tree 0`, equality is the modal
bisimulation, and membership is modal membership. Small atomic propositions
are LIFTED to the carrier's level for this satisfaction relation; no proposition
is lowered externally. Explicit witnesses are:

```text
e = the empty tree
u = the singleton tree containing e
o = the Bool-indexed tree with branches e and u.
```

All elementary set specifications and equality/membership compatibility used
in the generic proof are derived from existing constructive tree lemmas.
The file exports both the implication parameterized by FormulaLEM and its
instance using `negative-formula-lem`. It has no external LEM or resizing
parameter. It does not import the previously developed relational proposition
universe or its separately named InternalLEM.

The candidate tree structure has not thereby become a full ZF model. In
particular, this test does not supply general replacement, general power sets,
or a complete equality/substitution soundness development for all formulas.

## Why this is progress but not the end of the resizing problem

The result answers a precise intermediate question positively: deep formula
excluded middle can derive an internal set of singleton-subset truth codes and
formula-by-formula unique truth representation, with all statements written
in the original first-order syntax. A new internal dependent type theory is
not needed for this proof.

It does not follow that arbitrary powersets exist. Collecting the truth
values of a family into an internal function requires appropriate set
construction principles. Collecting ALL such functions requires a function
set/exponentiation principle. We must investigate these as FIRST-ORDER set
statements in the SAME negative interpretation; returning to unrelated host
function spaces would repeat the scope error identified by the user.

There is an exact scope check. In ordinary classical mathematics,
H_(omega_1) satisfies ZFC without powerset (including collection), hence
formula LEM and both displayed truth-code assertions. Every subset of omega
belongs to H_(omega_1), but their total collection does not: any member of
H_(omega_1) is externally countable, whereas P(omega) is uncountable. Therefore
even adding these truth-code assertions to the other classical set axioms
cannot by itself imply the general powerset axiom. Classical satisfaction
also agrees with its double-negation variant in that classical metatheory.

The model fact is documented in Gitman, Hamkins and Johnstone,
[What is the theory ZFC without power set?](https://arxiv.org/pdf/1110.2430),
pp. 1–3. The failure of powerset for this particular H_(omega_1) is the direct
cardinality argument just given. This is a counterexample to a specified
logical implication, not an impossibility theorem for every construction
allowed by the original project.

The relevant positive bridge is also explicit in the literature: over CZF0,
exponentiation plus the sethood of P(1) gives powersets. See Aczel, van den Berg,
Granström and Schuster, [Are There Enough Injective Sets?](https://arxiv.org/pdf/1111.5180),
p. 6. Its background axioms must be checked; this citation does not supply
them for our negative tree interpretation.

The next task is therefore a consumer audit stated entirely in deep FOL:
identify and prove the required first-order replacement/collection and
exponentiation instances, or find an applicable obstruction for those
instances. Neither those principles nor a universal impossibility result
has been obtained in this round.

## Validation and limitations

All three new files were checked sequentially with the repository compiler:

```sh
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home GHCRTS='-A64m -I0 -M8g' /Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda -i . -i /Users/alsg/Agentic/Bedrock/src DeepNegativeFOL.agda
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home GHCRTS='-A64m -I0 -M8g' /Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda -i . -i /Users/alsg/Agentic/Bedrock/src DeepFOLOmega.agda
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home GHCRTS='-A64m -I0 -M8g' /Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda -i . -i /Users/alsg/Agentic/Bedrock/src DeepFOLOmegaTrees.agda
```

All exited 0 with `--cubical --safe --guardedness`. There is one explicit
`UnsupportedIndexedMatch` warning in DeepNegativeFOL.lifted-environment,
lines 83–84: indexed Fin pattern matching does not compute on transports.
The warning was not disabled; it does not report an unsolved proof obligation,
but the limitation must be retained if this syntax infrastructure is reused.
No postulates, termination bypasses or unsolved metas were introduced.

The process check found no active Agda process before these sequential checks.
`git diff --exit-code -- src` exited 0. The worktree remains main with only the
pre-existing untracked dev/DOUBLE-NEGATION.md visible. All three proof files and
this report are ignored research artifacts. No full Origin or website check
was performed.
