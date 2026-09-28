# Boolean relation functions and modal power sets

Date: 2026-09-28. The preceding goal turn was progress: it supplied checked
quantifier and truth-choice results and a literature exclusion. This turn adds
two checked bridges. The full assumption-free internal ZF objective remains
unresolved. No production migration is claimed.

## A small cover supports relational currying

`RelationalExponential.agda` takes an explicitly conditional input:
`FunctionCover A` from `RelationalTruth.agda`. This consists of a small type E,
a family of stable, double-negation-total, single-valued relations A → Bool,
and double-negation coverage of every such relation.

Define equality of names i,j in E by pointwise logical equivalence of their
represented relations. It is a stable proposition. A map C → E is represented
by a stable proposition-valued graph, double-negation-total on C, single-valued
up to this equality, and invariant under replacing an output by an equal name.

For every host parameter type C, at any level, and every family F of Boolean
relation maps indexed by C, the experiment constructs:

```text
curry(F)(c,i) := the relation F(c) agrees with the relation named by i.
uncurry(K)(c,a,b) := ¬¬ Σ i:E, K(c,i) × evaluation(i,a,b).
```

It checks:

* the curried graph has all the stated map properties;
* beta: `uncurry(curry(F))` and F agree at every parameter and argument;
* eta: any graph K with the same uncurried relation agrees with `curry(F)`.

No actual representative i is extracted from double negation. Thus relational
functions have a valid parameterized beta/eta interface once the small cover is
available. The experiment does not axiomatize or verify an entire category,
products of arbitrary stable setoids, dependent exponentials, or internal
universe substitution. Its beta/eta statement is for the precise graph interface
above; it must not be reported as a completed internal type theory.

## An exact bridge to the tree power-set obligation

`FunctionPower.agda` assumes an index presentation `f : A → Tree ℓ` injective
for the internal tree equality. Then every stable predicate on A is automatically
saturated for that presentation. Packing and unpacking these predicates gives
mutual conversions:

```text
PredicateCover A  ↔  DenseCover f.
```

Combining these conversions with the previously checked results produces:

```text
FunctionCover A  ↔  PowerWitness f
¬¬ FunctionCover A  ↔  ¬¬ PowerWitness f.
```

Here arrows denote constructions in both directions, not round-trip laws for the
witness types. `PowerWitness f` states precisely that a tree contains exactly
the internal subsets of `sup A f`. The statement ranges over the current modal
tree model, not all conceivable interpretations of sets.

The file specializes both directions to the previously constructed injective
natural-number-indexed family `chain`. Its image is an internally discrete
countably indexed set (not asserted to be the von Neumann omega). Thus the
power set of this concrete infinite set already measures the required small
representation of Boolean relation functions on natural-number indices.

This is useful because it removes a possible ambiguity: fixing relational
currying does not itself construct the cover. The cover contains a genuine
power-set obligation. Conversely, a power witness would supply exactly the
cover needed for the checked relational currying construction.

## Literature and limits of a universal impossibility argument

The weak-predicate-classifier versus weak-power-object distinction is standard:
cartesian closure is needed to pass from a classifier to power objects. A recent
primary presentation states these separately in Definitions 2.22–2.25 and
Remark 2.24 of *A topos for extended Weihrauch degrees*:
<https://doi.org/10.1016/j.apal.2026.103781>.
This is background agreement, not a theorem instantiating our Agda structures.

A separate audit checked Dybjer–Setzer, *An extended predicative Mahlo universe
in Martin-Löf type theory*, Section 7 and footnote 2:
<https://academic.oup.com/logcom/article/34/6/1032/7158523>.
The paper reports Agda-checked definitions beyond its earlier IR/IIRD schemas.
Its proposed proof-theoretic upper bound for IR/IIRD is explicitly not worked
out. Therefore that proposed bound cannot be cited as a proved upper bound
for all definitions accepted by Cubical Agda, or as a universal no-go theorem
for this task. This source does not establish that our desired cover exists.

## Validation

Checked sequentially from this directory with:

```sh
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home GHCRTS='-A64m -I0 -M8g' /Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda FunctionPower.agda
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home GHCRTS='-A64m -I0 -M8g' /Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda RelationalExponential.agda
```

Both final exits were 0 with no warnings; both retain `--safe` and contain no
postulates or holes. The process inventory was empty before compilation.
No complete Origin or website checks were appropriate for these isolated
experiments. No `src/` changes were made.

The unresolved construction target is now explicit: derive the small function
cover, or construct an internal universe whose function objects and smallness
are interpreted differently and prove that it supports the complete ZF
development. Merely postulating the cover violates the user's boundary.
Relational beta/eta laws and a conditional power witness do not complete the
goal. A universal impossibility result is also not established.
