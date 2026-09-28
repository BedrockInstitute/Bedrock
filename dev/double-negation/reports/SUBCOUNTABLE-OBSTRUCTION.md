# Subcountability obstructs stable predicate covers

Date: 2026-09-28. The preceding goal turn was progress: two checked bridges
connected Boolean relation functions to modal power sets. This turn strengthens
the diagonal obstruction and audits two semantic sources. The original full
goal is neither achieved nor universally refuted.

## Checked obstruction

`SubcountableObstruction.agda` defines a deliberately weak form of
subcountability for a small type I:

```text
D : Nat → hProp 0
enumerate : (Σ n:Nat, D(n)) → I
∀ i:I, ¬¬ Σ nd, enumerate(nd) = i.
```

The domain need not be decidable. Surjectivity is required only under double
negation. Ordinary subcountability with actual or propositionally truncated
surjectivity therefore supplies this interface.

The experiment proves that the index of any `PredicateCover Nat` cannot be
subcountable in this sense. Here the covered predicates are the small stable
propositions on Nat, and coverage itself is already under double negation.
This strictly extends the earlier exclusion of Nat-indexed covers and quotients
of such covers: now a quotient of an arbitrary, possibly undecidable subset of
Nat is also excluded.

The proof extends a partially enumerated family R to a Nat-indexed stable
family:

```text
extended(n)(k) := ¬¬ Σ d:D(n), R(enumerate(n,d))(k).
```

For an inhabited D(n), this agrees with the corresponding original predicate:
proof irrelevance of D(n) identifies all its enumerated indices, and stability
removes the outer double negation. Coverage would then give a Nat-indexed cover,
contradicted by the stable diagonal `n ↦ ¬ extended(n)(n)`.

Consequently, under the explicitly hypothetical principle that every small
type is subcountable, neither `FunctionCover Nat` nor `PowerWitness chain`
exists. Even double-negation existence of that power witness is refuted. The
same nonexistence conclusion needs only pointwise double-negation existence of
subcountable presentations, so no simultaneous selection of presentations is
necessary. These principles are countermodel conditions, not proposed axioms
to add to Bedrock.

## A genuine set-theoretic exclusion with bounded scope

Van den Berg and Moerdijk, *Aspects of Predicative Algebraic Set Theory II:
Realizability*, Theorem 1.5 and Corollary 1.6, construct a CZF model with full
separation in which all sets are subcountable. Section 6 and Remark 6.9 discuss
the corresponding small-map/modest-family construction.

Primary source:
<https://www.phil.cmu.edu/projects/ast/Papers/vdb_m_aspects_ii.pdf>.

The elementary diagonal proof above has a set-theoretic counterpart. Suppose
a set I indexed a family of stable subsets of Nat covering every stable subset
up to double-negation existence of an equivalent name. A partial surjection
from Nat to I would yield the same extended family and diagonal contradiction.
The diagonal is definable by bounded separation from the given family and
partial enumeration; no impredicative truth predicate is required.

Thus, relative to the cited model's consistency assumptions, **CZF alone cannot
prove this dense stable-power-set principle**, nor its double negation. The
conclusion is about this specified principle and base theory. The Agda file
checks the type-theoretic diagonal argument; it is not a formalization of the
published model or a proof of its consistency.

In particular, an arbitrary predicative category with the small-map conditions
needed for CZF cannot be assumed to supply our covers after Booleanization.
Extra closure must be established; it is not a generic consequence of having a
CZF-style constructive set model.

## Why this is not yet a Cubical Agda impossibility theorem

Uemura, *Cubical Assemblies, a Univalent and Impredicative Universe and a Failure
of Propositional Resizing*, Section 5, refutes resizing into a particular
impredicative universe classifying modest families. Remark 20 explicitly leaves
resizing between its predicative universes unresolved. Section 6 discusses
extensions by some higher inductive types.

Primary source:
<https://drops.dagstuhl.de/opus/volltexte/2019/11411/pdf/LIPIcs-TYPES-2018-7.pdf>.

This is not a ready-made countermodel for our entire task. In particular:

* failure of ordinary propositional resizing does not by itself refute the
  relational cover used in our negative interpretation;
* the model's modest-family universe must not be conflated with its separate
  predicative universes;
* neither cited paper, as inspected, establishes our internal
  `ModalAllSmallSubcountable` for every needed Cubical Agda universe;
* the original objective permits a different internal interpretation and does
  not require its small objects to be represented by our current small host
  index types.

There is a possible external cardinality argument worth auditing separately:
a modest zero-dimensional fiber has countably many elements, whereas stable
predicates on Nat may encode arbitrary external subsets. To use this argument
one must verify the uniform fibrancy and stability of those predicate families,
how double-negation coverage is reflected at vertices, and the universe and
inductive-type closure of the chosen model. None of those obligations is
silently supplied by the checked conditional subcountability theorem.

## Validation

The new file passed the pinned compiler twice, with the second run checking
the added weakening to modal existence of subcountable presentations:

```sh
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home GHCRTS='-A64m -I0 -M8g' /Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda SubcountableObstruction.agda
```

Both exits were 0, with no warnings. The file uses `--safe`, contains no
postulates or holes, and was checked after confirming no other Agda process
was running. No formal book sources were changed and no whole-book gate was
run. The next semantic task is the explicit model/universe audit above, rather
than repeating the now-proved diagonal construction.
