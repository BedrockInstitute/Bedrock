# A checked relational proposition universe and resizing isomorphism

Date: 2026-09-28. This investigation follows the user's instruction to return
to general internal Ω-resizing, rather than treating a special proof for L as
completion. The full original objective remains active and unproved.

## What is new

Previously there was a pointwise stable truth-classification relation and
conditional arguments about function covers. There is now an explicit
relational calculus with identity, composition, map equality, and isomorphism;
a universe of codes for small internally propositional objects; a decoding
operation with coherent transport; and a checked implication from a precise
internal excluded-middle statement to a Boolean classification isomorphism
for that proposition universe. No external LEM, resizing, or small classifier
is a parameter of the resulting construction.

These are results in the specified relational interpretation. They are not
yet a model of the entire dependent type theory used by Bedrock. In particular,
no universe of arbitrary small types closed under dependent products and sums
has been supplied.

## Objects, functions, and universes are kept distinct

`StableRelations.agda` defines `Object a e` as a carrier in `Type a` with
an equivalence relation in `Type e` that is proposition-valued and stable.
`Map A B r` is a graph in `Type r`, stable and proposition-valued, invariant
under the source and target equivalences, double-negation-total, and
single-valued up to the target equivalence. Composition is

```text
(G ∘ F)(x,z) = ¬¬ Σ y, F(x,y) × G(y,z).
```

Map equality is pointwise logical equivalence of graphs, including graphs
at different host levels. The file checks preservation of the map conditions,
the equivalence laws for map equality, congruence of composition, both units,
and associativity. It defines isomorphisms by two such maps and round-trip laws.
Every isomorphism induces checked round trips on maps from an arbitrary
context, and these transformations commute with context substitution.

This is a universe-graded relation calculus. The carrier, equality, and graph
levels remain explicit; composition can raise the graph level by quantifying
over its middle carrier. We have not hidden this increase with a cast, resized
it externally, or packaged this as an already completed internal type universe.

## The stable-truth object

`RelationalOmega.agda` gives `Truth ℓ : Object (suc ℓ) ℓ`, whose carrier is
`StableProp ℓ` and whose equality is biimplication of the represented stable
propositions. Its maps to and from `Boolean : Object 0 0` have the same
classification graph in opposite directions: the true fiber is P and the
false fiber is not P. The round-trip laws are proved using modal totality and
stability, without selecting an actual host Boolean for arbitrary P.

The concrete statement `RelationalOmegaResizing` and its proof are:

```text
Σ O : Object 0 0, Isomorphism (Truth ℓ) O ℓ ℓ
```

with O = Boolean. It is a relational small-presentation theorem, not a host
equivalence `StableProp ℓ ≃ Bool`.

## Codes for actual internally propositional objects

`RelationalPropUniverse.agda` goes beyond renaming stable host propositions.
It defines

```text
IsInternalProp A = ∀ x y : Carrier A, Equal A x y
PropCode ℓ      = Σ A : Object ℓ ℓ, IsInternalProp A
El P           = the object A in code P
truth P        = ¬¬ Carrier (El P).
```

`PropUniverse ℓ` has carrier `PropCode ℓ`; code equality is biimplication
between these stable truth values. All maps into an internally propositional
object are proved equal in the relation calculus. Every stable small host
proposition has such a code, and its decoded modal truth is equivalent to it.

Code equality is justified by actual decoded-type behavior:

* an equality of codes constructs an isomorphism of their decoded objects;
* an isomorphism of their decoded objects, even with higher-level graphs,
  constructs equality of their codes;
* the chosen transport maps respect identity and composition, up to map equality.

The explicit internal excluded-middle statement is

```text
InternalLEM = ∀ P : PropCode ℓ, ¬¬ Dec(truth P).
```

It is constructively proved by the usual double-negated decision argument.
The separate theorem `internal-LEM-to-prop-universe-resizing` takes that
statement as input and proves

```text
Isomorphism (PropUniverse ℓ) Boolean ℓ ℓ.
```

Its forward map's totality is built from the supplied InternalLEM. The reverse
map has explicit empty/unit proposition codes as witnesses for false/true.
The theorem checks both round-trip laws; its unconditional instance uses the
proved `internal-lem`. The parameterized round-trip theorem follows from the
general relation calculus.

Thus there is now a concrete proposition-code interpretation and a checked
LEM-to-resizing implication for it. There is still no claim that `Object ℓ ℓ`
itself has been made into an internal universe with all dependent-type rules.
An external collection of object codes is not that additional structure.

## A reusable predicate interface

`RelationalClassifier.agda` defines stable predicates invariant under an
object's equality. They correspond in both directions to relational maps
into Boolean, with checked round-trip laws. Predicate pullback along arbitrary
relational maps satisfies identity, composition, and congruence, and Boolean
classification commutes with it.

The file also constructs the comprehension object of a predicate and its
inclusion. If the object, its equality, and the predicate all have level ℓ,
that comprehension remains an `Object ℓ ℓ`. It provides a universal stable
truth predicate on `Truth ℓ`, a naming map for any such predicate, and verifies
that decoding its name recovers the predicate. We have not claimed a full
categorical universal-property proof for every comprehension or a CwF.

## The small function-object test is still a real obligation

`RelationalFunctionBoundary.agda` specializes the relation calculus to the
natural-number object and Boolean. It defines a small presentation of ALL
level-zero relational maps Nat → Boolean and constructs `PredicateCover Nat`
from any such presentation. Consequently its carrier cannot be subcountable;
`ModalAllSmallSubcountable` refutes even double-negation existence of this
presentation, using the earlier checked diagonal argument.

This is a conditional obstruction for a universe-preserving version of the
current semantics. It does not establish that modal subcountability holds
for the entire permitted Agda foundation. It also does not cover every use
of higher-level evaluation graphs or every different interpretation of small
types. A full small exponential would have to provide the relevant evaluation
and representation interface; no such exponential has been constructed here.

The positive resizing result and this obstruction are compatible: a small
object classifying predicates does not by itself supply a small object of
all maps into that classifier. This gap now occurs inside a concrete checked
interpretation, rather than being left as an unspecified internal-world issue.

## Verification and scope

The five new Agda files are `StableRelations.agda`, `RelationalOmega.agda`,
`RelationalClassifier.agda`, `RelationalFunctionBoundary.agda`, and
`RelationalPropUniverse.agda`. They were checked with the repository compiler,
local `AGDA_DIR`, and `GHCRTS='-A64m -I0 -M8g'`, sequentially. The final
RelationalFunctionBoundary check also rechecked the changed classifier file;
the final RelationalPropUniverse check exited 0. All final checks exited 0
without warnings, retaining `--cubical --safe --guardedness`.

Intermediate failures were unsolved implicit map arguments in generic
round-trip proofs, fixed by explicit arguments, and an overestimated universe
level in the first map/isomorphism record declarations. The declarations were
tightened to their actual checked levels; no resizing axiom or cumulativity
override was used. No postulates or unsolved metas remain in the checked files.

`git diff --exit-code -- src` succeeds. The worktree remains on main, with
the pre-existing untracked `dev/DOUBLE-NEGATION.md` untouched. All new research
files are ignored under `_build/double-negation-investigation`. No full-book
or website gate was run because no production source or import graph changed.

The full completion requirements remain: a concrete internal universe of
arbitrary small types with the needed dependent closure, the general resizing
module valid for that universe, and the complete internally interpreted ZF
development. Alternatively, a no-go theorem must cover the actual permitted
foundation and every allowed interpretation. Neither terminal condition has
been established. The next construction question is small function-object
closure for this explicit semantics, with higher-level representations and
their substitution rules audited rather than silently assumed.
