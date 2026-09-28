# A vertex-cardinality obstruction for the modest-family universe

Date: 2026-09-28. The preceding turn made progress by checking the
subcountability diagonal theorem. This turn audits the proposed semantic
argument directly, without assuming internal subcountability of all cubical
types. The full original objective remains unresolved.

## Published ingredients and scope

Source: Taichi Uemura, *Cubical Assemblies, a Univalent and Impredicative
Universe and a Failure of Propositional Resizing*,
<https://drops.dagstuhl.de/opus/volltexte/2019/11411/pdf/LIPIcs-TYPES-2018-7.pdf>.

The inspected ingredients are Theorems 4 and 7, Proposition 6, the presheaf
universe construction in Section 4.1, Proposition 16, and Section 5's PER
universe. These give a fibrant universe classifying pointwise modest families.
Its decoded fibers remain the underlying presheaf fibers. The cube category
has a terminal zero-dimensional object and vertices for every cube. Constant
presheaves are discrete and admit fibrancy. PER codes have a common realizer,
whereas distinct elements of a decoded modest assembly have disjoint nonempty
realizer sets.

Remark 20 distinguishes this universe from the model's predicative universes.
The conclusion below concerns the modest-family universe only. It is our
derived argument, not a theorem attributed to the paper. It is a handwritten
semantic argument, not an Agda-checked implementation of the model.

## Derived argument

Work in an ordinary classical set metatheory for the semantic cardinality
argument. This metatheoretic reasoning is not an axiom added to Bedrock.
Write U for the fibrant modest-family universe, and v for the terminal cube.

### 1. U-small types have at most countably many vertices

For a closed U-small type E, its vertex assembly E(v) is modest. For each
underlying element choose its least natural-number realizer. Nonempty,
pairwise disjoint realizer sets make this an injection of the underlying
set of E(v) into Nat. No assertion of *internal* countability follows or is
needed.

### 2. Every external subset of Nat determines a stable small predicate

Fix an arbitrary external subset S of Nat. Over the constant natural-number
context, define P_S(n) to be the constant singleton assembly with realizer 0
when n belongs to S, and the empty assembly otherwise. The family is classified
by PER: its code map is tracked by the constant common realizer of PER, so
membership in S need not be computable.

The family is constant in the cube direction over a discrete base. Composition
returns the supplied endpoint element; this is uniform in n and S. It therefore
gives a small fibration. Each fiber is a strict proposition. Stability also has
a uniform tracker: return the singleton realizer 0. At a false fiber the
double-negated domain is empty, so there is no input on which this tracker
would have to produce an inhabitant of the empty fiber. Hence P_S is a global
stable predicate on Nat. At vertices it is inhabited exactly at the elements
of S.

This construction uses the universe's uniform codes, not a computable Boolean
characteristic function of S. Confusing these is precisely the erroneous
step that would make the argument appear to prove external decidability.

### 3. Closed double-negation existence implies nonemptiness at vertices

For any closed type X in this model, if X(v) is empty then X(c) is empty at
every cube c: restriction along a vertex v → c would otherwise produce an
element of X(v). Thus X is the empty presheaf and has a map to the empty type.
A closed inhabitant of double negation of X is consequently impossible.
Classically in the metatheory, a closed inhabitant of double negation of X
therefore entails that X(v) is nonempty. This does not supply an internally
chosen inhabitant, or a context-uniform choice principle.

### 4. A small dense predicate cover is impossible

Suppose there were a closed witness of the analogue of `PredicateCover Nat`
with index E small in U. Each i in E(v) determines the external subset

```text
S_i = { n in Nat | the vertex fiber of family(i)(n) is nonempty }.
```

Given any external S, instantiate the claimed coverage at P_S from step 2.
It yields a closed inhabitant of the double negation of the type of pairs
consisting of i:E and pointwise biimplications between P_S and family(i).
Step 3 provides a vertex of this type. Evaluating its biimplications at each
natural number shows S_i = S. Thus i ↦ S_i is a surjection from the at most
countable set E(v) onto the external power set of Nat, contradicting Cantor's
theorem.

The same argument rules out double-negation existence of a cover: a closed
double-negated cover would yield a vertex of its witness type by step 3.
An element at the terminal cube gives a closed element using restriction
along the unique maps from all cubes to that cube, reducing to the preceding
contradiction.

## What this excludes, and what is still not justified

The argument gives a semantic obstruction to the specific small dense cover
interface in a univalent universe of modest families. Through the already
checked `functions-to-predicates` conversion, it also obstructs the matching
small cover of Boolean relation functions. Internal negative excluded middle
continues to hold, since its proof is constructive. Thus these two properties
are separated in this setting.

It is legitimate to conclude nonderivability from a calculus whose rules and
universe are validated by this model. It is not legitimate to extrapolate to
every definition accepted by the installed Cubical Agda. The following
obligations remain before using this as the requested universal no-go theorem:

* validate the relevant full hierarchy and the allowed inductive-recursive,
  higher-inductive, and other extensions in one chosen model;
* justify compatibility with the precise cubical primitives if the argument
  is applied to the concrete compiler rather than abstract univalent type
  theory (the paper's chosen Bord cube category is not simply Agda's syntax);
* show that every internal interpretation permitted by the user's requirements
  yields this cover at the required host universe. This fails as an immediate
  inference if internal smallness is represented differently or the internal
  predicate domain is restricted.

The result therefore excludes the particular universe-preserving relational
infrastructure in the modeled fragment; it does not settle the original
unrestricted existence question. Moving to a larger external universe does
not follow from this argument either: those universes need a separate audit.

## Verification record

This turn inspected the source definitions and theorem statements listed above
and checked the four steps of the semantic argument. No new Agda file was
written or compiled; there is no new compiler result to report for this
handwritten model argument. `git diff --exit-code -- src` remained successful,
and no formal book source or Git state was changed.
