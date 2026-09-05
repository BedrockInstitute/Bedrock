# Probe report: the cut theorem and the closure-style internal tower

Probe run 2026-08-01 on the working tree of `godel-route` (uncommitted M5a
re-cut present in `src/L/Godel/Name.lagda.md` and `src/L/WellOrder/Base.lagda.md`;
no `src/` file was touched by this probe). Deliverables: `_build/probe/CutProbe.agda`
(Unknown 1, green) and `_build/probe/StepProbe.agda` (Unknown 3, green). All
timings are wall-clock on the warm tree, probe checked from scratch; no
interface conflicts occurred, no 60-second retries needed.

## 1. Verdict

**NO-GO on the fork as specified, with a priced partial salvage: the decisive
finding is that the naive values-cut over an unkinded closure is unsound (the
seed-cut junk `values (A ∩ ⟦t⟧)` escapes `𝒟ₒ A` for non-transitive carriers),
so the closure must carry arity kinding in its level structure, and the flat
name order cannot stay flat (its arguments are closure members, and a total
order on the closure carrier is only internal if the levels carry per-member
construction records, which is the certificate returning).** The closure-tower
half is salvageable at a structural price: a kinded arity-indexed level table
with kinded op clauses (Unknown 3 assembles from the delivered descriptions,
green at ~1.5 s), whose meta-level kinded-invariant induction replaces the
delivered per-entry certificate, priced at roughly 40 to 60 percent of the
delivered `Codes`+`Table`+`Tower` cost; the flat order should be dropped and
the delivered skeleton/parameter order kept.

## 2. Unknown 1: the cut condition and its theorem

### 2.1 The chosen cut condition

The naive values-cut with an arity guard, `v ∈ B ⇔ ∃u ∈ ⋃ₙ Lₙ. u ⊆ allTuples A 1 ∧ v = values u`,
is **not sound over a flat closure**, and the naive subset-cut `v ∈ cl(A) ∧ v ⊆ A`
fails for the same reason. The sound form is the **kinded values-cut**: the
closure level is an arity-indexed table `t = { (k, Sₖ) }` (functional in `k`,
the "level-table functionality conjunct" of Unknown 3), the step applies each
operation only inside a slice of the arity it respects (intersection, union,
difference, selections, and allTuples stay within a slice; extendFamily moves a
slice up by one; shiftDown moves a slice down; values reads slice one and
writes slice zero; a singleton-family slice feeds the constant-atom
composites), and the cut reads slice zero: `v ∈ B ⇔ ∃u. (0, v) ∈ ⋃ₙ tₙ` with
slice one's members constrained to be satisfaction sets.

The theorem, stated against the real library in `CutProbe`:

```
CutMem Clos v = ∥ Σ[ u ∈ V ] (⟨ u ∈ Clos ⟩ × ⟨ u ⊆ allTuples A 1 ⟩ × (values u ≡ v)) ∥₁

cut-sound : kinded-invariant Clos → (v : V) → CutMem Clos v → ⟨ v ∈ Def A ⟩
cut-complete (LEM) : (terms reach Clos) → (v : V) → ⟨ v ∈ Def A ⟩ → CutMem Clos v
```

where `kinded-invariant Clos` says every arity-one member of `Clos` is a
satisfaction set (`∃φ. u ≡ satSet A φ`), and "terms reach Clos" is the
terms-to-levels lemma kept abstract in the probe. Both directions are proved
in `CutProbe` against the banked lemmas:

- **Soundness** (`cut-sound`, `_build/probe/CutProbe.agda:322`, heart at
  `valuesSatSet` `:310`): the kinded invariant gives `u ≡ satSet A φ`; the
  banked bridge `sat-defSet` (`src/L/Godel/Satisfaction.lagda.md:744`) gives
  `values u ≡ defSet φ`, and the fiber of `Def` closes. No new mathematics.
- **Completeness** (`cut-complete`, `_build/probe/CutProbe.agda:347`): the
  banked `termDef≡Def` (`src/L/Godel/Terms.lagda.md:336`) gives, under LEM,
  `v = values ⟦t⟧` for an arity-one term `t`; `⟦t⟧ ⊆ allTuples A 1` by
  `sound` (`Terms.lagda.md:145`) and the probe's `satSet⊆`
  (`CutProbe.agda:331`); the abstract terms-to-levels lemma places `⟦t⟧` in
  the closure.

### 2.2 The junk-case table

Four concrete junk cases, each stated and proved (or, for the escape, stated
with its easy direction proved and its negation recorded) in `CutProbe`:

| case | closure member | values-cut | verdict | why |
|---|---|---|---|---|
| 1. mixed-arity intersection | `allTuples A 1 ∩ allTuples A 2` | `∅` | lands inside | graphs of length-1 and length-2 assignments are disjoint (`allTuples-12-disjoint`, `CutProbe.agda:86`, via `extendGraph` shape analysis); `∅ = defSet ⊥̇` (`defSet⊥` `:124`), so `∅ ∈ Def A` (`∅∈Def` `:127`) |
| 2. same-arity intersection | `allTuples A 1 ∩ allTuples A 1` | `defSet (⊤̇ ∧̇ ⊤̇)` | lands inside | banked `sat-⊤`, `sat-∧`, `sat-defSet` (`goodInter` `:136`, `goodInter∈Def` `:143`) |
| 3. mismatched complement | `allTuples A 2 ∖ allTuples A 1` | `A` | lands inside | disjointness makes the difference the whole family; `values (allTuples A 2) ≡ A` (`valuesAllTuples2` `:158`); `A = defSet ⊤̇` (`defSet⊤` `:240`, `A∈Def` `:253`) |
| 4. seed cut | `A ∩ allTuples A 1` | `{ v : ⟨ {pr ∅ v} ∈ A ⟩ }` | **escapes in general** | `values (A ∩ allTuples A 1) ⊆ A` is proved (`junkSeedInter` `:265`); membership in `Def A` requires the condition "the code of the singleton assignment at v is in A" to be first-order definable in `(A, ∈)`, which fails for non-transitive `A` (automorphism argument below); recorded as the postulate `escape-witness` (`CutProbe.agda:295`) |

The escape case is the crux. `v ∈ values (A ∩ allTuples A 1)` says exactly
`{pr ∅ v} ∈ A`, and a definable subset of `A` must be invariant under the
automorphisms of `(A, ∈)`. Choose `A = { x , y , c }` with `x = {∅}`,
`y = {{{∅}}}` and `c = { pr ∅ x }` (the code of the length-1 assignment at
`x`): within `(A, ∈)` no two members are related by membership, so every
permutation of `A` is an automorphism, yet `{ v ∈ A : {pr ∅ v} ∈ A } = { x }`
is not fixed by the permutation swapping `x` and `y`. Hence it is not
definable, and `values (A ∩ allTuples A 1) ∉ Def A`. This is a
model-theoretic argument; it is not expressible in this library, which is why
it enters the probe as a single flagged postulate.

The escape is a **non-transitive** phenomenon: for transitive carriers (the
tower's actual carriers, the L-stages) the condition "{pr ∅ v} ∈ A" is
expressible, because every quantifier in the spelled-out "the set with exactly
the members {∅} and {∅,v} is a member of A" lands in the carrier. But the
internal step description cannot assume transitivity without adding a
transitivity conjunct, and the naive cut's soundness proof would still need
that tuple-unpacking argument (the brief's option 2) at every junk shape. The
kinded design eliminates the junk by construction, so the escape never arises:
there is no clause that applies an operation across slices.

### 2.3 What is proved versus postulated in `CutProbe.agda`

Proved (all typechecked): `mixedArityInter`, `goodInter`, `junkComplement`,
`junkSeedInter` (the easy direction), `valuesSatSet`, `cut-sound`,
`satSet⊆`, `cut-complete` (under LEM), and the supporting algebra
(`allTuples-12-disjoint`, `valuesAllTuples2`, `∖-disjoint`, `defSet⊥`,
`defSet⊤`, `∅∈Def`, `A∈Def`).

Postulated (exactly one, flagged): `escape-witness`
(`CutProbe.agda:295`). Confidence: high; the argument is the automorphism
construction above, which is standard model theory. Expected proof cost: not
priced as production work; formalizing it would require a model-theoretic
development (automorphism-invariance of definable sets over `(A, ∈)`) that is
not in the library and is not needed by any production chapter, since the
kinded design never produces the junk member. The naive-cut soundness theorem
is deliberately **not** postulated: the escape witness is its falsifier, and
the report records the naive claim as rejected.

### 2.4 The priced remaining work for the kinded values-cut

The internal side (the closure chapter) plus the cut theorem's assembly:

1. **New meta lemmas, three small ones** (~80 to 140 lines total): the
   selections on satisfaction sets (`selectMember (satSet φ) ⁅#i⁆s ⁅#j⁆s ≡
   satSet (φ ∧̇ var i ∈̇ var j)`, and the `selectEqual` analog), and the
   family extension on satisfaction sets (`extendFamily (satSet φ) ⁅κ a⁆s ≡
   satSet ((var 0 ≐ con a) ∧̇ rename-shift φ)`), both by the tuple algebra and
   the banked `sat-resp`/renaming. The probe's `valuesAllTuples2` generalizes
   to `values (allTuples A k) ≡ A` with no new ideas.
2. **The singleton-family slice** (~60 to 120 lines): the constant-atom
   composite `selEqConK` requires the set `{κ a}` as an argument to
   `extendFamily`, so the closure must contain the family `{ {x} : x ∈ A }` or
   a singleton operation with its `At`-description and constructibility. This
   operation is missing from the memo's stock (`dev/memos/L3.28-ac-route.md`
   §4.1) and is a genuine price item found by the probe.
3. **The kinded-invariant meta-induction** (~150 to 250 lines): level by level,
   every member of slice `k` is a satisfaction set at arity `k`, each clause
   discharging through the banked equations (`sat-∧`, `sat-∨`, `sat-¬`,
   `sat-⊤`, `sat-∃`, `sat-∈vv`, `sat-≐vv`, `sat-defSet`) plus the three new
   lemmas above. This is the closure-level analog of `Terms.sound`
   (`Terms.lagda.md:145`) and replaces the delivered certificate's honesty
   induction.
4. **The terms-to-levels lemma** (~80 to 150 lines): one term induction, each
   constructor's denotation produced by the corresponding kinded clause of the
   level step (the `StepProbe` layer clauses are the pattern).
5. **The internal closure chapter** (~700 to 1,100 lines): the level-table
   ω-recursion (Sequence-class), the 10-clause step description with the
   functionality conjunct (Unknown 3 validated the shape on three clauses),
   approximation, graph, `mereFunct` assembly.
6. **The Def-equivalence against the internal description** (~150 to 300
   lines): the probe's meta `cut-sound`/`cut-complete` transported through the
   internal readings, in the `Tower`-style `step-out`/`step-in` shape
   (`src/L/Godel/Tower.lagda.md:2083`).

Total for Unknown 1: roughly 1,200 to 2,050 lines, against the delivered
codes-table-certificate cluster (`Codes` 277 + `Table` 1,562 + `Tower` 2,130
file lines), a saving of roughly 1,000 to 2,000 lines, with the per-entry
certificate (`CertAt`, `Tower.lagda.md:1204`) and its honesty induction
deleted. The kinded invariant is carried by the level table's arity indexing
and clause structure, not by per-member provenance, which is the difference
between this design and the certificate.

## 3. Unknown 2: the flat name order's honest shape

### 3.1 What flattening actually gives

The flat name for a member of `𝒟ₒ A` is a birth-level/tag/arguments triple.
Flattening the operations honestly means the tag set must carry the numeral
and `Fin` parameters of the arity-indexed operations: `allTuples` takes a
numeral, the selections take two `Fin` indices, the constant leaf takes a
carrier member. The triple is therefore `(birth, tag, numeral-params, args)`
with a variable-length parameter block, and the order is lexicographic with
the numeral order on the numeral block (all available from the combinator kit,
`src/L/WellOrder/Base.lagda.md`, `natSWO`/`sumSWO`/`prodSWO`/`pullSWO`). The
SWO-composability is not the problem: sums, lexicographic products, and
pull-backs are all in `Base`, and well-foundedness is the standard
lexicographic descent.

### 3.2 The completeness obligation: the argument carrier

The completeness obligation is where the flat design breaks. From
`v ∈ 𝒟ₒ A`, `termDef≡Def` supplies an arity-one term, and the term's top node
gives a triple whose arguments are denotations of subterms: closure members of
mixed arity, not members of `𝒟ₒ A` and not members of the stage. The order
below (the stage's SWO, which is all the Naming interface has) does not cover
them. Comparing arguments therefore requires a total order on the **closure
carrier**, and there is no such order available from the flat levels:

- Birth level is internal (the levels are the recursion's values), but the
  within-level tie-break is not. A level is a flat set of sets; a member `x`
  of level `n+1` does not carry its construction, and an intersection does not
  determine its factors, so no formula can recover `(tag, arg₁, arg₂)` from
  `x` alone.
- Ordering the closure carrier by `(birth, construction)` therefore requires
  the levels to store a name or construction record per member. That is
  per-member provenance, the certificate returning in a different costume,
  and it is exactly the machinery (`Codes`+`Table`+`Tower`) the fork set out
  to delete.
- The alternative, ordering within a level by the L-order on the level set,
  is unavailable: the tower builds the order stage by stage, and at the time
  of the step for `A = Lset δ` the closure members lie in `Lset (δ + K)` for
  a fixed climb `K` (`src/L/Godel/InL.lagda.md`, the climb lemmas), whose
  orders do not exist yet. Using them would be circular.

So the flat order does not stay flat: it quietly re-grows a syntax (the
construction trees of closure members), and the honest name after flattening
is a tree over the op alphabet whose leaves are the seeds and the carrier
members, ordered shortlex. That is the delivered `L.WellOrder.Tree` order
(`Tree` 378 lines, HEAD) or the M5a skeleton order, not a new flat structure.

### 3.3 Price comparison against the skeleton design

The flat order's honest price is: the closure levels must be derivation-carrying
(approximately the certificate's annotation-table machinery, `Tower`'s `CertAt`
branches and honesty, `Tower.lagda.md:1204` and the `d2` honesty batches), plus
the order's own assembly, plus the closure carrier's order recursion. That is a
net cost of roughly the delivered cluster again, with nothing deleted.

The delivered skeleton/parameter order (M5a ruling, `dev/PLAN.md:1123`) orders
the **syntax**, not the denotations: a name is an arity-one term, pictured as
a labelled tree, stripped to a parameter-free skeleton coded as a
hereditarily finite set and ordered by `limitOrder`, then by the parameter
list ordered pointwise by the stage's order (working tree
`src/L/Godel/Name.lagda.md:509-519`, `keyOrder = prodSWO limitOrder (listSWO w)`).
Its arguments are never closure members: the skeleton compares numerals and
tags, and the parameters are stage members ordered by the existing order. No
closure-carrier order is needed. Its price is `Tree` 378 + `Name` 258 (HEAD)
or the in-progress re-cut (~560 working-tree lines, with unfinished lemmas),
plus `Base`'s additions, and it is mostly sunk: the re-cut is the current
branch state. **Verdict: the flat order is a NO-GO; the skeleton order is the
cheaper honest design and should be kept.**

## 4. Unknown 3: one closure step against the delivered library

`_build/probe/StepProbe.agda` writes the closure layer over level slots:

- `FunAt` with both readings (`Fun-out`/`Fun-in`, `StepProbe.agda:62-90`),
  the level-table functionality conjunct, in the delivered `Tower` idiom
  (`Tower.lagda.md:477`).
- The three representative disjuncts as one disjunctive layer formula:
  `InterDisjAt` (entry is a pair `(k, z)` with `z = X ∩ Y` for same-arity
  members of the previous level), `AllTuplesDisjAt` (entry is `(m, allTuples A m)`
  with the arity entering as the entry's own numeral, the Table chapter's
  conditional-clause pattern), `ValuesDisjAt` (entry is `(0, values X)` for an
  arity-one member `(1, X)` of the previous level).
- `LayerAt` (every member of the next level is in the previous level or one
  of the three op-images) and `LayerDesc = LayerAt ∧ FunAt`.
- **The layer's out-reader for the intersection disjunct**, proved: `InterDisj-out`
  (`StepProbe.agda:102-123`) extracts `(k, z, X, Y)` with
  `fst e ≡ pr (fst k) (fst z)`, both slice memberships, and `fst z ≡ fst X ∩ fst Y`,
  discharging the intersection via the delivered `interAt-out`
  (`src/L/Godel/Definable.lagda.md:406`); `Layer-inter-out` (`StepProbe.agda:206`)
  applies it at the ∀-binder's member. The values disjunct's out-reader
  (`ValuesDisj-out`, `StepProbe.agda:146-183`) is also proved, via
  `valuesAt-out` (`Definable.lagda.md:578`).

Timings (warm dependencies, probe checked from scratch):

| run | wall | note |
|---|---:|---|
| `CutProbe.agda` | ~1.3 s | three consecutive runs 1.26, 1.26, 1.25 s |
| `StepProbe.agda` | ~1.5 to 3.5 s | 3.5 s on the first full check after edits, 1.5 s thereafter |

No wall approached the 180 s line, and no module-level conversion hazard was
met: the three clauses assemble directly from the delivered `interAt`,
`valuesAt`, `allTuplesAt` descriptions and the `appAt`/`prAtL` readers. The
one friction found was not a wall but a shape fact: the FOL term semantics
`⟦var zero⟧` does not reduce definitionally to the environment head at the
∀-binder, so unpacking `LayerAt`'s universal quantifier needs one small
atom-reading lemma (the Table chapter solves this class with named
continuations); the probe therefore states the layer-level out-reader with
the inter disjunct's satisfaction as its input, which is the mathematical
content the brief asked for.

## 5. The full re-priced alternative

Chapters deleted: `Codes` (277), `Table` (1,562), `Tower` (2,130) file lines,
roughly the 3,000 Agda-line certificate cluster, and the flat-order branch
(nothing delivered yet, so nothing to delete there).

Chapters kept: everything else of the delivered route, including `Terms`,
`Satisfaction`, `Tuples`, `Operations`, `Definable`, `InL` (the bridge
chapter stays: the closure's slices and the singleton-family are constructible
by its lemmas), and the M5a order (`Name`, `Tree`, `Base` additions) in place
of the flat order.

New chapters with sizes (estimated):

| new chapter | estimate |
|---|---:|
| the three meta lemmas (selections and family-extension on satisfaction sets) | 80 to 140 |
| the singleton-family slice/operation | 60 to 120 |
| the kinded-invariant induction | 150 to 250 |
| the terms-to-levels lemma | 80 to 150 |
| the internal closure chapter (level table, 10-clause step, recursion assembly) | 700 to 1,100 |
| the Def-equivalence against the internal description | 150 to 300 |
| total new | 1,220 to 2,060 |

Landing arithmetic: the delivered route projects to 15,000 to 15,700 lines
post-compression (`dev/PLAN.md:1123`, the ruled measurement of the M5-internal
side). Replacing the certificate cluster with the kinded closure tower and
keeping the skeleton order subtracts the cluster's content (about 3,000 Agda
lines) and adds the new chapters (about 1,220 to 2,060), for a net of roughly
13,200 to 14,500, i.e. about 1,000 to 2,000 lines under the delivered route.
Two consequences are honest and must be stated plainly: the fork does **not**
restore the 9.5 to 10.5k band or satisfy the 11k tripwire (the landing stays
above 13k), and its primary yield is unchanged from the memo's (the
satisfaction-internalization cluster retires, and the build stays in the
seconds-per-chapter class). The saving over the delivered route is real but
bounded, and it is bought by re-validating the whole tower on a new step
description.

Risks that remain after this probe:

1. The full 10-clause kinded step and its Sequence-class assembly are
   unmeasured; Unknown 3 validated three clauses and the inter out-reader.
   The delivered `Table`'s approximation machinery cost 1,562 lines with
   codes; the closure version has no codes but carries the arity table and
   the functionality conjunct, and the interaction of the arity-indexed
   recursion value with the `funct` contractibility (the P2 design fact, the
   domain must not be a stage) is the largest remaining performance question.
2. The three new meta lemmas and the singleton-family description are priced
   but unproved; the singleton-family is a genuinely new `At`-description and
   constructibility proof.
3. The kinded-invariant induction runs on the meta side against internal
   clauses that are conditional on numeral-ness (the Table chapter's
   conditional-clause pattern), and the conditional shapes may inflate the
   induction beyond the estimate.
4. The M5a skeleton re-cut is in progress in the working tree with unfinished
   lemmas; the order's internal side (M5b-d) remains unmeasured.

## 6. What this probe could not settle

- The internal closure chapter's measured line count and cold-check time (the
  three-clause layer is green; the remaining seven clauses and the recursion
  assembly are not written).
- Whether the kinded invariant's meta-induction stays cheap against the
  numeral-conditional internal clauses (the estimate of 150 to 250 lines could
  inflate).
- The exact net saving of the closure tower (estimated 1,000 to 2,000 lines
  against the delivered certificate cluster; only the meta half is measured).
- The escape case is settled meta-theoretically (automorphism argument) and
  enters the probe as one flagged postulate; a fully formal proof would need
  model-theoretic machinery not in the library.
- The skeleton order's internal-side cost (M5b-d) and the final landing
  measurement of the delivered route, both of which are branch work in
  progress, not probe questions.

The shape of the mathematics, on the record: the naive cut fails on junk
(case 4 escapes), the kinded level table makes the values-cut sound and
complete with the banked lemmas plus three small new ones, the flat order
cannot stay flat (Unknown 2 kills the fork as specified), and the kinded
closure step assembles from the delivered descriptions without new machinery
(Unknown 3 green). Partial salvage: build the closure tower on kinded level
tables, keep the M5a skeleton order, and take the ~1,000 to 2,000 line saving
against the delivered certificate cluster, accepting that the 10k target
stays out of reach.
