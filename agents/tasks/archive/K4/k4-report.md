# R5-K4: the definable power as a table's image, and the index that refutes the route

The kernel's closing batch. Reads done in the mandated order (`_build/k3-report.md` in full;
`L/Rud/CodePred` and `L/Rud/CodeSet` as committed; `L/Rud/DefInJ` and `L/Rud/BaseBlock`;
`L/Rud/SatSets` and `L/Rud/StepInL`'s `Reads`/`Desc`/`Values` surfaces; `L/Rud/Bridge`'s `Reduce`
telescope; `_build/r5d1-report.md`; the retiring `L/Coding` stack as pattern only; `dev/LESSONS.md`
with I-5 first, then R-35/R-36/R-37/R-38, I-2/I-3/I-4, P-c/P-i, R-16, C-11/C-12, D-7 to D-10). Two
files touched, both mine: `src/L/Rud/SatTable.lagda.md` (new) and this report. `Everything`
untouched, no commits, no sibling files touched.

**Headline, and it is a D-10 result rather than a build result.** The mandated D-10 check found
that the staged object does not serve its consumer: **`codeSet∈J`'s two-limit index is unavailable
at the limits `DefFragment` is actually called at, and is refuted there by the very theorem the
route is meant to prove.** So the coded satisfaction table was not built. What was built instead is
everything the finding leaves standing and the corrected target:
**246 code lines, 470 file lines, 1.9 s cold**, all four linters clean, `reuse lint` clean, three
type errors across the batch, no wall, no heap event.

The residue is one hypothesis and it is now index-free. `DefFragment` (a fragment quantified over
every limit) is proved **equivalent** to `GeneralPow` (a membership), whose base case is closed by
the base block and whose general case follows from a single uniform ω-block statement `BlockPow`
that quantifies over no level at all. Given either, the bridge's `Reduce` runs at its exact
telescope and `Matching` plus the three bridge theorems come out; the close-out probe confirms this
at the trunk's `A := ∅` in 1.5 s.

---

## 1. D-10 first: the table's form, the arity decision, the identity, and the index

### 1.1 The fragment identity (true, and now a theorem)

Write `C = Lset ζ`. The identity is the classical one and it is **`F8` of a relation over the code
set**, not a separation:

- `F10 R c = { v : pr c v ∈ R }` is the tenth basis operation, the **slice** of a relation at a
  code (`L/Rud/Images:295`).
- `F8 R K = { F10 R c : c ∈ K }` is the eighth, the **collection** of the slices
  (`L/Rud/Images:339`).

So if `R` is a coded satisfaction relation over `C` (its slice at `code φ` is `defSet φ`) and `K`
covers the codes, then

> `F8 R K ≡ 𝒟ₒ C`

on the nose, and since both operations are in the basis, **a limit level holding `R` and `K` holds
`𝒟ₒ C` with no offset at all**. This is `Pow.pow≡` / `Pow.pow∈J`, proved in the file at an abstract
code map `cod : Formula ⟪C⟫ 1 → S`, so no coding choice is baked in. Completeness of the table is
the `Covers` half (`𝒟ₒ C ⊆ F8 R K`) and soundness is the `Slices` half (`F8 R K ⊆ 𝒟ₒ C`), exactly
as the brief's part 3 asks; both come out of the same extensionality proof because the two
containments are the two directions of one equation.

**Checked true before building**, and the check paid: the shape is one rud step, not a separation
inside a bounding fragment, so the fragment is the **identity** fragment (`powFragment`), which is
what removes the `Sep`/`Sstage₂` apparatus from the general case entirely. The base block's own
witness had already been the identity fragment at `ω`; this says it is the identity fragment
everywhere.

### 1.2 The arity decision

**Sub-formula evaluation needs codes at every higher arity, unboundedly.** A quantifier's subformula
lives one arity up (`CodePred`'s `succK`/`bndK` are exactly this), and there is no bound on the
nesting, so one internal satisfaction table must be indexed by **keys** (arity paired with code) at
all arities at once, which is `CodePred`'s `keyOf` shape. Per-arity `codeSet∈J` does **not** suffice
for the table's own domain; `allCodes∈J` (K3's deferred 135-line item) is the minimum, and the
honest domain is the key set, one further object.

**But the fragment identity itself consumes arity 1 only.** `F8 R (codeSet C 1)` needs
`codeSet∈J 1` and nothing else. So the arity question separates cleanly: the *identity* is arity-1
and delivered; the *table* is all-arity and would have needed `allCodes∈J` built first. That
separation is why this batch could deliver the identity without the table.

### 1.3 The index, and the finding

`codeSet∈J` is delivered at K3's `At` telescope:

```agda
module At (γ : S) (limγ : ⟨ isLimit γ ⟩)
          (δ : S) (limδ : ⟨ isLimit δ ⟩) (δ∈γ : ⟨ δ ∈ˢ γ ⟩)
          (C : S) (C∈δ : ⟨ C ∈ˢ Sset δ ⟩) where
```

so it needs **a limit `δ ∈ γ` holding the carrier**. `DefFragment`'s premises are `γ` a limit,
`ζ ∈ γ`, `Lset ζ ∈ Sset γ`, and its consumer (`Bridge:749-756`, the successor case of `p2`) calls it
at an **arbitrary** limit. The two-limit index is not derivable from those premises, and worse:

**(a) A concrete instance with no such `δ`.** Take `γ = ω·2` and `ζ = ω+3`. Then `ζ ∈ γ`; the only
limit below `ω·2` is `ω`; and `Sset ω` is hereditarily finite (this batch's sibling `BaseBlock`
proves every `Sset (# n)` finite by its own S-side tally, so every member of `Sset ω` is finite),
while `Lset (ω+3) ⊇ Lset ω ⊇ HF` is infinite. So no limit `δ ∈ γ` holds `Lset ζ`. The premises of
this instance are satisfiable: **under the matching the batch is meant to prove**,
`Sset (ω·2) = Lset (ω·2) ∋ Lset (ω+3)`. So the index the route needs is refuted by the theorem the
route is meant to establish. That is the sharpest form of the finding and it is the D-10 lesson's
own shape (a target checked at the intended generality).

**(b) The obstruction is not about limits, it is about the coding, and it is stronger.** Let `δ₀` be
a stage with `C ∈ Sset δ₀` and let `γ = δ₀ +ω`, the first limit above it (this is the general shape
of (a)). Suppose some transitive `U ∈ Sset γ` held every code over `C`. Then `U ∈ Sset (δ + 1)` for
some `δ ∈ γ`, hence `δ ⊆ δ₀ + n` for a finite `n`, and `Sset (δ+1)` is transitive, so **every code
over `C` lies in `Sset (δ₀ + n + 1)`**, contradicting K2's recorded cofinality (a code's Kuratowski
pair depth grows with the formula, the depths are unbounded, so no finite offset above the carrier's
stage holds the family). So at `γ = δ₀ +ω` there is **no carrier at all** over which the
object-language predicate could be read, limit or not. The internal-codes route is structurally
absent there, not merely awkward.

**(c) And that `γ` is the only one that matters.** From `Lset ζ ∈ Sset γ` one gets `δ₀ ∈ γ` with
`Lset ζ ∈ Sset δ₀` (`DefInJ.Sstage`), and `δ₀ +ω ≤ γ` because `γ` is a limit. So the whole
∀-over-limits statement reduces to the single uniform statement at `δ₀ +ω` (this batch proves the
reduction: `+ω-fits`, `block→general`). The residue's entire content sits at zero slack, which is
exactly where the route has none.

**Recorded corrected target.** K2 recorded the cofinality as "a fact about the target". It is a fact
about the **coding**: `code φ = mkTag t (pr … …)` nests one Kuratowski pair per formula layer, so
rank grows with depth. A rank-bounded coding (a formula as a set of ⟨position, label⟩ pairs, labels
in `C ∪ ℕ`) has every code of rank `≤ rank C + 3`, hence a code set of bounded rank, hence a code
set inside the ω-block. Under such a coding "is a code" is a bounded-witness condition, so the
delivered comprehension direction (`L/Rud/Realize`: every Δ₀-definable subset of a transitive set is
a finite composite of the basis operations) would place the code set, the tables and the relation at
a **fixed finite offset**, which is what `BlockPow` needs. That is the repair, and it is a K2/K3
re-do, not a patch.

### 1.4 What this batch therefore built

Given (a)-(c), building the coded satisfaction table over `codeSet` would have been building on a
false premise (D-10, and the R-36 stop shape). The batch built the parts that are true and
coding-independent, and the corrected target:

1. the fragment identity at an abstract code map (survives the coding repair verbatim);
2. its instance at the delivered coding, with `codeSet∈J` plugged in, so the two-limit telescope is
   visible **in the code** (`module TwoLimit`) rather than only in prose;
3. the identity fragment and the base/general split as `DefInJ`'s `Discharge` wants it;
4. the equivalence of the residue with the target (no weakening);
5. the ω-block reduction, which removes the level quantifier from the residue;
6. the close-out: `Reduce` at all four hypotheses, `Matching`, and the three bridge theorems, over
   the one remaining hypothesis.

---

## 2. What is proved (`src/L/Rud/SatTable.lagda.md`)

| export | statement |
|---|---|
| `Pow.Covers` / `Pow.Slices` | the two halves an abstract code map owes: `K` holds every code and nothing else; `R`'s slice at a code is that formula's `defSet` |
| `Pow.pow≡` | `F8 R K ≡ 𝒟ₒ C` under those two, at any code map |
| `Pow.pow∈J` | hence `𝒟ₒ C ∈ˢ Sset γ` from `K , R ∈ˢ Sset γ` at a limit `γ`, **no offset** |
| `Coded.codeCovers` | the covering half at the delivered coding, free from `code∈codeSet` / `codeSet-out` |
| `Coded.SatRelation` / `Coded.coded-pow` | the one missing object, named and typed, and the definable power from it |
| `TwoLimit.codeSet∈J` / `two-limit-pow` | K3's `At` plugged in: at the two-limit index the relation is the **only** hypothesis left |
| `limit-ω-case` | a limit is `ω` or lies above it |
| `∅∈limit` | every limit holds the empty set (this places the trunk's relativization slot) |
| `powFragment` | the definable power is its own bounding fragment (both halves the identity) |
| `GeneralPow` | the residue as a **membership**: `𝒟ₒ (Lset ζ) ∈ˢ Sset γ` for `ω ∈ γ` |
| `defPow`, `fragment` | the base/general split: `γ ≡ ω` goes to `BaseBlock.baseDefPow`, `ω ∈ γ` to `GeneralPow`; hence `DefFragment` |
| `pow-from-fragment` | the converse: `DefFragment → GeneralPow`, so the residue is **equivalent**, not weaker |
| `BlockPow` | the uniform ω-block statement: `Lset ζ ∈ˢ Sset δ → 𝒟ₒ (Lset ζ) ∈ˢ Sset (+ω δ)`; no level quantifier |
| `+ω-fits` | `δ ∈ γ` at a limit `γ` gives `+ω δ ∈ γ` or `+ω δ ≡ γ` |
| `block→general` | `BlockPow → GeneralPow` |
| `slot-empty` | the trunk's `slot∈L` at `A ≡ ∅` |
| `Landing` | over `GeneralPow` and `slot∈L`: `defStage∈J` from `Discharge`, `Reduce` at all four hypotheses, `matching`, `bridge-isL→isJ`, `bridge-isJ→isL`, `bridge-level` |

**The split, recorded as implemented.** `DefInJ.Discharge` consumes `DefFragment` at an arbitrary
limit. This batch splits *inside* the fragment, on `limit-ω-case`:

- `γ ≡ ω`: `BaseBlock.baseDefPow` gives `𝒟ₒ (Lset ζ) ∈ˢ Sset ω`, transported. Closed.
- `ω ∈ γ`: `GeneralPow`. Open, and this is the residue.

The split is by **the level**, not by the carrier, and it is exhaustive because a limit is `ω` or
above it. The brief's suggestion that the general case "may assume a limit below γ" is exactly what
§1.3 refutes: that assumption is not available at `ω ∈ γ` in general, so the general branch is
stated without it.

---

## 3. Price table

| part | code lines |
|---|---|
| header and imports | 47 |
| `ext-⊆`, `module Pow` (`Cod`, `Covers`, `Slices`, `pow≡`, `pow∈J`) | 50 |
| `module Coded` (code map, covering, `SatRelation`, `coded-pow`) | 18 |
| `module TwoLimit` (K3's `At` plugged in) | 14 |
| `limit-ω-case`, `∅∈limit` | 20 |
| `GeneralPow`, `powFragment`, `defPow`, `fragment`, `pow-from-fragment` | 30 |
| `BlockPow`, `+ω-fits`, `block→general` | 44 |
| `slot-empty`, `module Landing` (the close-out) | 23 |
| **total** | **246** |

Stop-line was 1,600 with a pause gate at 900 for the table's existence half. Neither was approached,
because the D-10 check removed the table from the batch before any Agda was spent on it.

**What the table would have cost, priced for the record.** The design was carried far enough to
price it before it was dropped (all figures at K3's measured rates, inner-world, I-5 throughout):

| part | estimate |
|---|---|
| `allCodes∈J` (K3's deferred numeral predicate) | 135 |
| the key set at all arities (a second `Description`) | 150-200 |
| environments as position-indexed sets: `isEnv`, lookup, the shift for quantifiers, both directions | 250-350 |
| the twelve table clauses with their meta-level shapes and both translations | 450-650 |
| the table predicate, `Φ`, both directions | 150 |
| soundness: the iff by induction on the external formula, twelve cases | 300-400 |
| existence: the table for a formula's key closure as a member of the level (the piece that needs the `T`-sets tagged and unioned, and the piece K3's report warns is always the larger half) | 400-600 |
| the relation, its `Description`, the discharge | 120 |
| **total** | **≈1,950-2,600** |

Against the retiring five chapters' 3,040 file lines the inner-world discipline would have bought
roughly the fraction the brief expected. It is not a fraction of a batch, and it would not have
discharged `DefFragment`.

---

## 4. The discharge and the instantiation, with the probe

`DefFragment` is **not** discharged; it is proved equivalent to `GeneralPow` and reduced to
`BlockPow`. Everything downstream of the fragment is discharged and lives in `module Landing`:

```agda
module Landing (gp : GeneralPow)
               (slot∈L : (γ : S) → ⟨ isLimit γ ⟩ → ⟨ A ∈ˢ Lset γ ⟩) where
  open Discharge (fragment gp) using ( defStage∈J )
  module R = Reduce defStage∈J stepSet∈L values∈L slot∈L
  matching       : Matching
  bridge-isL→isJ : (x : S) → ⟨ isL x ⟩ → ⟨ isJ x ⟩
  bridge-isJ→isL : (x : S) → ⟨ isJ x ⟩ → ⟨ isL x ⟩
  bridge-level   : (x : S) → ⟨ isL x ⟩
                 → ∥ Σ[ γ ∈ S ] (Σ[ lim ∈ ⟨ isLimit γ ⟩ ] ⟨ x ∈ˢ Jset γ lim ⟩) ∥₁
```

`values∈L` and `stepSet∈L` are `StepInL`'s, unchanged. `slot∈L` is a module parameter because this
file keeps `A` abstract like every sibling; the trunk instance is `slot-empty refl`, proved from
`Bridge.∅∈Lset` and this file's `∅∈limit`. Applying `Reduce` **inside the file** is already the
r5d1 probe's content, so the telescope match is checked by the chapter itself.

**The r5d1-shape close-out probe, run as the final verification** (scratchpad, three explicit `-i`
roots, off the existing interfaces):

```agda
module ProbeSatTable {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
open import L.Rud.SatTable {ℓ} lem ∅ using
  ( GeneralPow; BlockPow; block→general; slot-empty; module Landing )
module FromBlock (bp : BlockPow) where
  module L = Landing (block→general bp) (slot-empty refl)
  matched : Matching                        ; matched = L.matching
  toJ : (x : S) → ⟨ isL x ⟩ → ⟨ isJ x ⟩     ; toJ = L.bridge-isL→isJ
  toL : (x : S) → ⟨ isJ x ⟩ → ⟨ isL x ⟩     ; toL = L.bridge-isJ→isL
```

**Green, 1.5 s.** It exercises three things the in-file module cannot: the trunk instantiation at
`A := ∅` (so `slot-empty refl` is accepted where the slot is actually empty), the chain
`BlockPow → GeneralPow → DefFragment → defStage∈J → Reduce → Matching` end to end, and the exports'
usability from outside. So the campaign's plumbing is verified to the last hypothesis.

**Exports, stated honestly.** `matching`, `bridge-isL→isJ`, `bridge-isJ→isL` and `bridge-level` are
delivered **conditionally**, over one hypothesis (`GeneralPow`, or `BlockPow` through
`block→general`) plus the trunk's slot. They are not unconditional, and §1.3 is why.

---

## 5. Timings

All runs `GHCRTS="-A64m -I0 -M12g"`, one check at a time, only on this file.

| # | content | result |
|---|---|---|
| 1 | header, imports, `Pow`, `Coded` | **2.7 s green, first attempt** |
| 2 | + the limit facts, the split, the block reduction, `Landing` | `NotInScope: Sset-mem`, 1.5 s |
| 3 | import added | `UnequalSorts` at `∈sucV-elim` (its motive is pinned at `ℓ-suc ℓ`; `Empty.⊥` is `Type₀`), 1.6 s |
| 4 | the three helpers restated at `Empty.⊥* {ℓ-suc ℓ}` | 2.9 s green |
| 5 | one unused import pruned (`Fof`); cold recheck | 1.8 s |
| 6 | + `module TwoLimit` (K3's `At`) | 2.9 s green |
| 7 | + `pow-from-fragment` (the equivalence test) | 1.9 s green |
| 8 | final cold recheck (interface deleted) | **1.9 s** |
| 9 | the close-out probe, scratchpad, trunk `A := ∅` | **1.5 s** |

Three type errors across the batch, each fixed in one edit; **no wall, no heap event, no rerun**.
The three-failure stop was never approached. `lint-agda --check`, `lint-prose --check`,
`weave-i18n --check`, `check-glossary` and `reuse lint`: all clean. `Everything` untouched, so
`make check` does not reach this file yet; adding it is the owner's call.

---

## 6. Residue, exactly stated

One hypothesis, in three interchangeable forms, in decreasing index content:

1. **`DefFragment`** (`DefInJ`, unchanged): the fragment at every limit.
2. **`GeneralPow`**: `𝒟ₒ (Lset ζ) ∈ˢ Sset γ` for every limit `γ` above `ω` holding `Lset ζ`.
   Equivalent to 1 (`fragment`, `pow-from-fragment`), with the `γ ≡ ω` case already closed.
3. **`BlockPow`**: `Lset ζ ∈ˢ Sset δ → 𝒟ₒ (Lset ζ) ∈ˢ Sset (+ω δ)`. Implies 2
   (`block→general`); no level quantifier at all; its `δ ∈ ω` instance is `BaseBlock`'s.

Form 3 is the classical statement (`Def(U) ∈ rud(U ∪ {U})`, Jensen), and the recommendation is to
carry the campaign's residue in that form from here: it is index-free, it is uniform in the carrier,
and it makes the base block a special case rather than a separate theorem.

**Two routes to form 3, priced:**

- **Repair the coding, then the table.** A rank-bounded coding (formula as a set of
  ⟨position, label⟩ pairs) makes the code set, the keys, the environments and the tables all of rank
  `≤ rank C + k` for a fixed `k`. Then the delivered comprehension direction (`L/Rud/Realize`) places
  each of them at a fixed finite offset, and the table's existence half stops being an ω-tower of rud
  depths. Cost: a K2/K3 re-do (the code function, `code∈J`, the twelve clauses' payload shapes) plus
  the table at §3's estimate; call it 2,800-3,600 lines and three or four batches. The `Pow` half of
  this chapter is written to survive it unchanged.
- **Jensen's lemma directly.** Prove `Def(U) ∈ rud(U ∪ {U})` by the rud recursion, which is the
  retiring `L/Coding/Model`-class development on the rud side. Not priced here; the delivered
  `Realize` is one half of its comprehension direction and `LevelDesc.closure→definable` is the other,
  so the campaign is closer to this than the line count suggests.

Both are architecture decisions and neither is a batch. They are the owner's call, which is why this
report stops at the corrected target rather than picking one.

---

## 7. Lesson candidates (IDs to be assigned by the owner)

1. **D-10, sharpened: a residue's INDEX can be refuted by the theorem the residue serves.** The
   recorded D-10 test is "check the target's truth at the intended generality". This batch found the
   next case: the target was true, the *index the delivered supplier is stated at* was not
   available, and the refuting instance (`γ = ω·2`, `ζ = ω+3`) is only satisfiable **under the
   conclusion of the very induction the residue feeds**. So the check that catches it is not "is the
   target true" but "**assume the theorem; is the supplier's telescope inhabited at the consumer's
   call sites?**". Five minutes of ordinal arithmetic against the consumer's call, and it removed a
   2,000-line build. Sibling of r5d1's "price the residue's WITNESS, not only its statement", one
   level up: price the supplier's INDEX against the consumer's quantifier.
2. **A cofinality recorded as "a fact about the target" may be a fact about the encoding.** K2
   recorded that the codes over a carrier are cofinal above its stage and called it a fact about the
   target, which licensed the two-limit index. It is a fact about the nested-pair coding: one
   Kuratowski pair per formula layer makes rank grow with depth. A flat coding has all codes of
   bounded rank and no cofinality at all. The general rule for this development: **when a "fact about
   the target" is a statement about ranks, check whether the ranks come from the mathematics or from
   the representation before letting it set an index.**
3. **The identity fragment is the native shape, twice.** `BaseBlock` discovered that the bounding
   fragment at `ω` is the definable power itself; this chapter shows that is not special to `ω`
   (`powFragment`), and that the fragment formulation is therefore an indirection: the residue is a
   membership. Both halves of the fragment collapse to `λ y k → k`. Worth recording as: **before
   building the machinery a two-sided approximation needs, check whether the approximation's own
   target is the witness.** It removed `Sep`/`Sstage₂` from the general case.
4. **The equivalence test, applied as standing practice.** r5d1 proposed it; this batch ran it on its
   own residue (`fragment` / `pow-from-fragment`, 4 lines) and it is what licenses trading
   `DefFragment` for `GeneralPow` without a footnote. Cheap enough to be mandatory for any batch that
   restates a residue.
5. **`∈sucV-elim`'s motive is pinned at `ℓ-suc ℓ`, so `Empty.⊥` cannot be the target of an ordinal
   contradiction.** Small but recurring: an ordinal-arithmetic no-go argument eliminated through a
   V-side eliminator must land in `Empty.⊥* {ℓ-suc ℓ}` with `Empty.isProp⊥* {ℓ-suc ℓ}`, and the two
   `Empty.rec` wrappers at the leaves are the whole cost. One of this batch's three errors, and it
   will fire again in any ordinal induction that reaches for a V-side eliminator.
6. **A close-out module beats a close-out probe, and then the probe still earns its keep.** Applying
   the consuming module (`Bridge.Reduce`) inside the exporting chapter makes the telescope match a
   typechecking obligation of the chapter rather than of a scratchpad. The scratchpad probe is still
   worth running afterwards, because it is the only place the module parameters get **concrete**
   (here `A := ∅`, which is what exercises `slot-empty refl`). Recommend both, in that order.
7. **P-i [A] datum, and a cheap-chapter datum.** Every heavy object in this chapter (`𝒟ₒ C`,
   `codeSet`, `Sset γ`, `F8 R K`) sits at a variable or a stuck term, every membership arrives as a
   variable hypothesis, and the only equations proved are between such terms. 246 lines over an
   import graph of ten chapters (including the 2,435-line `StepInL` and the 1,781-line `CodePred`)
   check cold in 1.9 s. The measured lesson is the negative one: **none of the conversion machinery
   fires when the chapter's own content is set-level identities at abstract carriers**, which is a
   reason to prefer that shape when a chapter has a choice.
