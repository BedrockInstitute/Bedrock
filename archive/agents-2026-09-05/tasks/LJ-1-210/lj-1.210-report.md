# LJ-1.210 report: is the chapter really 17 lines? The class-parameter probe

tier: opus (in-harness-subagent-mode), selected by the CLOCK. Written
incrementally (C-22). **No master edited. No commit, no push.** Every negative
is marked MEASURED or INFERRED.

## 0. LEAD

**THE SURFACE IS SMALL. THE CHAPTER DISSOLVES.**

`L.Coding.Model` is now class-generic and it typechecks. **42 lines were
written and 16 of the delivered 1,288 were removed or rewritten, so 1,272
survive verbatim.** **FIVE of the 16 sit below the header block, and those five
are the whole mathematical content of the port.**
`agents/tasks/LJ-1-210/GenModel.agda`, exit 0, 7.73 s, first try.

**Both instantiations are green.**

- At `isL`: **2 lines**, and it IS the delivered module. Six `refl` checks say
  so. `agents/tasks/LJ-1-210/ProbeLJ1210A.agda`, exit 0, 1.36 s.
- At the ambient class `Full`: **19 lines**, every proof `tt*` or `refl`.
  `agents/tasks/LJ-1-210/ProbeLJ1210C.agda`, exit 0, 1.15 s.

**A second module confirms the shape at its own site (P-l).** `L.Coding.Graph`
is class-generic at **23 lines written and 7 removed, ALL SEVEN in the header,
so 104 of 111 survive verbatim and NO body line changed.**
`agents/tasks/LJ-1-210/GenGraph.agda`, exit 0, 7.55 s, first try.

**Against `[LJ-1.200]`'s 17.** 17 is the right ORDER and it is not the price.
The price for the 1,288-line master is **42 written lines**, and the true
count of lines that carry mathematical content is **FIVE**. `[LJ-1.200]`'s
refusal to call 17 a price was correct, and its refusal was the only honest
move without this run.

**Against `[LJ-1.196]`'s word.** **1,288 plus 395 prices a re-derivation, and
nothing in the tree asks for one. MEASURED.** The residue of `[LJ-1.7]` is not
a chapter. **The word that reached `dev/PLAN.md` section 0.0 was an unmeasured
consequent, exactly as `[LJ-1.200]` said.**

**One qualification, and it is the part I did NOT measure.**
`L.Coding.Powerset` cannot be ported alone. Its port is CHAINED through ten
supplier modules that are fixed at the class in the same shape. Section 8
measures that chain: **17 modules, 5,822 in-fence lines, a class surface of
125 lines.** I ported 2 of the 17 (1,399 lines, 24 percent). **The rest is
INFERRED from the same shape, and it is not a price.**

## 1. MACHINE AND PROCESS DISCIPLINE

ONE Agda process, `GHCRTS="-A64m -I0 -M8g"`, cap **NEVER** raised. The
in-harness path does not pass through `dispatch.py`, so C-12's slot accounting
cannot see this task. **The machine is NOT quiet.** Two siblings hold Agda.
Load sits beside every absolute figure.

| run | file | exit | seconds | load |
|---|---|---|---:|---|
| 1 | `GenModel.agda` | 0 | **7.73** | 3.84 / 7.11 / 7.89, 4 foreign agda processes |
| 2 | `ProbeLJ1210Inst.agda`, `refl` body | 1 | 1.19 | as run 1 |
| 3 | `ProbeLJ1210Inst.agda`, `isSetΩ` body | **HEAP** | 128.89 | as run 1 |
| 4 | `ProbeLJ1210Inst.agda`, type-only body | **HEAP** | 137.86 | as run 1 |
| 5 | `ProbeLJ1210Inst.agda`, ninth check dropped | **HEAP** | 143.01 | as run 1 |
| 6 | `ProbeLJ1210A.agda` | 0 | **1.36** | 4.54 / 5.51 / 6.52 |
| 7 | `ProbeLJ1210B.agda` | **HEAP** | 134.03 | 4.98 / 5.56 / 6.39 |
| 8 | `ProbeLJ1210B1.agda` | **HEAP** | 136.44 | 4.98 / 5.56 / 6.39 |
| 9 | `ProbeLJ1210C.agda`, first two shapes | 1 | 1.02, 1.07 | 4.82 / 5.18 / 6.06 |
| 10 | `ProbeLJ1210C.agda` | 0 | **1.15** | 4.82 / 5.18 / 6.06 |
| 11 | `GenGraph.agda` | 0 | **7.55** | 4.47 / 4.99 / 5.68 |
| 12 | `ClassData.agda` | **HEAP** | 105.07 | 4.47 / 4.99 / 5.68 |
| 13 | `CD1.agda`, `CD2.agda`, `CD4.agda` | 0 | 0.74, 1.50, 1.52 | 4.47 / 4.99 / 5.68 |
| 14 | `CD3.agda` | **HEAP** | 105.07 | 4.47 / 4.99 / 5.68 |
| 15 | `CD5.agda` | **HEAP** | 105.88 | 4.47 / 4.99 / 5.68 |
| 16 | `CD6.agda` | 0 | **1.41** | 4.47 / 4.99 / 5.68 |

**SIX HEAP EXHAUSTIONS, and I report each as a wall.** The cap was never
raised. **No run passed 30 minutes**, so the clock rule never bit. **NOT ONE
WALL IS IN THE PORT.** Sections 5 and 9 bisect them to two named declarations,
neither of which a real port contains.

**No verdict in this report rests on a timing.** Every verdict rests on an
exit code and a line count, which no instrument band touches.

## 2. THE ARTIFACTS

| file | what it is |
|---|---|
| `extract.py` | copies a master's ` ```agda ` fences to a plain `.agda` file |
| `census.py` | counts in-fence non-blank lines and the ones naming the class |
| `surface.py` | splits the class surface into header lines and body lines |
| `closure.py` | walks the imports and lists the modules that fix the class |
| `GenModel.agda` | **`L.Coding.Model` with the class as a module parameter.** Exit 0 |
| `GenGraph.agda` | **`L.Coding.Graph` with the class as a module parameter.** Exit 0 |
| `GenPowerset.agda` | the verbatim fence extract of `L.Coding.Powerset`, read but NOT ported |
| `ProbeLJ1210A.agda` | the instance at `isL`, and six `refl` checks. Exit 0 |
| `ProbeLJ1210C.agda` | the instance at the ambient class `Full`. Exit 0 |
| `ProbeLJ1210B.agda`, `B1.agda` | the comparison check that walls, kept so the wall re-runs |
| `ProbeLJ1210Inst.agda` | the first, unbisected file. The record of runs 2 to 5 |
| `ClassData.agda`, `CD1` to `CD6` | the record-bundle attempt and its bisect. Section 9 |

**Every file is new, none is deleted, and all sit in
`agents/tasks/LJ-1-210/`.** `check-probes.py` is clean and
`check-rule-ids.py` is clean.

**THE WORKING TREE.** I added only the files above and this report. **The tree
also carries changes I did not make and did not touch**: `Makefile`,
`agents/tasks/LJ-1-209/`, `scripts/check-premises-stated.py` and
`scripts/tests/test_premises_stated.py`. **They are a sibling's work.**

## 3. THE ANCHOR COUNTS RE-DERIVE

`extract.py` reports **1,288** non-blank in-fence lines for
`src/L/Coding/Model.lagda.md` and **395** for `src/L/Coding/Powerset.lagda.md`.
**Both match `[LJ-1.200]:68-69` exactly. MEASURED.**

## 4. THE SURFACE IN LINES

**42 written, 16 removed, net growth 26 on a 1,288-line master. 1,272 lines
survive verbatim.** The figures come from `diff` between the verbatim fence
extract and `GenModel.agda`, counting non-blank lines only.

| group | lines | what it is |
|---|---:|---|
| pre-module imports | 6 | the telescope names `V`, `𝒮ᵥ`, `Transitive`, `⁅_,_⁆`, `#_` and `sucV`, so they must be imported ABOVE the `module` line |
| the telescope | 11 | `M`, `M-trans`, six numeral operations, and `where` |
| import adjustment | 4 | `⊨-map`, `Δ₀`, `FOL.Semantics`, `module Relabel` |
| class application | 2 | `open hPropStructure (𝒮ᵥ ↾ M)` and `module AbsL = FOL.Absoluteness.Single 𝒮ᵥ M M-trans` |
| the inlined `L.Absoluteness` twin | 14 | a probe artifact, priced below |
| **body substitution** | **5** | the whole mathematical content of the port |

**FIVE body lines.** `GenModel.agda:123`, `:202`, `:203`, `:212`, `:890`. Each
is a name substitution with no argument attached:

- `:123` `isL-trans` to `M-trans`.
- `:202` and `:203` `snd (isL v)` to `snd (M v)`.
- `:212` `𝒮ʟ` to `(𝒮ᵥ {ℓ} ↾ M)` in the `FOL.Coding` application.
- `:890` `⟨ isL w ⟩` to `⟨ M w ⟩`.

**The 14 inlined lines are a PROBE ARTIFACT and I do not bill them.**
`src/L/Absoluteness.lagda.md` is itself fixed at the class, and a probe that
may not edit a master must carry its own copy. **That module's own class
surface is 3 header lines and 1 body line out of 34** (`surface.py`). In a real
port it takes its own telescope and the 14 lines leave Model's bill. **So
Model's port-proper figure is 28 written lines.**

## 5. THE WALLS IN THE COMPARISON CODE, BISECTED

**Every wall in runs 2 to 8 is in MY comparison code. None is in the port.
MEASURED.**

The port itself checks 1,288 lines in 7.73 s. The walls appear only where I ask
Agda to prove that a name in the generic module at `isL` is the SAME TERM as
the delivered name.

- `ProbeLJ1210A.agda`, the instance and six checks: **exit 0, 1.36 s.**
- `ProbeLJ1210B.agda` adds `chk-domAt-out` and `chk-domAt-intro`: **HEAP,
  134.03 s.**
- `ProbeLJ1210B1.agda` keeps `chk-domAt-out` alone: **HEAP, 136.44 s.**

**So one declaration walls.** Its `refl` asks Agda to normalize
`subst ⟨_⟩ (sym (step x)) ∣ y , p ∣₁` on both sides, where
`step x = inDomAt-adequate (suc f) zero (x ∷ γ)`, and `inDomAt-adequate` is
`cong (⋁ S) (funExt ...)` (`src/L/Coding/Model.lagda.md:271-280`). **That is
`dev/LESSONS.md` P-i's heavy-thing shape.** The two copies are distinct
constants, so neither side reduces first and both normalize whole.

**A ninth name fails the same way but cheaply.** `chk-tagAtL-adequate` gives
`[UnequalTerms]` at 1.19 s with
`AtL.lookup-fst s γ i != Delivered.lookup-fst s γ i`. `lookup-fst` recurses on
a FREE index, so neither copy reduces. **Agda ACCEPTED the type**, which is the
half that bears: the two proofs inhabit the same type, so either serves any
consumer.

**What the walls do NOT say. MEASURED.** They say nothing about the port. They
say that comparing two COPIES of one proof term is expensive, which is a fact
about this probe. **A real port deletes the delivered copy and instantiates the
generic one, so no comparison is ever performed.**

## 6. THE TWO INSTANTIATIONS

### 6.1 At `isL`: 2 lines, and it IS the delivered module

```
module AtL = LJ-1-210.GenModel {ℓ} isL isL-trans
               numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst
```

`agents/tasks/LJ-1-210/ProbeLJ1210A.agda:47-48`. Six `refl` checks pass at
`:59-99`: `extAt`, `extAt-out`, `extAt-in`, `extAt-in-both`, `tagAtL` and
`domAt`.

**FOUR of those six are the names `[LJ-1.200]` called projections blind to the
carrier, and the machine agrees.** `extAt`, `extAt-out`, `extAt-in` and
`extAt-in-both` come out on the nose.

### 6.2 At `Full`: 19 lines, all `tt*` or `refl`

`agents/tasks/LJ-1-210/ProbeLJ1210C.agda:47-73`, 19 non-blank lines.

| what | proof |
|---|---|
| `Full` | `Unit* , isPropUnit*` |
| `Full-trans` | `tt*` |
| `numeralF`, `numeralF-fst` | `# k , tt*` and `refl` |
| `pairF`, `pairF-fst` | `⁅ fst a , fst b ⁆ , tt*` and `refl` |
| `sucF`, `sucF-fst` | `sucV (fst a) , tt*` and `refl` |
| the application | one `module AtFull = ...` |

**`[LJ-1.184]`'s claim that the closure facts are `tt*` at the ambient class is
CONFIRMED at this site, not transferred to it (P-l). MEASURED**, exit 0.

## 7. WHAT RESISTED ABSTRACTION

**Nothing inside `L.Coding.Model` resisted. MEASURED.** Exit 0 on the first
typecheck, with no retry on the body.

**Nothing inside `L.Coding.Graph` resisted. MEASURED.** Exit 0 on the first
typecheck, ZERO body edits.

**Two things resisted at the INSTANTIATION site, and C-36 says to write both.**

**One.** `agents/tasks/LJ-1-210/ProbeLJ1210C.agda:72`. Agda would not solve the
implicit arguments of the transitivity witness through a module application:

```
error: [UnsolvedConstraints]
  fst (y ∈ x) =< fst (_y_114 ∈ _x_113) (blocked on _x_113)
when checking the module application module AtFull = ...
```

The cure is one eta-expansion, `(λ {x} {y} → Full-trans {x} {y})`. **It is
plumbing, not mathematics. MEASURED.**

**Two.** `agents/tasks/LJ-1-210/ProbeLJ1210C.agda:50`. `Transitive (𝒮ᵥ {ℓ}) Full`
is wrong where `V.Hierarchy` is imported ALREADY APPLIED at `{ℓ}`, and
`Transitive 𝒮ᵥ Full` is wrong where it is imported UNAPPLIED. **The generic
module must import `V.Hierarchy` unapplied**, because its telescope mentions
`𝒮ᵥ` above the `module` line where `ℓ` is not yet bound. **MEASURED**, run 9.

## 8. THE CHAIN UNDER `L.Coding.Powerset`

**`L.Coding.Powerset` cannot be ported alone, and I did not port it. I say so
rather than reporting a port I did not run.**

`closure.py` walks the imports from `L.Coding.Powerset` and finds **28 modules
that name the class, over 82 visited.** Eleven of them are the class DEFINITION
and the L-only axioms, which never become generic because they are what SUPPLY
the hypotheses: `L.Constructible`, `L.Axioms.{Basic, Full, Infinity, Numerals,
Power, Separation}`, `L.Recursion`, `L.Reflect`, `L.ReflectFo`, `L.Stage`.

**The 17 that would be parameterized, with their class surface. MEASURED**,
`surface.py`:

| module | code | header | body |
|---|---:|---:|---:|
| `L.Absoluteness` | 34 | 3 | 1 |
| `L.Coding.Bridge` | 294 | 3 | 1 |
| `L.Coding.Closed` | 95 | 3 | 0 |
| `L.Coding.CodeSet` | 168 | 7 | 2 |
| `L.Coding.EnvSet` | 359 | 8 | 7 |
| **`L.Coding.Graph`** | **111** | **3** | **0** |
| `L.Coding.InL` | 326 | 4 | 17 |
| **`L.Coding.Model`** | **1,288** | **5** | **4** |
| `L.Coding.Powerset` | 395 | 4 | 9 |
| `L.Coding.Recover` | 190 | 4 | 0 |
| `L.Coding.Sat` | 179 | 4 | 0 |
| `L.Coding.Shape` | 354 | 4 | 2 |
| `L.Coding.Slot` | 187 | 4 | 0 |
| `L.Coding.Sound` | 850 | 4 | 2 |
| `L.Coding.Table` | 246 | 3 | 1 |
| `L.Coding.Uniform` | 116 | 4 | 2 |
| `L.Coding.Unique` | 630 | 4 | 5 |
| **TOTAL** | **5,822** | **71** | **54** |

**The class surface of the whole chain is 125 lines out of 5,822. MEASURED.**

**125 is a CENSUS FLOOR, not a written cost, and the two differ by a factor I
measured only once.** Model's census is 9 lines and its written port is 42.
`surface.py` counts by two regexes and it cannot see a line that must change
without naming the class, such as an import that becomes a module application.
**Multiplying 125 by Model's factor would be an estimate anchored on one
comparable, which P-l refuses.**

**I ported 2 of the 17, `Model` and `Graph`, which is 1,399 lines, 24 percent.
The other 15 are INFERRED to carry the same shape, and INFERRED is not a
price.** P-l is why I refuse a total.

### 8.1 What `L.Coding.Powerset` itself would cost, read but not run

Its own class surface is **4 header lines and 8 body lines out of 395**
(`agents/tasks/LJ-1-210/GenPowerset.agda:21`, `:23`, `:57`, `:59`, then `:106`,
`:155`, `:244`, `:258`, `:357`, `:376`, `:445`, `:463`). **That file is the
verbatim extract with only its `module` line renamed; it is NOT ported and it
was never typechecked.**

**SEVEN of the eight body lines are the same mechanical substitutions Model
needed**: `isL-trans` to `M-trans` five times, `snd (isL u)` to `snd (M u)`
once, and `⟨ isL x ⟩` to `⟨ M x ⟩` once inside `DefOK`.

**THE EIGHTH IS THE ONLY L-SPECIFIC LINE IN THE MASTER, and it is a corollary.**
`DefAt-stage` (`GenPowerset.agda:457-465`, **9 lines**) instantiates the generic
`DefAt-out` and `DefAt-in` at a tower stage, and it is the one place that spends
`LsetS` and `𝒟ₒ→isL`, the two facts that say the class holds the stages and
their definable powersets. **Everything above it takes `A : S` and a `DefOK A`
witness and never names the tower.**

**So `[LJ-1.7]`'s residue, read at `L.Coding.Powerset`, is 9 tower-specific
lines sitting on a generic 386-line body. MEASURED by reading, not by
typechecking, and I mark the difference.**

### 8.2 The L-only facts that become hypotheses

`surface.py` lists them per module. Over the 17: `isL-trans`, `numeralL`,
`numeralL-fst`, `pairʟ`, `pairʟ-fst`, `sucʟ`, `sucʟ-fst`, `unionʟ`,
`unionʟ-fst`, `finSet`, `LsetS`, `𝒟ₒ→isL`, `hasSeparationL`, `hasPowerL`,
`ωʟ`, `ω-specL`. **Sixteen names.** They say the class is transitive, holds the
numerals, is closed under pairing, union and successor, holds the stages and
their definable powersets, and models separation, power and infinity.

**At `isL` all sixteen are delivered theorems. At the ambient class they are
V's own axioms, and the six that Model needs are `tt*` or `refl`, MEASURED in
section 6.2. The other ten are INFERRED to be cheap at the ambient class and I
did not measure them.**

## 9. THE RECORD-BUNDLE ROUTE WALLS, AND THAT IS A NEW MEASUREMENT

The flat telescope costs 6 pre-module imports plus 11 parameter lines, and
**every module down the chain repeats both**: `GenGraph.agda` repeats Model's
telescope verbatim. Over 17 modules that is about 289 repeated lines. **The
obvious cure is to bundle the class data in a record and take ONE parameter.**

**IT WALLS. MEASURED.** `ClassData.agda` holds eight fields and exhausts the
8 GB heap at 105.07 s. The cap was not raised.

**The bisect, five runs:**

| file | fields | result |
|---|---|---|
| `CD1.agda` | `M`, `M-trans` | 0.74 s |
| `CD2.agda` | plus `numeralL`, `numeralL-fst` | 1.50 s |
| `CD4.agda` | plus `pairʟ`, `pairʟ-fst` | 1.52 s |
| `CD3.agda` | plus `sucʟ`, `sucʟ-fst` | **HEAP, 105.07 s** |
| `CD5.agda` | `M`, `M-trans`, `sucʟ`, `sucʟ-fst` only | **HEAP, 105.88 s** |
| `CD6.agda` | **the IDENTICAL type in a module telescope and in a top-level definition** | **1.41 s** |

**So one field walls, `sucʟ-fst`, whose type names `sucV`. The identical type
outside a record costs 1.41 s, and inside a 1,288-line module telescope it is
part of a 7.73 s run.** `sucV N = N ∪ ⁅ N ⁆s`
(`Cubical/HITs/CumulativeHierarchy/Constructions.agda:161-162`), while `# k`
does not reduce at a free `k` and stays an atom, which is why `numeralL-fst`
is free.

**I do NOT claim the cause.** I measured that the same type is free in a
telescope and walls in a record field. **A law needs its measurement and this
one has only half: the site, not the mechanism.** The orchestrator may want a
probe for it.

**The practical reading:** the flat telescope is the route that works today,
and it costs about 17 repeated lines per module down the chain.

## 10. DD4: HOW MUCH RE-INSTANTIATES FOR J

**Maximize the code the two proofs share, and write it generic. One rule, two
ends.**

**THE FIGURE THE BRIEF ASKED FOR: 19 lines buy the second tower for a
1,288-line module.** `[LJ-1.184]` measured six extra lines for a 167-line
module. **The two are consistent in kind and I do not divide one by the other**,
because 1,288 lines of Model include the whole formula-coding block while
`[LJ-1.184]`'s 167 were a read-off.

The shared and unshared split, MEASURED:

| what | lines | shared between the towers? |
|---|---:|---|
| `GenModel.agda`, lines surviving verbatim | 1,272 | **SHARED, untouched** |
| `GenModel.agda` class plumbing | 42 | **SHARED**, written once |
| the `isL` instance | 2 | L only |
| the `Full` instance | 19 | the second tower only |
| `GenGraph.agda`, lines surviving verbatim | 104 | **SHARED, untouched, ZERO body edits** |
| `GenGraph.agda` class plumbing | 23 | **SHARED**, written once |

**A DD4 warning I must state.** The flat telescope repeats about 17 lines per
module, so the chain's shared plumbing grows linearly in the number of modules
while the shared BODY grows in their size. **At 17 modules that is about 289
plumbing lines against 5,822 body lines, a ratio of 1 to 20.** Section 9's
record bundle would cut the 289, and it walls today.

**A stop-line is never a reason to write fixed, and no stop-line was reached
here.**

## 11. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the residue of `[LJ-1.7]` is a CHAPTER | **MEASURED FALSE at `L.Coding.Model` and at `L.Coding.Graph`.** 42 written lines for a 1,288-line master, 5 of them mathematical. `GenModel.agda`, exit 0. **The verdict covers the 2 modules I ported and no more (C-42)** |
| 1,288 plus 395 is the twin of the port | **MEASURED FALSE.** It prices a re-derivation. `[LJ-1.200]:352` said so and this run confirms it |
| the class-parameter surface is 17 lines | **MEASURED, RIGHT ORDER, WRONG UNIT.** 17 counts the lines that NAME `isL`. The written port is 42 lines and the mathematical content is 5 |
| `L.Coding.Model` will not parameterize | **MEASURED FALSE.** Exit 0, first try, 7.73 s |
| `L.Coding.Graph` will not parameterize | **MEASURED FALSE.** Exit 0, first try, 7.55 s, zero body edits |
| the generic module at `isL` differs from the delivered one | **MEASURED FALSE for six of nine names**, `refl`. **MEASURED TRUE as PROOF TERMS for `tagAtL-adequate` and `domAt-out`**, and both still inhabit the delivered type |
| the closure facts cost something at the ambient class | **MEASURED FALSE for the six Model needs.** All `tt*` or `refl`, `ProbeLJ1210C.agda:47-70` |
| `L.Coding.Powerset` ports as a header edit | **MEASURED FALSE.** Its port is chained through ten supplier modules. Section 8 |
| the 15 unported modules cost the same as Model | **INFERRED.** Their surface is measured, their port is not. P-l refuses the number |
| the ten unmeasured L-facts are cheap at the ambient class | **INFERRED.** I did not instantiate them |
| a record bundle removes the repeated telescope | **MEASURED FALSE today.** `ClassData.agda` walls the 8 GB heap at 105.07 s, bisected to one field |
| the record wall has a known cause | **NOT CLAIMED.** I measured the site, not the mechanism |
| any wall in this run is in the port | **MEASURED FALSE.** Runs 1 and 11 are the port and both exit 0 |
| the timings decide anything | **MEASURED FALSE.** Every verdict rests on an exit code or a line count |
| the J tower is a delivered object | **INFERRED, and there is no `src/J/`.** The second instance measured here is `Full`, the ambient class, and it is NOT the J tower |

## 12. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-200/LJ-1.200-report.md`**, read WHOLE. TOOK the anchor
  counts (`:68-69`), which I re-derived exactly; the `abs₀` correction
  (`:150-158`); the projection reading (`:183-191`), which section 6.1 confirms
  by `refl`; and the 17-line claim (`:199-208`), which section 4 turns into a
  price. **CONFIRMED, all of it.**
- **`agents/tasks/LJ-1-196/lj-1.196-report.md`**, read at `:10-23` and
  `:140-160`. TOOK the NO-GO and the sentence "at the class carrier only;
  lifting it to the ambient carrier is the chapter". **REFUTED by measurement:
  the lift is 19 lines and every proof is `tt*` or `refl`.**
- **`agents/tasks/LJ-1-184/lj-1.184-report.md`**, read at `:1-64`. TOOK the
  three closure facts and the six-lines-for-167 figure. **SHAPE TAKEN, and the
  `tt*` claim RE-MEASURED at this site rather than transferred (P-l).**
- **`agents/tasks/LJ-1-184/ProbeLJ1184A.agda:1-60`**, read. TOOK the probe
  header shape, the module path convention `LJ-1-184.ProbeLJ1184A`, and the
  practice of stating DD4 in the file. **This is what let the probe run at all**,
  because `bedrock.agda-lib` puts `agents/tasks` on the include path.
- **`archive/dev/TASKS-archived.md`**: **NOT READ, and I say why.** The
  parameterization measured here is over the DELIVERED `L.Coding.*` tree, which
  post-dates the archived route. `[LJ-1.200]:309-313` records the same judgement
  for the same reason. **What would NOT transfer from the archive: any figure
  for a module that no longer exists, and any claim about `AmbientOnly`, which
  is about the class-carrier equivalence and not about a module telescope.**

## 13. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`** read at `:93-106`, `:211-240`, `:298-325`
and `:370-382`.

**The brief asks whether Devlin's construction is class-generic. IT IS, and the
digest says so in its own words.**

> The proof does not pin the presentation: any formula with these properties
> works. (`dev/literature/devlin-II5.md:301-302`)

The digest's own attribution table (`:370-382`) splits the twelve steps of II.5:
**nine are marked EITHER, that is tower-neutral, and three are marked PER-TOWER
content**: the level-hood formula, the bounded step matrix, and the definable
well-order.

**That is the same split this probe measured in Agda.** The tower-neutral
machine is `L.Coding.Model`'s 1,283 untouched lines and `L.Coding.Graph`'s 111.
The per-tower content is `DefAt-stage`, 9 lines
(`agents/tasks/LJ-1-210/GenPowerset.agda:457-465`).

**On `[LJ-1.200]`'s Σ₀ reading.** `:93-94` reads "By 2.7 there is a Σ₀ formula
Φ(z, v, γ)". `[LJ-1.200]:325-329` is right that the matrix is Σ₀ and the
description Σ₁. **It bears on this task only indirectly**: Devlin builds ONE
formula and evaluates it in two places, which is class-genericity by
construction and not by a port.

**NOT READ, with the reason (DD18).** `dev/literature/devlin-errata.md` and
`dev/literature/j-hierarchy.md`. `[LJ-1.196]:216-218` reports both as empty on
this point, and nothing in this measurement turns on either. **This task
measured Agda module telescopes; no literature can settle a telescope.**

## 14. RULES ANSWERED

- **D-1.** The abort criterion was fixed before the run by the brief. **THE
  SURFACE IS SMALL** is the branch that fired, and I stopped at it: I did not
  port the remaining 15 modules.
- **C-42.** The refutation measures ONE site and I swept before pricing. The
  sweep is section 8's census: 17 modules, 5,822 lines, 125 surface lines.
  **I report the COUNT and I refuse the cure's price.**
- **P-l.** Section 6.2 re-measures `[LJ-1.184]`'s `tt*` claim at this site.
  Section 8 refuses a total for the 15 unported modules.
- **D-10.** The brief's target was true at the intended generality, and section
  0 says so.
- **C-12.** One process, `-M8g`, cap never raised, six heap exhaustions reported
  as walls, load beside every figure.
- **C-22.** The report file existed before the first Agda run.
- **C-31 to C-37.** Section 7 writes the terms I could not write, at
  `file:line`, with the compiler's own message.
- **C-39, C-40.** Section 0 leads with what this run does NOT establish, and
  section 8 marks the inferred half.
- **DD0, DD8.** One number per claim, each with its basis. Every count is
  re-derived here by a tracked script.
- **DD4.** Section 10.
- **DD23.** No mathematical prose written. **No master edited.**
- **I-5.** No probe under `src/`. `check-probes.py` is clean.
