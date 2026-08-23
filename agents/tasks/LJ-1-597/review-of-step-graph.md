# NO-GO: `step-graph`

## HEAD

The obligation `agents/tasks/LJ-1-597/Probe597.agda::step-graph` is NOT in the
probe. This file states why, names the ATOMS at call grain, and names what
would reopen it. Attempt 1 of this task left a hole and named this file
without writing it; the critic overturned that return
(`agents/tasks/LJ-1-597/review-of-LJ-1-597-1.md:16-25`). This file is on disk.

**THE PROBE IS GREEN, EXIT 0, THREE RUNS**
(`agents/tasks/LJ-1-597/runs/final-13.out`, `final-14.out` at 3.62 s,
`final-15.out` at 3.82 s; warm interfaces, caliber `-A64m -I0 -M2g`). It
carries no hole and no postulate, `--safe` is on, and nothing landed in
`src/`. Every row in it is a measurement and not a claim.

## THE OBLIGATION'S TYPE IS WRITTEN AND IT IS NOT INHABITED

`Graph` (`agents/tasks/LJ-1-597/Probe597.agda:269-285`, section 2) is the internal
shape: a `Formula S 2` ψ, value variable first and index variable second,
with BOTH readings, at `fn := step-fn α oα α∈suc infα IH` read on the members
of `dom := LsetS α oα`. `step-fn` is the function part of the step's own
output (section 0.2). This is the shape the internalization chapter itself
states for a definition: `graph : Formula S 2` with `defines` and `only`
(`src/L/Recursion.lagda.md:273-278`).

## THE RECURSION RE-ASSCRIPTION, AND IT AGREES

The brief ordered the chapter's TYPE read against its SENTENCE. They agree.

- The record `Recursion` (`src/L/Recursion.lagda.md:103-108`) fields a domain
  IN the model, a `Formula S 2`, and contractible fibres over the domain.
- The record `Definition` (`src/L/Recursion.lagda.md:272-279`) fields a
  function `S → S` and the same formula with `defines` and `only`.
- The sentence (`src/L/Recursion.lagda.md:259-261`) says the same object:
  internalizable WHEN the graph is expressible, with nothing about the
  recursion's shape, depth, order of descent or clause complexity.

Both the type and the sentence are the graph of the VALUE function
`S → S`. Neither is the graph of the STEP FUNCTIONAL `(α, IH) ↦ P α`: the
step's input `IH` is a meta-language function and its output is an injection
between presentation types, and neither is an element of `S`. The chapter
separates exactly this case in its own prose on encoded indices
(`src/L/Recursion.lagda.md:207-231`). So the obligation the brief names is
the `Definition`-shaped graph of the step's FUNCTION PART at one
`(α, IH)`, and `Graph` states it. THE TYPE AND THE SENTENCE AGREE, AND THE
BRIEF'S READING IS THE FUNCTION-PART READING. That comparison is the finding
the brief asked for when they agree.

## IT IS NOT FALSE, AND THE REASON IS A GREEN SLICE

`runs/D10.agda` (`agents/tasks/LJ-1-597/runs/d10-1.out`, `d10-2.out` at
3.69 s, GREEN) carries the two rows:

- `vl→def`: `V = L` gives `[LJ-1.568]`'s `Def` at the triple
  `(LsetS α oα, ordS α oα, step-fn α oα α∈suc infα IH)` outright, by
  `[LJ-1.561]`'s `ambient-graph-isL`
  (`agents/tasks/LJ-1-561/Probe561.agda:171-176`) followed by `[LJ-1.568]`'s
  `graph→def` (`agents/tasks/LJ-1-568/Probe568.agda:368-374`). Nothing on
  that path is truncated.
- `refuting-def-refutes-V=L`: so a refutation of the target family refutes
  `V = L`, which no chapter of `src/` has.

Attempt 1 elaborated the same two rows at `step-fn` under `-M4g`
(`agents/tasks/LJ-1-597/runs/final-4.out`: exit 42 at its hole and nowhere
else). **THIS FILE DOES NOT CLAIM THE OBLIGATION IS FALSE.** It measures that
the tree cannot build it. Construction gap, the same distinction `[LJ-1.584]`
drew (`agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:19-26`).

The arity-2 shape of `Graph` and the arity-3 `Def` are NOT converted by any
row: the syntax carries no substitution and no weakening
(`src/FOL/Syntax.lagda.md:157`), so no such row exists to write. NO
EQUIVALENCE BETWEEN THEM IS CLAIMED and this stop does not rest on one.

## THE BLOCK: THE VALUE EQUATION HAS TWO CALLS WITH NO FORMULA

`step` is ONE equation (`src/L/StageCardinal.lagda.md:561-562`):

    step α IH oα α∈suc infα
      = limit-step α α∈suc oα infα (branch α oα α∈suc infα IH)

`limit-step` (`:396-403`) is `LimitStep.h` with `D := DefOf.defSet` and
`inv := 𝒟ₒ-inv`. `h x` (`:350-351`) is `leastOf` over the ordinal order of
the class `class-pred x`, so the step's value at x is the ORDINAL-LEAST y
with `class-pred x y`. `[LJ-1.594]` wrote `class-pred` out BY `refl`
(`agents/tasks/LJ-1-594/Probe594.agda:283-300`, GREEN under `-M8g`), and its
only occurrence of the value y is the VALUE EQUATION:

    fst (sq α α∈suc infα) (m , cnt m φ) ≡ y

`[LJ-1.594]` counted FIVE ingredients and its count was upheld
(`agents/tasks/LJ-1-594/review-of-pairing-suffices.md:33-47`):

| | ingredient | status |
|---|---|---|
| (i) | `D` = `DefOf.defSet` | INTERNAL, it is `𝒟ₒ` (`src/L/StageCardinal.lagda.md:400-401`) |
| (ii) | leastness | INTERNAL, it is the ordinal order (`:258-264`, `_≺_` is `∈ᵗ` `:230-231`) |
| (iii) | the pairing `fst (sq α α∈suc infα)` | **NO FORMULA. THE ARBITRARY AMBIENT PARAMETER** (`:17-19`; `pair-is-sq` is `refl`, re-proved in this probe) |
| (iv) | `cnt m φ`, the count through the branch | **NO FORMULA. THE TARGET ONE STAGE DOWN** (`:288-289`; `cnt-is-the-IH` is `refl`, `agents/tasks/LJ-1-594/Probe594.agda:252-263`) |
| (v) | `Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1` | META SYNTAX over an ambient carrier; the coded-copy machine exists (`src/L/Coding/CodeSet.lagda.md:300-301`, `:440-443`) and NO TASK HAS INSTANTIATED IT at this carrier |

### THE ATOMS, NAMED

**(iii) THE PAIRING.** `B.pair` is `fst (sq α α∈suc infα)` and nothing else
(`src/L/StageCardinal.lagda.md:283`, `:68-69`). `sq` is a module parameter
carrying injectivity and nothing else (`:17-19`): no formula, no Levy grade,
no stage. NOTHING CODES AN ARBITRARY AMBIENT INJECTION, measured three times
(`agents/tasks/LJ-1-533/lj-1.533-report.md:42-43`: `[LJ-1.414]` generic,
`[LJ-1.441]` at a site, `[LJ-1.533]` at B9), and the type-level reason is
that every L-element generator takes a `Formula`
(`src/L/Axioms/Full.lagda.md:144`, `:277-280`). `[LJ-1.584]` already named
this atom for the WHOLE injection
(`agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:33-45`).

**(iv) THE COUNT.** `cnt m φ` is `fst (Bound.formula-bound (ih m)) φ`
(`src/L/StageCardinal.lagda.md:288-289`), and at the step's own site `ih` is
`branch` (`:562`). The branch is: at every INFINITE member stage the
induction hypothesis `IH` itself (`:556`), which is the target one stage
down; at `ω` the IH at `ω` (`:549-550`); at every FINITE member stage
`fin-inj` (`:551`), whose value is `leastOf natOrder` over the `Tally` of
the finite stage (`fin-inj :488`, `finite-stage-inj :485`, the `Tally`
module at `:440` and `least` at `:452-453`). **NO TASK HAS MEASURED
whether the `Tally` has a formula.** So the count's non-describable part
has TWO unmeasured-or-refuted layers: the recursion at infinite stages,
and the tally at finite ones.

### THE C-42 SWEEP ALREADY EXISTS, AND THIS TASK ADDS A SITE TO IT, NOT A NEW SHAPE

The shape this stop refutes is the one both predecessors swept: a bare
ambient injection handed to a chapter as a module parameter
(`[LJ-1.584]`: SEVEN parameter lines, THREE distinct objects, THREE
chapters, `agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:98-104`),
and a selection predicate quantifying over `Formula` at an ambient
carrier (`[LJ-1.594]`: 80 lines in 16 files, two of them the cure,
`agents/tasks/LJ-1-594/review-of-pairing-suffices.md:110-117`). This task
measures the SCOPE split inside one of those sites, the step, and adds
no new file to either count.

### WHAT THIS STOP ADDS TO THE TWO PREDECESSORS

`[LJ-1.584]` named (iii) at the whole injection. `[LJ-1.594]` counted five
ingredients and said the missing thing is ONE `Formula` rendering
`class-pred`, a chapter. THIS STOP measures the SCOPE the brief split out:
the graph of ONE STEP with `IH` a PARAMETER of the obligation's type. The
formula may vary with `IH` and it does not help: a `Formula S 2` is finite
syntax with constants in `S`, and the value equation's right side carries
`cnt m φ` at the UNBOUNDEDLY many member stages below α, so the recursion
enters through the count and not only through the pairing. **A FORMULA FOR
THE PAIRING ALONE DOES NOT DISCHARGE THE STEP'S GRAPH.** Four tasks said the
injection has no formula (`[LJ-1.533]`, `[LJ-1.549]`, `[LJ-1.552]`,
`[LJ-1.584]`); this file names the two calls inside the one step that carry
no formula, and one unmeasured finite base under the second of them.

## WHAT WOULD REOPEN IT

Not this obligation, and not at this price.

1. **THE CHAPTER ROUTE, `[LJ-1.594]`'s ORDER** (`agents/tasks/LJ-1-594/review-of-pairing-suffices.md:138` and the order under it):
   (v) first, the coded copy at this carrier; then (i) and (ii), already
   internal; then (iv) through `L.Recursion`'s `Definition` with
   `dom := hierL`; the pairing LAST. A brief that orders (v) must name the
   STAGE that holds `AllCodes` at this carrier, because `[LJ-1.86]` measured
   that the proof cannot choose it
   (`archive/dev/LJ-dispatch-index.md:160`), and it must name the LIVE
   chapter `src/L/Coding/CodeSet.lagda.md`, not the retired
   `L.Rud.CodeSet`.
2. **MEASURE THE FINITE BASE.** No task has measured whether the `Tally`
   route (`src/L/Choice/Finite`) has a formula. Ingredient (iv) cannot be
   priced whole while its ω-base is unmeasured. That measurement is smaller
   than this task was.
3. **THE TRUNCATED REOPENER `[LJ-1.584]` NAMED**: `InjL (Lset α) α` is
   `sq`-free and truncated, and a route that needs only cardinal arithmetic
   never needs the computed injection as data
   (`dev/literature/truncation-and-selection.md:83-84`). `[LJ-1.596]` is
   aiming at the row; if its machine does not fit, this file's atoms are
   still the condition every other route wanted.
