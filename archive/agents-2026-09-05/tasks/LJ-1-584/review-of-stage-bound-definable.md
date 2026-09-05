# NO-GO: `stage-bound-definable`

The obligation
`agents/tasks/LJ-1-584/Probe584.agda::stage-bound-definable` is NOT in the
probe. This file states why, names the term that blocks it, and names what
would reopen it.

**THE PROBE IS GREEN, EXIT 0, THREE RUNS** (`agents/tasks/LJ-1-584/runs/final-1.out`
to `final-3.out`). Nothing is postulated, there is no hole, `--safe` is on, and
nothing landed in `src/`.

## THE OBLIGATION'S TYPE IS WRITTEN AND IT IS NOT INHABITED

`Obligation` (`agents/tasks/LJ-1-584/Probe584.agda:95`) is `[LJ-1.568]`'s `Def`
(`agents/tasks/LJ-1-568/Probe568.agda:189`) at the triple the brief names:
`a := LsetS α oα`, `b := ordS α oα`, `g := fst (stage-card-upper α oα α∈suc α∉ω)`.
`Def` is IMPORTED and not restated, so the interface cannot drift.

## IT IS NOT FALSE, AND THE REASON IS A ROW THAT TYPECHECKS

**`V = L` GIVES THE OBLIGATION OUTRIGHT AND UNTRUNCATED.**
`vl→obligation` (`agents/tasks/LJ-1-584/Probe584.agda:108`) is
`[LJ-1.561]`'s `ambient-graph-isL` (`agents/tasks/LJ-1-561/Probe561.agda:171-176`)
followed by `[LJ-1.568]`'s `graph→def` (`agents/tasks/LJ-1-568/Probe568.agda:368-374`).
Nothing on that path is truncated.

So `refuting-obligation-refutes-V=L` (`Probe584.agda:126`): a refutation of the
obligation is a refutation of `V = L`, which no chapter of `src/` has.
**THIS FILE THEREFORE DOES NOT CLAIM THE STATEMENT IS FALSE.** It measures that
`L.StageCardinal` cannot build it. This is a construction gap, and the same
distinction `[LJ-1.580]` drew at its own site.

## THE BLOCK: EVERY VALUE OF THE INJECTION IS A VALUE OF AN AMBIENT PARAMETER

**THIS IS A THEOREM IN THE PROBE AND NOT A READING OF THE SOURCE.**
`value-is-a-sq-value` (`agents/tasks/LJ-1-584/Probe584.agda:200`): for every
stage α and every inductive input `ih`,

    ∥ Σ[ m ] Σ[ φ ] ( Dfn (⟪ α ⟫↪ m) φ ≡ ⟪ Lset α ⟫↪ x )
                  × ( fst (sq α α∈suc infα) (m , cnt m φ)
                      ≡ fst (limit-step α α∈suc oα infα ih) x ) ∥₁

The proof is one projection of `leastOf` (`src/L/WellOrder/Base.lagda.md:158-160`),
which returns the least element together with the predicate at it. The predicate
is `class-pred` (`src/L/StageCardinal.lagda.md:319-324`), whose only occurrence
of the value is `B.pair m (cnt m φ) ≡ y`.

**AND `B.pair` IS `sq` APPLIED, AND NOTHING ELSE.** `pair-is-sq`
(`agents/tasks/LJ-1-584/runs/W3a.agda:41-46`) is `refl`. `B` is
`Bound α oα infα (sq α α∈suc infα)` (`src/L/StageCardinal.lagda.md:283`).

**AND `sq` IS A MODULE PARAMETER CARRYING INJECTIVITY AND NOTHING ELSE**
(`src/L/StageCardinal.lagda.md:17-19`). It names no formula, no Levy grade and
no stage.

So by `[LJ-1.568]`'s `def∥↔conclusion` (`agents/tasks/LJ-1-568/Probe568.agda:387-393`),
the obligation is EQUIVALENT to putting the graph of a function whose every
value is a value of `fst (sq α α∈suc infα)` into L. **That is a code for an
arbitrary ambient function, which is `[LJ-1.533]`'s wall**
(`agents/tasks/LJ-1-533/lj-1.533-report.md:42-43`).

## AND `sq` IS NOT DATA AT THE ONLY CONSUMER

`src/L/SquareLawClosed.lagda.md:325-328` proves the square law **TRUNCATED**
only: `sq-trunc-closed : ... → ∥ sq δ ∥₁`. `src/L/StageBound.lagda.md:42` says
of the collection to a family "Not inhabited", and the chapter spends the
truncation through `bounded-from-trunc` (`src/L/StageBound.lagda.md:122`), a
`PT.rec` into the PROPOSITION `⟨ x ∈ˢ Lset κ ⟩`.

**SO THERE IS NO CANONICAL `stage-card-upper` IN THE TREE.** There is one per
representative of `∥ SqFam α ∥₁`. `dev/literature/truncation-and-selection.md:146-148`
records the law this runs into: "`leastOf` delivers the least INDEX untruncated,
and any payload it delivers with the index is a proposition. **A data payload
does not come out.**" The obligation asks for data (a `Formula S 3`) about a
`g` that is itself only defined up to that choice.

## THE FINDING THE NEXT BRIEF NEEDS: THE BRIEF ASKED FOR MORE THAN THE REOPENER SPENDS

Read the two signatures in the probe against each other.

- `Obligation` (`Probe584.agda:95`) takes `α∈suc` and `α∉ω`, **because it must
  name `stage-card-upper`**, and `stage-card-upper` is computed from
  `sq α α∈suc α∉ω`.
- `Reopener` (`Probe584.agda:250`) takes neither. It is
  `InjL (LsetS α oα) (ordS α oα)`, and `InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁`
  (`src/L/GCH.lagda.md:38`). **It names no injection, so it constrains no
  injection, and it is a TRUNCATION: any coded injection pays it.**

`obligation→graph` (`Probe584.agda:230`) shows the obligation is SUFFICIENT.
Nothing shows it is necessary, and the reopener's own type says it cannot be:
a target that quantifies over all codes cannot demand one named function.

**SO THE OBLIGATION AS STATED IS STRICTLY STRONGER THAN `[LJ-1.580]`'s REOPENER.**
`dev/literature/truncation-and-selection.md:83-84` is the same law from the
sources: "A cardinal inequality is a truncated existence of an injection ... a
proof that only needs cardinal arithmetic never needs an injection as data."

## THE C-42 SWEEP: HOW FAR THE SHAPE EXTENDS

C-42 orders the count before the cure. The shape is **a bare ambient injection
handed to a chapter of `src/` as a module parameter, carrying injectivity and no
`Formula`**. Grepped at today's tree:

**SEVEN parameter lines, THREE distinct objects, THREE chapters.**

| object | lines |
|---|---|
| `sq` | `src/L/StageCardinal.lagda.md:17`, `src/L/BoundedSubset.lagda.md:1388`, `src/L/StageBound.lagda.md:67` |
| `absorbs` | `src/L/BoundedSubset.lagda.md:1392`, `src/L/StageBound.lagda.md:69`, `src/L/StageBound.lagda.md:97` |
| `ih` | `src/L/StageCardinal.lagda.md:281` |

`absorbs` is `[LJ-1.580]`'s block
(`agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:49-61`). `sq` is this
one. **THE TWO INDEPENDENT ROUTES TO THE INTERNAL STAGE BOUND DIED AT THE SAME
SHAPE, AT DIFFERENT PARAMETERS OF THE SAME TWO CHAPTERS.** `ih` is not a third
case: it is supplied internally by `branch` (`src/L/StageCardinal.lagda.md:534`),
never by a caller.

`sq` and `absorbs` differ in one way that matters to a next brief: `sq` HAS a
producer in the tree, truncated (`src/L/SquareLawClosed.lagda.md:325-328`);
`absorbs` has NONE (`agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:62-71`).

## WHAT WOULD REOPEN IT

**Not this obligation.** Two routes, and neither is `Def` at `stage-card-upper`.

1. **AIM AT `Reopener`, NOT AT `Obligation`.** `InjL (Lset α) α` is `sq`-free and
   truncated. A next brief may assume `SqFam α` freely under `PT.rec`, because
   the target is a proposition, and then build ANY coded injection. It does not
   have to describe the one the chapter happens to compute.
2. **GIVE `L.StageCardinal` A DEFINABLE PAIRING INSTEAD OF `sq`.** If the module
   took a pairing that came with a formula rather than a bare injection, section
   2's theorem would carry the formula through to `h`, because `class-pred`'s
   other two ingredients are already internal: `defSet` is `𝒟ₒ`
   (`src/L/StageCardinal.lagda.md:400-401`), and the least-element selection is
   the ordinal order (`src/L/StageCardinal.lagda.md:258-259`). **THE PAIRING IS
   THE ONLY UNDESCRIBED INGREDIENT.** This is a re-parameterisation of a
   delivered chapter and it is priced against nothing measured; it is named as a
   route, not funded.

3. **MEASURE THE WEAKLY CONSTANT ENDOMAP ON `sq δ`.** The archive already named
   this and named it FIRST: `archive/dev/JOURNAL.md:1366-1367` reads "**That endomap on
   `sq δ` is now the widest unmeasured term, and the next probe is named for
   it.**" By Kraus, Escardó, Coquand and Altenkirch Theorem 16
   (`dev/literature/truncation-and-selection.md:158-160`) such an endomap is
   EXACTLY what lifts `∥ sq δ ∥₁` to `sq δ`, which would make `stage-card-upper`
   canonical and put a describable pairing in reach. **THAT PROBE WAS NAMED AND,
   BY THE ABSENCE OF ANY `Def` FOR THIS `g` AT TODAY'S TREE, IT HAS NOT LANDED.**

**A WARNING FOR WHOEVER WRITES THE NEXT PROBE.** `runs/W3b.agda` is one row:
`step α IH oα α∈suc infα` against
`limit-step α α∈suc oα infα (branch α oα α∈suc infα IH)` by `refl`, which is
`src/L/StageCardinal.lagda.md:562` read back. **IT DOES NOT TERMINATE**
(`agents/tasks/LJ-1-584/runs/w3b-1.out`, a 180 s bound the run did not reach the
end of, at 98.8% CPU with the resident set pinned at 1,154,848 KB: a conversion
loop and NOT a heap event). The same file without that row is green in 1.22 s
(`runs/w3a-1.out`). **DO NOT PUT `step` INTO A CONVERSION PROBLEM.** Measure
`limit-step` instead, which is the same value at every stage the induction
visits. This file does not claim the W3b loop is what stopped `[LJ-1.572]`. It
claims only that the row reproduces the symptom in 180 seconds.

## A BRIEF PREMISE THAT DOES NOT CHECK

**PREMISE 10 CITES A FILE THAT IS NOT IN THIS TREE.** Its basis is
`agents/tasks/LJ-1-572/LJ-1.572.md:1`, and `agents/tasks/LJ-1-572/` DOES NOT
EXIST here: `[LJ-1.572]` left not even its brief on disk. What does exist is its
row set in `dev/pod/table.toml`, admitted 2026-08-23; the `no-go-stated` row is
`dev/pod/table.toml:19146-19160`. The premise's CLAIM (a timeout with no report)
is consistent with the absence, and this file relies on none of it. The basis is
reported because a report that cannot be checked can only be believed.
