# LJ-1.620 report: where the four paid ingredients would live

Status: IN PROGRESS. No commit, no push. ASD-STE100. Written as a
skeleton before any Agda run (C-22) and filled as each run lands.

## THE VERDICT

(FILLED AFTER THE RUNS)

## D-10, THE GRAPH, BEFORE ANY AGDA

I read the `import` and `open import` lines of all **102 masters** under
`src/` (the count comes from `find src -name '*.lagda.md' | wc -l` and a
per-file extraction loop; no count in this report comes from a command
containing `head`). The per-file import lists are the evidence base for
every host claim below, each cited at `file:line`.

The four paid ingredients, as `[LJ-1.594]`'s table states them
(`agents/tasks/LJ-1-594/review-of-pairing-suffices.md:40-44`):

| ingredient | paid by | type-only rows in this probe |
|---|---|---|
| (i) `D` and its inversion | `[LJ-1.613]` | `Probe620.agda` section 1 |
| (ii) the least-element selection | `[LJ-1.613]` | `Probe620.agda` section 2 |
| (iv) the branch and its Recursion instance | `[LJ-1.601]` + `[LJ-1.608]` | `Probe620.agda` section 4, imported |
| (v) `keyS`, the coded copy | `[LJ-1.600]` | `Probe620.agda` section 3, imported |

## W3, THE IMPORT CLOSURE OF (v), MEASURED ALONE FIRST

(FILLED AFTER THE W3 RUN)

## THE FOUR COMPONENT ROWS, MEASURED

(FILLED AFTER THE MAIN PROBE RUN)

## FOUR INGREDIENTS, FOUR HOMES

One row each: chapter, import edge added, or the blocker.

| ingredient | cheapest host measured | new import lines | blocker |
|---|---|---|---|
| (i) | (FILLED) | (FILLED) | the definability chapter `L.Definability` itself is blocked: the rows need `Lset` and `𝒟ₒ` from `L.Constructible`, and `L.Constructible` already imports `L.Definability` (`src/L/Constructible.lagda.md:37`); the reverse edge is a cycle |
| (ii) | (FILLED) | (FILLED) | (FILLED) |
| (iv) | (FILLED) | (FILLED) | (FILLED) |
| (v) | (FILLED) | (FILLED) | (FILLED) |

## THE CHEAPEST ONE

(FILLED)

## WHAT A LANDING BRIEF FOR IT WOULD HAVE TO CARRY

(FILLED)

## THE GATES

(FILLED: individual checks run; `make check` NOT run, the brief forbids it)

## W2, ANSWERED

(FILLED)

## ARCHIVE USED

(FILLED: every candidate named)

## LITERATURE USED

(FILLED: every candidate named)
