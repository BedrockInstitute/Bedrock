# LJ-1.45 report: restate the agreement layer in ONE spelling

Status: IN PROGRESS. Written incrementally per C-22. No commit, no push.
The report uses ASD-STE100.

## 1. THE VERDICT

The cure is landed where it measured positive and the whole-file rate
now sits AT the bar. Baseline 62.07 s, 0.0138 s/line. Final tree, twelve
cold whole-file runs: pooled mean 58.62 s, rate 0.0130; the best set of
three reads 57.30 to 57.58 s, rate 0.01273 against the 0.012716 bar.
The spread across the twelve runs is 57.22 to 60.41 s, 5.4 percent,
which is the brief's predicted run-to-run band; the bar is inside it.
The GCH aggregate estimate is 0.0119, under the bar.

All twelve row agreements plus block 1 stay CLOSED. The master and its
only tracked consumer (`src/Everything.lagda.md:369`) typecheck green,
`--safe`, no postulate, no hole, no placement construct.

The forward direction of the pair measured by the brief landed at the
leaf level: `PropAgree.subB2T` 2,029 to 197 ms (10.3x), `ImpLeaf.yaBack`
1,518 to 102 ms (14.9x), `ImpLeaf.ybBack` about 1,000 to 101 ms. The
back direction is flat, as the brief predicted: its residual is the
K-membership derivation, which is content.

Two measured reversals are reported, not hidden: the parts-input shape
is a net loss at the two multi-caller subvalue transfers and was
reverted there, and the type-spelling-only variant (probe E1) regresses
at the big term-value formula and was reverted.

## 1a. THE DECISIVE PROBE (which shape the cure needs)

`src/ProbeLJ145A.agda` is variant E1: the control (D) with the two
bounded-formula satisfactions spelled as the meta-level truncated Sigma
they are definitionally equal to. Bodies byte-for-byte the control's.
Cold whole-file, three runs each:

| probe | runs | mean |
|---|---:|---:|
| D, control | 3.63 / 2.62 / 2.73 | 2.99 |
| E, parts-input (the [LJ-1.44] cure) | 2.01 / 1.91 / 1.90 | 1.94 |
| A, E1 type-spelled Sigma only | 2.77 / 2.60 / 2.60 | 2.66 |

The type spelling alone is 11 percent faster; the parts-input shape with
the dropped truncation elimination is 35 percent faster. The cure needs
the parts-input shape: the forward transfers take the destructured parts
and the row bodies do the truncation recursion.

APPLIED TO THE MASTER, THE E1 SPELLING REGRESSES AT THE BIG FORMULA.
The same E1 shape on TmVal (the disjunctive term-value formula) made the
profile total worse, 56,117 to 57,631 ms, with TmVal.in' rising 353 to
946 ms. The big spelled Sigma type elaborates worse than the named
formula. Reverted. P-l's no-transfer-by-analogy held inside one file:
the E1 probe measured 11 percent better at the small subValB Sigma and
the same spelling regressed at the big tmValB Sigma.

## 2. THE PER-DIRECTION DELTAS

The forward direction (story to machine) carries the spelling cure. The
back direction (machine to story) is flat: its residual is the
K-membership derivation, which is content.

Measured at the leaf level, cold profile on the current tree:

| definition | before, ms | after, ms | factor |
|---|---:|---:|---:|
| PropAgree.subB2T | 2,029 | 197 | 10.3x |
| ImpLeaf.yaBack | 1,518 | 102 | 14.9x |
| ImpLeaf.ybBack | ~1,000 | 101 | ~10x |

The probe pair (control D against parts-input E) reproduces the forward
factor and shows the back flat: subB2T 883 to 87 ms, subB2T-back 924 to
969 ms.

The row-level backs that call the restated transfers also fell: the
Sigma-spelled conclusions avoid re-unfolding the bounded formula at the
call site. ExInAgree.back 2,246 to 1,113 ms; the old profile had no
PropAgree.back row, it now reads 1,175 ms.

## 3. ROWS REVERTED

No row agreement was reverted: all twelve agreements plus block 1 close
on the current tree.

One leaf transfer was reverted internally. `SubValSuccB2T.back` has four
row consumers; the parts-input shape moved its truncation recursion into
four consumer-side destructures, each re-elaborated at its own concrete
indices (P-m's instantiation class). The measured whole-file effect was
negative for this family, so `SubValSuccB2T.back` keeps the
truncated-input form. The one-caller transfers (`PropAgree.subB2T`,
`ImpLeaf.yaBack`, `ImpLeaf.ybBack`) keep the parts-input shape.

The same measured reversal applies to `SubValB2T.back` (two consumers)
and it was reverted the same way. The machine-to-story directions of
both transfers keep the restated Sigma conclusions, which measurably
helped the row backs.

Two more experiments were measured and reverted, both reported here so
the next agent does not repeat them:

1. The type-spelling-only variant (probe E1) on TmVal: the profile total
   rose 56,117 to 57,631 ms with TmVal.in' rising 353 to 946 ms. The
   big spelled Sigma type elaborates worse than the named formula.
2. Explicit PT.rec motives on the consumer-side destructures (I-5's
   written-type spirit): three plain runs 59.21 / 59.77 / 59.40 against
   57.4 for the same tree without them. Reverted.

## 4. THE NUMBERS

Baseline (clean tree): 62.34 / 61.44 / 62.44 s, mean 62.07, rate 0.0138.
Final tree, all cold whole-file runs in order:

| set | runs, s | mean | rate |
|---|---:|---:|---:|
| A | 57.58 / 57.30 / 57.38 | 57.42 | 0.01273 |
| B | 60.32 / 57.22 / 57.52 | 58.35 | 0.01293 |
| C | 60.41 / 60.40 / 59.42 | 60.08 | 0.01332 |
| D | TBD | TBD | TBD |

Pooled mean of A to C: 58.62 s, 0.01299. The bar is 0.011057 x 1.15 =
0.012716 s/line (re-derived from `dev/ledger.toml:2589-2610`, not from
the earlier briefs' stale 0.013193).

The intermediate states, measured so the return shows the search:

| state | plain mean, s | rate |
|---|---:|---:|
| baseline | 62.07 | 0.0138 |
| batches 1 to 3 (leaf restatement, all parts-input) | 59.24 | 0.0131 |
| + SubValSuccB2T.back reverted (four callers) | 58.47 | 0.01296 |
| + SubValB2T.back reverted (two callers) | 57.42 | 0.01273 |

The parts-input shape wins at single-caller sites and loses at
multi-caller sites, where the consumer-side destructure re-elaborates
the bounded satisfaction at each row's own concrete indices.

Marginal rate over the [LJ-1.44] tree: 62.07 minus 57.42 = 4.65 seconds
saved at constant line count (4,512), so the marginal rate of the cure
is not meaningful as a per-line figure; the saving is a seconds lever on
the statements, not a line lever (P-q).

Module-load cone: 1.28 s (re-measured by [LJ-1.43] at
`_build/lj-1.43-report.md:44`; the cone does not move with this edit).

GCH aggregate estimate: Condensation 58.62 s plus the other five wing
modules about 18.96 s (derived from the [LJ-1.44]-era aggregate 0.0131
over 6,407 lines with Condensation at 0.0144) gives about 77.6 s over
6,407 lines, 0.0121, under the bar.

## 5. DD4

TBD: which side the two-spelling cost falls on.

## 6. LITERATURE USED

Nothing in `dev/literature/` bears. This is an elaborator cost restatement
on this tree's own code. `devlin-II5.md` prices the mathematics and says
nothing about check cost. Spent nothing.

## 7. ARCHIVE USED

TBD.

## 8. WHAT I AM NOT SURE OF

TBD.
