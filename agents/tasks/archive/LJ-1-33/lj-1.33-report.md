# LJ-1.33 report: leg D measured at its own site

Status: COMPLETE. Written incrementally per C-22. Untracked probes, no
commit, no push. The report uses ASD-STE100.

## 1. THE VERDICT

**NO-GO.** Leg D's measured rate is **0.34 seconds per line**, 25.7 times
DD24's bar (0.013193). The gate is NO-GO at or above 0.05.

The number comes from two flat cold runs of `src/ProbeLJ133.agda`: 50.99 and
50.90 seconds of user time over 150 non-blank non-comment lines. The rate is
0.3396. The block needs a re-shape before funding.

The target is true. The two-way decode typechecks at the intended
generality. D-10 passes: the residue is not false, it is expensive.

## 2. WHAT YOU BUILT

The probe is `src/ProbeLJ133.agda`. It is the smallest decisive miniature of
leg D: one clause's two-way decode against the delivered machine's
projections, at variable slots. `src/ProbeLJ133Ctrl.agda` is the control.

The story side is the bounded step clause, in the Clause style of
`src/L/Condensation.lagda.md`. It is `StepBnd` (arity `suc n`), the bounded
restatement of the machine's step: the value at the argument is the set of
exactly those z with c in b, w recorded by f at c, and d the definable
powerset of w, with z in d. The three existentials are bounded: c by b,
w by the bound K, d by the bound K. The bound K sits at slot zero, the
machine's slots v b f are shifted by one. This mirrors the Clause module's
shape: the bounded matrix at variable slots with the bound at slot zero.

The machine side is the delivered `StepAt` at the same environment, with its
delivered projections: `StepAt-out` and `StepAt-in`
(`src/L/Coding/Sequence.lagda.md:217-229`), and the step formula's own
`extAt-out` and `extAt-in` readings
(`src/L/Coding/Model.lagda.md:662-678`). The body of the bounded clause is
definitionally the delivered `StepBody` at the shifted slots
(`src/L/Coding/Sequence.lagda.md:113-120`), so the decode is about the real
site and no synthetic stand-in enters.

The two-way decode has four pieces:

1. `step-out₁`: a satisfied machine step, the `StepAt-out` content, the
   `PowOK` side condition, and the bound construction give the bounded
   story's witness content.
2. `step-out₂`: a satisfied machine step reads the bounded witness back into
   the value, through the step formula's own `extAt-in` with the bounds
   dropped.
3. `step-in₁`: the bounded witness is the machine step's own content, given
   to the delivered `StepAt-in` projection.
4. `step-in₂`: the machine step's own content assembles the bounded witness
   and the bounded story reads it back into the value.

The bound construction is a hypothesis (`BoundOK`), not a proof: the bound K
must contain every recorded value and its definable powerset. That content is
the carrier-facts row, not this row. The `DefAt` readings (`DefAt-in`,
`DefAt-out`) are the delivered powerset readings, used exactly as the
delivered machine uses them (`src/L/Coding/Sequence.lagda.md:181`,
`:200-201`).

## 3. COLD SECONDS AND LINES

The probe is 150 non-blank non-comment lines. The control is 61. The line
convention is `grep -v '^[[:space:]]*$' | grep -vc '^[[:space:]]*--'`.

Two cold runs of the probe, one Agda process each, quiet machine, at
`GHCRTS="-A64m -I0 -M8g"`. Dependencies were warm through
`_build/2.8.0/agda/src/`. The probe's own interface was moved aside before
each run. No interface ever sat beside a source.

| run | user s | wall s |
|---|---:|---:|
| 1 | 50.99 | 52.43 |
| 2 | 50.90 | 52.65 |
| mean | 50.95 | |

The pair is flat under the noise rule: the delta is 0.2 percent, under 5
percent.

Rate: 50.95 / 150 = 0.3396 seconds per line. DD24's bar is 0.013193. The
rate is 25.7 times the bar.

The control (same story formulas, no machine side) checks in 1.11 seconds of
user time over 61 lines. Its cost is near the import-cone floor; the story
side adds almost nothing. The machine-side decode carries the 0.34 rate.

The profile locates the seconds. `--profile=definitions` on the probe:

| definition | ms |
|---|---:|
| `step-in₁` | 15,223 |
| `hz` (the `DefAt-out` reading) | 11,950 |
| `writeWit` (the `DefAt-in` assembly) | 7,637 |
| `go` (the `StepAt-out` witness) | 7,532 |
| `dropB` (the bounds dropped) | 7,427 |
| the three `ha` helpers | 34 |
| miscellaneous | 1,396 |
| total | 51,204 |

The five named decode definitions carry 97 percent of the check. This is
P-t's signature: the cost is type elaboration of the built machine formula's
satisfaction, not missing types and not proof length.

## 4. WHICH COUSIN CLASS

Neither. The rate lands above both cousins, at the expensive end.

The low cousin is 0.0052, the variable-slot clause-to-content decode
(`_build/lj-1.15-report.md:82-91`). C-32 binds: that figure is pre-cure. The
post-cure anchor for the same class is block 1's delivered master at 0.0079
(`_build/lj-1.5-report.md:11-14`), and the control here checks in 1.11
seconds total, consistent with that class.

The high cousin is 0.085, the neutral-carrier decode class
(`dev/ledger.toml:643`). The measured 0.34 is 4.0 times that cousin.

The measured 0.34 sits at or above P-n's concrete-carrier floor band, 0.22
to 0.297 (`dev/LESSONS.md:2483`). It leans decisively to the expensive end,
not to either cousin.

The control explains why. The bounded step clause's own satisfactions at
variable slots are cheap. The machine side is not: the decode reads the
delivered `StepBody`'s satisfaction, whose tree contains `DefAt`, the
definable-powerset description (`src/L/Coding/Powerset.lagda.md:442-443`).
Every projection on that satisfaction forces the elaborator to unfold the
built tree, and the `DefAt-in` / `DefAt-out` readings carry the `DefOf`
machinery. This is P-t's law: the class follows the formula, not the carrier
(`dev/LESSONS.md:2601`). The machine formula is built, so the decode pays
the floor at variable slots.

## 5. DID IT NEED A PLACEMENT?

NO. The decode is a satisfaction-level two-way proof at variable slots. It
uses no `embed`, no `erase`, no `placeFo`, and no `absFo`. The bounded story
clause lives at the class carrier directly and uses the delivered readers
(`appAt`, `DefAt`, membership), so no Levy witness travels anywhere. This is
P-u's law from the other side: nothing is certified here (the clause's
Delta-0 certificate is a separate row), so no placement is needed and the
measured wall never enters.

## 6. THE PRICE OF THE NEXT BLOCK

With leg D at 0.34, the next block cannot fund.

| piece | lines | rate | seconds |
|---|---:|---:|---:|
| the clause-shaped residue, eleven more clauses | 2.7 to 3.0k | 0.008 to 0.010, MEASURED | 22 to 30 |
| leg D, the story-to-machine agreement | 0.3 to 0.8k | 0.34, MEASURED | 102 to 272 |
| total | | | 124 to 302 |

The GCH side's whole seconds budget is 99.6 to 147.7
(`dev/ledger.toml:305`). Leg D alone busts the budget's low end at its own
low line count. The block needs a re-shape before funding.

The re-shape direction, from the control: the story-side satisfactions are
cheap, and the machine-side reading is the cost. A re-shape must stop the
decode from unfolding the delivered machine's built body per use. One
candidate is a shared machine-reading layer, stated once and instantiated,
so the per-clause decode never mentions the built `StepBody` satisfaction in
its types. That layer would be template content. I did not measure it:
P-l forbids pricing it by analogy.

## 7. DD4

Leg D falls per-tower, and the measurement adds a DD4 finding.

The equivalence row is per-tower: each tower's story differs and each tower
proves its own agreement with its own machine. The measurement does not
move that placement. The decode shape is not a template half hiding inside
the row.

The finding is about WHERE the cost sits. The cost is the machine side:
reading the delivered `StepBody`'s built tree, dominated by `DefAt`. That
machine is shared by both towers. The story side is cheap. So a shared
machine-reading layer, written once, would buy the J tower the expensive
half for free, and the J tower's agreement row would then be much smaller
than the Def row. LJ-1.26's split books the equivalence whole in the
per-tower certificate list (`_build/lj-1.26-report.md:253-254`); this
measurement suggests the split should book the machine-reading half as
template.

D-26 bears directly, and the measurement answers it. The agreement's cost is
about the MACHINE, not the syntax. The machine's built tree (`StepAt`,
`DefAt`) is tower-neutral. D-26 predicts the J tower's row is much smaller,
and the measurement supports that prediction.

## 8. LITERATURE USED

`dev/literature/devlin-II5.md`, sections 2.1 to 2.8. WHY NOT deeper use:
Devlin has no story-to-machine agreement row at all, because his machine IS
the level formula. The literature cannot price this row
(`_build/lj-1.28-report.md:181` found this).

`dev/literature/devlin-errata.md`. NOT read. WHY NOT: the brief rules out
re-checking it, and `[LJ-1.14]` verified it does not cover Chapter II
section 5 (`_build/lj-1.14-report.md:107-108`).

## 9. ARCHIVE USED

`_build/lj-1.28-report.md`, in full. Took leg D's definition at `:95-106`,
the spread at `:128-135`, the machine-side cite at `:97-99`, and the
literature finding at `:181`.

`_build/lj-1.5-report.md`, in full. Took block 1's rate at `:11-14`
(0.0079), the pricing table at `:106-116`, the placement answer at
`:18-24`, and the DD4 split at `:117-138`.

`_build/lj-1.15-report.md`, in full. Took the 0.0052 at `:82-91` and the
unmeasured equivalence leg at `:187-191`.

`_build/lj-1.32-review.md`, in full. Took the erase-route mechanism at
`:284-311`, the post-cure re-runs at `:37-48`, and the wall ladder at
`:129-143`.

`_build/lj-1.27-review.md`, in full. Took the wall location at `:59-91` and
the erase-route mechanism at `:204-256`.

`_build/lj-1.26-report.md`, in full. Took the DD4 split at `:239-254` and
the probe design at `:279-310`.

`_build/lj-1.12-report.md`, sections 1 and 2. Took the component table at
`:20-49`: row 4, the equivalence against the delivered machine, at `:34`.

`archive/rud-route/src/L/Condensation.lagda.md`, in full. Read for SHAPE
only: the archived story is born parameter-free and decodes against the
meta-level reads at `:486-742`. Its target is classically false
(`[LJ-1.11]`), so no price was taken from it.

`dev/LESSONS.md`. P-m at `:2460`, P-n at `:2483`, P-t at `:2601`, P-u at
`:2908`, P-l at `:2305`, D-26 at `:1676`, D-10 at `:1316`, C-32 at
`:2947`. These decide the block.

`dev/ledger.toml`. The seconds budget at `:305`, the 0.085 class at `:643`.

`src/L/Condensation.lagda.md`, in full. `src/L/Coding/Sequence.lagda.md`,
in full. `src/L/Coding/Powerset.lagda.md`, `src/L/Coding/Model.lagda.md`,
`src/L/Constructible.lagda.md`. These fix the signatures; nothing was
reported from a name alone (D-10).

## 10. WHAT I AM NOT SURE OF

1. The rate is a miniature density. The probe is 150 lines with the fixed
   cost of the machine-body reading concentrated in a few definitions. The
   real row, 0.3 to 0.8k lines, may amortize that fixed cost over more
   proof lines, so its rate could sit below 0.34. The verdict does not
   move: even at the 0.085 cousin the row costs 26 to 68 seconds against a
   99.6 to 147.7 second budget.
2. The probe measures the step clause, the deep clause. The approximation
   and graph clauses' projections are one-liners
   (`src/L/Coding/Sequence.lagda.md:295-312`), so their decodes may be
   cheaper. The step is the binding clause, and its rate is the class
   certificate.
3. The bound construction and the vacuity arguments are hypotheses here,
   not proofs. Their cost is the carrier-facts row, which this probe does
   not price.
4. The re-shape (a shared machine-reading layer) is a hypothesis. P-l
   forbids pricing it by analogy; nothing measures it yet.
5. The bounded step clause's Delta-0 certificate is a separate wall. LJ-1.2
   showed the step's `DefAt` leaf carries unbounded quantifiers
   (`_build/lj-1.2-gate.md:28-35`). The decode needs no certificate, so
   the wall does not enter this measurement.
