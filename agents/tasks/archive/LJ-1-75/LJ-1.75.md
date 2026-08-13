# LJ-1.75: give each partial only the facts its rows use

tier: codex (default)

## GOAL

**One measurement.** The 105 s argument-check floor is half of every
partial's cost and it is paid once per partial. **A six-row partial does not
use sixty-nine facts. Measure what it costs with only the facts its rows
need.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`00220e7`**. HEAD is green and `[LJ-1.74]` left the tree byte-identical.

## WHAT IS MEASURED, so you do not re-derive it

`[LJ-1.74]` settled the mechanism: **the heap wall follows the PEAK, and the
peak is bounded per PROCESS**, not per module instance.

| shape | result |
|---|---|
| 3 rows in one module, full 69-fact telescope | green, **167.60 s** |
| 6 rows, same telescope | green, **209.82 s** |
| 9 rows, same telescope | **WALL**, 259.74 s |
| 12 rows, same telescope | **WALL**, 274.99 s |
| four 3-row partials in ONE file | **WALL**, 373.50 s |
| four 3-row partial FILES plus a composer file | **green**, 161/162/159/139 + 28.98 s |
| the same telescope with an EMPTY body (`[LJ-1.72]` CUT2tel) | green, **about 105 s** |

**Six is the largest green rung**, so the cheapest split I can price today is
**two partials of six rows**: `2 x 209.82 + 28.98 = 448.6 s`.

## THE QUESTION

**The 105 s floor is the sixty-nine argument checks.** It is 50 percent of a
six-row partial's cost, and the split pays it once per partial.

**A six-row partial does not use sixty-nine facts.** Each row draws on its
own tag facts and its own closure facts; the union is what `TwelveAgree`
needs, not what any six rows need.

**So: give each partial only the facts its six rows actually use, and
measure.**

1. **Count first, and report the count**: for rows 0 to 5, and for rows 6 to
   11, which of the sixty-nine facts does each set actually consume? Read the
   row modules' parameter lists in `src/L/Condensation.lagda.md`, whose line
   ranges `[LJ-1.70]` section 1 lists.
2. **Then measure** a six-row partial carrying only its own facts, cold, C-12
   caliber, against the 209.82 s full-telescope figure.

**If the floor scales with the fact count**, the two-partial split gets
cheaper by roughly the fraction removed, and that changes the number an
architecture decision is made against.

**If it does not scale**, say so: that is a fact about where the floor comes
from, and it is worth having.

## THE ABORT CRITERION, fixed in advance per D-1

- **A reduced-fact six-row partial is green**: report its seconds, the fact
  count it carries, and the implied two-partial total. **STOP.**
- **It walls, or is not cheaper**: report the number. **STOP.**

**Either way this dispatch ends at that one comparison.** Do not build the
split for production, do not create a master under `src/L/`, do not wire
`SatGraphAgree`, and do not touch `LeafAgree`, `levelIn` or `cover`.

**Creating separate masters is an architecture change reserved to the
owner.** This dispatch measures only.

## WHAT YOU MUST NOT DO

- **Do not raise the heap cap.** C-12. **A heap exhaustion is a WALL with its
  seconds and it is a result, not a failure.**
- **Do not drop a fact a row actually uses.** If a row needs it, it stays.
  **Removing a needed fact would make the partial fail, and removing a fact
  by weakening a row is the defect C-38 was admitted for.**
- **Do not leave the master non-compiling.** Work in
  `src/ProbeLJ175*.agda`; if you edit the master, revert before finishing and
  say the tree is byte-identical to your start.
- **Name probes `src/Probe*.agda`, never `.lagda.md`.**
- **Do not interpose a module that re-exports another.** P-w.
- **Do not touch anything under `src/L/Coding/`.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

Per-partial telescopes are less shared statement than one union telescope.
**If the reduction works, name that trade**: what the J tower would inherit,
and whether two narrower telescopes are still generic in the slots.

## ARCHIVE (DD18)

- **`_build/lj-1.74-report.md`**, read WHOLE, and its probes
  `src/ProbeLJ174*.agda`. The ladder, the split and the partial shape you
  narrow.
- **`_build/lj-1.72-report.md`** section 4, the 105 s empty-body floor that
  this dispatch attacks, and sections 1a and 1b for the repaired telescope.
- `_build/lj-1.70-report.md` section 1, which lists the twelve row modules'
  parameter line ranges. **That is where the fact counts come from.**
- `_build/lj-1.73-report.md` and `src/ProbeLJ173A.agda`, the abstract frame.
- `dev/LESSONS.md` P-t (`:2601`), P-w as amended, C-38, D-30 (`:3255`),
  P-m (`:2460`), P-n (`:2483`), read WHOLE. **D-30 is the question this
  dispatch asks: price what the CONSUMER needs.**
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature prices a spelling.** Say so in one line and spend
nothing.

## SCOPE (read)

`_build/lj-1.74-report.md` sections 1 and 2 FIRST, then
`src/ProbeLJ174P0.agda` for the partial shape, then the twelve row modules'
parameter lists in `src/L/Condensation.lagda.md` per `[LJ-1.70]` section 1.

## SCOPE (write)

`src/ProbeLJ175*.agda` only, and `src/L/Condensation.lagda.md` **only if you
revert it before finishing**. Your report is `_build/lj-1.75-report.md`.
**Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **D-1.** The probe doctrine; the abort criterion is fixed above.
- **D-30.** Price what the CONSUMER needs. **This dispatch is D-30 applied to
  a telescope.**
- **P-t.** The class follows the FORMULA, not the carrier.
- **P-w as amended.** No interposition.
- **C-38.** A hypothesis is discharged when something SUPPLIES it.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k, P-l, P-m, P-n, P-o, P-q, P-u, P-v** as above.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35.** State the membership at the SMALL index and climb.
- **R-40.** State a membership witness SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-8, D-10, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **HEAD is green and the tree is clean;
  leave it that way.**
- Do NOT run `make check`. You need not run `check-ratio`.
- **Run `scripts/check-fences.py --check` before you report anything closed**,
  and confirm it reads 84 masters.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check` on
  anything you touch.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours. Report the load
  average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.75-report.md` incrementally, skeleton first.

**Lead with the fact counts: how many of the sixty-nine each six-row half
uses**, at `file:line`. Then the measured seconds of a reduced-fact six-row
partial against the 209.82 s full-telescope figure, and the implied
two-partial total. Then whether the floor scales with the fact count,
**MEASURED or INFERRED.** Then the DD4 trade. **Mark every negative MEASURED
or INFERRED.** Confirm the tree is byte-identical to your start.
