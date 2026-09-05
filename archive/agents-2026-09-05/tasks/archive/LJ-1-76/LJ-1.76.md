# LJ-1.76: build the split composition as masters

tier: codex (default)

## GOAL

**Build the cheapest measured shape for real.** Two partial masters and a
composer, replacing the vacuous `TwelveAgree` that HEAD currently carries.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`dd3aa13`**. HEAD is green.

## THE OWNER'S RULING THAT AUTHORIZES THIS

The owner ruled: **commit the work now, and settle the DD24 threshold
question when the phase's content is complete.** This dispatch completes
content. **It does not trade the threshold away and it must not be reported
as doing so.**

## WHAT IS MEASURED, so you build rather than explore

| shape | result |
|---|---|
| 12 rows in one module | **WALL**, 275 s |
| 9 rows in one module | **WALL**, 260 s |
| 6 rows, full 69-fact telescope | green, 209.82 s |
| **6 rows, only its own 43 facts** | **green, 122.45 s** |
| four 3-row partials in ONE file | **WALL**, 373.50 s |
| partial FILES plus a composer file | **green**, composer 28.98 s |

**The peak is bounded per PROCESS**, so separate masters are what makes this
work. `[LJ-1.75]` tabulated which 43 facts each half uses, per row, at
`file:line`. **Read that table and use it. Do not re-derive the counts.**

**Target: two six-row partials of 43 facts each, plus a composer, about
274 s across three invocations.**

## WHAT TO BUILD

1. **Two partial masters.** Rows 0 to 5 (Mem, Eq, And, Or, Imp, Neg) and
   rows 6 to 11 (Top, Bot, Exist, Forall, AllIn, ExIn). Each carries ONLY
   its own 43 facts and proves the partial conjunction, both directions,
   at the abstract frame.
2. **A composer master.** It applies the two partials' already-proved
   `out`/`back` and conjoins them into the twelve-row agreement, both
   directions. **It must NOT re-apply the rows**; that is what makes it
   cheap and what keeps P-w's interposition finding off it.
3. **Remove the vacuous `TwelveAgree`** from
   `src/L/Condensation.lagda.md:6412`. `[LJ-1.71]` proved its `tagEq`
   uninhabited at every frame, so it proves nothing; I verified that myself
   and it has zero consumers. **Removing it is not a deletion of content: it
   is removing a statement that was never true.** Back it up outside the
   repository first and say where.

**You choose the module layout and you say what you chose.** `src/L/` already
has subdirectories (`src/L/Coding/`, `src/L/Ordinal/`), so a
`src/L/Condensation/` directory is consistent with the tree. **If you add a
directory under `src/`, give it a `README.md`.**

## WHAT YOU MUST NOT DO

- **Never touch `src/Everything.lagda.md`.** I wire the catalog after
  auditing your work.
- **Do not leave any master non-compiling.** `[LJ-1.72]` did and it cost a
  revert. **Every master you create or edit must check green before you
  report, and you must say so with its seconds.**
- **Do not raise the heap cap.** C-12. A wall is a result with its seconds.
- **You may not weaken a statement and you may not narrow a direction.** Both
  directions of every row and of the composition are required. **A partial
  conjunction of six rows is a partial conjunction; dropping a row is not.**
- **Do not drop a fact a row uses.** `[LJ-1.75]`'s 43 are what its six rows
  consume; that is the whole set and no more.
- **Do not touch anything under `src/L/Coding/`.**
- **Name probes `src/Probe*.agda`, never `.lagda.md`.**

## THE ACCEPTANCE TEST

**C-38: a hypothesis is discharged when something SUPPLIES it, never when it
is restated.** So:

- **The composer must produce the twelve-row agreement**, both directions,
  from the two partials. Report it at `file:line`.
- **Say plainly whether anything now consumes it.** If nothing does, say so:
  the composer is then delivered-and-unconsumed and C-35 applies to it, and
  that is honest rather than a discharge.

**Do not report a discharge on a parameter count.**

## THE ABORT CRITERION, fixed in advance per D-1

- **All three masters green**: report each one's cold seconds at C-12
  caliber, then run `python3 scripts/check-ratio.py --check` and quote its
  aggregate **with the seconds against the ceiling, not only the multiple**.
  Then STOP. Do not wire `SatGraphAgree`, `LeafAgree`, `levelIn` or `cover`.
- **Any master walls or fails**: **STOP**, revert your edits to
  `src/L/Condensation.lagda.md`, leave the tree green, and report the wall
  with its seconds.

**Either way this dispatch ends after the three masters are measured.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

Two narrower telescopes restate the 17 shared facts twice. `[LJ-1.75]` named
that trade. **Say what the J tower inherits from the split**, whether the
partials are generic in the slots, and whether the J tower can reuse the
composer or needs its own.

## ARCHIVE (DD18)

- **`_build/lj-1.75-report.md`**, read WHOLE. **Its section 1 is the fact
  table you build from**, and section 2 the measured partial.
- **`_build/lj-1.74-report.md`**, read WHOLE, and its probes
  `src/ProbeLJ174*.agda`. The ladder, the split shape and the composer.
- `_build/lj-1.72-report.md` sections 1a and 1b, the repaired per-row
  telescope.
- `_build/lj-1.71-report.md` and `src/ProbeLJ171A.agda`, the refutation that
  makes the removal correct.
- `dev/LESSONS.md` **C-38**, C-35, P-w as amended, P-t (`:2601`),
  D-30 (`:3255`), P-o (`:2509`), read WHOLE.
- `dev/STYLE-i18n.md` for the master's marker grammar, and
  `dev/STYLE-agda.md` for the OPTIONS header, since you are creating new
  masters.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature prices a spelling.** Say so in one line and spend
nothing.

## SCOPE (read)

`_build/lj-1.75-report.md` section 1 FIRST, then `src/ProbeLJ175A.agda` for
the reduced partial, then `src/ProbeLJ174*.agda` for the composer, then
`src/L/Condensation.lagda.md:6412-6470`.

## SCOPE (write)

New masters under `src/L/`, `src/L/Condensation.lagda.md`, and
`src/ProbeLJ176*.agda`. Your report is `_build/lj-1.76-report.md`. **Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38.** A hypothesis is discharged when something SUPPLIES it.
- **C-35.** A block with no consumer is UNTESTED. **Say if the composer has
  none.**
- **P-w as amended.** A composer of results is not an interposition.
- **P-t.** The class follows the FORMULA, not the carrier.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-o, P-q, P-u, P-v** as above.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35.** State the membership at the SMALL index and climb.
- **R-40.** State a membership witness SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-36, C-37.**
- **D-1, D-8, D-10, D-13, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck every master you create or edit, and every consumer. Do NOT run
  `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed**,
  and say the master count it reports.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check` on every file you touch.
- DD23 freezes mathematical prose. **A new master needs enough prose to be a
  master; keep it minimal and factual.**
- **The machine is quiet and both Agda slots are yours. Report the load
  average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.76-report.md` incrementally, skeleton first.

**Lead with the three masters' names and their cold seconds**, each green.
Then the composer's twelve-row agreement at `file:line`, both directions,
and whether anything consumes it. Then what you removed from
`src/L/Condensation.lagda.md` and where the backup is. Then the gate's
aggregate with seconds against the ceiling. **Mark every negative MEASURED or
INFERRED.** Then the DD4 answer and **the convergence answer.**
