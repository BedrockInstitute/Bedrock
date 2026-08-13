# LJ-1.74: split the twelve, so no module elaborates all of them

tier: codex (default)

## GOAL

Every shape measured so far puts **twelve row applications in one module**,
and every one of them walls. **Split them, and measure whether the wall
follows the total or the peak.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`787044d`**. HEAD is green. `[LJ-1.73]` left the tree byte-identical.

## WHAT IS MEASURED, so you do not re-derive it

| shape | where the twelve applications sit | result |
|---|---|---|
| `[LJ-1.72]` CUT2c | inside `TwelveAgree`, concrete cons-env | **WALL, about 210 s** |
| `[LJ-1.72]` CUT2opq | same, `envHypB2` sealed opaque | **WALL, about 220 s** |
| `[LJ-1.73]` | inside `TwelveAgree`, ABSTRACT env | **WALL, 265.18 s** |
| `[LJ-1.72]` CUT2tel | the same telescope with an EMPTY body | **green, about 105 s** |
| `[LJ-1.69]` | ONE row module at its discharge frame | **green, 3.6 s** |

**All at `GHCRTS="-A64m -I0 -M8g"`. Heap exhaustion, not type errors, not
load.**

**The empty-body row is the key comparison**: the sixty-nine argument checks
alone are affordable. **The where-block is what walls, and it walls whether
the environment is concrete or abstract.** So the cost follows the built
formula content inside the rows (P-t), not the carrier.

## THE QUESTION, and it has not been asked

`[LJ-1.69]` measured **one** row application at 3.6 s, green. Twelve would be
about 43 s of work. **Whether twelve wall is a question about PEAK
allocation, not about total seconds**, and nobody has separated those.

**So: does the wall follow the total, or the peak?**

Build a ladder and measure where it breaks:

1. `TwelveAgree` with **three** row applications and the matching partial
   conjunction.
2. With **six**.
3. With **nine**.
4. With **twelve** (the known wall, as the control).

**Report the seconds at each rung and the rung where it walls.** That single
table decides the architecture.

## THEN, IF THE WALL IS THE PEAK

If three or six are green and twelve is not, **split the composition across
module boundaries** so no single module elaborates more than the green
number: several modules each proving a partial conjunction of the rows, and
one small module composing those partials.

**A module that only composes already-proved partials does NOT re-apply the
rows**, so P-w's interposition finding does not bite: it is not re-exporting
a target, it is conjoining results.

**Measure the split shape.** If it is green, report its seconds and STOP.

**If a new master under `src/L/` would be needed to get separate Agda
invocations, do NOT create it. Say so and stop.** That is an architecture
change and it is the owner's.

## THE ABORT CRITERION, fixed in advance per D-1

- **The ladder walls at every rung above one**: STOP. Report the table. The
  composition cannot be built in this shape at all, and that goes to the
  owner.
- **A rung is green and the split shape is green**: report both, with
  seconds, and **STOP**. Do not wire `SatGraphAgree`, do not touch
  `LeafAgree`, `levelIn` or `cover`.
- **A rung is green but the split shape walls**: report both. That is a real
  finding about composition, not a failure.

**Either way this dispatch ends at the measurement.**

## WHAT YOU MUST NOT DO

- **Do not raise the heap cap.** C-12. **A heap exhaustion is a WALL with its
  seconds and it is a result, not a failure.**
- **Do not leave the master non-compiling.** Work in
  `src/ProbeLJ174*.agda`; if you edit the master, revert before finishing and
  say the tree is byte-identical to your start.
- **Name probes `src/Probe*.agda`, never `.lagda.md`.**
- **You may not weaken a statement and you may not narrow a direction.** A
  partial conjunction of three rows is not a weakening; dropping a row from
  the twelve is.
- **Do not interpose a module that re-exports another.** P-w.
- **Do not touch anything under `src/L/Coding/`.**

## THE REPAIRED TELESCOPE YOU BUILD ON

`[LJ-1.72]` sections 1a and 1b give the repair verbatim: `TwelveAgree`'s
universal `tagEq` and `numK` become twelve per-row fields each, the `KFacts`
shape, and the frame gains the forty union facts. **Both were checked green
in isolation.** `[LJ-1.73]`'s probe rebuilt them; read it and reuse it.

**Do not redesign the repair.** `[LJ-1.71]` proved the old universal `tagEq`
uninhabited, so the per-row form is required, not optional.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

A split composition is more modules and the same content. **Say whether the
J tower inherits the split unchanged**, and whether the partials are generic
in the slots as the rows are.

## ARCHIVE (DD18)

- **`_build/lj-1.73-report.md`** and **`src/ProbeLJ173A.agda`**, read WHOLE.
  The abstract wall and the probe you extend.
- **`_build/lj-1.72-report.md`**, read WHOLE. Sections 1a, 1b and 4: the
  repair and the wall table.
- `_build/lj-1.69-report.md`, the one-row measurement of 3.6 s and its
  instrument.
- `_build/lj-1.71-report.md`, the refutation the per-row form answers.
- `dev/LESSONS.md` P-t (`:2601`), P-w as amended, C-38, C-35, P-o (`:2509`),
  P-n (`:2483`), P-m (`:2460`), read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature prices a spelling.** Say so in one line and spend
nothing.

## SCOPE (read)

`src/ProbeLJ173A.agda` FIRST, then `_build/lj-1.72-report.md` sections 1a
and 4, then `src/L/Condensation.lagda.md:6412-6470`.

## SCOPE (write)

`src/ProbeLJ174*.agda` only, and `src/L/Condensation.lagda.md` **only if you
revert it before finishing**. Your report is `_build/lj-1.74-report.md`.
**Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **D-1.** The probe doctrine; the abort criterion is fixed above.
- **P-t.** The class follows the FORMULA, not the carrier. **This dispatch
  tests whether it also follows the COUNT.**
- **P-w as amended.** No interposition; a composer of partials is not one.
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
- **D-8, D-10, D-26, D-29, D-30.**

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

Write `_build/lj-1.74-report.md` incrementally, skeleton first.

**Lead with the ladder table: three, six, nine, twelve, with seconds and
green or WALL.** Then the split shape if you built it, with its seconds.
Then whether the wall follows the total or the peak, marked MEASURED or
INFERRED. **Mark every negative MEASURED or INFERRED.** Then the DD4 answer
and **the convergence answer.** Confirm the tree is byte-identical to your
start.
