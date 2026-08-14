# LJ-1.229: A2's range set and `ranAt`, the block every other block names

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.227]` produced the gate list DD8 demands: all five residue blocks have
a named widest term and a probe, and NONE of the five dissolves.** **A2 is the
one to run first, for three reasons it measured:**

1. **Every downstream block names A2's predicate.** A3, A4 and A5 all state「g
   is an injective graph from a to b」. **Until that predicate is a master,
   nothing downstream is statable** (`lj-1.136-report.md:351-354`).
2. **`injAt` and `IsInjGraph` exist NOWHERE in `src/**/*.lagda.md`.** I
   re-derived this: zero hits across every master. **The only copy is the probe
   `agents/tasks/LJ-1-134/ProbeLJ1134A.agda:61-93`**, which I moved out of
   `src/` today because it was untracked and one `git clean` from gone.
3. **Measuring A2 also pins the ONE surviving double-count** in Route A-prime's
   sum. Section「THE SECOND DELIVERABLE」below.

## THE WIDEST UNMEASURED TERM, named by `[LJ-1.227]`

**The range set, and the `ranAt` formula with adequacy.**

**`[LJ-1.134]` named both unpriced at `lj-1.134-report.md:177-180`, and its
probe took「every value lies in C」as a HYPOTHESIS.** **A master cannot. It must
PRODUCE C by replacement over the graph, and it must write `ranAt` to mirror
`domAt`.**

**A2's core is MEASURED at 78 lines. The two range pieces are NOT measured.**

## THE METHOD, and both halves are delivered

- **Build the range set with `hasReplacementL`**, delivered at
  `src/L/Axioms/Full.lagda.md:277`.
- **Write `ranAt` with both adequacy readings, mirroring `domAt`**, delivered at
  `src/L/Coding/Model.lagda.md:278`.
- **The probe's shape is `[LJ-1.134]`'s, plus the replacement step.** **Start
  from `agents/tasks/LJ-1-134/ProbeLJ1134A.agda`. Do not rebuild its core.**

**`[LJ-1.227]` infers 4 to 5 Agda minutes, with `hasReplacementL` the dominant
term at 254 s for one site (`lj-1.136-report.md:1059`).** **P-l: that is a
comparable at another site and NOT your price.**

## THE SECOND DELIVERABLE, and it corrects a figure in three documents

**`[LJ-1.227]` re-checked `[LJ-1.175]`'s five overlaps and RESOLVED four. One
stands: A4 consumes A2's predicate rather than rewriting it, so A4's 190
double-counts part of A2's 170.**

**It could not close the size by reading, and it said so: the floor is 27 lines
(the `injAt` description, `lj-1.134-report.md:219-227`) and the ceiling is A2's
full 78-line core. A4 needs the DESCRIPTION and the ADEQUACY conjuncts. It does
NOT need the READBACK. No report separates those two pieces.**

**Separate them. Measure the description plus adequacy apart from the
readback.** **That single number replaces a 27-to-78 range and corrects
A-prime's sum from「1,470 to 1,521」to one figure.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BOTH RANGE PIECES BUILD.** Report the written lines for the range set and
  for `ranAt`, against A2's standing 170. **Then A2 is MEASURED, the first
  residue block is closed, and the four remaining probes are writable.** STOP.
- **BUILT, BUT MATERIALLY OVER 170.** Report both numbers. **That re-prices A2
  and every block that names it.**
- **REPLACEMENT IS THE WALL.** If `hasReplacementL` over the graph does not
  elaborate, **name the term and stop.** **`[LJ-1.152]` MEASURED that separation
  carries a composition at 2,500 to 1 where replacement was assumed necessary.
  Ask whether separation carries this one too.** That would be the best outcome
  here.
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Every cut gets the SAME bound
  as its green control, and the control's elapsed time is reported BEFORE any
  cut is interpreted** (`[LJ-1.215]`'s law; `[LJ-1.217]` applied it today and
  found a 120-to-1 shape difference).
- **THE DOUBLE-COUNT CANNOT BE SPLIT.** If the description and adequacy cannot
  be measured apart from the readback, **say why**, and the 27-to-78 range
  stands.

## THE SHAPE LESSON, freshly measured today, and it is a hypothesis here

**`[LJ-1.217]` MEASURED that the same four conjuncts price 120 to 1 apart by
SHAPE alone**: the fibre form walled at 1,810 s, the direct-equality form is
green at 15.0 s. **If an adequacy conjunct wants a fibre, try the direct
equality first.** **P-l: a hypothesis at your site, not a price.**

## WHAT YOU MUST NOT DO

- **Do not edit any master.** This is a probe. **Nothing lands in `src/`, and a
  probe under `src/` is forbidden by I-5.** I moved three strays out of `src/`
  today; **do not put one back.**
- **Do not price A3, A4, A5, A6 or A7.** `[LJ-1.227]` named their terms and
  `[LJ-1.226]` is measuring A5's `pairω` right now. **You measure A2, and the
  A2-inside-A4 double-count.**
- **Do not quote 1,548 or 1,470 as A-prime's total.** Three reports refuse a
  total and the refusal stands.
- **Do not touch `agents/tasks/LJ-1-226/` or `LJ-1-228/`.** Two siblings are
  live there.
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-229/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **A sibling
  holds the other Agda slot.** **Report the load beside every absolute figure**,
  discard a warm-up, and take at least three kept runs for any figure a decision
  rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.227]` MEASURED that A2 is TOWER-NEUTRAL: its predicate names no `isL`
and no L stage, and `[LJ-1.223]` measured the whole coding chain tower-neutral
with a per-tower residual of ZERO.** **So write A2 generic from its first
line.** **A structure parameter costs nothing at the start and `[LJ-1.210]`
measured that retrofitting one costs 42 lines on a 1,288-line module.** **Say
whether the range set and `ranAt` stayed tower-neutral, or whether either
reached for `isL`.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-227/lj-1.227-report.md`** section 2 and section 7.1,
  read WHOLE. **Your two deliverables are stated there.**
- **`agents/tasks/LJ-1-134/lj-1.134-report.md`** and
  **`ProbeLJ1134A.agda`, read WHOLE**: the 78-line core, the readback GO, the
  per-part table at `:219-227`, and the two unpriced range pieces at
  `:177-180`. **This is your starting file.**
- `agents/tasks/LJ-1-136/lj-1.136-report.md` with `ProbeLJ1136A.agda` and
  `ProbeLJ1136B.agda`: A4's price at `:302` and `:87`, the consumption claim at
  `:359-368`, and `hasReplacementL` at 254 s at `:1059`.
- **`agents/tasks/LJ-1-152/lj-1.152-report.md`**: separation carrying what
  replacement was assumed to need, at 2,500 to 1.
- `src/L/Axioms/Full.lagda.md:277` and `src/L/Coding/Model.lagda.md:278`: **read
  the delivered `hasReplacementL` and `domAt`, never a report about them.**
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **The retired route reached its own trophy and may hold a range set. Take
  SHAPE from the archive, never a claim**, and say what would NOT transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:387-389` says the per-tower content is exactly
two objects, and `[LJ-1.227]` measured that A2 is NEITHER.** **Say whether
Devlin's proof needs a range set at this point, or whether it takes the range
for granted.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-134/lj-1.134-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-229/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed above.
- **DD8.** One estimate, and it names its basis.
- **P-l.** 254 s and 78 lines are comparables and NOT prices for your pieces.
- **C-36.** Write the term you could not write.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
  **`[LJ-1.134]` took「every value lies in C」as a hypothesis; you supply it.**
- **C-42.** A refutation measures the site it names, never its extent.
- **I-5.** No probe under `src/`.
- **P-i, P-k, P-m, P-t, P-y, R-40. C-12, C-22, C-39, C-40. DD0, DD24, D-10,
  D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with TWO numbers: A2's measured written lines against the standing 170,
and the description-plus-adequacy size that pins the A4 double-count.** Then the
range set and `ranAt` separately. Then whether replacement was needed or
separation carried it. Then the seconds with load and run count. Then whether
A2 stayed tower-neutral. **Mark every negative MEASURED or INFERRED.**
