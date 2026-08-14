# LJ-1.226: build `pairω` into L, the widest unmeasured line in the route

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.217]` closed A6 at 446 and then named what replaced it:「the two open
A5 rows (`pairω`, the column square) remain the widest unmeasured lines in the
route」.**

**`[LJ-1.176]` priced A5 at 547 lines and marked exactly two rows INFERRED:**

| row | object | lines | class |
|---|---|---:|---|
| 4 | the column square `pair` | **99** | INFERRED, `lj-1.176-report.md:205` |
| 5 | **`pairω`, the pairing on `ω`** | **160** | INFERRED, `:206` |

**And it warned about both, in its own words at `:252` and `:265`:「Row 5 may be
far too LOW, and this is the larger risk」and「Row 4 may be too low as well」.**

**`:446` is blunter still: for `pairω`,「NOBODY HAS WRITTEN ONE」.**

**Build `pairω`. Measure it. That is DD8: gate the widest unmeasured term before
anything funds the block.**

## WHY THIS ONE AND NOT THE OTHERS

**A-prime's seven cells now sum to 1,548, and `[LJ-1.217]` correctly refuses to
quote that as a price** because 555 lines still rest on reading. **`pairω` is
the single largest INFERRED item with an explicit warning that it is low.** A
number that may be「far too low」at 160 lines can move the route's total more
than every reading residue together.

**`pairω` is A5's and not A6's. MEASURED by one grep at
`lj-1.176-report.md:452`**, so `[LJ-1.217]`'s move of two objects into A6 does
not carry it.

## THE METHOD THE TREE ALREADY MEASURED, and it is a comparable

**`[LJ-1.176]` MEASURED that an A5 object builds into L by ONE separation, at
1.72 s.** **`[LJ-1.152]` MEASURED a GO at 2.50 s with NO second replacement,
because separation carries it at 2,500 to 1.**

**P-l: both are comparables and NEITHER is a price for `pairω`.** **Re-measure
at this site.**

## THE SHAPE LESSON, freshly measured TODAY, and it is a hypothesis here

**`[LJ-1.217]` MEASURED that the same four conjuncts price 120 to 1 apart by
SHAPE alone:** the fibre `sv` conjunct walls at **1,810 s**; the fibre `ij`
conjunct is a **type error** at 4.78 s; **the DIRECT-EQUALITY shape of the same
content is green in 15.0 s.**

**Try the direct-equality shape FIRST.** **This is a hypothesis at your site and
not a price (P-l), and if the fibre shape is the only one that expresses
`pairω`, say so.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BUILT AT OR NEAR 160.** Report the written lines and the seconds with load.
  **Then A5's row 5 is MEASURED, the largest inferred item in the route is
  closed, and I re-price A-prime.** STOP.
- **BUILT, BUT MATERIALLY OVER 160.** **Report both numbers.** **`[LJ-1.176]`
  predicted this and said so; a confirmed overrun is a real result and it
  re-prices A5.**
- **IT WALLS.** **Interrupt at 20 MINUTES on a single `agda` invocation.**
  Report the ELAPSED SECONDS, then bisect. **Every cut gets the SAME bound as
  its green control, and the control's elapsed time is reported BEFORE any cut
  is interpreted** (`[LJ-1.215]`'s law, which `[LJ-1.217]` applied today).
- **THE OBJECT IS NOT NEEDED.** If `pairω` dissolves the way `[LJ-1.156]`
  dissolved A5's `CSB` and `[LJ-1.176]` dissolved the 300-line item, **say so
  with the evidence.** **That is the best outcome available and this project has
  had it twice.**
- **THE COLUMN SQUARE IS FREE AFTER IT.** If row 4 falls out of your build,
  measure it too and report both. **Do NOT start with it.**

## WHAT YOU MUST NOT DO

- **Do not re-price A5's other five rows.** `[LJ-1.176]` measured them and
  `[LJ-1.217]` re-checked the sum. **You measure rows 5 and, if it is free,
  4.**
- **Do not quote 1,548 as A-prime's total.** `[LJ-1.176]` and `[LJ-1.217]` both
  refuse it and the refusal stands.
- **Do not edit any master.** This is a probe. **Nothing lands in `src/`.**
- **Do not touch `src/L/Choice/Name.lagda.md`** (DD23), and **do not touch
  `agents/tasks/LJ-1-224/` or `LJ-1-225/`**: two siblings are live there.
- **A probe goes in `agents/tasks/LJ-1-226/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **A sibling
  holds the other Agda slot and it is running in the orchestrator's own harness,
  so `dispatch.py status` will show that slot as free. It is NOT free.**
  **Report the load beside every absolute figure**, discard a warm-up, and take
  at least three kept runs for any figure a decision rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **This task exists to convert ONE
inferred number. Do not hand back another.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`pairω` is a pairing on `ω`, and a pairing on `ω` is not obviously L-specific.**
**Say whether what you build is tower-neutral.** **`[LJ-1.223]` measured that
the whole coding chain is tower-neutral with a per-tower residual of ZERO, and
`dev/literature/devlin-II5.md:387-389` says the per-tower content is exactly two
objects.** **If `pairω` is neither of those two, it is shared code and it should
be written generic from the first line.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-176/lj-1.176-report.md`**, read WHOLE. **It is your brief
  within this brief:** the 547 price, the two inferred rows, both warnings, and
  the one-separation method at 1.72 s.
- **`agents/tasks/LJ-1-217/lj-1.217-report.md`**, sections 2 and 5: the
  fixed-shape finding and A6's closed price. **Its `ProbeLJ1217A.agda` is a
  green 512-line file and a working example of the direct-equality shape.**
- `agents/tasks/LJ-1-156/`: how A5's `CSB` DISSOLVED, and `ProbeLJ1156A.agda`,
  whose `:496-497` is the column square and `:111-159` is
  `NumeralPresentation` and `pairω`.
- `agents/tasks/LJ-1-152/`: the GO at 2.50 s and「separation carries it」.
- `agents/tasks/LJ-1-175/lj-1.175-report.md`: the five measured overlaps, so you
  do not re-count a line another block already carries.
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **The retired route reached its own trophy and may already hold a pairing on
  `ω`. Take SHAPE from the archive, never a claim**, and say what would NOT
  transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/rudimentary-functions.md:68` is cited by `[LJ-1.176]` for the
basis it inferred from.** **Read it and say whether it settles `pairω`'s size or
only its existence.** Say separately whether
`dev/literature/devlin-II5.md:387-389`'s two per-tower objects include this one.
Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-176/lj-1.176-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-226/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed above.
- **DD8.** Gate the widest unmeasured term before you fund the block. **This
  task IS that gate.**
- **P-l.** 1.72 s and 2.50 s are comparables and NOT prices for `pairω`.
- **C-36.** Write the term you could not write.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-i, P-k, P-m, P-t, P-y, R-40. C-12, C-22, C-39, C-40. DD0, DD24, D-10,
  D-26, D-29, D-30. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with ONE number: `pairω`'s measured written lines, against the inferred
160.** Then the seconds with load and run count. Then which shape you used and
whether the direct-equality form worked. Then the column square if it came free.
Then whether the object is tower-neutral. **Mark every negative MEASURED or
INFERRED.**
