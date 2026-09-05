# LJ-1.204: `Deserialization` rose 8.3 s at Condensation and no report owns it

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda, so it takes pro and holds an Agda slot.

## GOAL

**`[LJ-1.201]`, an adversarial review, found a term in its target's OWN raw
files that no report has ever claimed.**

**MEASURED:** `Deserialization` at `src/L/Condensation.lagda.md` went from
**1,689 ms** (`[LJ-1.155]`) to **9,955 / 9,954 / 10,230 ms** (`[LJ-1.185]`).
**That is 68 percent of the master's 12.3 s rise in ONE DAY, and 8.3 s outside
the residue everyone was arguing about.**

**Its size is MEASURED. Its cause is INFERRED. Nobody owns it.**

**Find the cause and price the cure.**

## WHY THIS MATTERS MORE THAN THE TERM IT WAS FOUND BESIDE

**It is LARGER than the 5.2 s `DeadCode` ceiling that `[LJ-1.177]` called the
wing's remaining lever, and larger than the 17.8 s residue's curable share.**

**And the wing's gap to the DD24 bar is 56 to 67 s.** An unowned 8.3 s is a
seventh of it, sitting in a phase nobody has profiled.

## WHAT `[LJ-1.201]` ALREADY RULED OUT, so you do not repeat it

- **Page cache**: three runs flat, so it is not a cold-start artifact. MEASURED.
- **Machine contention**: the LOADED day was FASTER, so load does not explain
  it. MEASURED.

**Start where it stopped.**

## THE OBVIOUS HYPOTHESIS, and it is INFERRED and mine

**`Deserialization` is interface reading.** Between the two measurements this
master gained imports and its dependencies gained content: `[LJ-1.172]` and
`[LJ-1.173]` landed the `Coding` masters `Bound`, `Key` and `KeyRead`, and
`[LJ-1.173]` cured 21 fields across three records.

**So the first thing to test is whether the rise tracks the INTERFACE SIZE of
what this master imports.** That is cheap: measure the `.agdai` sizes and
compare against the two dates.

**I may be exactly wrong. `[LJ-1.201]` did not test it and neither have I.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **CAUSED AND CURABLE.** Name the cause, price the cure in lines and seconds,
  and say **SHARED or WING-LOCAL**. STOP.
- **CAUSED AND NOT CURABLE.** If the rise is the price of content the wing now
  needs, **say so plainly.** That closes the question and it is a complete
  answer.
- **NOT REPRODUCIBLE.** If `Deserialization` is back near 1,689 ms today, **that
  is the finding**: something between the two dates was transient, and you say
  what changed. **Measure it before you explain it.**
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the elapsed seconds, bisect. A sibling ran ONE typecheck for
  3.06 hours on 2026-08-14.

## THE INSTRUMENT, AND `[LJ-1.201]` CORRECTED THIS PROJECT ON IT

**The ±12.8 percent in `check-ratio.py` is a ONE-MODULE BETWEEN-SERIES figure**,
by that file's own words at `:72-76`. **Within-series spread is 0.5 to 4.0
percent.**

**`[LJ-1.185]` applied the between-series band to a twelve-master aggregate and
concluded no cure was measurable. That was MEASURED FALSE.**

**So: use a WITHIN-SERIES PAIRED design.** Measure before and after in the same
series, on the same machine state, and the resolvable effect is percent-level
rather than 24 s. **A 3 s cure is measurable that way and was not the other
way.**

## WHAT YOU MUST NOT DO

- **Do not edit any master** until you have reported. Diagnose first.
- **Do not delete a line to improve a ratio.** P-q measured 315 lines removed
  buying 11.8 s.
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-204/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** A sibling
  may hold the other slot. **Report the load beside every absolute figure.**
- **Create your report file in your FIRST five minutes (C-22).** A sibling died
  on 2026-08-14 having written nothing.
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words**, and mark my hypothesis above
**CONFIRMED or REFUTED**.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Here DD4 is a diagnostic question: if the rise is interface reading, does it
scale with SHARED machinery or with wing-local content?** A cost that grows with
shared code is paid by both towers and is worth curing once; a wing-local cost
is not. **Say which.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-201/LJ-1.201-report.md`**, read WHOLE. **It found this
  term and it names what it ruled out. Its section 8.5 also holds the narrower
  admissible form of a law this project nearly admitted too broadly.**
- **`agents/tasks/LJ-1-185/runs/`**, the tracked raw profiles. **Read the files,
  not the report about them.**
- `agents/tasks/LJ-1-155/runs/src_L_Condensation.int1.txt`: the earlier
  measurement, where `Deserialization` is 1,689 ms.
- `agents/tasks/LJ-1-145/lj-1.145-report.md`: the profiling method that worked.
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs interface serialization. Say so in one
line.**

## SCOPE (read)

`agents/tasks/LJ-1-185/runs/` FIRST, the raw files themselves.

## SCOPE (write)

`agents/tasks/LJ-1-204/` only. **No master until you report.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for probe` and read every statement.

- **P-t.** An average hides the term.
- **P-l.** A cure measured at one site is a hypothesis at another.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-s, P-q, P-m, P-y, C-12, C-22, C-36, C-39, C-40. DD0, DD8, DD24, D-1,
  D-10, D-26, D-29, D-30. I-5.**

## CONSTRAINTS

- Count with `python3 scripts/ledger.py`. Verify a per-module figure with
  `python3 scripts/check-ratio.py --module <file> --runs N`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the cause and whether it is curable, and with `Deserialization`'s
value TODAY against 1,689 and 10,000.** Then the paired measurement with its
within-series spread. Then the cure and its price, or why there is none. Then
SHARED or WING-LOCAL. **Mark every negative MEASURED or INFERRED, and mark my
interface-size hypothesis CONFIRMED or REFUTED.**
