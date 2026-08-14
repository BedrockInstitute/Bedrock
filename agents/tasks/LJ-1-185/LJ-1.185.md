# LJ-1.185: the 16 seconds billed outside every definition

tier: opus (override; the head for every case is in `scripts/dispatch_policy.py`,
which is the only place the tables live)

## GOAL

**`[LJ-1.177]` measured that the GCH wing's ONLY remaining lever is about 16
seconds of `[LJ-1.155]`'s 21,268 ms profile that is billed OUTSIDE every
definition**, which it identifies as module-application instantiation, and it
marked that **UNMEASURED**.

**Measure it. Then say whether it can be cured, and at what price.**

## WHY THIS IS THE LAST LEVER, and it is measured rather than assumed

| finding | source |
|---|---|
| the `*Agree` telescope term is SPENT: it was cured and returned 42.72 s | `[LJ-1.158]`, commit `99498e3` |
| the `L/Condensation` telescope cure is CAPPED at about **5.2 s**, because it collapses `DeadCode` and `DeadCode` is 4.4 percent of that master | `[LJ-1.177]`, from `[LJ-1.155]:127`'s own profile |
| a `[LJ-1.147]`-class seal is SHARED and refuted as a route: it made every master faster and the ratio WORSE | `[LJ-1.147]` |
| the wing sits about **44 s** above the bar, and 40.27 against 48.70 is ONE wing measured twice, inside the band | `[LJ-1.177]` |
| **a cure under about 21 s cannot be shown to have worked by one pair of runs** | `[LJ-1.177]` |

**That last row is your design constraint, not a caution.** A 5.2 s cure is a
quarter of what the instrument can resolve. **So this 16 s is the only candidate
whose cure could be MEASURED at all.**

## WHAT TO DO

1. **Profile `src/L/Condensation.lagda.md`** with `--profile=internal` and
   `--profile=definitions`, as `[LJ-1.145]` did, and **account for the seconds
   that no definition owns.**
2. **Say what that time IS**, with evidence. `[LJ-1.177]` says module-application
   instantiation and marks it INFERRED. **Confirm or refute it.**
3. **If it is real and curable, price the cure** in lines and seconds, and say
   **SHARED or WING-LOCAL**. That column decides whether the cure helps at all:
   a shared cure speeds the AC side too.
4. **Do not apply a cure. Report first.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IDENTIFIED AND CURABLE.** You account for the seconds and price a cure
  OUTSIDE the instrument's band. Report both. STOP.
- **IDENTIFIED AND NOT CURABLE.** **Say so plainly with the accounting.** That
  would mean the wing is intrinsically this expensive, and it is a complete
  answer the owner needs.
- **THE 16 s IS NOT WHAT `[LJ-1.177]` THINKS.** Refute it and say what the time
  actually is. **A refutation here is worth more than a cure.**
- **SHARED, NOT WING-LOCAL.** **STOP before applying anything** and estimate what
  it does to the baseline.

## WHAT YOU MUST NOT DO

- **A SIBLING'S FILE MAY BE RED WHILE YOU WORK.** `[LJ-1.178]` lost about
  fifteen minutes to exactly that and said a brief line would have cost nothing.
  **This is that line: expect a dirty tree, BUILD GENERIC FIRST so you do not
  depend on a sibling's import path, and read committed state where it matters.**
- **Do not edit any master.** This is a probe. A build lands only after you
  report the measurement to me.
- **A probe goes in `agents/tasks/LJ-1-185/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Siblings
  are running. **Report the load beside every absolute figure, discard a
  warm-up, and take at least three kept runs for any figure a decision rests
  on.**
- **Report a heap exhaustion as a wall.** Never raise the cap.
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE BAR

**DD24 unchanged, and nothing tightens it.** The owner ruled 2026-08-14 that
DD24 is the whole rule and the readings layered on it were the orchestrator's
own. **The GCH bar was FIXED when the AC trophy landed and does not drift; every
GCH module uses that one number; and INTERMEDIATE DEBT IS ALLOWED**, because
only the whole GCH side, at the end, is judged.

**Report your lines and seconds as measured. Record an overage plainly (DD8).
Never delete a line to improve a ratio**; P-q measured 315 lines removed buying
11.8 s.

## THE INSTRUMENT

**`check-ratio.py` prints `noise band: at least +-12.8%, MEASURED [LJ-1.148]`.**
`[LJ-1.173]` spent most of a leg discovering its own +6 s was inside it, then
withdrew a +126 s extrapolation built on it. **A delta inside the band is not a
small measurement, it is no measurement.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **`[LJ-1.159]:263` measured generic at 8.4 times
CHEAPER than fixed at a neighbouring site**, and `[LJ-1.178]` wrote a 301-line
probe naming the tower eleven times with every one in a TYPE and no body
mentioning it. **Write yours the same way and say how much re-instantiates for
the J tower.** **A stop-line is NEVER a reason to write fixed.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-177/lj-1.177-report.md`**, read WHOLE. **It named this
  term and its census method needs no Agda.**
- **`agents/tasks/LJ-1-155/lj-1.155-report.md`**, read WHOLE, especially `:127`'s
  profile. **The 21,268 ms and the 4.4 percent both come from there.**
- **`agents/tasks/LJ-1-145/lj-1.145-report.md`** and its four probes: the method
  that worked, and P-x and P-w REFUTED at this site, MEASURED, not to be
  revisited.
- `agents/tasks/LJ-1-158/`: the telescope collapse that spent the last term.
- **`archive/dev/TASKS-archived.md`, `STATUS-archived.md`, and whatever in
  `archive/src/2026-08-09-rud-route/` they point at.** **Take SHAPE from the
  archive, never a claim**, and say what would NOT transfer. `[LJ-1.107]`
  rebuilt 82 delivered lines because nobody looked.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs elaboration cost. Say so in one line.**

## SCOPE (write)

`agents/tasks/LJ-1-185/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-36.** Write the term you could not write.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-l, P-k, P-m, P-t, P-y, C-12, C-39, C-40.**
- **DD0, DD8, DD24, D-1, D-10, D-26, D-29, D-30. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with what the 16 seconds ARE, with the accounting, and whether
`[LJ-1.177]`'s identification holds.** Then the cure and its price, or why there
is none. Then SHARED or WING-LOCAL. Then the wing's gap re-measured with run
counts. **Mark every negative MEASURED or INFERRED.**
