# LJ-1.217: re-price A6 from the green interface, with a clock cap this time

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.215]`, an adversarial review, ruled that A6 is UNPRICED and NOT
WALLED, and it priced the difference to my brief.**

**What `[LJ-1.198]` reported:** A6's charge is a wall, one typecheck ran 3.06
hours and did not finish, and the seven cells do not sum.

**What `[LJ-1.215]` MEASURED about that report:**

1. **Its bisection's bounds SHRANK as it narrowed**: 480 s for the wide cuts,
   300 s for the green control, **180 s for the decisive cut**. **And the green
   control's own elapsed time is nowhere in the report**, so 「the decisive cut
   exceeds 180 s」 cannot be interpreted.
2. **A sixth probe ran and was dropped from every table.**
3. **`_build` holds only TWO interfaces**, for probes A and E. **Everything else
   failed to complete**, and the report never cites that record.
4. **My brief gave a heap cap and NO clock cap**, which the review priced at 53
   percent of a 5h50m dispatch.

**So re-price it. The answer is a NUMBER, and the run that produced a wall was
my brief's fault rather than A6's.**

## START FROM THE GREEN INTERFACE, NOT FROM SCRATCH

**`ProbeLJ1198E.agda` completed and its interface is in `_build`.**
`[LJ-1.215]` says a re-price starts there. **Read `agents/tasks/LJ-1-198/` whole
and reuse every probe that completed.**

## THE FIXED-SHAPE FINDING, which is the likely cure

**`[LJ-1.215]` measured DD4's own signature on this wall:** the obstruction is
`pair-out` returning a FIBRE, while **`[LJ-1.176]`'s equivalent returned the
equality DIRECTLY and cost 1.72 s.** `[LJ-1.198]` identifies that difference at
its `:149-153` and files the alternative as future work at `:223-224`.

**A NO-GO on a fixed shape is not a NO-GO.** **Try the direct-equality shape
first.**

## THE FIGURE TO STRIKE

**`[LJ-1.198]`'s 「at least 6,400 to 1」 ratio is void**: a non-completion has no
duration. **Do not carry it forward.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **PRICED.** A6 becomes ONE number with its basis named, and you say whether
  the seven cells now sum. STOP.
- **THE DIRECT SHAPE WORKS.** Then the wall was fixed-shape and you report both
  prices, the fibre form and the direct form.
- **A REAL WALL SURVIVES THE CLOCK CAP.** If a cut still will not finish in 30
  minutes, **name the term and stop.** That is a wall with evidence, unlike the
  last one.
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt it, report the ELAPSED SECONDS, and bisect. **Every cut gets the
  SAME bound as its green control, and you report the control's elapsed time
  BEFORE interpreting any cut.** That is `[LJ-1.215]`'s proposed law and this
  brief applies it.

## WHAT YOU MUST NOT DO

- **Do not edit any master.** This is a probe.
- **Do not re-run what completed.** `[LJ-1.198]`'s probes A and E are green;
  reuse them.
- **Do not touch `src/L/Condensation*`** if a sibling is building there, and
  **do not touch `src/L/Choice/Name.lagda.md`** (DD23).
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** A sibling
  holds the other slot. **Report the load beside every absolute figure.**
- **Report a heap exhaustion as a wall.** Never raise the cap.
- **A probe goes in `agents/tasks/LJ-1-217/`**, tracked, never deleted.
- **Create your report file in your FIRST five minutes (C-22).** An agent died
  on 2026-08-14 having written nothing.
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE INSTRUMENT

**`check-ratio.py`'s ±12.8 percent is a ONE-MODULE BETWEEN-SERIES figure by its
own words at `:72-76`; within-series spread is 0.5 to 4.0 percent.** **Use a
within-series paired design for any seconds figure**, and reverse the order in a
second series to cancel drift, as `[LJ-1.209]` and `[LJ-1.214]` both did.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.176]` measured genericity costing ONE line at this cluster, 78 against
77, with 81 percent re-instantiating for J.** **Give the same figure**, and say
whether the direct-equality shape is more or less generic than the fibre one.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-215/lj-1.215-report.md`**, read WHOLE. **The four defects
  and the fixed-shape finding are your brief within this brief.**
- **`agents/tasks/LJ-1-198/`** in full, including `ProbeLJ1198E.agda` and the
  dropped `ProbeLJ1198F.agda`.
- **`agents/tasks/LJ-1-176/`**: A5 priced at 547 with ONE `hasSeparationL` and
  the carve device that worked.
- `agents/tasks/LJ-1-152/`: one separation under 0.1 s against one replacement
  at 259 to 269.
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim**, and say what would NOT transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md`, `devlin-errata.md`. **`[LJ-1.154]` MEASURED
that Devlin's base theory has NO replacement. Say whether he builds A6's two
objects or assumes them.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-215/lj-1.215-report.md` FIRST, then `agents/tasks/LJ-1-198/`.

## SCOPE (write)

`agents/tasks/LJ-1-217/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe`.

- **D-1.** The abort criterion fixed BEFORE the run.
- **P-l.** A cure or a price measured elsewhere is a hypothesis here.
- **C-42.** A refutation measures the site it names, never its extent.
- **C-36, P-t, P-q, P-m, C-12, C-22, C-39, C-40. DD0, DD8, DD24, D-10, D-26,
  D-29, D-30. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with A6's price as ONE number with its basis, and whether the seven
cells sum.** Then the fibre shape against the direct shape, both priced. Then
every cut with its bound AND its control's elapsed time. Then what `[LJ-1.8]`
still needs. **Mark every negative MEASURED or INFERRED.**
