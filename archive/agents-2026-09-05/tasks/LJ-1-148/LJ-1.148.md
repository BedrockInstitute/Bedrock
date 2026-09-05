# LJ-1.148: DD24's tolerance is narrower than the machine's own swing

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**A verdict this project now acts on is inside its instrument's noise. Measure
the noise, and say what a trustworthy verdict costs.**

**This is a MEASUREMENT and TOOLING task. It does not touch mathematics and it
does not change DD24. The threshold is the owner's.**

## THE FINDING, and it is four measurements of one phenomenon, all today

| what | drift | source |
|---|---|---|
| identical tree, different day, whole build | **11.2 percent** | `[LJ-1.128]` |
| identical tree, control run in a worktree | **6.9 percent** | `[LJ-1.135]` |
| identical three masters, same instrument, morning against evening | **20.1 percent** | the orchestrator, verified below |
| `Condensation.lagda.md`, two runs hours apart | 122.64 s and 120.61 s | `[LJ-1.145]`, `[LJ-1.144]` |

**The third is the one to check first, because I found it and I could be
wrong.** `[LJ-1.135]` measured `TwelveAgree`, `UpperAgree` and `LowerAgree` at
30.68, 23.82 and 12.81 s, total **67.31 s**, at dispatch-time load 9.27. I ran
the same tool at load 4.89 and got 25.32, 19.38 and 11.36, total **56.06 s**.
**Both used `check-ratio.py --module` at the ledger's own `GHCRTS`.**
`[LJ-1.144]` read the same gap as a CALIBER difference and pointed at the
recorded 22.3 percent cost of a missing `-A64m -I0`. **I judged that wrong,
because the flags were identical. Verify which of us is right; that is your
first task.**

**DD24's tolerance is 1.15x.** `scripts/check-ratio.py` prints `bar 0.0136`
from a baseline of 0.011828.

**So a wing module can be judged OVER or UNDER by the machine.** From today's
run: `StageArith` at 0.91x of the bar and `BoundedSubset` at 0.83x both flip
red under a 20 percent upward swing, while the OVER verdicts hold at 1.4x to
6.9x.

## WHAT TO DO

1. **Settle the caliber question.** Read `check-ratio.py` and prove, from the
   code, which `GHCRTS` each path uses. **MEASURED, from the source, not from
   either of our readings.**
2. **Measure the noise properly.** Take ONE small master and run it N times
   cold. Report the spread, and say what N you needed for the mean to settle.
   **`[LJ-1.135]` used four runs and got 5.5 percent on a large set; a single
   module may be far noisier. That is the number nobody has.**
3. **Then answer the question that matters:** how many runs does a per-module
   verdict need before it means something? **Give a number with its basis.**
4. **Then make the tool say what it knows.** Options, and you choose with a
   reason:
   - **Report the run count and the spread beside every verdict**, so a reader
     can see whether a figure is inside the noise. Cheapest, and it changes no
     rule.
   - **Refuse a verdict within the noise band**, printing NOISE rather than
     OVER or UNDER.
   - **Require N runs for a verdict**, and say what that costs in wall time.

   **I lean toward the first: a tool that reports its own uncertainty is honest
   and changes nothing the owner has not ruled. Overrule me with a reason.**

## WHAT YOU MUST NOT DO

- **Do not change DD24's threshold or its tolerance.** That is the owner's and
  is deferred until the phase's content is complete. **You measure; you do not
  rule.**
- **Do not touch anything under `src/`.**
- **Do not re-measure the baseline.** `ac_baseline_module_rate = 0.011828` was
  set today over the 73 cone masters and it stands.
- **A probe goes in `agents/tasks/LJ-1-148/`**, never in `src/`, tracked, never
  deleted. **Read `AGENTS.md` and `dev/LESSONS.md` D-1 fresh; both changed
  today.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Two
  siblings may be running Agda and one of them is measuring seconds.**
  **Coordinate: if the machine is busy, say so and STOP rather than publish a
  number taken in a storm.** An honest refusal is a full deliverable here, and
  it is the one this task is about.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE ABORT CRITERION

- **The noise is measured and the tool reports it**: report and STOP.
- **The machine is too busy to measure noise**: **STOP AND SAY SO**, with the
  loads you sampled. Do not wait indefinitely and do not measure anyway.
- **The caliber question turns out to be the real cause**: that changes the
  whole finding. Report it and stop.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **My 20.1 percent reading is
INFERRED from two runs I did not control. Treat it as a hypothesis.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-135/lj-1.135-report.md`**, read WHOLE. Its control-run
  method is the model, and its own protocol section says how to report a spread.
- **`agents/tasks/archive/LJ-1-128/`**, read WHOLE: the 11.2 percent control.
- `agents/tasks/LJ-1-144/lj-1.144-report.md`, the caliber claim.
- **`dev/LESSONS.md` P-s, P-t, P-q, P-m, C-28, C-32, C-12**, read WHOLE. **C-28
  is a threshold outliving its tree and it is the family this belongs to.**
- `dev/PLAN.md` DD24 and `dev/ledger.toml`'s `[ratio]` block, read whole.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs measurement noise. Say so in one line.**

## SCOPE (read)

`scripts/check-ratio.py` FIRST, whole. Then `dev/ledger.toml`'s `[ratio]`
block.

## SCOPE (write)

`scripts/check-ratio.py`, `scripts/tests/`, `dev/ledger.toml` comments only.
Your report and probes are `agents/tasks/LJ-1-148/`.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for rewrite` and read every statement.

- **C-28, C-32.** A threshold outliving its tree, and its family.
- **P-s, P-t, P-q, P-m.** Rate, class, and why an average hides the term.
- **C-12.** ONE agda process. **A task that measures check time gets a quiet
  machine, and this task IS that task.**
- **P-l, DD8, C-22, C-36, C-39, C-40.**
- **C-31, C-32, C-33, C-34, C-37, D-10, D-26, D-29.**

## CONSTRAINTS

- **Add a test for any rule you change**, and run the FULL `scripts/tests/`
  suite.
- Run `scripts/lint-prose.py --check` on everything you write.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the caliber verdict: same instrument or not, from the code.** Then
the measured noise for one module, the run count you needed, and every load you
sampled. Then how many runs a verdict needs. Then what you changed in the tool
and its honest limit. **Mark every negative MEASURED or INFERRED.**
