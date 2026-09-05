# LJ-1.210: is the chapter really 17 lines? The class-parameter probe

tier: opus (in-harness-subagent-mode), **selected by the CLOCK.** Beijing time
is inside the 14:00 to 18:00 peak window, so the in-harness Opus leads. **This
task runs Agda and the in-harness path does NOT pass through `dispatch.py`, so
C-12's slot accounting cannot see it: hold ONE process and say so.**

## GOAL

**`[LJ-1.196]` said the residue of `[LJ-1.7]` is 84 free lines PLUS A CHAPTER.
`[LJ-1.200]` UPHELD the verdict and REFUTED that word.**

**MEASURED by `[LJ-1.200]`:** `src/L/Coding/Model.lagda.md` names `isL` on **6
of 1,288 lines** and names `Lset` and `𝒟ₒ` on **zero**;
`src/L/Coding/Powerset.lagda.md` names `isL` on **11 of 395**. The mathematical
uses are only `isL-trans`, the hProp field, numerals and `𝒟ₒ→isL`, **which are
exactly `[LJ-1.184]`'s three closure facts, and it measured them as `tt*` at the
ambient class.**

**So `[LJ-1.200]` says 1,288 plus 395 prices a RE-DERIVATION, while the
class-parameter generalization those files actually need has a surface it
measures at 17 LINES.** **It gave no figure for the port, citing P-l.**

**Measure it. Parameterize `L.Coding.Model` and `L.Coding.Powerset` on a class
`M`, instantiate at `isL` and at `Full`, and report what it costs.**

## WHY THIS IS THE BIGGEST SWING LEFT IN THE PHASE

**If the surface is 17 lines, `[LJ-1.7]`'s residue is NOT a chapter and the word
that reached the live status screen was an unmeasured consequent, as
`[LJ-1.200]` says.**

**If it is not, the chapter stands and it is priced for the first time.**

**Both answers close a question that has been open since `[LJ-1.196]`.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE SURFACE IS SMALL.** Report the actual line count of the parameterization
  and both instantiations, with the seconds. **Then `[LJ-1.7]`'s residue is
  priced and the chapter dissolves.** STOP.
- **THE SURFACE IS LARGE.** Say what it is and where the cost sits. **That
  prices the chapter and it is a complete answer.**
- **IT WILL NOT PARAMETERIZE.** If a name resists abstraction, **name it at
  `file:line` and stop.** C-36: write the term you could not write.
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt it, report the elapsed seconds, and bisect. On 2026-08-14 one run
  reached 4 hours 15 minutes because its brief gave a heap cap and no clock cap.

## THE TRAP `[LJ-1.200]` NAMED, and it is why the first attempt went wrong

**`abs₀` WANTS its witness at the class carrier and its conclusion IS the
ambient reading.** `[LJ-1.196]` read it backwards and concluded that lifting is
the chapter.

**And the 84 lines never ported through `abs₀` at all**: `extAt-out`,
`extAt-in` and `extAt-in-both` are projections, blind to the carrier
(`src/L/Coding/Model.lagda.md:669`, `:673`, `:678`). **So the port's price is
set by what `DefAt-out`'s PROOF consumes, not by what `abs₀`'s TYPE demands.**

**Start from that correction, not from `[LJ-1.196]`'s framing.**

## WHAT YOU MUST NOT DO

- **Do not edit any master** until you report. This is a probe.
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-210/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Two
  siblings may hold Agda. **Report the load beside every absolute figure,
  discard a warm-up, and take at least three kept runs for any figure a decision
  rests on.**
- **Report a heap exhaustion as a wall.** Never raise the cap.
- Never `src/Everything.lagda.md`.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.
- **Create your report file in your FIRST five minutes (C-22).** An agent died
  on 2026-08-14 having written nothing, and its reasoning had to be salvaged
  from its terminal.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**This task IS a DD4 probe.** The whole question is whether content written
fixed to one class can be written generic in the class and instantiated twice.
**`[LJ-1.184]` measured six extra lines buying the second tower for a 167-line
module. Give the same figure here: how much re-instantiates for J.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-200/LJ-1.200-report.md`**, read WHOLE. **The counts, the
  `abs₀` correction, and the 17-line claim you are measuring.**
- `agents/tasks/LJ-1-196/lj-1.196-report.md` and `agents/tasks/LJ-1-184/`: the
  NO-GO and the supply before it.
- `src/L/Coding/Model.lagda.md` and `Powerset.lagda.md`: **the files you are
  parameterizing. Read where `isL` actually appears.**
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim**, and say what would NOT transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md`. **`[LJ-1.200]` measured that Devlin's matrix is
`Σ₀` at `:93-94` while the description is `Σ₁`. Say whether his construction is
class-generic.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-200/LJ-1.200-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-210/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-l.** A measured result elsewhere is a hypothesis here.
- **D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-36, C-37, C-39, C-40.
  I-5. DD0, DD8.**

## CONSTRAINTS

- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line` or a command and its output. Write ASD-STE100.

## RETURN

**Lead with the surface in LINES, against `[LJ-1.200]`'s 17, and with whether
the chapter dissolves.** Then both instantiations and their seconds with load and
run count. Then anything that resisted abstraction, at `file:line`. Then the DD4
re-instantiation figure. **Mark every negative MEASURED or INFERRED.**
