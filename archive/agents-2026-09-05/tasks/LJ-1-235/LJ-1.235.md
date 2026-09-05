# LJ-1.235: strengthen the conclusion `hasReplacementL` already computes and throws away

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.233]` OVERTURNED `[LJ-1.230]`'s NO-GO and left `[LJ-1.7]` with ONE
genuinely absent thing.** Two of three walls fell to delivered machinery. **The
third is not a theorem to invent. It is a conclusion to strengthen.**

**MEASURED, and I re-derived it:** `src/L/Axioms/Full.lagda.md:231` reads

```
img∈βimg : (p : Mem) → ⟨ fst (img p) ∈ Lset βimg ⟩
```

**`hasReplacementL`'s own proof COMPUTES a bounding stage and then DISCARDS
it.** **The caller gets the replacement set and never learns where the image
landed.**

**That is the whole of wall (c). Strengthen the conclusion so the bound comes
out.**

## STEP ZERO, and it costs about 37 seconds

**`[LJ-1.233]`'s verdict rests on a 2026-08-13 measurement rather than a live
green, and it said so plainly.** **Run `agents/tasks/LJ-1-124/ProbeLJ1124A.agda`
first, under the cap, and report exit code and elapsed seconds BEFORE anything
else.**

**`[LJ-1.233]` measured that the API names it imports are unchanged, but the
typecheck is NOT re-measured.** **If it is red, say so and STOP: the whole
overturn rests on it and a red there is worth more than everything below.**

## THE TERM TO WRITE (C-36)

**A lemma pinning where `hierL b`'s replacement image lands**, so that `succλ`
climbs it into `Lset lam`. **`[LJ-1.230]` named two candidate shapes and either
would serve:**

- `hierL b ∈ Lset (sucV (sucV b))`, or
- the rank bound `rank (hierL b) ∈ sucV (sucV b)`.

**`[LJ-1.233]` measured that placing `hierL b` in SOME stage is already free via
`stage-mem`. What is absent is placing it in a stage BOUNDED BY `b`.**

**So the question is not existence. It is whether `hasReplacementL`'s internal
`βimg` can be exposed with a bound stated in terms of the input.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE BOUND COMES OUT.** Report the written lines and the seconds. **Then
  wall (c) falls, `[LJ-1.7]`'s residue is the six ambient readings plus an
  assembly, and I sequence both.** STOP.
- **THE BOUND COMES OUT BUT NOT IN TERMS OF `b`.** **Say what it IS in terms
  of.** A bound in the wrong variable is a different lemma and it may still
  serve; say whether `succλ` can climb it.
- **STRENGTHENING BREAKS A CONSUMER.** `hasReplacementL` has consumers.
  **If a stronger conclusion costs them, name them at `file:line` and price the
  change** (C-40: verify the CONSUMERS, never the master alone). **A new
  sibling lemma beside the old one is a legitimate answer and may be the
  cheaper one.**
- **THE INTERNAL BOUND IS NOT IN TERMS OF THE INPUT AT ALL.** If `βimg` is
  built from something the caller cannot see, **name it and stop.** **That is a
  real wall and it is the phase's blocker stated exactly.**
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Every cut gets the SAME
  bound as its green control, and the control's elapsed time is reported BEFORE
  any cut is interpreted** (`[LJ-1.215]`'s law). **Your control is step zero's
  37 s.**

## WHAT IS DELIVERED, so you assemble rather than invent

| object | at |
|---|---|
| `hasReplacementL` and its internal `βimg` | `src/L/Axioms/Full.lagda.md:231` and around it |
| `hierL`, built by replacement | `src/L/Hierarchy.lagda.md:621-622` |
| `stage-mem`, which places a set in SOME stage | find it; `[LJ-1.233]` names it |
| the level closure `isL-Lset`, `Lset-suc`, `Lset-mono` | `src/L/Axioms/Basic.lagda.md:154-157`, `:196`, `src/L/Constructible.lagda.md:355` |
| the limit hypothesis `succλ`, ALREADY in the site telescope | `src/L/BoundedSubset.lagda.md:904`, restated `:1394` |
| the bounded decode, GREEN since 2026-08-13 | `agents/tasks/LJ-1-124/ProbeLJ1124A.agda:199-209` |

## WHAT YOU MUST NOT DO

- **Do not re-litigate walls (a) and (b).** `[LJ-1.233]` measured both closed
  or bypassable. **Wall (c) is yours.**
- **Do not build `sl` or `sc`.** You supply the missing INGREDIENT.
- **Do not edit any master.** This is a probe. **Nothing lands in `src/`, and a
  probe under `src/` is forbidden by I-5.**
- **Do not touch `agents/tasks/LJ-1-236/`.** A sibling is live there.
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-235/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **A sibling
  holds the other Agda slot.** **Report the load beside every absolute figure**,
  discard a warm-up, and take at least three kept runs for any figure a decision
  rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap. **`[LJ-1.234]`
  met one today and it was R-34's unpinned `InfinitySet` level meta, cured by
  `module IS = InfinitySet {ℓ}`. Check that before you call a heap wall
  yours.**
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## CITE THE REPORT THAT MEASURED, NEVER THE ONE THAT QUOTED

**C-44 entered `dev/LESSONS.md` today with my own session as its
measurement.** **A brief's claim that something was never done is the one claim
an agent cannot check.** **If this brief asserts anything you cannot find, say
so in your report and treat it as unproven.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`hasReplacementL` is L's axiom instance, so a strengthened conclusion is
per-tower BY ITS NAME.** **But the SHAPE, that a replacement image has a stage
bound computable from the input, is tower-neutral mathematics.** **Say whether
what you write could be stated once over a structure parameter and instantiated
twice**, because `[LJ-1.228]` measured that `sl` and `sc` are ONE per-tower
object and the J tower will need its own.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-233/lj-1.233-report.md`**, read WHOLE. **It is your
  brief within this brief:** the three walls re-judged, the `liftFo` and
  `satBridge` route, and the wall (c) analysis.
- **`agents/tasks/LJ-1-230/lj-1.230-report.md`**: the two candidate shapes and
  the C-36 naming.
- **`agents/tasks/LJ-1-124/lj-1.124-report.md` and `ProbeLJ1124A.agda`**: the
  GO at 147 lines. **This is step zero.**
- `agents/tasks/LJ-1-228/lj-1.228-report.md`: the delivered-component map and
  the floor.
- **`src/L/Axioms/Full.lagda.md`, `src/L/Hierarchy.lagda.md:594-656`: read the
  source, never a report about it.**
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **The retired route also needed replacement images placed in the tower. Take
  SHAPE from the archive, never a claim**, and say what would NOT transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:374` is the C1 row.** **Say whether Devlin's
proof needs a rank bound on a replacement image at this point, or whether his
presentation gets it from the construction.** Return a **LITERATURE USED**
section.

## SCOPE (read)

`agents/tasks/LJ-1-233/lj-1.233-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-235/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed above.
- **C-40.** **Verify the CONSUMERS of a changed conclusion, never the master
  alone. This is the rule most likely to bite here.**
- **C-36.** Write the term you could not write.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-44.** A brief's claim that something was never done is unchecked until
  you check it.
- **P-l.** 147 lines and 37 s are comparables and NOT your price.
- **C-42.** A refutation measures the site it names, never its extent.
- **I-5, R-34. P-i, P-k, P-m, P-t, P-y, R-40. C-12, C-22, C-39. DD0, DD8,
  DD24, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with step zero's exit code and elapsed seconds, THEN the wall (c)
verdict.** Then the lemma you wrote, its written lines and its statement. Then
whether the bound is in terms of `b`. Then any consumer the strengthening
costs, at `file:line`. Then the seconds with load and run count. **Mark every
negative MEASURED or INFERRED.**
