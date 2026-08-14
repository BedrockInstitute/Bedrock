# LJ-1.230: the stage-carrier decode, the probe nobody has run since `[LJ-1.123]` named it

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.** **Queued: both Agda
slots were held when I wrote this.**

## GOAL

**`[LJ-1.228]` settled phase 1's largest uncertainty and then named the one
probe that turns its band into a price.**

**The record contradicted itself by 200 to 1 and BOTH figures were right about
something else:**

| record | figure | what it actually priced |
|---|---:|---|
| `[LJ-1.121]` | 2.8k to 3.3k | **the HULL route**, which `[LJ-1.160]` BYPASSED. It prices a route nobody uses |
| `[LJ-1.160]` | 16 | **the ASSEMBLY** of `levelIn` and `cover` from one crossing face. Its own report says the three face facts stay open |
| `[LJ-1.178]` | the live one | **the debt MOVED to the STAGE**, and `sl`/`sc` are where it landed |

**`[LJ-1.228]` prices `sl` at about 0.15k and `sc` at about 0.15k, joint about
0.25k to 0.35k because both share ONE object. All three figures are INFERRED,
and the basis is `[LJ-1.123]`'s band, which P-l calls a hypothesis at another
carrier.**

**Run the probe. `[LJ-1.123]` named it, sized it at 150 to 250 probe lines, and
NOBODY HAS RUN IT.**

## THE PROBE, in `[LJ-1.228]`'s own words

**「the stage-carrier version: write the decode at the stage with the bound and
the internal hierarchy placed in `Lset lam`.」**

**The two-way decode of the bounded level-hood `graphBndAt`, at the STAGE
carrier rather than the class carrier.**

## WHAT IS DELIVERED, so you assemble rather than invent

| object | at |
|---|---|
| the level-hood formula and its Σ₁ certificate | `src/L/BoundedSubset.lagda.md:74-146` |
| `graphBndAt` and `Δ₀-graphBndAt` | `src/L/BoundedSubset.lagda.md:111`, `:115` |
| the two-variable level-hood at arity zero, `Σ₂`, `Σ₁-Σ₂`, `reverse` | `src/L/BoundedSubset.lagda.md:840-869` |
| the class-carrier read-off, BOTH directions | `src/L/Hierarchy.lagda.md:334` (`Lset-only`), `:646` (`Lset-defines`) |
| the level closure | `src/L/Axioms/Basic.lagda.md:154-157` (`isL-Lset`), `:196` (`Lset-suc`), `src/L/Constructible.lagda.md:355` (`Lset-mono`) |
| the stage ordinal facts | `src/L/Ordinal/Stages.lagda.md:434`, `:265`, `:164` |
| absoluteness | `src/FOL/Absoluteness.lagda.md:122` (`abs₀`), `:182` (`σ₁-up`) |
| **the limit hypothesis `succλ`, ALREADY IN THE SITE TELESCOPE** | `src/L/BoundedSubset.lagda.md:904`, restated `:1394` |

**I re-derived the last row myself. `succλ` is there and `sc` needs it.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1) and taken from `[LJ-1.228]`

- **GO.** The delivered class-carrier decode plus `isL-Lset`, `Lset-suc` and
  `succλ` close the stage decode **at or below 150 lines**. Report the written
  lines and the seconds. **Then `sl` and `sc` have a PRICE rather than a band,
  and `[LJ-1.7]` becomes fundable for the first time.** STOP.
- **GO, BUT DEARER.** Over 150 lines. **Report both figures.** That re-prices
  `[LJ-1.228]`'s 0.25k to 0.35k and it is a complete answer.
- **NO-GO: THE PLACEMENT NEEDS NEW MACHINERY.** If placing the bound into the
  stage needs something the tree does not have, **NAME IT** (C-36). **That name
  is the phase's real blocker and it is worth more than any number here.**
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Every cut gets the SAME bound
  as its green control, and the control's elapsed time is reported BEFORE any
  cut is interpreted** (`[LJ-1.215]`'s law).

## WHAT YOU MUST NOT DO

- **Do not build `sl` or `sc` themselves.** **This probe measures the OBJECT
  THEY SHARE.** `[LJ-1.228]` measured that both consume one stage-carrier
  level-hood instantiation. **Measure that object.**
- **Do not re-open the hull route.** `[LJ-1.160]` bypassed it and
  `[LJ-1.121]`'s 2.8k to 3.3k prices it. **That route is not yours.**
- **Do not re-price `levelIn` and `cover`.** `[LJ-1.178]` BUILT them.
- **Do not edit any master.** This is a probe. **Nothing lands in `src/`, and a
  probe under `src/` is forbidden by I-5.** I moved three strays out of `src/`
  today; do not put one back.
- **Do not touch `agents/tasks/LJ-1-226/` or `LJ-1-229/`.** Two siblings are
  live there.
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-230/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure**, discard a warm-up, and take at least
  three kept runs for any figure a decision rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE TRUTH IS ALREADY CHECKED, so do not re-check it

**`[LJ-1.228]` applied D-10 and found no obstruction.** `sl` holds for EVERY
stage. **`sc` holds exactly at LIMIT stages and fails at a successor**, because
`Lset β ∈ Lset (sucV β)` and no earlier level holds it. **The site already
carries `succλ`, so `sc` is not false at the site.**

**One half of that is INFERRED and you may meet it:** the no-earlier-level half
was not typechecked. **If your work touches it, say what you found.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **This task exists to convert a band
into a number. Do not hand back another band.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.228]` MEASURED that `sl` and `sc` are ONE object and not two: the
level-hood certificate's stage instantiation.** **`dev/literature/devlin-II5.md:374`
classes that row PER-TOWER and `:387-389` says the per-tower content is exactly
two objects for all of II.5.**

**So this object is per-tower BY DEVLIN'S OWN TABLE, and the J tower will need
its own.** **Write it so the J tower's version is a re-instantiation and not a
re-derivation.** **Say what its structure parameter would be**, because
`[LJ-1.210]` measured that retrofitting one costs 42 lines on a 1,288-line
module and writing one at the start costs nothing.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-228/lj-1.228-report.md`**, read WHOLE. **It is your brief
  within this brief:** the delivered-component map in section 1.1, the band
  mapping in section 3, and the falsity check in section 4.
- **`agents/tasks/LJ-1-123/`**: the four bands, the 0.6k re-price, and section 3
  where this probe was named and sized at 150 to 250 lines. **Read why nobody
  ran it.**
- **`agents/tasks/LJ-1-178/lj-1.178-report.md` and `ProbeLJ1178A.agda:360-361`,
  `:405-406`, `:486-493`**: the two hypotheses as stated, and section 7 where
  the debt moves to the stage.
- `agents/tasks/LJ-1-160/`: the 16-line assembly and its section 3.3, which says
  the three face facts stay OPEN.
- `agents/tasks/LJ-1-184/ProbeLJ1184A.agda:257`, `:355`: the ambient read-off in
  one direction.
- **`src/L/BoundedSubset.lagda.md`, `src/L/Hierarchy.lagda.md`,
  `src/L/Ordinal/Stages.lagda.md`: read the delivered objects, never a report
  about them.**
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **The retired route reached its own trophy and this is Devlin's clause (b),
  which any route must pay. Take SHAPE from the archive, never a claim**, and
  say what would NOT transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:374` is the C1 row, marked PER-TOWER, and
`:387-389` is the two-object verdict.** **`[LJ-1.228]` reads `sl` and `sc` as
Devlin's clause (b), the LOCALIZED form rather than the hull transfer. Say
whether the text supports that reading**, and whether Devlin proves clause (b)
or assumes it. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-228/lj-1.228-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-230/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed above.
- **DD8.** One estimate, and it names its basis.
- **P-l.** `[LJ-1.123]`'s class-carrier band is a comparable and NOT your price.
  **This task is P-l's test case: the whole question is whether a class-carrier
  figure survives the move to the stage carrier.**
- **D-10.** The truth is checked; do not re-check it.
- **C-36.** Write the term you could not write.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-42.** A refutation measures the site it names, never its extent.
- **I-5.** No probe under `src/`.
- **P-i, P-k, P-m, P-t, P-y, R-40. C-12, C-22, C-39, C-40. DD0, DD24, D-26,
  D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with GO or NO-GO and ONE number: the stage decode's written lines
against the 150-line gate.** Then what the delivered class-carrier decode gave
you and what you had to write. Then whether the bound placed into `Lset lam`
without new machinery. Then the seconds with load and run count. Then the
structure parameter the J tower would need. **Mark every negative MEASURED or
INFERRED.**
