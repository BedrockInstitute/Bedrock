# LJ-1.241: build `φ₀` at arity two, and read the archive that two reports declined

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.240]` specified this probe and I am passing its specification through
unchanged.**

**Build `φ₀ : Formula (⊥*) 2` from `erase levelHoodB` plus the twelve numeral
definitions, and typecheck `φ₀ := ⊤̇` in the same file.**

**Two deliverables, and the second is small:**

1. **The real `φ₀` at arity two.** `erase` PRESERVES arity
   (`src/FOL/Count.lagda.md:598`), so this is the right instrument. **`absFo`
   is NOT: it raises arity by `countFo`, and `[LJ-1.240]` measured that it was
   the wrong instrument.**
2. **`φ₀ := ⊤̇` typechecked**, which converts `[LJ-1.240]`'s inhabitability
   finding from INFERRED to MEASURED.

## THE ARCHIVE IS PART OF THE TASK, NOT A FORMALITY

**`[LJ-1.237]` and `[LJ-1.239]` both recorded the archive as surveyed and NOT
bearing. Both said so plainly and BOTH WERE WRONG.**

**The retired route wrote the object everyone was looking for:**

| what | where |
|---|---|
| `levelStory : Formula (⊥* {ℓ}) 2`, an arity-two constant-free level story | `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:600-601` |
| its embeddings to both carriers, `σᴹ` and `σL` | `:768-769`, `:823-824` |
| `zeroForm`, constant-free | `:529-531` |
| `sucAt`, constant-free | `archive/src/2026-08-09-rud-route/L/LevelKit.lagda.md:567-571` |

**READ ALL FOUR SITES BEFORE YOU WRITE A LINE.** **I re-derived `levelStory`
and `LevelHood`'s zero consumers myself.**

**The archive gives the SHAPE and NEVER a discharge**, and `[LJ-1.240]` says so
against its own find: `Cl = ⊤̇` there (`:592-593`) and `CrossOut σᴹ` is never
applied. **So take the shape, price it here, and say what does NOT transfer.**

## WHAT IS TRUE ABOUT THE TREE, MEASURED, so you do not re-derive it

- **`levelHoodB : Formula CS.S (4 + n)`** at `src/L/BoundedSubset.lagda.md:108`.
  **The arity carries the twelve tag numerals as ENVIRONMENT SLOTS**, and
  `src/L/Condensation.lagda.md:1125` says so in the tree's own words: numerals
  are slots, so every formula is constant-free.
- **`LevelHood0` has ZERO consumers in `src/`.** A grep for `LevelHood`
  returns three lines and all three are definitions
  (`src/L/BoundedSubset.lagda.md:74`, `:840`, `:844`). **So the tree has never
  instantiated `LevelHood` at a correct `n`, and nothing you do here can break
  a delivered consumer.**
- **`sl` and `sc` are green over `φ₀` as a parameter and cost ZERO to keep**
  (`[LJ-1.240]`), because they touch `φ₀` only abstractly.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **`φ₀` BUILDS AT ARITY TWO.** Report the written lines and the seconds.
  **Then `lh`'s type has a real instance, the recipe's step 4 has its
  instrument, and I sequence the fifth step.** STOP.
- **`φ₀` BUILDS AND `⊤̇` TYPECHECKS.** **Report both.** The second is small and
  it converts an INFERRED finding to MEASURED.
- **`erase` DOES NOT CLOSE IT.** **Name the term** (C-36). **`[LJ-1.240]`
  measured that `erase` preserves arity; if it does not close this formula, say
  what does and why.** That is a complete answer.
- **THE ARCHIVE'S SHAPE DOES NOT TRANSFER.** **Say exactly which part fails and
  why**, at `file:line` on both sides. **`[LJ-1.240]` already warns that
  `Cl = ⊤̇` there, so the archive's story may be thinner than the tree's.**
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Every cut gets the SAME
  bound as its green control, and the control's elapsed time is reported BEFORE
  any cut is interpreted** (`[LJ-1.215]`'s law).

## WHAT THIS TASK IS NOT

- **It is NOT the numeral-closure.** `[LJ-1.240]` measured that the closure is
  real and that it is owed to **`amb`**, not to `lh`: an unconstrained tag
  satisfies the formula at a wrong `v`
  (`agents/tasks/LJ-1-178/ProbeLJ1178A.agda:190-192`). **That is the fifth step
  and it is a separate dispatch.**
- **It is NOT the supply of `lh`.** You build the FORMULA the type needs.
- **Do not rebuild `sl` or `sc`.** Green at 14 and 38 lines.

## WHAT YOU MUST NOT DO

- **Do not edit any master.** This is a probe. **Nothing lands in `src/`, and a
  probe under `src/` is forbidden by I-5.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-241/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure**, discard a warm-up, and take at least
  three kept runs for any figure a decision rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap. **`[LJ-1.234]`
  met one and it was R-34's unpinned `InfinitySet` level meta, cured by
  `module IS = InfinitySet {ℓ}`. Check that before you call a heap wall
  yours.**
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## CARRY A CLAIM'S QUALIFIER OR CARRY NEITHER

**`[LJ-1.239]` wrote that a type was not instantiable BY THE CITED PIECES. I
dropped those four words and the project's status screen then said the type was
REFUTED.** **It was not.** **`dev/JOURNAL.md` carries the episode.**

**So: when you bound a claim, bound it in the sentence a reader will quote.**
**And if THIS brief states anything you cannot find, say so and treat it as
unproven** (C-44).

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.240]` measured that nothing moves here: `lh` was already the per-tower
point, and `dev/literature/devlin-II5.md:375` says the J side of row C2 is
SYNTAX-FREE, so the numeral-closure lands in the small per-tower half.**

**`φ₀` itself is a FORMULA over `⊥*`. Say whether it is tower-neutral**, and if
it is, say so plainly, because a tower-neutral `φ₀` is shared code and the J
tower pays it once.

## ARCHIVE (DD18)

**This section is the task, not a formality. Two reports declined it and both
were wrong.**

- **`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:529-531`,
  `:592-593`, `:600-601`, `:768-769`, `:823-824`.**
- **`archive/src/2026-08-09-rud-route/L/LevelKit.lagda.md:567-571`.**
- `agents/tasks/LJ-1-240/lj-1.240-report.md`, read WHOLE: it found these and
  it says what does NOT transfer.
- `agents/tasks/LJ-1-239/lj-1.239-report.md` and `ProbeLJ1239A.agda`: the arity
  measurement and the closed step 1.
- `agents/tasks/LJ-1-237/lj-1.237-report.md` and `ProbeLJ1237A.agda`: `sl`,
  `sc` and the `lh` parameter.
- **`src/L/BoundedSubset.lagda.md:74-146`, `:840-869`,
  `src/FOL/Count.lagda.md:598`, `src/L/Condensation.lagda.md:1125`: read the
  source, never a report about it.**

**Return an ARCHIVE USED section that names, for each archived file you opened,
ONE line you read.** **A survey with no line is not a survey.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:95-96` states the level-hood as
`∃z Φ(z,v,γ)`, arity two.** **Say whether your `φ₀` is that statement**, and
whether the twelve numerals appear in Devlin at all or are an artifact of the
coding. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-240/lj-1.240-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-241/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed above.
- **C-36.** Write the term you could not write.
- **C-44.** A brief's claim is unchecked until you check it.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **P-l.** The archive's shape is a SHAPE and not a price.
- **C-42, C-39, C-40. I-5, R-34. P-i, P-k, P-m, P-t, P-y, R-40. C-12, C-22.
  DD0, DD8, DD18, DD24, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with whether `φ₀` builds at arity two, and with its written lines.**
Then whether `⊤̇` typechecked. Then what the archive's shape gave you and what
did NOT transfer, at `file:line` on both sides. Then whether `φ₀` is
tower-neutral. Then the seconds with load and run count. **Mark every negative
MEASURED or INFERRED.**
