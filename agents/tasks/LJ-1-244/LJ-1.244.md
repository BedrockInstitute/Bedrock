# LJ-1.244: the third route, which is route 2 cut in half

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.243]` found a third route and it is the cheapest of the three. Build
it.**

**`q` has ONE use site, `agents/tasks/LJ-1-184/ProbeLJ1184B.agda:122`, and the
`sym` there shows it spends ONE DIRECTION ONLY.** **So the module does not need
the equation. It needs:**

```agda
q' : (γ : Vec A.R.SC 2)
   → ⟨ ambient γ (embed φ₀) ⟩
   → ⟨ ambient γ (Graph {2} zero (suc zero)) ⟩
```

**That is `[LJ-1.242]`'s route 2 cut in half, and the half it keeps is the half
`amb` is.**

## WHY THE EQUATION CANNOT BE HAD, so you do not try

**Two independent refutations, both MEASURED, and I re-derived the second:**

1. **Constants.** `LsetGraphAt` keeps its numeral as `con (numeralL k)`, and
   `tagAtL` emits it at `agents/tasks/LJ-1-210/GenModel.agda:341`. **A
   constant-free `φ₀` can never equal it.**
2. **Shape, and this one needs only two definitions.** **`φ₀` is fourteen
   nested `∃̇`** (`agents/tasks/LJ-1-241/ProbeLJ1241A.agda:140-146`).
   **`LsetGraphAt` is ONE `∃̇` over a `∧̇`**
   (`agents/tasks/LJ-1-238/GenSequence.agda:167`). **`∧̇` and `∃̇` are different
   constructors** (`src/FOL/Syntax.lagda.md:96,99`). **The deepest frame is a
   type mismatch.**

**So do not attempt `q`. Build `q'`.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **`q'` BUILDS.** Report its written lines and the seconds, and **re-run
  `[LJ-1.184]`'s module with `q` replaced by `q'`**. **Then `amb` is supplied
  outright for the first time and phase 1's blocking row moves.** STOP.
- **`q'` BUILDS BUT THE MODULE NEEDS MORE.** **Say what else the `sym` at
  `:122` was carrying** (C-36). **`[LJ-1.243]` read one direction; if it read
  it wrong, that is the finding.**
- **`q'` IS AS HARD AS `q`.** **Name the term that blocks it.** **Then the
  third route collapses into route 2 and the phase faces a chapter.**
- **THE ONE USE SITE IS NOT ONE.** **`[LJ-1.243]` measured `q` at exactly one
  use site.** **Check it. If there are two, the halving does not apply.**
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Every cut gets the SAME
  bound as its green control, and the control's elapsed time is reported BEFORE
  any cut is interpreted** (`[LJ-1.215]`'s law).

## WHAT IS GREEN, so you assemble rather than invent

| file | what it is |
|---|---|
| `agents/tasks/LJ-1-184/ProbeLJ1184B.agda` | `AmbientStep` with `q` at `:112` and its one use at `:122` |
| `agents/tasks/LJ-1-184/ProbeLJ1184C.agda` | the real site; it RELAYS `q` at `:83` |
| `agents/tasks/LJ-1-241/ProbeLJ1241A.agda` | the real `φ₀`, arity two, with `pins` |
| `agents/tasks/LJ-1-238/GenSequence.agda` | the six readings, class-generic, residual 0 |

**Four green files. Assemble; do not rewrite any of them.**

## C-45 BINDS THIS TASK DIRECTLY

**C-45 entered `dev/LESSONS.md` today with this very episode as its
measurement: an assumed equation in a telescope is a performance idiom when
`refl` closes it and a HYPOTHESIS when it does not, and the telescope cannot
tell you which.**

**So: if you replace `q` with `q'`, SEARCH FOR EVERY APPLICATION of the module
and check that `q'` is given a real term.** **Do not report `q'` as supplied
because a file exits 0.** **A module with a false hypothesis typechecks, and it
typechecks fast.**

## WHAT YOU MUST NOT DO

- **Do not attempt route 1.** `[LJ-1.243]` re-priced it: `absFo` is the
  instrument there, not `erase`, and its widest term is **1,688 constant
  occurrences**, not twelve tags.
- **Do not supply `lh`.** Separate dispatch.
- **Do not rebuild `φ₀`, the readings, `sl` or `sc`.**
- **Do not edit any master.** This is a probe. **Nothing lands in `src/`, and a
  probe under `src/` is forbidden by I-5.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not touch `agents/tasks/LJ-1-245/`.** A sibling is live there.
- **A probe goes in `agents/tasks/LJ-1-244/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure**, discard a warm-up, and take at least
  three kept runs for any figure a decision rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap. **`[LJ-1.234]`
  met one and it was R-34's unpinned `InfinitySet` level meta, cured by
  `module IS = InfinitySet {ℓ}`.**
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THREE RULES THIS AREA EARNED THIS WEEK

**CARRY A CLAIM'S QUALIFIER OR CARRY NEITHER.** I dropped four words from a
report and the status screen said a type was REFUTED when it was not.

**THE ARCHIVE BEARS UNTIL YOU OPEN IT.** Two reports called it surveyed and
not bearing; both were wrong.

**`exit 0` IS NOT A SUPPLY.** I put `exit 0` beside a green file as evidence
that a hypothesis was discharged. **`[LJ-1.243]` measured that the citation
pointed INSIDE the assumption.**

**And if THIS brief states anything you cannot find, say so and treat it as
unproven** (C-44).

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.242]` measured the bridge as Def-tower content, running through the
satisfaction coding, and `[LJ-1.243]` upheld that.** **The J tower's analogue is
syntax-free op-graphs** (`dev/literature/devlin-II5.md:375`), **so it does not
pay this bridge.**

**Say whether `q'` is smaller than `q` would have been in the same sense**, and
whether any part of it is tower-neutral. **A one-directional implication may
share more than an equation does.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-243/lj-1.243-report.md`**, read WHOLE. **Its third-route
  section is your specification.**
- **`agents/tasks/LJ-1-242/lj-1.242-report.md`**: the two routes and why the
  equation fails.
- **`agents/tasks/LJ-1-184/lj-1.184-report.md`, `ProbeLJ1184B.agda`,
  `ProbeLJ1184C.agda`**, read WHOLE. **Read the telescopes, not the report.**
- `agents/tasks/LJ-1-241/` and `agents/tasks/LJ-1-238/`: `φ₀` and the readings.
- **`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:208`,
  `:806-809`.** **`[LJ-1.243]` measured that the retired route parameterized
  the SAME crossing and left it undischarged, and `:806-809` names the owed
  equivalence.** **Read it: the archive may show which DIRECTION it intended.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`[LJ-1.243]` measured that Devlin TAKES clause (a) from II.2.7, that II.5
never re-derives it, and that NO two-coding bridge appears in his proof: one
formula, read at two carriers, bridged by 1.9.15.** **Say whether 1.9.15's
shape is your `q'`.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-243/lj-1.243-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-244/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed above.
- **C-45.** Audit the INSTANTIATION, never the telescope. **This task is
  C-45's first test case.**
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-44.** A brief's claim is unchecked until you check it.
- **C-36.** Write the term you could not write.
- **P-l, C-42, C-39, C-40. I-5, R-34. P-i, P-k, P-m, P-t, P-y, R-40. C-12,
  C-22. DD0, DD8, DD18, DD24, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with whether `q'` builds, and whether `amb` is supplied OUTRIGHT with it
in place.** Then the instantiation audit: every application of the module, and
what each gives for `q'`. Then anything else the `sym` was carrying. Then the
seconds with load and run count. Then the DD4 answer. **Mark every negative
MEASURED or INFERRED.**
