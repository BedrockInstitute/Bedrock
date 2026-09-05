# LJ-1.234: does `pairω` need an object-language arithmetic at all?

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.231]` upheld that `pairω` is over 160, refused its「about 700」, and
then named a question nobody has asked in six dispatches.**

**BOTH CONSUMERS DEMAND AN INJECTION AND NAME NO FUNCTION. MEASURED, and I
re-derived both:**

- `src/L/Ordinal/SquareLaw.lagda.md:685-687`:
  `sq α = Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ] ((x y : …) → f x ≡ f y → x ≡ y)`
- `src/L/StageCardinal.lagda.md:15-19`: the same Σ, as a module hypothesis.

**Neither says `Count.pair`. Neither says addition. Neither says
multiplication.** **The obligation is「some injective function exists」.**

**`[LJ-1.226]` built an object-language ADDITION as the first step toward
`pairω`, and its 83 measured lines are addition alone without its adequacy.**

**Ask whether that step is needed.**

## WHY THIS IS THE RIGHT SHAPE OF QUESTION

**This project has DISSOLVED three items this month, and each was worth more
than the measurement it replaced:** A5's `CSB` (`[LJ-1.156]`), A5's 300-line
item (`[LJ-1.176]`), and `[LJ-1.196]`'s CHAPTER (`[LJ-1.210]`).

**`[LJ-1.231]` found the shape evidence in the archive:** the retired route
closed the base at `ω` with **ZERO arithmetic**, in about 79 lines at
`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:815-893`.

**That is AMBIENT, so it is a SHAPE and never a price (P-l).** **The question
is whether the same shape survives the move into L.**

**And `[LJ-1.231]` recorded the counter-evidence beside it, so you get both:**
`agents/tasks/archive/L3-32-T85/l3.32-t85-report.md:110` says the order core at
`ω` walled once. **Read that before you assume the shape is free.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **NO ARITHMETIC IS NEEDED.** Build an injective `⟪ω⟫ × ⟪ω⟫ → ⟪ω⟫` into L by
  a route that never states addition or multiplication in the object language.
  Report the written lines and the seconds. **Then A5 row 5 DISSOLVES from
  「about 355 and open」to one number, and this is the best outcome available.**
  STOP.
- **ARITHMETIC IS NEEDED, AND HERE IS WHY.** **Name the exact step that forces
  it** (C-36). **Then `[LJ-1.226]`'s 83 lines are load-bearing, the half-open
  band from about 355 stands, and the route knows what it is paying for.**
- **A CHEAPER ARITHMETIC EXISTS.** If the object language is needed but a
  smaller form serves, **price it against `[LJ-1.226]`'s 83 measured lines.**
- **THE ORDER CORE WALLS AGAIN.** `[T85]` recorded one wall at `ω`.
  **If you meet it, name the term and report the ELAPSED SECONDS.** **Do not
  assume it is the same wall.**
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Every cut gets the SAME
  bound as its green control, and the control's elapsed time is reported
  BEFORE any cut is interpreted** (`[LJ-1.215]`'s law).

## WHAT IS GREEN, so you extend rather than rebuild

**`agents/tasks/LJ-1-226/ProbeLJ1226A.agda` is green**, `--safe`, exit 0, cold
mean 1.69 s: 203 non-comment lines, of which Part 0 is the AMBIENT `pairω`
(`NumeralPresentation`) and Parts 1 and 2 are the object-language addition.

**Part 0 is the base and it is not the charge.** **Start there. You may find
that Part 0 plus a carve is the whole answer.**

## WHAT YOU MUST NOT DO

- **Do not rebuild `[LJ-1.226]`'s addition.** It is green and measured at 83
  lines. **You are asking whether it is needed, not whether it works.**
- **Do not re-price the rest of A5.** `[LJ-1.176]` measured 547.
- **Do not quote a total for Route A-prime.** Five reports now refuse one.
- **Do not edit any master.** This is a probe. **Nothing lands in `src/`, and a
  probe under `src/` is forbidden by I-5.** I moved three strays out of `src/`
  today; do not put one back.
- **Do not touch `agents/tasks/LJ-1-232/` or `LJ-1-233/`.** Two siblings are
  live there.
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-234/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **A sibling
  holds the other Agda slot.** **Report the load beside every absolute figure**,
  discard a warm-up, and take at least three kept runs for any figure a decision
  rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## CITE THE REPORT THAT MEASURED, NEVER THE ONE THAT QUOTED

**A figure quoted at one remove looks identical and is a different claim.** **I
broke this rule twice today in one brief and `[LJ-1.231]` caught both.** **When
you cite a number, open the report that MEASURED it.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.231]` MEASURED that `[LJ-1.227]`'s tower table does NOT cover A5**, so
`pairω`'s tower status is an open question and not a settled one. **Do not
assume either way.**

**A pairing on `ω` names no tower in its statement.** **If what you build is
tower-neutral, the J tower pays it once rather than twice, and that halves its
weight in any route decision. Say which it is, with evidence.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-231/lj-1.231-report.md`**, read WHOLE. **It is your
  brief within this brief:** the consumer analysis, the archive shape, and the
  counter-evidence beside it.
- **`agents/tasks/LJ-1-226/lj-1.226-report.md` and `ProbeLJ1226A.agda`, read
  WHOLE**: what is green and what it cost.
- `agents/tasks/LJ-1-176/lj-1.176-report.md:192-206`, `:227-229`, `:452`: A5's
  object list, the fact that the 160 was row 1's number transferred to another
  object, and the ruling that `pairω` is A5's.
- **`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:815-893`:
  the zero-arithmetic base at `ω`, about 79 lines. READ THE CODE, not the
  report about it. Take SHAPE from the archive, never a claim**, and say what
  would NOT transfer into L.
- **`agents/tasks/archive/L3-32-T85/l3.32-t85-report.md:110`: the order core
  walling at `ω`.**
- `src/L/Ordinal/SquareLaw.lagda.md:685-687` and
  `src/L/StageCardinal.lagda.md:15-19`: **the two obligations, read at the
  source.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/rudimentary-functions.md:68` is the basis `[LJ-1.176]`
inferred `pairω` from.** **Say whether it requires an object-language
arithmetic or only a pairing**, and whether any source treats the `ω` base
separately. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-231/lj-1.231-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-234/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed above.
- **D-10.** **Price the truth of a recorded residue before pricing its proof.
  This task IS D-10: the residue may not exist.**
- **P-l.** The archive's 79 ambient lines are a SHAPE and not a price.
- **C-36.** Write the term you could not write. **If arithmetic IS forced, the
  forcing step is the deliverable.**
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-42.** A refutation measures the site it names, never its extent.
- **I-5.** No probe under `src/`.
- **P-i, P-k, P-m, P-t, P-y, R-40. C-12, C-22, C-39, C-40. DD0, DD8, DD24,
  D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with YES or NO: is an object-language arithmetic needed for `pairω`?**
Then the written lines of whatever you built, against `[LJ-1.226]`'s 83. Then,
if arithmetic is needed, the exact step that forces it. Then whether the
archive's zero-arithmetic shape transferred. Then the seconds with load and run
count. Then the tower status with evidence. **Mark every negative MEASURED or
INFERRED.**
