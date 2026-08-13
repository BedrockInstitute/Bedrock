# LJ-1.168: re-measure the satisfaction layer, 5,047 lines nobody has re-priced

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`[LJ-1.166]` named the satisfaction layer as the phase's largest unpriced
volume: `[LJ-1.2]` priced that content at 5,047 lines and NO GATE HAS
RE-MEASURED IT against the current coding.**

**Re-price it. This is a recon, not a build.**

## WHY IT IS OPEN, MEASURED

`[LJ-1.166]` built one `KFacts` value and priced the closure layer at 88
in-fence lines. **It then said exactly where the figure stops:**

> it covers the closure layer, **29 of 29 `KFacts` fields but only 31 of
> `TFacts`' 57. The other 26 are satisfaction facts that a bound does not
> supply and nobody has priced.**

**So the phase now has: a working assembly (17 lines, `[LJ-1.165]`), a working
supply for the closure half (88 lines, `[LJ-1.166]`), and 26 satisfaction facts
with no price at all.**

## THE FIGURE YOU ARE TESTING

**`[LJ-1.2]`'s 5,047 lines**, at
`agents/tasks/archive/LJ-1-2/lj-1.2-gate.md`. **It was measured on a different
coding and it returned NO-GO.** `dev/PLAN.md`'s own row for it reads
「Step clause has no Delta-0 witness at ANY carrier」.

**But the literature digest says that NO-GO answered the wrong question:**

> **the direct answer to `[LJ-1.12]`: a Δ₀ witness for the satisfaction leaves
> is NOT what Devlin's argument needs.** Level-hood is used at Σ₁ strength,
> and the proof's satisfaction steps concern the Σ₁ statement inside `L_α`,
> not a Δ₀ certificate.
> (`dev/literature/devlin-II5.md:242-247`)

**So the 5,047 may be the price of something the argument never needed. That
is your first question and it may collapse the figure.**

## WHAT TO DO

1. **Search first.** `[LJ-1.163]` found `ElemDown` already delivered after
   three dispatches priced it; `[LJ-1.166]` found three of four closure classes
   already proved at `src/L/Choice/Name.lagda.md:120-135`, cited by no brief in
   this phase. **Two misses in four dispatches, both in `L/Choice/`.** **Report
   what is already delivered BEFORE you report a price.**
2. **Name the 26 facts.** `[LJ-1.166]` counted them; list them at `file:line`
   with what each asserts.
3. **Say which of them the Σ₁ reading actually needs**, against the Δ₀ reading
   `[LJ-1.2]` priced. **If the Σ₁ reading needs fewer, say how many fewer.**
4. **Then price what remains**, one best-effort figure with its basis named
   (DD8), and **name its widest unmeasured term and the probe that measures
   it.**

## THE ABORT CRITERION

- **You can price it**: report the figure, its basis and its widest unmeasured
  term. STOP.
- **The Σ₁ reading collapses the figure**: **say so FIRST and say by how
  much.** That would be the largest single re-price in the phase.
- **Most of it is already delivered**: **say so FIRST.** That is the third time
  this phase and it would confirm the pattern is the search rather than the
  tree.
- **The satisfaction facts cannot be supplied at all on this coding**: **STOP
  AND SAY SO.** That is a route-level finding and it outranks any number.

## WHAT YOU MUST NOT DO

- **Do not build.** This is a recon and a price.
- **Do not price by analogy.** P-l: `[LJ-1.2]`'s figure is a comparable on a
  DIFFERENT coding, so it is a hypothesis here, not a price.
- **Do not edit any master.**
- **A probe goes in `agents/tasks/LJ-1-168/`**, never in `src/`, tracked. **One
  small probe is allowed if a step genuinely cannot be priced by reading.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** A sibling
  is running Agda. **Your figures are lines and shape, so a busy machine costs
  you only time. Say so.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**A satisfaction table is coding-layer content and both towers need one.** Say
what fraction is template, and whether the J tower re-instantiates or rewrites.

## ARCHIVE (DD18)

**`[LJ-1.157]` measured 37 of 61 live briefs citing no archive; `[LJ-1.160]`
found the phase's bypass inside one; `[LJ-1.166]` found half its answer in a
live file no brief had cited.**

- **`agents/tasks/archive/LJ-1-2/lj-1.2-gate.md` section 5**, which the
  literature digest cites by name for the missing facts. **Read it WHOLE. It is
  the figure you are testing.**
- **`archive/src/2026-08-09-rud-route/L/Definability.lagda.md`** and
  **`L/Coding/`**: the retired route's satisfaction machinery. **Did it build
  the table? At what size?**
- `archive/src/2026-08-09-rud-route/L/LevelFormula.lagda.md`, 258 in-fence.
- **Take SHAPE, never a claim.** `[LJ-1.11]` ruled that route's condensation
  target classically FALSE.
- `agents/tasks/LJ-1-166/lj-1.166-report.md` and `LJ-1-165/`, read WHOLE.
- **`dev/LESSONS.md` C-38 as extended, D-1, DD8, P-l, C-36**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:240-260` is the load-bearing read**, and it is
the passage that may collapse the figure. **Say exactly what Devlin's
satisfaction steps need and at what Levy grade.** Return a **LITERATURE USED**
section.

## SCOPE (read)

`dev/literature/devlin-II5.md:240-260` FIRST, then
`agents/tasks/archive/LJ-1-2/lj-1.2-gate.md`, then `src/L/Coding/`.

## SCOPE (write)

`agents/tasks/LJ-1-168/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.

- **DD8, P-l, C-38 as extended, C-35, D-1, C-12, C-22, C-36, C-39, C-40.**
- **D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` on anything you write.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with what is already delivered, then with whether the Σ₁ reading
collapses `[LJ-1.2]`'s 5,047.** Then the 26 facts, named. Then the price with
its basis and its widest unmeasured term. Then the DD4 answer. **Mark every
negative MEASURED or INFERRED.**
