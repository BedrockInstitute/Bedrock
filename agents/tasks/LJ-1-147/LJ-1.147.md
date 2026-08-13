# LJ-1.147: seal `satGraphAt`, and measure what the seal really buys

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`[LJ-1.145]` diagnosed the GCH wing's cost down to ONE conversion and priced
one cure. Land it, and close its own widest unmeasured term.**

## WHAT IS MEASURED, and I verified each line myself

**The cure:** `opaque` on `satGraphAt`, `src/L/Coding/Graph.lagda.md:191-192`.

`agents/tasks/LJ-1-145/ProbeLJ1145D.agda` rebuilds `DefBody`'s exact shape
twice: **`midOpen` 2,459 ms, `midSealed` below 1 ms.**

**The term it kills:** in a verbatim transplant of `LeafAgree`, taking a
component out of a pattern split and naming its folded type costs **2,526 ms**,
**65 percent of the master's most expensive definition**. Splitting and
rebuilding costs 12 ms; applying the supplier costs 15 ms. **The cost is the
coercion and nothing else.**

**Two leads were refuted on measurement and you must not revisit them.** P-x:
the field `[LJ-1.109]` names was added and then REMOVED, `grep -c sucK` returns
0, and I verified that. P-w: `useApp` 10 ms against `useFun` 23 ms, so removing
a module application cost MORE.

## THE PRICE, and its honest limit

**About 21 s off the master, 25 lines added and none deleted, across five
masters.** `[LJ-1.145]`'s arithmetic has three steps and it marked the third
INFERRED: the out/back family at 39,731 ms MEASURED, minus 7,443 ms that must
carry `unfolding`, times the 65 percent share measured at ONE site.

**IT DOES NOT CLOSE THE GAP AND SAID SO.** 122.64 s to about 101.6 gives
0.0158; the wing lands at 0.0166 against the 0.0136 bar. **About 40 percent of
the 55.3 s gap.**

**Its widest unmeasured term is what the `unfolding` blocks COST**, never
measured at this scale. **It priced closing that at one edit and one cold run.
Do it.**

## WHAT TO DO

1. **Apply the seal**, and add `unfolding` wherever a proof genuinely needs to
   see through it. **Add the minimum, and count them.**
2. **Measure `unfolding`'s cost**, which is the point of this task and not a
   side errand. Report it MEASURED.
3. **Re-measure the master and the wing** with
   `.venv/bin/python scripts/check-ratio.py --module <file>` and then the whole
   wing. **Report the before and after with the LOAD beside each.**
4. **Verify the CONSUMERS.** C-40: `src/L/Coding/Graph.lagda.md` is imported by
   the AC wing as well as the GCH wing, MEASURED at
   `src/L/Choice/Internal.lagda.md` and `src/L/Choice/Adequate.lagda.md`.
   **Typecheck every consumer, not only the master you changed.** I committed
   three RED trees in one day for exactly this, which is why C-40 exists.
5. **If the seal makes the AC side slower, that is a finding and it may kill
   the cure.** Measure it, do not assume it.

## THE MEASUREMENT DISCIPLINE, and today made it sharp

**The machine moved figures by 20.1 percent between two runs of the SAME
instrument on the SAME tree today.** `[LJ-1.128]` measured 11.2 percent,
`[LJ-1.135]`'s control 6.9 percent, `[LJ-1.144]` 20.1 percent.

**DD24's tolerance is 1.15x, which is narrower than the machine's own swing.**

**So: report the load beside every absolute figure, and take more than one run
for any figure a decision rests on.** A single cold number is not a price
today. **Say how many runs each figure is.**

## THE ABORT CRITERION

- **The seal lands green and the wing improves**: report and STOP.
- **`unfolding` costs back what the seal saves**: **STOP AND SAY SO.** That is
  a complete and valuable answer: it means the term is intrinsic and the wing's
  verdict becomes a content question for the owner.
- **A consumer goes RED**: STOP, report it, do not paper over it.
- **Anything walls**: STOP, report it with its seconds.

## WHAT YOU MUST NOT DO

- **Do not delete lines to improve a ratio.** DD24's own row: the ratio exists
  so the content must be the same KIND of content, and shrinking the
  denominator is the cheat it refuses. P-q measured 315 lines removed buying
  11.8 seconds.
- **Do not touch the three `*Agree` masters.** `[LJ-1.144]` and `[LJ-1.145]`
  BOTH ruled that their fate must not be decided before this seal is measured.
  **You are the measurement they are waiting on.**
- **Do not revisit P-x or P-w.** Both refuted, MEASURED.
- **Do not touch `src/ProbeLJ1134A.agda` or `src/ProbeLJ1136*.agda`.**
- **A probe goes in `agents/tasks/LJ-1-147/`**, never in `src/`, tracked, never
  deleted. **Read `AGENTS.md` and `dev/LESSONS.md` D-1 fresh; both changed
  today.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** A sibling
  may run Agda; report the load and say whether the machine was quiet.
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it. **Run `agda` on each changed master and
  each consumer instead.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.145]` already answered it: the seal is upstream and generic, so one
edit serves both trophies. VERIFY that, by measuring the AC side before and
after.** A cure that helps one wing and hurts the other is not generic.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-145/lj-1.145-report.md`**, read WHOLE, and its four
  probes. **The diagnosis, the two refutations and the arithmetic you are
  closing.**
- `agents/tasks/LJ-1-144/lj-1.144-report.md`: why the `*Agree` decision waits
  on you.
- **`dev/LESSONS.md` P-q, P-t, P-s, P-m, C-40, C-12, P-l**, read WHOLE.
- `dev/PLAN.md` DD24, for what the bar is and why it is a ratio.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs elaboration cost. Say so in one line.**

## SCOPE (read)

`src/L/Coding/Graph.lagda.md` FIRST, then
`agents/tasks/LJ-1-145/lj-1.145-report.md`.

## SCOPE (write)

`src/L/Coding/Graph.lagda.md` and any master that needs `unfolding` because of
your seal. **Nothing else under `src/`.** Your report and probes are
`agents/tasks/LJ-1-147/`.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for build` and read every statement.

- **C-40.** Verify the CONSUMERS. **This is the rule this task turns on.**
- **P-q, P-t, P-s, P-m, P-l, C-12, C-22, C-36, C-38 as extended, C-39.**
- **DD8, D-1, D-10, D-26, D-29, D-30.**
- **C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. **Code comments are not prose; write them.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the before and after, in seconds, with the load and the run count
beside each.** Then what `unfolding` cost, MEASURED. Then every consumer and
its verdict. Then the wing's new figure against the bar. Then whether the AC
side moved. Then what remains of the 55.3 s gap and what would close it.
**Mark every negative MEASURED or INFERRED.**
