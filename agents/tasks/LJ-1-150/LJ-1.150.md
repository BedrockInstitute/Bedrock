# LJ-1.150: place the twelve-row bridge, which is already built

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`[LJ-1.144]` built the bridge in a probe and nobody placed it.** Put it in
the tree, so the three `*Agree` masters stop being a delivered block with no
consumer.

**This is the cheapest unbought result in the wing: about 38 in-fence lines,
about 3.5 s, and no new master.**

## WHAT IS ALREADY DONE, and I verified each line

**`agents/tasks/LJ-1-144/ProbeLJ1144A.agda` produces `twelve-out` and
`twelve-back` in the EXACT types the consumer states them**, `--safe`, exit 0.

**The consumer's sites, which I read myself:**

- `src/L/Condensation.lagda.md:6692-6697`, module `SatGraphAgree` at `:6682`:
  `twelve-out` and `twelve-back` are **unsupplied module parameters**.
- `src/L/Condensation.lagda.md:6911`, module `LeafAgree`, takes them onward.
- **`TwelveAgree.out` and `.back` are the only producers in the tree.**

**The audit row that stood for a day, `dev/PLAN.md:548`, is TRUE and is NOT a
blocker.** `∧̇` is a `Formula` constructor, so the right-nested chain and `sixB`
paired with `sixB` are different terms and no `refl` connects them. **But the
consumer's types are at SATISFACTION, not at equality, and satisfaction of a
conjunction is the product. The bridge is twelve projections and eleven
pairings.**

**No new master is needed:** `src/L/Condensation/TwelveAgree.lagda.md:31`
already imports `L.Condensation`, so `SatGraphB` is reachable with no cycle,
MEASURED by the probe.

## WHAT TO DO

1. **Read `agents/tasks/LJ-1-144/ProbeLJ1144A.agda` whole**, and its report.
2. **Place the bridge at `TwelveAgree`'s TOP LEVEL, written generic.** **NOT
   inside the frame.** `[LJ-1.144]` measured why: P-w copies 28 lines per
   application.
3. **Typecheck `TwelveAgree` and EVERY consumer.** C-40.
4. **Measure the delta**, with the load and the run count beside it.

## THE TREE MOVED UNDER THE PROBE, and you must check this FIRST

**`[LJ-1.147]` sealed `satGraphAt` at `src/L/Coding/Graph.lagda.md` after the
probe was written**, and it added an `unfolding satGraphAt` block at
`src/L/Condensation.lagda.md:6881`.

**So the probe may need an `unfolding` it did not need when it was built.**
**Check that before you conclude anything**, and if it does, **P-y** (admitted
today) says count the definitions that must look INSIDE the formula, not the
ones that name it.

**MEASURED after the seal:** the three `*Agree` masters moved by under 0.7 s,
so their content is stable.

## WHAT THIS DOES AND DOES NOT BUY

**It does NOT discharge anything.** C-38: it exports the type and shortens the
chain by one link. **`[LJ-1.144]` said so and you must repeat it.**

**The chain above stays unconsumed**, because `[LJ-1.146]` MEASURED that
`theorem` at `src/L/BoundedSubset.lagda.md:1621-1622` has no consumer either,
and C-35 fires over the whole wing until the GCH trophy is written.

**So the honest claim is: one link, closed.** Do not write a return that
implies more.

## THE DD24 CONTEXT, so your seconds are read correctly

The wing is **1.91x** the AC side after today's re-measure, on a baseline of
**0.009143**. **Adding 38 lines and 3.5 s moves the ratio by well under one
percent.** **That is not a reason to skip it and it is not a reason to claim
it helps.** Report the delta and let it be small.

## THE ABORT CRITERION

- **It lands and every consumer is green**: report and STOP.
- **The tree moved enough that the probe no longer elaborates**: **STOP AND SAY
  SO with the error.** Do not repair it blind; report what changed.
- **The placement needs a new master after all**: stop and price it.
- **Anything walls**: STOP, report it with its seconds.

## WHAT YOU MUST NOT DO

- **Do not touch `src/L/Coding/Graph.lagda.md`.** `[LJ-1.147]`'s seal landed
  hours ago and 21 consumers are green on it.
- **Do not touch `src/L/Condensation.lagda.md`** unless the placement forces
  it, and then say exactly why.
- **Do not delete lines to improve a ratio.**
- **Do not touch `src/ProbeLJ1134A.agda` or `src/ProbeLJ1136*.agda`.**
- **A probe goes in `agents/tasks/LJ-1-150/`**, never in `src/`, tracked, never
  deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.144]` already ruled the shape: generic at the top level, not inside
the frame.** **Say whether the bridge is template content both towers would
use, or GCH-only.** Its own literature reading says the twelve rows are OUR
encoding rather than Devlin's content, which points one way; check it.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-144/lj-1.144-report.md`**, read WHOLE, and
  `ProbeLJ1144A.agda`.
- **`agents/tasks/LJ-1-147/lj-1.147-report.md`**, for the seal that moved the
  tree under the probe.
- `agents/tasks/archive/LJ-1-76/`: the split that produced the three masters.
- **`dev/LESSONS.md` P-y** (admitted 2026-08-13), **P-w, C-35, C-38 as
  extended, C-40**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`[LJ-1.144]` read this already: the twelve rows are our encoding, not
Devlin's content.** Confirm or refute in one line and say which. Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-144/ProbeLJ1144A.agda` FIRST, then
`src/L/Condensation.lagda.md:6682-6700`, then
`src/L/Condensation/TwelveAgree.lagda.md`.

## SCOPE (write)

`src/L/Condensation/TwelveAgree.lagda.md`, and
`src/L/Condensation.lagda.md` ONLY if the placement forces it. Your report and
probes are `agents/tasks/LJ-1-150/`.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for build` and read every statement.

- **C-40.** Verify the CONSUMERS.
- **C-38 as extended.** This discharges nothing; say so.
- **P-w, P-y, P-q, P-l, C-12, C-22, C-35, C-36, C-39.**
- **DD8, D-1, D-10, D-26, D-29, D-30.**
- **C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. **Code comments are not prose; write them.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with green or not green, and every consumer's verdict.** Then the lines
and the seconds, with the load and the run count. Then whether the seal forced
an `unfolding` and what P-y said about it. Then what is still unconsumed above
it, plainly. Then the DD4 answer. **Mark every negative MEASURED or INFERRED.**
