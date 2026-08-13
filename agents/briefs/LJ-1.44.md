# LJ-1.44: locate the content class that costs 65 seconds in Condensation

tier: codex (default)

## GOAL

`src/L/Condensation.lagda.md` spends about 65 of the GCH side's 84 seconds.
The side is OVER DD24's bar. **Find what content class costs it, and say
whether the class can change.** This is a probe. Throw the code away.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`8019b6a`.

## THE NUMBERS, and the bar moved since the last brief said otherwise

`scripts/check-ratio.py --check` on the committed tree:

| module | lines | cold s | rate |
|---|---:|---:|---|
| `src/L/Condensation.lagda.md` | 4,512 | 64.91 | **0.0144 OVER** |
| `src/L/StageCardinal.lagda.md` | 491 | 12.08 | **0.0246 OVER** |
| `src/V/Presentation.lagda.md` | 18 | 0.66 | 0.0365 OVER, a module-load floor |
| `src/FOL/Count.lagda.md` | 620 | 1.68 | 0.0027 |
| `src/L/Hull.lagda.md` | 431 | 2.72 | 0.0063 |
| `src/V/Collapse.lagda.md` | 335 | 2.08 | 0.0062 |

Aggregate **0.0131 over 6,407 lines and 84.13 s, OVER THE BAR.**

**THE BAR IS 0.0127, NOT 0.013193.** It is computed from the AC baseline
0.011057 times the 1.15 tolerance, and the AC baseline was re-measured DOWN on
2026-08-11, so the bar came down with it. Earlier briefs of mine quote the
stale 0.013193. **Use 0.0127 and re-derive it yourself from
`dev/ledger.toml`.**

**RUN-TO-RUN VARIANCE IS ABOUT 10 PERCENT** and the breach is 3 to 13 percent,
so the verdict sits inside the noise on a fast run. **Repeat every measurement
at least three times and report the spread, not one number.** A verdict inside
the noise band is a finding in its own right.

## WHAT THE TOOL ITSELF SAYS, and it frames the task

> DD24 is the only threshold on this wing and the wing is over it. There is no
> line cap and no seconds cap to trade against; the content class has to
> change. Read P-m, P-q and P-t before optimizing: a line lever is not a
> seconds lever.

**So do not look for lines to remove.** `[LJ-1.39]` measured a 318-line
compression that made the file faster, and removing lines RAISES the rate.
**That is not the lever.**

## THE QUESTION

**Profile the master and attribute its seconds to content classes**, not to
files. `agda --profile=definitions` is the instrument this tree has used
throughout.

Then answer: **which class is it, and can it change?** The classes this tree
has measured, with their laws:

- **P-t.** The class follows the FORMULA, not the carrier. A built formula tree
  unfolds at every use.
- **P-l.** Naming a transparent or built construction in a statement's TYPE is
  what costs.
- **P-v.** A satisfaction-level conversion between two spellings of one formula
  costs seconds where the formula-level identity is free. **Measured at 59 ms
  against 29,415 ms in this same file.**
- **P-n.** Satisfaction content at a concrete carrier is a payable FLOOR, 0.22
  to 0.297 s per line. **If a block is at the floor, no restatement helps and
  that is the answer.**
- **P-m.** The rate certifies the class.

**If the cost is a payable floor, say so and stop.** That is a full deliverable
and it tells the owner the wing's bar has to be argued rather than engineered.

## WHAT IS SETTLED, so you do not re-open it

- The twelve-row table and block 1 are CLOSED and machine-checked. **Do not
  re-derive the mathematics.**
- The master has ZERO placement and that is load-bearing (P-u). **Any cure that
  needs `absFo` or a placed `Δ₀` is refused before it is measured**: that wall
  is flat at 8 GB.
- `[LJ-1.39]`'s compression is measured and held. **Not your task.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker, so it is stated in every brief and answered in
every return.

**Say which side the expensive class falls on.** If the cost is in the shared
frames, the J tower inherits it and the price doubles in effect. If it is in
the per-tower Def content, the J tower's structural certificate may avoid it
entirely (D-26).

## ARCHIVE (DD18)

**Nothing in the archives bears, and I say so naming them rather than omitting
the section.** `archive/rud-route/` holds the retired route's code, whose
`Condensation` module was measured at 0.395 s per line but whose target
`[LJ-1.11]` showed is classically FALSE, so it can price nothing here.
`archive/dev/TASKS-archived.md`, `JOURNAL-archived.md` and
`DECISIONS-archived.md` cover the retired `D` series and the rud dispatches.
**This task profiles code written this week against a bar re-measured this
week.**

**What DOES bear is not archived:** `dev/LESSONS.md`, which still binds, and
the live reports `_build/lj-1.43-report.md`, `_build/lj-1.42-report.md` and
`_build/lj-1.39-report.md`, the last holding the compression measurement you
must not repeat. **Read those whole.**

Return an **ARCHIVE USED** section at `file:line`, and say plainly if you found
an archived comparable I missed.

## LITERATURE (DD18)

**Nothing in `dev/literature/` bears.** This is an elaborator cost measurement
on this tree's own code. `devlin-II5.md` prices the mathematics and says
nothing about check cost; `j-hierarchy.md` covers the J side, which this file
does not touch; `devlin-errata.md` does not reach Chapter II section 5, which
`[LJ-1.14]` verified. **Say so in one line and spend nothing.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## SCOPE (read)

`src/L/Condensation.lagda.md`, `scripts/check-ratio.py` for the caliber, and
`dev/ledger.toml` for the baseline. Read `dev/LESSONS.md` P-l, P-m, P-n, P-q,
P-t and P-v whole.

## SCOPE (write)

`src/ProbeLJ144*.agda` only, and your report `_build/lj-1.44-report.md`. **No
master. No file under `dev/`. Never `src/Everything.lagda.md`.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for probe` and `--for recon`, and read each
statement.

- **D-1.** The smallest decisive miniature, GO or NO-GO with a price, thrown
  away.
- **D-10.** Every figure in this brief is a residue, **including the bar, which
  I quoted wrongly in three earlier briefs.** Re-derive it.
- **D-26.** A well-founded key on a tower needs generation data or syntax.
  **Say in one line whether it bears on which class is expensive.**
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, one process, cap never
  raised. A heap exhaustion is a wall with its seconds.
- **C-22.** Write the deliverable incrementally.
- **C-32.** A cure invalidates downstream measurements, **including in files it
  did not touch. Interfaces live in `_build/2.8.0/agda/src/`, NOT beside the
  source**: deleting a `.agdai` beside a `.agda` removes nothing and turns a
  cold run into a warm read.
- **C-34.** If you name a cure, build it and measure it, or report the wall
  that stopped you. **"P-l forbids it" is not a third option**; P-l forbids
  pricing by analogy, never measuring.
- **C-36.** A failed substitution is not a proof of impossibility.

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- **The machine is quiet and both Agda slots are yours.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.44-report.md` incrementally, skeleton first.

Lead with the verdict: the class, its share of the 65 seconds, and whether it
can change. Then the profile attribution. Then, if a cure exists, its measured
delta; if none does, the term you could not write. Then the spread across your
repeats, the DD4 side, and what you are not sure of.
