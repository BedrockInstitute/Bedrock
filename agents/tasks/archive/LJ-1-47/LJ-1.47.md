# LJ-1.47: can the square law's 41.36 seconds come down?

tier: codex (default)

## GOAL

The square law is the single largest measured cost still owed to the GCH side,
and at its archived rate it takes the wing from inside DD24 to 23 percent over.
**Measure whether its content class can change.** This is a PROBE. Throw the
code away.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`cf8ebaa`.

## WHY THIS IS THE PHASE'S BIGGEST LEVER

`src/L/StageCardinal.lagda.md` takes the square law at every infinite set as a
MODULE PARAMETER `sq`. **Nothing in the current plan builds it, so the trophy is
conditional on it.** `[LJ-1.46]` found this while gating `[LJ-1.7]`.

The archived port is **1,283 in-fence lines at a MEASURED 41.36 seconds**
(`dev/ledger.toml:252-253`), which is **0.0322 s per line, 2.5x the bar.**

The arithmetic, and I did it myself on the committed tree:

| state | lines | seconds | rate | against the 0.012716 bar |
|---|---:|---:|---:|---|
| GCH side today | 6,459 | 79.95 | 0.0124 | **within** |
| plus the square law at its archived rate | 7,742 | 121.31 | 0.0157 | **1.23x, over** |

**One module flips the wing.** No other owed item is both this large and this
well measured.

## THE QUESTION

**Profile the archived square law and attribute its seconds to a content
class.** Then answer: **can the class change, and by how much?**

This tree has cured the same family three times this phase, each time
measured and never argued:

- `[LJ-1.24]`: abstract the SOURCE. 29.1 s to 2.3 s, 12.8x.
- `[LJ-1.34-R]`: one spelling instead of two. 29,415 ms to 59 ms at the pair.
- `[LJ-1.45]`: the same law at the leaves. 2,029 ms to 197 ms, 10.3x.

**And it has also failed four times out of five on transplants**
(`dev/LESSONS.md`, the transplant table). **So measure; do not argue.** P-l
forbids pricing a cure by ANALOGY. It does NOT forbid building the cure and
measuring it (C-34).

## THE LAWS THAT NAME THE SUSPECTS

- **P-t.** The class follows the FORMULA, not the carrier.
- **P-l.** Naming a transparent or built construction in a statement's TYPE is
  what costs.
- **P-v.** A satisfaction-level conversion between two spellings of one formula
  costs seconds where the formula-level identity is free.
- **P-n.** Satisfaction at a concrete carrier is a payable FLOOR, 0.22 to
  0.297 s per line. **The square law is at 0.0322, well below that floor, so
  P-n is probably NOT the answer here.** Say so or refute it.
- **P-q.** A line lever is not a seconds lever.

**If the cost is intrinsic and no class change helps, say so with the profile.**
That is a full deliverable: it tells the owner the wing's budget has to be
argued rather than engineered, and it is the honest outcome if it is the true
one.

## AN ARCHITECTURE QUESTION THAT MAY MATTER MORE, and it is yours to raise

The square law is needed **only** to bound the level size. **Ask whether the
GCH chain needs the square law at every infinite set, or only at the specific
cardinals 5.5 and 5.6 use.** `[LJ-1.21]` took it as a parameter at every
infinite set because that was convenient, not because the consumer demanded it.

**If a weaker law suffices at the consumer, its price may be a fraction.**
Report what the consumer actually needs, at `file:line`, before pricing the
general law.

## WHAT IS SETTLED

- The archived module's SHAPE is available at
  `archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md`. **Its target is sound
  here**, unlike the archived `Condensation`, whose target `[LJ-1.11]` showed
  is classically false. **But `[LJ-1.17]` measured it and `[LJ-1.17-R]`
  corrected the arithmetic around it, so re-verify both.**
- **P-u**: certify before you place. The placement wall is flat at 8 GB across
  constant counts 0, 1, 2 and 5. **If a cure needs `absFo` or a placed `Δ₀`,
  stop and report it.**
- DD24's live bar is **0.012716**, from the AC baseline 0.011057 times the 1.15
  tolerance. **Do not use 0.013193**; several earlier briefs of mine quote that
  stale figure. Re-derive it from `dev/ledger.toml`.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker, so it is stated in every brief and answered in
every return.

**Cardinal arithmetic is template content.** `[LJ-0.7]` found exactly two
per-tower objects on the GCH chain and neither is this. **So a cure here pays
twice and a failure here costs twice.** Say what the J tower inherits.

## ARCHIVE (DD18)

- **`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md`**, the port, read
  WHOLE. `:918-963` holds the `Init` definition and its non-initial gap.
- `_build/lj-1.17-report.md` and `_build/lj-1.17-review.md`, the measurement
  and the correction, read WHOLE. C-32 exists because a brief of mine named a
  section and hid the decisive probe.
- `_build/lj-1.46-report.md`, which surfaced this, and
  `_build/lj-1.21-report.md`, which took `sq` as a parameter.
- `dev/LESSONS.md` is NOT archived and still binds.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

- `dev/literature/devlin-II5.md` for what 5.5 and 5.6 assume about cardinal
  arithmetic. **Devlin does not prove it; he assumes it.** Say in one line what
  he assumes, because that is the boundary of what must be built.
- The errata do NOT cover Chapter II section 5. `[LJ-1.14]` verified it. **Do
  not re-check it.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## SCOPE (read)

`_build/lj-1.46-report.md` FIRST, then
`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md`, then
`src/L/StageCardinal.lagda.md` for what consumes `sq`, then `dev/LESSONS.md`
P-l, P-m, P-n, P-q, P-t and P-v whole.

## SCOPE (write)

`src/ProbeLJ147*.agda` only, and your report `_build/lj-1.47-report.md`. **No
master. No file under `dev/`. Never `src/Everything.lagda.md`.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for probe` and `--for recon`, and read every
statement.

- **D-1.** The smallest decisive miniature, GO or NO-GO with a price, thrown
  away.
- **D-10.** Every figure here is a residue, **including the 41.36 seconds and
  the 1,283 lines.** Re-verify before you build on them.
- **D-26.** A well-founded key on a tower needs generation data or syntax.
  **Say in one line whether it bears.**
- **P-l, P-m, P-n, P-q, P-t, P-v** as above.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **Report a heap exhaustion as a WALL with its seconds.**
- **C-22.** Write the deliverable incrementally.
- **C-31.** A budget from a projected size is divided by the projected size.
- **C-32.** A cure invalidates downstream measurements. **Interfaces live in
  `_build/2.8.0/agda/src/`, NOT beside the source**: deleting a `.agdai`
  beside a `.agda` removes nothing and turns a cold run into a warm read.
- **C-34.** Build the cure or report the wall.
- **C-36.** A failed substitution is not a proof of impossibility.

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- **Repeat every timing at least three times and report the spread.**
  Run-to-run variance on this machine is about 5 to 10 percent and the verdicts
  here are inside that band.
- **The machine is quiet and both Agda slots are yours.** I am holding a second
  probe back so your timings are clean. Say if that changes.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.47-report.md` incrementally, skeleton first.

Lead with the verdict: the square law's content class, whether it can change,
and the measured delta if it can. Then what the CONSUMER actually needs, since
a weaker law may cost a fraction. Then the profile attribution, the spread
across your repeats, the DD4 answer, and what you are not sure of.
