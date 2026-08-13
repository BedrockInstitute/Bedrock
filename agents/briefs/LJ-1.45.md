# LJ-1.45: restate the agreement layer in ONE spelling

tier: codex (default)

## GOAL

`[LJ-1.44]` located 79 percent of Condensation's seconds and measured a cure.
**Land it.** The mathematics must not change: all twelve row agreements and
block 1 are closed and must stay closed.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`8019b6a`.

## THE FINDING AND THE CURE, both measured

The expensive class is the **row-agreement layer**
(`src/L/Condensation.lagda.md:2947-4943`): satisfaction-level transfer at built
formulas with concrete indices, whose types name **two spellings of each leaf**,
the story's bounded formula and the machine's unbounded one. That is the
**P-t and P-v** family.

It carries **48.8 of the 61.6 profile seconds, about 79 percent**. The import
cone is 1.28 s, so the cone is not the story.

**The cure, measured rather than argued (C-34):** restate the same theorem in
ONE spelling, carrying the bound as a **meta-level membership hypothesis**
instead of a second object-language spelling. At the hottest row,
`PropAgree.subB2T` falls from **883 ms to 87 ms**, 10.1x
(`src/ProbeLJ144D.agda` against `src/ProbeLJ144E.agda`).

**I verified the DIRECTION myself and not the per-definition figure**: both
probes are green cold, D at 2.69 s and E at 1.94 s whole-file. Re-derive the
10.1x with a profile before you rely on it (D-10).

**The back direction of that pair is FLAT.** Its residual is the K-membership
derivation, which is content and not a spelling artefact. **So expect the cure
to help one direction and not the other, and report both.**

## THE BAR, and it is not what my earlier briefs said

**DD24's live bar is 0.0127**, computed from the AC baseline 0.011057 times the
1.15 tolerance. The AC baseline was re-measured DOWN on 2026-08-11 and the bar
came down with it. **Three earlier briefs of mine quote a stale 0.013193.**
Re-derive it from `dev/ledger.toml` yourself.

Today: `Condensation` is **4,512 lines at 0.0144, OVER**; the GCH aggregate is
**0.0131 over 6,407 lines, OVER**. **Run-to-run variance is about 10 percent
and the breach is 3 to 13 percent, so repeat every measurement at least three
times and report the spread.**

## WHAT MUST NOT CHANGE

- **All twelve row agreements and block 1 stay CLOSED.** They are
  machine-checked. **If a restatement cannot close a row, revert that row and
  report it**; do not weaken an agreement to make it fast.
- **ZERO placement.** No `absFo`, no `placeFo`, no placed `Δ₀` (P-u). That wall
  is flat at 8 GB.
- **No `postulate`, no `TERMINATING`, no hole.** The master is `--safe`.

## WHAT TO WATCH, from this file's own history

- **`scripts/check-fences.py --check` before you report anything closed.**
  `[LJ-1.41]` reported two agreements closed that sat OUTSIDE the ` ```agda `
  fence as prose, carrying four defects, and every other gate passed.
- **C-35: the agreement IS the consumer.** A row is not restated until its
  agreement closes again.
- **C-36: a failed substitution is not a proof of impossibility.** If a
  restatement will not typecheck, write the term you could not write.
- **You may strengthen a statement; you may not weaken one.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker, so it is stated in every brief and answered in
every return.

`[LJ-1.44]` should have said which side the expensive class falls on. **Say it
in your return**: if the two-spelling cost is in the shared frames, the J tower
inherits it and the cure pays twice; if it is per-tower Def content, the J
tower's structural certificate may avoid it (D-26).

## ARCHIVE (DD18)

**Nothing in the archives bears, and I name them rather than omit the section.**
`archive/rud-route/`'s `Condensation` was measured at 0.395 s per line but
`[LJ-1.11]` showed its target is classically FALSE, so it prices nothing.
`archive/dev/TASKS-archived.md`, `JOURNAL-archived.md` and
`DECISIONS-archived.md` cover the retired `D` series.

**What bears is not archived**: `dev/LESSONS.md`, and the live reports
`_build/lj-1.44-report.md`, `_build/lj-1.43-report.md` and
`_build/lj-1.39-report.md`. **Read those whole**, and the probes
`src/ProbeLJ144D.agda` and `E`.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in `dev/literature/` bears.** This is an elaborator cost restatement
on this tree's own code. `devlin-II5.md` prices the mathematics and says
nothing about check cost. **Say so in one line and spend nothing.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## SCOPE (read)

`_build/lj-1.44-report.md` and the two probes FIRST, then
`src/L/Condensation.lagda.md:2947-4943`, then `dev/LESSONS.md` P-l, P-m, P-n,
P-q, P-t and P-v whole.

## SCOPE (write)

`src/L/Condensation.lagda.md`, plus `src/ProbeLJ145*.agda` if you need them.
Your report is `_build/lj-1.45-report.md`. **No other master. Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l.** Naming a built construction in a statement's TYPE is what costs.
- **P-m.** The rate certifies the content class.
- **P-n.** Satisfaction at a concrete carrier is a payable floor.
- **P-t.** The class follows the FORMULA, not the carrier.
- **P-u.** Certify before you place.
- **P-v.** One formula, one spelling, decided at the formula level. **This is
  the law you are applying.**
- **R-35, R-38, R-40, I-5.**
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, one process, cap never
  raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-36. D-10, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck the master and every consumer. Do NOT run `make check`.
- Count with `scripts/ledger.py`. Report cold seconds three times, the marginal
  rate, and the module-load cone separately.
- Run `scripts/lint-prose.py --check`, `scripts/lint-agda.py --check` and
  `scripts/check-fences.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.45-report.md` incrementally, skeleton first.

Lead with the verdict: the new whole-file rate against 0.0127, with the spread
across three runs, and whether all twelve agreements plus block 1 still close.
Then the per-direction deltas, since the back direction is expected flat. Then
any row you had to revert. Then the numbers, the DD4 side, and what you are not
sure of.
