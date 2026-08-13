# LJ-1.156: does A5 need `CSB` at all?

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`CSB` is the last unknown in Route A-prime.** Two dispatches have now stripped
A5's seconds problem down to this one object.

**Settle it: is `CSB` needed at all, and if it is, does it force a
`hasReplacementL` back into the chain?**

## WHERE A5 STANDS, and every figure is somebody's measurement

| finding | source |
|---|---|
| the composite composes with NO second `hasReplacementL`, 2.50 s | `[LJ-1.152]` |
| the identity graph CARVES by separation, 1.73 s against 254.22 | `[LJ-1.154]` |
| one `hasSeparationL` under 0.1 s, one `hasReplacementL` 259 to 269 s | `[LJ-1.152]` |
| Devlin's base theory has NO replacement at all | `[LJ-1.154]`, `devlin-errata.md:180` |
| **`CSB` is the only object that can put a replacement back** | `[LJ-1.152]` and `[LJ-1.154]` both |

**`[LJ-1.152]`'s reason, and it is the one to test:** `CSB`'s graph is a
**back-and-forth recursion**, not a first-order condition on pairs. **A
separation carves a subset out of something you already have. A recursion
builds.**

## THE FIRST QUESTION, and it may dissolve the whole thing

**`[LJ-1.136]` claimed `CSB` can be removed from the chain entirely**, and
marked it **INFERRED, and it has never been tested.** Its words: 「if it holds
it is the largest single saving in the route」.

**The claim:** `[LJ-1.107]` states leastness over **BIJECTIONS**, and **that is
the only reason `CSB` is in the chain at all**. State leastness over
**INJECTIONS** instead and all three `CSB` sites refute directly:

- the square clause's composite **IS** an L-injection with the right membership;
- `ShiftAbs` **IS** an L-injection;
- `NonInitial` wants two injections and no equivalence.

**`[LJ-1.136]` section 9.1 tabulates all three. Read it, then TEST it.**

**MEASURED and worth repeating: `CSB` does not exist anywhere in `src/`.** Zero
hits; it lives only in archived probes. **So nothing is being removed from the
delivered tree. The question is whether it must be ADDED.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **DISSOLVED** if leastness over injections closes all three sites and the
  chain never needs `CSB`. **Then A5 loses its last unknown and the block
  prices.** State which three sites and show each closing.
- **NEEDED, AND CHEAP** if `CSB` is required but carves or composes without a
  `hasReplacementL`, under 30 s. **Then A5 still prices.**
- **NEEDED, AND EXPENSIVE** if `CSB` forces a replacement. **Then A5 carries one
  replacement at 259 to 269 s and the block's price is that plus the rest.**
  **That is a complete answer and it finally PRICES A5**, which has been
  unpriced since `[LJ-1.131]`.

**All three outcomes price the block. There is no outcome here that leaves A5
unpriced, so do not stop short of one of them.**

## THE C-38 GUARD

**An interface nothing satisfies is a restatement, not a supply.** Instantiate
at a real injection pair. `[LJ-1.136]` nearly shipped a vacuous probe and its
own guard caught it; `[LJ-1.154]` instantiated at a concrete singleton and
proved the carved object was exactly right.

**If you conclude DISSOLVED, the burden is higher, not lower**: you must show
each refutation closing at a real site, not argue that it would.

## THE TRAP MEASURED THREE TIMES TODAY

**A measured cure does not transfer by analogy. P-l.**

- The `opaque` seal that cured Condensation moved `[LJ-1.152]`'s site by
  nothing.
- `[LJ-1.154]` then measured that its own seals were not load-bearing either.
- `[LJ-1.152]`'s composition device did not obviously transfer to construction,
  and `[LJ-1.154]` had to find a new index to make it work.

**So do not assume the separation device reaches `CSB` because it reached the
other two. Measure it.**

## WHAT YOU MUST NOT DO

- **Do not edit any master.** This is a probe.
- **Do not touch `src/L/Condensation.lagda.md` or the three `*Agree`
  masters.** `[LJ-1.155]` is profiling them right now.
- **Do not touch `src/ProbeLJ1134A.agda` or `src/ProbeLJ1136*.agda`.**
- **A probe goes in `agents/tasks/LJ-1-156/`**, never in `src/`, tracked, never
  deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
  `[LJ-1.155]` is measuring seconds. **Discard a warm-up, take at least three
  kept runs for any figure a decision rests on, and report the load beside
  every absolute figure.**
- **Report a heap exhaustion as a wall.** `[LJ-1.136]` hit three at this site
  and the walls were the finding.
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **`[LJ-1.136]`'s dissolution claim is
INFERRED and it is the thing you are here to convert or refute.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

`[LJ-1.136]` recorded that `CSB` is generic and would serve the other trophy
too. **`[LJ-1.154]` made its carve generic in the index type AND the family, so
90 of its lines re-instantiate for J.** **If `CSB` survives, say whether it can
take the same shape.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-136/lj-1.136-report.md` section 9.1**, read WHOLE. **The
  three `CSB` sites and the dissolution argument you are testing.**
- **`agents/tasks/LJ-1-154/lj-1.154-report.md`** and `ProbeLJ1154A.agda`, read
  WHOLE. The carve device and its generic shape.
- **`agents/tasks/LJ-1-152/lj-1.152-report.md`**, for why `CSB` was singled out.
- `agents/tasks/archive/LJ-1-107/ProbeLJ1107A.agda:99-207` and `:489-490`,
  where `CSB` is actually built and used.
- **`dev/LESSONS.md` P-l, P-y, C-38 as extended, C-12, D-1**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md`, `devlin-errata.md`, `rudimentary-functions.md`.
**`[LJ-1.154]` MEASURED that Devlin's base theory has no replacement and that
the rud basis delivers the product outright.** **Say whether Devlin's own
square-law argument uses a Cantor-Schroeder-Bernstein step at all, or whether
it is an artifact of our stating leastness over bijections.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-136/lj-1.136-report.md` section 9.1 FIRST, then
`agents/tasks/archive/LJ-1-107/ProbeLJ1107A.agda:99-207`.

## SCOPE (write)

`agents/tasks/LJ-1-156/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.

- **D-1.** The abort criterion fixed BEFORE the run.
- **C-38 as extended.** Instantiate, or a DISSOLVED verdict is an argument
  rather than a measurement.
- **P-l.** Measured three times today at this very cluster.
- **P-y, P-w, P-m, P-s, C-12, C-22, C-36, C-39, C-40.**
- **DD8, D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with DISSOLVED, NEEDED AND CHEAP, or NEEDED AND EXPENSIVE, and then with
A5's price**, which one of the three must now give. Then the three sites, each
shown closing or not. Then the seconds with load and run count. Then what
Devlin does. Then the DD4 answer. **Mark every negative MEASURED or INFERRED.**
