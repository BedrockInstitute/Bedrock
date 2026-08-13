# LJ-1.116: at which alpha does Upper actually need sq?

tier: codex (default)

## GOAL

**Ask D-30's question instead of paying the general price.** The truncated
square law cannot pass through `Upper`'s induction. **Find out whether
`Upper` ever needs `sq` at an ordinal where the honest one is
unconstructible.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`1f68a67`. `make check` passes.** A sibling agent works on the coding side
in probes only.

## WHAT IS MEASURED, and the negative is clean

`[LJ-1.114]` attempted the threading in the master and **it does not land.**
The tree is clean: the agent reverted, and I confirmed it.

**The wall is `Upper.LimitStep`'s `h-inj`.** The least-code injectivity
proof compares two class witnesses. **Each witness carries its own honest
branch injection, extracted from its own elimination of the truncated
induction hypothesis**, and count injectivity needs the SAME injection on
both sides. Agda refuses with `g₂' != g₁`.

**The mathematical fact behind the refusal is proved, not guessed**:
`src/ProbeLJ1114A.agda`, GREEN, exit 0 when I re-ran it. The tuple code is
injective per injection and **two distinct tuples collide across two honest
injections** (`collision : refl` at `:89-90`, `tuples-differ` at `:92-94`).

**Every alternative placement of the elimination is closed**, and the return
lists them: eliminating inside `Upper.step` (no proposition point),
eliminating nowhere (needs the honest `sq` at non-initial α, which
`[LJ-1.107]` measured unconstructible), restating `branch` per step (the
family is data), and any `leastOf` extraction (the same refusal, plus the
same cross-injection collision).

**`Devlin55` is NOT the blocker.** The return says that if `Upper` delivered
the truncated injection, the assembly could eliminate it at the two
proposition points `src/L/BoundedSubset.lagda.md:1594` and `:1605`. That
half is **INFERRED**, because the prerequisite never compiled.

## THE QUESTION THIS DISPATCH ASKS

**D-30: price what the CONSUMER needs.** Nobody has checked which `α` the
consumer actually applies `sq` at.

1. **Follow the applications.** `Devlin55` applies `stage-card-upper α ordα
   α∉ω` (`src/L/BoundedSubset.lagda.md:1530` area, VERIFY). `Upper`'s
   `∈-induction` then descends. **At which `α` is `sq α` demanded?** The
   site's own `α`, its members, or every infinite ordinal below it?
2. **Is `Init α` available at those `α`?** If the demand is only at
   cardinals, the delivered `via-col-square`
   (`src/L/Ordinal/SquareLaw.lagda.md:960-961`) supplies the honest `sq`
   and the whole truncation question dissolves.
3. **If not, could `StageCardinal` take `Init α` instead of `sq α`?**
   `[LJ-1.106]` proved `Init` at the Hartogs cardinal outright, no
   hypothesis left (`src/ProbeLJ1106A.agda:573-574`). **Say whether the
   consumer can supply `Init` at every `α` the induction reaches.**
4. **`[LJ-1.94]`'s site takes `α = ω`.** `sq ω` is honest, from the ℕ
   pairing (`src/ProbeLJ1106A.agda`, `NumeralPresentation.pairω`).
   **Does the whole site instance go through with `sq` demanded only at
   `ω` and its members?** **Machine-check it if it is small.**

**This is a reading and pricing task with one machine check. Do not rewrite
`StageCardinal`.**

## THE ABORT CRITERION

- **The demand is only at ordinals where `Init` holds, or only at `ω`**:
  report it with the machine check and STOP. **That would dissolve the
  truncation question and it is the answer I most want checked rather than
  assumed.**
- **The demand really is at every infinite ordinal below the site**: report
  it, and say what that leaves. **Then the truncation wall is load-bearing
  and the finding goes to the owner.**
- **Anything walls**: STOP, report the wall with its seconds.

**Do not stop at the first negative: the brief asks four questions.**

**Work in `src/ProbeLJ1116*.agda`. Do not touch any master.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not assume the axiom of choice.** Six dispatches measured this chain
  choice-free, and choice would dissolve the truncation for the wrong
  reason. **Say at once if a route needs it.**
- **Do not weaken any theorem's conclusion.**
- **Do not touch any master.** `[LJ-1.114]` already tried the master edit
  and reverted it; repeating that costs a dispatch.
- **Do not touch `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**Say whether restricting the hypothesis changes what the J tower
inherits.**

## ARCHIVE (DD18)

- **`_build/lj-1.114-report.md`**, read WHOLE, and **`src/ProbeLJ1114A.agda`**.
  **The wall, its measured mathematical cause, and the four closed
  alternatives. Do not repeat any of them.**
- **`_build/lj-1.111-report.md`** and `src/ProbeLJ1111A.agda`, the proved
  truncated chain.
- `_build/lj-1.107-report.md`, the unconstructible honest injection.
- `_build/lj-1.106-report.md` and `src/ProbeLJ1106A.agda`, `Init` and `sq`
  at the Hartogs cardinal, and the `ω` pairing.
- **`src/L/StageCardinal.lagda.md`, the whole `Upper` module**, and
  `:15-17` for the `sq` parameter.
- **`src/L/BoundedSubset.lagda.md:1361-1627`**, `Devlin55` whole.
- `dev/LESSONS.md` **D-30, C-38 as extended, C-39, C-40**, C-36, D-1, D-8,
  P-l, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Say in two lines at which ordinals Devlin's 5.5 uses the square law**,
from `dev/literature/devlin-II5.md`. **This is the one place the literature
can settle the question cheaply, so spend a little here.**

## SCOPE (read)

`src/L/StageCardinal.lagda.md`'s `Upper` module FIRST, then
`src/L/BoundedSubset.lagda.md:1520-1540`, then `_build/lj-1.114-report.md`
section 1.

## SCOPE (write)

`src/ProbeLJ1116*.agda` only. Your report is `_build/lj-1.116-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for recon`, and read every
statement.

- **D-30.** Price what the CONSUMER needs. **This brief IS D-30.**
- **D-8.** One best-effort figure with its basis named, and the widest
  unmeasured term.
- **C-36.** Write the term you could not write.
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.**
- **C-40, C-38 as extended, C-35, D-10, D-29.**
- **P-l.** A price from a comparable elsewhere is a hypothesis.
- **P-x, P-i, P-w, P-h, P-k, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the
  bundle gives them.
- **P-c, R-36, R-38, R-35, R-40.**
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-26.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- **Run `scripts/check-unbound-hyp.py` on your probe** and report what it
  says.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.116-report.md` incrementally, skeleton first.

**Lead with the set of `α` at which `sq` is demanded**, at `file:line`, and
whether `Init` holds there. Then whether `StageCardinal` could take `Init`
instead. Then the `α = ω` site check, machine-checked if small. Then what
Devlin assumes. Then the C-39 section. **Mark every negative MEASURED or
INFERRED.** Then the DD4 answer.
