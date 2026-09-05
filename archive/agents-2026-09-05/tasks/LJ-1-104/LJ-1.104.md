# LJ-1.104: give the row arityK, and re-prove it in tied form

tier: codex (default)

## GOAL

**Re-run `[LJ-1.102]` without the prohibition that blocked it.** The row
failed for one reason and the reason is a missing hypothesis that the
consumer already holds.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`b07d411` except `dev/PLAN.md`. HEAD is green. **A sibling agent holds the
other Agda slot and it may be editing `src/L/BoundedSubset.lagda.md`. Do
not touch that file.**

## WHAT `[LJ-1.102]` MEASURED, and why it is not the end

It restated `MemAgree`'s three refuted facts in tied form and the row did
NOT prove itself. **Both measurements are real and both are useful:**

- **The `Chain` tie** (premise `z ∈ E`) closes `EnvSet.out`'s FIRST
  component and leaves the second unsolved: the second has only `z ∈ K`,
  from `envInK z hz`.
- **The `ChainZ` tie** (premise `z ∈ K`) closes the SECOND and leaves the
  first unsolved: the first has `z ∈ E`.

**One tie, two components, two different premises.** The two are one
`arityK` step apart: `z ∈ E` and `E ∈ K` give `z ∈ K`.

**The row's telescope has no `arityK` and no `transK`**
(`src/L/Condensation.lagda.md:4142-4185`, MEASURED by listing). **That is
the whole obstacle.**

**My brief forbade adding a hypothesis to the row. That prohibition was
written to stop invented facts, and it stopped a delivered one instead.**
`arityK` is a field of the consumer's own `KFacts`
(`src/L/Condensation.lagda.md:5769-5770`), and `transK` is already a fact
of the composer's frame (`src/L/Condensation/TwelveAgree.lagda.md:167-169`).
**Neither is invented. Both are held.**

## WHAT TO DO

1. **Add `arityK` to the row's telescope**, in the `KFacts` field's exact
   shape, and use the **`ChainZ`** tie (premise `z ∈ K`) for `entryK`.
2. **Close the first component** by `arityK` from the row's `z ∈ E` and its
   `EK` binder (`src/L/Condensation.lagda.md:4195`, derived at `:4219`).
3. **Prove BOTH directions**, `out` and `back`. `[LJ-1.102]` never reached
   `back`.
4. **Report the diff**: the telescope's line count before and after, and
   the row's cold seconds.

**`src/ProbeLJ1102A.agda` already carries both tie forms and both EnvSet
copies. Start from it. Do not rewrite what is already there.**

## THE ONE RULE THAT STILL BINDS

**Every hypothesis you add must be one the CONSUMER can supply.**

- `arityK`: a `KFacts` field. **Supplied. Say so at `file:line`.**
- **Anything else you add: say what supplies it, at `file:line`, before you
  add it.** If nothing supplies it, **do not add it, and report the term you
  could not write instead.**
- **Try to refute every tied form you use**, the way `src/ProbeLJ197A.agda`
  does. **A tie that is itself an empty type would close the row for the
  wrong reason, and that is how this phase lost a thousand lines.**

## THE ABORT CRITERION, and it is deliberately generous this time

- **Both directions prove**: report the diff and the seconds and STOP. **Do
  not do a second row.**
- **One direction proves and the other does not**: report both, with the
  term you could not write. **That is still a good return.**
- **Neither proves**: report where, and **say what else the row would have
  to hold, at `file:line`, and whether the consumer holds it.**
- **Anything walls**: STOP, report the wall with its seconds.

**Do not stop at the first negative. Two of my abort criteria this session
have each hidden a live route, and this brief is the second correction.**

**Work in `src/ProbeLJ1104*.agda`. Do not touch any master.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken the row's conclusion.** The row must prove the SAME
  statement it proves today.
- **Do not touch `src/L/BoundedSubset.lagda.md`.** A sibling agent is
  repairing it.
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
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

**A tied hypothesis says what it means instead of over-quantifying, so it is
the more generic form.** Say whether the restated row stays generic in its
slots, and whether `EnvSet` itself should carry `arityK` rather than every
row that uses it. **That second question is the DD4 question here: nine rows
use `EnvSet`.**

## THE COST QUESTION

The wing is over DD24 and the owner ruled the threshold question is settled
when the phase's content is complete. **So measure, do not gate.** Report
the row's cold seconds and non-blank in-fence lines against the original's,
with the load average.

## ARCHIVE (DD18)

- **`_build/lj-1.102-report.md`**, read WHOLE, and **`src/ProbeLJ1102A.agda`**,
  read WHOLE. **Both tie forms and both EnvSet copies are already built
  there. This is your starting material.**
- **`src/ProbeLJ199A.agda`** and `_build/lj-1.99-report.md`, the chain and
  the per-row supply table.
- `src/ProbeLJ1100A.agda` and `_build/lj-1.100-report.md`, the extended
  frame and the eleven that remain.
- `src/ProbeLJ197A.agda`, the refutation shape you must use on every tie.
- `src/L/Condensation.lagda.md:4141-4240`, the Mem row; `:2764-2874`,
  `EnvSet`; `:5734-5770`, `KFacts`.
- `dev/LESSONS.md` **C-38 as extended**, C-35, C-36, D-29, D-30, P-i, P-w,
  read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** Say so in one line.

## SCOPE (read)

`src/ProbeLJ1102A.agda` FIRST, then `src/L/Condensation.lagda.md:2764-2874`,
then `:4141-4240`.

## SCOPE (write)

`src/ProbeLJ1104*.agda` only. Your report is `_build/lj-1.104-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it. **`arityK` is supplied by `KFacts`; say so at `file:line`.**
- **C-35.** A block with no consumer is UNTESTED.
- **C-36.** Write the term you could not write.
- **D-30.** Price what the CONSUMER needs.
- **P-i.** The conversion-explosion playbook. **Read it whole; heavy
  hypothesis packs go as module Pi-parameters, never as records.**
- **P-w.** A module application COPIES, and the copy is paid at USE.
- **P-h, P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle gives
  them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-8, D-10, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.104-report.md` incrementally, skeleton first.

**Lead with whether the row proves BOTH directions in tied form**, in the
words YES or NO for each, with the terms at `file:line` and their seconds.
Then the diff size. Then every hypothesis you added and what supplies it.
Then whether each tie survived your refutation attempt. **Mark every
negative MEASURED or INFERRED.** Then the DD4 answer, including whether
`EnvSet` should carry `arityK` for all nine rows. Confirm no master was
touched.
