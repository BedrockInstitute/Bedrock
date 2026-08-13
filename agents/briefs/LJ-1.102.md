# LJ-1.102: restate ONE row in tied form and re-prove it

tier: codex (default)

## GOAL

**Measure the last unmeasured thing in the repair.** The ties close at the
sites and the extended frame supplies everything else. **Nobody has checked
that a row's PROOF survives when its hypotheses are restated in tied form.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`563c0d5` except `dev/PLAN.md`. HEAD is green. **A sibling agent holds the
other Agda slot.**

## WHAT IS MEASURED, and I re-ran the decisive check myself

**`[LJ-1.100]`: 39 unsolved metas became 11.** I re-ran
`src/ProbeLJ1100A.agda`: exit 42, **exactly eleven unsolved interaction
metas** at `:380`, `:384`, `:386-389`, `:396-398`, `:401-402`, **and no
other error**, so the 28 added supplies typecheck.

**The 11 are exactly the eleven refuted facts.** They have no supplier
because their stated types are EMPTY. **No frame extension can supply an
empty type. The types must change.**

**`[LJ-1.99]`: the tied types close at the row sites**, GREEN. Four `arityK`
steps for `entryK`, one for `arSubK-*`, and the rows bind `E ∈ K`,
`ar ∈ K`, `a ∈ K`.

**So the repair has one unmeasured step left: does the ROW still prove
itself once its hypotheses carry the ties?**

## WHAT TO BUILD

**Take ONE row and restate it.** `MemAgree`
(`src/L/Condensation.lagda.md:4141-4240`) is the candidate: `[LJ-1.98]` and
`[LJ-1.99]` both tabled its use lines (`EK` at `:4195`, `entryK` at
`:4201`, `valK` at `:4216`, `back` `EK` at `:4219`). **Verify those in the
source; do not take them from a report.**

1. **Copy the row into a probe** with its telescope, and **replace every
   refuted hypothesis it takes by its tied form**. The tied forms are in
   `src/ProbeLJ199A.agda`. **Read them there.**
2. **Re-prove the row's `out` and `back`**, supplying the ties from the
   row's own binders.
3. **Report: does the row still prove itself?** With the term at
   `file:line`, the seconds, and the lines changed against the original.

**If `MemAgree` turns out to be a bad choice, say why in one line and pick
another row that uses `entryK` and `arSubK`. Say which you picked.**

## THE ABORT CRITERION, fixed in advance per D-1

- **The row proves itself in tied form**: report it with the diff size and
  STOP. **Do not do a second row.** That measurement makes the other eleven
  rows a price rather than a question, and it needs auditing first.
- **A step of the row's proof does NOT survive**: STOP there, write the term
  you could not write, and say **which use of which hypothesis needed the
  untied form.** **That is the more valuable outcome and it would mean the
  row proofs used the over-generality, which is the one thing that would
  make retirement the honest answer.**
- **Anything walls**: STOP, report the wall with its seconds.

**Work in `src/ProbeLJ1102*.agda`. Do not touch any master.**

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
  statement it proves today. **If the tied form forces a weaker conclusion,
  that is the finding and you stop.**
- **Do not add a hypothesis to the row to make the tie available.** The tie
  must come from the row's own binders. `[LJ-1.99]` measured that they are
  there.
- **Do not repair, delete or archive any master.**
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and counts from the source, never from a report.**
  **Two returns this session called delivered content absent, and both were
  caught by reading the source.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**The tied forms are more generic than what they replace**, because they say
what they mean instead of over-quantifying. **Say whether the restated row
is still generic in its slots, and whether the J tower gets it unchanged.**

## THE COST QUESTION

The wing is over DD24 and the owner ruled the threshold question is settled
when the phase's content is complete. **So measure, do not gate.** Report
the restated row's cold seconds and its non-blank in-fence lines against the
original's, with the load average.

## ARCHIVE (DD18)

- **`src/ProbeLJ199A.agda`**, read WHOLE, and `_build/lj-1.99-report.md`.
  **The tied forms and the per-row supply table. This is your starting
  material.**
- **`_build/lj-1.100-report.md`**, read WHOLE, and `src/ProbeLJ1100A.agda`.
  The extended frame and the eleven that remain.
- `_build/lj-1.97-report.md` and `src/ProbeLJ197A.agda`, the ten
  refutations.
- `_build/lj-1.96-report.md` and `_build/lj-1.98-report.md`, the two
  consumer-side negatives and the per-use tables.
- `src/L/Condensation.lagda.md:4141-4240`, the Mem row, and `:2764-2870`,
  `EnvSet`.
- `src/L/Condensation/TwelveAgree.lagda.md:45-243`, the composer's frame.
- `dev/LESSONS.md` **C-38 as extended**, C-35, C-36, D-29, D-30, P-i, P-w,
  read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** Say so in one line.

## SCOPE (read)

`src/ProbeLJ199A.agda` FIRST, then `src/L/Condensation.lagda.md:4141-4240`,
then `:2764-2870`.

## SCOPE (write)

`src/ProbeLJ1102*.agda` only. Your report is `_build/lj-1.102-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it. **A tied hypothesis supplied from the row's own binders is a
  discharge; a tied hypothesis added to the telescope is not.**
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

Write `_build/lj-1.102-report.md` incrementally, skeleton first.

**Lead with whether the row proves itself in tied form**, in the word YES or
NO, with the term at `file:line` and its seconds. Then the diff size: lines
changed, hypotheses restated, ties supplied and from which binder. Then, if
a step did not survive, the term you could not write and which hypothesis
needed the untied form. **Mark every negative MEASURED or INFERRED.** Then
the DD4 answer. Confirm no master was touched.
