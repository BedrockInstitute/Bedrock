# LJ-1.112: instantiate the repaired composer

tier: codex (default)

## GOAL

**Be the consumer of the repaired frames.** The eleven refuted names are
gone from all three. **Nothing has instantiated them since. Do it, and
report the unsolved-meta count.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`ee7e051`. `make check` passes.** A sibling agent works on the cardinal side
and will not touch anything under `src/L/Condensation/`.

## WHAT IS MEASURED, and I confirmed the repair with an independent tool

`[LJ-1.110]` restated all three frames. **`make check` passes: I ran it.**
Frame fact counts fell from 43, 43 and 69 to **37, 36 and 59**. The eleven
refuted hypotheses became `arityK`, `sucK`, and the site memberships the
rows already bind. The five tied key facts are DERIVED, not stated.

**`scripts/check-unbound-hyp.py`, written before the repair and blind to
it, flagged all eleven on the old frames and now flags six**: `valK` and
`valK-un` in each of the three, which `[LJ-1.97]` found to be the same shape
and could not refute. **So the eleven are gone by an instrument that never
saw the fix.**

## THE MEASUREMENT THIS DISPATCH TAKES

`[LJ-1.93]` measured **39** unsolved metas instantiating `AbstractFrame`
against the consumer's frame. `[LJ-1.100]` extended the consumer's frame and
measured **11**, and those eleven were exactly the refuted names, whose
types were empty.

**The frames no longer state them. Re-run the instantiation and report the
new count.**

1. **Start from `src/ProbeLJ1100A.agda`**, which carries the extended
   consumer frame (module `At`, module `Extended`). **Read it whole. Do not
   rebuild it.**
2. **Re-point it at the CURRENT `TwelveAgree.AbstractFrame`.** The telescope
   changed: read it in the source, not from any report.
3. **Add `sucK` to the extended consumer frame**, which `[LJ-1.110]`'s C-39
   section says the consumer must now supply:
   `sucK : (a : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ sucV (fst a) ∈ fst (lookup K γ) ⟩`.
   **Say what would inhabit it, at `file:line`, and TRY TO REFUTE IT.**
   `[LJ-1.109]` named the inhabitant as a constructibility level closed
   under V-successor and marked it NOT REFUTED, INFERRED.
4. **Report the new unsolved-meta count, with 39 and 11 beside it.**

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**Every addition to the consumer frame is a new hypothesis, not a discharge.
Say so in those words for each, and name what would supply it at
`file:line`.** C-38.

**Try to refute every fact you add.** `src/ProbeLJ197A.agda` is the shape,
and **`scripts/check-unbound-hyp.py` will tell you which of your additions
are worth attacking: run it on your probe.** Rule 3 catches a premise-free
telescope, rule 1 an unconstrained conclusion subject, rule 2 an
unconstrained premise object.

## THE ABORT CRITERION

- **The count reaches zero**: report the term and STOP. **That would mean
  the composer is instantiable for the first time, and it is the phase's
  acceptance test.**
- **The count does not reach zero**: report the number and **name every
  hypothesis still unsupplied, at `file:line`**. A number is the deliverable
  either way.
- **An addition is refutable**: STOP and report it. **That has happened
  seven times this phase and it is the most valuable outcome.**
- **Anything walls**: STOP, report the wall with its seconds.

**Do not stop at the first negative.**

**Work in `src/ProbeLJ1112*.agda`. Do not touch any master.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken any frame's conclusion.**
- **Do not add a fact whose only justification is that it closes the
  instantiation.** An empty type closes it for the wrong reason, and that is
  how this phase lost a thousand lines.
- **Do not touch any master**, and in particular nothing under
  `src/L/Condensation/`, `src/L/Coding/` or `src/V/`.
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and counts from the source, never from a report.**
  **All three frames moved an hour ago.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**`[LJ-1.93]` set the test that matters: sharing is only free when the
shared frame is the frame the consumer actually holds. This dispatch is that
test, at last, against a repaired frame. Answer DD4 with the count.**

## ARCHIVE (DD18)

- **`_build/lj-1.110-report.md`**, read WHOLE. **The restated frames, the
  per-frame fact counts, and its C-39 section naming `sucK` as the
  consumer's new obligation.**
- **`src/ProbeLJ1100A.agda`**, read WHOLE, and `_build/lj-1.100-report.md`.
  **The extended consumer frame. This is your starting material.**
- `_build/lj-1.109-report.md`, the tied key facts and P-x.
- `src/ProbeLJ197A.agda`, `src/ProbeLJ195A.agda`, the refutation shape.
- `src/L/Condensation/TwelveAgree.lagda.md`, the CURRENT frame.
- `src/L/Condensation.lagda.md`, the `KFacts` record and the consumer's
  telescope. **Find them by name, not by line.**
- `dev/LESSONS.md` **C-38 as extended, C-39, C-40, P-x**, C-35, C-36, D-29,
  D-30, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** Say so in one line.

## SCOPE (read)

`src/ProbeLJ1100A.agda` FIRST, then the current
`src/L/Condensation/TwelveAgree.lagda.md` telescope, then
`_build/lj-1.110-report.md` section 3.

## SCOPE (write)

`src/ProbeLJ1112*.agda` only. Your report is `_build/lj-1.112-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it. **An addition to a frame is a new hypothesis, not a discharge.**
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.**
- **C-40.** Verify the CONSUMERS of a changed master, never the master
  alone.
- **C-35, C-36, D-29, D-30, D-10.**
- **P-x.** A transparent construction in a record field type is paid by
  every elaboration of the record. **`sucK` stays out of `KFacts`.**
- **P-i, P-w, P-h, P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the
  bundle gives them.
- **P-c, R-36, R-38, R-35, R-40.**
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-8, D-26.**

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

Write `_build/lj-1.112-report.md` incrementally, skeleton first.

**Lead with the unsolved-meta count**, with 39 and 11 beside it. Then every
hypothesis still unsupplied, by name at `file:line`. Then every addition you
made, what would supply it, and whether you tried to refute it. Then what
`check-unbound-hyp.py` says about your probe. Then the C-39 section. **Mark
every negative MEASURED or INFERRED.** Then the DD4 answer with the count.
