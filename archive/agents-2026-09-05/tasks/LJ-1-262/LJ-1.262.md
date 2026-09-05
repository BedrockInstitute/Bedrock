# LJ-1.262: the DD25 review `[LJ-1.225]` never got, dispatched late and said so

tier: opus (deepseek-subagent-mode). **The switch's ADVERSARIAL row, taken as
the table gives it.** The target was written by pi, so DD17's invariant holds:
the critic is never the same head as the author.

## GOAL

**`make check` went RED on DD25 and it was right about one row of four.**

**`[LJ-1.225]` returned「NO. IT STOPS ONE MODULE SHORT」on 2026-08-14 and
NEVER GOT ITS DD25 REVIEW.** **That is the exact lapse the gate exists for, and
it is mine.** **I could write「DD25 review not needed」in the row and the gate
would go green. That is C-43's escape hatch and I am not taking it.**

**Review it.**

## WHAT IT FOUND, and much of it has since been tested by construction

**`[LJ-1.225]` measured that the class-generic port does NOT supply
`[LJ-1.7]`'s environment lift**, and named the missing module: `L.Coding.Sequence`
and its six readings, `StepAt-out` (`src/L/Coding/Sequence.lagda.md:217`),
`StepAt-back` (`:221`), `ApproxAt-dom` (`:295`), `ApproxAt-value` (`:298`),
`ApproxAt-step` (`:303`), `Graph-out` (`:325`), with the module pinning `𝒮ʟ` at
`:59`.

**`[LJ-1.238]` then PORTED that module: 40 written lines, 145 verbatim,
per-tower residual ZERO.** **So the finding was acted on and it held.**

**A review whose target has already been confirmed by construction is still a
review.** **Its job is to ask what the target got WRONG that nobody noticed
because the headline was right.**

## THE FOUR QUESTIONS

**1. IS THE NO CORRECT ON ITS OWN NUMBERS?** Re-derive the six readings and the
`:59` pin. **`[LJ-1.238]` ported them, so a defect here would show up as a
mismatch between what `[LJ-1.225]` named and what `[LJ-1.238]` built.**

**2. DID IT REACH TOO FAR?** **`[LJ-1.225]` also said the four hypotheses were
`amb` SUPPLIED, `s₁` BUILT, `sl` and `sc` OPEN.** **`[LJ-1.242]` and
`[LJ-1.243]` later measured that `amb`'s supply was CONDITIONAL on an
undischarged `q`.** **So `[LJ-1.225]` carried「SUPPLIED」forward unqualified.
Was that its error or an inherited one?**

**3. DID IT REACH TOO LITTLE?** **It concluded「land the port as DD4 and call it
DD4」.** **`[LJ-1.249]` later showed the assembly above it is carrier-generic
and paid once for both towers.** **Did `[LJ-1.225]` under-state what the port
buys?**

**4. DID THE BRIEF CAUSE IT?** **My brief asked「does the ported chain discharge
`[LJ-1.7]`'s residue」and handed it `dev/PLAN.md:49` as the statement of that
residue.** **That row said `amb` is SUPPLIED, which was false.** **So the brief
handed it the defect. Say whether it could have caught that.**

## THE ORCHESTRATOR LAPSE IS PART OF THE REVIEW

**Say in one line why this review is nineteen dispatches late.** **`[LJ-1.225]`
returned a NO, I registered its row, and I dispatched the next task instead of
its review.** **DD25's own enforcement point is the index row naming a code,
and `scripts/check-dd25-review-named.py` caught it only when a full gate
finally ran.** **Between those two moments, eleven negatives DID get their
reviews. This one did not, and the difference is worth naming.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **UPHELD.** Correct on its numbers. Say what you checked.
- **OVERTURNED.** Give the evidence at `file:line`.
- **UPHELD BUT MISATTRIBUTED.** The verdict is right and the cause is wrong,
  most often an inherited premise. **This is the likeliest branch given
  question 2.**
- **UNDECIDABLE ON THE RECORD.** Say what is missing.

## WHAT YOU MUST NOT DO

- **Do not edit any master, brief or report.** **Write your own report and
  nothing else.** **I write the status screen and the index row.**
- **DO NOT RUN AGDA.** The tree has just been gated and a run now costs a
  re-gate.
- **Do not re-litigate the port.** It is landed as DD4 and `[LJ-1.238]` ported
  the module.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`.
- **Create your report file in your FIRST five minutes (C-22).**

## SEVEN RULES THIS CHAIN EARNED

**AN ESCAPE HATCH IS THE SHAPE A WRONG CHOICE HIDES IN** (C-43). **The gate
offers「DD25 review not needed」and three rows of four genuinely qualified. This
one did not.**

**CHECK THE TREE BEFORE YOU CALL SOMETHING ABSENT.**

**`exit 0` IS NOT A SUPPLY** (C-45).

**A PROHIBITION IN A BRIEF CAN BE THE WHOLE BLOCKER** (C-39).

**SEARCH THE OPEN-WORK LIST BY CONTENT, NOT BY NAME.**

**A FAILED SUBSTITUTION IS NOT A PROOF OF IMPOSSIBILITY** (C-36).

**C-44: if THIS brief states anything you cannot find, say so and treat it as
unproven.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.225]` said the port is worth landing on DD4 alone.** **`[LJ-1.238]`
measured Sequence's per-tower residual at ZERO and `[LJ-1.249]` measured the
assembly carrier-generic.** **So the DD4 half of `[LJ-1.225]`'s verdict has
been tested three times since. Say whether it survives all three.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-225/lj-1.225-report.md`**, read WHOLE. **The target.**
- **`agents/tasks/LJ-1-238/lj-1.238-report.md` and `GenSequence.agda`**: the
  port that confirmed it by construction.
- `agents/tasks/LJ-1-242/` and `LJ-1-243/`: where `amb`'s conditional supply
  was found.
- `agents/tasks/LJ-1-249/`: the carrier-generic assembly.
- **`src/L/Coding/Sequence.lagda.md:59`, `:217`, `:221`, `:295`, `:298`,
  `:303`, `:325`: read the source.**
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:375` marks the C2 row PER-TOWER and
`[LJ-1.225]` read the six readings as that row.** **`[LJ-1.238]` then measured
their residual at ZERO, which looks like a contradiction. Resolve it.** Return
a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-225/lj-1.225-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-262/lj-1.262-report.md` ONLY.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for review` and read every statement.
**The tool now prints `Full entry: dev/LESSONS.md:<line>` for every rule and
says THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you
act on.**

- **C-43.** An escape hatch is the shape a wrong choice hides in.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
  **`[LJ-1.225]` carried「`amb` SUPPLIED」and it was conditional.**
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **C-42.** A refutation measures the site it names, never its extent.
- **C-44, C-45.** A claim is unchecked until you check it; audit the
  instantiation.
- **P-l, C-22, C-31, C-32, C-33, C-34, C-36, C-37, C-39, C-40. D-26, D-29,
  D-30. I-5. DD0, DD8, DD18, DD24, DD25.**

## CONSTRAINTS

- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line` on BOTH sides. Write ASD-STE100.

## RETURN

**Lead with ONE verdict word.** Then the four questions, answered. Then one
line on why the review is late. Then whether the DD4 half survives its three
later tests. **Mark every negative MEASURED or INFERRED.**
