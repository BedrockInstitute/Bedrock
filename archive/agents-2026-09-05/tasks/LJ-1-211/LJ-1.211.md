# LJ-1.211: why is the DD25 overturn rate 71 percent

tier: pi (in-harness-subagent-mode). **The switch's ADVERSARIAL row, taken as
the table gives it.** Every brief under audit here was written by the in-harness
Opus, so DD17's invariant holds: the critic is never the same head as the
author.

## GOAL

**`[LJ-1.208]` built a register that reads DD25's record back from
`dev/PLAN.md` instead of from anyone's memory. Its first run says:**

> **14 reviews: 10 overturn, 1 split, 3 uphold. Overturn rate 71 percent.**
> **A rate at or above 60 percent indicts the UPSTREAM process, not the
> reviews.**

**The upstream process is the orchestrator: it writes every brief and audits
every return.**

**Find out why, and say what would lower it.**

## THIS IS AN AUDIT OF THE ORCHESTRATOR, and the evidence is unusually honest

**The commit bodies carry the reasoning and the errors**, because this
orchestrator writes them there. **`git log` with bodies read is your primary
corpus.**

**Two of today's reviews came back UPHELD BUT MISATTRIBUTED and BOTH named the
BRIEF as the cause**, in those words:

- `[LJ-1.200]`: the brief froze a plan, forbade restating it, and shipped that
  plan's unmeasured consequent into the live status screen.
- `[LJ-1.201]`: the brief fixed the design at 「one pair of runs」 and called it
  「your design constraint, not a caution」, and the return then declined the
  probe that would have answered the question.

**A third case is on the record the same day:** `[LJ-1.206]` was told to build a
herdr agent as a test subject and that instruction killed it.

**So the hypothesis to test is that the briefs cause the overturns.** **It is
MINE and it is INFERRED. Refute it if the record says otherwise.**

## WHAT WOULD MAKE THIS A REAL FINDING

**A rate is not a diagnosis.** Split the 10 overturns by CAUSE and give the
counts:

1. **The brief carried a false premise.** Six are already admitted; check
   whether the reviews trace to them.
2. **The brief fixed a method that could not answer the question.**
3. **The brief shipped a conclusion as an instruction**, so the agent had no
   room to refute it.
4. **The agent erred on its own**, with the brief clean.
5. **The reviewer was wrong** and the overturn should not stand.

**Category 5 matters most and nobody has checked it.** **A 71 percent overturn
rate could also mean the REVIEWS are too eager, and this audit is the only place
that can say so.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **CAUSED, AND CLASSIFIED.** Report the counts by cause, ranked by what each
  cost, and say what would lower the rate. STOP.
- **THE RATE IS AN ARTIFACT.** If the register counts a split or a partial as an
  overturn and the true rate is lower, **say so with the recount.** That is a
  complete answer and it corrects a figure already in a commit.
- **THE REVIEWS ARE THE PROBLEM.** If the overturns do not hold up, **say so
  plainly.** That is the most valuable thing you can return and the hardest to
  say.
- **THE SAMPLE IS TOO SMALL.** 14 is not many. **If a cause split of 10 cannot
  carry a conclusion, say what would.**

## WHAT YOU MUST NOT PROPOSE

**Do not propose「write better briefs」.** That is not a mechanism, and this
project has measured that a rule with no enforcement point is a wish.

**Propose something with a MOMENT and a TRIGGER**: a checker, a brief section a
gate can see, a skill with keywords that fire at the writing moment, or a
ruling. **`[LJ-1.189]` set that discipline and its four proposals all named
their cure kind.**

## WHAT YOU MUST NOT DO

- **Do not edit any brief, report, master, checker or `dev/` file.** **This is
  an audit and its report is the whole product.**
- **Do not run Agda.** Two siblings hold Agda processes.
- **Do not dispatch an agent.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.
- **Create your report file in your FIRST five minutes (C-22).** An agent died
  on 2026-08-14 having written nothing, and its reasoning had to be salvaged
  from its terminal.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Here DD4 is one of the things to check.** It is stated in every brief and its
enforcement is that repetition. **Ask whether the briefs that produced overturns
differ from the ones that did not in any MEASURABLE way**, DD4's presence
included, or whether the difference is invisible to every gate this project
has.

## ARCHIVE (DD18)

- **`scripts/dd25-record.py`** and its output, and
  **`agents/tasks/LJ-1-208/lj-1.208-report.md`**, which explain how the register
  reads the record back and why it exists.
- **`agents/tasks/LJ-1-200/LJ-1.200-report.md`** and
  **`agents/tasks/LJ-1-201/LJ-1.201-report.md`**, read WHOLE: the two that named
  the brief as the cause.
- `agents/tasks/LJ-1-183/lj-1.183-report.md` and `agents/tasks/LJ-1-157/`: the
  two earlier audits of this same orchestrator.
- `dev/LESSONS.md` **C-39 to C-43**, the process laws already admitted.
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim**, and say what would NOT transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Not this task's subject. Say so in one line.**

## SCOPE (read)

`scripts/dd25-record.py`'s output FIRST, then `git log` with bodies.

## SCOPE (write)

`agents/tasks/LJ-1-211/lj-1.211-report.md` ONLY.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for review` and read every statement.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-l.** A measured result elsewhere is a hypothesis here.
- **D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-36, C-37, C-39, C-40.
  I-5. DD0, DD8.**

## CONSTRAINTS

- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line` or a command and its output. Write ASD-STE100.

## RETURN

**Lead with the cause split of the 10 overturns, as counts, and with the single
change that would lower the rate most.** Then each cause with its evidence at a
commit hash or `file:line`. Then category 5, whether any overturn should not
stand. Then what you propose, each with its MOMENT and TRIGGER. **Mark every
finding MEASURED or INFERRED.**
