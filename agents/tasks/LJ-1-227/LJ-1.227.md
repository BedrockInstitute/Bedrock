# LJ-1.227: the gate list for A-prime's reading residue, five blocks in ONE pass

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**. **This task runs
NO Agda and holds no slot, so the model rule would give flash. I override it and
record why: the task READS Agda source and judges what a block would cost to
build, which is the subject matter the `--agda` flag cannot see.** The clock
selected the mode.

## GOAL

**`[LJ-1.217]` closed A6 and moved `[LJ-1.176]`'s refusal to a new reason, in
its own words: 「A6 is no longer the blocker; the reading residue is.」**

**The seven cells now sum to 1,548. That sum is NOT a price, and both
`[LJ-1.176]` and `[LJ-1.217]` refuse to quote it, correctly.** **555 lines
across A1, A2, A3, A4 and A7 rest on READING, and only about 100 of those carry
a measured core.**

**`[LJ-1.175]` is blunter, at `lj-1.175-report.md:219` and `:247`: for A1, A2,
A3, A4 and A7, 「NO FIGURE EXISTS」, MEASURED.**

**Produce the gate list. One pass over all five.**

## WHY A LIST AND NOT A BUILD

**DD8: a build brief that cannot name the widest unmeasured term, and the probe
that measures it, is NOT READY TO SEND.** **I cannot write those five briefs
today, because nobody has named those terms.**

**And `[LJ-1.221]` measured my worst pattern this week:** a brief that fixes a
method which cannot answer the question, four of ten overturns. **Five separate
build dispatches on unnamed terms would be that pattern again.**

## THE FIRST QUESTION, PER BLOCK, and it beats every other outcome

**Is the block NEEDED AT ALL?**

**This project has dissolved three items this month, each worth more than the
measurement it replaced:**

| what dissolved | task | what it saved |
|---|---|---|
| A5's `CSB` | `[LJ-1.156]` | A5 carries ZERO replacement |
| A5's 300-line item | `[LJ-1.176]` | DISSOLVED, not divided |
| `[LJ-1.196]`'s CHAPTER | `[LJ-1.210]` | 42 written, 1,272 verbatim |

**Ask it first for every block. A dissolution beats a price.**

## THE SECOND QUESTION, PER BLOCK

**Name the widest UNMEASURED term in the block, and name the probe that would
measure it.**

**That pair is the whole deliverable.** A block whose widest term is named and
priced becomes a build brief I can send the same hour. A block whose widest term
is unnamed cannot be funded, whatever its inferred line count says.

**Say what each probe would cost in Agda minutes, and mark that INFERRED.**

## THE THIRD QUESTION, ONCE, ACROSS ALL FIVE

**`[LJ-1.175]` MEASURED that the seven blocks DO NOT PARTITION, and quoted five
overlaps from the reports' own text.** **`dev/PLAN.md:63-67` says a partition
ruling comes FIRST because it costs no machine and it decides what a probe must
measure.**

**Say whether the five overlaps still stand after `[LJ-1.176]`'s 547 and
`[LJ-1.217]`'s 446.** **If a line is counted in two blocks, the 1,548 is wrong
in a second way and the gate list must say which lines double.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **FIVE BLOCKS, FIVE NAMED TERMS, FIVE PROBES.** Then A-prime is fundable
  block by block and I send them widest first. STOP.
- **A BLOCK DISSOLVES.** **Say so with the evidence and stop counting it.**
  **That is the best outcome here.**
- **A BLOCK'S TERM CANNOT BE NAMED BY READING.** Say which and why. **That is
  the honest boundary and it is a complete answer for that block.**
- **THE OVERLAPS RE-PRICE THE SUM.** If lines double-count, **give the corrected
  figure and the lines that moved.**
- **THE RESIDUE IS SMALLER THAN 555.** If `[LJ-1.217]`'s composition is stale
  against the tree, **say so.** A status figure nobody re-derives is how this
  project has been wrong before.

## WHAT YOU MUST NOT DO

- **DO NOT RUN AGDA.** A sibling holds an Agda slot and a second runs in the
  orchestrator's own harness, which `dispatch.py status` cannot see.
- **Do not build anything.** This task names terms and probes.
- **Do not re-price A5 or A6.** `[LJ-1.176]` measured 547 and `[LJ-1.217]`
  measured 446. **Take both; do not re-derive them.**
- **Do not quote 1,548 as A-prime's total**, and do not produce a new total
  unless the overlaps force a correction. **Two reports refuse that sum and the
  refusal stands.**
- **Do not touch `agents/tasks/LJ-1-225/` or `LJ-1-226/`.** Two siblings are
  live there, and `[LJ-1.226]` is building A5's `pairω` right now. **Its rows 4
  and 5 are ITS work, not yours.**
- **Do not edit any master, brief or report.** **Write your own report and
  nothing else.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **A line count you read is MEASURED.
A cost you judge from it is INFERRED, and P-l says so.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.175]` MEASURED that no report gives a generic or re-instantiation
figure for six of the seven blocks.** **So ask of each block: is its content
tower-neutral?** `[LJ-1.223]` measured the whole coding chain tower-neutral with
a per-tower residual of ZERO, and `dev/literature/devlin-II5.md:387-389` says
the per-tower content is exactly two objects. **A block that is tower-neutral
should be written generic from its first line, and saying so now costs
nothing.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-175/lj-1.175-report.md`**, read WHOLE. **It is your brief
  within this brief:** the five overlaps, the「NO FIGURE EXISTS」measurement at
  `:219` and `:247`, and the partition problem.
- **`agents/tasks/LJ-1-176/lj-1.176-report.md`**: A5 at 547, the partition it
  stated, and the dissolution of the 300-line item.
- **`agents/tasks/LJ-1-217/lj-1.217-report.md`**, sections 5 and 9: A6 at 446,
  the composition of the 555, and what `[LJ-1.8]` still needs.
- `agents/tasks/LJ-1-156/lj-1.156-report.md`: how a block DISSOLVED, which is
  your first question's template.
- `agents/tasks/LJ-1-136/`: the A-prime block gates and the 2.594 s per line.
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **The retired route reached its own trophy, so a block A-prime treats as
  unwritten may exist there. Take SHAPE from the archive, never a claim**, and
  say what would NOT transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Say for each block whether Devlin settles its shape or only its existence.**
**`dev/literature/devlin-II5.md:387-389` says the per-tower content is exactly
two objects; say which blocks, if any, are those two.** Return a **LITERATURE
USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-175/lj-1.175-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-227/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.

- **DD8.** Name the widest unmeasured term and the probe that measures it.
  **This task IS DD8's precondition for five build briefs.**
- **D-10.** Price the truth of a recorded residue BEFORE pricing its proof.
  **A block can be false as well as unmeasured.**
- **C-22.** Write the deliverable incrementally.
- **C-36.** Write the term you could not write.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-l.** A cost measured at one block is a hypothesis at another.
- **D-26. C-32, C-38, C-39, C-40. DD0, DD2, DD4, DD24. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with how many of the five blocks DISSOLVE, and how many have a named
widest term.** Then one section per block: what it is, whether it is needed, its
widest unmeasured term at `file:line`, the probe that would measure it, and its
inferred Agda minutes. Then the overlap answer and any corrected figure. Then
which blocks are tower-neutral. **Mark every negative MEASURED or INFERRED.**
