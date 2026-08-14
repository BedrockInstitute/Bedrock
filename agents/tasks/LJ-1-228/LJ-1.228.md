# LJ-1.228: price `sl` and `sc`, the two hypotheses nothing on record prices

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**. **This task runs
NO Agda and holds no slot, so the model rule would give flash. I override it and
record why: the task READS Agda source and judges whether the tree already
supplies a hypothesis, which is the subject matter the `--agda` flag cannot
see.** The clock selected the mode.

## GOAL

**`[LJ-1.225]` measured that the class-generic port does NOT unblock
`[LJ-1.7]`, and it left the residue in four named pieces.** Two of them are
closed enough to sequence. **Two are OPEN AND UNPRICED BY ANYTHING ON RECORD.**

| hypothesis | what it says | state | at |
|---|---|---|---|
| `amb` | Devlin (a) at the ambient carrier | **SUPPLIED** by `[LJ-1.184]` | `ProbeLJ1178A.agda:190-191` |
| `s₁` | the level-hood formula is Σ₁ | **BUILT in shape**, 2-line gap | `src/L/BoundedSubset.lagda.md:145-146` |
| **`sl` = `StageLevels`** | **the stage believes every ordinal has a level** | **OPEN** | `ProbeLJ1178A.agda:360-361` |
| **`sc` = `StageCovered`** | **the stage believes every set lies in a level** | **OPEN** | `ProbeLJ1178A.agda:405-406` |

**Both are hypotheses of `module Whole` at `ProbeLJ1178A.agda:486-493`. Price
them.**

## THE RECORD DISAGREES WITH ITSELF, and that is why this task exists

**`dev/PLAN.md:695`, `[LJ-1.121]`:「NEITHER REFUTABLE, NEITHER SUPPLIED. The
wall is the `[LJ-1.12]` crossing, the level-hood certificate, priced 2.8k to
3.3k lines and not built.」**

**`dev/PLAN.md:733`, `[LJ-1.160]`:「THE WALL IS BYPASSED, 16 LINES. Both
hypotheses from one crossing face at the collapse image. The wall term is
absent.」**

**`dev/PLAN.md:751`, `[LJ-1.178]`:「Two of three facts discharged and the debt
moves to the STAGE.」**

**So one record prices this at about 3,000 lines, another says 16, and a third
says the debt MOVED to the stage rather than being paid.** **Settle it. That
difference is the largest open uncertainty in phase 1.**

**D-10: price the TRUTH of a recorded residue before pricing its proof.** **A
row can be stale and a row can be wrong.**

## THE THREE QUESTIONS

**1. DOES THE TREE ALREADY SUPPLY THEM?** **C-38 as extended: a hypothesis is
discharged when something SUPPLIES it.** `sl` and `sc` are statements ABOUT the
stage. **`src/L/StageCardinal.lagda.md`, `src/L/Hierarchy.lagda.md` and
`src/L/Ordinal/` carry stage facts.** **Search for the content, not the name.**
**If something supplies either one, that is the whole answer and it is worth
more than any price.**

**2. IS THIS THE `[LJ-1.121]` CROSSING, OR DID `[LJ-1.160]` BYPASS IT?** **Read
`[LJ-1.160]`'s 16-line bypass and say whether it reaches `sl` and `sc`, or only
`levelIn` and `cover`.** **`[LJ-1.178]` says the debt MOVED to the stage. Say
what that means at `file:line`.**

**3. WHAT IS THE PRICE?** One number each, with its basis named (DD8). **If the
basis is a probe nobody has run, name the probe.**

## WHAT MAKES THIS ANSWERABLE BY READING

**Both are `⊨ᵐ` statements about ONE stage variable**, at
`ProbeLJ1178A.agda:360-361` and `:405-406`. **They quantify over `ASt.SL` and
they embed a formula.** **So the question is whether the tree proves those two
formulas at a stage**, and that is a search over delivered content.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **SOMETHING SUPPLIES ONE OR BOTH.** Name it at `file:line` on both sides.
  **Then `[LJ-1.7]`'s residue shrinks and I sequence the discharge.** STOP.
- **NEITHER IS SUPPLIED, AND HERE IS THE PRICE.** Two numbers, each with its
  basis. **Say which record was right, `[LJ-1.121]`'s 3,000 or `[LJ-1.160]`'s
  16.**
- **THE CROSSING IS REAL AND IT IS THE 2.8k TO 3.3k.** **Say so plainly.** **Then
  `[LJ-1.7]` needs a different plan and phase 1 needs to know today.** **This is
  a real outcome and I want it if it is true.**
- **A HYPOTHESIS IS FALSE.** If `sl` or `sc` cannot hold at the stage as
  stated, **that is the most valuable outcome available.** D-10: a target can
  be false, and a Tarskian or cardinality obstruction is the usual killer.
- **THE RECORD IS STALE.** If `dev/PLAN.md`'s rows do not match the probes they
  cite, **say which row and give the evidence.** `[LJ-1.174]` found three false
  figures in the status screen this way.

## WHAT YOU MUST NOT DO

- **DO NOT RUN AGDA.** Siblings hold both Agda slots, and one runs in the
  orchestrator's own harness where `dispatch.py status` cannot see it.
- **Do not re-litigate the port.** `[LJ-1.225]` measured that it stops one
  module short of the six ambient readings, and that is settled. **You are
  pricing the OTHER half of the residue.**
- **Do not price the six ambient readings.** They are `L.Coding.Sequence` and
  `[LJ-1.225]` measured them at 157 non-blank lines. **Take that; do not
  re-derive it.**
- **Do not edit any master, brief or report.** **Write your own report and
  nothing else.**
- **Do not touch `agents/tasks/LJ-1-226/`, `LJ-1-227/` or `LJ-1-229/`.** Three
  siblings are live there.
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **A supplier you find at `file:line`
is MEASURED. A price you judge from a line count is INFERRED, and P-l says
so.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`dev/literature/devlin-II5.md:374` marks the C1 row PER-TOWER, and
`[LJ-1.225]` measured that `sl` and `sc` ARE that row.** **So the honest DD4
question is not how to share them; it is whether the J tower will need its own
pair.** **Say whether what you find is one object or two**, because
`:387-389` says the per-tower content is exactly two objects for the whole of
II.5, and `[LJ-1.7]`'s residue is claiming one of them.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-178/lj-1.178-report.md` and `ProbeLJ1178A.agda`**, read
  WHOLE. **`:360-361`, `:405-406` and `:486-493` are your targets and the probe
  is the evidence.**
- **`agents/tasks/LJ-1-121/`**: the 2.8k to 3.3k crossing price. **Read how it
  was derived, not the row about it.**
- **`agents/tasks/LJ-1-160/`**: the 16-line bypass. **Read what it actually
  bypassed.**
- `agents/tasks/LJ-1-184/`: how `amb` was SUPPLIED. **That is your template for
  what SUPPLIED means here.**
- `agents/tasks/LJ-1-225/lj-1.225-report.md`: the four-hypothesis table and the
  Devlin mapping.
- **`src/L/StageCardinal.lagda.md`, `src/L/Hierarchy.lagda.md`,
  `src/L/BoundedSubset.lagda.md:1555-1621`: the delivered stage content. Read
  the source, never a report about it.**
- **`archive/dev/TASKS-archived.md`, `archive/dev/JOURNAL-archived.md` and
  `archive/src/2026-08-09-rud-route/`.** **The retired route reached its own
  trophy and `[LJ-1.184]` found the archive had stopped on this very
  obligation. Take SHAPE from the archive, never a claim**, and say what would
  NOT transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:374` is the C1 row and `:387-389` is the
two-object verdict.** **Say whether Devlin's own proof discharges `sl` and `sc`
or assumes them**, and whether he prices them at all. Return a **LITERATURE
USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-178/lj-1.178-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-228/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.

- **D-10.** Price the truth of a recorded residue before pricing its proof.
  **This task IS D-10, and the record contradicts itself by a factor of 200.**
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **DD8.** One estimate, and it names its basis.
- **C-36.** Write the term you could not write.
- **C-22.** Write the deliverable incrementally.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-l.** A price measured at one site is a hypothesis at another.
- **D-26. C-32, C-39, C-40. DD0, DD2, DD24. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with whether anything supplies `sl` or `sc`, and with ONE price each if
nothing does.** Then which record was right, `[LJ-1.121]`'s 2.8k to 3.3k or
`[LJ-1.160]`'s 16, with the evidence. Then whether either hypothesis could be
FALSE. Then whether this is one per-tower object or two. **Mark every negative
MEASURED or INFERRED.**
