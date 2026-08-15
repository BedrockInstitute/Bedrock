# LJ-1.265: align DD24's bar, because three rates are in force and they disagree

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**. **This task runs
NO Agda and holds no slot, so the model rule would give flash. I override it
and record why: the task READS rulings and derives which figure a rule
licenses, which the `--agda` flag cannot see.** The clock selected the mode.

## GOAL

**The owner asked whether the GCH wing can be compressed back inside DD24's
threshold. I could not answer, because THREE different per-line rates are in
force and I have not aligned them.** **I refused to quote the one I could not
derive, and this task derives it.**

**The three, all in the live tree:**

| rate | where | what it is called there |
|---|---:|---|
| **0.013193** | `dev/ledger.toml:249` | 「DD24's bar of 0.013193 s/line over the a-priori wing」, credited to `[LJ-1.6-R]` |
| **0.007913** | `dev/PLAN.md` DD26 | 「DD24's baseline is 0.007913 over 16,897」 |
| **0.009143** | `dev/ledger.toml:2746` | `ac_baseline_module_rate`, which `[LJ-1.218]` used with a 1.15 tolerance |

**Say which one DD24 licenses, and what the wing's real gap is.**

## THE ARITHMETIC IS ALREADY PINNED, so do not redo it

**I derived all of this myself before writing the brief:**

| rate | budget over the a-priori band 7,553 to 11,197 | allowance at today's 11,926 lines |
|---|---|---|
| 0.013193 | **99.6 to 147.7**, which is exactly `gch_wing_seconds_budget` | 157.3 s |
| 0.009143 | 69.1 to 102.4 | 109.0 s |
| 0.007913 | 59.8 to 88.6 | 94.4 s |

**So `gch_wing_seconds_budget` is internally consistent with 0.013193 and with
nothing else. MEASURED.**

**And the three do not reduce to one another:** `0.013193 / 1.15 = 0.011472`,
which is neither of the others; `0.007913 × 1.15 = 0.0091`, which is close to
`0.009143` but NOT equal.

**The wing measures 185.41 s over 11,926 lines** (`[LJ-1.218]`, corrected by
`[LJ-1.222]`). **So the gap is about 28 s, 76 s or 91 s depending on which
rate is DD24's, and `[LJ-1.218]` reported 60.0 s using `0.009143 × 1.15 =
0.010514`.**

**FOUR different answers to one question. That is what you are settling.**

## THE THREE QUESTIONS

**1. WHAT DOES DD24 ACTUALLY SAY?** **Read the DD24 row in `dev/PLAN.md`
section 3 whole, and DD26, which re-based it.** **DD24 is a RULING and the
ruling's own words decide this, not any report's arithmetic.**

**2. WHERE DID 0.013193 COME FROM?** **`dev/ledger.toml:249` credits
`[LJ-1.6-R]`.** **Open that report.** **If it derived 0.013193 from a bar that
has since been re-based by DD26, the budget is STALE and the ledger says so
nowhere.**

**3. WHAT IS THE WING'S REAL GAP?** One number, with its basis, and **say
whether the a-priori band or today's 11,926 lines is the right denominator**,
because DD24 judges the wing AS DELIVERED and DD5 measure 2 is about the
a-priori projection. **Those are two different questions and the ledger may be
answering one with the other's number.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **ONE RATE IS DD24's AND THE OTHERS ARE DERIVED OR STALE.** Say which, at
  `file:line`, and give the wing's gap with its basis. STOP.
- **THE BUDGET IS STALE.** **Then `dev/ledger.toml:311`'s
  `gch_wing_seconds_budget` is wrong and I correct it today.** **Say what it
  should read.**
- **THEY ANSWER DIFFERENT QUESTIONS.** **If 0.013193 prices the a-priori
  projection and 0.007913 prices the delivered wing, then nothing is stale and
  the defect is that neither field says which question it answers.** **That is
  a real finding and the cure is a comment, not a number.**
- **DD24 DOES NOT LICENSE ANY OF THE THREE.** **Say what it licenses.** **A
  ruling that fixes a bar and three fields that quote three numbers is a
  governance defect and the owner should hear it plainly.**
- **UNDECIDABLE ON THE RECORD.** Say what is missing. **Do not pick the
  friendliest number.**

## WHAT YOU MUST NOT DO

- **DO NOT RUN AGDA.** Two siblings hold both Agda slots (C-12).
- **Do not re-measure the wing.** 185.41 s over 11,926 lines is `[LJ-1.218]`'s
  and `[LJ-1.222]` reviewed it.
- **Do not edit `dev/ledger.toml`, `dev/PLAN.md` or any master.** **Write your
  own report and nothing else.** **I correct the fields.**
- **Do not touch `agents/tasks/LJ-1-263/` or `LJ-1-264/`.** Siblings are live.
- **Create your report file in your FIRST five minutes (C-22).**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## WHY THIS MATTERS MORE THAN ITS SIZE

**The owner asked a strategy question: is the plan to finish the proof and
compress afterwards?** **DD24's answer is yes, because intermediate debt is
allowed and only the whole wing at the end is judged.**

**So the ONLY number that says whether that plan can work is the wing's gap to
the bar, and right now that number has four values.** **About 1,500 lines are
still to land on top of it.**

## EIGHT RULES THIS CHAIN EARNED

**DERIVE A FIGURE OR DO NOT WRITE IT** (C-44). **Three of my briefs have
carried a number I did not derive, and this task exists because I refused to
write a fourth.**

**A FIGURE REACHES THREE DOCUMENTS BEFORE ANYONE CHECKS IT.** **This one
reached three fields with three values.**

**SEARCH THE OPEN-WORK LIST BY CONTENT, NOT BY NAME.**

**AN ESCAPE HATCH IS THE SHAPE A WRONG CHOICE HIDES IN** (C-43). **Picking the
friendliest of four rates is that shape.**

**`exit 0` IS NOT A SUPPLY** (C-45).

**CHECK THE TREE BEFORE YOU CALL SOMETHING ABSENT.**

**A FAILED SUBSTITUTION IS NOT A PROOF OF IMPOSSIBILITY** (C-36).

**CARRY A CLAIM'S QUALIFIER OR CARRY NEITHER.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**DD24's bar is an AC-side figure applied to the GCH side, so it is a
cross-tower comparison by construction.** **`[LJ-1.262]` measured that this
phase mixes two axes: Def against J, which is Devlin's, and L against ambient,
which is the port's.** **Say which axis DD24's bar is on**, because a bar
measured on one axis and applied on another is exactly the defect `[LJ-1.262]`
found in a DD4 figure.

## ARCHIVE (DD18)

- **`dev/PLAN.md` section 3, the DD24 row and the DD26 row, read WHOLE.**
- **`dev/ledger.toml:243-260`, `:305-316`, `:2740-2750`: the three fields and
  every comment around them.**
- **`agents/tasks/LJ-1-6-R/`** or wherever `[LJ-1.6-R]` lives: **the report
  the 0.013193 is credited to. Open it.**
- `agents/tasks/LJ-1-218/lj-1.218-report.md` and
  `agents/tasks/LJ-1-222/lj-1.222-report.md`: the 60.0 s and its review.
- `agents/tasks/LJ-1-1/`: the a-priori band and what it was told.
- **`archive/dev/TASKS-archived.md` and `archive/dev/DECISIONS-archived.md`.**
  **DD24 has a history and the retired `D` series may hold the bar's first
  statement. Take SHAPE from the archive, never a claim.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**Nothing in the literature governs a check-cost bar. Say so in one line.**
Return a **LITERATURE USED** section.

## SCOPE (read)

`dev/PLAN.md` section 3's DD24 and DD26 rows FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-265/` only. **No master, no ledger, no plan.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **C-44.** **A figure is unchecked until you derive it. The centre.**
- **C-32.** A cure invalidates every downstream measurement; re-run the gate
  before acting on the old number. **DD26 re-based DD24 and the ledger may not
  have followed.**
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **P-l.** A rate measured at one site is not a rate at another.
- **D-26.** A well-founded key on a tower needs generation data, or syntax.
- **C-22, C-36, C-38, C-39, C-40, C-42, C-43, C-45. I-5. DD0, DD5, DD8, DD18,
  DD24, DD26.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with ONE rate and ONE gap: which figure DD24 licenses, and what the
wing's gap to it is.** Then where 0.013193 came from and whether it is stale.
Then whether the a-priori band or the delivered 11,926 is the right
denominator. Then what `dev/ledger.toml:311` should read. Then DD24's axis.
**Mark every negative MEASURED or INFERRED.**
