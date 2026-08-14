# LJ-1.248: Route A-prime's total, now that every block is measured

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**. **This task runs
NO Agda and holds no slot, so the model rule would give flash. I override it and
record why: the task READS Agda probes and judges whether two blocks' figures
count the same lines, which the `--agda` flag cannot see.** The clock selected
the mode.

## GOAL

**SIX reports have refused to give Route A-prime a total, and every one was
right at the time.** **The reason was always the same: some block rested on
reading rather than measurement.**

**That reason is gone. Every block now has a measured number.**

| block | figure | source |
|---|---:|---|
| A1 | 54 | `[LJ-1.232]`, against a standing 40 |
| A2 | 186 | `[LJ-1.229]`, against 170 |
| A3 | 26 | `[LJ-1.232]`, against 45 |
| A4 | 43 | `[LJ-1.236]`, against 190. **A MINIMAL CORE, not the master** |
| A5 | 348 | `[LJ-1.247]`, all six rows measured, two dissolved |
| A6 | 446 | `[LJ-1.217]`, 150 base plus a 296 measured charge |
| A7 | 47 | `[LJ-1.236]`, against 110 |

**Derive the total. And say plainly whether it is a PRICE or still
arithmetic.**

## THE THREE THINGS THAT DECIDE IT

**1. THE OVERLAPS.** `[LJ-1.175]` measured that the seven blocks DO NOT
PARTITION and quoted five overlaps. `[LJ-1.227]` re-checked them against
`[LJ-1.176]`'s 547 and `[LJ-1.217]`'s 446 and RESOLVED four, leaving one: A4
consumes A2's predicate. **`[LJ-1.229]` then closed that one by measurement at
27 lines.**

**All five overlaps were checked against figures that have since MOVED.**
**A5 went 547 to 348. A4 went 190 to 43.** **Re-check all five against
today's numbers.** **An overlap resolved against a dead figure is not
resolved.**

**2. THE A4 GAP, and it is the one thing I know is missing.** **`[LJ-1.236]`
said its 43 is a MINIMAL CORE and that the master still owes the full
object-language internal `IsCardinal` with its adequacy, plus the concrete
nonempty witness.** **So A4's 43 is not comparable to A6's 446, which is a
full charge.** **Say how much that gap is worth, or say it needs a probe and
name the probe** (DD8).

**3. WHAT THE FIGURES COUNT.** **`[LJ-1.236]` excluded 5 copied lines from
A4. `[LJ-1.229]` counted `injAt` at 27 and the readback at 51. `[LJ-1.247]`
counted a shared `StageBound` device at 16.** **Check that no two blocks count
the same line and that no line falls between two blocks.** **A total whose
parts use different calibers is not a total.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT IS A PRICE.** Give one number with its basis, and say what makes it a
  price where six earlier reports refused one. STOP.
- **IT IS ARITHMETIC, AND HERE IS WHAT IS MISSING.** **Name the missing piece
  and price it.** **`[LJ-1.236]`'s A4 gap is my candidate; if it is the only
  one, say so and the refusal has a single named cause for the first time.**
- **AN OVERLAP RE-OPENS.** If a resolved overlap fails against today's
  figures, **say which and by how much.**
- **THE CALIBERS DIFFER.** If two blocks count differently, **say which and
  give the corrected figures.** **That is more valuable than a total.**

## WHAT YOU MUST NOT DO

- **DO NOT RUN AGDA.** Siblings may hold slots.
- **Do not re-measure any block.** All seven are measured and each is another
  task's work.
- **Do not touch `[LJ-1.7]`'s `amb` question.** Blocked on a chapter, under
  review at `[LJ-1.246]`.
- **Do not touch `agents/tasks/LJ-1-246/` or `LJ-1-249/`.** Siblings are live.
- **Do not edit any master, brief or report.** **Write your own report and
  nothing else.** **I write the status screen.**
- **Create your report file in your FIRST five minutes (C-22).**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## FOUR RULES THIS AREA EARNED THIS WEEK

**CARRY A CLAIM'S QUALIFIER OR CARRY NEITHER.**

**THE ARCHIVE BEARS UNTIL YOU OPEN IT.**

**`exit 0` IS NOT A SUPPLY** (C-45). **Audit the instantiation, never the
telescope.**

**C-44: if THIS brief states anything you cannot find, say so and treat it as
unproven.** **The seven figures above are other reports' and I have re-derived
only A5's arithmetic.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **A figure you read in a report is
MEASURED by that report. A SUM is INFERRED unless the overlaps and the calibers
are both checked.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.227]` measured the tower split for A1, A2, A3, A4 and A7 and did NOT
cover A5 or A6.** **`[LJ-1.234]` and `[LJ-1.247]` have since dissolved two of
A5's rows and neither was asked for a tower verdict.**

**So give the tower split for the WHOLE route, or say which blocks are still
open.** **The per-tower half of A-prime is what the J tower would have to pay
again, and nobody has added it up.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-227/lj-1.227-report.md`**, read WHOLE, especially its
  overlap section and its tower table.
- **`agents/tasks/LJ-1-175/lj-1.175-report.md`**: the five overlaps as first
  measured, and the partition finding.
- **`agents/tasks/LJ-1-247/`, `LJ-1-236/`, `LJ-1-232/`, `LJ-1-229/`,
  `LJ-1-217/`, `LJ-1-176/`**: the seven figures at their sources. **Read the
  reports, and read what each says it counted.**
- **`agents/tasks/LJ-1-234/lj-1.234-report.md`**: the `pairω` dissolution,
  which is inside A5's 348.
- **`archive/dev/TASKS-archived.md`.** **The retired route reached a trophy and
  had a total. Say what its total counted and why it does NOT transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**Say in one line whether the literature bounds any of the seven blocks**, and
whether `dev/literature/devlin-II5.md:387-389`'s two per-tower objects map onto
the tower split you give. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-227/lj-1.227-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-248/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.

- **DD8.** One estimate, and it names its basis.
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **P-l.** A figure measured for one block is not a figure for another.
- **C-44.** A brief's claim is unchecked until you check it.
- **C-45.** Audit the instantiation, never the telescope.
- **C-42.** A refutation measures the site it names, never its extent.
- **D-26.** A well-founded key on a tower needs generation data, or syntax.
- **C-22, C-32, C-36, C-38, C-39, C-40. I-5. DD0, DD18, DD24.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with ONE number and ONE word: the total, and whether it is a PRICE or
ARITHMETIC.** Then the five overlaps re-checked against today's figures. Then
the A4 gap, priced or named. Then any caliber mismatch. Then the tower split
for the whole route. **Mark every negative MEASURED or INFERRED.**
