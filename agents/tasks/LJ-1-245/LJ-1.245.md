# LJ-1.245: apply C-45 to the whole record, and find the other conditional supplies

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**. **This task runs
NO Agda and holds no slot, so the model rule would give flash. I override it and
record why: the task READS Agda telescopes and judges whether a parameter is an
idiom or a hypothesis, which is the subject matter the `--agda` flag cannot
see.** The clock selected the mode.

## GOAL

**C-45 entered `dev/LESSONS.md` today because one undischarged telescope
parameter made the project record a hypothesis as SUPPLIED for days, and briefed
two later dispatches on it as a green fact.**

**`[LJ-1.243]` swept 4,165 telescopes and found SEVEN undischarged sites of the
dangerous form, all in the probe layer.** **It named one of them:
`ProbeT193.agda:63,94,97`, where the pass-through move recurs.**

**Find the other six, and say for each whether a RECORDED RESULT rests on it.**

## THE BOUNDARY, which `[LJ-1.243]` measured and you must apply rather than
re-derive

**The bare count of equation parameters is USELESS: 1,379 of 4,165.** **The
BOUNDARY is the result:**

| form | shape | verdict |
|---|---|---|
| **idiom** | one side is independent, the other is determined; `refl` closes it at the call site | **harmless.** `src/L/Coding/Sequence.lagda.md:332` is one, closed at `src/L/Hierarchy.lagda.md:539`, and the comment at `:540-541` records the 85 seconds it saves |
| **hypothesis** | terms on BOTH sides are independently quantified, so `refl` is impossible | **dangerous.** `agents/tasks/LJ-1-184/ProbeLJ1184B.agda:112` is one |

**Both look identical in a telescope. That is the whole point of C-45.**

## THE TEST, and it is one search per site

**C-45's action: search for every APPLICATION of the module and check that each
equation parameter is given a real term.**

**`[LJ-1.243]` settled the worst case in one search:** `AmbientStep` is applied
at exactly one site, `agents/tasks/LJ-1-184/ProbeLJ1184C.agda:83`, and every
argument there is the caller's own parameter. **It relays; it discharges
nothing.**

## WHAT MAKES A SITE MATTER, and this is the ranking I want

**A site matters in proportion to what the RECORD claims on it.** For each of
the seven:

1. **Is it discharged anywhere?** One search.
2. **Does a row in `dev/PLAN.md` section 11 record a result that rests on it?**
   **That is the question that decides whether the record is wrong.**
3. **If a row rests on it, does the row say so?** `[LJ-1.184]`'s row said
   SUPPLIED and did not.

**Rank the seven by 2 and 3. A site nothing claims on is a note; a site a row
claims on is a defect.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE OTHER SIX ARE HARMLESS.** Say what each is and why nothing rests on
  it. **Then C-45's cost was one row and the record is otherwise clean.** STOP.
- **N ROWS REST ON AN UNDISCHARGED PARAMETER.** **Name each row, its code, and
  the parameter at `file:line`.** **Then I correct every one of them today**,
  the way `dev/PLAN.md:731` was corrected for `[LJ-1.184]`.
- **THE SEVEN ARE NOT SEVEN.** **`[LJ-1.243]`'s sweep is a measurement and C-44
  says it is unchecked until you check it.** **If the count is wrong, say so
  with your own count and your own boundary test.**
- **THE BOUNDARY DOES NOT SEPARATE THEM.** If a site is neither clearly idiom
  nor clearly hypothesis, **say so and say what would settle it.** **Do not
  guess, and do not run Agda to find out.**

## WHAT YOU MUST NOT DO

- **DO NOT RUN AGDA.** A sibling holds a slot and is measuring seconds.
- **Do not discharge anything.** You audit; you do not build.
- **Do not edit any master, brief or report.** **Write your own report and
  nothing else.** **I correct the rows.**
- **Do not re-litigate `[LJ-1.184]`.** `[LJ-1.242]` and `[LJ-1.243]` settled
  it and `dev/PLAN.md:731` is already corrected.
- **Do not touch `agents/tasks/LJ-1-244/`.** A sibling is live there.
- **Create your report file in your FIRST five minutes (C-22).**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE DELIVERED BOOK IS CLEAN, and that is a finding to CHECK, not to assume

**`[LJ-1.243]` measured that the seven are all in the PROBE layer and that
`src/` is clean.** **Check that.** **If a delivered master carries the
dangerous form, that is far more serious than seven probes and it is the single
most valuable thing you can return.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **A parameter you read is MEASURED. A
judgement that nothing rests on it is INFERRED until you have searched the
index.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**An undischarged equation parameter is a DD4 question as well as a
correctness one:** a module parameterized over an equation it cannot prove is
not shared code, it is a shape waiting for a proof. **Say whether any of the
seven sits in machinery both towers would use.** **If one does, the shared half
of some DD4 figure is smaller than it reads.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-243/lj-1.243-report.md`**, read WHOLE, especially its
  sweep and its boundary test. **It is your method.**
- `agents/tasks/LJ-1-242/lj-1.242-report.md`: how the parameter was found.
- `agents/tasks/LJ-1-184/`: the worst case, fully worked.
- `dev/LESSONS.md` C-45, read whole.
- **`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:208`,
  `:806-809`.** **`[LJ-1.243]` measured that the RETIRED route parameterized
  the same crossing and left it undischarged, with `:806-809` naming the owed
  equivalence.** **So the archive carries an eighth instance. Say whether it
  carries more**, and whether the archived route's rows claimed anything on
  them.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**Nothing in the literature governs Agda telescopes. Say so in one line**, and
say separately whether any archived or delivered row cites the literature to
support a result that rests on an undischarged parameter. Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-243/lj-1.243-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-245/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.

- **C-45.** Audit the INSTANTIATION, never the telescope. **This task IS
  C-45's sweep.**
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-44.** A brief's claim is unchecked until you check it. **The seven is
  `[LJ-1.243]`'s count, not yours.**
- **C-42.** A refutation measures the site it names, never its extent.
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **P-l.** A judgement made at one site is a hypothesis at another. **`[LJ-1.243]`
  worked ONE site fully; the other six are not priced by that work.**
- **D-26.** A well-founded key on a tower needs generation data, or syntax.
- **C-32, C-36, C-39, C-40. I-5. DD0, DD8, DD18, DD24.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with TWO numbers: how many undischarged sites you found, and how many
have a `dev/PLAN.md` row resting on them.** Then one section per site: the
parameter at `file:line`, whether anything discharges it, which row claims on
it, and whether that row says so. Then whether `src/` is really clean. Then the
archive's instances. **Mark every negative MEASURED or INFERRED.**
