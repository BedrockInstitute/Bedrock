# LJ-1.194: build P4, the DD number-uniqueness check

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-flash`**, by the owner's
rule of 2026-08-14: work that touches no Agda code takes flash. **The model is a
command-line flag and this line only records the choice.**

## GOAL

**`[LJ-1.189]`'s fourth proposal, and the orchestrator proposed it against
itself.**

**Extend `scripts/check-rule-ids.py` to refuse a code that appears in more than
ONE row of its series.**

**MEASURED: the orchestrator minted a duplicate `DD27` on 2026-08-14** when
`DD27` had been ruled on 2026-08-10. **`check-rule-ids.py` reported CLEAN
through the whole episode, because it verifies that a code RESOLVES and never
that a code is UNIQUE.**

**`dev/PLAN.md`'s own preamble says a number is never reused, in either
series.** The rule exists and nothing enforced it.
## WHY A CHECKER AND NOT A SKILL

**Uniqueness is mechanical in a way intent is not.** `check-rule-ids.py` already
parses every row of both series to resolve codes, so the set it needs is already
in hand. **A skill cannot be trusted to check every row.**

**This is C-41 one level down**, and the commit that struck the duplicate says
so in those words.
## THE DESIGN CONSTRAINTS

**Both series.** The live `DD` series in `dev/PLAN.md` section 3, and the
retired `D` series in `archive/dev/DECISIONS-archived.md`. **A number is never
reused in EITHER.**

**And across the two:** a `DD<n>` and a `D<n>` are DIFFERENT codes and both may
exist. **Do not report that pair as a duplicate**; the existing series check
already handles the citation side of it.

**Extend the existing checker rather than writing a new one.** Its ID parsing is
already correct and duplicating it is the defect this batch is about.

**Pin it with a test** beside `scripts/tests/test_rule_series.py`, in that
file's style: a synthetic duplicate must fail and the real tree must pass.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BUILT AND GREEN.** The real tree passes, a synthetic duplicate fails, and
  the test pins both. **Show all three.** STOP.
- **A REAL DUPLICATE EXISTS TODAY.** **Report it and do NOT fix it.** A `DD` row
  is the owner's under DD0, and a duplicate in the canon is the owner's to
  resolve.
- **THE LESSONS SERIES HAS A LEGITIMATE REPEAT.** If a `P-`, `C-`, `R-`, `D-`,
  `T-` or `I-` code legitimately appears twice, **name it and scope the check to
  the series where uniqueness is ruled.**

## WHAT YOU MUST NOT DO

- **Do not edit `dev/`, `src/`, `AGENTS.md`, or any brief or report but your
  own.** DD0: a `DD` row is the owner's and is not edited unless the owner asks.
- **Do not edit another proposal's file.** Three siblings are building
  `[LJ-1.191]` to `[LJ-1.194]` right now and their write territories do not
  overlap yours. **Stay inside SCOPE (write).**
- **Do not run Agda and do not dispatch an agent.**
- **Do not run `dispatch.py run`, `queue` or `resume`.** `check` and `status`
  launch nothing and are allowed.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE TRAP THIS PROJECT PAID FOR FIVE TIMES ON 2026-08-14

**A search that excludes what it looks for.** The orchestrator grepped
`(override)` in parentheses when the real form was `` (version `override`, ...)
``, got 5 hits against a true 52, and acted on the 5. **Sweep by SHAPE, never by
one spelling, and say which searches you ran.**

## THE CLASSIFICATION I WANT

**MEASURED, INFERRED or UNMEASURED, in those words**, on every claim your
deliverable makes about how the machine behaves.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Write the uniqueness test generic in the SERIES**, so it covers `DD`, the
retired `D`, and every LESSONS series with one code path rather than five. A
check written per series is paid for five times.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-189/lj-1.189-report.md`**, read WHOLE. **It is the
  proposal you are building, with its evidence at commit hashes, and its
  section 8 names what has NO cure so you do not promise one.**
- **`scripts/check-rule-ids.py`**, read WHOLE, and `scripts/tests/test_rule_series.py`.
- `dev/PLAN.md` section 3's preamble, for the consolidated and revoked codes:
  **they still RESOLVE and must not be reported as defects.**
- `dev/LESSONS.md` **C-32, C-39, C-40, C-41, C-42, C-43**, read WHOLE. **They
  are the process laws already admitted, and C-32's failure to reach the moment
  of action is the argument this whole batch rests on.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Not this task's subject. Say so in one line.**

## SCOPE (read)

`agents/tasks/LJ-1-189/lj-1.189-report.md` FIRST, whole.

## SCOPE (write)

`scripts/check-rule-ids.py`, `scripts/tests/test_rule_series.py`, and
`agents/tasks/LJ-1-194/lj-1.194-report.md`. **Nothing else.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-42.** A refutation measures the site it names, never its extent.
- **C-43.** An escape hatch is the shape a wrong choice hides in.
- **P-l, D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-36, C-37, C-39,
  C-40. I-5. DD0.**

## CONSTRAINTS

- Run `python3 scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line` or a commit hash. Write ASD-STE100.

## RETURN

**Lead with the three runs: the real tree passing, a synthetic duplicate
failing, and the test.** Then any real duplicate you found, reported and NOT
fixed. Then what the check cannot see. **Mark every claim MEASURED or
INFERRED.**
