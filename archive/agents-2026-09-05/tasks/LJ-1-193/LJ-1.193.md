# LJ-1.193: build P3, the commit gate against live write territory

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-flash`**, by the owner's
rule of 2026-08-14: work that touches no Agda code takes flash. **The model is a
command-line flag and this line only records the choice.**

## GOAL

**`[LJ-1.189]`'s third proposal, and it is a CHECKER because the act is
mechanical.**

**Build a pre-commit check that refuses a staged file lying inside a LIVE
agent's write territory.**

**What it catches, MEASURED:** two directory-wide `git add -A` calls on
2026-08-13 swept a sibling agent's work in progress into the orchestrator's
commit. The habit rule 「commit by explicit path」 is recorded and it is
unenforced.
## WHAT ALREADY EXISTS, so you build less

**`dispatch.py` ALREADY computes write-scope intersections** for its own refusal
「a live agent whose write scope intersects this brief's」. **Read that code and
reuse its shape.**

**The registry is at `.claude/skills/codex-dispatch/.state/registry.json`** and
records live agents with their brief paths, MEASURED by `[LJ-1.189]`.

**`scripts/check-probes.py --staged` is the shape of a staged-file gate**, and
its `STAGED_FILTER` records a real defect: it must be `--diff-filter=ACMR`,
because `R` is renames and dropping it once hid 257 staged renames.
## THE DESIGN CONSTRAINTS

**It must be a GATE and it must be quiet when nothing is wrong.** A staged file
inside a live agent's territory is a defect with nothing left to judge, which is
why this is a gate and not a report.

**It must not fire when no agent is live**, and it must not fire on the
orchestrator's own task directory when that task has no live agent.

**It must name the agent and the file**, so the fix is obvious: commit by
explicit path, or wait.

**Wire it into `make check`** beside the other staged gates, and give it its own
target.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BUILT AND GREEN.** It refuses a synthetic staged file inside a live
  territory and passes on a clean index. **Show both runs.** STOP.
- **THE REGISTRY CANNOT BE READ RELIABLY.** If a live agent's territory is not
  derivable, **say what is missing**. A gate that fires wrongly is worse than
  none, because it trains the author to bypass it.
- **IT WOULD FIRE ON NORMAL WORK.** Name the case and stop. **A false positive
  here blocks every commit.**

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

**Write it generic in the territory source**, so it serves any registry shape
and any future dispatcher, not the one JSON file that exists today. A gate
written for one file is paid for twice.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-189/lj-1.189-report.md`**, read WHOLE. **It is the
  proposal you are building, with its evidence at commit hashes, and its
  section 8 names what has NO cure so you do not promise one.**
- **`scripts/check-probes.py`**, read WHOLE: the staged-gate shape, and its
  `STAGED_FILTER` comment, which records the rename defect.
- **`.claude/skills/codex-dispatch/dispatch.py`**, the write-scope intersection
  refusal. **Read it; do not edit it.** A sibling is editing that file.
- `dev/LESSONS.md` **C-32, C-39, C-40, C-41, C-42, C-43**, read WHOLE. **They
  are the process laws already admitted, and C-32's failure to reach the moment
  of action is the argument this whole batch rests on.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Not this task's subject. Say so in one line.**

## SCOPE (read)

`agents/tasks/LJ-1-189/lj-1.189-report.md` FIRST, whole.

## SCOPE (write)

`scripts/check-live-territory.py` (new), `Makefile`, and
`agents/tasks/LJ-1-193/lj-1.193-report.md`. **Nothing else, and in particular
NOT `dispatch.py`, which a sibling is editing.**

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

**Lead with the two runs: the refusal on a synthetic staged file, and the pass
on a clean index.** Then the design and what it cannot see. Then the `make check`
wiring. **Mark every behavioural claim MEASURED or INFERRED.**
