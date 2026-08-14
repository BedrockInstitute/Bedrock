# LJ-1.208: gate DD25, because the orchestrator forgets it

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-flash`**, by the owner's
rule of 2026-08-14: work that touches no Agda code takes flash.

## GOAL

**The owner asked what mechanism would make DD25 actually execute, because
the orchestrator keeps forgetting it.**

**DD25:** a negative return is adversarially reviewed at maximum effort,
IMMEDIATELY, and the two are then read together. **Its own declared enforcement
point is the index row: `dev/PLAN.md` section 11's row for a negative return
must NAME its review's code.**

**MEASURED, twice this week:** `[LJ-1.183]`, an audit, found that no negative
return had named a review code. The orchestrator fixed four rows, then let four
MORE negatives go unreviewed inside the same session, and the owner caught it
again.

**Build the gate.**

## WHY THIS IS MECHANICAL, and that is the whole argument

**The verdict cell of an index row is structured text**, and a negative verdict
announces itself: `STOP`, `NO-GO`, `REFUTED`, `BLOCKED`, `FALSE`, `WALL`,
`OVERTURNED`, `DOES NOT`, `NOTHING`, `ZERO`. **A row that carries one of those
and does not name a review code is DD25 unmet, and nothing has to read a mind to
see it.**

**This is `[LJ-1.194]`'s shape exactly.** The orchestrator minted a duplicate
`DD27` and the resolver reported CLEAN, because it verified that a code
RESOLVES and never that a code is UNIQUE. **Uniqueness was mechanical; so is
this.**

## WHAT THE GATE CANNOT DO, and say so in its own docstring

- **It cannot tell whether a verdict is REALLY negative.** A row reading 「GO at
  20 lines, AND A NEW WALL」 is positive and negative at once. **So it must be
  tunable and it must explain itself, and a false positive must be cheap to
  silence with a reason rather than by deleting a word.**
- **It cannot tell whether the review was any GOOD.** DD25 asks for an
  adversarial review; this checks that one was NAMED.
- **It cannot fire at the moment the return lands**, which is when the
  orchestrator forgets. **The honest enforcement point is the commit or the
  gate, and the docstring must say that rather than claim more.**

**`AGENTS.md` says a row claiming more than its checker delivers turns a rule
into false safety. Write the limits down.**

## THE PRE-EPOCH QUESTION, and answer it the way this project already does

**Every negative row before today is frozen history.** `check-dd4-stated.py`
solved this with a `PRE_EPOCH` set: the twelve frozen briefs are reported once
and never fail. **Do the same**, so the gate is green from its first run instead
of carrying a backlog nobody will fix.

**But measure the backlog first and report its size**, because that number is
the honest scale of the lapse.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BUILT AND GREEN.** The real tree passes, a synthetic negative row without a
  review code fails, and the backlog is counted. **Show all three.** STOP.
- **THE VERDICT CELL IS NOT SEPARABLE.** If a negative cannot be recognized
  without reading a mind, **say so and propose the next best thing**: a report
  that lists candidates rather than a gate that fails.
- **THE BACKLOG IS THE FINDING.** If most rows would fail, **say so with the
  count** and grandfather them.

## THE ACCEPTANCE TEST, and run it BEFORE and AFTER

1. **`python3 scripts/check-<your-name>.py` on the real tree** must exit 0
   after grandfathering, and print the backlog count.
2. **A synthetic index row** with a negative verdict and no review code must
   make it exit 1, with a message that names the row and says what to do.
3. **A row that DOES name a review code must pass.** `[LJ-1.162]`, `[LJ-1.165]`,
   `[LJ-1.169]` and `[LJ-1.172]` all name theirs today and are good controls.
4. **Wire it into `make check`** beside the other gates, and give it its own
   target.
5. **`make check`'s other gates must be unaffected**: run
   `check-task-index.py`, `check-rule-ids.py` and `check-dd4-stated.py` after.

## WHAT YOU MUST NOT DO

- **Do not weaken or delete a REFUSAL.** Each encodes a real incident, and
  `[LJ-1.203]` classified them as project law no general tool can carry.
- **Do not touch a live sibling's pane, agent or files.** Agents are running.
- **Do not run Agda.** Both Agda slots are held.
- **Do not dispatch through `dispatch.py`.** `check` and `status` launch
  nothing and are allowed.
- **Do not edit `.claude/skills/herdr/SKILL.md`.** It regenerates from
  `herdr --skill`.
- **`dispatch.py` and the skills are GIT-IGNORED**, so a bad edit has no
  `git checkout` to undo it. **Copy any file you edit aside first and say
  where.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`.
- **Create your report file in your FIRST five minutes (C-22).** An agent died
  on 2026-08-14 having written nothing.

## THE CLASSIFICATION I WANT

**MEASURED, INFERRED or UNMEASURED, in those words**, on every claim about how
the machine behaves. **This project shipped a wrong claim by reading a `--help`
line and calling it MEASURED when the claim was about BEHAVIOUR.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Write the negative-verdict vocabulary as a TABLE, not as a regex buried in a
function.** The next rule that needs 「what counts as a negative」 should read the
table rather than reinvent it, and a vocabulary written inline is paid for
twice.

## ARCHIVE (DD18)

- **`scripts/check-dd4-stated.py`**, read WHOLE. **It is the shape to follow:
  a narrow gate, an epoch set, and a docstring that states its own limits.**
- **`scripts/check-task-index.py`**, for how an index row is parsed today.
- `scripts/check-rule-ids.py`, as `[LJ-1.194]` extended it: one code path for
  every series.
- **`agents/tasks/LJ-1-183/lj-1.183-report.md`**, which MEASURED the DD25 lapse
  and named the index row as the unmet enforcement point.
- `dev/PLAN.md` DD0, DD17 and DD25, and `dev/ORCHESTRATION.md` sections 1 to 3.
  **Read them; do not edit them.** DD0: a `DD` row is the owner's and is edited
  only when the owner asks.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Not this task's subject. Say so in one line.**

## SCOPE (read)

`scripts/check-dd4-stated.py` FIRST, whole.

## SCOPE (write)

`scripts/check-<your-name>.py`, `Makefile`, `scripts/tests/` for its test,
and `agents/tasks/LJ-1-208/lj-1.208-report.md`. **Nothing else, and in
particular NOT `dev/PLAN.md`: a row is the owner's under DD0 and this gate
reports, it does not repair.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-41.** A retired name must keep resolving at every citation.
- **C-42.** A refutation measures the site it names, never its extent.
- **C-43.** An escape hatch is the shape a wrong choice hides in.
- **P-l, D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-36, C-37, C-39,
  C-40. I-5. DD0.**

## CONSTRAINTS

- Run `python3 scripts/lint-prose.py --check` on your report.
- **The file must stay valid Python**: `python3 -m py_compile` after every edit,
  and report that you did.
- **No em dash in any language.**
- Evidence is a command and its output, or a `file:line`. Write ASD-STE100.

## RETURN

**Lead with the three runs: the real tree passing, a synthetic negative row
failing, and the backlog count.** Then the negative-verdict vocabulary as you
wrote it. Then what the gate cannot see, quoted from your docstring. Then the
`make check` wiring. **Mark every behavioural claim MEASURED or INFERRED.**
