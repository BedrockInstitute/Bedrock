# LJ-1.207: auto-switch the dispatch mode on DeepSeek's peak and off-peak clock

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-flash`**, by the owner's
rule of 2026-08-14: work that touches no Agda code takes flash.

## GOAL

**The owner's instruction, 2026-08-14:**

> DeepSeek uses peak and off-peak pricing. **The off-peak price is HALF the peak
> price. Peak is Beijing time 09:00 to 12:00 and 14:00 to 18:00; everything else
> is off-peak.**

**Make the dispatch mode follow that clock automatically.**

**OFF-PEAK: `deepseek-subagent-mode` leads**, because deepseek is half price
then. **PEAK: `in-harness-subagent-mode` leads**, because deepseek is dear and
the in-harness Opus is not billed on that clock.

## WHERE IT GOES, and it is ONE place

**`scripts/dispatch_policy.py` is the ONLY home of DD17's tables** and it
already holds `VERSION_IN_FORCE`, `ALIASES` and `model_for()`. **The clock rule
goes there and nowhere else.** A head or a mode restated anywhere else is the
DD19 canonical-twice defect, and `[LJ-1.183]` found exactly that in this
project's rulebook this week.

## THE DESIGN CONSTRAINTS, and they are what make this safe

1. **THE OWNER'S EXPLICIT SETTING ALWAYS WINS.** `VERSION_IN_FORCE` is a
   ruling. **The clock decides only when the owner has not pinned a mode**, and
   the file must make that order visible in one read. **A tool that silently
   overrides a ruling is worse than no tool.**
2. **THE SWITCH MUST STILL PRINT WHY.** `dispatch_policy.py` prints the version
   in force, when it was set, by whom, why, and what reverts it. **A
   clock-selected mode prints the window it is in and the next boundary**, so a
   reader never has to compute it.
3. **BEIJING TIME, NOT LOCAL TIME.** The rule is stated in Beijing time. **Do
   the conversion explicitly and say how**; a machine in another zone must get
   the same answer.
4. **THE BOUNDARY CASES ARE THE TEST.** 08:59, 09:00, 12:00, 13:59, 14:00,
   18:00. **Say which side each falls on and pin it in a test.**
5. **A DISPATCH IN FLIGHT KEEPS ITS MODE.** DD17's own switch checklist says a
   running agent keeps the head that was correct when it was sent, and the
   checker judges a brief by the mode the brief NAMES. **Crossing a boundary
   must not retro-invalidate a live brief.**

## THE HALF THIS COULD GET WRONG, and it is worth stating

**The saving is real but the invariant is not negotiable.** DD17's invariant is
that **the critic is never the same head as the author**, and the two modes swap
exactly the default and adversarial rows to keep it. **A clock that flips the
default must flip the adversarial row with it, which the existing tables already
do.** **Confirm that, do not assume it.**

**And the emergency tier is untouched:** it binds two conditions and neither is
a clock.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **LANDED.** The clock selects, the owner's pin still wins, the boundaries are
  pinned in a test, and the acceptance test passes. STOP.
- **THE CLOCK CANNOT BE MADE SAFE.** If a live dispatch could be
  retro-invalidated and you cannot prevent it, **say so and change nothing.**
- **THE OWNER'S PIN AND THE CLOCK CANNOT BE ORDERED CLEANLY.** Name the case
  and stop. **A ruling silently overridden by a clock is the worst outcome
  available.**

## THE ACCEPTANCE TEST, and run it BEFORE and AFTER

1. **Copy `scripts/dispatch_policy.py` aside** and say where.
2. **`python3 scripts/dispatch_policy.py`** must still print the version, the
   provenance and the full table for both modes.
3. **`python3 scripts/check-dispatch-policy.py`** must stay clean over all 500+
   briefs. **It judges a brief by the mode the brief NAMES**, so a clock change
   must not redden a frozen record.
4. **Six briefs through `dispatch.py check`, before and after**, identical.
   `agents/tasks/LJ-1-157/LJ-1.157.md` is refused for carrying no DD4 and is a
   good control.
5. **Pin the six boundary times in a test** beside `scripts/tests/`.

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

**Write the clock generic in the WINDOWS, not in the two modes.** A second
provider with different windows, or a change to DeepSeek's hours, must be one
edit to a table and not a rewrite. A clock written for one price list is paid
for twice.

## ARCHIVE (DD18)

- **`scripts/dispatch_policy.py`** WHOLE: `VERSION_IN_FORCE`, the two mode
  tables, `ALIASES`, `model_for()`, and the provenance it prints.
- **`scripts/check-dispatch-policy.py`**, and especially how it judges a brief
  by the mode the brief NAMES rather than by today's switch.
- `.claude/skills/dispatch-herdr/SKILL.md`: the modes section and the six-step
  switch checklist, which you must keep true.
- `agents/tasks/LJ-1-203/lj-1.203-report.md`: what is Bedrock law and what is
  not.
- `dev/PLAN.md` DD0, DD17 and DD25, and `dev/ORCHESTRATION.md` sections 1 to 3.
  **Read them; do not edit them.** DD0: a `DD` row is the owner's and is edited
  only when the owner asks.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Not this task's subject. Say so in one line.**

## SCOPE (read)

`scripts/dispatch_policy.py` FIRST, whole.

## SCOPE (write)

`scripts/dispatch_policy.py`, `scripts/tests/` for the boundary test,
`.claude/skills/dispatch-herdr/SKILL.md`, and
`agents/tasks/LJ-1-207/lj-1.207-report.md`. **Nothing else.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for rewrite` and read every statement.

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

**Lead with the rule as you implemented it, in two lines, and with what the
mode is RIGHT NOW and why.** Then the precedence between the owner's pin and the
clock, quoted from your code. Then the six boundary cases with which side each
falls on. Then the acceptance table. **Mark every behavioural claim MEASURED or
INFERRED.**
