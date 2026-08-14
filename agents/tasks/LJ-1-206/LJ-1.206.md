# LJ-1.206: measure herdr's wait supersession, and land it if it holds

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-flash`**, by the owner's
rule of 2026-08-14: work that touches no Agda code takes flash.

## GOAL

**`[LJ-1.203]` measured that Agent Automation OPTIMIZES and COMPLETES the
dispatch machinery and never replaces it: 74 percent of `dispatch.py` is Bedrock
law no herdr feature can carry.**

**It found exactly ONE thing with a documented herdr supersession: the WAIT
PROTOCOL and the waiter.** **And it marked that supersession DOCUMENTED, not
MEASURED.**

**Measure it. If it holds, land it. If it does not, say so and change nothing.**

## WHY THIS IS THE ONE WORTH DOING

**The wait protocol is where this project has lost the most.** MEASURED, all on
2026-08-14:

- **One waiter reports once**, and three returns sat unread because the
  orchestrator armed one and moved on.
- **`queue --wait` ACCEPTS the flag and IGNORES it**; only `run --wait` honours
  it. The orchestrator wrote the opposite into the skill on the strength of a
  `--help` line, which is the exact failure `load-bearing-claim` exists for.
- **The driver's own wait is TWO PHASE**, because a one-phase `--until idle`
  returns at once: the agent is already idle at submission.
- **`herdr agent prompt` QUEUES and does not interrupt.** A stop instruction sat
  behind the 4.25-hour run it was telling the agent to stop, and was never read.

**If Agent Automation supersedes any of that, it is worth landing. If it does
not, the hand-rolled protocol keeps every line and we stop wondering.**

## WHAT TO MEASURE, and DOCUMENTED is not enough

**For each capability `[LJ-1.203]` reports as documented, run it and record what
happened.**

1. **Does the automation layer deliver ONE notification PER AGENT**, without a
   waiter to arm and re-arm?
2. **Does it survive the case that broke ours**: several agents live, one slow,
   the others returning first?
3. **Does it distinguish a RETURN from a DEATH from a BLOCK?** Our driver needs
   all three, and the blocked case is a ruling as of today.
4. **Can it interrupt a BUSY agent**, which `herdr agent prompt` cannot?

**Every answer needs the command you ran and its output. A capability you read
about and did not run is DOCUMENTED, and this brief does not accept DOCUMENTED
as an answer.**

## HOW TO MEASURE IT SAFELY, because live agents are on this machine

**Two siblings hold Agda slots and one is mid-recovery.**

**So: make your OWN agent to test against.** Dispatch nothing through
`dispatch.py`. Start a throwaway herdr agent in a pane you create, drive it, and
close it when you are done. **Never test against a sibling.**

**If you cannot make a safe test subject, say so and stop.** A measurement taken
against a live sibling would cost more than the answer is worth.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT HOLDS, AND LANDED.** You measured the supersession, changed the driver or
  the waiter, and the acceptance test below passes. Report both. STOP.
- **IT HOLDS BUT LANDING IS DEAR.** Report the measurement and the migration
  cost, change nothing, and let the orchestrator sequence it.
- **IT DOES NOT HOLD.** **Say so plainly and change NOTHING.** That is a
  complete answer: it retires a question this project has carried since
  `[LJ-1.203]`, and it means the hand-rolled protocol keeps its lines with a
  reason.
- **IT CANNOT BE MEASURED HERE.** If the automation layer needs a setup this
  machine does not have, name what is missing and stop.

## THE ACCEPTANCE TEST, if you land anything

**`dispatch.py` is the tool every dispatch passes through and it is
GIT-IGNORED, so a bad edit has no `git checkout` to undo it.**

1. **Copy the file aside first** and say where.
2. **`python3 -m py_compile` after every edit.**
3. **Run `dispatch.py check` on SIX briefs across the kinds, before and after.**
   Identical results are the requirement: a brief that passed must still pass, a
   brief that would be refused must still be refused for the SAME reason.
   `agents/tasks/LJ-1-157/LJ-1.157.md` is refused for carrying no DD4 and is a
   good control.
4. **Run `dispatch.py status` and confirm every banner still prints.**

**If any result changes, revert that edit and report it.**

## WHAT YOU MUST NOT DO

- **Do not weaken or delete a REFUSAL.** Every one encodes a real incident, and
  `[LJ-1.203]` classified them as project law that no herdr feature can carry.
- **Do not touch a live sibling's pane, agent or files.**
- **Do not run Agda.** Both slots are held.
- **Do not dispatch through `dispatch.py`.** `check` and `status` launch nothing
  and are allowed.
- **Do not edit `.claude/skills/herdr/SKILL.md`.** It regenerates from
  `herdr --skill` and an edit would be lost and would lie.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`.
- **Create your report file in your FIRST five minutes (C-22).**

## THE CLASSIFICATION I WANT ON EVERY CAPABILITY

**DOCUMENTED, MEASURED or REFUTED, in those words.** **This task exists because
`[LJ-1.203]` honestly marked its finding DOCUMENTED. Do not hand back another
DOCUMENTED.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Here: a mechanism herdr maintains that we hand-roll is one we pay for twice,
and the copy that drifts is OURS.** **But a refusal that encodes a Bedrock
ruling cannot be delegated, because the tool does not know the ruling.** Say
which side anything you land falls on.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-203/lj-1.203-report.md`**, read WHOLE. **The two-kind
  split, the five questions, and the one supersession you are here to measure.**
- **`.claude/skills/herdr/SKILL.md`**, the official skill from `herdr --skill`,
  and **`.claude/skills/dispatch-herdr/SKILL.md`**, ours as `[LJ-1.205]`
  reconciled it.
- **`.claude/skills/codex-dispatch/dispatch.py`**, the driver block and the
  waiter. **Its comments record why each retry and each existence check exists.**
- `agents/tasks/LJ-1-205/lj-1.205-report.md`: the reconciliation and the
  `blocked` finding the owner then ruled.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**The herdr documentation is this task's literature.** Return a **LITERATURE
USED** section with every URL, and say whether the site and `herdr --skill`
agree, **because a difference means the binary and the docs are out of step.**

## SCOPE (read)

`agents/tasks/LJ-1-203/lj-1.203-report.md` FIRST, whole.

## SCOPE (write)

`.claude/skills/codex-dispatch/dispatch.py`,
`.claude/skills/dispatch-herdr/SKILL.md`, and
`agents/tasks/LJ-1-206/lj-1.206-report.md`. **Nothing else.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for rewrite` and read every statement.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-42.** A refutation measures the site it names, never its extent.
- **C-43.** An escape hatch is the shape a wrong choice hides in.
- **P-l.** A capability measured elsewhere is a hypothesis here.
- **D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-36, C-37, C-39, C-40.
  I-5. DD0.**

## CONSTRAINTS

- Run `python3 scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is a command and its output, or a `file:line`. Write ASD-STE100.

## RETURN

**Lead with HOLDS or DOES NOT HOLD, in one word, and with what you landed or why
you landed nothing.** Then the four questions, each with the command you ran.
Then the before-and-after acceptance table over six briefs. Then what you would
do next. **Mark every capability DOCUMENTED, MEASURED or REFUTED.**
