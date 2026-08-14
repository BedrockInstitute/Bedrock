# LJ-1.205: reconcile our dispatch SKILL against herdr's official one

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-flash`**, by the owner's
rule of 2026-08-14: work that touches no Agda code takes flash.

## GOAL

**The owner installed herdr's OFFICIAL skill at `.claude/skills/herdr/SKILL.md`,
195 lines, obtained from `herdr --skill` rather than from the web, so it is the
version this binary ships.**

**Correct our own `.claude/skills/dispatch-herdr/SKILL.md` against it: fill what
is MISSING, delete what is DUPLICATED.**

## THE TWO SKILLS AND WHY BOTH EXIST

| | |
|---|---|
| `.claude/skills/herdr/SKILL.md` | **herdr's own**, 195 lines, authoritative on the TOOL |
| `.claude/skills/dispatch-herdr/SKILL.md` | **ours**, authoritative on BEDROCK'S USE of it: `dispatch.py`, the DD17 modes, the refusals, C-12's slots, and ten measured mistakes |

**Neither replaces the other. The official one cannot know DD17; ours must not
re-document `herdr agent list`.**

## THE FIRST THING TO NOTICE, and it is a real design difference

**The official skill's `description` says: 「Use only when the user explicitly
mentions Herdr or asks to use Herdr to inspect...」**

**Ours triggers from the MODEL side, on the model's own keywords, with no user
mention required.** That was the owner's explicit requirement for ours.

**So the two have OPPOSITE trigger philosophies and both are correct for their
purpose.** **Do not copy the official trigger into ours.** **Report the
difference and say whether it creates a gap: is there a case where a model needs
herdr facts and neither skill fires?**

## WHAT TO DO

1. **Read both WHOLE.**
2. **DUPLICATION: what does ours say that the official one already says
   better?** Delete it from ours and leave a pointer. **A fact documented in
   two places drifts**, and `[LJ-1.183]` found exactly that defect in this
   project's own rulebook this week.
3. **GAPS: what does the official one document that ours does not, and that a
   Bedrock dispatch would use?** Add it, or add a pointer if it belongs to the
   official skill.
4. **CONTRADICTIONS: where do they disagree?** **The official skill wins on the
   TOOL. Ours wins on BEDROCK'S RULES.** If ours states a tool fact the official
   one contradicts, ours is wrong unless we MEASURED otherwise, in which case
   say so and keep the measurement with its date.

## OUR MEASURED FACTS ARE NOT NEGOTIABLE, and this is the trap

**Our skill carries facts measured on THIS machine that the official
documentation may not mention:**

- `herdr agent` has **no `stop` and no `kill`** subcommand.
- **`pkill` does NOT kill a herdr agent**, because herdr owns the pane.
- **`send-keys C-c` did not stop a working pi agent**, marked UNMEASURED as a
  method.
- **`agent wait --until` is TWO PHASE**; a one-phase wait returns at once.
- **Names are lowercased**: `LJ-1.123` becomes `lj-1-123`.
- **A freshly split pane is not yet a shell**, so `agent start` retries.
- **A pane does not inherit the launcher's environment.**

**If the official skill documents a `stop` we did not find, say so and mark it
DOCUMENTED-NOT-MEASURED: that would be a finding worth a lot, because we have
been closing panes to stop agents.**

**But do NOT delete a measured fact because the official docs are silent about
it. Silence is not contradiction.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **RECONCILED.** Report what you deleted, what you added, and every
  contradiction with which side won. STOP.
- **OURS IS ALREADY RIGHT.** **Say so plainly.** `[LJ-1.186]` found nine of
  nineteen rows already correct and that was a real result. **Do not
  manufacture edits.**
- **THE OFFICIAL SKILL SUPERSEDES MOST OF OURS.** If the honest answer is that
  ours should shrink to the Bedrock-specific half, **say so with the line
  counts.** That would be the best outcome and it is what「删除重复」asks for.
- **A CONTRADICTION YOU CANNOT SETTLE.** Name it and leave both. **A fact you
  left with a reason beats one you resolved wrongly.**

## WHAT YOU MUST NOT DO

- **Do not edit `.claude/skills/herdr/SKILL.md`.** It is herdr's, regenerable by
  `herdr --skill`, and an edit would be lost and would lie.
- **Do not edit `dispatch.py`, `scripts/`, `dev/`, `src/`, or any brief or
  report but your own.**
- **Do not run `herdr agent start`, `prompt`, `send-keys`, `rename` or `attach`
  against a LIVE agent.** Two are running with Agda slots held. **`herdr agent
  list` and `get` are read-only and allowed.**
- **Do not dispatch an agent and do not run Agda.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`.

## THE CLASSIFICATION I WANT ON EVERY FACT YOU MOVE OR DELETE

**DOCUMENTED, MEASURED or INFERRED, in those words.**

- **DOCUMENTED**: the official skill says it.
- **MEASURED**: observed on this machine, and our skill records the date.
- **INFERRED**: neither.

**This project shipped a wrong claim yesterday by reading a `--help` line and
calling it MEASURED. The claim was about behaviour and the evidence was
documentation.** **Do not repeat it in either direction.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Here it is about the two skills: a fact maintained in both is a fact we pay
for twice, and the one that drifts is ours, because herdr's regenerates from the
binary.** **Prefer a pointer to a copy, every time.**

## ARCHIVE (DD18)

- **`.claude/skills/herdr/SKILL.md`**, read WHOLE. **The authority on the tool.**
- **`.claude/skills/dispatch-herdr/SKILL.md`**, read WHOLE. **Ours, including
  its ten measured mistakes and the modes.**
- `.claude/skills/codex-dispatch/dispatch.py`: **read its comments where the two
  skills disagree.** The code is what actually runs.
- `agents/tasks/LJ-1-188/lj-1.188-report.md`: how ours was built and what it
  corrected in its own brief.
- `agents/tasks/LJ-1-190/lj-1.190-report.md`: the last reconciliation of the
  script against ours, and the contradiction it left open.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**The herdr documentation is this task's literature and its local copy is the
installed skill.** If you fetch https://herdr.dev/docs/agent-skill/ say whether
it differs from `herdr --skill`'s output, **because a difference means the
binary and the site are out of step and that is worth knowing.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`.claude/skills/herdr/SKILL.md` FIRST, whole.

## SCOPE (write)

`.claude/skills/dispatch-herdr/SKILL.md` and
`agents/tasks/LJ-1-205/lj-1.205-report.md`. **Nothing else.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for rewrite` and read every statement.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-41.** A retired name must keep resolving at every citation.
- **C-42.** A refutation measures the site it names, never its extent.
- **C-43.** An escape hatch is the shape a wrong choice hides in.
- **P-l, D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-36, C-37, C-39,
  C-40. I-5. DD0.**

## CONSTRAINTS

- Run `python3 scripts/lint-prose.py --check` on your report. **The skills are
  exempt from the linter, like their siblings, but write ASD-STE100 anyway.**
- **No em dash in any language.**
- Evidence is `file:line` in one of the two skills, or a command and its output.

## RETURN

**Lead with three counts: lines deleted as duplication, lines added as gaps, and
contradictions found.** Then the deletion table with what each pointer now says.
Then the gap table. Then every contradiction with which side won and why. Then
the trigger-philosophy difference and whether it leaves a case uncovered.
**Mark every fact DOCUMENTED, MEASURED or INFERRED.**
