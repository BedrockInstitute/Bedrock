# LJ-1.192: build P2, the artifact-over-proxy SKILL

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-flash`**, by the owner's
rule of 2026-08-14: work that touches no Agda code takes flash. **The model is a
command-line flag and this line only records the choice.**

## GOAL

**`[LJ-1.189]`'s second proposal. Build it.**

**THE RULE IN ONE LINE: the artifact is the evidence; the status field is a
hint.**

**Three outcomes were recorded from a proxy on 2026-08-14, all by the
orchestrator.** It recorded a task as DIED because a status table said so, while
the report sat on disk. It read `RUNNING` after a re-dispatch and declared the
launch a success, when that row was the OLD agent and the launch log's third
line was the error. It read a verdict cell instead of opening the report.

**The commit that records the first one calls it the third time in one
session.**

## THE TRIGGER REQUIREMENT, and it is the part most likely to be got wrong

**The skill must auto-load from the MODEL side, on the model's own keywords,
never from something the owner types.** NOT a slash command, NOT a magic word.

**The `description:` field in the frontmatter is the whole mechanism.** Read
`.claude/skills/dispatch-herdr/SKILL.md` and `.claude/skills/asd-ste100/SKILL.md`
for the shape: the description says what the skill DOES, then lists trigger
phrases.

**`[LJ-1.189]` set the test that can refute a skill by its own mechanism: would
this skill have LOADED at the moment the error happened?** **For this skill the answer is yes: the error happens
while the model is about to RECORD an outcome it read from a table, a header, a
verdict cell, a note or a machine-load number.**

**Answer that in your report and quote your description whole.**

## WHAT THE SKILL MUST HOLD

**`[LJ-1.189]` section 5 lists the rules with their episodes. Take them from
there and keep every commit hash.**

**The shape to generalize, and it is broader than dispatch:** a status table, a
verdict cell in an index, a `STATUS:` header in a memo, a summary line in a
report, a machine-load figure, and a tool's own exit message are ALL proxies.
**The artifact is the file the claim is about.**

**And state the cheap test:** before recording an outcome, name the artifact you
opened. If you cannot name one, you read a proxy.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BUILT.** Quote the description and list the rules with their evidence. STOP.
- **THE SHAPE IS NARROWER THAN THE PROPOSAL CLAIMS.** If the three episodes are
  really one situation and not a class, **say so**: a skill for a single
  situation is worth less than an honest refusal.
- **A RULE CANNOT BE WRITTEN AS A TRIGGER.** Say so plainly.

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

**Write the skill for ANY proxy, not for `dispatch.py`'s status table.** The
episodes came from one tool; the disease is general, and a skill written for one
tool is paid for twice.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-189/lj-1.189-report.md`**, read WHOLE. **It is the
  proposal you are building, with its evidence at commit hashes, and its
  section 8 names what has NO cure so you do not promise one.**
- `.claude/skills/dispatch-herdr/SKILL.md`, read WHOLE, and note that its own
  mistake 2 is one of the three episodes this skill generalizes.
- `dev/LESSONS.md` **C-32, C-39, C-40, C-41, C-42, C-43**, read WHOLE. **They
  are the process laws already admitted, and C-32's failure to reach the moment
  of action is the argument this whole batch rests on.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Not this task's subject. Say so in one line.**

## SCOPE (read)

`agents/tasks/LJ-1-189/lj-1.189-report.md` FIRST, whole.

## SCOPE (write)

`.claude/skills/<your-name>/` and
`agents/tasks/LJ-1-192/lj-1.192-report.md`. **Nothing else.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for recon` and read every statement.

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

**Lead with the skill's path and its `description:` line, quoted whole.** Then
the rules with their evidence. Then your answer to the would-it-have-loaded
test. Then whether the shape is a class or a single situation, MEASURED.
