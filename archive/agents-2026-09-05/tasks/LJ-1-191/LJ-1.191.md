# LJ-1.191: build P1, the load-bearing-claim SKILL

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-flash`**, by the owner's
rule of 2026-08-14: work that touches no Agda code takes flash. **The model is a
command-line flag and this line only records the choice.**

## GOAL

**`[LJ-1.189]` measured that the orchestrator's recurring errors are ONE disease
in seven costumes: it records and acts on a claim, a search result, a figure, a
status field, a named source or a premise, and the claim is not bound to an
artifact it opened.**

**P1 is the first cure and the one to build first. Build it.**

## WHY A SKILL AND NOT A LESSON, and the argument is measured

**`dev/LESSONS.md` C-32, the figure-freshening law, has existed since
2026-08-11.** Its own measured instance records the orchestrator holding a
pre-cure figure and quoting it three times.

**Two days after C-32 was admitted, the same orchestrator quoted a pre-seal bar
into a brief, inherited a bar in the wrong direction, and left three false
figures in the live status screen.**

**The lesson did not reach the moment of action.** That is the brief's own
condition for needing a skill, and the moment is a WRITING moment with writable
keywords.

## THE TRIGGER REQUIREMENT, and it is the part most likely to be got wrong

**The skill must auto-load from the MODEL side, on the model's own keywords,
never from something the owner types.** NOT a slash command, NOT a magic word.

**The `description:` field in the frontmatter is the whole mechanism.** Read
`.claude/skills/dispatch-herdr/SKILL.md` and `.claude/skills/asd-ste100/SKILL.md`
for the shape: the description says what the skill DOES, then lists trigger
phrases.

**`[LJ-1.189]` set the test that can refute a skill by its own mechanism: would
this skill have LOADED at the moment the error happened?** **For this skill the answer is yes, and say why: the
error happens while the model is writing a claim into a brief, a plan, a status
screen, a commit body or a checker, and those are keyword-rich moments.**

**Answer that in your report and quote your description whole.**

## WHAT THE SKILL MUST HOLD

**`[LJ-1.189]` section 4 lists the rules with their episodes at commit hashes.
Take them from there rather than from my summary, and keep every hash.**

**The two that carry the most weight:**

1. **A claim written as MEASURED names the SEARCH that established it, AND the
   search's filter.** The founding case wrote 「MEASURED: nothing supplies it」 on
   a grep whose own filter excluded the file holding sixteen hits.
2. **A figure written into any document traces to the report row that MEASURED
   it, at `file:line`.** A figure from a plan paragraph, a note, a status screen
   or a memory is a hypothesis and never a price (P-l).

**Write the rest from the report. Do not invent rules it did not measure.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BUILT.** The skill exists, its description names the triggers, every rule
  from `[LJ-1.189]` section 4 is in it with its evidence. Quote the description.
  STOP.
- **A RULE CANNOT BE WRITTEN AS A TRIGGER.** **Say so.** `[LJ-1.189]` warns that
  a proposal whose trigger cannot be written is refuted by its own mechanism.
- **A RULE IN THE PROPOSAL IS WRONG.** The report cites commit hashes. **If a
  hash does not say what the report claims, that is the most valuable thing you
  can return.**

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

**Here DD4 applies to the skill itself: write it so it serves ANY task kind and
any document, not the six figures that happened to go wrong this week.** A skill
written for one document is paid for twice.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-189/lj-1.189-report.md`**, read WHOLE. **It is the
  proposal you are building, with its evidence at commit hashes, and its
  section 8 names what has NO cure so you do not promise one.**
- `.claude/skills/dispatch-herdr/SKILL.md`, read WHOLE, for the shape
  `[LJ-1.188]` set and for how its description is written.
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
`agents/tasks/LJ-1-191/lj-1.191-report.md`. **Nothing else.**

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
a checklist of `[LJ-1.189]` section 4's rules, each marked present or absent.
Then your answer to the would-it-have-loaded test. Then anything in the proposal
that its own cited commits contradict.
