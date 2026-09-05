# LJ-1.189: which recurring orchestrator errors would a SKILL prevent

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-flash`**, by the rule
the owner set 2026-08-14: pure natural-language work that touches no Agda code
takes flash. `scripts/dispatch_policy.py` holds it as `model_for()`.

## GOAL

**`[LJ-1.188]` turned the dispatch and `herdr` knowledge into a skill because
the orchestrator kept making the same mistakes there.**

**Find the OTHER recurring orchestrator errors, and say which of them a SKILL
would actually prevent.**

## THIS IS A PROPOSAL. YOU WRITE NO SKILL

**Deliverable: a proposal for the owner. Nothing is created, nothing is edited.**

**Do not write a `SKILL.md`. Do not edit a checker. Do not touch `dev/`.** Your
report is the whole product, and the owner rules what gets built.

## THE DISTINCTION THAT IS THE WHOLE TASK

**A recurring error has exactly one cheapest cure, and naming the wrong one
wastes the fix.**

| the error is | the cure is | because |
|---|---|---|
| **「I did not KNOW or did not RECALL at the moment of acting」** | **a SKILL** | it auto-loads on the model's own keywords, at the moment of action |
| **「I did it, and nothing caught it」** | **a CHECKER** | the act is mechanical and a gate can see it |
| **「nobody had DECIDED」** | **a `DD` ruling** | the owner rules it |
| **「it was measured once and is now a law」** | **a `dev/LESSONS.md` entry** | measurements bind new code |

**For every error you propose, say which of the four it is, and why the other
three are worse.** A proposal that says 「add a skill」 without that argument is
half a proposal.

**AND SAY WHEN THE ANSWER IS NONE.** Some errors are attention failures that no
document prevents. **Naming one honestly is worth more than a skill nobody
loads.**

## THE KNOWN LIST, and your value is in what is NOT on it

**These are MEASURED, all on 2026-08-14, all the orchestrator's own. Verify each
is real, then go past them.**

1. **A SEARCH THAT EXCLUDES WHAT IT LOOKS FOR. Five times in one day.** Grepped
   `(override)` in parentheses when the form was `` (version `override`, ...) ``
   and got 5 against a true 52. Grepped a struck ruling by its NUMBER when two
   sites wrote its NAME. Grepped `status` for `RUNNING`, which filters out the
   tool's own `!! N RETURN(S) NEVER REPORTED`. **The oldest instance is
   `[LJ-1.163]`: a grep excluded the file holding the answer and three
   dispatches priced a term the tree already had.**
2. **EDITING A FILE UNDER A RUNNING AGENT. At least three times.** A tool
   rewrite landed while a sibling was measuring with that tool and cost it four
   figures. Two directory-wide `git add -A` calls swept in a sibling's work.
3. **A BRIEF PREMISE THAT WAS FALSE. Six times.** Most recently `[LJ-1.177]`,
   sent to cure a term that `[LJ-1.158]` had cured five dispatches earlier,
   whose row sits DIRECTLY BELOW the row the brief cited.
4. **ACTING ON A FIGURE WITH NO MEASURED BASIS.** The 5,047 lines that were
   never measured. A +126 s extrapolation built on a delta inside the
   instrument's own band. A 16 s term that was a double subtraction and never
   existed.
5. **FIXING ONLY WHAT THE SEARCH COULD SEE, THEN DECLARING DONE. Three times in
   one hour.** An audit reported a struck ruling at three sites; the
   orchestrator fixed the one its grep matched and called the file clean.
6. **BELIEVING THE CODE OVER THE RULE IT CITES.** A refusal cited
   `dev/ORCHESTRATION.md` section 3, which said the opposite of what the code
   enforced, and the orchestrator built a workaround rather than opening the
   section.
7. **DERIVING A STANDING RULE FROM A ONE-OFF OWNER INSTRUCTION.** Now DD0 and
   `dev/LESSONS.md` C-43.

## WHERE TO MINE, and build your own list rather than trusting mine

- **`git log` with the commit BODIES read.** This orchestrator writes its
  reasoning and its errors into them, so the corpus is unusually honest.
- **`agents/tasks/*/` briefs and reports**, especially any return whose verdict
  refutes its own brief's premise.
- **`dev/JOURNAL.md`**, whose 2026-08-14 entry now holds the `DD` remainder.
- **`dev/LESSONS.md` C-39 to C-43**, which are the process laws already
  admitted. **An error already covered by a LESSONS entry needs no skill unless
  the entry never reaches the moment of action.**
- **`agents/tasks/LJ-1-183/lj-1.183-report.md`**, the audit of this
  orchestrator against every `DD`.
- **`agents/tasks/LJ-1-157/`**, the earlier audit of the same orchestrator.

## THE SHARPEST QUESTION TO ASK OF ANY SKILL PROPOSAL

**Would the skill have LOADED at the moment the error happened?**

A skill fires on the model's own keywords in its `description`. **So an error
that happens while the model believes it is doing something else will not be
caught by a skill about that something else.** The grep failures happened while
the orchestrator thought it was verifying, not searching.

**Answer that question for every proposal, and name the keywords that would
have fired.** A proposal whose trigger cannot be written is refuted by its own
mechanism.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **PROPOSED.** A ranked list, each with its cure kind and its trigger. STOP.
- **NOTHING BEYOND THE SEVEN.** **Say so plainly.** That would mean the record
  is already mined, which is a real result. **Do not manufacture proposals.**
- **AN ERROR HAS NO CURE.** Name it and say why. **This is the most valuable
  single line you can return**, because a skill nobody loads costs more than
  nothing: it makes the problem look solved.

## RANK BY WHAT THE ERROR COST

In dispatches, lines, seconds, or a wrong decision that shipped. **An error that
cost nothing is still an error and it is not the same finding.**

## WHAT YOU MUST NOT DO

- **Do not create or edit any skill.** `.claude/skills/` is read-only to you.
- **Do not edit `dev/`, `scripts/`, `src/`, or any brief or report but your
  own.**
- **Do not run Agda and do not dispatch an agent.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`.

## THE CLASSIFICATION I WANT ON EVERY FINDING

**MEASURED or INFERRED, in those words.** 「This happened N times」 is MEASURED
only if you counted and say which search found them. **And sweep by SHAPE, never
by one spelling**, which is finding 1 applied to your own method.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Here it is a question about your proposals: would each one serve ANY task kind
and any head, or only the case that bit this week?** `[LJ-1.188]`'s brief carried
the same test. **A skill written for one mode is paid for twice when the mode
flips.**

## ARCHIVE (DD18)

- **`.claude/skills/dispatch-herdr/SKILL.md`**, read WHOLE. **The skill
  `[LJ-1.188]` just wrote. It is your model for what a good one looks like, and
  for what its description must do.**
- `.claude/skills/asd-ste100/SKILL.md` and the other two, for the frontmatter
  shape.
- **`agents/tasks/LJ-1-183/` and `agents/tasks/LJ-1-157/`**, the two audits of
  this orchestrator.
- `archive/dev/JOURNAL-archived.md`: **the retired route ran for months and its
  orchestrator made mistakes too. An error that repeats across a route change is
  the strongest case for a skill.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Not this task's subject. Say so in one line.**

## SCOPE (read)

`.claude/skills/dispatch-herdr/SKILL.md` FIRST, then `git log` with bodies.

## SCOPE (write)

`agents/tasks/LJ-1-189/lj-1.189-report.md` ONLY.

## MANDATORY RULES

Run `python3 scripts/rules.py --for recon` and read every statement.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-42.** A refutation measures the site it names, never its extent. **So when
  you find one instance of an error, sweep for the rest of its shape.**
- **C-43.** An escape hatch is the shape a wrong choice hides in.
- **P-l.** A cure measured at one site is a hypothesis at another.
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **DD0, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-36, C-37, C-39, C-40.
  I-5.**

## CONSTRAINTS

- Run `python3 scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line` or a commit hash. Write ASD-STE100.

## RETURN

**Lead with the COUNT of proposals and the single one you would build first.**
Then the ranked table: the error, its cost, how many times it occurred, the cure
kind of the four, and the trigger keywords if the cure is a skill. Then every
error you found that has NO cure. Then what you swept and how. **Mark every
finding MEASURED or INFERRED.**
