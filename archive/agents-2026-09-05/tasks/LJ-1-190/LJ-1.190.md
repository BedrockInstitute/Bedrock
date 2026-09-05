# LJ-1.190: reconcile `dispatch.py` against the dispatch SKILL, and delete what is stale

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-flash`**, by the owner's
rule of 2026-08-14: work that touches no Agda code takes flash. **The model is a
command-line flag and this line only records the choice**, which `[LJ-1.188]`
MEASURED.

## GOAL

**Two documents describe one machine and they may disagree.**

- `.claude/skills/codex-dispatch/dispatch.py`, **2,270 lines**, the tool every
  dispatch passes through.
- `.claude/skills/dispatch-herdr/SKILL.md`, **410 lines**, written yesterday
  from that file plus the orchestrator's own errors.

**Find every contradiction between them. Then delete what is STALE or REDUNDANT
in the SCRIPT.**

## WHEN YOU CANNOT JUDGE, THE `DD` CANON RULES

**The owner's instruction, and it settles every tie.** `dev/PLAN.md` section 3
is the canon. The switch, `scripts/dispatch_policy.py`, is the one home of
DD17's tables.

**Order of authority, highest first:**

1. **A `DD` row** in `dev/PLAN.md` section 3.
2. **`scripts/dispatch_policy.py`**, for heads, modes and the model rule.
3. **`dispatch.py`'s behaviour**, which is what actually runs.
4. **`SKILL.md`**, which is a description of 1 to 3.

**A disagreement between 3 and 4 is usually the skill being wrong. A
disagreement between 1 and 3 is the SCRIPT being stale, and that is the
interesting case.**

## ONE CONTRADICTION IS ALREADY MEASURED, so you know the shape

`[LJ-1.188]` MEASURED that **the model is a command-line flag and `dispatch.py`
never reads it from the brief's `tier:` line.** The first `[LJ-1.187]` launch
ran `deepseek-v4-pro` while its brief named flash. **The skill records this
correctly. Check whether the script's own comments do.**

## WHAT IS KNOWN TO BE STALE, and each needs your verdict

**1. THE `_build/briefs/` PINNING PATH.** The owner merged briefs and reports
into `agents/tasks/<CODE>/`. `dispatch.py` demanded `_build/briefs/` until
2026-08-14 and **refused every dispatch for days without anyone seeing it**,
because the mode in force sent every default in-harness. Both homes are accepted
now. **`_build/` is git-ignored and `make clean` empties it, and the directory
no longer exists.** **Say whether the legacy branch is dead code, and delete it
if it is.**

**2. THE PRE-SWITCH DEFAULTS.** DD17 once made codex the default for every
dispatch. It no longer does, and the switch owns the tables. **Any comment or
constant in the script that still asserts a fixed default is stale.**

**3. THE RETIRED MODE NAMES.** `normal` and `override` were renamed 2026-08-14
to `deepseek-subagent-mode` and `in-harness-subagent-mode`. **The names must
keep RESOLVING through `ALIASES`, because 52 frozen briefs carry one (C-41), but
prose that presents them as current is stale.**

**Find more. That list is mine and it may be exactly wrong.**

## WHAT YOU MUST NOT DELETE, and this is the load-bearing prohibition

**EVERY REFUSAL EXISTS BECAUSE A FAILURE HAPPENED.** The file's own header
records the three that built it: a dead model that killed two agents silently, a
read-only sandbox that blocked a report, and a killed watcher that took two live
agents with it. It was then hardened against an adversarial review that found 18
defects with reproductions.

**So: do NOT delete a refusal, a retry loop, a lock, or a guard, unless you can
show the failure it prevents can no longer occur.** 「It looks redundant」 is not
that showing. **A comment explaining WHY a refusal exists is not redundancy: it
is the only record of the incident, and deleting it makes the refusal look
arbitrary to the next reader.**

**What IS deletable:** a code path nothing can reach, a constant nothing reads,
a comment that describes behaviour the file no longer has, and a duplicated
statement of a rule the canon owns.

## THE ACCEPTANCE TEST, and you run it BEFORE and AFTER

**`python3 .claude/skills/codex-dispatch/dispatch.py check <brief>` on at least
SIX live briefs**, chosen to span the kinds: a build, a probe, a recon, a
rewrite, an adversarial review, and one of the pre-epoch briefs.

**Record the exit code and the output for each, before your edit and after.
Identical results are the requirement.** A brief that passed must still pass; a
brief that would be refused must still be refused for the same reason.

**If any result changes, you have changed behaviour and not deleted staleness.
Revert that edit and report it.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **RECONCILED.** Report the contradictions, the deletions with line counts, and
  the before-and-after test table. STOP.
- **THE SCRIPT IS RIGHT AND THE SKILL IS WRONG.** **Say so and do NOT edit the
  skill**; report the correction and let the orchestrator rule where it lands.
- **A DELETION WOULD CHANGE BEHAVIOUR.** Leave it and name it. **A guard you
  left with a reason is a better return than one you removed.**
- **THE CANON ITSELF IS SILENT.** If a tie has no `DD` and no switch entry to
  settle it, **that is a finding for the owner**: name it and stop on it.

## WHAT YOU MUST NOT DO

- **Do not edit `.claude/skills/dispatch-herdr/SKILL.md`.** Report its errors;
  the orchestrator rules them.
- **Do not edit `scripts/dispatch_policy.py`, any checker, `dev/`, or `src/`.**
- **Do not dispatch an agent, and do not run Agda.** Siblings are live.
- **Do not run `dispatch.py run`, `queue` or `resume`.** **`check` and `status`
  only**, which launch nothing.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`.

## THE TRAP THIS PROJECT PAID FOR FIVE TIMES ON 2026-08-14

**A search that excludes what it looks for.** The orchestrator grepped
`(override)` in parentheses when the real form was `` (version `override`, ...)
``, got 5 against a true 52, and acted on the 5. **So sweep the script by SHAPE
and never by one spelling**, and say which searches you ran.

## THE CLASSIFICATION I WANT ON EVERY JUDGEMENT

**CONTRADICTION, STALE, REDUNDANT or KEPT, in those words**, and for every
deletion, **MEASURED or INFERRED** on the claim that nothing reaches it.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Here DD4 is a question about the script: is any refusal written for ONE mode
or ONE head when it should be written for both?** A guard that only fires under
the mode that happened to be in force is the shape that let the `_build/briefs/`
defect hide for days. **Report any you find; do not rewrite them without saying
so.**

## ARCHIVE (DD18)

- **`.claude/skills/codex-dispatch/dispatch.py`**, read WHOLE. **Its header and
  its per-defect comments are the primary record of why each guard exists.**
- **`.claude/skills/dispatch-herdr/SKILL.md`**, read WHOLE. The other side.
- **`scripts/dispatch_policy.py`** WHOLE: the switch, `ALIASES`, `model_for()`.
- `dev/PLAN.md` DD0, DD17, DD18, DD25 and `dev/ORCHESTRATION.md` sections 1 to
  3. **Read them; do not edit them.**
- `agents/tasks/LJ-1-188/lj-1.188-report.md`: what the skill's author measured
  and what it corrected in its own brief.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Not this task's subject. Say so in one line.**

## SCOPE (read)

`.claude/skills/codex-dispatch/dispatch.py` FIRST, whole.

## SCOPE (write)

`.claude/skills/codex-dispatch/dispatch.py` and
`agents/tasks/LJ-1-190/lj-1.190-report.md`. **Nothing else.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for rewrite` and read every statement.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-41.** A retired name must keep resolving at every citation.
- **C-42.** A refutation measures the site it names, never its extent.
- **C-43.** An escape hatch is the shape a wrong choice hides in.
- **D-27.** 「No consumer」 identifies a dead helper, never a dead result.
- **P-l, D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-36, C-37, C-39,
  C-40. I-5. DD0.**

## CONSTRAINTS

- Run `python3 scripts/lint-prose.py --check` on your report.
- **The script must remain valid Python**: `python3 -m py_compile` it after
  every edit, and report that you did.
- **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the contradiction count and the lines deleted.** Then the
before-and-after `check` table over six briefs. Then every contradiction, with
which side the canon says is right. Then every deletion with its MEASURED or
INFERRED unreachability claim. Then what you left and why. **Mark every
judgement CONTRADICTION, STALE, REDUNDANT or KEPT.**
