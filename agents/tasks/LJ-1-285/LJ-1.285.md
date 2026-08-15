# LJ-1.285: rename the dispatch mode off the vendor name

tier: opus (in-harness-subagent-mode), **model `sonnet`**: the owner named the
model. I ran `scripts/dispatch_policy.py` before dispatching:
`in-harness-subagent-mode` is IN FORCE, clock-selected, PEAK.

**THIS LINE WAS CORRECTED AFTER THE RUN, and the correction is recorded rather
than hidden.** It first read `tier: sonnet (...)`, which names a HEAD that does
not exist: the legal head tokens are `codex`, `fable`, `opus` and `pi`.
`scripts/check-dispatch-policy.py` refused it and the agent flagged it rather
than editing its own pinned brief, which was the right call.

**The defect is the orchestrator's and it is mistake 9 of the dispatch skill's
own ten: the head and the model are two different choices.** The head names the
harness and the path, here in-harness; the model is the separate axis and it
carries `sonnet`. **`sonnet` is not being added to the head tokens**, because
that would conflate the two axes DD17 keeps apart.

## GOAL

THE OWNER'S INSTRUCTION, in their own words: rename `deepseek` inside `deepseek-subagent-mode` to a more general name, and sweep the repository for `deepseek` and replace it consistently, BECAUSE WE MAY NOT STAY ON DEEPSEEK AND MAY USE OTHER NON-CLAUDE MODELS.

So the goal is not a string substitution. It is to remove a VENDOR name from a structural concept, so that swapping vendors later is a one-line change and not a repository sweep.

## THE NAME, and I am fixing it rather than delegating it

`pi-subagent-mode`.

The naming convention is the owner's own, 2026-08-14: each mode is named for the HEAD IT LEADS WITH. `in-harness-subagent-mode` leads with the in-harness Opus. The other mode leads with `pi`, which is the harness's agent name and carries no vendor. The tier tokens are already `opus`, `pi`, `codex`, `fable`, all vendor-neutral. So `pi-subagent-mode` follows the convention exactly and needs no new vocabulary.

## WHAT YOU MUST NOT CHANGE, and this is the part that matters most

**1. THE MODEL ID STRINGS ARE REAL API IDENTIFIERS. DO NOT RENAME THEM.**
`deepseek-v4-pro` and `deepseek-v4-flash` are what the backend accepts. MEASURED 2026-08-13: the API rejects `deepseek-v4-pro-0813`, and two agents died in seconds having written nothing before a refusal existed. Those literal strings stay exactly as they are, wherever they name a model passed to a tool.
The Python constants that hold them are already vendor-neutral, `MODEL` and `FLASH` at scripts/dispatch_policy.py:210 and :231. Generalize the COMMENTS around them so a later vendor swap is obvious, and change no literal value.

**2. DO NOT TOUCH agents/ OR archive/. THEY ARE FROZEN RECORDS.**
I measured this: 252 tracked files mention deepseek and 244 of them are under agents/. A brief and a report are records, and a record is never rewritten. dev/LESSONS.md C-41 is the law: a retired name that stops resolving turns every citation into a dangling pointer, and one that resolves to the WRONG thing is worse. archive/dev/JOURNAL-archived.md is frozen for the same reason.

**3. THE OLD NAME MUST KEEP RESOLVING FOREVER.**
Add `"deepseek-subagent-mode": "pi-subagent-mode"` to ALIASES in scripts/dispatch_policy.py:248-251, keeping the existing entries. `"normal"` currently maps to the old name and must be re-pointed to the new one so it still resolves in one hop. 210 occurrences of `deepseek-subagent-mode` live in frozen briefs and every one of them must keep working.

## THE LIVE SURFACE, which is 8 files and I measured it

  dev/JOURNAL.md
  dev/LESSONS.md
  dev/ORCHESTRATION.md
  dev/PLAN.md
  scripts/check-dispatch-policy.py
  scripts/dispatch_policy.py
  scripts/tests/test_dispatch_clock.py
  archive/dev/JOURNAL-archived.md    <- FROZEN. Do not edit. Listed so you do not wonder.

Check that list yourself with `git grep -il deepseek -- . ':!agents/'`. C-44: my list is a claim until you check it.

dev/JOURNAL.md is a dated record of what happened. Where it says a mode WAS named deepseek-subagent-mode on a given date, that sentence is history and stays true; do not rewrite history into the new name. Where it describes the CURRENT rule, update it. Judge each hit and say in your report which you changed and which you left, with a reason.

AGENTS.md does NOT mention deepseek. I checked. So DD19's gate does not fire and you must not edit AGENTS.md.

## DD17'S SIX-STEP CHECKLIST GOVERNS A RENAME. Read it in dev/PLAN.md section 3, the DD17 row, and follow it. Step 4 is exactly this case: "If a mode is RENAMED, the retired name keeps resolving through ALIASES (C-41), because briefs carry it."

Step 5 says: delete or rewrite any memory or document that asserted the outgoing name. Apply that to the live surface only.

## THE ACCEPTANCE TESTS, all of which must pass

1. `.venv/bin/python scripts/dispatch_policy.py` prints the new name and the correct clock line.
2. `.venv/bin/python scripts/dispatch_policy.py deepseek-subagent-mode` still resolves and renders, through the alias.
3. `.venv/bin/python scripts/check-dispatch-policy.py` exits 0 over every brief, including the 244 frozen ones that name the old mode. THIS IS THE TEST THAT MATTERS. If it goes red, the alias is wrong, not the records.
4. `.venv/bin/python -m pytest scripts/tests/test_dispatch_clock.py -q` passes. Update the test file's own uses of the old name.
5. `.venv/bin/python scripts/lint-prose.py --check` on every file you edited.
6. `.venv/bin/python scripts/check-rule-ids.py` exits 0.

There is one more consumer you cannot run a checker against: `.claude/skills/codex-dispatch/dispatch.py`. It is untracked and out of your write scope. It calls POLICY.in_force() and POLICY.canonical(), so the alias should carry it. VERIFY by running `.venv/bin/python .claude/skills/codex-dispatch/dispatch.py check agents/tasks/LJ-1-279/LJ-1.279.md --agda`, which is a frozen brief naming the OLD mode. Report what it prints. Do not edit that file; if it breaks, say so and I fix it.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- ALL SIX TESTS PASS. Report each with its output line. STOP.
- A FROZEN BRIEF GOES RED. The alias is wrong. Fix the alias, never the brief.
- A MODEL ID WAS ABOUT TO BE RENAMED. Stop and say where. That is the failure this brief exists to prevent.
- THE NAME `pi-subagent-mode` IS ALREADY TAKEN OR COLLIDES. Say so and propose one, with the convention's reason.

## CONSTRAINTS

- Write scope: scripts/dispatch_policy.py, scripts/check-dispatch-policy.py, scripts/tests/test_dispatch_clock.py, dev/PLAN.md, dev/ORCHESTRATION.md, dev/LESSONS.md, dev/JOURNAL.md, and agents/tasks/LJ-1-285/ for your brief and report. NOTHING under agents/tasks/ except your own directory. NOTHING under archive/. NOT AGENTS.md. NOT CLAUDE.md. NOT src/. NOT .claude/.
- THREE SIBLINGS ARE LIVE and none of them touches your files: [LJ-1.283] in agents/tasks/LJ-1-283/, [LJ-1.284] in agents/tasks/LJ-1-284/ and src/L/Absorption.lagda.md and src/L/InjChain.lagda.md. Do not touch any of those paths.
- dev/PLAN.md is the live status screen and I write it. You may change ONLY the mode name where it appears there, and you must not touch its section 0 status text, its section 11 table rows, or any figure.
- DO NOT RUN AGDA. Two siblings hold the Agda work.
- Never commit, never push, never git checkout ., git stash, git reset --hard, git clean. Do not run make check.
- NO EM DASH in any language. Use full-width punctuation in CJK prose. Write ASD-STE100 Simplified Technical English in your report: one meaning per word, active voice, simple tenses, one instruction per sentence, 20 words or fewer for an instruction and 25 for a description.
- Create agents/tasks/LJ-1-285/lj-1.285-report.md in your first five minutes and fill it incrementally (C-22).
- Evidence is file:line. Mark every negative MEASURED or INFERRED, in those words.

## DD4

Maximize the code the two proofs share, and write it generic. One rule, two ends, no metric and no checker. This task writes no mathematics, so DD4 does not bind its content. It binds its SHAPE, and the connection is real: the reason the owner asked for this rename is the same reason DD4 exists, which is that a name tied to one instance costs a sweep when the instance changes. Say in one line whether the renamed structure would survive a third mode being added.

## ARCHIVE (DD18)

archive/dev/JOURNAL-archived.md holds the mode's earlier history and is FROZEN: read it to learn what the names meant, cite it, change nothing in it. dev/LESSONS.md C-41 is the law that makes the alias mandatory. Return an ARCHIVE USED section naming ONE line read per archived file.

## LITERATURE (DD18)

No mathematical literature bears on a naming change. Say so in one line and return a LITERATURE USED section.

## SCOPE (read)

scripts/dispatch_policy.py FIRST, whole.

## SCOPE (write)

The eight paths listed under CONSTRAINTS, minus the two frozen ones.

## RETURN

Lead with the six acceptance tests, each with its actual output line. Then every file you changed with a hit count before and after. Then every hit you deliberately LEFT and why, especially in dev/JOURNAL.md. Then what dispatch.py printed for the frozen brief. Then confirmation that no model ID string changed, with the grep that proves it. Mark every negative MEASURED or INFERRED.

End your final message with: whether all six tests pass, and whether any model ID string was touched.
