# LJ-1.288: a vendor config for pi-subagent-mode's model, and a clock that belongs to the vendor

tier: opus (in-harness-subagent-mode), model `opus`. I ran scripts/dispatch_policy.py before dispatching: in-harness-subagent-mode is IN FORCE, clock-selected, PEAK, Beijing window 14:00 to 18:00.

## GOAL, and it is the owner's instruction in two parts

**PART 1.** Give `dispatch.py` a CONFIG FILE so the model that `pi-subagent-mode` runs on can be switched between vendors: deepseek, glm, grok, and anything else `pi` has been wired to.

**The owner's own caveat, and you must honour it: `pi` is NOT wired to anything except deepseek today. This is opening compatibility ahead of need, not claiming support that exists.** A vendor that pi cannot actually run must be DECLARABLE and must fail LOUDLY at dispatch, never silently.

**PART 2, and this is the sharp half.** The peak and off-peak clock exists because DEEPSEEK prices that way. `scripts/dispatch_policy.py:120-121` says so in its own comment: "the two states and the two modes are the whole economics: off-peak deepseek is half price, peak it is dear."

**So the clock must fire ONLY when the configured vendor IS deepseek.** With any other vendor the clock has no basis and must not drive the mode.

## THE DESIGN QUESTION YOU MUST ANSWER, not dodge

**When the vendor is not deepseek, what selects the mode?** `VERSION_IN_FORCE = 'auto'` currently means "ask the clock". With no clock there is no answer, and a silent fallback would be the worst outcome.

My reading, and you may overturn it with a reason: the peak windows are DATA ABOUT A VENDOR, not a global fact. So the config should let each vendor declare its own windows, and:

- a vendor WITH declared windows drives the clock exactly as today,
- a vendor with NO declared windows makes `auto` resolve to a configured `default_mode`,
- and an explicit pin in `VERSION_IN_FORCE` still beats both, which is today's rule and must not change.

That generalization makes deepseek's 09:00-12:00 and 14:00-18:00 into deepseek's own rows rather than a hardcoded global, and it answers PART 2 by construction. **If you find a better shape, say why and take it.**

## THE DD19 TRAP, and I want it handled rather than tripped

`AGENTS.md:98` names `scripts/dispatch_policy.py` **the ONLY home of the tables**, and DD19 forbids a rule being canonical twice. A config file that holds the HEAD TABLES would break that.

**So draw the line explicitly and state it in both files:** the config holds VENDOR DATA, which is which vendor is in force, its model IDs, and its price windows. `scripts/dispatch_policy.py` keeps the HEAD TABLES, the two modes, the invariant and the mode logic. **Nothing that is canonical in one may be restated in the other.**

**DO NOT EDIT AGENTS.md.** An edit there needs an owner ruling and a dated trailer (DD19). If you conclude that row must change, say so in your report and stop short of it.

## PREMISES

- `scripts/dispatch_policy.py:120-124` hardcodes `CLOCK_STATES` and its comment ties the clock to deepseek's pricing. VERIFY.
- `MODEL = "deepseek-v4-pro"` at :215 is the file's declared single vendor seam, and its comment says a vendor swap is one edit to that literal. That comment becomes wrong once a config exists; update it.
- `FLASH` and `model_for()` were DELETED on 2026-08-15 by the owner's ruling: there is no automatic model rule and you must not reintroduce one. The file's revocation comment explains why. Read it before you touch anything nearby.
- The public API that `.claude/skills/codex-dispatch/dispatch.py` depends on is `canonical`, `in_force`, `table`, `head`, `tier_token`, `default_harness`, `expected_tier_tokens`, `render`, `clock_mode`, `clock_state`, `next_boundary`, `current_window`. That file is UNTRACKED and OUTSIDE your write scope. **Do not break its callers.** VERIFY the list yourself with a grep; my list is a claim (C-44).
- `dev/` already holds four TOML configs: ledger, rules, glossary, build-manifest. Follow that convention unless you have a reason.

## BACKWARD COMPATIBILITY IS THE ACCEPTANCE BAR

**With no config file present, or with the config naming deepseek, every observable behaviour must be IDENTICAL to today.** That is not a preference; it is how you prove you changed the shape and not the policy.

Prove it:
1. `.venv/bin/python scripts/dispatch_policy.py` prints the same mode, clock line, windows and tables as it does now. Capture the CURRENT output BEFORE you edit, and diff.
2. `.venv/bin/python scripts/tests/test_dispatch_clock.py` passes all 35 checks. Extend it with new checks for the vendor switch, and say how many it has after.
3. `.venv/bin/python scripts/check-dispatch-policy.py` exits 0 over all 585 briefs.
4. `.venv/bin/python .claude/skills/codex-dispatch/dispatch.py check agents/tasks/LJ-1-279/LJ-1.279.md --agda` behaves as it does now. Capture before and after.
5. Deleting the config file, or leaving it absent, must not crash anything. Test it.
6. A config naming a vendor pi cannot run must produce a LOUD, specific refusal naming the vendor. Test it and paste the message.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT LANDS AND ALL SIX PASS.** Report each with its output. STOP.
- **THE DD19 LINE CANNOT BE DRAWN CLEANLY.** If vendor data and head tables cannot be separated without one restating the other, say so and stop. That is a real finding and the owner should rule before code lands.
- **A CALLER OUTSIDE YOUR SCOPE BREAKS.** Name it at file:line and stop. `dispatch.py` is untracked and I fix it.
- **THE CLOCK CANNOT BE MADE VENDOR-CONDITIONAL WITHOUT CHANGING TODAY'S BEHAVIOUR.** Say exactly what would change and stop.

## CONSTRAINTS

- Write scope: `scripts/dispatch_policy.py`, `scripts/tests/test_dispatch_clock.py`, the NEW config file you create under `dev/`, `dev/build-manifest.toml` ONLY IF your file needs a lifecycle declaration there, and `agents/tasks/LJ-1-288/`.
- **DO NOT EDIT** `AGENTS.md`, `CLAUDE.md`, `dev/PLAN.md`, `dev/ORCHESTRATION.md`, `dev/ledger.toml`, anything under `src/`, anything under `.claude/`, or any other task directory.
- **A SIBLING IS LIVE in agents/tasks/LJ-1-287/**, curing an Agda term. Do not touch it. **DO NOT RUN AGDA**: it holds the Agda work and needs a quiet machine.
- Never commit, never push, never git checkout ., git stash, git reset --hard, git clean. Do not run make check.
- Run `.venv/bin/python scripts/lint-prose.py --check` on any prose you write. NO EM DASH in any language.
- Create `agents/tasks/LJ-1-288/lj-1.288-report.md` in your first five minutes and fill it incrementally (C-22).
- Evidence is file:line. Write ASD-STE100. Mark every negative MEASURED or INFERRED, in those words.
- The config file must carry a header comment saying what it is FOR, what it does NOT hold, and where the head tables live. A reader must not have to guess the DD19 line.

## THE RULES THAT BIND THIS TASK

**C-41.** A retired name must keep resolving. `deepseek-subagent-mode` resolves to `pi-subagent-mode` through ALIASES and 189 frozen briefs depend on it. Do not disturb that.

**C-43. An escape hatch is the shape a wrong choice hides in.** A config that silently defaults when a vendor is unknown is that shape. Fail loudly.

**C-44.** Every claim in this brief is unchecked until you check it.

**C-48, written today.** A policy that only a document states is not enforced, and a tool that can read a condition must refuse on it. Your config is a condition a tool can read.

**C-50, written today.** Profile before you cure. Not directly applicable, but its discipline is: measure the current behaviour before you change it, which is acceptance test 1.

## DD4

Maximize the code the two proofs share, and write it generic. One rule, two ends, no metric and no checker. This task writes no mathematics, so DD4 does not bind its content. It binds its SHAPE, and the connection is exact: the owner is asking for the same thing DD4 asks for, which is that a structure not be welded to one instance. Say in one line whether your config would survive a third mode, and whether it would survive a vendor with three price bands rather than two.

## ARCHIVE (DD18)

`agents/tasks/LJ-1-285/lj-1.285-report.md`, the rename that took the vendor name off the mode identifiers and the alias mechanism it used; `archive/dev/JOURNAL-archived.md`, the mode's earlier history, FROZEN, read and cite only. Return an ARCHIVE USED section naming ONE line read per archived file.

## LITERATURE (DD18)

No mathematical literature bears on a configuration format. Say so in one line and return a LITERATURE USED section.

## SCOPE (read)

`scripts/dispatch_policy.py` FIRST, whole.

## SCOPE (write)

As listed under CONSTRAINTS.

## RETURN

Lead with the six acceptance tests, each with its actual output. Then the config file's path and its full contents. Then the DD19 line you drew, in one sentence, and where you stated it. Then what happens with each of: no config, config naming deepseek, config naming glm, config naming an unknown vendor. Then the diff of `dispatch_policy.py`'s printed output before and after. Then the DD4 shape answer. Mark every negative MEASURED or INFERRED.

End your final message with: whether all six pass, the config path, and what the clock does when the vendor is not deepseek.
