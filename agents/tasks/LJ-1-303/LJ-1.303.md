# LJ-1.303: slim the dispatch scripts, function unchanged

tier: opus (pi-subagent-mode), **the OWNER named this model**, 2026-08-15. Under the mode in force the default head is pi and in-harness is the adversarial row; the owner's word overrides the table and this line records that it was theirs and not my inference.

## GOAL

**The owner's instruction: slim the dispatch-related scripts. Function unchanged, redundant code removed.**

I measured the four files before writing this:

    .claude/skills/codex-dispatch/dispatch.py    2,515 lines  1,634 code   653 comment  49 defs
    scripts/dispatch/dispatch_policy.py          1,095 lines    754 code   200 comment  30 defs
    scripts/dispatch/check-dispatch-policy.py      334 lines    225 code    62 comment  10 defs
    scripts/tests/test_dispatch_clock.py           439 lines    297 code    92 comment   7 defs

## THE TRAP, AND IT IS THE WHOLE DIFFICULTY

**THE COMMENTS ARE NOT REDUNDANCY. MOST OF THEM RECORD MEASUREMENTS.**

This repository's rules are enforced in three ways: a checker, a brief section, or a comment that says what was measured and when. `AGENTS.md` states that a rule with no enforcement point is a wish. In these files, a comment is frequently the ONLY enforcement a rule has.

Concrete examples you must not touch:

- Every refusal in `dispatch.py` carries the failure that produced it, with a date. "MEASURED 2026-08-13: a resume on the wrong harness hands a pi session id to codex." Delete that and the next reader removes the refusal as pointless.
- `dispatch_policy.py`'s `ALIASES` block records that 189 frozen briefs carry a retired mode name, which is why the alias can never be dropped (C-41).
- `dispatch.py`'s `clock_defects` records the two dispatches that ran the wrong head this morning, which is why the refusal exists at all.
- The vendor-seam comment records that a vendor swap is now one edit to `dev/vendors.toml` and no longer one edit to a literal.

**SO: SLIM THE CODE. KEEP THE MEASUREMENTS.** If you believe a comment is genuinely redundant, say so in the report with its line and let me judge; do not delete it silently.

**A comment that merely restates the code IS fair game.** So is a docstring that repeats its function's name in a sentence. Judge by whether a reader loses a MEASUREMENT or a DATE.

## WHERE THE REAL SLACK PROBABLY IS

I measured one thing already and it is small: of `dispatch.py`'s 49 functions, exactly ONE has no reference beyond its own definition, `already_announced`. **So there is no forest of dead functions. The slack is elsewhere and you must find it.**

Look for:
- **Duplicated logic across the four files.** `check-dispatch-policy.py` and `dispatch.py` both reason about tier lines and modes; `test_dispatch_clock.py` may re-derive what the policy exports.
- **Repeated inline patterns** that want one helper: subprocess calls, path resolution, JSON reads, the registry read-modify-write.
- **Refusal messages built by hand** where a shared formatter would do, WITHOUT losing any of their measured content.
- **Branches that cannot be reached** now that the vendor config exists. `[LJ-1.288]` moved vendor data out of the policy; some old handling may be stranded.
- **`dispatch.py` grew a lot today**: a clock guard, the vendor adoption, a launch-path refusal, a path fix, a case-flag pair. Some of it was added in haste by me and may duplicate what was there.

## THE ACCEPTANCE BAR: FUNCTION UNCHANGED, PROVED AND NOT ASSERTED

**Capture the behaviour BEFORE you touch anything**, then diff after:

1. `.venv/bin/python scripts/dispatch/dispatch_policy.py` full output, byte-identical apart from the live clock reading.
2. `.venv/bin/python scripts/dispatch/dispatch_policy.py deepseek-subagent-mode` still renders through the alias.
3. `.venv/bin/python scripts/tests/test_dispatch_clock.py` passes all 67 checks. If you touch the test file, say what and why.
4. `.venv/bin/python scripts/dispatch/check-dispatch-policy.py` exits 0 over every brief; capture the count.
5. `.venv/bin/python .claude/skills/codex-dispatch/dispatch.py status` prints the same census.
6. `.venv/bin/python .claude/skills/codex-dispatch/dispatch.py check <brief>` on THREE briefs: one that passes, one that fails the clock guard, one that fails the rule bundle. Same messages before and after.
7. The vendor refusals still fire: a declared-but-unwired vendor still lets `status` work and still refuses a launch loudly. Test it with a temporary row and REMOVE the row afterwards.

**Report the line counts before and after, per file, and the percentage.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT SLIMS AND ALL SEVEN CHECKS MATCH.** Report the diff of behaviour, the counts, and every comment you removed. STOP.
- **THE SLACK IS SMALL.** **Say the number plainly.** If these files are already tight, that is a real answer and better than a cosmetic rewrite. **Do not manufacture a saving by deleting measurements.**
- **A BEHAVIOUR CHANGES.** Stop and report which. Function unchanged is the bar, not a preference.
- **A SIMPLIFICATION WOULD BE BETTER BUT CHANGES AN INTERFACE.** Say what and let me judge. `.claude/skills/codex-dispatch/dispatch.py` has consumers you cannot see.

## CONSTRAINTS

- **`.claude/skills/codex-dispatch/dispatch.py` IS OUTSIDE YOUR WRITE SCOPE.** It is untracked and mine. **Write its changes as a DIFF in your report; I apply them.** You may READ it and RUN it freely.
- Your write territory: `scripts/dispatch/`, `scripts/tests/test_dispatch_clock.py`, and `agents/tasks/LJ-1-303/`. **NOT `AGENTS.md`, NOT `dev/PLAN.md`, NOT `dev/vendors.toml`, NOT `src/`, NOT another task directory.**
- **DO NOT RUN AGDA.** Two siblings hold both slots and are working on the phase terminus.
- **Do not run `make check`**; I run it. Run the individual checkers.
- Never commit, never push, never `git checkout .`, `git stash`, `git reset --hard`, `git clean`.
- **Create `agents/tasks/LJ-1-303/lj-1.303-report.md` in your FIRST five minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` on your report. **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative MEASURED or INFERRED, in those words.
- Run `.venv/bin/python scripts/dispatch/rules.py --for rewrite` and read every statement.

## THE RULES THIS CHAIN EARNED

**DD13. Price a retirement from the REWRITE side.** Applied here: for each block you would cut, ask what it would look like written fresh today, then compare. "It has been there a while" decides nothing.

**C-43. An escape hatch is the shape a wrong choice hides in.** A slimming that removes a refusal, or the measurement that justifies it, is that shape.

**C-48. A policy that only a document states is not enforced.** These files ARE the enforcement for several rules. Removing a comment can remove a rule.

**C-44.** Every figure in this brief is mine from today and you must re-derive it.

## DD4

Maximize the code the two proofs share, and write it generic. One rule, two ends, no metric and no checker. This task writes no mathematics. It binds the shape: say in one line whether the slimmed files would survive a third dispatch mode and a third vendor, which is the same generality question DD4 asks of the proofs.

## ARCHIVE (DD18)

`agents/tasks/LJ-1-288/lj-1.288-report.md`, the vendor config that moved data out of the policy and may have stranded handling. `agents/tasks/LJ-1-285/lj-1.285-report.md`, the rename and the alias mechanism. `archive/dev/TASKS-archived.md`, taking SHAPE and never a claim. Return an ARCHIVE USED section naming ONE line read per archived file.

## LITERATURE (DD18)

No mathematical literature bears on code size. Say so in one line and return a LITERATURE USED section.

## SCOPE (read)

`.claude/skills/codex-dispatch/dispatch.py` FIRST, whole. It is the largest and the one you cannot edit.

## SCOPE (write)

As listed under CONSTRAINTS.

## RETURN

Lead with the line counts before and after, per file, with the percentage. Then the seven behaviour checks, each with its actual output. Then every comment you removed, with its line and why it carried no measurement. Then the diff for `dispatch.py`. Then anything you would change but did not because it touches an interface. Mark every negative MEASURED or INFERRED.

End your final message with: the total lines removed, the percentage, and whether any behaviour changed.
