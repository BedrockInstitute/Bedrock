# LJ-1.282: land the seal on A1, worth 91 seconds

tier: opus (in-harness-subagent-mode). I ran scripts/dispatch_policy.py before dispatching: in-harness-subagent-mode is IN FORCE, clock-selected, PEAK, Beijing window 14:00 to 18:00.

## GOAL

Land the opacity cure that [LJ-1.281] measured this afternoon. `src/L/Cardinal.lagda.md` costs 100.57 s cold and A1 alone carries 98.24 of it. The cure takes the file to 9.16 s.

## PREMISES

- A1 alone is 100.50 s cold, measured by [LJ-1.281] over four kept runs at agents/tasks/LJ-1-281/lj-1.281-report.md:9-11, reproducing [LJ-1.278]'s 98.24 s and [LJ-1.232]'s 100.3 s. RE-DERIVE the control on the landed master before you change anything.
- The term is `κ-min-at` at src/L/Cardinal.lagda.md:125-138, carrying 85 of the 100 s. The root is the transparent well-order `w = ordSWO (sucV (fst α))` at src/L/Cardinal.lagda.md:86, which unfolds in `least = leastOf w` at :102 and RE-unfolds inside κ-min-at's conversion checks. Verify this yourself.
- Sealing `w` opaque plus one read lemma `w-lt` gives 9.16 s, measured at agents/tasks/LJ-1-281/lj-1.281-report.md:23-28, arm TreatedOpaque, three kept runs at load 4.9 to 5.3.
- P-y prices this seal LOW: only two internal definitions, `least` and `κ-min`, name `w` in their types, and NEITHER is what the GCH proof imports. The consumer-facing `κ-min-at` keeps a type that does not name `w`. Verify by grepping consumers.

## WHAT TO DO

Make `w` opaque inside `module LeastCardInjL` and add the read lemma `w-lt` beside it, taking the shape from agents/tasks/LJ-1-281/TreatedOpaque.agda, which is green. Keep `κ-min-at`'s exported type unchanged.

DO NOT take the R-35 arm. It costs 15.53 s against the seal's 9.16 and it changes what the consumer can call. The seal is the ruled choice.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- IT LANDS AND THE FILE DROPS. Report the control you measured, the treated time, and the delta. STOP.
- A CONSUMER NEEDS TO SEE INSIDE `w`. Name it at file:line and report how many `unfolding` blocks the tree needs. P-y says price the seal by the definitions that look INSIDE, not the ones that name it. If the count is more than two, say so and stop before landing.
- THE SEAL DOES NOT REPRODUCE ON THE MASTER. The probe arm is green in its own file; if the master refuses, name the term (C-36).
- A WALL. A single agda invocation past 30 MINUTES is a wall: interrupt, report elapsed seconds, bisect.

## CONSTRAINTS

- ONE agda process at a time, always GHCRTS="-A64m -I0 -M8g". The cap is C-12's and is NEVER raised. Report a heap exhaustion as a wall. Report the machine load beside every absolute figure, discard a warm-up, take at least three kept cold runs per arm with the .agdai deleted between them.
- Your write territory is src/L/Cardinal.lagda.md and agents/tasks/LJ-1-282/ ONLY. Never src/Everything.lagda.md, never dev/ledger.toml, never dev/PLAN.md, never src/L/Choice/Name.lagda.md (DD23 blocks a pending change).
- A SIBLING IS LIVE in agents/tasks/LJ-1-283/, surveying other masters for the same shape. Do not touch it.
- C-40: verify the CONSUMERS of a changed master, not the master alone. src/L/GCH.lagda.md imports L.Cardinal and landed an hour ago. Re-run it and report its time.
- Create agents/tasks/LJ-1-282/lj-1.282-report.md in your first five minutes and fill it incrementally (C-22).
- Never commit, never push, never git checkout ., git stash, git reset --hard, git clean. Do not run make check.
- Run .venv/bin/python scripts/lint-prose.py --check and .venv/bin/python scripts/lint-agda.py --check on what you write. NO EM DASH in any language. DD23 freezes mathematical prose: write code and its own comments only.
- Evidence is file:line. Write ASD-STE100. Mark every negative MEASURED or INFERRED, in those words.
- Run .venv/bin/python scripts/rules.py --for build and read every statement; open the full entry for any law you act on. P-y, P-i, P-l, P-m, P-t, R-35, R-36, R-40, C-12, C-22, C-32, C-36, C-40, C-44, C-45, C-49, I-5, D-1, DD8, DD24 all bear.

## DD4

Maximize the code the two proofs share, and write it generic. One rule, two ends, no metric and no checker. [LJ-1.227] measured A1 PER-TOWER on the Def-against-J axis, so its seconds are paid once today and would be paid twice if the J tower builds its own A1. Say whether the seal is generic enough that the J tower inherits it. NAME YOUR AXIS (C-46): DD4's own axis is AC-against-GCH, fixed at scripts/ledger.py:50, and L.Cardinal now sits inside the GCH closure that ran for the first time today.

## ARCHIVE (DD18)

agents/tasks/LJ-1-281/lj-1.281-report.md read WHOLE and agents/tasks/LJ-1-281/TreatedOpaque.agda read WHOLE; agents/tasks/LJ-1-278/lj-1.278-report.md sections 0 and 1; dev/LESSONS.md P-y read as a FULL entry, and R-36; archive/dev/TASKS-archived.md, taking SHAPE and never a claim. Return an ARCHIVE USED section naming ONE line read per archived file.

## LITERATURE (DD18)

Nothing in the literature governs elaboration cost. Say so in one line and return a LITERATURE USED section.

## SCOPE (read)

agents/tasks/LJ-1-281/lj-1.281-report.md FIRST, whole.

## SCOPE (write)

src/L/Cardinal.lagda.md and agents/tasks/LJ-1-282/ only.

## RETURN

Lead with the control you measured, the treated cold seconds, and the delta. Then each premise VERIFIED or REFUTED at file:line. Then how many definitions look INSIDE `w` and how many `unfolding` blocks the tree needs. Then L.GCH's re-run time (C-40). Then the new whole-file rate against the 0.010514 bar. Then the DD4 answer with its axis. Mark every negative MEASURED or INFERRED.
