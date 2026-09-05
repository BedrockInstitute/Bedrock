# LJ-1.284: LAND A6 and A5 row 3, the last two A-prime blocks

tier: opus (in-harness-subagent-mode). I ran scripts/dispatch_policy.py before dispatching: in-harness-subagent-mode is IN FORCE, clock-selected, PEAK, Beijing window 14:00 to 18:00.

## GOAL

Land Route A-prime's last two blocks: A6 into a new master src/L/Absorption.lagda.md, and A5 row 3 into the delivered src/L/InjChain.lagda.md.

[LJ-1.268] put them in wave 3 at agents/tasks/LJ-1-268/lj-1.268-report.md:36-38, blocked behind a re-site. Everything else in A-prime landed today: A2 as src/L/Coding/Injection.lagda.md, A1+A3+A4 as src/L/Cardinal.lagda.md, A5 rows 5 and 1 as src/L/InjChain.lagda.md, A7 as src/L/GCH.lagda.md.

## THE BLOCKER IS MINE AND THE CURE IS NOW AVAILABLE

Both probes open a file that no longer exists:

  agents/tasks/LJ-1-176/ProbeLJ1176A.agda:73   open import ProbeLJ1134A {ℓ} lem
  agents/tasks/LJ-1-217/ProbeLJ1217A.agda:239  open import ProbeLJ1134A {ℓ} lem

I moved ProbeLJ1134A.agda out of src/ while another task was running. The move itself was right, the file was untracked and git-ignored. I checked the tree and not the importers, and [LJ-1.268] measured that this blocked 511 of A-prime's 1,089 lines.

THE CURE: A2 is now a DELIVERED MASTER. Re-site both probes onto src/L/Coding/Injection.lagda.md instead of the vanished probe. Verify that the master supplies what ProbeLJ1134A supplied; if it does not, name the gap at file:line and STOP rather than reconstructing a deleted probe.

## PREMISES

- A6 is priced at 399 lines and A5 row 3 is part of A5's 348, both at agents/tasks/LJ-1-253/lj-1.253-report.md:12-21, in the NARROW definitions-only caliber. Today's landings ran 1.28x to 1.5x that caliber. Report what lands and do not trim to a number.
- A6's home is src/L/Absorption.lagda.md, new, and row 3's home is the delivered src/L/InjChain.lagda.md, per agents/tasks/LJ-1-268/lj-1.268-report.md:36-38.
- [LJ-1.279] left row 3 a place in InjChain and its report says where. Read agents/tasks/LJ-1-279/lj-1.279-report.md and use it.
- [LJ-1.279] measured that PairBound is kept whole at 38 lines because the shared StageBound is NOT delivered, and that StageBound lands with row 3. So row 3 may let you DELETE that duplication. Check it, and if it does, report the lines removed as well as added.
- A7's hypotheses sq : SqShape and absorbs : AbsorbsShape are unsupplied Pi-parameters at src/L/GCH.lagda.md:66-76. [LJ-1.236] measured that A6's `absorbs` has a conclusion type that is A7's hypothesis ON THE NOSE. So landing A6 may let A7 name a delivered theorem instead of a parameter. DO NOT EDIT src/L/GCH.lagda.md. Say whether it now could be discharged and I decide.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- BOTH LAND GREEN. Report both masters, both timings, the Everything lines, and whether the PairBound duplication went away. STOP.
- THE RE-SITE FAILS. Name what ProbeLJ1134A supplied that src/L/Coding/Injection.lagda.md does not, at file:line, and STOP. Do not reconstruct the deleted probe: that would be rebuilding a thing whose replacement is already delivered, and I need to hear the gap instead.
- A6 IS MUCH LARGER THAN 399. Land what is real and report the figure.
- A6 CAN DISCHARGE ONE OF A7'S HYPOTHESES. That is the most valuable outcome here. Say so with the type at file:line and stop before touching GCH.
- A WALL. A single agda invocation past 30 MINUTES is a wall: interrupt, report elapsed seconds, bisect.

## CONSTRAINTS

- ONE agda process at a time, always GHCRTS="-A64m -I0 -M8g". The cap is C-12's and is NEVER raised. Report a heap exhaustion as a wall. Report the machine load beside every absolute figure, discard a warm-up, take at least three kept cold runs per master with the .agdai deleted between them.
- Your write territory is src/L/Absorption.lagda.md (new), src/L/InjChain.lagda.md (existing, row 3 only), and agents/tasks/LJ-1-284/. You may also fix the stale import inside agents/tasks/LJ-1-176/ and agents/tasks/LJ-1-217/, since re-siting those probes is the task.
- NEVER src/Everything.lagda.md. I wire it. Name the exact line and position for src/L/Absorption.lagda.md, derived from its own imports and consumers.
- NEVER src/L/GCH.lagda.md, never dev/ledger.toml, never dev/PLAN.md, never src/L/Choice/Name.lagda.md (DD23 blocks a pending change).
- Do not edit src/L/Cardinal.lagda.md: [LJ-1.282] sealed it an hour ago and it is green at 9.31 s.
- A SIBLING IS LIVE in agents/tasks/LJ-1-283/, surveying over-bar masters for the seal shape. Do not touch it.
- C-40: verify the CONSUMERS. src/L/InjChain.lagda.md is a DELIVERED master and you are editing it, so re-run everything that imports it and report each time.
- C-45: exit 0 is not a supply. Prove each landing by re-running something that IMPORTS the master, as [LJ-1.277], [LJ-1.279] and [LJ-1.282] all did.
- Create agents/tasks/LJ-1-284/lj-1.284-report.md in your first five minutes and fill it incrementally (C-22).
- Never commit, never push, never git checkout ., git stash, git reset --hard, git clean. Do not run make check.
- Run .venv/bin/python scripts/lint-prose.py --check and scripts/lint-agda.py --check on what you write. lint-agda binds a MASTER and did not bind the probes: expect to trim using lists. NO EM DASH in any language. DD23 freezes mathematical prose: code and its own comments only.
- Count with .venv/bin/python scripts/ledger.py, the only admissible source for a size figure.
- Evidence is file:line. Write ASD-STE100. Mark every negative MEASURED or INFERRED, in those words.
- Run .venv/bin/python scripts/rules.py --for build and read every statement; open the full entry for any law you act on. P-h, P-k, P-l, P-m, P-n, P-q, P-t, P-y, R-35, R-36, R-38, R-40, I-5, C-12, C-22, C-32, C-36, C-40, C-44, C-45, C-46, C-49, D-1, D-10, D-26, DD8, DD23, DD24 all bear.

## DD4

Maximize the code the two proofs share, and write it generic. One rule, two ends, no metric and no checker.

[LJ-1.248] measured A-prime's per-tower half at 146 to 196 lines, a BAND because the partition is a survey and it EXCLUDES A5. You are landing the last of A5, so say what row 3's tower status is and close that gap if you can.

NAME YOUR AXIS (C-46). DD4's own axis is AC-against-GCH, fixed in code at scripts/ledger.py:50. That report ran for the FIRST TIME today at 41.1 percent shared, 7,596 of 18,480 lines, and src/L/GCH.lagda.md is the declared gch_root. Your two masters land INSIDE the GCH closure, so say what each does to that figure and whether any of it lands in the shared intersection.

## ARCHIVE (DD18)

agents/tasks/LJ-1-217/ProbeLJ1217A.agda read WHOLE, the A6 content; agents/tasks/LJ-1-176/ProbeLJ1176A.agda for row 3; agents/tasks/LJ-1-268/lj-1.268-report.md:36-38 for the wave-3 order and the re-site; agents/tasks/LJ-1-279/lj-1.279-report.md for where row 3 goes and the PairBound duplication; agents/tasks/LJ-1-282/lj-1.282-report.md for today's landing method; archive/dev/TASKS-archived.md and archive/src/2026-08-09-rud-route/, taking SHAPE and never a claim, saying what would NOT transfer. Return an ARCHIVE USED section naming ONE line read per archived file.

## LITERATURE (DD18)

dev/literature/devlin-II5.md splits II.5 into twelve rows. Say which rows A6 and A5 row 3 serve. Return a LITERATURE USED section.

## SCOPE (read)

agents/tasks/LJ-1-217/ProbeLJ1217A.agda FIRST, whole.

## SCOPE (write)

src/L/Absorption.lagda.md (new), src/L/InjChain.lagda.md (row 3 only), agents/tasks/LJ-1-284/, and the two stale imports in agents/tasks/LJ-1-176/ and agents/tasks/LJ-1-217/.

## RETURN

Lead with both delivered line counts, both cold elapsed seconds, and both rates against the 0.010514 bar. Then whether the re-site onto A2 worked, at file:line. Then each premise VERIFIED or REFUTED. Then whether A6 discharges one of A7's hypotheses. Then whether the PairBound duplication went away and how many lines that removed. Then the exact src/Everything.lagda.md line for Absorption. Then the re-runs that PROVE both landings, including every consumer of InjChain. Then the DD4 answer with its axis. Mark every negative MEASURED or INFERRED.

End your final message with: both line counts, both times, whether the re-site worked, and whether A6 discharges an A7 hypothesis.
