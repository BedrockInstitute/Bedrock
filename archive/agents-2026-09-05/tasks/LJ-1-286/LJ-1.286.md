# LJ-1.286: take A6's discharge of A7's `absorbs`

tier: opus (in-harness-subagent-mode), model `opus`. I ran scripts/dispatch_policy.py before dispatching: in-harness-subagent-mode is IN FORCE, clock-selected, PEAK, Beijing window 14:00 to 18:00.

## GOAL

Discharge one of the two unsupplied hypotheses in the GCH trophy statement.

src/L/GCH.lagda.md:69 currently reads `→ (absorbs : AbsorbsShape)`. [LJ-1.284] measured that src/L/Absorption.lagda.md supplies it exactly, and proved it with a green typecheck rather than a reading of two types: agents/tasks/LJ-1-284/ReRun.agda:92-93 writes

    absorbsShape : AbsorbsShape
    absorbsShape = absorbs

with AbsorbsShape imported from src/L/GCH.lagda.md:49-53 and absorbs from src/L/Absorption.lagda.md:613-618. No subst. No wrapper.

Take it: add the import of L.Absorption to src/L/GCH.lagda.md and delete the `(absorbs : AbsorbsShape) →` parameter at :69, threading the now-available term through every use.

## THE ORCHESTRATOR'S RULING, so you do not re-open it

TAKING THIS DISCHARGE LOWERS DD4's PUBLISHED FIGURE FROM 41.1 PERCENT TO 39.1 PERCENT. [LJ-1.284] measured that: it pulls 1,063 lines into the GCH closure and only 36 of them land in the shared intersection.

I have ruled that we take it anyway, and the reason is DD4's own row. DD4 has NO HARD METRIC by the owner's 2026-08-09 ruling, because a shared-line count would be gamed the moment it gated anything. The reuse report is evidence for a human and never a gate. A statement with one fewer unsupplied hypothesis is strictly stronger mathematics, and a number that argues against that is exactly the number DD4 refused to create.

DO NOT re-litigate this. DO report the figure the report actually prints after your change, so the record carries the real number and not my projection.

## PREMISES

- `absorbs` supplies `AbsorbsShape` on the nose, proved at agents/tasks/LJ-1-284/ReRun.agda:92-93. RE-DERIVE IT yourself before editing: write the same one-liner in your own probe and typecheck it.
- The parameter to delete is at src/L/GCH.lagda.md:69. VERIFY the line number; the file may have moved.
- `sq : SqShape` is NOT dischargeable. [LJ-1.284] measured that src/L/InjChain.lagda.md supplies only the base `squareω : sq ω` and not the uniform law. DO NOT attempt it. If you find you CAN discharge it, that is a large finding: stop, report the term at file:line, and do not land it in the same change.
- src/L/GCH.lagda.md is the declared `reuse.gch_root` in dev/ledger.toml. Changing its imports changes DD4's first published figure. That is expected and ruled above.
- src/L/Absorption.lagda.md landed minutes ago at 525 lines, 5.75 s, 1.04x the bar, and is wired into src/Everything.lagda.md after L.Cardinal and before L.GCH. The catalog order already anticipates this import.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- IT LANDS GREEN. Report the new GCH timing, the remaining hypotheses, and the reuse report's actual new numbers. STOP.
- THE DISCHARGE NEEDS A subst OR A WRAPPER. Then it is not on the nose and [LJ-1.284]'s claim is weaker than it read. Report the term you had to write and let me judge whether to take it.
- A CONSUMER OF GCH BREAKS. C-40. Name it at file:line. Nothing in src/ imports L.GCH today by my grep, but check rather than trust me (C-44).
- sq TURNS OUT DISCHARGEABLE. Stop and report. Do not bundle two discharges in one change.
- A WALL. A single agda invocation past 30 MINUTES is a wall: interrupt, report elapsed seconds, bisect.

## CONSTRAINTS

- ONE agda process at a time, always GHCRTS="-A64m -I0 -M8g". The cap is C-12's and is NEVER raised. Report the machine load beside every absolute figure, take at least three kept cold runs with the .agdai deleted between them.
- Your write territory is src/L/GCH.lagda.md and agents/tasks/LJ-1-286/. NOTHING ELSE under src/. Never src/Everything.lagda.md: I wire it, and this change needs no new catalog line because L.Absorption is already there.
- Never dev/ledger.toml. I declare it. Tell me if the declaration comment needs updating; do not edit it.
- Never dev/PLAN.md. Never src/L/Choice/Name.lagda.md (DD23 blocks a pending change).
- A SIBLING IS LIVE in agents/tasks/LJ-1-283/, surveying over-bar masters for the seal shape. Do not touch it.
- C-45: exit 0 is not a supply. Prove the landing by re-running something that IMPORTS L.GCH, and by showing the statement type no longer carries the parameter.
- RUN `.venv/bin/python scripts/ledger.py --reuse` AFTER the change and paste the output verbatim. That is DD4's own report and it ran for the first time in this project's history today.
- Create agents/tasks/LJ-1-286/lj-1.286-report.md in your first five minutes and fill it incrementally (C-22).
- Never commit, never push, never git checkout ., git stash, git reset --hard, git clean. Do not run make check.
- Run .venv/bin/python scripts/lint-prose.py --check and scripts/lint-agda.py --check on what you write. NO EM DASH in any language. DD23 freezes mathematical prose: code and its own comments only.
- Count with .venv/bin/python scripts/ledger.py, the only admissible source for a size figure.
- Evidence is file:line. Write ASD-STE100. Mark every negative MEASURED or INFERRED, in those words.
- Run .venv/bin/python scripts/rules.py --for build and read every statement; open the full entry for any law you act on. C-38 as extended, C-40, C-44, C-45, P-k, P-m, DD4, DD8, DD24 all bear.

## DD4

Maximize the code the two proofs share, and write it generic. One rule, two ends, no metric and no checker.

THIS TASK IS THE FIRST TIME THE PROJECT HAS WATCHED DD4'S FIGURE POINT THE WRONG WAY, and that is worth one careful paragraph in your report rather than a shrug. Answer: does the change lower REUSE, or only lower the RATIO? Those are different. The AC side loses nothing; the GCH side gains 1,027 lines it always needed. Say which of the two the figure is actually measuring here, and whether a reader six months from now could tell them apart from the number alone.

NAME YOUR AXIS (C-46). DD4's own axis is AC-against-GCH, fixed in code at scripts/ledger.py:50.

## ARCHIVE (DD18)

agents/tasks/LJ-1-284/lj-1.284-report.md read WHOLE, the discharge and its DD4 arithmetic; agents/tasks/LJ-1-284/ReRun.agda:92-93, the proof; agents/tasks/LJ-1-280/lj-1.280-report.md, how GCH was landed and what its hypotheses are; agents/tasks/LJ-1-274/lj-1.274-report.md, what the reuse report actually reads; archive/dev/TASKS-archived.md, taking SHAPE and never a claim. Return an ARCHIVE USED section naming ONE line read per archived file.

## LITERATURE (DD18)

dev/literature/devlin-II5.md splits II.5 into twelve rows. Say which row `absorbs` is, and whether Devlin treats it as a hypothesis or a theorem. Return a LITERATURE USED section.

## SCOPE (read)

agents/tasks/LJ-1-284/lj-1.284-report.md FIRST, whole.

## SCOPE (write)

src/L/GCH.lagda.md and agents/tasks/LJ-1-286/ only.

## RETURN

Lead with the remaining unsupplied hypotheses of the trophy statement, at file:line. Then the verbatim output of `scripts/ledger.py --reuse` after your change. Then GCH's new cold timing and line count. Then each premise VERIFIED or REFUTED. Then the re-run that proves the landing. Then the DD4 paragraph: reuse versus ratio. Mark every negative MEASURED or INFERRED.

End your final message with: which hypotheses remain, and the reuse report's actual new share.
