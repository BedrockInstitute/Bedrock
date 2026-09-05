# LJ-1.746-SPLIT: BoundInStage at empty, split-spelled row types

## HEAD

head_slot: coder
machine: shared
task: LJ-1.746-SPLIT
agda_tier: wide
pane caliber: GHCRTS=`-A64m -I0 -M2g`, set by the program; never touched
here (recorded as line 1 of every `.out`)
verdict: **NO-GO stated.** The obligation does not land: the chain
walls at `Amb4`'s assembly, and the wall is independent of the rows'
spelling.  The brief's candidate 1 SPLITS: the spelling module it
named is GREEN (`runs/PT.agda`, rc 0 in 90.92 s), and the assembly
consuming it heap-exhausts at the 2 g cap (`runs/PT2.agda.txt`,
351.07 s, rc 251).  The NO-GO statement is
`review-of-bound-in-stage-at-empty.md` in this directory.  Nothing in
`src/`; nothing committed; no watchdog kill.

## THE DELIVERABLE

- `agents/tasks/LJ-1-746-SPLIT/Probe746Split.agda.txt` -- the drafted
  probe: the 673 At telescope as leading arguments, `StepKilledGen`
  taken as a TYPE from the green vendored `runs/Amb7.agda`, the
  conv-first bridge, the pins, the obligation, the top-level alias
  export.  Named `.agda.txt` because it cannot typecheck: its
  `LJ-1-746-SPLIT.runs.Amb2` import does not close.
- `agents/tasks/LJ-1-746-SPLIT/runs/PT.agda` -- **rc 0, 90.92 s**
  (`runs/pt6.out`): the spelling module, candidate 1's own moves.
  `pA`/`pS` (runs/PT.agda:42,52) name the split count proofs with
  every plus-zero implicit spelled and `countTm`'s alphabet pinned;
  `ApproxSlot`/`StepSlot` (runs/PT.agda:63,67) name the split-spelled
  row types at those proofs; `approx-split`/`step-split`
  (runs/PT.agda:72,78) carry the green 746 rows into them by
  `erase-cong`.
- `agents/tasks/LJ-1-746-SPLIT/runs/Amb7.agda` and
  `runs/EraseIrr.agda` -- verbatim vendor copies of 746's green
  modules under this task's module names (`LJ-1-746-SPLIT.runs.*`),
  because `agents/tasks/LJ-1-746/` is uncommitted in the tree at this
  worktree's HEAD (`f54e89cb`), so the brief's named import
  `LJ-1-746.runs.Amb7` has no file to resolve to anywhere a fresh
  checkout could reach.  Only the `module` line differs; the bodies
  are diff-verbatim.  Both re-measured green here: `runs/warm-amb7.out`
  (3.13 s), `runs/warm-eraseirr.out` (0.79 s).
- `agents/tasks/LJ-1-746-SPLIT/runs/` -- the probe record: M0, PA,
  PM, PT, PT2, the 732-Amb4 verbatim run, the floors, and every
  number cited below.
- `agents/tasks/LJ-1-746-SPLIT/review-of-bound-in-stage-at-empty.md`
  -- the NO-GO statement (DD25).

Not inhabited, as the brief demands: `Completeness`,
`completeness-from-pack`.  Nothing landed in `src/`.  `approx-part`
was not rebuilt: the transports consume 746's green
`approx-part : StepKilledGen → ApproxAt` unchanged.  No `PT.rec` sits
anywhere in this dispatch's files.

**W2 ANSWER:** the rule is honored by reuse, not by rewriting: the
generic vacuity mathematics stays in 746's green `approx-part :`
`StepKilledGen → ApproxAt` and is instantiated through the two
transports in `runs/PT.agda`; this dispatch wrote only spelling and
glue (`pA`/`pS`, the two named row types, the two transports), and no
duplicate of any generic lemma exists in the write scope.

## MEASUREMENTS

The worktree's `_build` held no task interfaces.  The cone was warmed
bottom-up, ONE Agda process at a time, each module its own process,
before any measurement: P520 2.52 s, P652 5.67 s, P667 15.21 s,
P673 115.88 s, Num 0.99 s, Amb1 5.39 s, Amb4a 3.68 s, Amb7a 3.63 s,
Amb5 3.81 s, Amb6 3.92 s, Amb3 3.74 s, Amb2a 3.55 s, all rc 0
(`runs/warm-*.out`).

| run | file | rc | what it prices |
|---|---|---|---|
| `runs/amb4-732-verbatim.out` | 732's committed `runs/Amb4.agda`, verbatim | **251, HEAP WALL** | **358.21 s**, `Heap exhausted` at 2 g, 2.28 GB: the committed 732 chain shape was never green at this caliber |
| `runs/m0.out` | `runs/M0.agda.txt` (746's b12, here) | **251, HEAP WALL** | **285.23 s**, 2.39 GB: rows as variables at the inline split spellings, assembly vs `GraphAt` |
| `runs/pa.out` | `runs/PA.agda.txt` | **251, HEAP WALL** | **276.71 s**, 2.51 GB: the SAME-spelling conversion in isolation |
| `runs/pm3.out` | `runs/PM.agda.txt` | no completion in 300 s | candidate 2's mirror bridge `GraphMirror ≡ GraphAt` by `refl` (pm/pm2 died fast on scope errors only) |
| `runs/pt.out` | `runs/PT.agda`, first spelling | 42 | **89.42 s**, blocked on `_a`: the unifier cannot decompose `countFo graphBndAt` against a meta-headed plus |
| `runs/pt4.out` | implicits spelled in `pA`/`pS` only | 42 | **92.80 s**, still blocked: the inline chains in the signatures carry the same metas |
| `runs/pt5.out` | signatures at `pA`/`pS` | 42 | **91.11 s**, unsolved metas at `countTm (var kk)`: the alphabet implicit has no inference path |
| `runs/pt6.out` | `runs/PT.agda`, final | **0** | **90.92 s**, 1.14 GB: `countTm {K = CS.S}` + all implicits spelled + signatures at the named proofs |
| `runs/pt2-run3.out` | `runs/PT2.agda.txt` | **251, HEAP WALL** | **351.07 s**, 2.20 GB: the assembly consuming the green spelling module |
| `runs/floor746split.out`, `runs/floor746split-2.out` | the full frame floor | no completion in 300 s / 700 s | the 746 draft's `AT.read` bridge grinds on its own |
| `runs/floorB1.out` | frame minus the bridge | 42 (designed) | **31.95 s**: the frame WITHOUT the bridge is cheap; the only metas are the hole and its echo through the alias |
| `runs/floorB2b.out` | bridge rewritten cong-conv-first | no completion in 300 s | the conv-first rewrite does not cure the bridge |

**W3 ANSWER: NO.**  One shared split-spelling of the row types does
not make `Amb4` convert at wide.  The spelling module lands; the
assembly does not.  The fatal step is the elaborator's comparison
between the rows and the slots it derives by evaluating the reading
of `CntS.erase Mx.G.graphBndAt countGB`: it normalizes `countFo` over
the unfolded `ApproxB`/`StepB` trees and exceeds the cap in EVERY
shape measured -- rows inline-spelled (M0), rows transported and
named (PT2), the same spelling on both sides of one isolated
conversion (PA), a written one-level mirror bridge (PM), and the
committed 732 shape (amb4-732-verbatim).  Because `PA` kills identical
spellings, no spelling of the rows can dodge the assembly's
conversion, and because `Amb2`'s matrix15 slot is the same shape one
level up and the probe's `MatrixAt` (φ₃ body `W3.erased`,
`agents/tasks/LJ-1-667/Probe667.agda:46-47`) forces that row, the
chain behind the obligation is closed at wide.

## WHY THIS IS NOT A RETRY OF WHAT 746 WALLED

746 walled the direct `Amb4` term and the erase-cong bridge inside the
assembly, and priced candidate 1 only as a proposal.  This dispatch
built candidate 1's own named moves -- the sibling spelling module
with the rows transported inside it -- and they are GREEN
(`runs/PT.agda`), with two new measured cures inside them (the
implicit spelling and the `countTm` alphabet pin, `runs/pt4.out`/
`runs/pt5.out` vs `runs/pt6.out`).  What walls is the assembly
itself, measured fresh here three ways (PT2, M0, PA) plus the mirror
bridge (PM) plus the committed 732 shape.  Per the coder's heap-wall
clause, the restructures were tested in the same dispatch before any
of this was reported; the last one (FloorB2's conv-first bridge) ran
minutes before this report was filled.

## WHAT THE NEXT BRIEF NEEDS

- Import `LJ-1-746-SPLIT.runs.PT`; do not rebuild it.  It is the
  green spelling module, tracked, rc 0.
- Do not retry the `GraphAt` assembly in any spelling, and do not
  retry a reading-level `≡` conversion (mirror included) without a
  new idea: `runs/pa.out` shows identical spellings die.  The
  surviving escape routes are named in the review: a brief-level
  candidate 3 that changes what `Amb2`/the probe consume (a named
  mirror type end to end), the owner's heavy-tier ruling (PA's
  evidence cuts against it -- the conversion's normalization is the
  poison, and heavy only caps it later), or a new bridge candidate.
- The bridge is its own wall: the frame minus the bridge is 31.95 s
  (`runs/floorB1.out`), the frame with the `AT.read` step grinds past
  700 s (`runs/floor746split-2.out`), and the conv-first rewrite
  still grinds (`runs/floorB2b.out`).  Any chain cure must also price
  the bridge at its own site.
- `Probe746Split.agda.txt` is the ready shape: it typechecks the day
  the chain closes and the bridge lands.

## WHAT THE SHAPE RESISTED

- The plus-zero implicits: Agda cannot decompose `countFo` of a Def
  formula against a meta-headed plus (`_a + (countFo A + _b) = 0`,
  blocked on `_a`, `runs/pt.out:4-14`).  Spell them.
- `countTm (var kk)` leaves its alphabet implicit unsolved; it needs
  `countTm {K = CS.S}` (`runs/pt5.out`).
- The vendor-copy necessity: the brief's named import target
  (`LJ-1-746.runs.*`) is uncommitted, so a fresh checkout cannot
  resolve it; the copies under this task's module names are the way
  the import happens, and they are diff-verbatim.

## RECORD FACTS

- Nothing in `src/` was written; nothing was committed or pushed.
- ONE Agda process at a time; `GHCRTS` never set by this dispatch
  (line 1 of every `.out` records the pane's caliber).  All deaths
  were heap exhaustion (rc 251) or this dispatch's own bash windows:
  no kill line in either watchdog log falls inside this task's run
  window (first run `2026-08-29T04:12:57Z`, last `05:39:37Z`, per the
  `.out` headers), and the logs' last entries remain the 09:39:41 /
  09:40:03 kills 746 already recorded.  Swap never neared the guard
  (total 2048 MB).  Two sibling panes ran their own Agda processes
  during this dispatch (LJ-1-740-SPLIT, LJ-1-742-SPLIT-SPLIT, seen in
  `ps` mid-session); the shared machine was under that load while
  these numbers were measured, as it was for 746's.
- Files that cannot typecheck are named `.agda.txt`: M0, PA, PM,
  PT2, Floor746Split, FloorB1, FloorB2, and the drafted probe.  Green
  files keep `.agda`: Amb7, EraseIrr, PT.
- The floor discipline: FloorB1 is the frame's price (31.95 s); the
  full floor never landed, so the frame-plus-bridge has no green
  number and none is claimed.
- The ratio bar cannot fire on this task: the write scope holds no
  `src/` master and no fenced agda lines; the divisor is 0.
- `make check` was not run: no `src/` file and no commit is proposed
  by this return.  The green runs are the type evidence for what
  landed; the walls are the evidence for what did not.

## THE ORDERED CHECKER OUTPUT

```
check-survey-quotes: LJ-1-746-SPLIT clean (0 note(s), 0 defect(s))
```
(Run as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-746-SPLIT`
from this worktree root; this worktree has no `.venv`, so the main
checkout's pinned interpreter was used, the LJ-1.745/746 precedent.)

## ARCHIVE USED

- **`archive/dev/DD-archived.md` READ.**  Line 30 carries DD18, which
  makes these two sections a duty: "THE ARCHIVE AND LITERATURE
  SURVEYS are sections of the brief and of the return, not a hope."
  Line 35 carries DD25, the rule this return's paired review is
  written under: "A NEGATIVE RETURN IS ADVERSARIALLY REVIEWED AT
  MAXIMUM EFFORT, IMMEDIATELY, AND THE TWO ARE THEN READ TOGETHER."
  Hence `review-of-bound-in-stage-at-empty.md` beside this report.
- **`archive/dev/ORCHESTRATION.md` DECLINED.**  Not read: dispatch
  mechanics do not bear on an elaboration wall.
- **`archive/dev/PLAN-archived.md` DECLINED.**  Not read: a retired
  construction registry; the live status is the screen the program
  injected, and this return does not restate it.
- **`archive/dev/STATUS-archived.md` DECLINED.**  Not read: a
  superseded goal table; this task's goal and verdict come from its
  brief and its own runs.
- **`archive/dev/TASKS-archived.md` DECLINED.**  Not read: every
  number above was measured this task at its own site; no earlier
  dispatch's findings are load-bearing here except 746's and 745's,
  whose reports sit in the live tree and are cited by path.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` DECLINED.**  Not
  read: the slot-role question is about the level formula's reading;
  this task measured elaborations and built no new formula roles.
- **`dev/literature/devlin-errata.md` DECLINED.**  Not read: no
  literature formula is quoted or corrected; the target's truth (D-10)
  is not in question -- the wall is elaboration cost.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.**  Not
  read: no glossary term is proposed or questioned here.
- **`dev/literature/primary-sources.md` DECLINED.**  Not read: this
  is not a provability probe (DD28's trigger); it is a caliber
  measurement over an existing chain.
- **`dev/literature/rudimentary-functions.md` DECLINED.**  Not read:
  rudimentary functions play no part in the plus-split conversions
  this dispatch measured.
