# LJ-1.619 report: what it costs merely to LOAD what a landing needs

## HEAD
head_slot: coder
machine: exclusive
verdict: GO

## WHAT THIS MEASURED

One term, `import-floor`, at the top rung
(`agents/tasks/LJ-1-619/Probe619.agda:34-35`), over the eleven cumulative
import rungs `runs/Rung01.agda` through `runs/Rung10.agda`. A fresh Agda
process typechecked each rung alone. The order of the eleven is
`[LJ-1.555]`'s count of `CardAboveL`'s dependencies
(`agents/tasks/LJ-1-555/review-of-CardAboveL-landing.md:56`):

1. `L.Cardinal`
2. `L.BoundedSubset`
3. `L.CantorBernstein`
4. `L.InjChain`
5. `L.Ordinal.Stages`
6. `L.Ordinal.Linear`
7. `L.Constructible`
8. `L.Ordinal`
9. `V.Model`
10. `V.Presentation`
11. `V.Hierarchy`

**THE CALIBER, STATED FOR THE FIRST TIME FOR A LANDING OF THIS SHAPE.**
`GHCRTS=-A64m -I0 -M2g`, taken from the pane, one Agda process at a time,
never set by this task. Every `.out` file records the caliber it ran under.

The `src/` interfaces were WARM: all eleven `.agdai` files existed under
`_build/2.8.0/agda/src/` before any rung ran, and no rung rebuilt one. The
numbers below are the cost of a fresh process loading the closure from warm
interfaces, which is the cost a landing's first elaboration pays before it
can start on its own term.

## THE LADDER

Filled rung by rung; the `.out` file is the evidence. Peak RSS in bytes.

| rung | module added            | peak RSS     | seconds | exit |
|------|-------------------------|--------------|---------|------|
| 1    | L.Cardinal              | 399130624    | 1.57    | 0    |
| 2    | L.BoundedSubset         | 636403712    | 2.98    | 0    |
| 3    | L.CantorBernstein       | 636469248    | 2.65    | 0    |
| 4    | L.InjChain              | 636469248    | 2.68    | 0    |
| 5    | L.Ordinal.Stages        | 636502016    | 2.67    | 0    |
| 6    | L.Ordinal.Linear        | 635404288    | 2.69    | 0    |
| 7    | L.Constructible         | 635453440    | 2.67    | 0    |
| 8    | L.Ordinal               | 635420672    | 2.65    | 0    |
| 9    | V.Model                 | 635420672    | 2.69    | 0    |
| 10   | V.Presentation          | 637534208    | 2.77    | 0    |
| 11   | V.Hierarchy (Probe619)  | 634322944    | 3.01    | 0    |

## CAN ANYTHING LAND AT THIS CALIBER

**Yes, and the import floor leaves most of the cap free.** The top of the
ladder, the full eleven-module closure with one trivial term, peaks at
634,322,944 bytes (605 MiB) of the 2,147,483,648 byte (`-M2g`) cap and takes
3.01 s: 29.5 % of the heap and 3 s of the wall clock, with 1.36 GB of headroom
left for a new module's own elaboration. A new master over these imports is
therefore possible at this caliber, and it stopped being possible at NO rung:
every one of the eleven rungs exited 0 and no rung approached the cap, so
the defect the two predecessors walled on is not the import floor.

## WHAT THE NEXT BRIEF NEEDS

**THE LOAD IS NOT THE WALL, AND NO RUNG NAMES A MODULE THAT COSTS.** Rung 2
(`L.BoundedSubset`) is the only real step: +237 MB and +1.4 s over rung 1.
Rungs 3 through 11 are flat within 3 MB of one another, because the nine
remaining modules share the closure rung 2 already forced open. The
ladder's shape says the eleven load in one step and then stop costing.

**THEREFORE THE 18.79 s AND 19.32 s WALLS LIVED ABOVE THIS FLOOR.** The top
floor is 3.01 s, so both predecessors spent roughly 16 s and 16.3 s in work
this probe does not carry: the new master's OWN elaboration, and anything a
run pays when its `_build` ifaces are not the warm set this probe loaded.
This task's numbers rule out the load alone. They do not price the new
term, and the floor price does not transfer to it (the cure does not
transfer by analogy): the next attempt at a landing must measure the new
module's own elaboration, e.g. by the floor-with-a-hole discipline of
`[LJ-1.559]` (`agents/tasks/LJ-1-559/lj-1.559-report.md:1`), before the
full proof runs at this caliber.

**ONE CAVEAT, STATED.** Every rung above loaded WARM interfaces: all eleven
`.agdai` files existed under `_build/2.8.0/agda/src/` before any rung ran,
and no rung rebuilt one (the `.out` files show one `Checking` line each,
the rung itself, and no dependency recheck). If a landing worktree's
`_build` were colder or stale, its load would cost more than these numbers,
and the brief that prices a landing should say which state it assumes.

**THE CALIBER OF RECORD.** `GHCRTS=-A64m -I0 -M2g` from the pane, the wide
tier's cap. Every `.out` file under `runs/` records the caliber it ran
under, the limit, and the clock. One Agda process ran at a time. The
deadline limit was 900 s; the slowest rung took 3.01 s, so no rung came
near it.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md` was read. Premise 10 cites it, and the
  ladder is its discipline re-applied to a load. Line 142: `| LJ-1.75 | Give
  each partial only the facts its rows use | 43 of 69; 122.45 s | Better than
  proportional: 41.6 pc cheaper for a 37.7 pc smaller telescope. Two partials
  plus composer, 273.88 s |`. It is the comparability of SHAPE the brief's
  ESTIMATE names, and nothing is funded against it here.
- `archive/dev/JOURNAL-archived.md`, declined: not read. This task prices a
  load; the journal holds campaign history, and the brief's premises cite
  nothing from it.
- `archive/dev/JOURNAL.md`, declined: not read. Same reason.
- `archive/dev/ORCHESTRATION.md`, declined: not read. Same reason.
- `archive/dev/DECISIONS-archived.md`, declined: not read. Same reason.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`, declined: not read. This is
  a measurement task with one term and no mathematics to settle.
- `dev/literature/devlin-II5.md`, declined: not read. Same reason.
- `dev/literature/digest.md`, declined: not read. Same reason.
- `dev/literature/fine-structure.md`, declined: not read. Same reason.
- `dev/literature/terms-2026-08.md`, declined: not read. Same reason.
