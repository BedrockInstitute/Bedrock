# LJ-1.622 report: bisecting the `CardAboveL` elaboration at the pane's caliber

## HEAD
head_slot: coder
machine: exclusive
verdict: GO. No part of the `CardAboveL` elaboration exceeds the caliber, and no
single part dominates: every rung, including the top, is green at
`-A64m -I0 -M2g` in this worktree, and the highest peak of the whole ladder is
843,366,400 bytes (39.3 percent of the cap). The wall the two predecessors hit
is not in the master in this worktree, and this report says what is left.

## THE OBLIGATION

ONE term in `agents/tasks/LJ-1-622/Probe622.agda`:

    landing-bisection : CardAboveLᵀ

which is `CardAboveL` itself: `noInjOrd→CardAboveLᵀ noInjOrd`, the same
declaration the probe states at `agents/tasks/LJ-1-528/Probe528.agda:638-643`.
It is a
MEASUREMENT: nothing lands in `src/` and `make check` is not run.

## CALIBER AND STATE

- **Caliber: `-A64m -I0 -M2g`**, read from the pane's `GHCRTS` at the start of
  this dispatch. It is the WIDE tier's cap (2,147,483,648 bytes), and it is NOT
  the `-M8g` several earlier reports quote. It was never set by this task.
- **The eleven src interfaces were WARM** before any rung ran: the floor rung
  (below) re-checked nothing under it, the way `[LJ-1.619]`'s ladder did.

## D-10: THE PARTS, NAMED BEFORE ANY AGDA

The 587-line landed master is absent from this worktree: `[LJ-1.555]`
delivered it at a path its write scope could not commit, and
`git log --all -- src/L/CardinalAbove.lagda.md` is empty at HEAD `62c52de1`.
The master's content is the probe's sections 0 to 4, 8 and 9 trimmed to the
obligation, and `[LJ-1.555]`'s report says the statement is byte-identical to
the probe's. The bisection therefore runs over `agents/tasks/LJ-1-528/Probe528.agda`'s
sections, re-cut into four parts under one shared header, so that a delta
between two rungs is never an import delta. The parts, before any of them ran:

| part | what it is | file, lines | probe source |
|---|---|---|---|
| floor | one trivial term over the eleven imports | `agents/tasks/LJ-1-619/Probe619.agda:34-35` | re-measured in this worktree |
| 1 | the bridges: the obligation type, `ordL`, `ambient→internal` | `agents/tasks/LJ-1-622/Part1.agda` | `Probe528.agda:62-105` (sections 0 to 2) |
| 2 | the separation module `Sep` | `agents/tasks/LJ-1-622/Part2.agda` | `Probe528.agda:106-175` (section 3) |
| 3 | the reduction: `NoInjOrd`, `above`, `cardAboveAt`, `ambientCardAbove`, `noInjOrd→CardAboveLᵀ` | `agents/tasks/LJ-1-622/Part3.agda` | `Probe528.agda:177-236` (section 4) |
| 4 | the Hartogs construction, `module Hartogs`, and `noInjOrd` | `agents/tasks/LJ-1-622/Part4.agda` | `Probe528.agda:295-634` (section 8 plus the one line of 9) |
| top | `landing-bisection`, the obligation, one term over the parts | `agents/tasks/LJ-1-622/Probe622.agda` | `Probe528.agda:638-643` |

Each rung after the floor imports the parts that precede it, and each is
typechecked by ONE fresh Agda process, so the peak RSS of a rung is the
high-water mark of a single fresh master at the point that part elaborates.
The floor is rung 0 of the ladder and the W3 part is Part 1: the smallest
part of `CardAboveL` that typechecks alone, run first and written to
`runs/` before a second part exists.

## THE PARTS

Peak RSS in bytes; the cap is 2,147,483,648 bytes. Each rung ran in ONE fresh
Agda process; each number was written to `runs/` before the next rung started.
The first pass is the valid set: every rung of it carries a `Checking` line
for its own module, so each part was genuinely elaborated over warm interfaces
of the parts below it. The second pass re-ran the same files; Agda found each
module up to date (no `Checking` line) and so those numbers are pure
interface loads, not re-elaborations.

**First pass: the elaboration, rung by rung.**

| rung | part | peak RSS | percent of cap | seconds | exit | log |
|---|---|---|---|---|---|---|
| 0 | floor, eleven imports, one trivial term | 765,902,848 | 35.7 | 3.06 | 0 | `runs/floor.out` |
| 1 | Part 1, the bridges | 675,119,104 | 31.4 | 2.99 | 0 | `runs/part1.out` |
| 2 | Part 2, `Sep` | 840,253,440 | 39.1 | 3.29 | 0 | `runs/part2.out` |
| 3 | Part 3, the reduction | 843,366,400 | 39.3 | 3.28 | 0 | `runs/part3.out` |
| 4 | Part 4, `Hartogs` and `noInjOrd` | 738,099,200 | 34.4 | 3.91 | 0 | `runs/part4.out` |
| 5 | `landing-bisection` over the parts | 687,243,264 | 32.0 | 3.15 | 0 | `runs/probe622.out` |

**Second pass: the same rungs as pure interface loads.**

| rung | part | peak RSS | seconds | exit | log |
|---|---|---|---|---|---|
| 0 | floor | 765,902,848 | 3.05 | 0 | `runs/floor2.out` |
| 1 | Part 1 | 658,964,480 | 2.70 | 0 | `runs/part1b.out` |
| 2 | Part 2 | 770,129,920 | 2.75 | 0 | `runs/part2b.out` |
| 3 | Part 3 | 760,692,736 | 2.72 | 0 | `runs/part3b.out` |
| 4 | Part 4 | 671,580,160 | 2.73 | 0 | `runs/part4b.out` |
| 5 | top | 764,903,424 | 2.75 | 0 | `runs/probe622b.out` |

One further data point, recorded before any part existed: a manual run of the
floor file in this worktree, before `runs/run.sh` existed, peaked at
635,387,904 bytes in 2.74 s, exit 0. It is the same file under a different
condition (it wrote the module's first interface here), and the two
`run.sh` floor runs are identical to the byte at 765,902,848, so the run-to-run
spread of the floor alone is 635 to 766 MB (20 percent) and the per-part
deltas inside that spread are not separable from it.

## WHAT A LANDING BRIEF SHOULD NOW SAY

1. Land the 587-line master as `src/L/CardinalAbove.lagda.md` with a write
   scope that names that path AND the one aggregator line in
   `src/Everything.lagda.md`, because `[LJ-1.555]`'s scope named neither and
   the result was green in its worktree and absent from the branch (`git log
   --all -- src/L/CardinalAbove.lagda.md` is empty at `62c52de1`).
2. It must state the WARM premise and the term set: with the eleven src
   interfaces warm at `-M2g`, the whole four-part ladder plus the term peaks
   at 843,366,400 bytes (39.3 percent of the cap) in 3.91 s, so the master
   lands with 1.3 GB of headroom; the two predecessors walled at 18.79 s and
   19.32 s, and that duration matches the 14 s cost of `[LJ-1.526]`'s probe
   plus a 4 s master, so the landing must not import that probe (the probe
   calls it "a 14 s module", `agents/tasks/LJ-1-528/Probe528.agda:99`) and must not
   re-run `make check` as part of the landing run.
3. It must start with a floor check at the `[LJ-1.559]` discipline: if the
   landing worktree's warm floor reads about 766 MB / 3 s as this task's did,
   the elaboration fits; if the floor itself reads far higher, the wall is in
   that worktree's `_build` and not in the term, and the brief should bisect
   the build state instead of the term again.

## WHAT THE MEASUREMENT CARRIES AND WHAT IT DOES NOT

**CARRIES.** Two numbers per rung over the whole landing shape (the
elaboration and the interface load), the obligation term green at the top
rung (`runs/probe622.out`, exit 0), and the verdict that the master's own
elaboration fits the wide-tier cap in this worktree: the highest rung is Part
3 at 843,366,400 bytes, 39.3 percent of the cap, and the highest delta between
two adjacent rungs of the first pass is 165 MB (Part 1 to Part 2), which is
inside the floor's own 131 MB run-to-run spread. Nothing in the term
dominates, and the brief's second result branch is the one that landed: the
587 lines are not uniformly expensive either, they are all cheap, and the
expensive thing in the ladder is the floor load itself, 766 MB and 3 s,
against a 3.91 s wall clock on the longest rung.

**DOES NOT CARRY.** The cause of the two 19 s walls. This worktree's warm
state cannot reproduce them, and four causes are now excluded by
measurement: `make check` (`[LJ-1.616]`), the import order (`[LJ-1.599]`
against `[LJ-1.616]`), the import closure (`[LJ-1.619]` at 29.5 percent of
cap), and, in this worktree, the master's own elaboration (this task,
39.3 percent at the worst rung). What remains is the difference between this
worktree and the predecessors': a colder or stale `_build` in their trees
(`[LJ-1.619]` states exactly this caveat in its own report), or a wider term
set than the 587-line master, of which the 14 s `[LJ-1.526]` probe is the only
cost of that order in the campaign. This task priced the master; it did not
price the predecessors' runs, and a measured cure does not transfer by
analogy in either direction.

**W2.** The brief names no fixed carrier and this task instantiates nothing:
the obligation term is stated once, at a generic `ℓ` and one `LEM`,
byte-identical to the probe's, and there is no second proof in this tree that
could have gotten its own copy. The rule is not exercised here, so it is
answered as: nothing to share, nothing fixed.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md` was read. Premise 10 cites it, and the
  landing brief's trimming sentence stands on it. Line 142: `| LJ-1.75 | Give
  each partial only the facts its rows use | 43 of 69; 122.45 s | Better than
  proportional: 41.6 pc cheaper for a 37.7 pc smaller telescope. Two partials
  plus composer, 273.88 s |`. It is a comparability of SHAPE and nothing in
  this measurement is funded against it.
- `archive/dev/JOURNAL-archived.md`, declined: not read. The campaign history
  it holds is not a premise of this measurement.
- `archive/dev/JOURNAL.md`, declined: not read. Same reason.
- `archive/dev/DECISIONS-archived.md`, declined: not read. Same reason.
- `archive/dev/ORCHESTRATION.md`, declined: not read. Same reason.

## LITERATURE USED

- `dev/literature/digest.md`, declined: not read. This is a measurement task;
  no mathematical statement is settled and no digest entry changes anything.
- `dev/literature/truncation-and-selection.md`, declined: not read. Same
  reason; the truncation behavior is settled by `[LJ-1.526]` and untouched.
- `dev/literature/devlin-II5.md`, declined: not read. The Devlin II.5 content
  lives in `L.StageCardinal` and `L.BoundedSubset`, which this probe only
  loads, not prices.
- `dev/literature/level-formula-slot-roles.md`, declined: not read. No level
  formula question is open in this task.
- `dev/literature/formalizations-landscape.md`, declined: not read. No
  positioning question is open in this task.
