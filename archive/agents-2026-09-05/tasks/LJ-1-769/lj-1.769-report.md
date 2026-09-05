# LJ-1.769 report: commute-from-reading, no pinned Sigma

## HEAD

head_slot: coder
machine: shared
agda_tier: heavy
task: LJ-1.769
obligation: agents/tasks/LJ-1-769/Probe769.agda::commute-from-reading
verdict: **NO-GO, a HEAP WALL, PARKED AND SPLIT.** `commute-from-reading`
is not assemblable at `-M4g` in this frame from the delivered pieces.
The route's collapse-crossing, Probe652's `Carry.push` applied at
code-coordinate entries, HEAP-WALLS in every shape this dispatch
could build or factor: shape 1, all inline, dies on GHC's own heap
overflow (runs/probe769-1.out:4-8, EXIT 251 at 1019.64 s, peak RSS
4607737856 B); shape 2, the variable-membership core, is killed at
the same footprint (runs/probe769-4.out:4-6, 493.92 s, 4642553856 B);
shape 3, the ascribed reading with the ordinality carried by the
small isOrdAt reading, dies on GHC's heap overflow again
(runs/probe769-5.out:4-8, EXIT 251 at 1017.53 s, 4613963776 B, the
message "Heap exhausted; Current maximum heap size is 4294967296
bytes (4096 MB)"). The split instrument settles the site: the push
ALONE, with the sound application and every transport below it a
designed hole, is killed at 817.97 s and peak RSS 4335517696 B
(runs/split4-769.out:4,5,6,24) -- the same push that Probe652's
commute₃ pays inside a 4.87 s whole-file check when its vector
entries are variables (runs/warm-p652.out:5). The obligation file
cannot typecheck and rests at `Probe769.agda.txt` (naming rule);
supply stays 0. No `review-of` is written: the brief forbids one for
a resource wall. The floor, the two interfaces, and the four warm-up
rows are green and on the meter (section 1). The environment
degraded mid-dispatch after the first wall and recovered near the
end; every post-wall kill that preceded the recovery is marked
environment in section 1 and section 4. After this report was
first written, the PROGRAM'S acceptance arm was itself killed
under load (runs/accept-1.out:8,10,16: load 8.97/11.03/14.96,
conjunct 1 FAILED, its `Frame769` run rc -9 at 1.99 s), and this
dispatch re-measured both interfaces green at 2026-09-03T04:24Z
(section 1), so that kill is environment of the same class and
the interfaces' greens now have surviving .out files.

## THE DELIVERABLE

- `Probe769.agda.txt` -- the obligation at the brief's type, in
  shape 3, the strongest of the four shapes: the reading produced and
  consumed at code coordinates, the collapse-coordinate reading
  ascribed once, the parameter's ordinality crossing by the arity-1
  isOrdAt reading. Its only diagnostic is the GHC heap overflow
  (runs/probe769-5.out:4-8). It rests at `.agda.txt`, never `.agda`
  (naming rule): it cannot typecheck under the pane caliber.
- `runs/Frame769.agda` -- the vendored frame, transcribed,
  byte-faithful below the header (diff-measured: exactly one
  differing line, the module line). GREEN, re-measured
  2026-09-03T04:24Z under the pane caliber at 3.62 s, peak RSS
  658702336 B, EXIT 0 (runs/frame769.out:3,4,21). The 01:50 floor
  attempt had checked it green first, but that run's .out was
  overwritten by the 01:56 floor re-run, which is why the file's
  own header names this re-measure. Every later run loads its
  cached interface
  (`_build/2.8.0/agda/agents/tasks/LJ-1-769/runs/Frame769.agdai`)
  without a recheck.
- `runs/HullHalf769.agda` -- the vendored hull half, transcribed,
  import retargeted (diff-measured: exactly two differing lines, the
  module line and the import). GREEN, re-measured
  2026-09-03T04:24Z under the pane caliber at 3.53 s, peak RSS
  672727040 B, EXIT 0 (runs/hullhalf769.out:3,4,21).
- `runs/Floor769.agda.txt` -- the floor instrument: the obligation
  file with the term a designed hole. Its only diagnostic is the
  designed hole, at `Floor769.agda:135.5-9` (runs/floor769.out:4-6).
  GREEN-to-the-hole at 110.87 s, peak RSS 1865203712 B, EXIT 42 by
  design (runs/floor769.out:4,7,8,25).
- `runs/Shape1-769.agda.txt` -- the first shape, kept as the wall
  instrument (naming rule: it cannot typecheck, so it rests at
  `.agda.txt`).
- `runs/Split4-769.agda.txt` -- the SPLIT instrument: the push alone,
  the sound application and the transports a designed hole. Killed at
  4.34 GB (runs/split4-769.out:4,5,6,24). This is the row that parks
  the route: the wall's site is the push, not the assembly around
  it.
- `runs/BisectB1-769.agda.txt`, `runs/BisectB2-769.agda.txt`,
  `runs/BisectC1-769.agda.txt`, `runs/BisectC2-769.agda.txt` --
  written for the mid-dispatch bisection, killed by the environment
  collapse (runs/bisect-b1.out, runs/bisect-c1.out); B2 and C2 never
  ran. They stay for any re-dispatch on a settled box.

## 1. THE PRICES

All runs under `runs/run.sh`, one Agda process per row, pane caliber
`-A64m -I0 -M4g`, 1800 s cap. The warm-up rows paid this worktree's
cold closure and are environment, not prices.

| run | file | exit | time | peak RSS | evidence |
|---|---|---|---|---|---|
| warm Probe652 | `agents/tasks/LJ-1-652/Probe652.agda` | 0 | 4.96 s | 1083211776 B | runs/warm-p652.out:4,5,6,23 |
| warm Probe667 | `agents/tasks/LJ-1-667/Probe667.agda` | 0 | 13.52 s | 1844461568 B | runs/warm-p667.out:6,7,24 |
| warm Probe673 | `agents/tasks/LJ-1-673/Probe673.agda` | 0 | 98.03 s | 1418936320 B | runs/warm-p673.out:4,5,22 |
| warm Probe692 | `agents/tasks/LJ-1-692/Probe692.agda` | 0 | 108.38 s | 1753743360 B | runs/warm-p692.out:7,8,25 |
| floor | `runs/Floor769.agda.txt` | 42, designed | 110.87 s | 1865203712 B | runs/floor769.out:4,7,8,25 |
| shape 1 | `Probe769.agda` (now `runs/Shape1-769.agda.txt`) | 251, WALL | 1019.64 s | 4607737856 B | runs/probe769-1.out:4,5,6,7,8,25 |
| shape 2 | `Probe769.agda` | SIGKILL | 493.92 s | 4642553856 B | runs/probe769-4.out:4,5,6,24 |
| floor re-run (environment canary) | `runs/Floor769.agda.txt` | SIGKILL | 14.93 s | 1758347264 B | runs/floor769-env.out:4,5,6 |
| floor canary, recovered | `runs/Floor769.agda.txt` | 42, designed | 143.07 s | 1865252864 B | runs/floor769-canary5.out:4,7,8,25 |
| shape 3 | `Probe769.agda.txt` | 251, WALL | 1017.53 s | 4613963776 B | runs/probe769-5.out:4,5,6,7,8,25 |
| shape 4, the split | `runs/Split4-769.agda.txt` | SIGKILL | 817.97 s | 4335517696 B | runs/split4-769.out:4,5,6,24 |
| frame re-measure | `runs/Frame769.agda` | 0 | 3.62 s | 658702336 B | runs/frame769.out:3,4,21 |
| hull re-measure | `runs/HullHalf769.agda` | 0 | 3.53 s | 672727040 B | runs/hullhalf769.out:3,4,21 |

Three rows are REAL walls under the pane caliber, each in a
different shape of the same term: shape 1 and shape 3 die on GHC's
own heap-overflow exit 251 with the message in the .out, and shape 2
is killed at the same footprint with the box's swap collapsing during
the run (section 4). The floor re-run row is environment: the SAME
floor file that greened at 110.87 s at 01:59 is killed at 14.93 s at
02:38, so the post-02:24 kills before 03:34 are not prices; the
canary row shows the floor green again at 03:34, and shape 3 and the
split ran after that recovery, so THEIR rows are prices. The split
row is the finding: with everything below the push a designed hole,
the push alone still reaches 4.34 GB. The wall's site is the push's
own elaboration at code-coordinate entries, not the assembly around
it.

## 2. THE ROUTE CORRECTION

The brief's named route, "use grounded-from-complete for the reading,
rec on that truncated Sigma", is not assemblable for THIS goal, and
the report says so before the wall rows do. Two independent grounds,
both from the tree:

1. **The truncated Sigma erases exactly what a push-consumer needs.**
   The SPLIT-SPLIT packing keeps only ca, cp, z and the reading --
   the hull membership of the witness is discharged by a wildcard and
   names no slot (Probe767SplitSplit.agda:140: `PT.map (λ { (a , _ ,
   sat) -> ...`), and neither code equation survives. `Cy.push`'s
   vector carries a pair per slot, so its third entry needs exactly
   `⟨ z ∈ˢ HS.M ⟩`, and the goal's coordinates can only be reached
   through the code equations -- both are gone at the rec. The
   obligation's type never mentions the Sigma, so no consumer can
   re-derive the erased facts from them: the quadruple is compatible
   with any δ.
2. **The reading therefore comes from the supplier's own pipeline run
   untruncated**: codeOf at the telescope's memberships (the two
   memberships the brief sends to the telescope), hullClosed at those
   codes, conv0 at the witness. Every piece is a frame export; no new
   mathematics, no pinned Sigma, no mkWit, no Convert hypothesis, and
   no reading is ever transported along either code equation -- the
   push consumes the reading at code coordinates, and only the
   resulting set equality moves by cong.

Every prohibition of the brief holds in the delivered file.
`grounded-from-complete` itself is not imported: its truncated export
has no legal consumer here (ground 1), and re-running its pipeline
untruncated is what grounds 2 delivers.

The wall then sits ON that legal route: the push at code-coordinate
entries walls in all three shapes (HEAD), and the split instrument
puts the wall inside the push itself (shape 4).

## 3. THE W2 ANSWER

DD4's rule is "MAXIMUM REUSE is the architecture's objective, and it
is the same rule as WRITE IT GENERIC" (archive/dev/DD-archived.md:22).
The dispatch answers it: the mathematics stands ONCE at the generic
carrier, and this task copies none of it. The carrier is the vendored
hull frame: the repaired telescope, Completeness as a hypothesis,
SatIn, HullM, codeOf (runs/Frame769.agda, byte-faithful to the
vendor, one differing line), hullClosed (runs/HullHalf769.agda,
byte-faithful, two differing lines), the generic carry Cy.push
(Probe652's Frame652.Carry, opened at this frame, not restated), the
constructed conv0 (hull-convert-at-matrix, opened, never
hypothesised), and the two tree lemmas the term reads
(isOrdAt-in/out, Probe652's commute₃ as the shape the core follows).
What this task writes new is glue only: the obligation's type spelled
once (Probe769.agda.txt:132-138), the arity-3 ordinality extraction
ord-at-p, four lines mirroring isOrdAt-out one binder deeper
(Probe769.agda.txt:124-130), and the two transports at the end. The
P-r exception does not bite: nothing here is a fold over a clause
list.

## 4. THE ENVIRONMENT AT DISPATCH AND ITS COLLAPSE

- No Agda process at dispatch (`pgrep -x agda` empty).
- Pane caliber `GHCRTS=[-A64m -I0 -M4g]` (heavy), read at dispatch,
  never set or changed by this task.
- `sysctl vm.swapusage` at dispatch: total 5120.00M, used 3897.31M,
  free 1222.69M.
- This worktree's `_build/2.8.0/agda/src/` holds 208 `.agdai` files
  and its `_build/2.8.0/agda/agents/tasks/` holds none of Probe652,
  667, 673, 692 (all cold here); the warm-up rows of section 1 paid
  that cold closure. The two interfaces (Frame769, HullHalf769) were
  paid inside the floor run.
- AFTER the shape-1 wall (1019.64 s at 4.61 GB), the box's swap grew
  from total 5120 MB to total 9216 MB, used 8726 MB, free 490 MB
  (02:38 reading). From then on the OS kills Agda during interface
  load: the floor, green at 01:59, is SIGKILLed at 02:38, 02:51,
  03:00, 03:12 and 03:22 (runs/floor769-env.out,
  runs/floor769-canary.out, runs/floor769-canary2.out,
  runs/floor769-canary3.out, runs/floor769-canary4.out), then greens
  again at 03:34 (runs/floor769-canary5.out:4-8, 143.07 s, 1.87 GB,
  the designed exit). Bisection
  instruments written at 02:35-02:37 (runs/BisectB1-769.agda.txt,
  runs/BisectB2-769.agda.txt, runs/BisectC1-769.agda.txt,
  runs/BisectC2-769.agda.txt) are killed
  the same way; their runs (runs/bisect-b1.out, runs/bisect-c1.out)
  are environment, not prices, and no conclusion is drawn from them.
- AFTER this report was first written, the program's acceptance
  arm re-ran the task and was killed in its turn:
  runs/accept-1.out records a 12:19:10 local start under load
  8.97/11.03/14.96 (accept-1.out:8,9), conjunct 1 FAILED
  (accept-1.out:10), and its own run of runs/Frame769.agda
  SIGKILLed at 1.99 s, rc -9 (accept-1.out:16). That kill is
  environment of the same class as the 02:38-03:22 kills above and
  not a price: this dispatch re-measured Frame769 and HullHalf769
  green at 2026-09-03T04:24Z on the recovered box, 3.62 s and
  3.53 s at under 0.7 GB each (runs/frame769.out,
  runs/hullhalf769.out, section 1), so the interface greens carry
  surviving evidence and the arm's failure has a green re-run
  beside it.

## 5. WHAT THE NEXT BRIEF NEEDS

- **The route is PARKED at the push, not at the type.** The goal
  type is cheap at this site (the floor greens at 110.87 s to
  143.07 s), and the assembly below the push is cheap (the
  SPLIT-SPLIT class, about 210 s). What walls is `Carry.push` itself
  at code-coordinate entries: cheap at variable entries
  (Probe652 whole file, 4.87 s, runs/warm-p652.out:5), killed at
  4.34 GB with only its own machinery live (runs/split4-769.out:4-6).
- **A next brief that wants this Commute needs a NEW collapse
  crossing**, or a push whose entries are variables at the call site.
  Two candidates the mathematician can judge: (a) prove the
  commutation at the codes by an induction that never pushes the
  3-slot reading (the twelve-wrap formula is what the iso machinery
  chokes on); (b) fund a re-cut where the hull vector's entries are
  bound INSIDE the push's own scope -- a push variant taking x with
  the membership as its parameter, so no entry is a redex at
  elaboration time. Both are mathematics-first; the second is priced
  by a probe like this one.
- **Do not re-brief this route with the same frame pieces.** The wall
  is measured at four shapes (probe769-1, probe769-4, probe769-5,
  split4-769); a fifth shape that still calls `Cy.push` on a vector
  whose entries are `fst (val _)` will wall the same way.
- The bisect instruments B1, B2, C1, C2 (runs/Bisect*.agda.txt) never
  produced usable rows: the box collapsed before they could run
  (section 4). On a settled box they would localize inside the push;
  a re-dispatch that wants that localization should run them first.
- The cone is now WARM at this worktree: the four probes, both
  interfaces, and the floor are cached, so a re-dispatch starts in
  the 5 to 15 s class for frame-level files (runs/floor769-canary5.out).

## SURVEY CHECK

Command: `.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-769`
(run with the main checkout's venv; this worktree has none of its
own; re-run at the close of this dispatch, same output). Output:

    check-survey-quotes: LJ-1-769 clean (0 note(s), 0 defect(s))

## ARCHIVE USED

- archive/dev/DD-archived.md -- READ at archive/dev/DD-archived.md:22,
  and the W2 answer rests on it: "MAXIMUM REUSE is the architecture's
  objective, and it is the same rule as WRITE IT GENERIC." The
  dispatch's reuse answer is section 3.
- archive/dev/ORCHESTRATION.md -- declined, header read only
  (archive/dev/ORCHESTRATION.md:1: "# ORCHESTRATION: the
  orchestrator's operating rules"). The one ruling this return needed
  (DD4) is quoted from DD-archived.md:22; the operating rules hold no
  term this task reads.
- archive/dev/PLAN-archived.md -- declined, not read (its first line
  is the archive stamp "# ARCHIVED 2026-08-20", at :1): a superseded
  plan, and no decision of this task needed one.
- archive/dev/STATUS-archived.md -- declined, header only (:1: "#
  STATUS-archived: the goal table of the internalization route"): a
  closed goal table of another route; this task's standing status is
  the screen, not this file.
- archive/dev/TASKS-archived.md -- declined, header only (:1: "#
  Archived task index: the `L3.32-T` series"): an index of a finished
  series outside this campaign.

## LITERATURE USED

All five candidates are digests of mathematics for chapter writing.
This task is an elaboration-wall probe: it states no mathematical
prose, quotes no source, and its only literature-facing duty was the
already-delivered Devlin II.5 mapping of Probe667. Each is therefore
declined, header read to confirm scope:

- dev/literature/glossary-review-2026-08.md -- declined (:1: "#
  Glossary review: the 119 pre-protocol entries"): terminology
  protocol work; this term adds no glossary entry and translates
  nothing.
- dev/literature/BIBLIOGRAPHY.md -- declined (:1: "# Bibliography for
  the rud route"): the rud route's source list; the probe cites no
  source.
- dev/literature/primary-sources.md -- declined (:1: "# Primary
  sources, second round: Jensen manuscript, Devlin, Jech"): fetch
  notes for chapter mathematics; nothing here is fetched or quoted.
- dev/literature/rudimentary-functions.md -- declined (:1: "#
  Rudimentary functions, closure, and the comprehension theorem"):
  the comprehension-theorem route; this probe's obligation touches no
  rudimentary function.
- dev/literature/fine-structure.md -- declined (:1: "# Fine
  structure: projecta, standard codes, the reductions, and their
  dependencies"): projecta extraction notes; no projectum appears in
  this task.
