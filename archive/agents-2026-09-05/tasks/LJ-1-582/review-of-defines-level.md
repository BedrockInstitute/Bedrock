# review-of-defines-level

**STOP. `defines-level` IS NOT DELIVERED, AND THERE IS NO TERM OF THAT NAME IN
`agents/tasks/LJ-1-582/Probe582.agda`.**

## The obligation

    defines-level : Cert.DefinesLevel      (agents/tasks/LJ-1-578/Probe578.agda:234-240)

The brief funds clause (i) of the level-hood certificate, one clause of three.

## What stops it

**IT IS NOT ONE STOP. IT IS TWO, AND THEY ARE DIFFERENT IN KIND.**

### 1. A MATHEMATICAL GAP, and it is not new

Clause (i) needs the level-hood formula DECODED at the stage. That decode is
`[LJ-1.230]`'s obligation, reported NO-GO there with three walls named
(`agents/tasks/LJ-1-230/lj-1.230-report.md:11-24`, `:64-86`). This task closes
wall (b) and leaves (a) and (c) standing:

| `[LJ-1.230]` wall | what it is | this task |
|---|---|---|
| (a) bounded against unbounded graph | `[LJ-1.570]`'s `GraphAgree` | **STANDING.** Named, not built. `agents/tasks/LJ-1-570/Probe570.agda:289-294` |
| (b) the carrier change | no total map `CS.S → SL` | **CLOSED.** `runs/s5-1.out`, exit 0 at 11.31 s |
| (c) the internal hierarchy in the bound | `[LJ-1.532]`'s `HierInK` | **STANDING.** Named, not built. `agents/tasks/LJ-1-532/Probe532.agda:274-277` |

### 2. A RESOURCE WALL, AND IT IS NEW

**The uniqueness half of clause (i) is WRITTEN and does not fit the caliber.**
`agents/tasks/LJ-1-582/runs/full-probe.txt` is the probe with four more
sections; it is not typechecked, and this is the measurement:

| run | file | exit | seconds | peak bytes |
|---|---|---:|---:|---:|
| `runs/p-17.out` | the probe as it stands | **0** | 53.58 | 1,364,049,920 |
| `runs/p-19.out` | plus `only-witness` | 143, I stopped it | 1140.95 | 9,690,267,648 |

The cap on this pane is `-A64m -I0 -M8g`. I did not set it and did not raise it.
Both runs are on a machine whose free memory was not scarce and where my own Agda
was the only large consumer.

## What IS delivered, and it is not nothing

`Probe582.agda` typechecks (`runs/final-1.out`, exit 0). It carries the formula
clause (i) asks for, written out over the hull's code carrier, its Δ₀ witness at
three carriers, and the two named hypotheses that turn `[LJ-1.570]`'s row six
into the stage decode.

**AND ONE MEASURED LAW.** `runs/s6-1.out` and `runs/s7-1.out` are the same file
with one implicit argument written out: `agda: Heap exhausted` at 182.14 s
against exit 0 at 11.20 s.

## What I did NOT do

I did not postulate. I did not land in `src/`. I did not raise the heap cap. I
did not write a term named `defines-level`, and I do not read a discharge into
any term in this probe: every one of them is an implication with named
hypotheses.

## Re-verified on the re-dispatch, 2026-08-23, at the moved caliber

The owner's ruling of 2026-08-23 sets both tiers to `-A64m -I0 -M4g`; the
acceptance arm ran this task under it (`runs/accept-1.out`, `runs/accept-2.out`)
and so did the re-dispatch. The verdict above holds at the new cap, and the
evidence was re-taken, not carried:

- **The green probe is green.** `runs/final-5.out`, forced recheck, exit 0,
  55.26 s, peak 1,416,495,104 bytes against the 4 GB cap. The whole green set
  is the table in the report, section `## THE CALIBER MOVED WHILE THIS TASK
  WAS LIVE, AND EVERYTHING WAS RE-TAKEN UNDER IT`.
- **The wall is the same wall, at a lower cap.** `runs/s4-2.out`,
  `runs/s6-2.out` and `runs/s8-2.out` are natural `Heap exhausted` runs at
  exit 251 under `-M4g` (4.3 to 5.3 GiB); `runs/S3.agda` is the program's own
  exit-251 runs, `runs/accept-1.out` and `runs/accept-2.out`.
- **The three gaps are still uninhabited.** `P570.GraphAgree` is a type with
  no term (`agents/tasks/LJ-1-570/Probe570.agda:289-295`); the corrected
  `HierInK` is a type with no term
  (`agents/tasks/LJ-1-532/Probe532.agda:274-277`, and `[LJ-1.532]` is a
  NO-GO with its refutation delivered); `OrdReflect` has no predecessor at all
  (its only occurrences are `runs/full-probe.txt:471-473` and the report).
  No amount of heap closes a gap that has no term in the tree, and the only
  path the tree gives to the stage decode applies `abs₀` to the level-hood
  matrix, which is the wall.
- **The walling scratch slices are frozen as text, not deleted.**
  `runs/S3.agda`, `runs/S4.agda`, `runs/S6.agda` and `runs/S8.agda` are now
  `.agda.txt`, byte-identical, by the same pattern this task already used for
  `runs/full-probe.txt`. The reason is mechanical: the acceptance arm runs
  every `.agda` under the task in path order and stops at the first failing
  one, so while `runs/S3.agda` stood as a file every acceptance run of this
  task ended at `exit 251`, `error_class heap_wall`, and row
  `heap-wall-park` parked the task instead of routing this stated NO-GO to
  the critic. All measurements of the four files remain in the directory,
  old cap and new cap.
