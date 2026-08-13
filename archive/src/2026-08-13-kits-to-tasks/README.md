# The 2026-08-13 kit move: a tombstone

**THE OLD PATH OF THIS FILE WAS `archive/kits/README.md`.** That directory is
retired. It held five refused kits from 2026-08-10 to 2026-08-13 and holds
nothing now.

**Why the record sits under `archive/src/`.** A kit is candidate `src/` content
that was built, measured and refused, and the tree was reverted. Two of the
five name their target master in their own first lines. So the kits were
`src/`-bound, the archive's mirror rule puts their record with the other `src/`
archivals, and the directory name says which archival it was.

**NOTHING ARRIVES HERE AGAIN.** This file records where the five kits went.

A **refused kit** is code that was written, typechecked, measured, and then
NOT landed because its arithmetic did not pay. This directory holds those
kits, so a later task can revive one instead of rebuilding it.

## The second kind: a written chapter that never landed

`[LJ-1.132]` added `l3.32-t28-CodeSetBlock.lagda.md`, and it is not a refused
kit. It is `[L3.32-T28]`'s template for the arity-one code set: a full
trilingual chapter, prose and code, that states the successor obligation
precisely. It never landed, and later tasks re-typed toward its shape rather
than reviving it (`agents/reports/archive/l3.32-t34-report.md:195` calls it
"the target shape the surviving chain re-types toward").

So this directory holds two kinds, and one rule covers both: **code or prose
that was written and measured, and then not landed.** The naming and the
freezing rules below apply to both. A template carries no arithmetic, so it
has no register row and nothing to re-price; read it as a specification, not
as a candidate to land.

## Why they are here and not under `_build/`

`[LJ-0.4]` preserved four kits under `_build/kits/`, and `dev/LESSONS.md`
C-30's ninth gate said to put them there. **That was wrong and the closeout
caught it.** `_build/` is in `.gitignore` and `make clean` runs `rm -rf
_build`, so a kit "preserved" there is one command from gone. It is the fate
that already befell blocks E and G, whose `Walk` and `Lex` kits were deleted
and now survive only as prose.

An artifact a routine command destroys is not preserved. So refused kits live
in the archive, which exists precisely because retired code is archived and
never deleted (ruling D20).

## WHERE THEY WENT, 2026-08-13, and why the old reasoning was stale

**The five kits now live in their own task directories** under
`agents/tasks/archive/`, beside the brief and the report that produced them.
This file is the index.

| kit | now at |
|---|---|
| `l3.32-t28-CodeSetBlock.lagda.md` | `agents/tasks/archive/L3-32-T28/` |
| `lj-0.4b-Frame.lagda.md` | `agents/tasks/archive/LJ-0-4B/` |
| `lj-0.4f-recassembly.lagda.md` | `agents/tasks/archive/LJ-0-4F/` |
| `lj-0.4f-hierarchy-wiring.diff` | `agents/tasks/archive/LJ-0-4F/` |
| `lj-0.4i-placeBin.lagda.md` | `agents/tasks/archive/LJ-0-4I/` |

**This file used to argue that a refused kit has NO original path, because it
never landed in `src/` and the tree was reverted.** `[LJ-1.143]` read that and
left the directory unmoved when the owner ruled that `archive/` mirrors the
repository root.

**The owner refused the argument the same day, and the argument was stale
rather than wrong when written.** It was written when a kit had two possible
homes, `src/` and `archive/`. **`agents/tasks/` did not exist until
2026-08-13.** A kit is an artifact of ONE task, exactly as a probe and a report
are, and every one of these five carries its task code in its own filename.

**Two of them name an original path in their own first lines**, which the
argument also missed: `lj-0.4i-placeBin.lagda.md` says the helper was built for
`src/FOL/Manipulation/Parameters.lagda.md`, and
`lj-0.4f-hierarchy-wiring.diff` opens with
`diff --git a/src/L/Hierarchy.lagda.md`.

**The lesson is not about kits.** A rule keeps being applied after the world it
described has changed, and nothing notices, because the rule still reads true.
`dev/LESSONS.md` C-32 is the same shape.

## The same archive rules apply

- **Frozen.** Never edited in place. A revival copies a kit OUT and works on
  the copy.
- **Not required to be green.** These were measured against a tree that has
  moved. A kit that no longer typechecks is not a defect here.
- **Outside every gate**, structurally, because `archive/` is outside `src/`.

## Do not revive one without re-pricing it

Every kit here was refused on a MEASUREMENT, and the measurement is in its
register row. `dev/LESSONS.md` **D-28** is why: a kit's break-even is set by
its PARAMETER count, not its line count. `[LJ-0.4f]`'s kit is the worked case.
It was refused at eleven parameters over two sites, and its shape half then
shipped as `RecShape` at ONE parameter over five sites for minus 104. **Revive
the low-parameter part, or re-split before reviving anything.**
