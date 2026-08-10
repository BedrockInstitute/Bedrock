# Refused kits

A **refused kit** is code that was written, typechecked, measured, and then
NOT landed because its arithmetic did not pay. This directory holds those
kits, so a later task can revive one instead of rebuilding it.

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

## Why the path is flat, and not the original path

[archive/README.md](../README.md) says an archived module keeps its ORIGINAL
path, so provenance is self-evident and `git log --follow` keeps working. A
refused kit has no original path: it never landed in `src/`, and the tree was
reverted to HEAD. There is nothing to preserve provenance of.

So the filename carries the provenance instead: `<task>-<name>`. The task code
resolves in `dev/PLAN.md` section 11 and in `dev/JOURNAL.md`, and the
measurement and the revival trigger for each kit are rows S19 to S22 in
[dev/memos/simplification-register.md](../../dev/memos/simplification-register.md).

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
