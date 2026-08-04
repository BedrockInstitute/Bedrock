# ARCHIVE.md: the archive registry

The registry of Bedrock's retired modules. One entry per module, written at
the moment of archival, recording what went, why, its last-green state, its
measured size, and the condition under which it would be worth consulting
again. The archive itself lives at `archive/` (repository root) and its rules
are stated in full in [archive/README.md](../archive/README.md) and in ruling
D20 ([dev/PLAN.md](../dev/PLAN.md) section 3, 2026-08-04). This file is the
index; the archive is the evidence.

## When an entry is made

An entry is written as part of the same change that moves a module into
`archive/`. It records facts as of that moment: the ruling that retired the
module, the commit at which it was last green, and its measured size.
Pre-regime deletions (made under D14 before D20 superseded it) are entered
against their deletion commits when the final archival sweep runs; git history
is their archive, so no files are restored.

## Columns

- **Module.** The module's name as it was known in the live tree, e.g.
  `L.Coding.Sequence`.
- **Original path.** The path the module held before retirement. The archive
  keeps that path under `archive/`, so the archived path is the original path
  prefixed with `archive/`.
- **Why archived.** The ruling and its date, e.g. `D17 + D20, 2026-08-04`,
  plus one line on what actually retired the module.
- **Last green.** The commit at which the module last passed the full gate
  (`make check`). This is what makes the module usable later: a revival starts
  from a known-green state. For a pre-regime deletion there is no archived
  file, so this column carries the deletion commit.
- **Measured size.** Non-blank lines inside the module's Agda code fences at
  its last-green commit, single caliber. This column is a measurement of the
  file as archived, never a projection; projections carry two calibers and do
  not belong here.
- **Revival condition.** The concrete condition under which this module would
  be worth consulting again. A condition that becomes provably moot may be
  closed, and the module's files may then be genuinely deleted, recorded in
  the entry.

## Closing a revival condition

The archive is an index of evidence, not a landfill. When a revival condition
becomes provably moot, the entry records the closure, with the ruling or
reasoning that made the condition moot, and the module's files may then be
genuinely deleted. A revival that lands is recorded in the entry; the archived
original stays frozen unless and until the condition is closed as moot.

## Entries

| Module | Original path | Why archived (ruling, date) | Last green (commit) | Measured size | Revival condition |
|---|---|---|---|---|---|

## Verification record

The gate exclusions were confirmed on 2026-08-04 by a poison-pill test rather
than by reading: a file was placed under `archive/` that violates every gate at
once (no OPTIONS header, an em dash, CJK mixed with half-width punctuation,
and Agda that does not typecheck), and `make check` passed with it in place.
The four scripts skipped it, the Agda gate never reached it, and `reuse lint`
covered it through the carve-out at full compliance. The file was then removed.
Repeat this test whenever a gate or a script's file-discovery changes.
