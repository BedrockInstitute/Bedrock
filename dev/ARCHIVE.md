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
- **What this code did right.** Added 2026-08-06 under `[L3.32-F4]`, and the
  only column here that is not about retrieval. A retirement removes files; it
  should not silently remove a PRACTICE. `[L3.32-T86]` measured the retiring
  internalization subtree at **0.013 s/line over 26,483 lines** against a
  surviving trunk at 0.104, and found the cause was not sealing but that these
  chapters state at **abstract carriers and variable indices**, so nothing
  re-normalizes. Nobody knew that until a profile was run, and by then the
  newer chapters had already lost the habit. **So if an archived module did
  something measurably well, record it here in one sentence, with the
  measurement.** Leave it blank rather than filling it with praise: an
  unmeasured compliment in this column is worse than an empty cell, because it
  makes the column unreadable. This is the field the freeze's exit condition
  (D30 part 3) requires filled before the D18 archival lands.
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

| Module | Original path | Why archived (ruling, date) | Last green (commit) | Measured size | What this code did right | Revival condition |
|---|---|---|---|---|---|---|
| `L.Rud.Realize` | `src/L/Rud/Realize.lagda.md` | The realization induction over an abstract basis: for every Delta-0 formula, a realizing basis composite. It served the comprehension switch through the image-principle route. That route was superseded when the switch was discharged unconditionally in `L.Rud.SatSets` (`full-switch-⊇`), after which nothing in the ruled configuration exercised the import edge that kept this chapter alive. Retired under D17 and D20, 2026-08-04, on `[T7]`'s import analysis and `[T11]`'s compile gate. | `d31b196` | 789 code lines | Not yet assessed. `[L3.32-T86]`'s profile covered the internalization subtree, not this chapter; if the basis-neutral statement style is why it was cheap, that belongs here with the number. | If a future development needs realization over an ABSTRACT basis (this chapter's whole point was basis-neutrality, validated by a probe before the rud route was adopted), rather than the concrete sixteen-operation discharge the tree now uses. The fine-structure era's rud-A relativizations are the named candidate. |
| `L.Rud.Switch` (partial, 506 lines cut in place) | `src/L/Rud/Switch.lagda.md`, the Realize-dependent half | Six modules (`Bs`, `Ev`, `Rl`, `Closure` with its nested `Eval-J`, `WalkCon`, `LimitSwitch`) and the notation-and-spec layer consuming Realize's bounded-existential notation. `[T11]` proved by compile gate that the narrow cut (the six modules alone) does NOT compile and the widened cut does, which is why the spec layer travels with them. The surviving chapter is the reverse hops and the description side, which are what the bridge consumes. | `d31b196` | 506 code lines of the chapter's 803; the chapter now stands at 297. The cut regions are not moved to `archive/` as files, since they were interior to a surviving chapter: this commit is their archive, and `git show d31b196:src/L/Rud/Switch.lagda.md` recovers the pre-cut text | Not yet assessed, same reason as the row above. | Same as `L.Rud.Realize`: these are its consumers. Revive together or not at all. |

## Verification record

The gate exclusions were confirmed on 2026-08-04 by a poison-pill test rather
than by reading: a file was placed under `archive/` that violates every gate at
once (no OPTIONS header, an em dash, CJK mixed with half-width punctuation,
and Agda that does not typecheck), and `make check` passed with it in place.
The four scripts skipped it, the Agda gate never reached it, and `reuse lint`
covered it through the carve-out at full compliance. The file was then removed.
Repeat this test whenever a gate or a script's file-discovery changes.
