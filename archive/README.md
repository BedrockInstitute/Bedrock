# The archive

`archive/` is the home of Bedrock's retired code. Retired code is archived,
never deleted: archived D20 of 2026-08-04, in
`archive/dev/DECISIONS-archived.md`, supersedes archived D14, and the live home
of the rule is DD13 in `dev/PLAN.md` section 3. This README states the archive
rules in full, [dev/ARCHIVE.md](../dev/ARCHIVE.md) is the registry that indexes
it, and the rule set is [AGENTS.md](../AGENTS.md).

## What the namespace is

**`archive/` MIRRORS THE ROOT.** An archived thing sits at the same path under
`archive/` that it had under the repository root. Something archived from
`dev/measurements/` goes to `archive/dev/measurements/`. Something archived
from `scripts/` goes to `archive/scripts/`. Provenance is then self-evident and
`git log --follow` keeps working. **The owner ruled this on 2026-08-13**, and
the reason is drift: a flat bucket with no structural rule fills up, and then
nobody can tell where anything came from.

**ONE ROOT PATH CAN BE ARCHIVED MORE THAN ONCE, so `archive/src/` adds one
level: the ARCHIVAL EVENT.** `src/` has been archived six times. Each archival
gets a directory named `<date>-<slug>`, and the slug comes from that archival's
own commit subject. Inside the event directory the path mirrors `src/` exactly.
So `L/Godel/Closure.lagda.md`, archived on 2026-08-07, lives at
`archive/src/2026-08-07-arm-a/L/Godel/Closure.lagda.md`.

| Event directory | Archival commit | Files | What went |
|---|---|---:|---|
| `2026-08-05-realize-cone` | `93bf246`, `[L3.32-T29]` | 1 | `L.Rud.Realize` |
| `2026-08-06-four-dead-modules` | `e33a4ce`, `[L3.32-F6.0]` | 4 | `BaseBlock`, `CodePred`, `CodeSet`, `OpGraph` |
| `2026-08-07-arm-a` | `b06822e`, `[L3.32-F]` | 16 | the `L.Godel` cone, `StepInL`, `WellOrder.Tree` |
| `2026-08-08-describe-switch` | `9b15509`, `[L3.32-F]` | 2 | `L.Rud.Describe`, `L.Rud.Switch` |
| `2026-08-09-hf-finite` | `43ca411`, `[L3.32-F]` | 2 | `L.Rud.HF`, `L.Rud.Finite` |
| `2026-08-09-rud-route` | `86c7b66`, `[L3.32-F]` | 74 | the whole retired route's `src/`, plus its patch and its README |
| `2026-08-13-probe-sweep` | `[LJ-1.141]`, `[LJ-1.143]` | 1 | **empty of code.** The tombstone only |
| `2026-08-13-kits-to-tasks` | `1044c8a`, `[LJ-1.143]` | 1 | **empty of code.** The tombstone only |

**WHY THE EVENT LEVEL EXISTS, and it is not decoration.** Two archivals both
took files out of `src/L/Rud/` and `src/L/WellOrder/`. A flat merge would put
them in one directory and lose which archival each came from, which is the
exact fact the owner asked the layout to keep.

**PROBES ARE NO LONGER HERE.** `archive/probes/` held 257 of them for one day.
The owner ruled on 2026-08-13 that a probe pairs one-to-one with its report and
lives beside it, so all 257 moved to `agents/tasks/<TASK>/` and nothing arrives
here again. `archive/src/2026-08-13-probe-sweep/README.md` is the tombstone and
maps the old path to the current one; `dev/LESSONS.md` **D-1** is the live rule,
and `scripts/gate/check-probes.py` still refuses a probe under `src/`
absolutely.

**EVERY DIRECTORY MIRRORS THE ROOT.** `archive/kits/` was the one exception and
it is retired: a refused kit has no original path to mirror. `[LJ-1.143]` moved
the five kits into their own directories under `agents/tasks/archive/`, and
`archive/src/2026-08-13-kits-to-tasks/README.md` is the tombstone. MEASURED
2026-08-17: `archive/` holds `dev`, `scripts`, `src` and this file, nothing else.

## Outside every gate

The archive sits OUTSIDE `src/`, which makes every exclusion STRUCTURAL rather
than configured:

- the Agda gate is `agda src/Everything.lagda.md` and cannot reach it;
- the include path (`bedrock.agda-lib`) does not contain it;
- the linters, the marker checker and the glossary checker do not scan it;
- the site builds from `src/` and never publishes it.

That is what makes keeping the archive free: it taxes no build and no check,
and archived D2's claim that the whole checked tree is `--safe` and
postulate-free stays literally true of the tree the gates see.

## Not required to be green

The archive is NOT required to typecheck and NOT required to be green. A red
archive is not a defect. Archived modules keep their original imports even
where those imports no longer resolve, and they may contain constructs the
live tree forbids (postulates, `TERMINATING`, prose that no longer passes the
linters). Nothing in the archive is a current claim about the current tree.

## Frozen

Archived files are FROZEN. They are never edited in place, not even to fix a
typo or an import. A revival copies a module OUT of the archive and works on
the copy; the archived original stays exactly as it was retired. This is what
keeps the archive from rotting into a half-maintained second tree.

## The boundary

Nothing may import across the boundary in either direction. No live module
imports an archived module, and no archived module is relied on by live code.
The archive is on no include path and `src/` never references it.

## What a reader should expect

Archived code was correct when written, against the interfaces that existed at
its retirement date. The tree has since moved: names have changed, modules have
been re-cut, and current interfaces are different. An archived module is a
record of a route that was tried and priced, not a current source. Its prose
and comments describe the tree as it was, and they are stale in exactly the
ways retirement implies.

## How to revive a module

1. Copy the module out of `archive/` into its new home under `src/`. Never
   edit the archived original.
2. Wire it into the reading catalog (the orchestrator owns
   `src/Everything.lagda.md`).
3. Repair it against the current interfaces and treat it as new code: read the
   relevant `dev/LESSONS.md` entries, meet `dev/STYLE-agda.md`, and carry the
   goal code of the work that revives it.
4. Update `dev/ARCHIVE.md`: record the revival there; a revival condition that
   becomes provably moot is closed in the registry, and the files may then be
   genuinely deleted.

## Licensing

Moving a file does not relicense it. Retired content keeps its original
license, CC BY-NC-SA 4.0, through the `archive/**` carve-out in
`REUSE.toml`; `reuse lint` continues to cover the archive because REUSE is a
repository-wide scan and coverage there is free.
