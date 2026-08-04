# The archive

`archive/` is the home of Bedrock's retired code. Retired code is archived,
never deleted (ruling D20, `dev/PLAN.md` section 3, 2026-08-04, superseding
D14). This README states the rules that govern the archive in full; the
registry that indexes it is [dev/ARCHIVE.md](../dev/ARCHIVE.md).

## What the namespace is

The archive holds retired modules, each at its ORIGINAL path under `archive/`,
so provenance is self-evident and `git log --follow` keeps working. A module
retired from `src/L/Coding/Sequence.lagda.md` lives at
`archive/src/L/Coding/Sequence.lagda.md`. Nothing else belongs here: no live
code, no probes, no generated files, no half-maintained second tree.

## Outside every gate

The archive sits OUTSIDE `src/`, which makes every exclusion STRUCTURAL rather
than configured:

- the Agda gate is `agda src/Everything.lagda.md` and cannot reach it;
- the include path (`bedrock.agda-lib`) does not contain it;
- the linters, the marker checker and the glossary checker do not scan it;
- the site builds from `src/` and never publishes it.

That is what makes keeping the archive free: it taxes no build and no check,
and D2's claim that the whole checked tree is `--safe` and postulate-free
stays literally true of the tree the gates see.

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
