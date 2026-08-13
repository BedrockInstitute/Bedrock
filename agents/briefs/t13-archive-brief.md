# [L3.32-T13] Build the archive infrastructure (D20, unblocks the retirement surgery)
tier: codex (default)

GOAL: D20 rules that retired code is ARCHIVED, never deleted, and that the
infrastructure is created at the FIRST archival, which is this campaign's
retirement surgery. Build it now so the surgery is not blocked on it. Read
`dev/PLAN.md` section 3 row D20 in full first: it is the specification, and
every constraint in it is binding.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `archive/README.md` (new), `dev/ARCHIVE.md` (new),
`REUSE.toml` (one carve-out), `.gitignore` if needed, and whichever of
`Makefile` / `scripts/*.py` implement the gate exclusions. NOTHING under
`src/`. Never `src/Everything.lagda.md`.
SCOPE (read): `dev/PLAN.md` D20 and the `[L7]` rows; `AGENTS.md` (the
retirement section states the same rules contributor-facing, keep them
consistent); `Makefile`; `scripts/README.md` and the linters; `REUSE.toml`.

THE WORK:
1. Create `archive/` with its `README.md`. State in full: what the namespace
   is; that it is outside `src/` so every gate is structurally blind to it;
   that it is NOT required to typecheck and a red archive is not a defect;
   that archived files are FROZEN (a revival copies out, it never edits in
   place); that nothing may import across the boundary in either direction;
   what a reader should expect (code that was correct when written, against
   interfaces that have since moved); and how to revive a module. English
   only, developer doc, no em dash.
2. Create `dev/ARCHIVE.md`, the registry, with its format documented and an
   empty table ready for the first entries. Per-module columns: the module
   and its original path, WHY it was archived (the ruling and its date), the
   commit at which it was last GREEN, its measured size, and the CONDITION
   under which it would be worth consulting again. Include the rule that a
   condition which becomes provably moot may be closed and its files then
   genuinely deleted, recorded here.
3. `REUSE.toml`: add an `archive/**` carve-out that PRESERVES the archived
   content's original license (content moved out of `src/` keeps CC BY-NC-SA;
   moving a file must not relicense it). `reuse lint` must still cover the
   archive: coverage there is free and D20 requires it.
4. The gate exclusions. Verify, and implement only where it is NOT already
   structural: the Agda gate is `agda src/Everything.lagda.md` and cannot
   reach `archive/`; the include path must not contain it (check the
   `.agda-lib`); the linters and the marker and glossary checkers must not
   scan it; the site build must not publish it. For each, say in your report
   whether it was already structural or needed a change, and name the change.
5. Record the convention in `scripts/README.md` in one short paragraph.

CONSTRAINTS: do NOT run `make check` (a sibling agent holds the Agda slot);
verify with the individual checks instead (`python3 scripts/lint-prose.py
<files>`, `reuse lint`, and a dry read of the Makefile targets), and say
exactly what you verified and what you left for the orchestrator. No git
commands. Never touch `.claude/`.

RETURN (final message): the files created, the exclusions that were already
structural versus the ones you implemented, the REUSE carve-out's exact
text, and anything you could not verify without the full gate.
