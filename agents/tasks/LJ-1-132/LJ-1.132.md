# LJ-1.132: salvage what is left in `_build`

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**Clear the rest of `_build`.** `[LJ-1.130]` moved the reports and the
briefs out. What remains is a decade of run logs, profiles, kits and
one-off artefacts, and nobody has looked at them as a set.

## CWD

`/Users/alsg/Agentic/Bedrock`, branch `two-tower-bridge`, clean at
`5a61a69`. `make check` passes.

## THE OWNER'S INSTRUCTION, in three parts

1. **Delete what is not needed.**
2. **Rehome what is still needed, in a fitting place.**
3. **Put what is worth keeping for future reference into `archive/`.**

**Those are three different verdicts and every file gets exactly one.**

## WHAT `[LJ-1.130]` ALREADY DID, so you do not redo it

- `agents/reports/` holds the 41 live reports; `agents/reports/archive/`
  holds 452 older ones; `agents/briefs/` holds all 406 briefs.
- **20 non-report data files were deliberately LEFT in `_build` by the
  owner's ruling.** Find them, and **treat that ruling as settled for those
  files unless you find one that is plainly dead.** If you propose moving
  one, say why and mark it a PROPOSAL for the owner rather than doing it.

## WHAT IS THERE, measured before you started

`_build` is **183 MB**. **163 MB of that is `_build/2.8.0/`, the Agda
interface store. DO NOT TOUCH IT.** It is rebuilt by the toolchain and
deleting it costs a twelve minute cold build.

The rest is roughly: `kits/`, `literature/`, `probes/`, `probe3/`, cold
profiles and run logs as `.txt`, a `dashboard.html`, and stray artefacts.
**Inventory it yourself; that list is from a glance.**

## HOW TO DECIDE, and the project has rules for this

**A file is worth keeping when a document cites it, or when it is the only
evidence for a measurement that a rule now rests on.** This project's whole
discipline is that a claim is checkable at `file:line`.

**So the decisive test is: does anything cite it?**

```
grep -ro "_build/[a-zA-Z0-9._/-]*" dev/ agents/ scripts/ | sort -u
```

- **CITED and still needed** for a live rule, a live PLAN row, or a live
  LESSONS provenance line: **rehome it and rewrite the citation.**
- **CITED but the citing document is historical** (`dev/memos/`,
  `agents/reports/archive/`, `dev/JOURNAL.md`): **archive it** so the
  citation still resolves.
- **NOT CITED and reproducible** by re-running a command: **delete.** A cold
  profile that any future run can reproduce is not evidence, it is exhaust.
- **NOT CITED and NOT reproducible**, for example a measurement of a tree
  state that no longer exists: **archive it.** That is exactly what
  `archive/` is for.

**When in doubt, archive. `AGENTS.md`: archive, never delete.** A wrong
deletion is unrecoverable; a wrong archive costs disk.

## THE SECOND DELIVERABLE: A LIFECYCLE REGIME, and it is why this happened

**The owner's ruling, 2026-08-13:** `_build` must not be a temporary folder
and a rubbish bin. **Every temporary file declares its lifecycle when it is
created**: under what condition it may be deleted, and under what condition
it moves somewhere permanent.

**That is the real fix. The salvage is only the backlog.** A cleanup with no
regime refills in a month.

**Design it from what you actually find, not from first principles.** You are
about to inventory every file in there. **Let the classes fall out of the
inventory**, then write them down. The orchestrator's guess at the classes,
which you may replace:

- **exhaust**: reproducible by re-running a command. Deletable at any time.
- **evidence**: the only record of a measurement a rule now rests on. Never
  deleted; moves to `archive/` when its citing document becomes historical.
- **working**: alive only while one task runs. Deletable when that task's
  report lands.
- **toolchain**: `_build/2.8.0/`. Owned by the toolchain, never touched by
  hand.

**Then give the regime an enforcement point.** `AGENTS.md` is explicit: a
rule that no machine enforces must name its enforcement point, and a rule
with no enforcement point is a wish.

**The orchestrator's proposal, which you may overrule with a reason:** a
manifest at `_build/MANIFEST.toml` mapping path globs to a class and an
expiry condition, plus a checker that lists any file in `_build` matching no
entry. **Advisory, not a gate**, because the checker cannot know intent and
`AGENTS.md` warns that a rule claiming more than its checker delivers becomes
false safety.

**Write the regime into `_build/README.md`**, and say in your report where
else it must be stated so that a dispatched agent meets it: a brief section,
`dev/ORCHESTRATION.md`, or both. **Do not edit `AGENTS.md`; propose the line
and let the owner rule.**

**And apply it to yourself:** your own report goes to `agents/reports/`, and
anything you leave in `_build` must have a manifest entry.

## WHERE THINGS GO

- **Live evidence a rule rests on**: propose a home under `dev/` or
  `agents/`, and say why. **Ask before inventing a new top-level directory**:
  that needs the owner's word.
- **Historical evidence**: `archive/`, mirroring the shape already there
  (`archive/dev/` holds the retired records).
- **`_build/literature/`**: check whether `dev/literature/` cites it. The
  digested literature is tracked; the raw fetches may not be. **Say which is
  which before you move anything.**

## LICENSING, and it is already settled

`REUSE.toml` declares `path = "**"` as AGPL by default, with CC-BY-NC-SA for
`src/`, `docs/`, `agents/`, `dev/` and `archive/`. **A file moved into
`archive/` inherits CC; one moved into `dev/` or `agents/` inherits CC; one
left at top level inherits AGPL.** Check with `reuse spdx` on a sample after
you move, **not by reading the config**, and report the file count from
`reuse lint`.

## THE ABORT CRITERION

- **The inventory is complete and every file has a verdict**: report the
  three counts and STOP.
- **A file's verdict is genuinely unclear**: **leave it, list it, and say
  what would decide it.** An honest undecided list is better than a wrong
  deletion.
- **Anything walls**: STOP, report it.

## WHAT YOU MUST NOT DO

- **Do not touch `_build/2.8.0/`.**
- **Do not delete anything that any tracked document cites.**
- Do not touch anything under `src/`.
- Do not edit `AGENTS.md`. DD19.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; I run it. Do not run Agda.
- **Do not write a probe as `.lagda.md`.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** "Nothing cites this" is MEASURED
only if you ran the grep and say so.

## ARCHIVE (DD18)

- `agents/reports/lj-1.130-report.md`, read WHOLE. **The move that came
  before you, and its measured surprises.**
- `archive/README.md` and `dev/ARCHIVE.md`, for what an archival record must
  carry.
- `REUSE.toml`, read whole.
- `dev/LESSONS.md` **D-1** on probes being throwaway, and **C-22**.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs a build directory. Say so in one line.**
**But `_build/literature/` may hold raw fetched sources**, and
`dev/literature/BIBLIOGRAPHY.md` records what was fetched and what consumed
it. **Read that before you judge anything under `_build/literature/`.**

## SCOPE (read)

`_build/` whole, then the citation grep, then `dev/literature/BIBLIOGRAPHY.md`.

## SCOPE (write)

`_build/`, `archive/`, and wherever you rehome a file. Your report is
`agents/reports/lj-1.132-report.md`.

## MANDATORY RULES

Run `python3 scripts/rules.py --for rewrite` and read every statement.

- **D-1.** A probe is throwaway by doctrine. **A probe under `_build` is
  exhaust unless a report cites it.**
- **C-22.** Write the deliverable incrementally.
- **C-36.** Write the term you could not write, which here is: name any file
  you could not classify.
- **C-39, C-40, D-10, D-26, D-29, D-30.**
- **P-l.** A price from a comparable elsewhere is a hypothesis.
- **C-31, C-32, C-33, C-34, C-37.**

## CONSTRAINTS

- Run `scripts/lint-prose.py --check` on anything you write.
- Evidence is `file:line`. Write ASD-STE100.
- **Report sizes before and after.**

## RETURN

**Lead with the three counts: deleted, rehomed, archived**, and the size of
`_build` before and after, excluding `2.8.0/`. Then the table: file or
group, verdict, and the reason. Then anything you could not classify. Then
`reuse lint`'s count.

**Then the lifecycle regime**: the classes you settled on, why they came from
the inventory rather than from theory, the manifest's shape, the checker's
honest limits, and where the regime must be stated so a dispatched agent
meets it. **Then the `AGENTS.md` line you propose, for the owner's ruling.**

**Mark every negative MEASURED or INFERRED.**
