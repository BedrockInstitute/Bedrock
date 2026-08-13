# Measurement records

A **measurement record** is the raw output of a timing run, a profile or a
check: the table or the log a live document quotes its numbers from. This
directory holds the records that a LIVE document cites, so the citation
resolves.

Records whose citing documents have all become historical move to
[archive/dev/measurements](../../archive/dev/measurements/README.md).

## Why they are here and not under `_build/`

`_build/` is in `.gitignore` and `Makefile:180` deletes everything in it
except `literature/`. `dev/ledger.toml`, the project's canonical size ledger,
cited three of these tables as the provenance of standing figures while they
sat one command from deletion. `[LJ-1.132]` moved them.

`archive/src/2026-08-13-kits-to-tasks/README.md` records the same finding for refused kits: an
artifact a routine command destroys is not preserved.

## Why a measurement record is not exhaust

A cold profile is not reproducible. Re-running the command measures TODAY's
tree on TODAY's machine and gives different numbers. `[LJ-1.128]` measured
that difference: the identical tree cost 11.2 percent more seconds than its
recorded figure, because the machine moved, not the mathematics. A record of a
tree state that no longer exists cannot be regenerated. It is evidence.

## What is here

| File | The record | Cited by |
|---|---|---|
| `l3.32-coldprofile-2026-08-06.txt` | full per-module cold profile, 124 rows, 1,070.2 s | `dev/ledger.toml:2320,2351` |
| `l3.32-coldprofile-2026-08-09.txt` | full per-module cold profile, 112 rows, 700.42 s | `dev/ledger.toml:1824` |
| `l3.32-t256-belowlim-profile.txt` | per-definition profile of the below-limit master, 546,708 ms | `dev/ledger.toml:2133` |
| `lj-1.128-run2.log` to `-run5.log` | `[LJ-1.128]` main series, runs 2 to 5 | `agents/tasks/LJ-1-128/lj-1.128-report.md:86` |
| `lj-1.128-controlA.log`, `-controlB.log` | `[LJ-1.128]` control runs on the old tree | `agents/tasks/LJ-1-128/lj-1.128-report.md:101-106` |

The two control logs are the raw evidence for that report's headline finding
and are kept with the series they are compared against. The report tabulates
their numbers but does not name the files.

## The citation in `lj-1.128-report.md` is stale, and stays stale

A brief and a report are frozen records; they are corrected in the next one,
never rewritten. `agents/tasks/LJ-1-128/lj-1.128-report.md:86` still cites the old
`_build/` path. **Find the file by its basename.** The three `dev/ledger.toml`
citations WERE rewritten, because the ledger is a live document.

## When a record belongs here

**When a live document cites it and re-running the command would not
reproduce it.** If a future run reproduces it exactly, it is exhaust and
belongs in `_build/`. The lifecycle rule is stated in `_build/README.md`.
