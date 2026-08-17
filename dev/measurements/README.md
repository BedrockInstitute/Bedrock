# Measurement records

A **measurement record** is the raw output of a timing run, a profile or a
check: the table or the log a live document quotes its numbers from. This
directory holds the records that a LIVE document cites, so the citation
resolves. The rule set is [AGENTS.md](../../AGENTS.md).

Records whose citing documents have all become historical move to
[archive/dev/measurements](../../archive/dev/measurements/README.md).

## Why they are here and not under `_build/`

`_build/` is in `.gitignore` and the `clean:` target deletes everything in it
except `literature/`. `dev/ledger.toml`, the project's canonical size ledger,
cited three of these tables as the provenance of standing figures while they
sat one command from deletion. `[LJ-1.132]` moved them.

## Why a measurement record is not exhaust

A cold profile is not reproducible. Re-running the command measures TODAY's
tree on TODAY's machine and gives different numbers. `[LJ-1.128]` measured
that difference: the identical tree cost 11.2 percent more seconds than its
recorded figure, because the machine moved, not the mathematics. A record of a
tree state that no longer exists cannot be regenerated. It is evidence.

## What is here

| File | The record | Cited by |
|---|---|---|
| `l3.32-coldprofile-2026-08-06.txt` | full per-module cold profile, 124 rows, 1,070.2 s | `dev/ledger.toml:2413,2444` |
| `l3.32-coldprofile-2026-08-09.txt` | full per-module cold profile, 112 rows, 700.42 s | `dev/ledger.toml:1917` |
| `l3.32-t256-belowlim-profile.txt` | per-definition profile of the below-limit master, 546,708 ms | `dev/ledger.toml:2226` |
| `lj-1.128-run2.log` to `-run5.log` | `[LJ-1.128]` main series, runs 2 to 5 | `agents/tasks/LJ-1-128/lj-1.128-report.md:86` |
| `lj-1.128-controlA.log`, `-controlB.log` | `[LJ-1.128]` control runs on the old tree | `agents/tasks/LJ-1-128/lj-1.128-report.md:101-106` |
| `pod-retrieval-scoping-2026-08-17.txt` | the retrieval scoping experiment: gold rank on the full corpus against the archive scope, seven cases | `dev/memos/L9-pod-program-design.md:2615` |
| `pod-retrieval-scoping-2026-08-17.py` | the experiment that produced the line above, frozen. Nothing runs it | the record beside it |

The report tabulates the two control runs but does not name their files, so
the table above is their only index.

## Two citations are stale, and stay stale

A record is frozen and nobody rewrites it.
`agents/tasks/LJ-1-128/lj-1.128-report.md:86` still cites the old `_build/`
path, and the two `pod-retrieval-scoping` records name `dev/POD.md` in their
own headers, which is now `dev/memos/L9-pod-program-design.md`. **Find the file
by its basename, and read the table above for the live pointer.** The
`dev/ledger.toml` citations WERE rewritten, because the ledger is live.

## When a record belongs here

**When a live document cites it and re-running the command would not
reproduce it.** If a future run reproduces it exactly, it is exhaust and
belongs in `_build/`. The lifecycle rule is stated in `_build/README.md`.
