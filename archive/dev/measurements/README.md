# Archived measurement records

A **measurement record** is the raw output of a timing run, a profile or a
check: the table or the log that a report quoted its numbers from. This
directory holds the records whose only citing documents are historical, so the
citation still resolves.

Live records, cited by `dev/ledger.toml` or another live document, live in
[dev/measurements](../../../dev/measurements/README.md). A record moves here when
every document that cites it has become historical.

## Why they are not under `_build/`

`_build/` is in `.gitignore` and `Makefile:180` runs
`find _build -mindepth 1 -maxdepth 1 ! -name literature -exec rm -rf {} +`.
A record kept there is one command from gone. `archive/kits/README.md` records
the same finding for refused kits: an artifact a routine command destroys is
not preserved.

## Why a measurement record is not exhaust

A cold profile is not reproducible. Re-running the command measures TODAY's
tree on TODAY's machine, and gives different numbers. `[LJ-1.128]` measured
that difference directly: the identical tree cost 11.2 percent more seconds
than its recorded figure, because the machine moved. A record of a tree state
that no longer exists cannot be regenerated, so it is evidence, not exhaust.

## What is here

| File | The record | Cited by |
|---|---|---|
| `t129-baseline.log` | `[L3.32-T129]` baseline check | `agents/tasks/archive/L3-32-T129/l3.32-t129-report.md` |
| `t132-check.log` | `[L3.32-T132]` check log | `agents/tasks/archive/L3-32-T132/l3.32-t132-report.md`, `l3.32-t139-report.md` |
| `l3.32-t242-profile.txt` | `[L3.32-T242]` profile | `agents/tasks/archive/L3-32-T242/l3.32-t242-report.md` |
| `l3.32-t242-run3.txt` | `[L3.32-T242]` run 3 | same |
| `l3.32-t242-t222-profile.txt` | `[L3.32-T242]` profile over `[T222]` | same |
| `l3.32-t242b-run1.txt` | `[L3.32-T242b]` run 1 | same |
| `l3.32-t242b-run2.txt` | `[L3.32-T242b]` run 2 | same |
| `l3.32-t242b-run3.txt` | `[L3.32-T242b]` run 3 | same |

## The paths in the citing documents are stale, and stay stale

Every citing document above is a frozen record. A brief and a report are never
rewritten; they are corrected in the next one. So each cites the old
`_build/` path. **Find the file by its basename**, which is unique in this
directory. The move is recorded in `agents/tasks/LJ-1-132/lj-1.132-report.md`.

## The same archive rules apply

- **Frozen.** Never edited in place.
- **Not required to be green.** These measure trees that have moved.
- **Outside every gate**, structurally, because `archive/` is outside `src/`.
