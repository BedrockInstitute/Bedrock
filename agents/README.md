# agents/

**Everything in this directory is agent-generated.** No human wrote these files. They are the
written record of the dispatches that built Bedrock: what each agent was told, and what it
found.

The directory moved here from `_build/` on 2026-08-13, by the owner's ruling. `_build/` is
git-ignored and `make clean` empties it, so 493 reports and 406 briefs sat one command from
deletion. They are now tracked.

## The layout

| Path | What it holds | Count at the move |
|---|---|---|
| `reports/` | The reports of the current arc, `LJ-1.90` and later | 41 |
| `reports/archive/` | Every earlier report, back to the first dispatch | 452 |
| `briefs/` | Every brief, the instruction each agent was dispatched with | 406 |

The split at `LJ-1.90` is not a date. `[LJ-1.90]` is where the first real consumer landed and
the current arc began.

## These files are frozen records

**Nobody edits a file in this tree.** A brief says what an agent was told on a date. A report
says what it found. Both are evidence, and evidence that gets rewritten is no longer evidence.

Two consequences follow, and both are mechanical:

1. **`scripts/lint-prose.py` skips `agents/`**, beside `archive/`. A style gate over a record
   can only force an edit to the record. The exemption is at `scripts/lint-prose.py:437` with
   its reason. The same reasoning exempts `dev/JOURNAL.md` at `scripts/check-rule-ids.py:83`.
2. **Correct a report in the next report, never in place.** If a report is wrong, the record
   of the error and its correction is worth more than a clean file.

A report may still be cited from anywhere. Evidence is `file:line`, and a citation into this
tree resolves like any other.

## What is NOT here

- **Probes.** A probe is thrown away by doctrine (`dev/LESSONS.md` D-1). Its verdict survives
  in a report here; the probe file never does.
- **Run logs, profiles and scratch data.** These stay in `_build/`, which is where volatile
  build output belongs.
- **The primary sources.** `_build/literature/` holds copyrighted OCR text and PDFs, which
  cannot be committed.

## Licensing

Everything here is CC BY-NC-SA 4.0, declared centrally in `REUSE.toml`. That follows the
owner's three-way split: source is CC, scripts are AGPL, and agent-generated documents are CC.
An agent document is CC from birth, so no later move can relicense it. Never add an in-file
`SPDX-*` header; `REUSE.toml` is the one source of truth.

## Who reads what

- **The orchestrator** writes every brief here before dispatch, and audits every report.
- **A dispatched agent** writes exactly one report here, incrementally, and reads the briefs
  and reports its own brief names.
- **The owner** reads `reports/` to see where the work stands.
