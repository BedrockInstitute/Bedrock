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
| `reports/<TASK>/` | **The probes of one task**, added 2026-08-13 | 258 files in 118 directories |
| `briefs/` | Every brief, the instruction each agent was dispatched with | 406 |

The split at `LJ-1.90` is not a date. `[LJ-1.90]` is where the first real consumer landed and
the current arc began.

## Probes live here

**A probe pairs one-to-one with its report, lives beside it, is tracked, and is never
deleted.** The owner ruled that on 2026-08-13. `dev/LESSONS.md` **D-1** is the canonical rule
and everything below is how to obey it.

**Write your probe in `agents/reports/<TASK>/`, and nowhere else.**
`agents/reports/LJ-1-141/ProbeLJ1141A.agda` sits beside `agents/reports/lj-1.141-report.md`.
`src/` is forbidden absolutely; `scripts/check-probes.py` refuses a commit that carries a probe
there, and that rule was bought on 2026-08-04 when one `git add -A src/` committed 13 probe
files.

**The directory name is the module qualifier, so declare `module LJ-1-141.ProbeLJ1141A`.**
`bedrock.agda-lib` lists `agents/reports` as an include root, so your probe imports `L.Choice.Step`
exactly as a master does, and you run it where you wrote it. It never moves.

**Write the directory as `LJ-1-141`, not `lj-1.141`.** A directory under an include root must
parse as an Agda name. MEASURED 2026-08-13: `LJ-1-141` works; `lj-1.141`, `LJ-1_141` and
`LJ_1_141` are all `[ParseError]`, because `.` splits the qualifier, `_` splits a mixfix name,
and the trailing digits are then a literal.

**Nothing typechecks your probe once your task closes.** It becomes text, exactly like your
report, and its claim is true of the tree at its date. That is why you run it yourself, while
you still can, and why the verdict still goes in the report.

**Do not name a probe after the module it probes.** Two include roots make a shared module name
an `[AmbiguousTopLevelModuleName]` error.

**The 258 probes moved here on 2026-08-13 keep their old flat module lines**, so
`agda` refuses them with `[ModuleNameDoesntMatchFileName]`. They are frozen records and nothing
typechecks them. `archive/probes/README.md` maps every old path to its new one.

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
