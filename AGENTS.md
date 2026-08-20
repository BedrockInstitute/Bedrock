# AGENTS.md

Shared rules for every slot. Slot-only clauses live in the file before this one.
Loop operation lives in `dev/pod/README.md`. Neither is here.

## Boundary

- **Evidence is `file:line`.** A report that cannot be checked can only be believed.
  Never write a number, a date or a certainty the evidence does not give.
- **A stop is a deliverable.** If the target is false, the price wrong, or the plan
  rests on a bad premise, give the evidence and stop.
- **A measured cure does not transfer by analogy.** Re-measure it at its own site.
- **A live document carries no history.** A closed rule, a closed goal, a moved
  ruling: each belongs in `archive/`. The program searches the archive at brief
  build. A document that makes you read the history first is a defect.
- **Never** commit a generated file; use an em dash in any language; use half-width
  sentence punctuation in CJK prose; commit or print a secret; add an unpinned or
  globally installed dependency; or add an in-file `SPDX-*` header.
- **Each rule has one canonical home, and the home names its enforcer**: the
  program, a hook, or agent discipline. Never write one rule in two files.
  **Never add a `dev/glossary.toml` entry you chose yourself.** A missing term is
  settled by two dispatches: a sourced provenance dossier, then a PASS or FAIL
  review. PASS lands the entry; FAIL goes to the owner.
- **Place a new document by audience.** A user document is trilingual under
  `docs/<lang>/`. A developer document is English only and is never translated. A
  `README.md` follows the user rule, and a new top-level directory carries one in
  the same commit that creates it.
- **Author in English first**, then translate, then cross-check the Chinese and
  the Japanese against each other for drift.
- **Write a controlled style, and the audience picks it.** To the repository
  owner: Chinese, in the Chinese Tech Doc Style. To everyone else, including
  every brief and every report: ASD-STE100 Simplified Technical English. The two
  skills carry the full rule sets and **Bedrock's own prose rules win over both**.
  Neither applies to mathematical prose, to `docs/`, or to the prose in a
  `.lagda.md` master.
- **Write no mathematical prose until both trophies are proved in the tree.**
  Write only code, the comments inside it, and the project records.
- **Every file you create under `_build/` declares its lifecycle** in
  `dev/build-manifest.toml`.
- **A one-off instruction from the owner binds only the task it names.** It
  changes no ruling, and it is not evidence about what any other agent may do.
- **`make check` is the gate before any commit.** While you work, run the
  individual checks.
- **Never commit and never push.** Leave the working tree exactly as your report
  describes it. **The program commits**, by explicit path from the task's scope.
  It never runs `git add -A` and never pushes (rule R8). One push is one CI run
  and one deploy: the owner's call.

## What Bedrock is

Bedrock proves two theorems in Cubical Agda, both inside the constructible
universe `L`: **`L ⊨ AC`** and **`L ⊨ GCH`**, with a two-directional bridge.
The proofs are literate `.lagda.md` masters under `src/`.

**The endpoint is RULED. The architecture is a CANDIDATE.** The two towers and
the bridge are settled only by a measurement, at `[LJ-2.5]`. A brief says which
is which.

Requirements: Agda 2.8.0 with cubical 0.9, and Python 3.11 or later.
[requirements-dev.txt](requirements-dev.txt) pins every dependency.
**Run every `python3` command as `.venv/bin/python`.**

## The milestone

**`[LJ-1]` is the live campaign.** `dev/pod/screen.toml` is the only standing
status. `dev/pod/queue.toml` is the task producer.

**`ledger.py --brief` is the only admissible source for a standing size figure.**
Never quote a number found in a paragraph.

**`dev/pod/direction.md` is guidance, never a rule.** When it and an older
document disagree about where the work is going, the direction wins and you say
so in your return. When it and a Boundary clause disagree, stop and report.

| Need | Home |
|---|---|
| Measured laws that bind new code | `dev/LESSONS.md` |
| Rulings, numbered and dated | `dev/pod/rulings.toml` |
| Agda code and chapter style | `dev/STYLE-agda.md` |
| Literate Agda, i18n markers, prose rules | `dev/STYLE-i18n.md` |
| Translation terms | `dev/glossary.toml`, `dev/GLOSSARY.md` |
| Size ledger | `dev/ledger.toml` |
| Briefs, reports and probes | `agents/README.md` |
| The program | `dev/memos/LJ-4-pod-program-design.md` |
| How the loop is operated | `dev/pod/README.md` |
