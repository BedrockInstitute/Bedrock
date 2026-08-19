# AGENTS.md

The one rule set for every agent on Bedrock. Claude Code loads it through the root
`CLAUDE.md`; other agents load it directly.

**THIS FILE HOLDS ONLY WHAT ALL FIVE SLOTS SHARE.** Owner's ruling, 2026-08-19. It is
`cat`ed ahead of every brief for every slot, so a sentence here is paid for five times
and is read by a coder who needs to write Agda and by a mathematician who needs to think.
**A rule that binds one slot belongs in that slot's file, and a fact about operating the
loop belongs in `dev/pod/README.md`.** Neither is here.

It holds four things: what the project is, where it stands, the Boundary every slot
shares, and a pointer to your own slot's file.

## What Bedrock is

Bedrock proves two theorems in Cubical Agda and states both inside the constructible
universe `L`: **`L ⊨ AC`** and **`L ⊨ GCH`**, with a two-directional bridge between the
towers. The proofs are literate `.lagda.md` masters under `src/`, which are the single
source of both the mathematics and its prose.

**The endpoint is RULED. The architecture is a CANDIDATE.** The two towers and the
bridge are settled only by a measurement, at `[LJ-2.5]`. A brief says which is which,
because an agent told the architecture is ruled will not report evidence against it.

Requirements: Agda 2.8.0 with cubical 0.9, and Python 3.11 or later.
[requirements-dev.txt](requirements-dev.txt) pins every dependency and `make venv`
installs them into `.venv`. **Run every `python3` command as `.venv/bin/python`.**

## The milestone

**`[LJ-1]` is the live campaign and `dev/PLAN.md` section 0 is the screen.** Read it
first: it states where the work stands today in one screen, and it is the only place
that does. Section 11 is the goal registry, and `dev/pod/queue.toml` is the task
producer.

**`ledger.py --brief` is the only admissible source for a standing size figure.** Never
quote a number found in a paragraph.

**`dev/pod/direction.md` CARRIES THE OWNER'S CURRENT MATHEMATICAL DIRECTION, and it is
in front of you now.** The program `cat`s it into every dispatch, for every slot, so it
is the freshest thing you were told and it may have been written this hour. It holds
guidance and never a rule. When it and an older document disagree about WHERE the work
is going, the direction wins and you say so in your return; when it and a Boundary
clause disagree, stop and report, because a direction cannot repeal a rule.

## Boundary

**These bind every slot, including the maintainer.** Your own file carries the clauses
that bind only you, and it is in front of you too.

- **Evidence is `file:line`.** A report that cannot be checked can only be believed.
  Never write a number, a date or a certainty the evidence does not give.
- **A stop is a deliverable.** If the target is false, the price wrong, or the plan
  resting on a bad premise, give the evidence and stop. Refutations gave this project
  its best results.
- **A measured cure does not transfer by analogy.** Re-measure it at its own site.
- **A LIVE DOCUMENT CARRIES NO HISTORY. RETRIEVE IT.** A rule that a checker now
  enforces, a goal that closed, a ruling that moved: each belongs in `archive/`, and
  the program searches the archive at brief build. **You do not need to know how the
  project got here to start work**, and a document that makes you read the history
  first is a defect in the document. Owner's ruling, 2026-08-18.
- **Never** commit a generated file; use an em dash in any language; use half-width
  sentence punctuation in CJK prose; commit or print a secret; add an unpinned or
  globally installed dependency; or add an in-file `SPDX-*` header.
- **Each rule has ONE canonical home, and the home names its enforcer**: the program, a
  hook, or agent discipline. Never write one rule in two files. **Never add a
  `dev/glossary.toml` entry that you chose yourself.** A term the glossary lacks is
  settled by two dispatches. The first writes a sourced provenance dossier, and the
  second reviews it and returns PASS or FAIL for each term. A PASS lands the entry, and a
  FAIL goes to the repository owner.
- **Place a new document by AUDIENCE.** A user document is trilingual under
  `docs/<lang>/`. A developer document is English only and is never translated. A
  `README.md` follows the user rule, and a new top-level directory carries one in the
  same commit that creates it.
- **Author in English first**, then translate, then cross-check the Chinese and the
  Japanese against each other for drift.
- **Write a controlled style, and the AUDIENCE picks it.** To the repository owner:
  Chinese, in the Chinese Tech Doc Style. To everyone else, including every brief and
  every report: ASD-STE100 Simplified Technical English. The two skills carry the full
  rule sets and **Bedrock's own prose rules win over both**. Neither applies to
  mathematical prose, to `docs/`, or to the prose in a `.lagda.md` master.
- **Write no mathematical prose until both trophies are proved in the tree.** Write only
  code, the comments inside it, and the project records. The prose phase opens on the day
  the double trophy lands.
- **Every file you create under `_build/` declares its lifecycle** in
  `dev/build-manifest.toml`. It is a temporary folder, not a rubbish bin.
- **A one-off instruction from the owner binds ONLY the task it names.** It changes no
  ruling, and it is not evidence about what any other agent may do.
- **`make check` is the gate before any commit**, and it runs in the background: a cold
  typecheck takes about twelve minutes. While you work, run the individual checks.
- **NEVER COMMIT AND NEVER PUSH.** Leave the working tree exactly as your report
  describes it. **The program commits**, by explicit path derived from your task's own
  scope, and it never runs `git add -A` and never pushes (rule R8). A commit you make
  yourself sweeps whatever else is in the tree, including another task's half-written
  file. **One push is one CI run and one deploy**, and that is the repository owner's
  call and nobody else's.

## Your slot

**`dev/pod/instructions/<slot>.md` carries the clauses that bind you**, and the program
puts that file in front of your brief at every dispatch. The five slots are
`mathematician`, `mathematician_adversarial`, `coder`, `coder_adversarial` and
`maintainer`.

**THE TWO ROLES THAT DO THE WORK ARE JOINED BY THE BRIEF AND THE REPORT.** Amendment
A21, ruled 2026-08-19. **The mathematician writes no Agda**, deliverable or probe: it
reads the coder's report, its code and its probes, and it writes briefs. **The coder
writes the Agda** the brief names. That channel is the centre of this design, and your
own file states your half of it.

**NEITHER FILE COPIES THE OTHER.** This file holds the shared Boundary, your slot file
holds only what binds your slot, and the program `cat`s the two ahead of your brief at
dispatch. So one Boundary cannot become five that drift, and there is nothing to
regenerate: edit this file and every slot has the new clause at the next dispatch.

| What else you may need | Where it lives |
|---|---|
| The measured laws that bind new code | `dev/LESSONS.md` |
| The project's rulings, numbered and dated | `dev/PLAN.md` section 3 |
| Agda code and chapter style | `dev/STYLE-agda.md` |
| Literate Agda, the i18n markers, the prose rules | `dev/STYLE-i18n.md` |
| Translation terms | `dev/glossary.toml`, explained by `dev/GLOSSARY.md` |
| The size ledger | `dev/ledger.toml` |
| Briefs, reports and probes, one directory per task | `agents/README.md` |
| The program that runs all of this | `dev/memos/LJ-4-pod-program-design.md` |
| How the loop is operated, and it is not your job | `dev/pod/README.md` |
