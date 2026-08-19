# AGENTS.md

The one rule set for every agent on Bedrock. Claude Code loads it through the root
`CLAUDE.md`; other agents load it directly.

**This file is deliberately short, and the POD cutover of 2026-08-18 made it shorter.**
It holds four things and nothing else: what the project is, where it stands, the
Boundary every slot shares, and a pointer to your own slot's file. **Your slot's file
carries the rest, and the program puts it in front of your brief at every dispatch.**

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

**HOW THE LOOP IS STARTED, and it is a plain terminal.**

```sh
sh scripts/pod/keeper.sh                          # the keeper, which owns the loop
.venv/bin/python scripts/pod/pod.py tick --plan   # one pass, launching nothing
```

**START THE KEEPER, NOT THE LOOP.** `keeper.sh` runs `pod.py` as a direct child in the
same pane, so this pane's scrollback is the loop's own output. When the loop crashes the
keeper restarts it in place, with a backoff; after three fast failures it stops guessing
and asks the maintainer, then waits for `.pod-state/keeper-retry`. It restarts a CRASH
and never a decision: `pod run` exits 3 on rule (d)'s STOP and 4 on a startup refusal,
and neither is restarted.

**`pod.py` IS A PROGRAM AND NOT AN AGENT.** Do not start it from inside a coding-agent
session in the hope that the session's own model or effort applies: it does not, and
the session would only be a shell. **The program launches all five heads itself**, each
with the model and effort of its row in `dev/pod/heads.toml`, so the maintainer's
`claude-opus-5` at `high` takes effect because `ensure_maintainer()` reads that row and
passes it to the launcher. The same is true of every other slot.

**THE MAINTAINER IS RESIDENT AND OUTLIVES THIS PROGRAM.** Owner's ruling, 2026-08-18.
It is the role that repairs `pod.py`, so it cannot be `pod.py`'s child: the loop's
repairman would die with the loop. Rule (e) ensures it every tick, idempotently, and
feeds it a batch by prompt. It is ONE long-lived session and its pane is never closed.
Liveness runs one way and repair runs the other, and neither is a cycle:

```
you  ->  keeper.sh  ->  pod.py  ->  maintainer        (who is alive)
maintainer  ->  reads the keeper's pane, edits the tree, touches the retry file
```

**THE PANES OPEN AND CLOSE THEMSELVES, so there is nothing to attach.** A dispatch splits
a pane in the keeper's own workspace and starts the head inside it, so a running head is
already in front of you. A clean finish closes that pane; every other ending keeps it,
because a dead agent's terminal is the only record of how it died. **Nothing ever takes
your focus**: the program splits and starts, and never calls `pane focus`.

**THE ONE PANE THAT NEVER CLOSES IS THE MAINTAINER'S**, because it is resident. That is
what makes it reachable at any hour.

```sh
herdr agent list                     # every live head and its pane
herdr agent prompt pod-batch "..."   # send one message without leaving your pane
herdr agent attach pod-batch         # only from ANOTHER workspace; in the pod's own
                                     # workspace the pane is already on your screen
```

**A FINISHED AGENT IS NOT A DEAD ONE.** MEASURED 2026-08-18: after its turn a head
reports `agent_status: done`, and a second `herdr agent prompt` is accepted and answered
on the same session. Only `herdr pane close` ends an agent.

**A PROMPT TO A BUSY HEAD QUEUES AND NEVER INTERRUPTS** (`dev/LESSONS.md` C-61): it is
read when the head finishes its current tool call, and once cost 4.25 hours. To reach a
busy head, end what is keeping it busy first.

**`[LJ-4]` replaced the orchestrator with a program.** The program measures six facts,
matches one rule table, and performs one action. It reads no report and it makes no
judgement. Its design is `dev/memos/LJ-4-pod-program-design.md`.

## Boundary

**These bind every slot. Your own file carries the clauses that bind only you.**

- **Write it generic.** Write the mathematics once at a generic carrier and instantiate
  it, so both proofs share the maximum code. This is the constraint that has cost this
  project most, and it has **no metric by the owner's ruling**, because a shared-line
  count would be gamed the moment it gated anything. **A stop-line is never a reason to
  write fixed:** say so and stop for a re-price.
- **Evidence is `file:line`.** A report that cannot be checked can only be believed.
  Never write a number, a date or a certainty the evidence does not give.
- **A stop is a deliverable.** If the target is false, the price wrong, or the plan
  resting on a bad premise, give the evidence and stop. Refutations gave this project
  its best results.
- **Verify the load-bearing assumption cheaply before heavy work.** Build the smallest
  decisive miniature, report GO or NO-GO with a price, and write it in
  `agents/tasks/<TASK>/`. **`src/` is forbidden for a probe.** Nothing typechecks it
  once your task closes, so run it while you can.
- **A measured cure does not transfer by analogy.** Re-measure it at its own site.
- **A LIVE DOCUMENT CARRIES NO HISTORY. RETRIEVE IT.** A rule that a checker now
  enforces, a goal that closed, a ruling that moved: each belongs in `archive/`, and
  the program searches the archive at brief build. **You do not need to know how the
  project got here to start work**, and a document that makes you read the history
  first is a defect in the document. Owner's ruling, 2026-08-18.
- **Archive a retired MODULE, never delete it.** The rule is module-granular: a dead
  fragment inside a live file is not a module.
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
- **NEVER SET `GHCRTS` YOURSELF.** The program sets the caliber on your pane, one caliber
  per tier, from `dev/pod/heads.toml`: `-A64m -I0 -M8g` wide and `-A64m -I0 -M12g` heavy.
  Start one Agda process and no more. A number you measure under any other caliber is not
  comparable, and you must never report it as a price. A heap exhaustion is a WALL event:
  report it and never simply rerun.

## Your slot

**`dev/pod/instructions/<slot>.md` carries the clauses that bind you**, and the program
puts that file in front of your brief at every dispatch. The five slots are
`mathematician`, `mathematician_adversarial`, `coder`, `coder_adversarial` and
`maintainer`.

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
