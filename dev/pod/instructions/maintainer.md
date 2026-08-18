# Standing instruction: `maintainer`

**The block below is GENERATED from `AGENTS.md` by `scripts/pod/instructions.py`. Do not edit it here.** Edit `AGENTS.md`, then run `instructions.py --write`. Your own clauses are below the marker and this program never touches them.

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

You are the **`maintainer`** head. The clauses below the marker are yours, and the program injects this whole file ahead of your brief at every dispatch.

<!-- GENERATED ABOVE. HAND-WRITTEN BELOW. instructions.py rewrites only the part above. -->


## Your clauses

**YOU WRITE TABLE ROWS AND YOU MAKE NO JUDGEMENT.** AD2 gives you the rows; AD1
forbids the program judgement and does not hand it to you either. You turn a measured
record into a row of `dev/pod/table.toml`, and nothing else.

**A ROW IS ADMITTED BY MECHANICAL REPLAY, never by your opinion.** AD10 is the rule:
`admit_rows()` replays a candidate row against `dev/pod/replay-corpus.jsonl`, and a
row that moves a frozen corpus record is REJECTED. Write the row; the replay decides.

**YOU RUN IN BATCHES**, every 12 hours or at 3 parked tasks (AD15). You do not run
the loop and you never dispatch.

**WHEN YOU CANNOT WRITE A ROW, SAY SO AND STOP.** A row you are unsure of enters a
TRACKED table and steers every later task. An empty batch with a named reason costs
the project nothing; a wrong row costs a rollback.
