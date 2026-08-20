# agents/

**Everything in this directory is agent-generated.** No human wrote these files. They are the
written record of the dispatches that built Bedrock: what each agent was told, and what it
found. This is an English developer-facing folder guide; the rule set is
[AGENTS.md](../AGENTS.md).

The directory moved here from `_build/` on 2026-08-13, by the owner's ruling. `_build/` is
git-ignored and `make clean` empties it, so 493 reports and 406 briefs sat one command from
deletion. They are now tracked.

## The layout: ONE TASK, ONE DIRECTORY

**A task directory holds the brief that ordered the work, the report that returned it, and every
probe the task wrote.** The owner ruled that on 2026-08-13 and `[LJ-1.142]` built it. Before that
ruling a task's three halves sat in three places, and reading one dispatch meant opening three
directories.

| Path | What it holds | Count, measured 2026-08-17 |
|---|---|---|
| `tasks/<CODE>/` | One LIVE task: its brief, its report, its probes | 292 directories |
| `tasks/archive/<CODE>/` | One task of the retired route, the same three files | 494 directories |
| `tasks/archive/Unpaired/` | Probes no report claims by its own name | 12 probes |

```
agents/tasks/LJ-1-141/LJ-1.141.md            the brief
agents/tasks/LJ-1-141/lj-1.141-report.md     the report
agents/tasks/LJ-1-141/ProbeLJ1141A.agda      the probe
```

The split between `tasks/` and `tasks/archive/` is the route, not a date. `[LJ-1.90]` is where
the current arc began; everything earlier is the retired route and nothing writes there again.

**`<CODE>` is the task code with `.` written `-`, in capitals.** `LJ-1.142` is `LJ-1-142` and
`L3.32-T126` is `L3-32-T126`. The reason is in the next section: the directory is an Agda module
name component and a `.` is illegal in one.

**A file inside keeps the name it was born with.** A brief and a report are frozen records, and a
renamed record breaks every citation that ever named it. Only the directory around them is new,
so an old citation still resolves under `find agents -name <the-old-name>`.

**`scripts/agents_tree.py` is the one place that knows this shape.** Nine scripts read the tree
through it, and `scripts/README.md` names the members. Do not write `agents/tasks` into a tenth
script by hand.

**The brief's FORM is `dev/memos/LJ-4-pod-program-design.md` section 6.3, and this file does
not restate it.** No live rulebook section replaces `dev/ORCHESTRATION.md` section 3. The
POD cutover of 2026-08-18 archived that file to `archive/dev/ORCHESTRATION.md`, and the
design memo is the only place that states the form today.

**`scripts/pod/preflight.py` is the gate on the form.** It runs 22 checks over a brief
before the program spawns it, and it refuses a brief that carries no `## ARCHIVE`, no
`## LITERATURE`, no `## PREMISES` or no `## LAWS` section. The program writes the archive
and literature blocks itself, through `scripts/pod/retrieve.py`. `dev/pod/queue.toml` is
the only producer of a task.

## Probes live here

**A probe pairs one-to-one with its report, lives beside it, is tracked, and is never
deleted.** The owner ruled that on 2026-08-13. `dev/LESSONS.md` **D-1** is the canonical rule
and everything below is how to obey it.

**A probe may also copy a live document into `agents/tasks/<TASK>/copy/`.**
`agents/tasks/LJ-1-290/copy/scripts/` is one, and it holds a 642-line frozen copy of
`scripts/README.md` used as the root-anchor fixture. A sweep over `README.md` files must
exclude `agents/`, exactly as the prose linter does at `scripts/gate/lint-prose.py:446`.
Nothing marks a fixture from the outside, so the sweep's filter is the only protection.

**Write your probe in `agents/tasks/<TASK>/`, and nowhere else.**
`agents/tasks/LJ-1-141/ProbeLJ1141A.agda` sits beside `agents/tasks/LJ-1-141/lj-1.141-report.md`.
`src/` is forbidden absolutely; `scripts/gate/check-probes.py` refuses a commit that carries a probe
there, and that rule was bought on 2026-08-04 when one `git add -A src/` committed 13 probe
files.

**The directory name is the module qualifier, so declare `module LJ-1-141.ProbeLJ1141A`.**
`bedrock.agda-lib` lists `agents/tasks` as an include root, so your probe imports `L.Choice.Step`
exactly as a master does, and you run it where you wrote it. It never moves.

**Write the directory as `LJ-1-141`, not `lj-1.141`.** A directory under an include root must
parse as an Agda name. MEASURED 2026-08-13 twice, by `[LJ-1.141]` and again by `[LJ-1.142]` at
its own site: capitals, digits and dashes typecheck, and so does an all-lower-case name. A `.`
in the name fails, because it splits the qualifier and Agda then looks for a directory that is
not there. A `_` fails with `[ParseError]`, because it splits a mixfix name and the digits after
it read as a literal.

**The evidence is kept, not just claimed.** `agents/tasks/LJ-1-142/ProbeNameIndex.agda` imports
one probe per legal shape, and the two sibling directories `NAMETEST-L3.32-DOT` and
`NAMETEST-L3_32_UNDERSCORE` are the negative controls. They are the only Agda-illegal directory
names in the tree and they are illegal on purpose. `scripts/tests/test_agents_tree.py` enforces
the rule over every other directory and checks that it still rejects those two.

**Nothing typechecks your probe once your task closes.** It becomes text, exactly like your
report, and its claim is true of the tree at its date. That is why you run it yourself, while
you still can, and why the verdict still goes in the report.

**Do not name a probe after the module it probes.** Two include roots make a shared module name
an `[AmbiguousTopLevelModuleName]` error.

**The 258 probes moved here on 2026-08-13 keep their old flat module lines**, so
`agda` refuses them with `[ModuleNameDoesntMatchFileName]`. They are frozen records and nothing
typechecks them. **`archive/src/2026-08-13-probe-sweep/README.md` is the tombstone**, and it maps
every pre-2026-08-13 probe path to the path the probe holds today. `[LJ-1.143]` corrected it
through all three hops: `[LJ-1.141]` moved the probes out of `archive/probes/`, `[LJ-1.142]`
renamed the root to `agents/tasks/`, and `[LJ-1.143]` placed the 55 DD25 probes in the task
directory of the review that built each one.

## These files are frozen records

**Nobody edits a file in this tree.** A brief says what an agent was told on a date. A report
says what it found. Both are evidence, and evidence that gets rewritten is no longer evidence.

Two consequences follow, and both are mechanical:

1. **`scripts/gate/lint-prose.py` skips `agents/`**, beside `archive/`. A style gate over a record
   can only force an edit to the record. The exemption is at `scripts/gate/lint-prose.py:446` with
   its reason. The per-episode journal is archived; it is not a live exemption.
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

**The program** replaced the orchestrator on 2026-08-18. `scripts/pod/pod.py` runs the
loop: it takes a task from `dev/pod/queue.toml`, builds the brief here, runs
`scripts/pod/preflight.py` over it, dispatches it, runs the six acceptance conjuncts of
`scripts/pod/accept.py` over the return, and commits by explicit path under rule R8. It
reads no report and it makes no judgement.

- **A dispatched worker** writes exactly one report here, incrementally, and reads the briefs
  and reports its own brief names.
- **The adversarial reviewer** is a dispatch like any other. It gets its own task code and its
  own directory, and it reads the brief and the report it attacks. `agents/tasks/LJ-1-385/` is
  one: the DD25 review of `[LJ-1.383]`.
- **The owner** reads `tasks/` to see where the work stands.
