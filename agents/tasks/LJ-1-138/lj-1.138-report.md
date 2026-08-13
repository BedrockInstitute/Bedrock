# LJ-1.138 report: a correct trigger and a real execution point for the probe lifecycle

STATUS: **DONE.** The trigger landed, the execution point landed, and part C is
a priced proposal. Nothing committed. Nothing pushed. **`src/ProbeLJ1134A.agda`
is untouched and the new rule HOLDS it.** No top-level directory was created.
Nothing was deleted.

Every negative below is marked **MEASURED** or **INFERRED**.

## 1. THE TRIGGER, in one sentence

> **A probe may be swept when no LIVE task needs it, where a task is live if
> `dev/PLAN.md` section 11 says `DISPATCHED` or `planned`, or a live task's
> brief names the probe, or a brief exists for the code and no report file
> exists.**

**It EXECUTES in `make check`**, through `Makefile:82-88`, which now runs
`scripts/check-probes.py --gate`. The gate FAILS when a finished probe still
sits in `src/`. `make probes-sweep` is the one-command fix.

Every one of the three tests can only ADD a hold. None can release one. That is
the whole safety argument: a test that goes stale over-holds, and over-holding
costs disk while under-holding kills an agent.

## 2. THE FINDING THAT CHANGED THE DESIGN

**The brief offers 「a brief with no matching report」 as a live signal. The
converse of it is FALSE in this repository, and two files prove it right now.**

**MEASURED.** `agents/reports/lj-1.136-report.md` exists, 39,948 bytes, and its
own line 9 reads:

> **STATUS: reading, grep and site counting are COMPLETE. Agda is HELD.**

`[LJ-1.136]` is running. Its report file already exists because **C-22 orders
every agent to write the deliverable as a skeleton FIRST** and fill it as
answers land. `agents/reports/lj-1.137-report.md` is the same shape, 11,966
bytes.

**So 「the report exists」 can never CLOSE a task here.** A rule built on it
would have swept `src/ProbeLJ1134A.agda` today, which is the exact failure this
task exists to prevent. The signal survives one way round only: **a MISSING
report proves the task is unfinished.** It is used as a widener and never as a
closer. `scripts/check-probes.py:52-58` states this, and
`scripts/tests/test_probe_lifecycle.py:120-143` pins it.

**INFERRED:** that no other rule in the tree reads a report file as a closed
task. I did not audit every checker for the pattern.

## 3. THE OLD CLOCK, confirmed wrong in both directions

**MEASURED.** The brief's measurement reproduces. `scripts/check-probes.py:122`
set `FRESH_HOURS = 6.0` and `:207` compared the file mtime. That rule is gone.

**MEASURED, and it is the deeper defect.** mtime is a proxy for 「a task is
live」 and it fails both ways, because a probe is written once and read for
hours. `dev/build-manifest.toml`'s `working` class already carried the correct
clock in words: 「Alive only while ONE task runs.」 Nothing read it.

## 4. THE TWO FAILURE DIRECTIONS, and the `ProbeLJ1134A` case

### 4.1 Sweeping too early, the direction that kills an agent

**Cost when wrong: an agent dies mid-task.** That is the 2026-08-05 incident,
two agents.

**The worked case, MEASURED, live in the tree right now:**

```
$ .venv/bin/python scripts/check-probes.py --stale
HELD: a LIVE task needs these. Never touched, for any reason (1):
  src/ProbeLJ1134A.agda
      agents/briefs/LJ-1.136.md:39 names it, and that document is the brief
      of the live task LJ-1.136
```

The chain, every link MEASURED:

| Step | Evidence |
|---|---|
| `[LJ-1.134]` is CLOSED | `agents/reports/lj-1.134-report.md` holds its verdict; `dev/PLAN.md:615` reads `GO, 207 LINES` |
| The old rule would have held it on mtime alone | and released it 6 hours after the last write |
| `[LJ-1.136]` is LIVE | `dev/PLAN.md:617` reads `DISPATCHED` |
| `[LJ-1.136]` needs the file | `agents/briefs/LJ-1.136.md:39` names `src/ProbeLJ1134A.agda` |
| The hop is there too | `agents/briefs/LJ-1.136.md:152` sends it into `agents/reports/lj-1.134-report.md`, which cites the probe 19 times |

**MEASURED: the stem test does NOT hold this file.** `ProbeLJ1134A` parses to
`LJ-1.134`, `LJ-11.34` and `LJ-113.4`, and none of the three is live. **Only
the live-brief test holds it.** That is why the second half of the trigger is
not optional, and the brief was right to demand it.

**THE RULE TRACKED A TASK CLOSING, DURING MY OWN RUN. MEASURED.** `[LJ-1.136]`
finished while I worked. `dev/PLAN.md:616` now reads `705 PLUS A5 UNPRICED`, a
verdict, so `[LJ-1.136]` stopped being live. On the next `--stale` the hold
moved by itself:

```
src/ProbeLJ1134A.agda
    agents/briefs/LJ-1.138.md:53 names it, and that document is the brief
    of the live task LJ-1.138
```

**The probe stayed HELD across the transition, with no decision from anybody**,
and the reason it gives is the new one. **It becomes sweepable when my own row
takes a verdict, which is the correct answer**: at that point no live task names
it. This is the trigger working end to end inside one session, and it is the
strongest evidence in this report.

### 4.2 Holding too long, the direction that re-creates the backlog

**Cost when wrong: `src/` never empties, which is the 284-probe backlog.**

**MEASURED, over all 255 probes in the tree, `src/` and `archive/probes/`
together.** I priced four hop widths before choosing:

| Hop policy | Probes HELD | Holds `ProbeLJ1134A`? |
|---|---:|---|
| Hop into `agents/` and `dev/`, a NAME is enough | **69 of 255** | yes |
| Hop into `agents/` only, a NAME is enough | 57 of 255 | yes |
| **Hop into `agents/` only, must POINT IN** | **23 of 255** | **yes** |
| No hop at all | 2 of 255 | yes |

**I took the third row**, at `scripts/check-probes.py:158-176`. The wide forms
re-create the backlog: a live brief's ARCHIVE section names a prior report, and
that report names every probe its task ever ran, so a quarter of the corpus
never leaves `src/`. **`dev/` is excluded for a second reason: a `dev/` document
is a PERMANENT binding rule, not evidence that a task is running**, and a probe
it names is already EVIDENCE and already archived where the citation resolves.

**The honest cost of the choice.** 21 of the 23 are held by a hop, and today
they are all already in `archive/probes/`, so the choice changes nothing in
`src/`: `ProbeLJ1134A` is HELD under every one of the four policies. **MEASURED.**
The figure is also inflated by five STALE `DISPATCHED` rows (`LJ-1.127`,
`LJ-1.128`, `LJ-1.129`, `LJ-1.131`, `LJ-1.135`), whose reports are written.
**A stale row over-holds, which is the safe direction.**

### 4.3 The residual hole, and it is not closed

**An agent under a task nobody registered, writing a probe whose name carries
no code, gets NO hold from any of the three tests.** It reads as ORPHAN.

**Two things bound it, and neither closes it:**

1. **`dev/PLAN.md` section 6.0 rule 6** requires the row BEFORE the work starts,
   and `scripts/check-task-index.py` fails any cited code with no row. **MEASURED:
   it does not check the verdict cell**, so a row that reads `planned` while the
   task runs is legal, and `planned` is in the live vocabulary for exactly that
   reason.
2. **The DELETION FLOOR.** `scripts/check-probes.py:104-108`. An ORPHAN younger
   than 24 hours is reported and kept.

**The floor uses mtime, and it is NOT the old rule.** The old rule made mtime
the SOLE protection, so its expiry RELEASED a live agent's file. Here three
task-derived holds do the protecting and **mtime only DELAYS the one
irreversible operation.** Its expiry releases nothing that a hold protects.
`scripts/tests/test_probe_lifecycle.py:172-188` pins that a floor of zero still
does not touch the HELD group.

**MEASURED: 191 of 255 probe names carry a task code**, 75 percent. The 64 that
do not are almost all `ProbeDD25*`, which carry a DECISION code, and a decision
has no live or closed state. **INFERRED:** that the naming convention holds for
future probes. It is a convention, not a gate.

## 5. THE EXECUTION POINT, and its honest limit

**I took the brief's option 2, with the threshold at ZERO.** `Makefile:75-88`.

```
probes:
	$(PY) scripts/check-probes.py --check
	$(PY) scripts/check-probes.py --gate

probes-sweep:
	$(PY) scripts/check-probes.py --sweep
	$(PY) scripts/check-probes.py --index
```

**Why the gate moves no file.** A gate with a side effect on the working tree
is not idempotent, its output is not reproducible, and `AGENTS.md` tells a
dispatched agent to leave the tree as its report describes it. The orchestrator
runs `make check` while agents run. **Option 1 puts a file move inside that
window, which is the 2026-08-05 shape.**

**Why the threshold is zero, not a number.** `[LJ-1.133]` found 284 probes
because `--stale`, `--archive` and `--delete` had no caller.
**MEASURED: `grep -rn "check-probes" Makefile scripts/ .pre-commit-config.yaml
dev/ .github/` finds `Makefile:82` and `scripts/git-hooks/pre-commit:16`, and
both used `--check` and `--staged`.** A reminder that does not fail is what
produced the backlog. **A threshold above zero only sets the size of the next
one.**

**Cost: 0.25 s.** MEASURED, `time` on `--gate`, against a 12-minute `make check`.

### The honest limit, and it is real

**The gate does not make the sweep run. It makes a commit impossible until
somebody runs it.** That is a guarantee about the COMMIT, not about the file.
Three gaps stay open, and I state all three:

1. **`make check` is a convention, not a hook.** `scripts/git-hooks/pre-commit`
   runs `--staged` only. A commit that skips `make check` skips the gate.
   **Putting `--gate` in the pre-commit hook would close this**, and I did not
   do it: the hook is outside my write scope, and a hook that blocks an
   unrelated commit on an unrelated backlog is a bigger commitment than a
   dispatched agent should make alone. **Priced: one line in
   `scripts/git-hooks/pre-commit`, 0.25 s per commit.**
2. **A red gate arrives at minute 12** of a cold `make check`, for a
   one-command fix. `probes` runs late in the `check` list at `Makefile:36`.
   **Moving it earlier is one edit and I did not make it**, because I did not
   measure the ordering's other consequences.
3. **The window between a report landing and the next brief being written.** If
   `[LJ-1.134]`'s probe is swept before `[LJ-1.136]`'s brief is written, the
   brief's `src/ProbeLJ1134A.agda` path is stale on the day it is written.
   **The file is not lost**: it is in `archive/probes/`, and
   `archive/probes/README.md`'s generated index maps it. **The cost is friction,
   not loss**, which is the whole reason the sweep archives instead of deleting.

## 6. THE TRAP FIXED: a command that no-ops while printing success

**MEASURED, and it reproduces.** The old `main()` treated `--stale` as the mode
and `--archive` as a flag, so `--archive` alone fell through to the default
check and printed `check-probes: clean`.

**Now every ineffective combination FAILS**, at `scripts/check-probes.py:404-409`:

```
$ .venv/bin/python scripts/check-probes.py --archive
check-probes: `--archive` does nothing under `--check`. It needs --stale or --sweep.
$ echo $?
2
```

**MEASURED, seven combinations, all exit 2:** `--archive`, `--delete`,
`--check --delete`, `--staged --archive`, `--stale --check` (two modes),
`--floor-hours` with no number, and an unknown flag. Two modes at once is now
an error rather than a silent last-wins.
`scripts/tests/test_probe_lifecycle.py:196-236` pins every one.

## 7. PART C: the second include root

### 7.1 Does Agda 2.8.0 accept several paths in `include:`? YES

**MEASURED, by doing it.** I built the miniature outside the repository, at
`/tmp/lj1138-agdalib/`, so that no sibling's Agda run and no repository file was
touched. Two roots, `mastersdir` and `probesdir`:

```
name: twoRoots
include: mastersdir probesdir
```

`probesdir/P.agda` opens `M`, which lives in `mastersdir/M.agda`. Result:

```
Checking P (/private/tmp/lj1138-agdalib/roots/probesdir/P.agda).
 Checking M (/private/tmp/lj1138-agdalib/roots/mastersdir/M.agda).
exit 0
```

**`agda --version` reports 2.8.0.** Total Agda load: two modules of four lines,
under `GHCRTS=-M2g`, about one second. **I ran no Agda on the repository tree.**

### 7.2 What does it cost? Four measurements, one inference

1. **A MISSING include root is NOT an error. MEASURED.** I added `nosuchdir` to
   the same `include:` line and the typecheck still exited 0. **This is the
   cheapest finding in part C:** `probes/` never has to exist in git. No
   `.gitkeep`, no tracked file, no `REUSE.toml` entry, no empty directory in a
   clone.
2. **`_build/2.8.0/` DOES change shape. MEASURED.** Interfaces land at
   `_build/2.8.0/agda/<root>/...`; the miniature produced
   `_build/.../mastersdir/M.agdai` beside `_build/.../probesdir/P.agdai`.
   **MEASURED: `_build/2.8.0/agda/` in this repository holds exactly one entry,
   `src`.** A second root adds a second subtree. `dev/build-manifest.toml`
   classes `_build/2.8.0/**` as `toolchain`, so the new subtree needs no entry.
3. **A module name in BOTH roots is a hard error. MEASURED.** I copied `M.agda`
   into the second root and got `[AmbiguousTopLevelModuleName]`, naming both
   files. **Today the risk is zero**, because probes are `ProbeXxx` and masters
   are `L.*`, but it is a real trap for a probe named after the module it
   probes.
4. **`src/Everything.lagda.md` sees nothing new. INFERRED.** An include root
   makes a module FINDABLE, not checked; `make typecheck` runs
   `agda src/Everything.lagda.md` and `Everything` is a hand-written import
   list. I did not run it, because a sibling is measuring build times.
5. **`make check`'s time. INFERRED, negligible.** One more directory in the
   module search path. **I did not measure it**, for the same reason, and a
   number I did not measure is not a price (P-l).

### 7.3 What must follow

| File | Change | Size |
|---|---|---|
| `bedrock.agda-lib` | `include: src probes` | 1 line |
| `.gitignore` | `probes/` | 2 lines |
| `scripts/check-probes.py` | a `PROBE_ROOTS` constant, and 3 glob sites read it | about 8 lines |
| `probes/README.md` | new; every top-level directory needs one (`AGENTS.md`) | about 25 lines |
| `.gitignore` again | `!probes/README.md`, or the README cannot be tracked | 1 line |
| `REUSE.toml` | **only if the owner wants `probes/**` CC**; the `**` default at `REUSE.toml:11-16` already gives AGPL | 0 or 1 line |
| `scripts/README.md:196-219` | the CLI section, already stale, see section 9 | about 6 lines |
| `dev/LESSONS.md` D-1 | `:1059-1062` says a probe's home is the working tree | 2 lines, and it is a live rule |
| `AGENTS.md` | 「probe files (`src/Probe*.agda`)」 at the Never list | **DD19: the owner rules** |

**No change needed, MEASURED in each case:**

- **`scripts/check-probes.py`'s `classify()`.** `probes/ProbeX.agda` is ALREADY
  refused, because the match is on the basename shape anywhere outside
  `archive/probes/`. `scripts/tests/test_probe_lifecycle.py:240-248` pins it.
  **The 2026-08-04 gate is not weakened by part C.**
- **`scripts/ledger.py`.** `:103` runs `git ls-files src/`, tracked files only,
  and a probe is never tracked. Its docstring at `:12-13` names
  `src/Probe*.agda` and would read stale, which is prose, not counting.
- **`dev/build-manifest.toml`.** It governs `_build/` and the new subtree is
  `toolchain` by glob.
- **`reuse lint`.** An ignored directory is invisible to it. **INFERRED from
  `_build/`**, which is ignored and untracked while `reuse lint` reports
  1,546 / 1,546.

### 7.4 What breaks for an agent, and it is the finding that decides part C

**MEASURED: 216 of 412 briefs write `src/Probe`.** 249 reports do. **Those
documents are FROZEN** by `[LJ-1.130]`'s ruling, which `[LJ-1.132]` and
`[LJ-1.133]` both followed.

**So an agent reading a frozen brief writes to `src/` for as long as frozen
briefs are read.** The tool would have to sweep BOTH roots, which means `src/`
is cleared by the same sweep as today, not by structure.

**That is the honest answer to the owner's question. The second include root
WORKS and it is cheap. It does not make the probe rule structural until the
frozen briefs stop being read.** It becomes structural only if `src/` refuses a
probe outright, and then an agent following a frozen brief hits a wall.

**And the incident it would prevent is already gated.** `git add -A src/` cannot
commit a probe today: `scripts/check-probes.py --staged` refuses it, MEASURED
end to end by `[LJ-1.133]` (its section 4.1) and pinned by my test. **The second
root converts a live gate into a structure. That is worth something, and it is
not worth much.**

**MY RECOMMENDATION, and the owner rules.** Take it if `src/` holding only
masters is worth about 40 lines and one `AGENTS.md` diff. **Do not take it
expecting the probe rule to become self-enforcing**, because 216 frozen briefs
say otherwise. **I did NOT create the directory.**

### 7.5 What `probes/README.md` would say

> # `probes/`
>
> A **probe** is a throwaway miniature that prices a load-bearing assumption
> before heavy work. `dev/LESSONS.md` **D-1** holds the doctrine.
>
> **This directory is the ONLY place a probe is written.** `src/` holds masters
> and nothing else. `bedrock.agda-lib` lists both as include roots, so a probe
> imports `L.Choice.Step` exactly as a master does.
>
> **Nothing here is ever committed.** `.gitignore` ignores the whole directory
> and `scripts/check-probes.py` is the gate, because `git add -f` walks past an
> ignore rule. This README is the one tracked file.
>
> **A probe leaves when no LIVE task needs it.** `make check` fails while a
> finished probe waits here; `make probes-sweep` archives what a document
> points into and deletes what nothing names.
>
> **Name a probe after its task**, `ProbeLJ1138A.agda`, so the tool can read the
> owner off the filename. A probe with no code in its name gets no hold from
> its task and waits on the deletion floor instead.
>
> **Do not name a probe after the module it probes.** Two include roots make a
> shared module name an `AmbiguousTopLevelModuleName` error. MEASURED at
> `[LJ-1.138]`.

## 8. TESTS ADDED

**`scripts/tests/test_probe_lifecycle.py`, 55 checks, all pass.** Wired into
`make test` at `Makefile:178`.

| Group | Checks | What it pins |
|---|---:|---|
| `stem_codes` | 6 | Every digit split is generated; the ambiguity is deliberate |
| `_file_code` | 9 | A brief and its report pair on the CODE across both series |
| the trigger, live tree | 7 | **`ProbeLJ1134A` is HELD, and `[LJ-1.134]` is not the reason** |
| **C-22** | 3 | **A live task with a report file on disk stays live** |
| the narrow hop | 4 | `dev/` is not a hop target; `agents/reports/` is |
| the deletion floor | 6 | A floor of ZERO still does not touch HELD |
| the CLI | 16 | **Seven ineffective combinations exit 2, none prints a success line** |
| the never-commit gate | 8 | `src/`, `probes/`, bare and `archive/src/` all refused |

**MEASURED: `_file_code` pairing is what made the live set usable.** Pairing on
the filename stem read 81 briefs as unreported; pairing on the code reads 8, and
all 8 are retired `T`-series codes that hold zero probes.

## 9. CONSUMERS VERIFIED (C-40)

| Consumer | Result |
|---|---|
| `Makefile:82` `--check` | **exit 0**, 1,479 tracked files. Unchanged behaviour |
| `scripts/git-hooks/pre-commit:16` `--staged` | **exit 0.** MEASURED, unchanged |
| `scripts/check-build-manifest.py:85` cites `check-probes.py:60` | **ALREADY STALE BEFORE MY EDIT.** MEASURED: at HEAD, `check-probes.py:60` is `Exit status: ...` in the docstring. The `_build/` clause is now at `:139-140`. **Out of my write scope; OWED** |
| `dev/build-manifest.toml:13` cited `:60-61` | **FIXED to `:139-140`**, in scope |
| `scripts/check-build-manifest.py --check` | **exit 0** after the edit |
| `scripts/README.md:196-219` | **STALE. It documents `--stale --delete # delete it` with no floor and no gate, and it does not mention `--gate` or `--sweep`. Out of my write scope; OWED** |
| `scripts/ledger.py` | No call. `:12-13` mentions probes in prose only |

**Two checkers are RED and NEITHER is mine. MEASURED:**

- `scripts/check-task-index.py`: `dev/PLAN.md`'s `LJ-1.133` row is 212
  characters against the 200 cap. **`dev/PLAN.md` is a sibling's file and I did
  not touch it.**
- `make test`: `scripts/tests/test_dev_docs.py` fails
  「AGENTS.md one word over 2,200 fires」, 30/31. **`[LJ-1.137]` is editing
  `AGENTS.md` right now.** `make` stops there, so **my test file is never
  reached under `make test` today**; it passes standalone, 55/55.

**Green, MEASURED:** `check-tree.py`, `check-rule-ids.py`, `check-dev-docs.py`,
`ledger.py --check`, `check-build-manifest.py --check`, `lint-prose.py --check`
on all five files I wrote.

**I did not run `make check`.** The brief forbids it.

## 10. WHAT I DID NOT DO

- **I did not touch `src/ProbeLJ1134A.agda`.** MEASURED: 12,996 bytes before and
  after, and the tool reports it HELD.
- **I did not create `probes/`.** It is priced, not built.
- **I did not delete one file.** Nothing was archived either: the sweep found
  nothing to sweep.
- **I did not edit `AGENTS.md`, `dev/PLAN.md`, `dev/LESSONS.md` or any
  `.lagda.md` master.** Three siblings hold uncommitted work in this tree.
- **I did not run Agda on the tree.** The one experiment ran in `/tmp`.
- **`--fresh-hours` is gone and `--floor-hours` replaced it.** MEASURED: no
  caller anywhere passed `--fresh-hours`.

## 11. DD4

**Nothing in this task touched a proof, so DD4 had no line to share.** Where the
instinct applied is the checker, and it applied twice. **The live-task set is
computed once** and the verdicts, the gate, the sweep and the floor all read it;
no mode re-derives it. **`_grouped()` is written once** and `--stale`, `--sweep`
and `--gate` share it, so the gate cannot disagree with the sweep about what is
sweepable. A second copy of either would be the tooling equivalent of writing it
fixed.

## 12. EVERY NEGATIVE, MARKED

- **MEASURED.** A live task's report file exists while it runs.
  `agents/reports/lj-1.136-report.md`, 39,948 bytes, line 9.
- **MEASURED.** `ProbeLJ1134A`'s stem parses to three codes and none is live.
- **MEASURED.** `agents/briefs/LJ-1.136.md:39` names the probe and
  `dev/PLAN.md:617` reads `DISPATCHED`.
- **MEASURED.** `[LJ-1.136]` closed during my run, `dev/PLAN.md:616` took a
  verdict, and the hold on `ProbeLJ1134A` moved to `agents/briefs/LJ-1.138.md:53`
  by itself.
- **MEASURED.** The four hop widths: 69, 57, 23, 2 held of 255.
- **MEASURED.** 191 of 255 probe names carry a task code.
- **MEASURED.** Code pairing gives 8 unreported briefs; stem pairing gave 81.
- **MEASURED.** 216 of 412 briefs and 249 reports write `src/Probe`.
- **MEASURED.** Agda 2.8.0 accepts several `include:` paths, a missing root is
  not an error, a shared module name is `[AmbiguousTopLevelModuleName]`, and
  `_build/2.8.0/agda/` gains one subtree per root.
- **MEASURED.** `_build/2.8.0/agda/` in this repository holds one entry, `src`.
- **MEASURED.** `--gate` costs 0.25 s.
- **MEASURED.** Seven ineffective flag combinations now exit 2.
- **INFERRED.** That `make check`'s time does not move. **I did not measure it**,
  because a sibling is measuring build times. It is a hypothesis, not a price.
- **INFERRED.** That `src/Everything.lagda.md` sees nothing new under a second
  root. It follows from Agda's search model; I did not run it.
- **INFERRED.** That `reuse lint` ignores an untracked ignored directory. It
  follows from `_build/` passing at 1,546 / 1,546; I did not test `probes/`.
- **INFERRED.** That the probe naming convention holds for future probes. It is
  a convention with no gate, and the deletion floor exists because of that.
- **INFERRED.** That the residual hole in section 4.3 is narrow. **I cannot
  measure a task that was never registered.**

## 13. ARCHIVE USED

- `scripts/check-probes.py`, read WHOLE, plus `git log -p` on it. Took: the
  four-verdict order, `classify()`'s `archive/probes/` exemption at `:78-84`,
  the shorthand recall cure at `:150-168`, and the `--index` derive rule at
  `:296-327`. **The mtime block at `:122` and `:207` is what I replaced.**
- `agents/reports/lj-1.133-report.md`, read WHOLE. Took: the verdict-versus-term
  split at `:8-12`; the counterexample pair at `:57-60` that stopped the bulk
  deletion; the recall-bug pair at `:172-186`; **`:446-460`, where `[LJ-1.133]`
  reported the freshness rule keeping `ProbeLJ1134A` and called that the rule
  beating the instruction** — it was right for one day and the clock was still
  wrong; and `:529-535`, the three open items.
- `dev/LESSONS.md` **D-1**, read WHOLE at `:1038-1077`. **Lifecycle rule 2 at
  `:1063-1064` is the trigger's first half** (「the report is written before the
  probe is deleted」) **and rule 3 at `:1065-1069` is the second** (「the file
  survives only while it is a TEMPLATE for imminent work」). My rule is those two
  made mechanical.
- `dev/build-manifest.toml:58-63`, the `working` class, and
  `agents/reports/lj-1.132-report.md`'s seven classes. **The vocabulary FITS and
  I reused it rather than adding a class.** A probe IS `working`. Two
  refinements were needed and both are now recorded in the toml: the clock is
  the task index rather than the report, and a task's own closure is not enough
  because another live task may need the file.
- `archive/probes/README.md`, read WHOLE. Took its three citation forms and the
  shorthand warning. I added the WHEN section above them.
- `dev/PLAN.md` `:197-258` (section 6.0 rules 6 to 8) and `:375-640` (the task
  index). **Rule 6 at `:228-230` is what makes the row a usable live signal:
  registration happens BEFORE the work starts.**
- `dev/ARCHIVE.md`. **It indexes retired MODULES and its columns do not fit a
  lifecycle rule. I added no row**, following `[LJ-1.132]` and `[LJ-1.133]`.
- `REUSE.toml:5-45` for the default bucket, and `scripts/ledger.py:92-103` for
  the tracked-only counting.

## 14. LITERATURE (DD18)

**Nothing in the literature governs a probe directory.**

## 15. TREE STATE

**Nothing committed. Nothing pushed. Nothing staged.**

**Mine, modified:** `scripts/check-probes.py`, `Makefile`,
`dev/build-manifest.toml`, `archive/probes/README.md`.
**Mine, new:** `scripts/tests/test_probe_lifecycle.py`, this report.

**`archive/probes/README.md`'s generated index moved from 244 to 257 rows.** That
is `--index` catching up with the directory, which a sibling filled. The table is
DERIVED, so the change is the tool working.

**Not mine, and I touched none of them:** `AGENTS.md`, `dev/PLAN.md`,
`dev/LESSONS.md`, `agents/reports/lj-1.133-report.md`, `src/ProbeLJ1134A.agda`,
and every `agents/reports/lj-1.13[5-7]-report.md`.
