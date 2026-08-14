# LJ-1.193 report: the commit gate against a LIVE agent's write territory

tier: pi (deepseek-subagent-mode), model deepseek-v4-flash, by the owner's rule
of 2026-08-14: work that touches no Agda code takes flash. The model is a
command-line flag and this line only records the choice.

## 0. LEAD

**The gate is built and green. The two runs the brief orders are in section
1.** The deliverable is `scripts/check-live-territory.py`, wired into
`make check` as the `liveterritory` target. Every behavioural claim below is
MEASURED or INFERRED in those words.

**The one design decision that could have failed the gate, and how it was
found.** A gate that refuses any staged file inside a live task directory
would fire on the orchestrator's NORMAL work. MEASURED: the orchestrator
committed a task's brief while its agent was live in three of the last five
dispatches (`4ae98f3`, `82dd1fb`, `8eb2ba0`). The gate therefore exempts the
registry-named brief path of each live record, and nothing else. Section 2.1
carries the measurement.

**The mid-task correction, recorded first because it is a rule the project
paid for (C-41).** My first version used the labels D2, D5 and D12 for the
defects `dispatch.py` records, in a file under `scripts/`. `check-rule-ids.py`
read them as citations of the live `DD` series and reported 8 defects. The
orchestrator's correction forbade the D-SERIES NOTE declaration, because my
codes are not archived-series citations. I renamed the labels to `LT-2`,
`LT-5` and `LT-12`, and `check-rule-ids.py` prints clean. Section 6.

## 1. THE TWO RUNS THE ABORT CRITERION ORDERS

**Run one: refusal on a synthetic staged file inside a live territory.**
MEASURED, 2026-08-14, with the real registry. The live set at the run was
LJ-1.193 (this task) and LJ-1.195. I created `agents/tasks/LJ-1-193/
zz-sweep-test.md`, staged it, and ran the gate:

```
$ .venv/bin/python scripts/check-live-territory.py --staged
check-live-territory: 1 file(s) staged for commit inside a LIVE agent's write territory:
  agents/tasks/LJ-1-193/zz-sweep-test.md
      agent LJ-1.193 is live (pid 67448); the file lies inside its task directory agents/tasks/LJ-1-193/

A staged file inside a live agent's territory is a defect with nothing left
to judge: the sweep or the edit lands on work that is still in flight.

Unstage them and commit the rest:
    git restore --staged agents/tasks/LJ-1-193/zz-sweep-test.md
Commit by explicit path, or wait for the agent to finish.
$ echo $?
1
```

The gate names the agent and the file, so the fix is obvious. The synthetic
file was unstaged and removed after the run.

**Run two: pass on a clean index.** MEASURED, same session, nothing staged:

```
$ .venv/bin/python scripts/check-live-territory.py --staged
check-live-territory: clean (0 staged files, 2 live agent(s), no file in a live territory)
$ echo $?
0
```

**The supporting runs, all MEASURED in the same session.**

| run | what | result |
|---|---|---|
| staged scope file | my wired `Makefile` staged while LJ-1.193 is live and holds it in scope | exit 1, "named in its brief's write scope" |
| staged rename | `git mv requirements-dev.txt agents/tasks/LJ-1-193/zz-renamed.txt` | exit 1; `--name-only` reported the destination, which the gate checked |
| brief exemption | synthetic registry, my real live pid, staged file equals the record's brief | exit 0 |
| exemption narrowness | same synthetic registry, a non-brief file in the task dir | exit 1 |
| non-territory file | temp file at the repo root, real registry | exit 0 |
| closed-task report | LJ-1.188's report staged, LJ-1.188 dead, LJ-1.193 and LJ-1.195 live | exit 0 |
| corrupt registry | a broken JSON, `--registry` pointed at it | exit 2, REFUSING, copy saved |
| empty registry | `{"dispatches": {}}` | exit 0, "0 live agent(s)" |
| tracked mode | `make liveterritory`, real tree | exit 0, "1892 tracked files, 2 live agent(s)" |

## 2. THE DESIGN

### 2.1 The one exemption is measured, not hoped

**The failure mode a naive gate would have.** A gate that refuses every staged
file inside a live task directory blocks the orchestrator's normal commit.
MEASURED, 2026-08-14, from `git log` and the registry:

| brief | committed | agent started | gap |
|---|---|---|---|
| `LJ-1.186.md` (`4ae98f3`) | 09:46:39 | 09:46:21 | 18 s after start, agent live |
| `LJ-1.188.md` (`82dd1fb`) | 10:22:00 | 10:21:08 | 52 s after start, agent live |
| `LJ-1.190.md` to `LJ-1.194.md` (`8eb2ba0`) | 10:41:50 | 10:36:23 / 10:41:16 | all five agents live |

The brief is the one file the orchestrator owns inside a live task directory.
The agent never writes it, and committing it changes nothing on disk. The
registry names it in the record's `brief` field, so the gate exempts exactly
that path for each live record, and nothing else. The narrowness is itself
tested: a non-brief file in the same directory still refuses.

**Why the exemption cannot hide a swept report.** A report is committed after
its agent finishes. MEASURED: LJ-1.186's final message was written at 10:03:40
and its report was committed at 10:05:13, 93 seconds later. A live agent's
report is untracked, so the exemption has nothing to hide it behind.

### 2.2 The territory source is generic (DD4)

A live record's territory comes from the record's OWN data, never from a
code-to-directory table:

1. **The task directory.** The parent directory of the record's brief path.
   A brief at `agents/tasks/LJ-1-191/LJ-1.191.md` owns `agents/tasks/
   LJ-1-191/`, where its report and probes land. INFERRED: a future
   dispatcher that writes its briefs outside the deliverable directory would
   under-fire here; the current dispatcher always writes the brief beside the
   deliverable, MEASURED on every live-era record.
2. **The write scope the brief declares.** Every path token in the brief's
   `SCOPE (write)` section, plus directory prefixes for tokens that end in
   `/`. `dispatch.py`'s `write_paths` reads the same section for its clash
   refusal; this gate reads it WIDER, because a commit sweep is blind to the
   file type the clash check filters for. MEASURED on the live briefs:
   `Makefile`, `agents/tasks/...` reports and `.claude/skills/...` grants are
   all real territory here, and none of them matches `write_paths`'s
   `(src|dev|scripts|_build)` prefix.

The registry path itself is overridable with `--registry`, so a future
dispatcher's registry is served without editing the gate. The `--registry`
flag also carries the tests.

### 2.3 When a record counts as live

The gate reuses `dispatch.py`'s `alive()` semantics (LT-2 and LT-5): the pid
exists per `os.kill(pid, 0)` with EPERM counting as existing, and a recorded
start time must match `ps -o lstart=`. ONE DELIBERATE DIFFERENCE: a record
WITHOUT a non-empty `proc_start` is NOT counted live, because a recycled pid
cannot be told from the original process (LT-5), and an adopted-era record
read as live would invent a territory the gate must not invent. MEASURED:
every record whose brief lives under `agents/tasks/` carries a `proc_start`,
0 exceptions among 358 records, so the stricter rule cannot under-fire on any
live-era agent. A record with a live pid and no start time is reported in the
output, never silently ignored.

### 2.4 The write-scope half is staged-only

The scope-file half refuses a STAGED file that a live agent holds. It is
deliberately absent from tracked mode. MEASURED: the scope files of the live
briefs are pre-existing tracked files the agent is authorized to EDIT
(`Makefile`, `scripts/...`), so a tracked-mode audit cannot tell the
pre-existing file from the live edit, and checking it would fire on every
normal tree. Tracked mode checks the task-directory half only, which is what
a swept report or probe would occupy. This limit is stated in the docstring
at `scripts/check-live-territory.py:163-173`.

### 2.5 A corrupt registry refuses, never clears

The gate follows the LT-12 lesson from `dispatch.py`'s `load()`: a gate that
cannot read its own state must stop, not proceed as though no agent were
live. A corrupt JSON is copied aside with a timestamp, named, and exit status
2 is returned, so `make check` sees it. MEASURED by the corrupt-registry run
in section 1.

## 3. WHAT THE GATE CANNOT SEE

These are named honestly, so nobody promises a cure that does not exist.

1. **An open grant that names no directory.** A scope token with a
   placeholder that does not end in `/` names no concrete path, so no staged
   file can match it. This is the same limit as `dispatch.py`'s `open_grant`:
   it is invisible to any path check. INFERRED: the current corpus uses
   `<your-name>/` shapes, which end in `/` and ARE matched as prefixes, so
   the invisible case has not fired yet.
2. **The tool-rewrite half of the incident.** A live agent that READS a tool
   while the orchestrator rewrites it is invisible to a commit-time gate,
   because the agent never writes the tool. `[LJ-1.189]` section 8.2 names
   this and records that no mechanical cure exists. This gate does not add
   one.
3. **A gitignore-resident grant.** `.claude/` is git-ignored, so a staged
   file can never hit a `.claude/` prefix. The parser still matches the
   prefix; the tree just cannot stage it. MEASURED: `git ls-files .claude/`
   returns zero files.

## 4. THE make check WIRING

`Makefile` gains the `liveterritory` target and the `check` line gains it,
beside `probes`, which is the other staged-gate family member:

```
check: venv-check typecheck markers lint lint-agda glossary ledger probes liveterritory tree ...
```

The target runs `scripts/check-live-territory.py --check` (the tracked-tree
mode). The `--staged` mode is the pre-commit shape; `scripts/git-hooks/
pre-commit` is outside this task's SCOPE (write), so wiring the hook there is
the orchestrator's step. MEASURED: `make liveterritory` passes on the real
tree in 0.092 s of wall time including the interpreter startup.

## 5. THE C-41 RENAME (the orchestrator's mid-task correction)

The first version used the labels D2, D5 and D12 for the defects
`dispatch.py` records. In a file under `scripts/`, `check-rule-ids.py` read
them as citations of the LIVE `DD` series, because DD2, DD5 and DD12 exist
and the checker cannot tell which series a bare `D` means. MEASURED: the
checker reported 8 defects at `scripts/check-live-territory.py` lines 37, 38,
41, 48, 130 (twice), 149 and 172. The D-SERIES NOTE declaration was NOT
added, because my codes are not archived-series citations and the declaration
would be false. The labels are now `LT-2`, `LT-5` and `LT-12`. MEASURED:
`.venv/bin/python scripts/check-rule-ids.py` prints clean, and the gate still
passes and refuses exactly as section 1 records.

## 6. THE SEARCHES I RAN (the trap this project paid for five times)

Sweeps by shape, never by one spelling:

- `git log --format=... --date=iso -1 -- <brief path>` for each of the last
  nine task briefs: when each brief was first committed.
- The registry's `started` field for each of those tasks: when each agent
  started. The two lists together gave the brief-while-live measurement.
- A full aliveness probe over all 358 registry records, using `dispatch.py`'s
  own `alive()` semantics reimplemented in a scratch script: the live set.
- `git ls-files .claude/`: the gitignore finding.
- A per-record census of `proc_start` presence for `agents/tasks/` briefs:
  the 0-exceptions measurement.
- `grep -n "D2\|D5\|D12" scripts/check-live-territory.py`: the C-41 sweep
  before and after the rename.

## 7. DD4

The territory source is the record's own data: its brief path and its brief
content. The gate serves any registry shape, any dispatcher that writes the
same three fields (pid, proc_start, brief), and any future task kind. It is
not written for the case that bit one week.

## ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-189/lj-1.189-report.md`, read whole. This is the
  proposal I built: section 6 is P3, section 8 names what has no cure (the
  tool-rewrite half, which I did not promise), section 9 is the method, and
  section 10 is DD4.
- `scripts/check-probes.py`, read whole. Took the staged-gate shape: the
  `--staged`/`--check` modes, the exit codes, the `STAGED_FILTER =
  --diff-filter=ACMR` with its measured rename defect at
  `scripts/check-probes.py:128-137`, and the refusal message shape.
- `.claude/skills/codex-dispatch/dispatch.py`, read at the write-scope sites
  (`write_paths` at `dispatch.py:1331-1368`, `territory_in_flight` at
  `dispatch.py:1370-1400`, `open_grant` at `dispatch.py:1402-1418`,
  `alive` at `dispatch.py:316-346`, `load` at `dispatch.py:231-262`) and the
  launch refusal at `dispatch.py:768-781`. NOT edited: a sibling holds it.
- `dev/LESSONS.md` C-32 (line 2965), C-33 (line 3005), C-34 (line 3189),
  C-36 (line 3302), C-37 (line 3399), C-39 (line 3539), C-40 (line 3620),
  C-41 (line 3657), C-42 (line 3704), C-43 (line 3758), D-29 (line 3260),
  D-30 (line 3350), D-26 (line 1693), C-31 (line 1873), read whole. C-43 is
  the law this gate's exemption had to survive: the exemption is the escape
  hatch, so it is one exact path per live record, tested for narrowness.
- `dev/PLAN.md` DD0 (line 244), read whole: the constraint that a temporary
  instruction is not a standing rule.
- `dev/JOURNAL.md` 2026-08-14, the [LJ-1.187] entry cited in the proposal:
  the two `git add -A` sweeps this gate exists for.
- `.claude/skills/codex-dispatch/.state/registry.json`, read whole: the 358
  records, the liveness census, the brief paths, the proc_start census.
- `scripts/rules.py --for build`, read whole, plus `--grep` over the named
  rules. The bundle is Agda-specific; this task touches no Agda code.
- `scripts/git-hooks/pre-commit`, read whole: where the staged gates live
  today and where this gate's `--staged` mode belongs next.

## LITERATURE (DD18)

Not this task's subject. Nothing in `dev/literature/` bears on a commit gate
against a live-agent registry; DD18 is satisfied by this one honest line.
