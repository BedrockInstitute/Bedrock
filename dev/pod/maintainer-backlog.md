# The maintainer's backlog

**THE QUEUE IS FOR NON-RESIDENT AGENTS AND THIS FILE IS FOR THE RESIDENT ONE.** Owner's
ruling, 2026-08-19. `dev/pod/queue.toml` exists because a mathematician or a coder does
not exist until rule (f) starts one: an entry is how you hand work to something that is
not there yet. **The maintainer is resident, so it needs no queue.** Work reaches it two
ways, and both are direct: the owner attaches to its pane and says so, or the owner
writes it here and the next batch brief carries it.

**WHAT BELONGS HERE.** Defects in the POD program itself, its rules, its gates and its
records. Anything whose write scope is `scripts/pod/`, `dev/pod/` or the design memo.

**WHAT DOES NOT.** Mathematics and the proof tree. Those are queue entries, and AD3 gives
every one of them to a mathematician.

**THE PROGRAM NEVER WRITES THIS FILE.** `write_batch_brief()` reads it and copies it into
the brief; it does not edit it. The maintainer strikes an item by editing this file in
the same batch that lands the fix, so the next brief no longer carries it.

## Open

### 32. `scripts/pod/launcher.py:70` hardcodes the absolute repo path, so its own test suite cannot run from a git worktree. FOUND 2026-08-25

**NOT MINE, FOUND BY A DISPATCHED AGENT, VERIFIED HERE.** `ROOT =
Path("/Users/alsg/Agentic/Bedrock")` is a literal, not a `Path(__file__)`
derivation. `test_pod_launcher.py` reads `mod.STATE`/`mod.LOGS` off that
constant, so when the suite runs from ANY OTHER checkout of this repo (a git
worktree, a second clone), those paths resolve into the MAIN checkout instead
of the one under test. Two checks fail there every time, unrelated to
whatever the worktree actually changed.

**MEASURED, NOT TAKEN ON REPORT.** Ran the same suite twice on the identical
committed test file: from `.claude/worktrees/agent-ad6572326da066201`, 2
failures (`launcher.py:70`'s doing); from `/Users/alsg/Agentic/Bedrock`
itself, 268 checks, 0 failures. Same file, same commit, different `ROOT`
value at runtime.

**WHY IT MATTERS NOW, NOT JUST IN PRINCIPLE.** `isolation: "worktree"` on a
dispatched agent is the normal way to keep a maintainer-session refactor
reviewable before it lands (used for backlog item 31's landing and for the
heads.toml test refactor this item accompanies). Every one of those agents
gets a false-red `test_pod_launcher.py` it has to explain away, which is
exactly the "a gate that fails a commit nobody could have complied with
teaches every author to ignore a red gate" shape memory already names.

**NOT FIXED HERE.** The cure is presumably `Path(__file__).resolve().parents[2]`
or equivalent, matching how `scripts/pod/pod.py`'s own `ROOT` is derived
(check before copying the pattern). Left for whoever next touches
`launcher.py`, since this task's scope was the test file, not the module
under test.

**LANDED, `7c0bf58b`. FOUND WHILE REVIEWING A POD-REFILL, NOT WHILE LOOKING FOR
IT.** `dev/pod/queue.toml`, `dev/pod/replay-corpus.jsonl` and
`dev/pod/transitions/2026-08.jsonl` were all last committed 2026-08-19 (`212cfe2`
/ `34a8780`). The corpus was 19 of 865 lines committed (846 missing, 98 percent);
the transition log 157 of 4037 (3880 missing, 96 percent). **Six days of the
entire LJ-1 campaign's replay record and dispatch history, at risk on one
machine with no cloud backup** (pCloud sync stopped 2026-08-19 and stays off,
per the owner's own ruling). All three parse cleanly (0 malformed JSONL lines,
valid TOML), so nothing was torn; it was simply never landed.

**WHY THE SCOPE CHECK NEVER CAUGHT IT.** `PROGRAM_WRITES_PREFIX`
(`scripts/pod/pod.py:169-188`) exempts these paths from
`maintainer_scope_ok()` on the premise that SOMETHING ELSE commits them,
matching the pattern item 29 already names for the wider tree. Checked the
other four members of the same list: `dev/pod/table.toml` IS committed
correctly (`admit_rows()` calls `git_commit()` directly, last commit today),
`agents/tasks/POD-BATCH/` and `archive/dev/direction/` are now clean (landed
in today's earlier catch-up, `447f125b`/`33a526b6`). **So the gap was exactly
these three, and nothing in `scripts/pod/` ever calls `git_commit()` on any of
them.**

**NOT REPAIRED IN CODE.** Whether the right cure is a periodic auto-commit
inside the loop (and at what cadence, given `transitions/` grows every state
change) or a standing maintainer habit (grep this trio's `git log -1` dates
at the start of a session) is a design question for the owner, not mine to
decide unilaterally. **The next occurrence of this gap will look identical:
check `git log -1 -- dev/pod/queue.toml dev/pod/replay-corpus.jsonl
dev/pod/transitions/*.jsonl` periodically rather than assuming
`PROGRAM_WRITES_PREFIX` means committed.**

### 30. A real NO-GO landing with no companion artifact matches neither task-scoped NO-GO branch. PARKED NOW on LJ-1.630, MEASURED 2026-08-25

**NOT A PROGRAM DEFECT: the routing mechanism worked correctly.** `_hits()`/`_route()`
correctly found no match, because neither of LJ-1.630's own task-scoped NO-GO branches
covers this exact shape. This is a template gap in what the mathematician wrote into the
brief, the same class as items 20/23/24/25, at a new site.

**THE FACTS**, from `.pod-state/worktrees/LJ-1-630/agents/tasks/LJ-1-630/runs/accept-1.out`
and `dev/pod/transitions/2026-08.jsonl:4017`. A genuine Agda type error, not a heap wall
and not a D-10 stop: conjunct 1 (the whole-tree typecheck) FAILED with `UnequalTerms`,
conjunct 6 FAILED too, conjuncts 2-5 held. `exit_code 42`, `error_class "other"`,
`obligations_delta 0`, `changed_files` names `src/L/BoundedSubset.lagda.md` (the coder's
own landing target, actually edited) plus five ad-hoc `runs/*.out` files
(`floor-1.out`, `heavy-1-floor.out`, `heavy-2-with-row.out`, `heavy-2b-with-row.out`,
`heavy-2c-with-row.out`). **No `Probe630.agda` and no `review-of-*.md` anywhere in the
list.**

**WHY NEITHER TASK-SCOPED ROW MATCHES**, `dev/pod/table.toml:25779` and `:25796`:
`task-lj-1-630-no-go-attacked` needs `exit_code = 42` AND
`changed_files_any = ["agents/tasks/LJ-1-630/Probe630.agda"]`; `task-lj-1-630-no-go-stated`
needs `exit_code = 42` AND `changed_files_any = ["agents/tasks/LJ-1-630/review-of-*.md"]`.
The coder produced neither companion file: it edited the landing target directly and left
its trial output under ad-hoc names, which is a real return (a failed proof, not silence),
just not the shape either template anticipated. The one system row carrying
`error_class = "other"` (`sys-sigkill-escalate`, `dev/pod/table.toml:97`) also needs
`exit_code = -9`, so it does not reach this either.

**WHAT `pod-math` MAY WANT TO DECIDE, NOT MINE TO WRITE.** A third task-scoped branch
covering `exit_code = 42` with NEITHER companion file present, presumably `escalate` to
`mathematician_adversarial` (the same action items 20/25 already established for "a real
return with no stated verdict"), OR a brief-side fix so every NO-GO attempt is instructed
to leave the expected artifact. Whichever shape, this is AD3's call and a proposal needs
the replay-verified batch path, not a row I write here.

**PARKED, WAITING.** `no-match` is not one of rule (a2)'s auto-reopening reasons, so
LJ-1.630 stays PARKED until a corrective row is admitted (a batch proposal) or the owner
runs `--retry`.

### 29. `maintainer_scope_ok()` has no BEFORE snapshot, so long-standing ambient drift refuses every batch on `scope`. MEASURED 2026-08-25

**THE DRIFT NAMED BELOW IS NOW CLEARED, OWNER-AUTHORISED 2026-08-25.** Six
commits (`f71700d2`, `9de9c337`, `f5e74d0d`, `33a526b6`, `fdc66a15`,
`3c4a3d2d`, `447f125b`) landed the program, the oMLX watchdog, docs, the
direction archive and shelf, three orphaned admitted-proposal records, one
drive-by test regex fix, and 242 terminal tasks' worth of `agents/tasks/`.
Re-ran the exact `maintainer_scope_ok()` predicate against the live tree
afterward: **0 bad paths.** A future batch will not lose to this UNLESS new
drift accumulates the same way. **The structural gap itself (no
before-snapshot) is UNCHANGED and UNFIXED**: this cleared today's instance,
it did not close the item. LJ-1.629 through LJ-1.632 were deliberately left
uncommitted (live at the time), as were two probes `check-probes` refused
under `agents/tasks/LJ-1-607/runs/cold/` (names collide with LJ-1.134/136,
task ownership undetermined), and the retired `*.toml.{scope,empty,refused,
reject}` proposal litter (already exempted from the check by design, left
alone rather than committed).

**FOUND WHILE REVIEWING A POD-REVIEW, NOT WHILE LOOKING FOR IT.** My own batch
`dev/pod/proposals/20260825-193112.toml` (0 rows, reasoned) was refused with
verdict `scope` at `dev/pod/transitions/2026-08.jsonl` seq 3998, one minute
after I wrote it. I did not know until I later grepped the log for an
unrelated review. A 0-row batch losing to this costs nothing; a batch that
proposes real rows does not.

**THE ROOT CAUSE IS STRUCTURAL, NOT A MISSING EXCLUSION.**
`side_scope_report()` (for the refill and the resident mathematician) takes a
snapshot at DISPATCH and diffs it at RETURN (backlog item 10's whole fix).
`maintainer_scope_ok()`, `scripts/pod/pod.py:3542`, takes NO before-snapshot
at all: it calls `facts_mod._status_paths(root)` fresh and flags every path
outside a static allowlist (the proposal itself, `PROGRAM_WRITES_PREFIX`,
a retired-proposal suffix, `agents/tasks/`). Every OTHER path already dirty
in the tree, however old and however unrelated to this batch, reads as this
batch's stray write.

**THE DIRT IS REAL AND OLD, NOT THIS SESSION'S.** The mathematician's own
2026-08-25 session-start report said it plainly: "I changed no file and I
created no file. The 1447 paths that git status --porcelain reports were
there before this session started." My batch's refusal named 20 of them:
`Makefile`, `agents/README.md`, `dev/build-manifest.toml`,
`dev/pod/README.md`, `dev/pod/heads.toml`, `dev/pod/maintainer-backlog.md`,
`scripts/README.md`, `scripts/gate/check-omlx-quiet.py`,
`scripts/ops/agda-watchdog.sh`, `scripts/ops/omlx-watchdog.sh`, and eight
`scripts/pod/*.py` files (`dev/LESSONS.md` was on the same list; I have
since committed it, `4b6c8054`). None of these is `PROGRAM_WRITES_PREFIX`,
none is under `agents/tasks/`, and I did not write any of them in that
batch.

**THIS HAS COST REAL ROWS, NOT ONLY EMPTY ONES.** `grep -c '\[\[row\]\]'`
over every retired `*.toml.scope` proposal: 9 carried real rows (1 or 2
each), including `dev/pod/proposals/20260819-150740.toml.scope`
(`sys-lint-accept`, a system row now live in the table under a LATER,
successful proposal) and `dev/pod/proposals/20260821-102037.toml.scope`
(`task-lj-1-440-stop-stated`, `task-lj-1-444-stop-stated`, item 20's own
fix, which the backlog records as later proven in the field: meaning it
too was re-proposed successfully afterward). **Nothing named here is
provably lost for good**, because the same content can be, and evidently
was, resubmitted until it landed on a moment the tree happened to be
scope-clean. What is lost is the SIGNAL: a refused batch looks identical to
an empty one from the maintainer's own seat, unless the maintainer thinks to
grep the transition log for its own proposal's fate. `75` of the historical
proposals under `dev/pod/proposals/` carry verdict `scope`, against 5
`admitted`.

**NOT REPAIRED HERE.** Two different cures fit and they are not the same
decision: (a) give `maintainer_scope_ok()` a before-snapshot the way
`side_scope_report()` has one, so only paths that changed DURING this
batch's own window count against it; or (b) commit the 20 standing dirty
paths so the tree is actually clean, which is a judgement call about
WHOSE in-progress work they are and whether it is safe to land, not a
mechanical fix. I have not read what changed in those 20 files and will
not guess. Whichever the owner prefers, the next maintainer batch should
read this item before assuming a `scope` refusal names ITS OWN write.

### 26. `heap-wall-escalate`, another branch the MATHEMATICIAN wrote, loops on a resource fact. TEMPLATE FIXED 2026-08-22

**SECOND DEFECT OF THE SAME SHAPE AS ITEM 24, IN THE SAME TEMPLATE.** Found
2026-08-22 when `[LJ-1.534]` parked at `attempt_max`. Repaired for every brief
written from now; the briefs already dispatched still carry the broken row.

**THE ROW, IN EVERY BRIEF SINCE `[LJ-1.492]`.**

```toml
id = "heap-wall-escalate"
priority = 30
action = "escalate"
head_slot = "coder_adversarial"
  [branch.when]
  heap_wall = true
```

**MEASURED ON `[LJ-1.534]`**, from `dev/pod/transitions/2026-08.jsonl`:

| attempt | ts | exit | heap_wall | row |
|---|---|---|---|---|
| 1 | 10:34:13Z | 251 | true | `task-lj-1-534-heap-wall-escalate` |
| 2 | 10:49:04Z | 251 | true | same |
| 3 | 10:59:49Z | 251 | true | same |
| 3 | 11:13:11Z | 251 | true | same, `reason: attempt_max` |

**WHY IT CANNOT WORK, AND IT IS NOT AN EXCLUSION PROBLEM.** Item 24's cure was
a delta key. **This one is different: a critic dispatched at a heap wall
RE-RUNS THE SAME PROBE AND RE-HITS THE SAME WALL.** No exclusion helps, because
the second run is as entitled to the row as the first. **A heap wall is a
resource fact and no critic can adjudicate it.**

**THE FIX, NOW IN `pod-math`'s TEMPLATE: `action = "park"`.** A park is the
honest state for "this probe does not fit in memory", and it stops the loop
dead instead of spending three dispatches to reach `attempt_max`.

**WHAT IT COST HERE, AND THE LOSS IS SMALL.** `[LJ-1.534]`'s worktree holds no
report and no probe: the wall fired before anything was written. **Unlike
`[LJ-1.512]` under item 23, nothing delivered was stranded.**

**AND THE WALL ITSELF IS A MEASUREMENT `pod-math` IS ACTING ON.** The task
collected sixteen hypotheses at one frame and the elaborator ran out of memory
four times. That is evidence about the frame, not only about the program.


### 25. Amending a dispatched brief does NOT admit its new row. `[LJ-1.505]` needs the owner. MEASURED 2026-08-22

**`pod-math` TRIED THE BRIEF ROUTE AND IT DID NOT WORK.** Answering the
maintainer's `[LJ-1.505]` request, `pod-math` added a `no-verdict` branch to
`agents/tasks/LJ-1-505/LJ-1.505.md:208-218` at about 00:36Z and said in its
return that if the program does not re-read an amended brief on re-attempt then
this needs the owner. **It does not, and it does.**

**THE MEASUREMENT.**

- `grep -n "no-verdict" dev/pod/table.toml` returns **NOTHING**. The row was
  never admitted.
- `grep -c "task-lj-1-505" dev/pod/table.toml` returns **7**, which are the
  rows admitted from the brief at first dispatch. The eighth was not added.
- `[LJ-1.505]` has recorded `reason: no-match`, `exit_code 0`, **eleven more
  times** between 2026-08-22T00:38:44Z and T01:11:08Z, all after the edit
  (`dev/pod/transitions/2026-08.jsonl`).

**SO THE `[LJ-1.422]` PRECEDENT IS THE ONLY ROUTE**, and it is what
`dev/pod/table.toml:3562-3574` records: a task-scoped row, `added_by =
"maintainer"`, under an owner's ruling. `pod-math` cannot write it; a row that
routes live corpus records needs the owner's word.

**THE ROW, READY TO WRITE, WITH THE MATHEMATICAL JUDGEMENT ALREADY MADE (AD3).**
`[LJ-1.505]`'s obligation is waiting on a verdict the coder never gave: its
accept record is exit 0, `error_class` null, `obligations_delta` 0,
`obligations_open` 1, 18 changed files that are its own census scripts, and NO
`review-of-*.md`. That is neither a GO nor a stated stop. An open obligation
with no stated verdict is what the adversarial slot exists to adjudicate.

```toml
[[row]]
id = "task-lj-1-505-no-verdict"
scope = "task:LJ-1.505"
priority = 13
action = "escalate"
head_slot = "mathematician_adversarial"
added = 2026-08-22
added_by = "maintainer"
reason = "AD3 judgement by pod-math: an open obligation with no stated verdict is neither a GO nor a stop. Disjoint from go (delta max -1) and from stop-stated (which needs a review file PRESENT). The changed_files_none exclusion stops the critic's own return re-matching it."

  [row.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_none = ["agents/tasks/LJ-1-505/review-of-*.md"]
```

**TWO MORE LJ-1 TASKS ARE PARKED AND `pod-math` DID NOT DIAGNOSE THEM.** The
last recorded event of each carries a reason: `[LJ-1.497]` **`admission`** and
`[LJ-1.498]` **`launch`**. `[LJ-1.498]` has never produced a probe, a report or
a `runs/` directory since 2026-08-21T20:48Z, which a launch failure would
explain. These are named here as facts from the transition log, not as
diagnoses.

**WHY THIS MATTERS BEYOND ONE TASK.** `dev/pod/direction.md` says LJ-1 is
complete when, among other things, "the parked LJ-1 tasks are settled or the
owner has declined `--retry`". **Three of them are parked right now**, and two
of the three are parked for program reasons rather than mathematical ones.


### 24. `accept-failed`, a branch the MATHEMATICIAN wrote, loops a task that delivers nothing. TEMPLATE FIXED 2026-08-22

**THIS IS `pod-math`'s DEFECT, NOT THE PROGRAM'S, AND IT IS IN A DOZEN BRIEFS.**
Found 2026-08-22 while answering a refill. The template is repaired for every
brief written from now on; the briefs already dispatched still carry the broken
row and that is why this item exists.

**THE ROW, AS WRITTEN IN EVERY BRIEF SINCE `[LJ-1.492]`.**

```toml
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"
  [branch.when]
  exit_code = 1
  changed_files_none = ["agents/tasks/LJ-1-NNN/review-of-LJ-*-*.md"]
```

**IT HAS NO `obligations_delta` KEY.** So it matches an acceptance failure
whether the obligation was delivered or not.

**MEASURED ON `[LJ-1.497]`, from `dev/pod/transitions/2026-08.jsonl`.** The
worker was silent from 2026-08-21T20:48Z to 2026-08-22T00:29Z, then:

| attempt | ts | exit | delta | row |
|---|---|---|---|---|
| 1 | 00:29:45Z | 1 | **0** | `task-lj-1-497-accept-failed` |
| 2 | 00:31:22Z | 1 | **0** | `task-lj-1-497-accept-failed` |
| 3 | 00:33:29Z | 1 | **0** | `task-lj-1-497-accept-failed` |
| 3 | 00:35:35Z | 1 | **0** | same row, `reason: attempt_max:task-lj-1-497-accept-failed` |

**Four matches in six minutes to `attempt_max`.** Its worktree holds the brief
and two critic briefs and NOTHING ELSE: no probe, no report, no `runs/`, no
accept record. Two critic dispatches were made against a return that does not
exist on disk.

**WHY THE ROW EXISTS AND WHAT IT SHOULD HAVE SAID.** It was written after
`[LJ-1.469]`, where the term was GREEN, the ratio was under the bar, and
acceptance conjunct 4 failed: exit 1 with `obligations_delta = -1`. **That is
the case it is for.** A return that delivers nothing and fails acceptance is a
different event and must not route here.

**THE FIX, NOW IN `pod-math`'s TEMPLATE.** Add `obligations_delta_max = -1` to
the `[branch.when]` block. Every brief `pod-math` writes from 2026-08-22 carries
it.

**WHAT THE MAINTAINER MAY WANT TO DECIDE.** Briefs already dispatched carry the
broken row and their rows are already admitted. `pod-math` is NOT proposing a
`table.toml` write and is not naming a system row: a row that has already routed
live corpus records is not fixable by an ordinary batch proposal, and that needs
the owner's word. This item is the evidence, with the task and the timestamps.

**ONE CORRECTION `pod-math` OWES.** Two refills of 2026-08-22 recorded that
`[LJ-1.497]` was "silent inside the six-hour `worker_deadline_s`" and that this
was not a defect. The silence was real for three and a half hours; **what
followed was not silence but four loops on a row `pod-math` wrote**, and the
earlier reading did not survive the measurement.


### 23. `sys-lint-accept` loops a task whose obligation is ALREADY CLOSED. LIVE NOW on LJ-1.500

**RECURRENCE 2026-08-22, ON `[LJ-1.512]`, AND THE PATTERN IS IDENTICAL.** From
`dev/pod/transitions/2026-08.jsonl`:

| attempt | ts | exit | delta | row |
|---|---|---|---|---|
| 1 | 09:11:38Z | 1 | **-1** | `task-lj-1-512-accept-failed` |
| 2 | 09:23:39Z | 1 | 0 | `sys-lint-accept` |
| 3 | 09:35:42Z | 1 | 0 | `sys-lint-accept` |

**The obligation was INHABITED at attempt 1** (`delta -1`), exactly as on
`[LJ-1.500]`, and the task then repeats on the system row. Its directory holds
`review-LJ-1-512-1.md` and `review-LJ-1-512-2.md` and no report.

**ONE THING IS DIFFERENT AND IT IS GOOD NEWS FOR ITEM 24.** Attempt 1 matched
`task-lj-1-512-accept-failed` at `delta -1`, which is the `[LJ-1.469]` case that
row exists for. **The repaired `accept-failed` row behaved correctly.** The loop
that follows is the system row and it is unchanged.

**TERMINAL 2026-08-22T09:57Z. `[LJ-1.512]` DID NOT RESOLVE.** It recorded
`reason: attempt_max:sys-lint-accept` and is permanently parked. **Unlike
`[LJ-1.500]`, which recovered on attempt 5, this one did not.**

**WHAT IT COST: A COMPLETE 59-ROW CENSUS, DELIVERED AND UNLANDABLE.** The
report is at
`.pod-state/worktrees/LJ-1-512/agents/tasks/LJ-1-512/lj-1.512-report.md`, with
`Probe512.agda` and three critic reviews beside it. Its answer, which the
campaign needs: **41 of the 59 `TFacts` fields have an honest form delivered in
`src/L/Coding/EnvSupply.lagda.md`, 16 have theirs elsewhere, and 2 have none in
`src/`.** `pod-math` has read it from the worktree and is acting on it.

**THIS IS NOW A RECORDS PROBLEM AS WELL AS A ROUTING ONE.**
`agents/README.md` rules that a probe pairs one-to-one with its report, is
tracked, and is never deleted. **`Probe512.agda` and its report are in neither
state**: they exist, they are not tracked, and nothing will land them.

`pod-math` still proposes no row: `sys-lint-accept` is a SYSTEM row and needs
the owner's word. **But the cost is no longer hypothetical.**


**`[LJ-1.500]` HAS RUN FOUR ATTEMPTS AND ITS OBLIGATION IS INHABITED.** Diagnosed
by `pod-math` 2026-08-22 while answering a refill. This is a program matter, not a
mathematical one, and the task is looping as this is written.

**THE ROUTING, FROM `dev/pod/transitions/2026-08.jsonl`.**

| attempt | exit | delta | row matched |
|---|---|---|---|
| 1 | 1 | **-1** | `task-lj-1-500-accept-failed` (correct: obligation inhabited, acceptance failed) |
| 2 | 1 | 0 | `sys-lint-accept` |
| 3 | 1 | 0 | `sys-lint-accept` |
| 4 | 1 | 0 | `sys-lint-accept` |

**THREE IDENTICAL ITERATIONS WITH NO STATE CHANGE.** Each re-dispatch reaches the
same acceptance and matches the same system row, so it will run to `attempt_max`.

**THE ACCEPTANCE FACTS, from the worktree's last `runs/accept-*.out`.**

- `conjunct 6 FAILED`; conjuncts 1 to 5 held.
- `error class lint`, `exit 1`, `wall seconds 0.0`, `in-fence lines 0`.
- **`"obligations_open": 0`** and attempt 1 carried `obligations_delta: -1`.
- `"changed_files_refused": ["agents/tasks/LJ-1-500/Probe500.agda"]`.
- `changed_files` is 32 entries: the coder's report, TWO critic outputs
  (`review-of-LJ-1-500-1.md`, `review-of-LJ-1-500-2.md`) and 29 files under
  `runs/`.

**WHAT THIS COSTS.** The coder's work is DONE and is sitting in
`.pod-state/worktrees/LJ-1-500`, which holds `lj-1.500-report.md`,
`Probe500.agda` and two critic reviews. **`obligations_open` is 0.** The task
cannot land it because every re-dispatch fails the same conjunct.

**WHY THE OTHER ESCALATIONS DID NOT HIT THIS.** `[LJ-1.490]`, `[LJ-1.492]`,
`[LJ-1.494]`, `[LJ-1.496]` and `[LJ-1.504]` all closed on
`sys-critic-upheld-no-go`. They exited before a second critic ran.
**`[LJ-1.500]` is different because its attempt 1 was `accept-failed` (exit 1)
and not a NO-GO**, so the escalation chain kept going. Any task that escalates
on `accept-failed` may reach this.

**WHAT `pod-math` IS NOT CLAIMING.** I did not determine WHICH clause of
conjunct 6 fails, and I am not proposing a row. `sys-lint-accept` is a SYSTEM
row; a task brief cannot reach it, and a row that has already routed live corpus
records is not fixable by an ordinary batch proposal. The facts above are what
the record gives.

**ONE CORRECTION `pod-math` OWES.** The refill of 2026-08-22 (seventh) wrote that
`[LJ-1.500]`'s brief was the defect behind its non-closure. **That is wrong.**
The brief was too broad (two fields plus a census where one term was the gate),
but the reason it has not closed is this loop, and its obligation is inhabited.


### 22. `salvage:LJ-1.459` is RULED SUPERSEDE. Close the park. RULED 2026-08-22

**THIS IS THE MATHEMATICAL RULING THE MAINTAINER ASKED FOR THREE TIMES.** The
question reached `pod-math` on 2026-08-21 and again twice; the returns did not
reach the maintainer, so the ruling is written here where a batch brief carries
it. Owner's instruction was to decide, not to describe.

**RULING: SUPERSEDE. `[LJ-1.461]`'s `Residue` is the one to keep. Nothing
mathematical is lost. `salvage_worktree()` was right to refuse.**

**THE EVIDENCE.** `diff src/L/StageBound.lagda.md
.pod-state/worktrees/LJ-1-459/src/L/StageBound.lagda.md`, re-run against the tree
of 2026-08-22, is **5 hunks and 18 lines**, and `Residue`'s BODY is byte
identical in both. There is no third possibility to weigh: the two constructions
agree on the mathematics and differ only in presentation.

| # | site | difference | content |
|---|---|---|---|
| 1 | `src/L/StageBound.lagda.md:23` | `open PT using ( ∣_∣₁; ∥_∥₁ )` against `( ∥_∥₁; ∣_∣₁ )` | none, order inside one `using` |
| 2 | `:49` | one comment line against two | none |
| 3 | `:52-54` | the three arguments of `Residue`'s type: landed anonymous, 459 named `isL-ord`, `κL`, `κC`, and `oa` in the two maps | **the same type** |
| 4 | 459 at `:126-130` | an `inside` helper, `inside f = bounded-from-trunc ∣ f ∣₁` | a factoring |
| 5 | landed `:133` against 459 `:139` | `bounded-from-data f = bounded-from-trunc ∣ adapter f ∣₁` against `= inside (adapter f)` | the same term, inlined |

**NOTHING IS LOST BY DISCARDING THE WORKTREE.** `[LJ-1.459]`'s whole record is
already in the main tree at `agents/tasks/LJ-1-459/`: the brief, the report, both
reviews and `runs/`. `find` reports **no `.agda` file** in either the main tree
copy or the worktree copy, so rule D-1's probe protection is not engaged. The
worktree holds exactly one file the tree does not, and that file is the
superseded copy.

**ONE THING `[LJ-1.459]` DID BETTER, CARRIED FORWARD SO IT IS NOT LOST WITH THE
WORKTREE.** Its named parameters are the better spelling. `pod-math` will put the
instruction to name those three arguments into the next brief that writes to
`src/L/StageBound.lagda.md`. No such brief is queued today, and `pod-math` writes
no Agda, so this is not an edit anyone should make now.

**WHAT THE MAINTAINER MAY DO.** Close the `salvage:LJ-1.459` park as superseded.
**Removing `.pod-state/worktrees/LJ-1-459` is a deletion and `pod-math` is not
directing it**; that is the owner's call, and the park can be closed without it.


### 21. Every seconds gate is inert, and the ratio bar has never had one eligible record. OWNER-RULED 2026-08-21

**THE OWNER ASKED WHETHER THE RUNNING PROBE TASKS ACCOUNT FOR THE SECONDS
GATES, AND THE ANSWER TURNED INTO A DEFECT.** Written down by `pod-math` at the
owner's instruction, 2026-08-21.

**THE THREE SECONDS GATES.**

| gate | where | condition |
|---|---|---|
| `sys-dd24-ratio-bar` | `dev/pod/table.toml:71-84` | `exit 0`, `heap_wall false`, `seconds_per_line_min = 0.0123` |
| `sys-slow-green-empty` | `dev/pod/table.toml:86-102` | `exit 0`, `obligations_delta` 0, `seconds_min = 300.0` |
| `ran-long-and-changed-little` | every task brief | `seconds_min = 3600.0`, `changed_files_count_max = 1` |

**ALL THREE CARRY ONE GUARD AND IT MAKES ALL THREE INERT IN PRACTICE.**
`matches()` sets `one = rec.get("concurrency") == 1` (`scripts/pod/table.py:575`)
and every seconds key is `one and ...` (`:589-590`, `:596-599`). **A seconds
condition can only match a record measured while EXACTLY ONE process ran.**

**THE GUARD IS RIGHT AND IT MUST NOT BE REMOVED.** A wall clock measured while
two or three Agda processes share the machine is not a rate. The guard is what
keeps a seconds figure honest.

**THE MEASUREMENT, over `dev/pod/transitions/2026-08.jsonl`, 2026-08-21.**

- 265 acceptance records carry a facts object.
- By `concurrency`: `0` 51, `1` 64, `2` 40, `3` 54, `4` 56.
- **64 records are eligible for a seconds condition. Of those, ZERO carry
  `lines > 0`.**

`lines` is fact 7, the in-fence line count of the task's own write scope, and a
raw `.agda` probe carries no fence and counts 0. **So the ratio bar prices
landings only, and no landing record has ever been eligible.** The row appears
**0 times** in the whole transition log.

**THE TWO LANDINGS, AND NEITHER NUMBER IS ADMISSIBLE.**

| task | seconds | lines | recorded rate | concurrency | closed on |
|---|---|---|---|---|---|
| `[LJ-1.442]` | 15.42 | 79 | 0.19519 | **2** | `task-lj-1-442-go` |
| `[LJ-1.445]` | 3.48 | 280 | 0.01243 | **3** | `task-lj-1-445-go` |

Both rates sit above the 0.0123 bar. **Neither is a measurement of the bar's
quantity**, because both were taken under contention. `[LJ-1.442]`'s own brief
predicted the bar would fire and it could not have.

**A SECOND, INDEPENDENT SHADOW, SO FIXING THE GUARD ALONE IS NOT ENOUGH.**
`sort_key` (`scripts/pod/table.py:607-610`) orders by `stop_loop` first, then
**scope**, and only then priority: `0 if row["scope"].startswith("task:") else 1`,
which is AD8. **Every task-scoped row outranks every system row before priority
is compared.** `sys-dd24-ratio-bar`'s `when` is `exit 0` plus the rate and names
no obligation condition, so it overlaps a task's own `go` row completely. Even
with an eligible record, `go` wins. Priority 150 is not the reason and moving it
to 1 would change nothing.

`sys-slow-green-empty` is NOT affected by this second shadow and must not be
"fixed" with it: it requires `obligations_delta` 0 and every `go` row requires
`obligations_delta_max = -1`, so the two are disjoint by construction.

**THE DESIGN CONFLICT UNDERNEATH.** A10 restored DD24's ratio bar. A14 and C-12
run a WIDE tier of up to four concurrent Agda writers, and that tier is the
default (`dev/pod/heads.toml [tiers]`). **Under the default tier the bar can
never see an eligible record.** The two rulings are each correct and together
they make one of them inert.

**THE FIX HAS TWO HALVES AND THEY ARE INDEPENDENT.**

1. **Make a landing's acceptance measurable.** A task whose write scope touches
   `src/` should have its acceptance run alone. `machine: exclusive` already
   exists in the HEAD block and the loop already reads it. **VERIFY that it
   makes the acceptance record carry `concurrency = 1` before relying on it**;
   the exclusivity that is measured today is at dispatch, and the acceptance run
   is a separate moment. If it does not, the fact wants a different source: the
   coder already reports three forced rechecks under a single process, and that
   is the honest rate.
2. **Give the bar a `when` that a `go` row cannot satisfy.** The bar exists to
   price a GREEN landing, which is exactly what `go` closes, so no `when` edit
   can separate them while AD8 stands. Either the bar becomes a task-scoped row
   the mathematician writes into a landing brief at a priority above `go`, or
   AD8 gains an exception. **This is a rule change and it needs the owner.**

**WHAT `pod-math` CAN DO WITHOUT A RULING, AND WILL ON REQUEST.** Half 1's brief
side: write `machine: exclusive` into every future brief whose write scope names
a file under `src/`, and carry a task-scoped ratio row above `go` in those
briefs. That needs no program change and no ruling. Say the word.

**HALF 1 IS APPROVED AND ADOPTED, 2026-08-21. HALF 2 IS NOT.** The owner
approved the no-ruling half: `pod-math` writes `machine: exclusive` into every
future brief whose write scope names a file under `src/`, and carries a
task-scoped ratio row in those briefs. **The AD8 exception, and making the bar
generally task-scoped, stay OPEN and UNRULED and are no part of that approval.**

**THE SHAPE, VERIFIED BEFORE ADOPTION.** `pod-math` built it on a copy of a
landing brief and ran the real gates: `preflight.py` prints `22 checks, no
refusal`, and `table.check_table` admits 7 rows.

```toml
[[branch]]
id = "go"
priority = 10
action = "done"
outcome = "go"

  [branch.when]
  exit_code = 0
  obligations_delta_max = -1
  heap_wall = false
  seconds_per_line_max = 0.0123      # closes only when MEASURABLY under the bar

[[branch]]
id = "ratio-bar"
priority = 11
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_max = -1
  heap_wall = false
  seconds_per_line_min = 0.0123
```

**WHY THE CEILING GOES ON `go` AND THE RATIO ROW SITS BELOW IT.** P20 refuses a
non-`done` branch that OUTRANKS a `done` branch it does not contradict, and its
contradiction table knows four tests: `exit_code`, the `_in` lists, the
`obligations_delta` range, and a glob shared between one block's
`changed_files_any` and the other's `changed_files_none`. **`seconds_per_line`
is not among them**, so a ratio row placed above `go` is REFUSED however
exclusive the two are in fact. Putting the ceiling on `go` makes the two
disjoint by matching instead of by rank, and the ratio row then wins the only
case `go` no longer takes. A three-row shape with an unmeasured fallback was
tried and P20 refuses it for the same reason.

**WHY `machine: exclusive` IS THE RIGHT LEVER.** `admits()` returns
`not running` for an exclusive task (`scripts/pod/pod.py:2056`) and refuses
every other task while one is live (`:2050-2051`), and `slots` counts the Agda
processes during the acceptance run **including its own**
(`scripts/pod/facts.py:207`). So an exclusive landing should record
`concurrency = 1` and its seconds facts become eligible.

**AND IT IS UNVERIFIED IN THE FIELD. NO BRIEF HAS EVER DECLARED IT.**
`grep -l "^machine: exclusive" agents/tasks/*/[A-Z]*.md` returns nothing, and
`scripts/pod/pod.py:3287` says the same in a comment. The first landing under
this rule IS the measurement.

**THE RESIDUAL RISK, NAMED SO NOBODY IS SURPRISED.** Both seconds keys carry
the `concurrency == 1` guard. If an exclusive landing still records
`concurrency != 1`, then NEITHER `go` nor `ratio-bar` matches, nothing matches,
and the task parks `no-match`. **That is item 20's disease at a new site.**
`pod-math` watches the first landing under this rule; if it parks, the cure is
to drop `seconds_per_line_max` from `go` in that brief and report the
concurrency the record actually carried. Until then this shape goes into
landing briefs only, never into a probe brief, where `lines` is 0 and both
keys are dead anyway.

**THE CLAUSE WANTS ITS CANONICAL HOME.** It binds ONE slot, so it belongs in
`dev/pod/instructions/mathematician.md`, not in this backlog and not in a
session's memory. `pod-math` cannot write that file. **Maintainer: move the two
sentences of the approval there, and strike this paragraph when you do.**

**THE ACCEPTANCE TEST.** One landing closes with an acceptance record carrying
`concurrency = 1` and a non-zero `lines`, and the digest's `shadow_list`
(`scripts/pod/digest.py:660`) either shows the bar losing or shows it winning.
Today it can show neither, because the row never enters `hits()` at all.

**A NOTE ON THE DIGEST.** `shadow_list` was built for exactly this signal, and
its docstring says a row that never wins in 30 days is a maintainer signal. It
could not have caught this one: a row that never MATCHES never appears in the
hit list, so it is invisible to a report that counts losses. **A row that has
never matched needs its own line in the digest, beside the rows that lost.**


### 20. A D-10 stop matches no branch row. MEASURED AND THE CURE IS PROVEN 2026-08-21

**THE DEFECT.** A brief that orders a D-10 stop when a premise is absent gets a
worker that runs NO Agda. It exits 0 and discharges nothing, so it matches no
`exit_code = 42` branch and no `obligations_delta_max` branch. Nothing matches,
the task parks `no-match`, and it re-accepts the same scene on every table
write. `[LJ-1.440]` did that seven times
(`dev/pod/transitions/2026-08.jsonl:832`, `:836`, `:849`, `:907`, `:929`), and
`[LJ-1.443]` has now joined it (`:911`, `:934`).

**THE ROUTING DECISION AD3 ASKED FOR, AND IT IS MADE.** The maintainer's own
`[LJ-1.440]` queue entry declined to name the action because it is a
mathematical judgement. **It is `escalate` to `mathematician_adversarial`**: a
stated NO-GO is the critic's input and never a close, and the close is
`sys-critic-upheld-no-go`.

**THE ROW, AND IT IS ALREADY PROVEN IN THE FIELD.** `pod-math` put it in the
five briefs of 2026-08-21. It fired on `[LJ-1.448]`, which stopped on an absent
predecessor report and was routed to a critic instead of parking
(`dev/pod/transitions/2026-08.jsonl:915`, row `task-lj-1-448-stop-stated`).

```toml
[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/<CODE>/review-of-*.md"]
```

It passes P10, P19 and P20, and it cannot shadow `go`, which outranks it at
priority 10 and requires `obligations_delta_max = -1`.

**FOUR BRIEFS STILL NEED IT AND A MATHEMATICIAN CANNOT REACH THEM.** The refill
scope covers only the briefs it writes, so `[LJ-1.440]`, `[LJ-1.442]`,
`[LJ-1.443]` and `[LJ-1.444]` still carry the template without the row. Adding
it un-parks 440 and 443 at the next table write.

**A SECOND, SEPARATE DEFECT IN `[LJ-1.443]`, AND THE ROW DOES NOT FIX IT.** Its
first gate reads `agents/tasks/LJ-1-440/lj-1.440-report.md` and requires GO.
`[LJ-1.440]` wrote only into its own worktree and returned NO-GO, so that gate
can only fail. `[LJ-1.449]` carries the same obligation with the gate
re-pointed at `[LJ-1.445]`, which is DONE and GO. **`[LJ-1.443]` is superseded
and settling it is the owner's `--retry` call, not a repair.**

**A THIRD DEFECT, IN THE ROW ITSELF, MEASURED LIVE ON `[LJ-1.448]` 2026-08-21
AFTER THIS ITEM WAS FIRST WRITTEN.** The `[branch.when]` above has no
`changed_files_none`, so once the critic writes its OWN return
(`review-of-LJ-<N>-<M>.md`), that return ALSO carries the coder's leftover
`review-of-*.md` obstruction file (the worktree's changed-files listing is
cumulative across attempts) and STILL matches `exit_code = 0`,
`obligations_delta_min = 0`. The row fires again, task-scope beats
`sys-critic-upheld-no-go` (section 4.4), and the critic is re-dispatched to
review its own review. Measured: `[LJ-1.448]` reached attempt 3
(`dev/pod/transitions/2026-08.jsonl:915`, `:957`, `:983`) before `attempt_max`
would have parked it. `pod-math` kept writing the SAME unfixed template into
new briefs after this was found: `[LJ-1.449]` (`:986`) and `[LJ-1.451]`
(`:994`) both carry it and will loop the same way once their critics return.
**The cure is one added key:**

```toml
  changed_files_none = ["agents/tasks/<CODE>/review-of-LJ-*-*.md"]
```

This maintainer used it in the `[LJ-1.440]` and `[LJ-1.444]` rows proposed
2026-08-21 (`dev/pod/proposals/20260821-102037.toml`). `[LJ-1.448]`,
`[LJ-1.449]` and `[LJ-1.451]`'s rows are already admitted and rows are never
edited; each will self-park via `attempt_max` naming its own row, which is the
documented behaviour for "a design error in the ROW and not in the task"
(`scripts/pod/pod.py`, `same_row_runs()`'s neighbouring comment). **Add the
exclusion to the template `pod-math` writes into new briefs**, so it stops
propagating.


### 7. A check for the defect shape three audits missed

A written rule that some code path contradicts. The instance: `AGENTS.md` said nothing
typechecks a probe once its task closes, while `replay.py --seed` re-ran 426 of them. The
audits asked whether documents agreed with each other and whether each rule still had an
enforcer; none asked whether code does what a rule says never happens, and the seed had
never been run, so it contradicted nothing until it executed.

The items above share one shape: **a sentence describing the program's behaviour lives
in a different file from the code that performs it, and the sentence was true when
written.** Nobody edited the sentence. Somebody added a new write, a new scope entry or a
new dispatch site, and the old sentence quietly stopped describing the program.

**2026-08-19 ADDS A SECOND SHAPE, AND IT IS THE MORE AUTOMATABLE ONE: A TEST THAT PINS A
SNAPSHOT OF SOMETHING THE PROGRAMME IS DESIGNED TO GROW.** Six instances in one day, each
turning red because the programme worked:

| test pinned | what legitimately changed it |
|---|---|
| the corpus file is empty | the first `live` record landed |
| the system rows, by equality | the maintainer admitted `sys-lint-accept`, which AD2 is for |
| EVERY row unexpired | LJ-1.392 closed and `expire_rows()` retired its branches |
| `len(PARK_REASONS) == 9` | `salvage:` was ruled in |
| `VOCAB == "seven-facts/1"` | A23 added fact 8 |
| `len(ARCHIVE_SCOPE) == 5` | the archive scope was widened to reach DD4 |
| `len(PARK_REASONS) == 10` | `quota:` was ruled in, the day after `salvage:` |
| the eight park CLASS names | both new reasons, and the class list DERIVES from the reasons |
| `停放计数 3/3` in the digest | `parked_max` moved to 7 and rule (d) followed it |
| `HERDR_HARNESSES == (three names)` | `herdr-grok` was wired |
| `legal.models == (eight strings)` | the two grok ids were admitted |
| A12's maintainer model | the owner moved the slot to grok |

Each was repaired by asserting the INVARIANT rather than the snapshot: a seeded row is
still present, a SYSTEM row is unexpired, the vocabulary is read from the table's own
constant. **A checker for this shape would look for a test comparing by equality against
a literal that names a program-written artifact**, which is a narrower and far more
tractable target than the general case above.

### 8. Ask of every producer whether it can do its job

The retired seed was internally consistent, its four exclusion measurements were real, its
implementation matched its prose, and it was inert. Three consistency audits ran over it
and none asked the fourth question: **can the thing this produces actually do the job it
is produced for?** Sweep the POD's other producers for the same shape.

### 12. A test suite that stops running returns SILENT GREEN

MEASURED 2026-08-19, twice in one day and by two different mechanisms. A helper pasted
inside `main()` of `scripts/tests/test_pod_launcher.py` made everything after it
unreachable: the suite printed NOTHING and exited 0. And earlier, `scripts/tests/`
held 21 suites while four were being run, so two were red for hours with real defects.

`test_pod_launcher.py` now carries a `MIN_CHECKS` floor, enforced OUTSIDE `main()`,
because a floor at the end of `main()` is skipped by exactly the early return it exists
to catch. **The other 20 suites have no such floor.** Either give them one, or give
`make test` a per-suite check count it compares against a recorded floor. A suite that
reports success without running is the same defect class as a gate that does not bite,
and `scripts/tests/mutation-audit.py` cannot see it, because a mutant dies for the wrong
reason when the suite is not running at all.

### 13. `herdr-pi` has no banner marker, so the read-back guard is inert for it

`model_readback_ok()` refuses a dispatch whose pane prints the requested model id
verbatim, which is what a NON-RESOLVING id does. The marker is per harness and only
`herdr-claude` and `herdr-grok` have one, both measured. For the two `pi` heads the guard
always passes. That is recorded rather than hidden, and the vendor's real discriminator is
`pi --list-models`, but nobody has measured what a `pi` pane prints. Measure it and add
the marker, or rule that the guard is deliberately absent for that vendor.

### 15. The deadline kills the DRIVER and not the agent that hangs

Raised by an adversarial review on 2026-08-19, finding 3.2, and CONFIRMED as process
topology rather than as a live kill. For a herdr dispatch `t.pid` is the `bash -c driver`
child; the driver starts the agent with `herdr agent start` and the agent lives in a
SERVER-OWNED pane, so Agda is a child of the agent and not of that bash session.
`kill_process_group(t.pid)` therefore kills the waiter and leaves the agent `working` with
the heap. Rule (b) marks the task RETURNED, `admits()` sees a free slot, and a second
writer can start beside the first.

The cure is a different mechanism, not a different pid: a herdr agent is ended through
`herdr agent`, so the deadline limb needs the agent NAME beside the pid. Rule (b) now
reports `pid unrecognised` for the neighbouring case, which is the same leak arriving
through the other door.

**THE AGDA HALF OF THIS LEAK IS CLOSED AND THE AGENT HALF IS NOT.** On 2026-08-22 the
same topology left two Agda processes of LJ-1.524 alive at PPID 1 for 153 and 145
minutes and stalled the loop for 2 h 07 min. `reap_orphan_agda()` in `scripts/pod/pod.py`
now ends an Agda run that outlived its owner, and memo section 11.2.1 carries the
measurement. What this item still asks for is untouched: the AGENT is what holds the
pane, the context and the vendor spend, and nothing here ends one.

### 16. Rule (e) writes, commits and spawns on the tick that stops

Raised by the same review, finding 2.1. The reorder of `cf6c519` was justified with「(e)
dispatches no worker so it is safe under a stop」. `harvest_batch()` writes
`dev/pod/table.toml`, renames a proposal and runs `git_commit`; `prune_logs()` unlinks
files; `ensure_maintainer()` launches. **The stop refuses rule (f) and nothing else**, so
all three were already reachable under `.pod-state/STOPPED` before the reorder; what the
reorder changed is that they now also run on the tick that DECIDES to stop.

The maintainer start is the one this project wants there, and the other two are older.
Decide whether a stopping tick should harvest and prune at all, or whether the stop should
be checked between them.

### 17. An exclusive live task still blocks the maintainer on a stopping tick

Raised by the same review, finding 2.3. `ensure_maintainer()` returns None while any
RUNNING or CHECKING task is `exclusive`, and rule (d) stops afterwards regardless. The
shape is the grok handover incident with a different cause: the loop halts and the role
that repairs it is absent. `--handover` now gives the name back on this path; the LOOP
path has no equivalent.

## Closed

### 19. One label, two meters: the AC line-count figures. DONE 2026-08-21

**THE OWNER RULED THREE THINGS.** Rename the AC line-count definitions so they
cannot be confused. Unify the several 17,000-series figures into the one most
orthodox. **The standing reference figure is the 17,000 one and not the 23,000
one.** Written down by `pod-math` at the owner's instruction, 2026-08-21.

**THE FIX LANDED, BY FILE AND LINE.**

1. `scripts/measure/ledger.py`, `--reuse`. The import closure now prints as
   `AC delivered closure`, never `AC closure`. A new helper,
   `ac_delivered_closure(files, sizes, ac_root)`, computes it from `ac_root`
   alone, with no `gch_root` dependency.
2. `scripts/measure/ledger.py`, `--brief`. The headline now prints
   `AC delivered closure {lines} lines over {masters} masters` unconditionally
   (via the new helper), right after `standing`. It is the orthodox reference
   figure part 3 of the ruling names. `ac_total` (the projection) is printed
   only where a live budget is armed, and stays named `ac-total (projection)`
   everywhere it appears (STDERR threshold banner, the tripwire defect
   message, `--trophy-split`, `--budget`).
3. `--trophy-files` now prints an `ambiguous subtotal` line (modules, lines)
   after its per-file listing, so the count without the lines is no longer the
   only reading.
4. `dev/ledger.toml:761` `[trophy_budget]`, beside `ac_cap`: a comment records
   that the cap reads `ac-total (projection)` and never the AC delivered
   closure, so a future `[LJ-2.2]` re-arm cannot confuse the two.

**BEYOND THE NAMED FOUR:** `trophy_split()`'s own `gch_assign`-DEAD check
(two comments, one defect message) also said "the AC closure reaches it" for
the same import-closure concept; renamed to "the AC delivered closure reaches
it" for the same reason, since a defect message a reader can see is not
exempt from the ambiguity this item is about.

**THE ACCEPTANCE TEST, RUN.** `grep -c "AC closure" scripts/measure/ledger.py`
returns **0** (the item asked for at most 1; every remaining use was
renamed, not only the two headline prints). `ledger.py --check` exits 0,
`declaration clean`. No number in `dev/ledger.toml` changed. `check-rule-ids`,
`check-fences`, `check-closure`, `check-probes` all clean.

**MEASURED AFTER THE FIX**, `ledger.py --reuse`: `AC delivered closure 73
masters 17,183 lines` (same reading as the ruling's table; the tree has moved
since 2026-08-21's 23,513 figure, `ledger.py --trophy-split` now reads
`ac-total (projection) 23,793`, growth from tasks landing in the interim, not
from this fix).

**WHAT THIS ITEM DID NOT DECIDE, AND STILL DOES NOT.** Whether the retired
20,000 cap re-arms against the import closure, and at what value. That is a
threshold ruling for `[LJ-2.1]` and `[LJ-2.2]`, and the owner has not made it.
No new cap was written.

### 18. What two adversarial rounds found and nobody has fixed. FIXED 2026-08-19

Five findings from the second adversarial review, landed together.

- **B1.** `vendor_refusal()` stamps the machine's current UTC offset onto the vendor's
  local clock, and `quota_open()` compares aware stamps in UTC. A naive stamp already on
  disk is still local `now()`, which is what it was when it was written. Newest `-final.md`
  is by mtime then name, so a restored relic whose stamp sorts last cannot hide a later
  real return.
- **B4.1.** `splice_deleted_appends` writes `pass` over one `d.append` in the original
  text. `ast.unparse` of the whole file is gone, so a death is no longer a quote-style
  failure in `test_pod_table`.
- **B5.1.** `columns_lock()` is the same `fcntl.flock` shape as `pod_lock()`. `main()`
  holds it across read-plan-split-write. `write_columns` uses `os.replace` of a sibling,
  so a reader never sees a truncate.
- **A4.1.** `MAINT_ROW` accepts an optional trailing comment and the rewrite keeps it.
- **A4.2.** The loader reads a sibling `.tmp`. `os.replace` is the one write to the live
  path, so a kill before it leaves `heads.toml` on the old bytes.

Each fix has a test that went red when the fix was reverted.



### 14. Rule (b) killed a process group it had not checked. FIXED 2026-08-19

The deadline limb ran `kill_process_group(t.pid)` before testing liveness. A pid the
operating system has RECYCLED belongs to somebody else, and `os.killpg` then takes out a
whole unrelated process group. `rec_alive()` compares the recorded `proc_start` with the
live process, which is exactly the recycling guard, and the old order skipped it for every
task past its deadline.

**IT FIRED TWICE**, at the shutdown for the maintainer handover: LJ-1.398 and LJ-1.399 had
been RUNNING since 08:43Z, both pids were long gone, and `pod stop` reached the kill for
both. Nothing was harmed because `killpg` raised `ProcessLookupError`, so this was
measured before it cost anything rather than after. It is the launcher's founding incident
in miniature: on 2026-08-05 two live agents died because a process group was killed out
from under them.

Liveness is tested first now, and a task past its deadline whose pid is already gone
reports `pid dead`, which is the truer of the two words. Three tests pin the order.


### 5. Five MEASURED corpus records, one per RUNNER class. DONE 2026-08-19

**R3's balance check is armed for every RUNNER class.** `lint` and `spec_surface` the
`live` stream earned by itself. The other three were MADE, each by failing ONE conjunct
on purpose in an isolated worktree and letting `accept.py` produce the record, then
hand-loading it with `provenance = "report"`. VERIFIED after: a system row naming any of
the five now passes `check_balance()`, where three were refused before.

| class | how it was made | evidence |
|---|---|---|
| `obligations_up` | an obligation name nothing resolves, `--obl-before 0`, delta +1 | `agents/tasks/LJ-9-001/runs/accept-5.out:20` |
| `closure_open` | a master `Everything` does not import, STAGED | `agents/tasks/LJ-9-001/runs/accept-6.out:20` |
| `unbound_hyp` | a rule 3 telescope in a master inside the task's scope | `agents/tasks/LJ-9-002/runs/accept-1.out:21` |

**WHAT `unbound_hyp` COST, because it is the one that resisted.** Four facts had to line
up at once and each was read out of the code rather than guessed:

- `check-unbound-hyp.py` scans `tracked_masters()`, so the master must be STAGED. A
  worktree has its own index, verified, so staging there never touches the main tree.
- Rule 3 needs a telescope whose binder is SET-typed, and `SET_TYPE` is
  `^S$|^V\b|⟪|hProp`. Two earlier attempts bound `(x : A)` and `(x : Type)`, so `bound`
  was empty and the rule never looked. A binder of type exactly `S` fires it.
- `OPEN` matches a `(` or `{` at the START of a line, so the telescope has to sit on its
  own line and not inside a `module M (...) where` one-liner.
- **The master must ALSO typecheck**, because conjunct 1 runs Agda on a master inside the
  scope and its class would win over 4's. The first draft imported
  `Cubical.Foundations.Prelude` and died on `InfectiveImport` under `--safe`; builtin
  `Set` needs no import and checks green in 0.35 s.

Conjunct 3 also had to be satisfied, so the master is wired into `Everything` in the
worktree. `src/Everything.lagda.md` is NOT in the trophy spec surface, checked before
touching it, so that wiring does not fire conjunct 5 instead.


### 10. Nothing measured where the refill wrote. FIXED 2026-08-19

Rule (g) dispatches the refill as an EVENT, so it never enters the state machine: no
fact 4, no record, no acceptance, no scope check. It is the ONLY producer of tasks and
nothing would have noticed if it wrote somewhere else.

**THE SNAPSHOT IS TAKEN AT DISPATCH AND DIFFERENCED AT RETURN**, which is the repair the
item said not to ship without. A `git status` taken only at the return blames the refill
for every file the tasks it queued have written since, and those tasks are dispatched
BEFORE it finishes. `cmd_run()` snapshots on the first tick a side dispatch is seen, and
`side_scope_report()` differences it.

FOUR SUBTRACTIONS, each naming what it removes: the refill's declared scope, which is
what it is FOR; a brief under `agents/tasks/<CODE>/`, which is the rest of that scope;
every home the program itself created, because a task running in the window wrote there;
and a retired proposal, which is `retire_proposal()`'s write.

IT REPORTS AND NEVER REFUSES, because AD1 keeps judgement out of the program. The verdict
rides on the POD-REVIEW prompt the maintainer already gets.

**TWO DEFECTS WERE CAUGHT WHILE BUILDING IT.** The first draft read a name `root` that
`cmd_run()` does not bind, so it would have raised `NameError` on the first tick that saw
a side dispatch, which is the tick the alarm fires; no test drives that loop body. And
the prefix list of program writes now has ONE home, `PROGRAM_WRITES_PREFIX`, because it
grew a second reader and W5 forbids the copy.


### 6. The stop that could not tell success from sabotage. FIXED 2026-08-19

The owner ruled the ROW's behaviour unchanged, so only what the owner is TOLD had to
move, and it has. **`check-spec-surface.py` already names the direction** and always did:
`declaration added`, `declaration removed`, `declaration changed`, `surface file added`,
`surface file removed`, `guarded rule home changed`. What was missing was the plumbing.
`spec_surface()` discarded the checker's output, so the record and the owner's push both
carried the bare four words `row sys-spec-surface`.

`accept.py` captures that text on failure into `changed_files_refused`'s neighbour
`spec_surface_detail`, and the `stop_loop` branch appends it to the owner's message,
together with a count of FOREIGN dirty files when there are any, because the conjunct
reads the whole tree. MEASURED the same day: the first stop under it named
`guarded rule home changed: AGENTS.md`, which is the direction and the mover, where the
previous three had named neither.


### 11. ONE WORKTREE PER TASK. Probed 2026-08-19 and the price is 46 seconds

The owner asked whether each task could run in its own git worktree, with the work
salvaged on return and the worktree cleaned. **The decisive unknown was one number**: a
fresh worktree carries `src/` but NO `_build/`, so the first Agda run pays a cold cost.

MEASURED, same probe (`LJ-1.390/Probe390.agda`), same runner (`facts.run_agda`), same
WIDE caliber, so the two numbers are comparable:

| | main tree | fresh worktree |
|---|---|---|
| first run | (warm) 1.43 s | **45.79 s** |
| second run, same tree | 1.43 s | **1.53 s** |
| `_build` after | 345 MB | **12 MB** |
| checkout | | 74 MB |

**IT IS CHEAP, AND THE REASON IS THAT A PROBE BUILDS ONLY THE SLICE IT IMPORTS.** The
twelve-minute figure in `AGENTS.md:91` is the COLD WHOLE TREE and is the wrong
comparable for a task. Against the measured task durations of the day, 6, 8 and 10
minutes of agent time, a 46 second one-off is roughly 8 percent and falls to nothing on
a longer task.

**WHAT IT WOULD BUY, and every one of these is a defect measured on 2026-08-19:**
conjunct 5 stops attributing the maintainer's edits to whatever task is being accepted
(three times in one day); `territory_in_flight()` becomes unnecessary because there is
no shared checkout to collide in; item 9 dissolves, because a parked task's dirt is in
its own worktree and never in the tree every gate reads; and item 10 becomes measurable,
because the refill's writes are a diff of one worktree.

**AND THE 46 SECONDS GOES AWAY TOO. PROBED AGAIN 2026-08-19, at the owner's question:
clone `_build` into the worktree with an APFS copy-on-write clone.**

| worktree | clone cost | first run |
|---|---|---|
| no `_build` | | 45.79 s |
| `cp -c -R _build` | **0 s** | **1.58 s** |

Against the main tree's warm 1.43 s that is the SAME SPEED, so **the Agda interfaces are
path-portable and a worktree costs nothing at all**. `cp -c` on APFS shares the blocks,
so the 344 MB is apparent and not real, and the main tree measured 1.48 s immediately
afterwards, unchanged.

**PREFER THE CLONE TO A SYMLINK, and the reason is the whole point of the exercise.** A
symlinked `_build` is SHARED: the worktree's Agda writes into the main tree's interfaces,
two concurrent tasks write into one another's, and the isolation worktrees exist to buy
is given straight back. A clone is copy-on-write, so it is as cheap as a link and stays
private.

**SHIPPED AND TURNED ON 2026-08-19.** The worker runs in the worktree, acceptance
measures that worktree, and the work is copied back path by path from the brief's
`## SCOPE (write)` at a `done` close. So the scope stops being an honour system: anything
written outside it never reaches the main tree.

**THE COPY NEVER MERGES, SO IT CANNOT CONFLICT.** Its one failure is the main tree moving
the same path while the task ran, and that is DETECTED and never resolved: rule (c) parks
with `salvage:`, the tenth park reason, and the resident maintainer reads it. AD1 keeps
the program out of that decision and no sub-agent is introduced. A task that PARKS keeps
its worktree, because that tree is the scene.

**NO WORKTREE IS A NO-OP AND NEVER A REFUSAL.** A task dispatched before the changeover
ran in the main tree and its work is already there; a worktree that vanished took the
writes with it. Both mean there is nothing to copy, and parking either would have
stranded the eight instances in flight when this shipped.

**STILL NOT MEASURED, and stated rather than assumed.** One probe is one import slice and
a task importing most of `src/` was never tried, though the cloned interfaces make that
far less likely to bite. `cp -c` is APFS only, so another filesystem falls back to a real
copy or to the 45.79 s cold build, and neither is measured. **The first dispatch under
isolation has not run yet**, because the coder vendor's quota stopped the loop the hour
this landed.


### 3 and 4. The archive scope and the missing exclusivity test. FIXED 2026-08-19

`ARCHIVE_SCOPE` named three `archive/dev` files by hand and 48 of the 152 archived files
sat outside it, including both categories the rule names. It now lists the subtrees:
`archive/src`, `archive/dev`, `archive/scripts` and `dev/ARCHIVE.md`. **A single
`archive` entry would have made it worse**: `corpus()` reads a directory as
`masters or markdown`, and `archive/src` holds masters, so one entry would have returned
those and silently lost every archived record. MEASURED after the fix: 109 files
reachable, `archive/dev/DD-archived.md` among them, retrieval 0.19 s.

`ensure_maintainer()` now refuses while an exclusive task is live, which is R12's other
half. Rule (g) always tested it and this did not; the asymmetry was the whole evidence.

### 9. A parked task's output blocked the batch that would un-park it. FIXED 2026-08-19

`maintainer_scope_ok()` counted a worker's task home against the maintainer, so a parked
task's uncommitted deliverables refused every batch: the park needed a row, the row a
batch, the batch a clean tree, and the tree was dirty BECAUSE of the park. The whole of
`agents/tasks/` and `dev/pod/queue.toml` are exempt now, because the maintainer provably
writes neither. **Worktree isolation removes the cause as well as the symptom**, since a
parked task's work never enters the main tree at all.


### 1 and 2. Fact 4 counted the program's own writes as the worker's. FIXED 2026-08-19

`facts.program_task_write()` now filters them in `changed_files_scoped()`, so one reader
no longer disagrees with the other. Four writers are excluded: `.pod` from
`stamp_pod_marker()`, the brief itself from `inject_survey()`, `review-<PRED>.md` from
`review_brief()`, and `runs/accept-<N>.out` from `run_acceptance()`, which item 2 did not
name because it is invisible until attempt 2.

MEASURED 2026-08-19 on LJ-1.388: fact 4 was
`['.pod', 'LJ-1.388.md', 'Probe388.agda', 'lj-1.388-report.md']` and is now the two
deliverables alone. Its own row `ran-long-and-changed-little`, keyed on
`changed_files_count_max = 1`, could not have fired before this.

**IT IS A BEHAVIOUR CHANGE AND NOT ONLY A COUNT.** R7's dead-worker guard (`if not ch`)
is reachable again, so a return that writes nothing now parks with `no-change` instead of
producing a record that says it worked.

## 27. A queued sequence cannot chain: a running task's output is invisible to its sibling

Raised by the mathematician, 2026-08-23. **Not a program defect. A written note,
so the next holder of this slot does not lose a dispatch to it.**

The refill brief rules「THINK SEVERAL MOVES AHEAD AND QUEUE A SEQUENCE, NOT ONE
TASK」and asks for briefs「in dependency order」. **A dependency between two tasks
queued in the same dispatch cannot be satisfied.** `[LJ-1.548]` assumed
`[LJ-1.547]`, and its worktree had no `agents/tasks/LJ-1-547/` directory at all:
a RUNNING task's output is uncommitted, so a sibling cannot see it. The stop is
recorded at `agents/tasks/LJ-1-548/review-of-stage-counted-coded.md`, STOP 1.

**The D-10 stop instruction in the brief worked**, and the task cost one hour
instead of five. **The cure is at the mathematician's end**: queue only
independent tasks in one dispatch, and write a later dependent brief in the NEXT
dispatch, after the predecessor's row is in the transition log.

**No table row and no code change is asked for.** If the owner wants the program
to enforce it, the shape would be a `depends_on` key in `dev/pod/queue.toml`
that holds a task back until the named code has a DONE row, and that is a
design question, not a repair.

## 28. A task parked at attempt_max on timeout loses everything it built

Raised by the mathematician, 2026-08-23. **Evidence, not a proposal.**

`[LJ-1.541]` closed `sys-timeout-escalate` with `reason attempt_max`, at attempt
5, `seconds 1800.01`, `heap_wall false`
(`dev/pod/transitions/2026-08.jsonl:2996`). **That record's `changed_files` names
39 paths**, including `Probe541.agda`, `lj-1.541-report.md` and a seven-file
bisection `BisA.agda` to `BisG.agda` with their `.out` files.

**None of them is in the MAIN tree.** `agents/tasks/LJ-1-541/` holds the brief and
four review briefs, and `agents/tasks/LJ-1-541/runs/` is EMPTY. `[LJ-1.547]`
closed the same way.

**CORRECTION, 2026-08-23: they were never lost.** The worktree is one per task
code and is reused across attempts, so the files survived in
`.pod-state/worktrees/`; what was missing was the salvage. The maintainer's fix
now salvages, restricted to the task home, at the `attempt_max` park.

**What did not reach the main tree is not the proof, which did not finish. It
is the BISECTION**, which is exactly the measurement a successor needs and
which cost five attempts to produce. `[LJ-1.559]` now starts cold and
re-measures the floor.

**No repair is proposed here** because the commit rule is R8 and the owner's:
the program commits by explicit path from the task's scope, and a parked task
has no closing scope. **If the owner wants the artifacts kept, the question is
whether a park should commit `runs/` and the report before it discards the
worktree.** That is a design question.
