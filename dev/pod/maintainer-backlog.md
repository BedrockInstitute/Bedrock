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

### 3. The brief builder cannot search where retired rules actually live

`AGENTS.md:116-118` promises the program searches the archive at brief build. Measured:
`ARCHIVE_SCOPE` (`scripts/pod/retrieve.py:148-154`) names five paths, and 48 of the 152
files under `archive/` sit outside them, including **both categories the rule itself
names**: an archived gate lives in `archive/scripts/`, and a moved ruling lives in
`archive/dev/DD-archived.md`. The mathematician's slot file cites W2 as coming from DD4,
and DD4's text is at `archive/dev/DD-archived.md:22`, which no brief can reach.

Either add the missing paths, or change the sentence. The code is the right side to move.

### 4. `ensure_maintainer()` skips the exclusivity test

R12 says a timed task holds the machine alone and nothing else starts beside it. Rule (g)
tests `admits()` before dispatching the refill (`scripts/pod/pod.py:2830`);
`ensure_maintainer()` launches with no such test. The asymmetry is the evidence. Not yet
observed: no brief has ever declared `machine: exclusive`.

### 5. Five MEASURED corpus records, one per RUNNER class

`obligations_up`, `closure_open`, `unbound_hyp`, `spec_surface`, `lint`
(`scripts/pod/accept.py:72-73`). Made by failing acceptance conjuncts 2 to 6 on purpose
and running the runner over each. It needs no probe, and it doubles as the acceptance
runner's own self-test. The `probe-rerun` seed that used to own this slot was retired on
2026-08-19 because a probe record can match only the two heap-wall rows and `replay()`
skips every NO MATCH record, so the seed could never have armed R3 at all.

### 6. The stop that cannot tell success from sabotage

Row `sys-spec-surface` fires on `error_class = "spec_surface"` with no other condition, so
landing the second trophy, deleting a trophy and weakening one all produce the same class,
the same action and the same sentence to the owner. **The owner ruled on 2026-08-19 to
leave the row's behaviour as it is**, so this item changes only what the owner is TOLD:
name the direction of the move, a declaration added versus changed or removed versus a
surface file gone.

### 7. A check for the defect shape three audits missed

A written rule that some code path contradicts. The instance: `AGENTS.md` said nothing
typechecks a probe once its task closes, while `replay.py --seed` re-ran 426 of them. The
audits asked whether documents agreed with each other and whether each rule still had an
enforcer; none asked whether code does what a rule says never happens, and the seed had
never been run, so it contradicted nothing until it executed.

The four items above share one shape: **a sentence describing the program's behaviour
lives in a different file from the code that performs it, and the sentence was true when
written.** Nobody edited the sentence. Somebody added a new write, a new scope entry or a
new dispatch site, and the old sentence quietly stopped describing the program.

### 8. Ask of every producer whether it can do its job

The retired seed was internally consistent, its four exclusion measurements were real, its
implementation matched its prose, and it was inert. Three consistency audits ran over it
and none asked the fourth question: **can the thing this produces actually do the job it
is produced for?** Sweep the POD's other producers for the same shape.

### 9. A PARKED task's output dirties the tree for ever and blocks every batch

`commit_task()` runs only on a `done` close, so a task that parks keeps its deliverables
uncommitted. `maintainer_scope_ok()` refuses on any path it does not recognise, so ONE
parked task blocks every maintainer batch from then on.

MEASURED 2026-08-19, and it cost the whole day: LJ-1.386 and LJ-1.388 both parked
`no-match`, their files stayed dirty, and both batches of the day were retired
`.toml.scope` without their rows ever being read. The maintainer could not write the very
rows that would have un-parked those tasks. **The deadlock is exact: a park needs a row,
the row needs a batch, the batch needs a clean tree, and the tree is dirty BECAUSE of the
park.** The owner broke it by hand, by authorising a commit.

It is not enough to commit at `done`. Either a park commits the task's own scope too, or
`maintainer_scope_ok()` stops counting a live task's own home against the maintainer. The
second is smaller and matches the exemption already granted to `/.pod`.

**A RUNNING task has the same shape and is benign only because it ends.** MEASURED the
same day: with LJ-1.390 dispatched, the gate refuses on its three live files.

### 10. The refill writes real files and NOTHING measures where it wrote them

Rule (g) dispatches `POD-REFILL.md` as an EVENT, so it never enters the state machine:
no fact 4, no record, no acceptance, no scope check. It is the ONLY producer of tasks and
it writes `dev/pod/queue.toml` plus one brief per task, and nothing in the program would
notice if it wrote somewhere else. The maintainer's own proposals get
`maintainer_scope_ok()`; the refill gets nothing.

REVIEWED BY HAND 2026-08-19 and it was CLEAN: the refill of 15:01 queued five tasks, wrote
`dev/pod/queue.toml` and exactly five briefs, all `head_slot: coder`, with the dependency
order written into the queue's own comments. The Agda under `LJ-1-391/` and `LJ-1-393/`
is the coders' and its mtime proves it, 15:31 against a 15:29 brief. **A clean result by
hand is not a gate.**

**THE HARD PART IS ATTRIBUTION AND IT IS WHY THIS IS NOT FIXED YET.** By the time a refill
finishes, the tasks it queued are already dispatched and writing, so a `git status` taken
at its return blames it for the coders' files. A real check needs the status snapshotted
at DISPATCH and differenced at return, which is what `changed_files_scoped()` does for a
task and what `side_dispatches()` would have to grow. Do not ship the naive version.

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

**WHAT IS NOT MEASURED AND MUST BE BEFORE ADOPTION.** One probe is one import slice. A
task that imports most of `src/` approaches the whole-tree cost, and no task has yet
done that. The salvage path is also undesigned: how work returns from the worktree, by
patch or by commit-then-cherry-pick, and what happens when it fails to apply.

## Closed

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
