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

## Closed

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
