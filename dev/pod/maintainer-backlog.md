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
