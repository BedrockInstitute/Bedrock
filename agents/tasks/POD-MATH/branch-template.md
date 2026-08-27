# The branch table I write into every brief, and the ruling behind one row

**Owner of this file: the resident mathematician.** It is not program-generated.
The program parses the `pod-branches` block a brief carries; this file is where I
keep the current shape so a later session does not reconstruct it from a
dispatched brief.

## THE RULING OF 2026-08-27: A LINT FAILURE NEVER GOES TO A CRITIC

**It is mine under AD3**, which gives the mathematician which head an escalation
targets. The maintainer found the mechanism and said so; I verified it at source
before ruling.

**THE CAUSAL CHAIN, AND IT STARTS WITH MY OWN ROW.** From
`dev/pod/transitions/2026-08.jsonl` on `[LJ-1.685]`:

    2026-08-26T20:37:21Z  row task-lj-1-685-accept-failed  head_slot coder_adversarial

My `accept-failed` row escalated an `error_class: lint` failure to a critic. From
that moment the task's return is a review companion, and
`check-survey-quotes.py`'s `report_of()` resolves only to `<task>-report.md`, by
explicit design: its docstring reads "A review companion is another dispatch's
return and is not judged here" (`scripts/pod/check-survey-quotes.py:426-437`).
Every accept run calls it with the task code alone. **So conjunct 6 re-checks the
same static pair forever and can never pass again.** Four `sys-lint-accept`
iterations followed, each with `obligations_open 0`.

**WHY THE ROUTING WAS WRONG ON ITS OWN TERMS, BEFORE ANY MECHANISM.** DD25 sends
a NEGATIVE mathematical return to a critic. A survey-duty failure is a RECORDS
defect in the author's own report. A critic cannot repair another agent's report,
and it should not be asked to. The mechanism makes a category error terminal; the
category error came first.

**THE ROW.** `lint-back-to-author` at priority 13, above `accept-failed` at 14,
so it wins on a lint failure and nothing else changes:

    [[branch]]
    id = "lint-back-to-author"
    priority = 13
    action = "escalate"
    head_slot = "coder"

      [branch.when]
      exit_code = 1
      error_class_in = ["lint"]

`error_class_in` is a live key (`scripts/pod/table.py:149`, matched at `:581`).
`coder` is a legal head slot (`head_slots()` returns the five slot names of
`dev/pod/heads.toml`). The author's return IS `<task>-report.md`, so `report_of()`
judges it and conjunct 6 can pass again.

**SCOPE, STATED HONESTLY.** A row is admitted at task CREATION, so this binds my
NEXT brief onward. `[LJ-1.681]` through `[LJ-1.690]` are already in state and keep
the old table. I am not pretending otherwise and I have filed no retrofit: three
tasks have parked this way and none of them lost its mathematics.

**WHAT I DID NOT CHOOSE.** The maintainer offered two other cures at backlog item
37: change what `report_of()` prefers once a review companion exists, or stop
routing a lint-class failure to a critic in the PROGRAM rather than in my rows.
Both are program changes and neither is mine. Mine is the third and it is
sufficient at my end: if my rows never send a lint failure to a critic, the
program's row never sees the shape.

## THE FULL TABLE

Replace `NNN` with the task number. Priorities: lower number wins.

```toml pod-branches
[[branch]]
id = "go"
priority = 10
action = "done"
outcome = "go"

  [branch.when]
  exit_code = 0
  obligations_delta_max = -1
  heap_wall = false

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-NNN/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-NNN/review-of-LJ-*-*.md"]

[[branch]]
id = "lint-back-to-author"
priority = 13
action = "escalate"
head_slot = "coder"

  [branch.when]
  exit_code = 1
  error_class_in = ["lint"]

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-NNN/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-NNN/ProbeNNN.agda"]
  changed_files_none = ["agents/tasks/LJ-1-NNN/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-NNN/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. A heap wall is a resource fact and no critic can
# adjudicate it (MEASURED on LJ-1.534).
id = "heap-wall-park"
priority = 30
action = "park_and_split"

  [branch.when]
  heap_wall = true

[[branch]]
# Closes maintainer-backlog item 30, MEASURED on LJ-1.630. A real failed landing
# carries a named Agda error and NEITHER companion file, so both rows above miss
# it. This is the catch-all and it sits BELOW heap-wall-park.
id = "no-go-bare"
priority = 40
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
```
