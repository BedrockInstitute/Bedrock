# The standing REFILL brief, rule (g)

**This file is a STANDING BRIEF and the program never rewrites it.** Rule (g) of
`pod_tick()` sends it when a slot is free AND `dev/pod/queue.toml` holds no
dispatchable entry. Amendment A11 of `dev/memos/L9-pod-program-design.md` rules it.

**WHY IT EXISTS.** DD17 said an idle agent slot is a defect. The POD's rule set
supersedes DD17, and gap M12 recorded the loss: `admits()` caps concurrency and
nothing requires the queue to be non-empty, so an empty queue idles the whole loop
and no digest field counts it. The owner ruled on 2026-08-17 that the cure is
mechanical, not a written clause.

**WHAT THE PROGRAM DECIDES AND WHAT IT DOES NOT.** The program decides only that
somebody must be asked. It decides nothing about the work. AD1 stands. This is the
same shape as AD15's maintainer trigger and AD16's automatic re-dispatch, which the
design already admits.

## HEAD

head_slot: mathematician
machine: shared

## THE OBLIGATION

Write the next task or tasks into `dev/pod/queue.toml`, so the loop has work.

## OBLIGATION NAMES

None. This task writes no Agda and closes no proof obligation. Fact 3's witness
meter reads an empty obligation list and returns the vacuous pass of section 4.7.

## SCOPE (write)

- `dev/pod/queue.toml`
- `agents/tasks/<CODE>/<CODE>.md`, one per task you queue

## PREMISES

1. **The queue is empty or holds nothing dispatchable, and a slot is free.** The
   program measured both before it sent this. You do not re-check them.
2. **The route is `dev/PLAN.md`.** Section 0 says where the work stands and section
   11 carries the goal registry. Both are live documents.
3. **`[LJ-2.5]` is the open architecture question.** The two towers and the bridge
   are a CANDIDATE and not a ruling, and only a measurement settles them. Clause W1
   is the rule.

## WHAT IS DELIVERED ALREADY

`dev/PLAN.md` section 0 and its open-work list. Read them before you write a row.
The transition log holds every task the loop has closed, with its outcome.

## WHAT IS MISSING

That is your question to answer.

## THE REASONING

Read `dev/PLAN.md` section 0, the open-work list and the most recent DONE lines of
the transition log. Pick the work that unblocks the most, and prefer a task whose
obligation list you can state as names. **Queue the smallest task that makes real
progress**, never a large one you cannot price.

**A STOP IS A DELIVERABLE HERE TOO.** If the route is genuinely blocked on an owner
ruling, queue nothing, say so, and name the ruling. The digest prints the block and
the owner reads it. **Do not invent work to fill a slot.** An empty queue with a
named reason is a better state than a queued task nobody wanted.

## WHAT GO AND NO-GO EACH EARN

**GO** earns one or more queue entries, each with a brief the pre-flight accepts.
**NO-GO** earns a named blocker and the ruling it waits on, which is worth as much:
it converts an idle loop from a silent state into a reported one.

## ARCHIVE

**Read these before you queue a mathematical task, and name what you took at
`file:line` in an ARCHIVE USED section of your return.** The retired route left four
records, and a task queued without them repeats work that is already delivered.

- `archive/src/` holds the retired Agda, one directory per archival event.
  `archive/src/2026-08-09-rud-route/` is the retired route. A chapter there may
  already carry the content a new task would rebuild.
- `archive/dev/TASKS-archived.md` says what each retired dispatch found.
- `archive/dev/JOURNAL-archived.md` says why, and it carries the episodes.
- `archive/dev/DECISIONS-archived.md` holds the archived `D` rulings. The live rulings
  are the written clauses of `dev/memos/L9-pod-program-design.md` section 3.1.

**If nothing in the archives bears on the task you queue, say so in one line and name
the archives you read.** A `NO HIT` is a first-class result here.

## LITERATURE

`dev/literature/` holds the digested mathematics: `digest.md` for the orthodox route,
`j-hierarchy.md` for condensation, `devlin-errata.md` for the known errors in the
primary text, and `BIBLIOGRAPHY.md` for what was fetched and what consumed it.

**THIS TASK QUEUES WORK AND IT PROVES NOTHING, so it reads the literature only to
price a candidate task.** Read `BIBLIOGRAPHY.md` to learn whether the mathematics a
candidate needs is digested already. When it is not, say so in the queue entry: the
task you queue then carries a literature step of its own. Name in a LITERATURE USED
section of your return what you read, and WHY NOT for anything you skipped.

## BRANCHES

```toml pod-branches
[[branch]]
id = "queued"
priority = 10
action = "done"
outcome = "go"

  [branch.when]
  exit_code = 0
  obligations_delta_max = 0

[[branch]]
id = "blocked"
priority = 15
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 0

[[branch]]
id = "attacked"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
```
