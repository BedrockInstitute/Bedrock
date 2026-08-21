# Running the POD

**This is the ONE home for how the loop is operated.** Its audience is the repository
owner and the `maintainer` slot. A developer document, English only.

**IT IS NOT IN `AGENTS.md`, and that is the point.** Owner's ruling, 2026-08-19.
`AGENTS.md` is `cat`ed into every dispatch for all five slots, after the slot file,
so a sentence there is read by a mathematician who only needs to do mathematics and
by a coder who only needs to write Agda. **A worker does not operate the loop and
must not be told how to.** The Boundary stayed in `AGENTS.md`; this left it.

The design behind all of it is `dev/memos/LJ-4-pod-program-design.md`, which this file
never restates.

## How the loop is started, and it is a plain terminal

```sh
sh scripts/pod/keeper.sh                          # the keeper, which owns the loop
.venv/bin/python scripts/pod/pod.py tick --plan   # one pass, launching nothing
```

**START THE KEEPER, NOT THE LOOP.** `keeper.sh` runs `pod.py` as a direct child in the
same pane, so this pane's scrollback is the loop's own output. When the loop crashes the
keeper restarts it in place, with a backoff; after three fast failures it stops guessing
and asks the maintainer, then waits for `.pod-state/keeper-retry`.

**IT RESTARTS A CRASH AND NEVER A DECISION.** `pod run` exits 3 on rule (d)'s STOP and 4
on a startup refusal, and neither is restarted. Read the reason before you restart
anything: a stop is a decision with an author.

| exit | what it means | what to do |
|---|---|---|
| 0 | a signal arrived. Every running worker is untouched | start the keeper again |
| 1 | a crash | the keeper restarts it. Read the pane |
| 3 | STOPPED, a decision | read the newest `STOPPED` line in `dev/pod/transitions/`, then `pod.py resume` |
| 4 | it refused to start and never ticked | read the pane. The reason is printed |

## The hot restart

**`.pod-state/reload` reloads the loop between two ticks.** `cmd_run()` re-execs itself,
and it also reloads on its own when a `scripts/pod/*.py` change has settled for one full
tick. `os.execv` keeps the pid, so the keeper sees no death and every running worker is
untouched. A source that does not compile is REFUSED and the old image keeps running.

**A HOT RESTART IS NOT A RESUME.** A reload cures stale CODE. It does not clear
`.pod-state/STOPPED` or `.pod-state/DRAINING`.

## Starting it

    sh scripts/pod/start.sh

That is the whole of it. The script resumes the loop, opens a pane in the pod's workspace
and runs `keeper.sh` in it, and **it refuses when the resident name `pod-batch` is already
held**, which is the one step of a maintainer swap that is silent when it is skipped. Pass
`--no-resume` to start the keeper against a STOPPED loop, which exits 3 at once and is
only what you want when you mean to inspect rather than to run.

## Switching the maintainer head

    .venv/bin/python scripts/pod/pod.py maintainer                     # show it and the presets
    .venv/bin/python scripts/pod/pod.py maintainer --use claude        # edit the row
    .venv/bin/python scripts/pod/pod.py maintainer --handover grok     # do the whole swap

`dev/pod/heads.toml` carries `[maintainer_presets]`, and the command copies one into the
`[heads].maintainer` row. **The row is still the ONE home**: a preset is a set of fields
the owner has already approved, and nothing reads the table except this command.

**THE FOUR FIELDS MOVE TOGETHER, and that is the reason a preset exists.** A row carrying
`harness = "herdr-grok"` with `model = "claude-opus-5"` loads, dispatches, and fails inside
the pane; that is the failure class the read-back guard exists for, and it cannot catch it
for every harness. A preset that produces a row the loader would refuse is rejected before
the file is left changed.

**`--use` ALONE DOES NOT SWAP A RUNNING MAINTAINER.** AD26 makes a head change bind the
NEXT head, and the slot is RESIDENT: `ensure_maintainer()` starts one only when the herdr
name `pod-batch` is free, so a live session keeps the slot until it gives the name up.
`--use` is the file edit; `--handover` is the procedure.

**WHAT `--handover` DOES, in order.** It writes the row; renames the live agent to
`pod-batch-retired-<ts>`, which frees the name and KEEPS the pane, because a pane is a
record and an outgoing session mid-repair must be allowed to finish its sentence; starts
the new head through the same `ensure_maintainer()` the loop uses, so it arrives with
`AGENTS.md`, its slot file and a batch brief; prompts it to read
`dev/pod/maintainer-handover.md` first; and prompts the outgoing one that it is retired and
will receive no further batches.

## Stopping the whole pod, and swapping the resident maintainer

**FOUR THINGS RUN AND STOPPING THE LOOP STOPS ONE OF THEM.** A full stop is:

| what | how to find it | how to stop it |
|---|---|---|
| the alarm, when one is set | `ps aux \| grep wait-and-start` | `kill <pid>`, or interrupt its pane |
| the keeper | `ps aux \| grep keeper.sh` | it exits with the loop; kill it if it waits |
| the loop | `ps aux \| grep 'pod.py run'` | `pod.py stop`, or kill the runner |
| the agda watchdog | `ps aux \| grep agda-watchdog` | `kill <pid>`. Rule (f) then REFUSES every Agda task until it is back |

`.pod-state/STOPPED` stays where it is. It is what makes rule (f) refuse a dispatch on the
next start, and clearing it is `pod.py resume`, which is the owner's call.

**A SOFT STOP DRAINS.** `pod.py stop --soft` writes `.pod-state/DRAINING`. The live
loop then launches no new agent (rule (f) and rule (g)), keeps observing and
closing returns (rules (a1) to (e)), and STOPs when no task is RUNNING,
RETURNED or CHECKING. It writes `STOPPED` at that moment. Workers are not
killed. A hard `pod.py stop` still writes `STOPPED` at once, which makes the
loop exit on the next tick.

**SWAPPING THE RESIDENT MAINTAINER NEEDS ONE MORE STEP THAN A DISPATCHED HEAD, and
skipping it is silent.** AD26 makes a `dev/pod/heads.toml` change bind new tasks only,
which is the whole procedure for the four dispatched slots: edit the row, and the next
dispatch uses it.

The mathematician is also RESIDENT, owner's ruling 2026-08-20. It is addressed by
the herdr agent name `pod-math`. `ensure_mathematician()` starts it once from
`agents/tasks/POD-MATH/POD-MATH.md`. Rule (f) and rule (g) then prompt that same
agent. One turn at a time: a second mathematician task, or a refill, waits while
the agent is `working` or `blocked`. Isolation is off for this slot: it writes
briefs in the main tree. Swapping it is the same procedure as the maintainer:
rename `pod-math` so the name is free, then the next tick starts the new head.

The maintainer is RESIDENT and is addressed by its herdr agent NAME, `pod-batch`.
`maintainer_alive()` answers TRUE while ANY agent holds that name, whatever kind it is, so
until the outgoing session gives the name up:

- `ensure_maintainer()` sees a live maintainer and never starts the new head, and
- every batch, every close notification and every keeper alarm reaches the OUTGOING
  session.

MEASURED 2026-08-19 during the move to grok: a feed sent to test the new head landed in
the outgoing Claude session. The order is therefore:

1. Stop all four things above.
2. Edit the `maintainer` row in `dev/pod/heads.toml`. It is the owner's file (AD26).
3. **Retire the outgoing session** so `pod-batch` is free. Confirm with `herdr agent list`
   that no row carries that name.
4. `pod.py resume` and start the keeper. `ensure_maintainer()` starts the new head on the
   next tick and hands it the batch brief, which is `cat`ed behind `AGENTS.md` and
   `dev/pod/instructions/maintainer.md`.

## `pod.py` is a program and not an agent

Do not start it from inside a coding-agent session in the hope that the session's own
model or effort applies: it does not, and the session would only be a shell. **The
program launches all five heads itself**, each with the model and effort of its row in
`dev/pod/heads.toml`.

## The panes open and close themselves

A dispatch splits a pane in the keeper's own workspace and starts the head inside it, so
a running head is already in front of you. A clean finish closes that pane; every other
ending keeps it, because a dead agent's terminal is the only record of how it died.
**Nothing ever takes your focus**: the program splits and starts, and never calls
`pane focus`.

**THE ONE PANE THAT NEVER CLOSES IS THE MAINTAINER'S**, because it is resident. That is
what makes it reachable at any hour.

**WHERE A NEW PANE LANDS IS ONE RULE WITH TWO PHASES, and you can ask it without running
a dispatch.** `scripts/pod/pane-slot.py` owns it. While there is room for another column
at `MIN_COL_WIDTH`, a dispatch opens one by splitting RIGHT off the RIGHTMOST column, so
the columns grow left to right and every one is the same width. Once they are open, a
dispatch deepens the SHALLOWEST column, leftmost on a tie, by splitting its LAST pane
DOWN. **There is no alternation inside either phase**: the layout goes right, right,
right, then down, down, down.

    .venv/bin/python scripts/pod/pane-slot.py --base <PANE> --plan

That prints the direction, the source pane and the column count, and changes nothing.

**IT USED TO ALTERNATE and the result was measured broken.** The old rule split DOWN
whenever a half-empty column existed and RIGHT otherwise, and it opened the new column off
a pane that had already been split down. MEASURED 2026-08-19 over six dispatches: columns
145, 73, 36 and 36 wide, panes 62, 31, 16 and 8 rows tall, and each column's BOTTOM pane
spanning every column opened after it. Twelve dispatches under the rule above: every
column 58 wide, and no width moves once the columns are open.

```sh
herdr agent list                     # every live head and its pane
herdr agent prompt pod-batch "..."   # send one message without leaving your pane
herdr agent attach pod-batch         # only from ANOTHER workspace; in the pod's own
                                     # workspace the pane is already on your screen
```

**A FINISHED AGENT IS NOT A DEAD ONE.** MEASURED 2026-08-18: after its turn a head
reports `agent_status: done`, and a second `herdr agent prompt` is accepted and answered
on the same session. Only `herdr pane close` ends an agent.

**A PROMPT TO A BUSY HEAD QUEUES AND NEVER INTERRUPTS** (`dev/LESSONS.md` C-61): it is
read when the head finishes its current tool call, and once cost 4.25 hours. To reach a
busy head, end what is keeping it busy first.
