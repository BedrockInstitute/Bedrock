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

**IT ALSO STARTS THE OMLX WATCHDOG, owner's ruling 2026-08-24, and this step never blocks
the rest.** `scripts/ops/omlx-watchdog.sh` runs detached, not in a pane, and its own pidfile
guard makes a repeat `start.sh` a no-op on this step rather than a duplicate. Unlike the
keeper, its absence is never fatal to a start: read "The oMLX watchdog" below for what it
does and why `start.sh` only reports on it rather than refusing when it is missing.

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

**FIVE THINGS CAN RUN AND STOPPING THE LOOP STOPS ONE OF THEM.** A full stop is:

| what | how to find it | how to stop it |
|---|---|---|
| the alarm, when one is set | `ps aux \| grep wait-and-start` | `kill <pid>`, or interrupt its pane |
| the keeper | `ps aux \| grep keeper.sh` | it exits with the loop; kill it if it waits |
| the loop | `ps aux \| grep 'pod.py run'` | `pod.py stop`, or kill the runner |
| the agda watchdog | `ps aux \| grep agda-watchdog` | `kill <pid>`. Rule (f) then REFUSES every Agda task until it is back |
| the oMLX watchdog, when you started one | `ps aux \| grep omlx-watchdog` | `kill <pid>`. NOTHING refuses a qwen dispatch after that; the drift comes back and the 400s with it |

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

## The oMLX watchdog

    scripts/ops/omlx-watchdog.sh --once --dry-run   # one pass. It decides and restarts nothing
    scripts/ops/omlx-watchdog.sh                    # the loop
    _build/tools/omlx-watchdog.log                  # every decision it took, and why

**IT IS NOT RUNNING UNTIL YOU START IT, and no part of the program starts it.** That is
the one way it differs from the agda watchdog, which `pod run` starts and confirms every
tick. The reason is below.

**WHAT IT CURES.** `omlx-server` does not return its MLX buffer pools to the OS, so its
idle memory footprint rises with uptime, and that footprint is subtracted from the 56 GB
`iogpu.wired_limit_mb` cap before qwen gets any context at all:

    usable context ceiling = (56 GB - idle footprint) / 218,372 bytes per token

MEASURED overnight on 2026-08-23: the footprint drifted 12.4 GB in fourteen hours and the
ceiling fell from 176K tokens to 100K. Seven of thirteen qwen dispatches in that window
died on a hard HTTP 400 (`stopReason: error`, `usage.totalTokens: 0`), each losing the
whole session's work with no retry from `pi`. Those are the
`fallback:Qwen3.8-27B-oQ4e-mtp` parks in `dev/pod/transitions/2026-08.jsonl`. One restart
of the app on 2026-08-24 11:20 took the footprint from 41.41 GiB to 16.25 GiB in under
thirty seconds.

**WHEN IT RESTARTS.** Two triggers, and the first is the one that fires.

| trigger | value | where the value comes from |
|---|---|---|
| idle footprint | at or above 24 GB | a context that settles near 146,000 tokens costs 31.88 GB, so the baseline must stay under 56 - 31.88 |
| time backstop | 3.5 hours of ACTIVE qwen dispatch since the last restart | the same 2026-08-23 window, RE-MEASURED from the transition log: 6.84 active hours for 12.4 GB, so 1.81 GB per active hour, and 6.55 GB of margin is 3.6 hours |

Active hours are read from `dev/pod/transitions/`, by summing the RUNNING to RETURNED spans
whose model is qwen. Wall clock since the last restart was the simpler proxy and it is
rejected: idle uptime does not move the footprint, so a wall clock fires after a quiet
night that cost nothing.

**IT NEVER RESTARTS UNDER A LIVE AGENT.** A restart mid-run gives that agent a
`Connection error` and the run is a total loss, which is worse than the drift. The gate is
herdr's own `agent_status`, asked twice with thirty seconds between, and it also requires
the oMLX server log to have been silent for ninety seconds. **Every unreadable answer
counts as BUSY.** `pgrep -f "pi --mode json"` cannot see a `pi` agent at all, because it
runs inside a herdr pane.

**IT RESTARTS THE APP AND NEVER THE SERVER ALONE.** MEASURED 2026-08-24 11:16: a `kill -9`
of `omlx-server` was not answered by the parent for five minutes and `open -a oMLX` did
nothing, because the app was already running; the service was down about seven minutes.
`killall oMLX` is the only kill in the script and it cannot match `omlx-server`.

**`pod.py` DOES NOT GATE ON IT, and that is a decision.** Rule (f) refuses every Agda task
while `scripts/ops/agda-watchdog.sh` is down (A13) because that absence is a MACHINE
hazard: one runaway Agda takes the whole box and every agent on it. This watchdog's
absence is not that. It costs at most the one dispatch that hits the wall, the loss is
already routed (the park falls the task through to glm-5.3), and the record is already
visible in the transition log and the digest. A refusal built on `pgrep omlx-watchdog`
would instead send EVERY qwen dispatch to the fallback for as long as nobody had started a
shell script, which is a routing change wearing a safety check's clothes. `_omlx_excluded()`
is not a precedent for it either: that one fires on a lock a live `make check` holds and
then releases, and a watchdog nobody started clears itself never.

**WHAT WOULD CHANGE THE CALL**, stated so the next reader does not have to re-derive it: a
qwen 400 that costs more than the one task, or a park rate that stays high with the
watchdog running.

**ONE SETTING IS COUPLED TO IT AND LIVES OUTSIDE THIS REPOSITORY.** `contextWindow` for
qwen in `~/.pi/agent/models.json` is 150,000, which leaves 6.67 GB of drift tolerance;
135,000 leaves 9.94 GB. **Without periodic restarts in place, 150,000 is the wrong
setting.** The watchdog reads the live value at start and writes it to its log, and it says
so loudly when the value is above 150,000, because the 24 GB trigger is derived for 150,000
and is too loose above it. It never writes that file, and it never writes
`~/.omlx/model_settings.json` or `iogpu.wired_limit_mb` either.

## The SUPERHEAVY cap, and it is not a task tier

    .venv/bin/python scripts/pod/superheavy-check.py src/Everything.lagda.md

**A MANUAL TOOL FOR THE RESIDENT MAINTAINER, OWNER'S RULING 2026-08-25, and nothing
else ever calls it.** WIDE (2 GB) and HEAVY (4 GB) are the two tiers a brief's
`agda_tier:` line may declare (`scripts/pod/facts.py TASK_TIERS`) and the dispatch
loop admits automatically. `dev/pod/heads.toml [tiers.superheavy]` (8 GB) is
deliberately absent from `TASK_TIERS`, from `heads.py`'s tier validation, and from
`[tiers.shared]`'s heap-sum budget, so no brief and no automatic dispatch can ever
reach it.

**WHY IT EXISTS.** MEASURED 2026-08-25 on `[LJ-1.628]`: an owner-approved, 10-line,
no-new-imports addition to `src/L/Constructible.lagda.md` still heap-walled the
whole tree at HEAVY's `-M4g`, 166.5 s and 4.38 GiB, on a WARM interface cache. Not
every landing that clears the owner's spec-surface approval also clears HEAVY's
cap, and this is how the maintainer checks which before spending a dispatch on it.

**THE GATE IS EXISTENCE AND NEVER A MEMORY FLOOR**, unlike `check-omlx-quiet.py`'s
2026-08-24 relaxation to a percentage floor: that gate protects a routine, frequent
`make check` run. This is a rare, hand-invoked, 8 GB commitment, and the owner's
ruling is narrower on purpose: no qwen (`omlx-server`) running at all, checked the
same way `check-omlx-quiet.py`'s `_omlx_live()` checks it, with no `--assume-quiet`
escape when the sensor itself is unreadable.

## The shelf, and putting a task back on the table

    .venv/bin/python scripts/pod/pod.py unshelve LJ-1.541 --why "the restructuring landed"

**A SHELVED TASK IS ONE THE MATHEMATICIAN HAS RULED SETTLED.** Owner's ruling,
2026-08-24 (A30). Its obligation is delivered by another task, so another attempt buys
nothing, and DONE would be a false record because nothing measured it. It keeps its
worktree, its park record and its whole history; it stops holding a `parked_max` slot;
and the maintainer's batch brief names it as a code and asks for nothing.

**ONLY THE MATHEMATICIAN DECLARES ONE**, by writing `dev/pod/shelve-request.toml`, and
the request is refused unless it carries a `file:line` and a `reopen` condition. The
honoured declaration is kept at `dev/pod/shelf/<CODE>.toml.shelved`, which is the record
of who ruled what and on what evidence. `pod.py status` prints the shelved count beside
the parked one.

**UN-SHELVING IS YOURS AND IT GOES TO PARKED, NEVER TO READY.** A straight READY would
re-dispatch the task into whatever made it park, with no new information. Coming back
through PARKED costs a `parked_max` slot again, which is the honest price of asking for
the loop's attention. `--why` is required: the log line is the only record that the
reversal had a reason. `pod.py resume --retry` never un-shelves, and says so when you
name a shelved code.

**A `quota:` PARK NO LONGER STOPS THE LOOP**, ruled the same day and part of the same
amendment. A vendor's five-hour window re-opens on its own clock, so it no longer counts
toward `parked_max` and no longer feeds the maintainer. It is still a park, still in
`pod.py status` and still in the digest.

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
