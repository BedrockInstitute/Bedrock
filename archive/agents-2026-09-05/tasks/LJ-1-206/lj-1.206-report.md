# LJ-1.206 report: measure herdr's wait supersession, and land it if it holds

## VERDICT: DOES NOT HOLD. I landed nothing.

The wait protocol is not superseded. I measured the socket API on this
machine. `events.wait` reproduces the at-once-idle flaw that makes the
two-phase wait necessary. It also rejects every non-status event match, so a
death is not waitable through it. The one documented cure for the at-once
flaw, the embedded `agent.prompt` wait with its five-second state-change
rule, cannot be measured here: it needs a prompt to a live agent, and the
brief forbids touching agents. P-l binds: a capability measured elsewhere is
a hypothesis here.

The notification half does hold. A single `events.subscribe` socket delivers
one status-change event per agent, live, with no re-arming. I observed it
deliver a sibling's return while other agents kept working. But landing it
is dear: it is a new long-lived socket client, its death re-creates the
silent-return failure this file was built to refuse, and the durable
`returns.log` and the registry stay. Per the abort criterion, a supersession
that holds but is dear to land is reported and not landed.

So the honest result: the wait protocol keeps every line, with a reason. The
question `[LJ-1.203]` left open is now answered by measurement, and the
answer retires it.

## The four questions

### Q1. Does the automation layer deliver ONE notification PER AGENT, without a waiter to arm and re-arm?

**MEASURED. Yes, for `events.subscribe`; no, for `events.wait`.**

Command:

```sh
.venv/bin/python lj206-waitprobe.py subscribe 75 w7:p17 w7:p13 w7:p14 w7:p15 w7:pV w7:p1
```

This armed one subscription with pane-scoped `pane.agent_status_changed`
filters for six panes. The ACK returned at once. Events arrived later:

```text
[  61.5s] {"agent": "pi", "agent_status": "idle", "pane_id": "w7:p14", ...}  event: pane.agent_status_changed
[  66.0s] {"agent": "claude", "agent_status": "working", "pane_id": "w7:p1", ...}  event: pane.agent_status_changed
[  95.8s] {"agent": "claude", "agent_status": "idle", "pane_id": "w7:p1", ...}  event: pane.agent_status_changed
```

One connection, many agents, per-agent push events. Nothing was re-armed.

Three caveats, each measured:

1. `events.wait` is one-shot. It takes one match and returns one event
   (`EventsWaitParams` has `match_event`, from `herdr api schema --json`).
   For N agents you arm N waits.
2. The pane-scoped filter exists only for `pane.agent_status_changed`,
   `pane.output_matched` and `pane.scroll_changed`. The subscriptions for
   `pane.exited`, `pane.closed` and `pane.agent_detected` carry no pane
   filter in the schema, and they replay recent events for OTHER panes. I
   subscribed to one pane, w7:p13, and received `pane_closed` replays for
   w7:p12, w7:pZ and w7:p14, none of which I subscribed to. Those three
   subscription types are global and noisy.
3. The status-change event data carries the agent KIND (`"agent": "pi"`),
   not the agent name. A subscriber maps an event to a task through the
   pane_id, by `agent get` or a maintained map.

### Q2. Does it survive the case that broke ours: several agents live, one slow, the others returning first?

**MEASURED. Yes.**

The same subscription delivered the sibling's return while the slow agents
kept working:

```text
[  61.5s] pane.agent_status_changed -> idle  for w7:p14 (agent lj-1-207)
[  61.6s] pane_closed                       for w7:p14 (the driver closed it on clean finish)
[  95.8s] pane.agent_status_changed -> idle  for w7:p1
```

At 61.5s my own pane, w7:p1, and the other siblings were still live. The
socket kept delivering. This beats both hand-rolled forms: `wait` reports
once and exits, and `wait --all` is refused with more than one live agent.

The caveat is the same one `[LJ-1.203]` named: a subscriber is a new
long-lived process. If it dies, the returns are silent. The current waiter
is not the agent's parent, and its death is harmless
(`dispatch.py:1885-1891`). A subscriber needs the same property plus the
durable `returns.log`, which stays.

### Q3. Does it distinguish a RETURN from a DEATH from a BLOCK?

**PARTIAL. RETURN and BLOCK yes, DEATH no. The death half is REFUTED.**

RETURN. A status change to `idle` or `done` fires
`pane.agent_status_changed`. MEASURED: the w7:p14 event above.

BLOCK. A status change to `blocked` fires the same event type with
`agent_status: "blocked"`. The schema's `pane.agent_status_changed`
subscription accepts an `agent_status` filter. DOCUMENTED and MEASURED in
the schema. Not observed live: no agent on this machine is blocked now
(`herdr agent list`, this run).

DEATH. Three measurements:

```sh
.venv/bin/python lj206-waitprobe.py wait-event pane_exited w7:p17 none 8000
```
```text
elapsed=0.00s {"error": {"code": "unsupported_event_wait_match",
  "message": "events.wait currently supports pane agent status matches"}}
```

```sh
.venv/bin/python lj206-waitprobe.py wait-event pane_agent_detected w7:p13 none 5000
```
```text
elapsed=0.00s {"error": {"code": "unsupported_event_wait_match", ...}}
```

`events.wait` accepts only `pane_agent_status_changed` matches. The schema's
`EventMatch` lists 19 event kinds; the implementation rejects 18 of them.
The schema overstates the binary. A death is not waitable.

The death subscriptions exist but are global and replaying, and cannot be
scoped to one pane. So there is no per-agent death signal through the
automation layer. The driver's own death guard, the `agent get` existence
check (`dispatch.py:967-975`), has no herdr event counterpart.

One more subtlety: the driver closes the pane on a clean finish
(`dispatch.py:985-990`), and that close emits `pane_closed`. A death keeps
the pane open. So `pane_closed` alone cannot tell a clean return from a
death. The event ORDER does: idle before close is clean, close without idle
is a death. The subscriber must have been live at the time.

### Q4. Can it interrupt a BUSY agent?

**REFUTED. No.**

Commands:

```sh
herdr agent prompt --help
herdr agent
herdr api schema --json
```

The help text has no `--interrupt` flag. The agent subcommand list has no
`stop` and no `kill`. The schema's `AgentPromptParams` has three fields:
`target`, `text`, `wait`. The word "interrupt" appears nowhere in the
socket-api docs or the agent-automation docs (grep, this run). The
agent-automation page says `agent prompt` "can prompt an agent that is
already working", which is the queued-prompt behavior that cost 4.25 hours
on 2026-08-14.

`send-keys ctrl+c`: UNMEASURED as a stop. Two `send-keys C-c` did not stop
a working pi agent (episode 2026-08-14, recorded in the skill). The
automation layer adds no interrupt primitive over the CLI.

So the finding "a prompt is not a stop" stands against herdr, and the
automation layer does not supersede it.

## The before-and-after acceptance table

I made no edit. `dispatch.py` is byte-identical to the aside copy:

```sh
cmp .claude/skills/codex-dispatch/dispatch.py agents/tasks/LJ-1-206/dispatch.py.before-lj206
```

The aside copy is at `agents/tasks/LJ-1-206/dispatch.py.before-lj206`
(2,319 lines). `python3 -m py_compile` passed before and after (there was
no after edit). The table is the baseline, and after == before by
byte-identity.

| Brief | Kind (derived) | check rc | Result |
|---|---|---|---|
| agents/tasks/LJ-1-203/LJ-1.203.md | recon | 0 | well formed |
| agents/tasks/LJ-1-204/LJ-1.204.md | probe | 0 | well formed |
| agents/tasks/LJ-1-205/LJ-1.205.md | recon | 0 | well formed |
| agents/tasks/LJ-1-198/LJ-1.198.md | probe | 0 | well formed |
| agents/tasks/LJ-1-190/LJ-1.190.md | review | 0 | well formed |
| agents/tasks/LJ-1-157/LJ-1.157.md | review (control) | 1 | refused: missing C-22; no DD4 |

The control is refused for the SAME two reasons in both runs, and the five
passing briefs pass in both runs. `dispatch.py status` prints every banner:
`Agda slots`, `agents live`, `!! 1 RETURN(S) NEVER REPORTED: LJ-1.195`,
`6 herdr agent(s) outside this registry`, and `!! NO WAITER IS ARMED`.
Nothing changed, so nothing could change.

## What I would do next

1. Measure the embedded `agent.prompt` wait on a live test agent, outside
   the driver. The skill's own rule says a herdr-measuring task must run
   outside the driver. That measurement decides whether the two-phase wait
   can shrink: if the embedded wait's five-second state-change rule fires
   as documented, one phase may be enough; if it fires at once like
   `events.wait`, the two-phase pattern stays forever.
2. Keep the polling waiter and the two-phase wait as they are. The
   `returns.log`, the singleton, and the re-arm contract stay.
3. If a push channel is ever wanted, price it as new code with a death
   contract, not as a swap. The subscriber must not be the agent's parent,
   and the durable log must stay.

## DD4

The waiter and the wait protocol are two different ends, and the measurement
separates them.

The polling waiter is generic infrastructure. herdr maintains a push event
channel. Keeping the 15-second poll hand-rolled is paying twice, and the
push channel is measured to work. This end is a delegation candidate, but
landing it is dear and the migration is not funded.

The wait protocol is Bedrock law shaped by measurement. It exists because a
one-phase wait was measured wrong on 2026-08-13, twice. I measured that
`events.wait` reproduces the same at-once-on-current-state behavior
(0.00 seconds on an already-idle agent), and that it cannot wait on a
death. A general tool that reproduces the flaw cannot carry the guard. This
end is not a delegation candidate.

The refusals were never in question. They encode Bedrock rulings, and the
tool does not know the rulings. No refusal was weakened or deleted, because
none was touched.

## ARCHIVE USED

- `agents/tasks/LJ-1-203/lj-1.203-report.md`, read whole. Taken: the
  two-kind split, the five questions, and the one supersession this task
  was sent to measure. The report's "What I could not settle" names the
  at-once-idle question and the events.wait question; both are now measured.
- `.claude/skills/codex-dispatch/dispatch.py`, read whole (2,319 lines).
  Sites: the three-failure header `:1-22`; the herdr driver `:818-1032`,
  with the fresh-pane retry `:886-896`, the two-phase wait `:928-949`, the
  blocked check `:960-965`, the death guard `:967-975`, the
  close-on-clean-finish `:985-990`; the resume driver's one-phase-wait
  lesson `:997-1001`; `_wait_for` `:1201-1231`; `cmd_queue` `:1247-1331`,
  whose `--wait` is accepted and ignored; the waiter singleton `:1821-1884`;
  `cmd_wait` `:1885-2002`, with the one-report contract and the `--all`
  refusal; `warn_if_unarmed` and the `returns.log` writer.
- `.claude/skills/herdr/SKILL.md`, read whole (195 lines). Taken: the
  lifecycle states `:54,58`, the `--wait` and stalled rules `:128-130`, the
  safety rules `:187-195`.
- `.claude/skills/dispatch-herdr/SKILL.md`, read whole. Taken: the waiter
  contract, the blocked ruling, the ten mistakes, and the rule that a
  herdr-measuring task must run outside the driver.
- `agents/tasks/LJ-1-205/lj-1.205-report.md`, read whole. Taken: the C4
  blocked finding, and the byte-identity of `herdr --skill` and the
  installed skill.
- The measurement corpus under
  `.claude/skills/codex-dispatch/.state/logs/`. This is the corpus the
  brief says nobody mined. Sites: `LJ-1.206-20260814-160523.log`, the first
  attempt's own self-kill: the driver waited `working` (seq 229), then
  matched `idle` (seq 241) while the agent was still working, closed the
  pane, and `returns.log` recorded it clean at 16:10:54. That log is the
  live proof of the false-idle failure mode the two-phase wait cannot
  fully close. `LJ-1.208-20260814-161001.log`: `agent wait --until working
  --timeout 120000` timed out and the driver kept the pane for forensics.
  `herdrtest1-20260813-104059.log` and the two resume logs: the two-phase
  wait working on a real codex agent, and `agent_not_found` on resume after
  the pane closed. `LJ-1.124-20260813-093733.log`: the DIED path. Counts
  across all 452 logs: 27 clean `HERDR done` closes, 1 DIED, 1
  never-started-working, 1 name collision, 2 existence-check failures.
  `returns.log`, 389 lines, is the durable notification record.
- `agents/tasks/LJ-1-206/probe_socket.py` and `LJ-1.206.md`, read. The
  first attempt's probe and brief. I used the probe's read-only commands
  only (ping, get). The probe is a tracked record and is left in place.
- Why not the retired route's archives: nothing in `archive/dev/` bears on
  a herdr tooling question. The retired dispatch mechanics predate herdr.

## LITERATURE USED

- `https://herdr.dev/docs/socket-api/`, fetched this run, read whole. The
  raw methods, the embedded prompt wait, `events.subscribe`, `events.wait`,
  event subscriptions, waiting for state, protocol stability. The site and
  the binary agree on the method surface and the stalled rule. They
  DISAGREE in one place, measured: the schema's `EventMatch` lists 19
  event kinds, and the implementation rejects all but
  `pane_agent_status_changed` with `unsupported_event_wait_match`. The
  schema overstates the binary.
- `https://herdr.dev/docs/cli-reference/`, fetched this run, read whole.
  The agent command surface, the `--wait` and `--until` semantics, the
  stalled rule. The help text and the page agree, and neither has an
  interrupt.
- `https://herdr.dev/docs/agent-automation/`, fetched this run, read
  whole. The three primitives, the control-surface table, the recipe that
  `agent prompt` "can prompt an agent that is already working", and the
  stalled rule. No interrupt is mentioned anywhere on the page.
- `herdr --skill` against the installed file: byte-identical, MEASURED this
  run. The installed skill is the version the binary ships. The site's
  docs pages describe the same 0.8.0 surface.
- WHY NOT the rest of `dev/literature/`: nothing in it bears on a herdr
  tooling question. DD18 is satisfied by this section.

## What was measured this run, and what was not

Measured (all read-only): `herdr --version` prints `herdr 0.8.0`; `herdr
--skill` is byte-identical to the installed skill; `herdr agent` lists no
stop and no kill; `herdr agent prompt --help` has no interrupt flag;
`herdr api` has only `snapshot` and `schema`; `herdr api schema --json`
prints protocol 19 with `AgentPromptParams` = target, text, wait;
socket `ping` returns protocol 19; `events.wait` fires at once (0.00s) on
an already-idle agent; `events.wait` waits and times out (8.06s) for a
state the agent does not hold; `events.wait` rejects `pane_exited` and
`pane_agent_detected`; `events.subscribe` delivered a live return event for
a sibling at 61.5s and another agent's at 95.8s on one subscription;
`pane.closed` subscriptions are global and replay recent closes of
unsubscribed panes; the status-change event data carries the agent kind,
not the name; `dispatch.py check` on six briefs; `dispatch.py status`
prints every banner; no agent is blocked on this machine.

Not measured: the embedded `agent.prompt` wait and its five-second
state-change rule. It needs a prompt to a live agent, which the brief
forbids. UNMEASURABLE HERE. A live `blocked` transition event and a live
death event: no agent on this machine is blocked, and I will not create a
death. The pane-scoped filter for `pane.output_matched` and
`pane.scroll_changed`: not relevant to the wait protocol.

Nothing was launched. No live agent was prompted, keyed, renamed, moved or
closed. No pane was created. No file in `src/`, `scripts/`, `dev/` or
`.claude/` was changed. The only file I wrote is this report. The aside
copy `agents/tasks/LJ-1-206/dispatch.py.before-lj206` is a backup taken per
the acceptance protocol; it is a copy of an untracked file and is left
beside this report for the orchestrator's use.
