# LJ-1.203 report: can herdr Agent Automation replace `dispatch.py` and its SKILL?

## Verdict in one sentence

Agent Automation does NOT replace the dispatch machinery; it OPTIMIZES the wait
and the resume path, it COMPLETES the notification and the restore story, and
it cannot carry any refusal, so the honest verdict is OPTIMIZE and COMPLETE,
never REPLACE.

The evidence for that verdict is the two-kind split below. 74 percent of
`dispatch.py` is Bedrock law. No herdr feature can supply it. Of the 15
percent that compensates for what herdr lacks, only the wait protocol has a
documented herdr supersession, and that supersession is not measured.

## The two-kind split of the 2,319 lines

The brief names 2,276 lines. The file is 2,319 lines today. The difference is
the blocked-agent census banner that `[LJ-1.205]`'s finding added
(`dispatch.py:1682-1710`). The count below is of the file as it stands.

The rule I used: a line is kind 1 when its reason for existing is a gap in
herdr that herdr 0.8.0 could fill. A line is kind 2 when its reason for
existing is a Bedrock ruling. A line is neutral when it is transport, CLI
plumbing, or the direct codex and pi paths that do not touch herdr at all.
Mixed subsystems are split and the split is marked.

| Subsystem | Lines | Kind | Why |
|---|---|---|---|
| Header, docstring, imports | 77 | neutral | transport |
| Model and policy constants | 43 | 2 | DD17 switch wiring, the model rule |
| PI_STREAM constant | 10 | neutral | the pi path, not herdr |
| herdr kind and workspace constants | 60 | 1 | herdr name, kind and workspace interface |
| `herdr_name` | 7 | 1 | name mapping for herdr's lowercase grammar |
| Agda ceiling and SESSION_RE | 36 | 2 | C-12's ceiling; the scrape is shared |
| Registry lock, load, save | 58 | 2 | the audit trail's durability, D1 and D6 |
| `proc_start`, `alive`, `final_is_clean` | 93 | 2 | liveness correctness, D2 and D5, gate-ready safety |
| Agda holders and pileup | 43 | 2 | C-12 slot accounting and the pileup audit |
| `strays` | 75 | 2 | the unmanaged-agent audit, D12 |
| `herdr_agents` | 21 | 1 | thin wrapper over `herdr agent list` |
| `sweepable_panes` | 53 | mixed | 30 mechanism (1), 23 evidence rules (2) |
| `close_pane` | 9 | 1 | thin wrapper |
| Validation-head regexes | 13 | 2 | refusal patterns |
| `check_model` | 13 | 2 | the dead-model refusal, D3 and D17 |
| `launch_defects` and `validate` | 113 | 2 | the refusals |
| Launch head, the launch-time refusals | 88 | 2 | brief, territory and slot refusals |
| The herdr driver block | 215 | 1 | wait protocol, retries, existence checks |
| The pi path | 46 | neutral | the pi harness, not herdr |
| The codex paths | 12 | neutral | the fallback harness |
| Launch tail, env and Popen and registry | 70 | mixed | 30 transport (neutral), 30 audit write (2), 10 scrape |
| `announce` | 32 | 2 | the durable returns log |
| `_wait_for` | 31 | 1 | the polling wait |
| `cmd_run` | 15 | 2 | the refusal entry point |
| `cmd_queue` | 85 | mixed | 30 detached waiter (1), 50 D9 and territory (2) |
| Territory parsing | 109 | 2 | the write-scope intersection, C-25 |
| `cmd_resume` | 54 | mixed | 20 herdr-by-name resume (1), 30 harness-from-record (2) |
| Stall header and `stall_note` | 111 | 2 | the C-22 heuristic |
| `unregistered_returns` | 34 | 2 | the PLAN section 6.0 check |
| `cmd_status` | 166 | mixed | 20 sweep report (1), 140 census and banners (2) |
| The no-harness-check comment | 15 | neutral | a record |
| Waiter singleton machinery | 64 | mixed | 50 PID-file singleton (1), 14 warn_if_unarmed (2) |
| `cmd_wait` | 118 | mixed | 60 polling loop (1), 55 refusals and log (2) |
| `cmd_gate_ready` | 22 | 2 | the full-tree gate refusal |
| `dd4_defects` | 38 | 2 | the DD4 gate |
| `survey_defects` | 57 | 2 | the DD18 gate |
| `brief_kind` | 69 | 2 | the kind derivation |
| `rule_bundle_defects` | 37 | 2 | the rules.py bundle gate |
| `cmd_check` | 12 | 2 | the refusal entry point |
| `main` | 82 | neutral | argparse and the harness-from-record wiring |

**Totals: kind 1 = 343 lines (14.8 percent), kind 2 = 1,721 lines (74.2
percent), neutral = 242 lines (10.4 percent).** The 13 remaining lines are
section separators. The mixed splits are estimates and are marked in the
table.

**Which side each subsystem falls on.** The refusals, the slot accounting, the
audit registry, the kind derivation, the territory intersection, the stall
detector, the gate-ready refusal, the unregistered-returns check and the
blocked banner are project law, kind 2, and no herdr feature can carry them.
The herdr driver's wait protocol, the polling waiter, the queue waiter, the
name mapping and the pane sweep are herdr-lack compensation, kind 1. Of those,
only the wait protocol and the waiter have a documented herdr supersession.

## The five questions

### 1. What IS Agent Automation?

From the docs, in three sentences:

- "Herdr can act as an automation layer for coding agents. A script can
  control them, or one agent can create work for other agents, inspect their
  state, and collect their results."
  (DOCUMENTED, https://herdr.dev/docs/agent-automation/)
- It offers three primitives: Layout for workspace, tab and pane topology,
  Pane for raw terminal control, and Agent for a recognized agent addressed
  by name or pane and by lifecycle state.
  (DOCUMENTED, https://herdr.dev/docs/agent-automation/, the "Three
  primitives" table)
- "Most automation should start with the CLI wrappers. Use the raw socket API
  only when you need direct request/response control or long-lived event
  subscriptions."
  (DOCUMENTED, https://herdr.dev/docs/socket-api/, the "Choose an
  integration layer" section)

So Agent Automation is not one feature. It is the CLI surface plus the raw
socket API, and the socket API carries the parts that matter here: an embedded
wait in `agent.prompt`, server-owned `agent.wait`, `events.wait` and
`events.subscribe`, and `pane report-agent` for custom state. All of it is in
the 0.8.0 schema the installed binary ships, which I verified with `herdr api
schema --json` (MEASURED, 2026-08-14; the schema names `AgentPromptWaitOptions`,
`EventsWaitParams`, `EventsSubscribeParams` and `PaneReportAgentParams`).

### 2. Which hand-rolled mechanisms does it supersede?

The waiter. `dispatch.py wait` polls the registry every 15 seconds
(`dispatch.py:1938`). The socket API documents `events.wait` and
`events.subscribe`, and the installed schema defines a one-shot wait that
matches `pane_agent_status_changed` or `pane_exited` with a `pane_id` filter
(DOCUMENTED, https://herdr.dev/docs/socket-api/ "Waiting for state"; MEASURED
in `/tmp/herdr-schema.json`). This is a push wait, not a poll. It supersedes
the polling loop in principle. Whether it fires at once for an already-idle
agent is not measured, and that question is what decides the two-phase wait
(see "What I could not settle").

The two-phase wait race. The driver waits for `working` first, then for
`idle` and `done`, because a bare wait armed after the prompt fires at once
(`dispatch.py:922-949`, measured 2026-08-13, twice). The socket API documents
that `agent.prompt` accepts an embedded `wait` object with `until` and
`timeout_ms`, and that it "submits the prompt and starts the wait in one
request, avoiding a race between separate calls" (DOCUMENTED,
https://herdr.dev/docs/socket-api/ "Raw methods"). The race is documented as
avoided. The at-once-idle behavior of that embedded wait is not measured.

The moved-pane wait failure. Measured 2026-08-13: moving an agent's pane made
`agent wait` return `agent_not_running` against the old pane while the agent
kept working at the new one (`dispatch.py:931-936`). The socket API documents
that `agent.wait` "pins the resolved pane occupant so a replacement cannot
satisfy the wait" (DOCUMENTED, https://herdr.dev/docs/socket-api/ "Raw
methods"). That is a documented supersession of a measured failure.

The resume path after a server restart. herdr documents native agent session
restore: after a Herdr server restart, panes that reported a native session
reference resume with their own `--resume` or `--session` command
(DOCUMENTED, https://herdr.dev/docs/session-state/ "Native agent session
restore"). For pi, the resume command is `pi --session <path-or-id>` and it
needs integration version 2 (DOCUMENTED, https://herdr.dev/docs/integrations/
"Pi"). `dispatch.py` cannot do this: its resume works only while the pane is
alive, and it says so (`dispatch.py:1467`). So native restore COMPLETES
the resume story. It does not replace it: dispatch resume re-prompts a killed
agent with a note; native restore resumes a conversation after the server
died. They are different failures. And on this machine no integration is
installed, so native restore does nothing today (MEASURED 2026-08-14, `herdr
integration status` reports every integration "not installed").

Not superseded: the registry, the slot accounting, the retry loops, the queue
waiter, the sweep, the name mapping, the stall detector. herdr has no queue
and no run-to-completion primitive (INFERRED from the measured subcommand
lists). `agent start` has a 30-second timeout, but
the measured fresh-pane race fails with `agent_pane_busy` BEFORE the timeout
starts (MEASURED 2026-08-13; DOCUMENTED at https://herdr.dev/docs/
cli-reference/ "Start returns only after Herdr detects the expected agent"),
so the retry loop stays. The registry is Bedrock's audit trail, not a herdr
gap: herdr tracks agents, and it does not track task code, brief, sandbox,
model or Agda flag, which is what the refusals and the audit read.

### 3. Which of our REFUSALS could it carry?

None. herdr validates agent names, keys and pane states. It has no brief
validation, no DD4 gate, no DD18 archive and literature gates, no rules.py
bundle, no tier line, no write-territory intersection, no Agda slot ceiling,
no gate-ready refusal, no sandbox model, and no knowledge of `dev/PLAN.md`
section 11. Every one of those encodes a Bedrock ruling, and the tool does
not know the ruling. Saying so plainly is the real answer: the refusals are
the 74 percent, and they are why the file cannot shrink to a wrapper.

One nuance: herdr's lifecycle states could carry PART of the blocked story.
`pane report-agent` lets an integration report `blocked` semantically
(DOCUMENTED, https://herdr.dev/docs/integrations/ "Integrate your own
agent"). That is a mechanism, not a ruling. The ruling, that `blocked` is not
a stop state and that the census shouts until the pane is gone, stays
Bedrock's (`dispatch.py:1682-1710`).

### 4. What does it give us that we do not have at all?

This is where the value is.

Event-driven notification. `events.subscribe` and `events.wait` push a return
instead of the waiter polling every 15 seconds. The harness would not need to
track a polling process. (DOCUMENTED, https://herdr.dev/docs/socket-api/
"Event subscriptions"; MEASURED in the installed schema.)

Server-owned waits that pin the occupant. The moved-pane failure is a
measured defect with a documented herdr cure. (DOCUMENTED, https://herdr.dev/
docs/socket-api/ "Raw methods".)

Native session restore across server restarts. Today a herdr server restart
kills the pi agents and `dispatch.py resume` cannot bring them back. herdr
0.8.0 documents resuming them with `pi --session` when the pi integration v2
reports the reference. That is a capability Bedrock does not have at all.
(DOCUMENTED, https://herdr.dev/docs/session-state/ "Native agent session
restore"; the requirement is in https://herdr.dev/docs/integrations/.)

`pane report-agent`. Bedrock could report each dispatch's lifecycle state so
the owner's herdr sidebar shows the census live, with the agent name and a
message. The docs' custom-integration guide is exactly this
(DOCUMENTED, https://herdr.dev/docs/integrations/ "Integrate your own
agent"; the CLI is `herdr pane report-agent`, MEASURED in `herdr pane`).

`pane wait-output`. A documented wait for literal text in a pane
(DOCUMENTED, https://herdr.dev/docs/cli-reference/ "Output waits"). The
driver reads the pane after the fact; this would wait for a marker.

`notification show`. A documented toast with sound on a return
(DOCUMENTED, https://herdr.dev/docs/cli-reference/ "Notifications"). The
harness notification is the current channel; this is a second one.

Worktrees. `worktree create` makes a Git checkout a workspace
(DOCUMENTED, https://herdr.dev/docs/cli-reference/ "Worktrees"). Bedrock
shares one workspace today. A worktree per dispatch is a new isolation
option, and it comes with the same caveat the owner ruled on 2026-08-13:
closing the workspace kills the agents in it.

`layout export` and `layout apply`. A declarative tab tree that restores
structure, labels and cwd after a restart (DOCUMENTED, https://herdr.dev/
docs/socket-api/ "Raw methods"). It does not preserve live processes.

`terminal session observe` and `control`. Live read-only and writable
terminal streams (DOCUMENTED, https://herdr.dev/docs/cli-reference/
"Direct terminal attach"). A new observation channel for a stuck agent.

### 5. What would BREAK if we adopted it?

The migration cost is real, and it is a regression risk, not a line count.

The driver is the record of three silent deaths and 18 fixed defects
(`dispatch.py:1-22`). Its wait protocol exists because the one-phase wait was
measured wrong on 2026-08-13. Every substitution must be measured on a live
agent BEFORE it replaces a guard. P-l binds: a capability measured elsewhere
is a hypothesis here. The docs describe the embedded wait; nobody has
measured it on this binary against a live pi agent. Adopting it unmeasured
risks recreating the one-phase failure, which reads as a finished run and
closes the pane.

The event waiter is a new long-lived process. `events.subscribe` keeps a
socket open. If that client dies, the return is silent. That is exactly the
2026-08-05 watcher failure that this file's header records. The current
waiter is deliberately not the agent's parent and its death is harmless
(`dispatch.py:1888-1890`). An event client needs the same property, and it
needs a re-arm contract or the durable returns.log, which stays.

There is no CLI wrapper for `events.wait`. `herdr api` has only `snapshot`
and `schema` (MEASURED, 2026-08-14). A raw socket client is new code in a new
language on a versioned protocol (protocol 19 in the installed schema,
MEASURED). An upgrade can change event shapes. The docs say to check the
protocol before depending on new behavior (DOCUMENTED, https://herdr.dev/
docs/socket-api/ "Protocol stability").

The refusals stay, so the file stays. The honest maximum reduction is the
wait protocol and the waiter, roughly 180 to 210 of the 2,319 lines, and that
reduction is conditional on measurements that do not exist yet.

The native restore does nothing until `herdr integration install pi` writes
`~/.pi/agent/extensions/herdr-agent-state.ts` (DOCUMENTED, https://herdr.dev/
docs/integrations/ "Pi"). That is a change to the pi install outside Bedrock,
and it writes into the user's home. The owner must approve it. The extension
must survive a pi update.

Blocked detection for pi is screen-manifest on this machine, because no
integration is installed (MEASURED). The docs say blocked detection is
"deliberately strict" for screen-manifest agents and falls back to `idle`
(DOCUMENTED, https://herdr.dev/docs/agents/ "Blocked state"). The
`blocked`-as-not-finished ruling already lives in the driver and the census.
Any adoption that leans on herdr's `blocked` must first resolve the C4
contradiction that `[LJ-1.205]` left open.

## What I could not settle

The at-once-idle semantics. The docs say `agent prompt --wait` from a
non-working state requires a lifecycle change within five seconds
(DOCUMENTED, https://herdr.dev/docs/cli-reference/ "Agents"). dispatch.py
measured `agent prompt --wait --until idle` returning at once from an
already-idle agent (MEASURED 2026-08-13, `dispatch.py:997-1001`). The two
readings can be reconciled if a matching current state satisfies the wait
immediately, but I could not test it: it needs a live agent, which the brief
forbids. This is THE question that decides whether the two-phase wait can
shrink. Until it is answered on this binary, the driver stays.

Whether `events.wait` fires on transitions only. The schema matches
`pane_agent_status_changed` with a target `agent_status`
(MEASURED, `/tmp/herdr-schema.json`). Whether an already-idle agent fires it
immediately is unmeasured. Same blocker.

Whether `pane_agent_status_changed` is reliable for screen-manifest pi
agents. No pi integration is installed (MEASURED). The lifecycle authority
table says pi uses "lifecycle hooks when installed; otherwise screen
manifest" (DOCUMENTED, https://herdr.dev/docs/agents/). A transition event
from screen-manifest detection is an inference, not a fact.

The exact mixed-subsystem counts. The 30/23 and 60/55 splits are estimates.
The arithmetic is reproducible from this report's table.

Whether `agent.wait`'s pinning is in the 0.8.0 CLI or only in the raw API.
The docs describe it under raw methods (DOCUMENTED). The installed CLI's
`agent wait` help text does not mention pinning. I did not test it live.

## DD4

The tooling axis of DD4 has two ends, and the evidence lands on both. The
waiter and the wait protocol are generic infrastructure. herdr maintains a
wait and an event channel, so keeping the 15-second poll hand-rolled is
paying twice, once the semantics are measured. The refusals are project law.
DD4, DD18, C-12, the territory intersection and the kind derivation encode
Bedrock rulings, and a general tool cannot know them, so delegating them is
wrong even though it would be cheaper. The split makes the boundary visible:
343 kind-1 lines are candidates on measurement, 1,721 kind-2 lines are not
candidates at all.

## The proposal, in one paragraph

Keep `dispatch.py` as the refusal gate, the audit registry, the slot
accounting and the census. That is the 74 percent and it does not move. Run
three measurements, in order, on a live test agent: whether the embedded
`agent.prompt` wait returns at once for an already-idle agent; whether
`events.wait` on `pane_agent_status_changed` and `pane_exited` fires on
transitions; and whether `agent.wait` pins the occupant after a pane move.
Each measurement that passes lets one hand-rolled mechanism shrink: the
two-phase loop, then the polling waiter, then the moved-pane retry. Install
the pi integration v2 under the owner's approval and test native session
restore across a server restart; that is new capability, not a swap. Do not
move a refusal into herdr. Sequence the skill edit after `[LJ-1.205]` lands:
the skill changes only if a measurement passes.

## ARCHIVE USED

- `.claude/skills/codex-dispatch/dispatch.py`, read whole (2,319 lines).
  Sites: the three-failure header `:1-22`; the model block `:76-84`; the
  harness and policy wiring `:84-120`; the pi stream wrapper `:121-130`; the
  herdr kind and workspace history `:131-190`; `herdr_name` `:191-197`; the
  Agda ceiling `:198-217`; the registry primitives `:234-386`; `agda_holders`
  and `agda_pileup` `:392-429`; `strays` `:430-504`; `herdr_agents`
  `:508-528`; `sweepable_panes` `:529-581`; `close_pane` `:582-590`; the
  refusals `:591-729`; the launch head `:733-817`; the herdr driver
  `:818-1032`, with the fresh-pane retry `:886-896`, the two-phase wait
  `:928-949`, the moved-pane lesson `:931-936`, the blocked check
  `:960-965`; the pi path `:1033-1078`; the codex fallback `:1079-1090`;
  the resume driver's one-phase-wait lesson `:997-1001`; `announce`
  `:1169-1200`; `_wait_for` `:1201-1231`; `cmd_queue` `:1247-1331`; the
  territory parsing `:1332-1440`; `cmd_resume` `:1441-1494`; the stall
  detector `:1495-1605`; `unregistered_returns` `:1606-1639`; `cmd_status`
  `:1640-1805`, with the blocked banner `:1682-1710`; the waiter singleton
  `:1821-1884`; `cmd_wait`
  `:1885-2002`; `cmd_gate_ready` `:2003-2024`; `dd4_defects` `:2025-2062`;
  `survey_defects` `:2063-2119`; `brief_kind` `:2120-2188`;
  `rule_bundle_defects` `:2189-2225`; `cmd_check` `:2226-2237`; `main`
  `:2238-2319`.
- `.claude/skills/herdr/SKILL.md`, read whole (195 lines). Taken: the
  authority doctrine, the name grammar `:56`, the lifecycle states `:54,58`,
  the `--wait` and stalled rules `:128-130`, the safety rules `:187-195`.
- `.claude/skills/dispatch-herdr/SKILL.md`, read whole (529 lines). Taken:
  the measured herdr limits, the waiter contract, the blocked ruling, the ten
  mistakes.
- `scripts/dispatch_policy.py`, read whole (317 lines). Taken: the switch
  `:52`, the two tables `:117-171`, `model_for` `:108-110`, the honest limit
  `:28-46`.
- `dev/ORCHESTRATION.md` sections 1 to 3, read `:1-241`. Taken: the
  enforcement points and the brief home rule.
- `dev/PLAN.md` DD17 `:259`, DD18 `:260`, DD25 `:265`, DD0 `:249`, DD19
  `:261`, DD24 `:264`, read. Taken: the rulings the refusals encode.
- `agents/tasks/LJ-1-205/lj-1.205-report.md`, read whole. Taken: the
  reconciliation result, the C4 open contradiction, the measured binary and
  site agreement.
- `agents/tasks/LJ-1-190/lj-1.190-report.md`, read whole. Taken: the
  script-versus-skill reconciliation and the 2,276-line figure the brief
  cites.
- `scripts/rules.py --for recon`, run. Taken: the recon bundle this report
  obeys.
- Why not the retired route's archives: nothing in `archive/dev/` bears on a
  herdr tooling question; the retired dispatch mechanics predate herdr.

## LITERATURE USED

- `https://herdr.dev/docs/agent-automation/`, read whole. The three
  primitives, the identity and launch rules, the control-surface table, the
  recipes.
- `https://herdr.dev/docs/cli-reference/`, read whole. The full command
  surface, the `--wait` and `--until` semantics, the five-second stalled
  rule, `agent start` timeout, `pane wait-output`, plugins, env vars.
- `https://herdr.dev/docs/socket-api/`, read whole. The raw methods, the
  embedded prompt wait, `events.wait` and `events.subscribe`, `agent.wait`
  pinning, `pane report-agent`, protocol stability, socket paths.
- `https://herdr.dev/docs/session-state/`, read whole. Native agent session
  restore, the per-agent minimum integration versions, snapshot restore,
  pane history, live handoff.
- `https://herdr.dev/docs/agents/`, read whole. The status-authority model,
  the lifecycle-authority table, blocked detection strictness, detection
  manifests.
- `https://herdr.dev/docs/integrations/`, read whole. The pi integration
  install path, the custom-integration guide, the session-restore
  requirements.
- `https://herdr.dev/docs/plugins/`, read whole. The plugin host surface,
  startup and event hooks.
- `https://herdr.dev/docs/config-reference/`, read `:1958` and `:2039`.
  `session.resume_agents_on_restore` and `experimental.pane_history`.
- WHY NOT `https://herdr.dev/docs/quick-start/`, `install/`, `keyboard/`,
  `concepts/`, `how-to-work/`, `persistence-remote/`, `preview/`,
  `windows-beta/`, `marketplace/`, `configuration/`, `troubleshooting/`:
  the pages cover setup, keybindings, remote access, preview builds and
  Windows. Nothing in them bears on automation capability. The brief names
  the agent-automation page and its links, and the links are read.
- WHY NOT `https://herdr.dev/docs/agent-skill/`: `[LJ-1.205]` already read it
  and established that it is meta-documentation, not the skill text, and
  that the binary and the site are in step at 0.8.0.

## What was measured this run, and what was not

Measured (read-only): `herdr --version` prints `herdr 0.8.0`; `herdr agent`
lists `list get read send-keys prompt rename focus wait attach start explain`
and no stop or kill; `herdr api` lists only `snapshot` and `schema`; `herdr
api schema` prints protocol 19 and the five schema blocks; `herdr api schema
--json` contains `AgentPromptWaitOptions`, `EventsWaitParams`,
`EventsSubscribeParams`, `PaneReportAgentParams` and the 26 event types;
`herdr integration status` reports every integration not installed; `herdr
agent list` shows the live agents and their states; `herdr api snapshot`
returns the bootstrap snapshot. Nothing was launched. No live agent was
prompted, keyed or renamed. No file in `src/`, `scripts/`, `dev/` or
`.claude/` was changed. The only file I wrote is this report.
