# LJ-1.126 report: streaming and resume for the pi harness

## 1. Verdict

**STREAMING: YES.** **RESUME: YES.** Both are proven end to end with a real
dispatch through `dispatch.py`.

### 1.1 Streaming, proven

Command: `python3 /tmp/lj126-drive.py pitest2`. It calls `dispatch.py`'s real
`launch()` with `HARNESS = "pi"`.

```
dispatch: pitest2 away, pid 77090, session 019ff8fd-2a5f-712e-89f1-8b8ae67d2211
          log .../.state/logs/pitest2-20260813-103928.log
```

The log grew while the process was alive:

```
t=03s logbytes=648    delta=648    pid77090_alive=yes
t=06s logbytes=844    delta=196    pid77090_alive=yes
t=09s logbytes=844    delta=0      pid77090_alive=yes
t=12s logbytes=844    delta=0      pid77090_alive=yes
t=15s logbytes=1039   delta=195    pid77090_alive=yes
t=18s logbytes=1039   delta=0      pid77090_alive=yes
t=21s logbytes=1133   delta=94     pid77090_alive=yes
t=24s logbytes=1289   delta=156    pid77090_alive=no
```

The log is readable. This is the whole file at
`.claude/skills/codex-dispatch/.state/logs/pitest2-20260813-103928.log:1`:

```
[pi] launching: pi --mode json -p --provider deepseek ... (9 argv items)
session id: 019ff8fd-2a5f-712e-89f1-8b8ae67d2211
[pi] cwd=/Users/alsg/Agentic/Bedrock session-version=3
[pi] agent start
[pi] --- turn start ---
[user] prompt sent
[think] The user wants me to run `sleep 7; date` three separate times, as three separate sequential
  tool calls, one after another. Then reply with exactly "ok".
[usage] in=136 out=112 cacheRead=8192 total=8440 stop=toolUse
[tool] bash {"command": "sleep 7; date"}
[tool] bash -> ok: Thu 13 Aug 2026 10:39:37 +08
[pi] --- turn end ---
...
[reply] ok
[usage] in=42 out=2 cacheRead=8576 total=8620 stop=stop
[pi] agent end (willRetry=False)
[pi] agent settled
[pi] exit rc=0
```

The final-message file is still produced. `pitest2-20260813-103928-final.md`
holds `ok`, taken from the last `message_end` whose role is `assistant`.

### 1.2 Resume, proven

Command, the real CLI:

```
python3 dispatch.py resume pitest1 --note "What was the secret word I told you? \
Reply with exactly that one word and nothing else."
```

Output:

```
dispatch: resuming on the pi harness, as recorded at launch
dispatch: pitest1-resume away, pid 76596, session 019ff8fc-6161-722a-a3d6-01dc42d3fb3c
          log .../.state/logs/pitest1-resume-20260813-103857.log
```

`pitest1`'s brief said "Remember this secret word: banana." The resumed run
answered:

```
[think] The secret word was "banana". Reply with exactly that one word.
[reply] banana
```

`pitest1-resume-20260813-103857-final.md:1` holds `banana`. The word exists
nowhere in the resume prompt, so the run really continued the earlier session.
Both runs carry the same session id, and pi appended to one session file:
`~/.pi/agent/sessions/--Users-alsg-Agentic-Bedrock--/2026-08-13T02-38-37-409Z_019ff8fc-6161-722a-a3d6-01dc42d3fb3c.jsonl`.

### 1.3 The pid constraint holds

The wrapper is the only child. It reads pi's stdout until pi closes it, then
returns pi's exit code, so the wrapper pid lives exactly as long as the run.
The table above shows `pid77090_alive` going from `yes` to `no` at the same
sample where the log stopped growing. The slot accounting, `status` and `wait`
need no change.

## 2. Prior art

**I found prior art, and it is abundant. I copied no code.** I read the shapes,
then wrote `pi_stream.py` from scratch.

### 2.1 Official documentation

| URL | Loaded | What it gave |
|---|---|---|
| `https://pi.dev/docs/latest` | yes | The index. A "Programmatic Usage" group with `/sdk`, `/rpc`, `/json`, `/tui` |
| `https://pi.dev/docs/latest/json` | yes | The JSON event stream |
| `https://pi.dev/docs/latest/rpc` | yes | `--mode rpc`, strict JSONL |
| `https://pi.dev/docs/latest/sessions` | yes | Sessions under `~/.pi/agent/sessions/`, keyed by working directory |
| `https://pi.dev/docs/latest/session-format` | yes | The on-disk record schema |
| `https://pi.dev/docs/latest/usage` | yes | Print mode and the session flags |
| `https://pi.dev/docs/latest/cli` | **no, HTTP 404. MEASURED** | No such page exists |

**One documentation claim is false, and I disproved it.** The `/usage` page says
`-p`/`--print` cannot combine with `--mode json`. Every run in this report uses
both. The source shows why: `resolveAppMode` tests `mode === "json"` first, at
`/Users/alsg/.nvm/versions/node/v24.12.0/lib/node_modules/@earendil-works/pi-coding-agent/dist/main.js:83`.
`--print` is redundant there, never a conflict.

### 2.2 Open-source projects

| Repo | What it does |
|---|---|
| `https://github.com/banteg/takopi` | The closest match. A chat bridge that spawns `pi --print --mode json --session <id> <prompt>`, translates the JSONL into a harness-neutral event set, and prints a resume line. It has a written spec at `docs/reference/runners/pi/runner.md` |
| `https://github.com/assistant-ui/assistant-ui` | `packages/react-pi/src/node/mapping.ts` holds the most complete enumeration of pi event types I found |
| `https://github.com/buihongduc132/verifier-loop` | Rust. Templates `spawn="pi --mode json"` and `resume="pi --session {sid} --mode json"`. It moved the prompt to stdin after an argv overflow |
| `https://github.com/code-yeongyu/oh-my-openagent` | Waits on `agent_settled` with a timeout |
| `https://github.com/shaftoe/pi-coding-agent-action` | A CI action, but it uses the Node SDK and not the CLI |

More than thirty other repositories spawn `pi --mode json`. Upstream source is at
`https://github.com/earendil-works/pi`.

### 2.3 What I took, as an IDEA and not as text

1. **Resume with `--session <id>`, never with `--resume`.** takopi documents that
   `--resume` opens an interactive picker and takes no argument. I confirmed it
   against `pi --help` and against
   `.../pi-coding-agent/dist/cli/args.js:31`, where `--resume` and `--continue`
   parse as booleans.
2. **Read the answer from `message_end`, not from the concatenated deltas.**
   takopi and assistant-ui both do this. pi strips the cumulative `partial`
   field from `message_update` on purpose, at
   `.../dist/modes/json-event.js:5`, so deltas alone are the wrong source.
3. **`agent_settled` is the last event, not `agent_end`.** `agent_end` carries
   `willRetry`, so a retry can follow it. My wrapper does not stop on any event
   at all. It stops when pi closes stdout, which is stricter and needs no event
   list.
4. **Detect failure from `stopReason` and from `isError`.** There is no
   top-level `error` event type. My wrapper prints `stop=<stopReason>` on every
   usage line and marks a failed tool `ERROR`.
5. **`--session-id <slug>` would remove the scrape.** verifier-loop and the pi
   source at `.../dist/core/session-manager.js:15` show that `--session-id`
   accepts any slug and creates the session if it is missing. **I did NOT take
   this one**, and section 6 says why.

I wrote no line of `pi_stream.py` from any of these projects. The rendering
scheme, the sidecar file, the codex-shaped session line and the signal
forwarding are ours.

## 3. What I changed

### 3.1 New file

`.claude/skills/codex-dispatch/pi_stream.py`, 307 lines. It runs
`pi --mode json`, renders each event to stdout and flushes at once, appends the
raw event to a sidecar `.jsonl`, writes the final message, and returns pi's exit
code. Its docstring holds the full design record.

**What the readable log drops.** All of it stays in the sidecar `.jsonl`.

| Dropped | Reason |
|---|---|
| `tool_execution_update` | partial tool output. The complete result is kept |
| `toolcall_start`, `toolcall_delta`, `toolcall_end` | `tool_execution_start` carries the same tool name and the same complete arguments, and it fires when the call really runs |
| the `agent_end` message array | it repeats every message of the whole run |
| `message_start` and `message_end` for `user` and `toolResult` roles | already shown by the prompt line and by `tool_execution_end` |
| `bash_execution_update`, `queue_update`, `entry_appended`, `session_info_changed`, `thinking_level_changed` | high volume, no operator value |

Kept and rendered: the session header, `agent_start`, `agent_settled`,
`agent_end`, turn boundaries, thinking and reply text as it streams, tool calls
and their results, per-message token usage, and every compaction, retry or
extension error.

### 3.2 Edits to `dispatch.py`

| Line | Change |
|---|---|
| `dispatch.py:104` | `PI_STREAM` constant, with the measurement that justifies it |
| `dispatch.py:194` | comment on `SESSION_RE`: pi reuses it and adds no pattern |
| `dispatch.py:600` | `events` path, one per dispatch, beside the log |
| `dispatch.py:726` | the pi branch builds `pi --mode json -p` under `pi_stream.py` |
| `dispatch.py:743` | resume adds `--session <id>` to pi's argv |
| `dispatch.py:745` | `cmd` is now `[sys.executable, PI_STREAM, --events, --final, --, pi ...]` |
| `dispatch.py:793` | the registry record carries `harness` |
| `dispatch.py:794` | the registry record carries `events`, for the pi harness only |
| `dispatch.py:949` | `queue --resume-of` adopts the prior record's harness |
| `dispatch.py:1136` | `cmd_resume` sets the harness from the record |
| `dispatch.py:1814` | `--harness` help text corrected |

### 3.3 The defect I found on the way, and it was not in the brief

**Every resume ran on the codex path, whatever launched the original.**
`main()` sets the harness global from `--harness`, and the `resume` subcommand
has no such flag, so `getattr(a, "harness", "codex")` always returned `"codex"`
there. A pi session id handed to `codex exec resume` starts a codex agent on an
id codex never issued. The registry held no harness field, so `resume` had no
way to know better.

The fix records the harness at launch and reads it back in both resume paths.
**The fallback is `"codex"` and not the module default**, because every record
written before 2026-08-13 lacks the field and every one of those did run on the
codex path. `dispatch.py:1136`.

### 3.4 `SKILL.md`

Added a `--harness pi` section after the `--harness codex` paragraph. It states
the three output files, the `--session` flag, the harness-aware resume, that pi
enforces no sandbox, and that a herdr agent still cannot be resumed.

## 4. What I verified on the codex and herdr paths

**Both are unbroken. I dispatched one trivial agent on each after the change.**

| Path | Task | Result |
|---|---|---|
| codex | `codextest1`, pid 77700 | Session id scraped (`019ff8fd-f139-7dd3-a4e4-5abec6393a7c`), log carries the `OpenAI Codex v0.147.0` header, final message `ok` |
| herdr | `herdrtest1`, pid 78603 | Pane `w7:p8` created, agent started, prompted, waited, final message read, pane closed. `herdr pane list` returned to `['w7:p1', 'w7:p2']` |
| pi | `pitest1`, `pitest1-resume`, `pitest2` | Section 1 |

Logs, in `.claude/skills/codex-dispatch/.state/logs/`:
`codextest1-20260813-104019.log`, `herdrtest1-20260813-104059.log`.

The shared code I touched is three lines: the `events` variable and the two new
registry keys. The codex and herdr runs both crossed all three and both wrote a
correct record. `python3 -m py_compile dispatch.py pi_stream.py` passes, and
`python3 dispatch.py status` runs.

**The two live agents were not disturbed.** `LJ-1.124` was `working` in pane
`w7:p2` before my herdr test and after it. No test dispatch used `--agda`, so
neither Agda slot was touched.

## 5. Measurements worth keeping

### 5.1 pi streams, and my first two probes lied about it

**MEASURED.** `pi --mode json` writes one JSON event per line and flushes each
one. Source: `writeRawStdout` at
`/Users/alsg/.nvm/versions/node/v24.12.0/lib/node_modules/@earendil-works/pi-coding-agent/dist/core/output-guard.js:67`.
It calls `process.stdout.write` per event with a completion callback. It never
collects events.

**MEASURED, and it is a trap that costs an hour.** My first two probes ran pi as
a shell background job and left a terminal on stdin. Both wrote **zero bytes for
75 seconds**, which reads exactly like "pi does not stream". The cause is
SIGTTIN: a background job that reads a terminal stops. Adding `< /dev/null`
fixed it, and the same run then streamed from t=3s. `dispatch.py` already passes
`stdin=subprocess.DEVNULL` at `dispatch.py:775`, so the dispatcher was never
exposed to this. `pi_stream.py` passes it too.

### 5.2 The raw stream is not readable, which is why the wrapper renders

**MEASURED.** A 27-second run with three tool calls wrote 27 KB over 269 lines.
237 of those lines were `message_update` token deltas. Event counts:

| type | count |
|---|---|
| `message_update` | 237 |
| `message_start` / `message_end` | 6 / 6 |
| `tool_execution_update` | 6 |
| `tool_execution_start` / `_end` | 3 / 3 |
| `turn_start` / `turn_end` | 2 / 2 |
| `session` | 1 |
| `agent_start`, `agent_end`, `agent_settled` | 1 each |

`message_update` sub-types, in the `assistantMessageEvent` field:
`thinking_start`, `thinking_delta`, `thinking_end`, `text_start`, `text_delta`,
`text_end`, `toolcall_start`, `toolcall_delta`, `toolcall_end`.

The first line is the session header:

```json
{"type":"session","version":3,"id":"019ff8ee-f6d0-7e7b-ba65-6617ed6cfe9a","timestamp":"2026-08-13T02:23:58.160Z","cwd":"/private/tmp"}
```

### 5.3 A herdr agent still cannot be resumed

**MEASURED.** `python3 dispatch.py resume herdrtest1` answers:

```
dispatch: herdrtest1 has no session id in its record or its log; it cannot be
resumed, only re-dispatched
```

The herdr driver log carries the pane id and the agent name, never a session id,
so `SESSION_RE` finds nothing. This is a pre-existing gap and it was not in my
brief. **It is now cheap to close**, because the herdr resume branch already
prompts the named agent and does not need a session id at all: only
`cmd_resume`'s session-id refusal blocks it. I did not change that, because
loosening a refusal on the DEFAULT harness while two agents run under it is not
a change to make without the orchestrator's word.

### 5.4 This machine has no `timeout`

**MEASURED.** `timeout` and `gtimeout` both return exit 127, "command not
found". Any brief that tells an agent to bound a command with `timeout` will
fail on this machine.

## 6. What I could not do, and why

1. **I did not switch to `--session-id <slug>`, which is the better design.**
   `--session-id` accepts a slug the caller chooses and creates the session if
   it is missing, so the session id would need no scrape at all. **I left it
   alone deliberately.** The scrape already works, the codex-shaped line reuses
   a pattern that two call sites already trust, and a deterministic slug changes
   what happens when a task code is dispatched twice. That is a design fork, and
   the brief did not ask for one. **INFERRED**, from the pi source at
   `.../dist/core/session-manager.js:15` and from verifier-loop. I did not
   measure `--session-id` on this machine.

2. **My test briefs live in `/tmp`, not in `_build/briefs/`.** `validate()`
   refuses an unpinned brief at `dispatch.py:464`, and my brief forbids me to
   write under `_build/briefs/`. So the two pi launches and the codex and herdr
   launches went through a five-line driver that imports `dispatch` and stubs
   `launch_defects` before calling the real `launch()`. **Everything else is the
   real code**: the command construction, the registry lock, the record, the
   session scrape and the pid accounting. `dispatch.py resume` needed no stub at
   all, because `launch()` skips `launch_defects` on a resume, so section 1.2 is
   the untouched CLI. Drivers at `/tmp/lj126-drive.py` and `/tmp/lj126-drive2.py`.

3. **I did not measure a long brief through the wrapper.** verifier-loop moved
   its prompt to stdin after an argv overflow. Our longest test prompt was a
   14-line brief. The wrapper adds one more argv copy of the prompt on top of
   the copy pi already gets. **INFERRED**, not measured: a brief of the size
   Bedrock normally sends should still fit, because the pre-change pi path
   already passed the whole brief on argv and `LJ-1.121` ran. If a large brief
   ever fails with `E2BIG`, the cure is a `--prompt-file` option on
   `pi_stream.py`, which is a small change.

4. **I did not test a kill and resume in the middle of a run.** Section 1.2
   resumes a run that finished cleanly. **INFERRED**, not measured: a killed run
   should resume too, because `pi_stream.py` writes the final file on every
   assistant `message_end` rather than once at exit, and the session id is in
   the log from the first event. The forwarding of SIGTERM to pi is written and
   compiled but **not measured**.

5. **Five test records are now in the registry**: `pitest1`, `pitest1-resume`,
   `pitest2`, `codextest1`, `herdrtest1`. They will show as `exited` in
   `dispatch.py status`. I left them because they are the evidence for this
   report. Delete them when the report is audited.
