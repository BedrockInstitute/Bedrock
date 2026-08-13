# [LJ-1.127] report: the dispatch policy switch, its checker, and a herdr audit

**Every negative below is marked MEASURED or INFERRED, in those words.**

## 1. What I changed, file by file

### New files

| File | What it is |
|---|---|
| `scripts/dispatch_policy.py` | **THE SWITCH.** `VERSION_IN_FORCE` at `scripts/dispatch_policy.py:51`, the two tables, the date set, the reason, the revert condition. `python3 scripts/dispatch_policy.py` prints all of it |
| `scripts/check-dispatch-policy.py` | The checker. Imports the switch and holds no policy of its own |
| `_build/lj-1.127-agents-diff.md` | The `AGENTS.md` diff, prepared and NOT applied |

### Edited files

| File | Change |
|---|---|
| `dev/ORCHESTRATION.md:13-64` | Section 1 rewritten. It points at the switch and does NOT restate the tables. Section 1.1 renamed and its head now follows the switch |
| `dev/PLAN.md:176` | DD17's tier paragraph replaced by the switch pointer. Row grew from 321 to 485 words against a 1,600-word cap |
| `scripts/README.md:397-428` | Both new scripts documented, with their limits |
| `Makefile:36,108-115` | New `dispatchpolicy` target, wired into `check` |
| `.claude/skills/codex-dispatch/dispatch.py` | The audit's fixes. Listed in section 5 |
| `.claude/skills/codex-dispatch/SKILL.md:224-271` | The switch, `herdr-pi`, the pane sweep, and the seven repairs |

### What I did NOT change, and why

- **`AGENTS.md`.** DD19 forbids it without the owner's ruling and a dated
  `AGENTS-diff-approved:` trailer. The diff is prepared. **The owner must
  rule.**
- **No DD number invented.** DD17 is amended in place, which is what the owner's
  instruction describes. If the orchestrator wants a new row, it assigns the ID.
- **Nothing under `src/`.** No Agda ran and `make check` did not run.
- **The registry's 344 records were not pruned.** Five test records from
  `[LJ-1.126]` and two failed `herdrtest1-resume` records are live state that a
  human should decide about, and D10 says a dead record's session id is the only
  way to resume it.
- **`dispatch.py status`'s full listing was not trimmed.** It prints all 344
  records. See finding 10.

## 2. The policy, and the design the owner specified

**One hardcoded field, one place, and everything derives from it.**
`scripts/dispatch_policy.py:51`:

```python
VERSION_IN_FORCE = "override"
```

Beside it sit `SET_ON`, `SET_BY`, `REASON` and `REVERT_CONDITION`, because a
switch that records only its position loses why it is there.

**I took the orchestrator's suggested location.** A module under `scripts/`
rather than a TOML file, for one reason: the consumers are Python
(`check-dispatch-policy.py` and `dispatch.py`), so a module is imported with no
parser and no second format to keep in step. `dev/ledger.toml` is the
counter-example that argues for TOML, and it is a counter-example precisely
because the owner edits figures there; here the owner edits **one word**.

**Inspection is one command:**

```
$ python3 scripts/dispatch_policy.py
DISPATCH POLICY: `override` is IN FORCE
  set 2026-08-13 by the repository owner
  reason: QUOTA, not quality. ...
  revert: The owner cancels the override by word. Set VERSION_IN_FORCE = "normal" ...

  case           harness      agent    model              tier:
  default        in-harness   opus 5   -                  opus
  adversarial    herdr        pi       deepseek-v4-pro    pi
  fallback       herdr        codex    deepseek-v4-pro    codex
```

`python3 scripts/dispatch_policy.py normal` prints the other version without
changing anything.

**The three things the switch authoritatively drives, as required:**

1. **`dispatch.py`'s default harness.** MEASURED: with the override in force
   the module-level `HARNESS` is `herdr`; setting the switch to `normal` makes
   it `herdr-pi`. Both read back from `import dispatch`.
2. **What the checker accepts in a `tier:` line.**
3. **What the inspection command prints.**

**THE FLIP TEST, MEASURED end to end.** I set the switch to `normal`, ran both
consumers, and set it back. `dispatch.py`'s default harness moved from `herdr`
to `herdr-pi`. The checker's own count moved from **4 notes to 3**, because
`l3.32-t147.md` is an adversarial review carrying `opus`, which is wrong under
the override and RIGHT under the normal version. **One edited word changed both
consumers and nothing else was touched**, which is the property the owner
asked for.

**THE HONEST LIMIT, stated in the module docstring, in `scripts/README.md`, in
`dev/ORCHESTRATION.md` section 1, in the `AGENTS.md` diff, and here.** The
switch **cannot force the orchestrator's behaviour.** An in-harness Opus
dispatch never passes through `dispatch.py`, so no value in the module can
start it, stop it, or redirect it. What the switch does is make a wrong choice
**detectable by an audit**. Anything stronger would be the false safety
`AGENTS.md` warns about.

**Two points the owner asked to be stated plainly, and both are in DD17,
ORCHESTRATION section 1 and the module:**

- **The normal version's default is pi, not codex.** That is a real change to
  DD17, not a restatement. `[LJ-1.126]` made pi viable the same day.
- **The override's reason is QUOTA, not quality.** `[LJ-1.121]` measured pi's
  return quality as fully acceptable. It is temporary and reverts on the
  owner's word.
- **The invariant under both versions: the critic is never the same head as the
  author.** That is why the tables swap.

## 3. The checker: what it enforces, what it cannot, and whether it is clean

**It is CLEAN on the current tree and it is wired into `make check`.**

```
$ make dispatchpolicy
dispatch policy OK: `override` in force, 406 brief(s) read,
4 pre-epoch note(s) not judged (run with --notes to see them)
```

### What it enforces

1. **The switch is single and readable.** `VERSION_IN_FORCE` names a version
   the module defines, or the checker stops.
2. **Nobody restates the table.** A governed document (`dev/**/*.md`,
   `AGENTS.md`, `scripts/README.md`) that names the head model
   `deepseek-v4-pro` must also point at `scripts/dispatch_policy.py`. MEASURED
   before I wrote anything: no document in the tree named that model, so this
   rule binds only new text.
3. **Every brief carries a legal `tier:` token**, one of `opus`, `pi`, `codex`,
   `fable`. MEASURED across 406 briefs: 390 `codex`, 7 `opus`, 6 `fable`, and 3
   with no `tier:` line at all.
4. **A post-epoch brief names the version it was chosen under.** `tier: opus
   (override)` leaves a trace; `tier: opus` does not.
5. **An adversarial review carries the critic's head, not the author's.**

### What it CANNOT do

- **It cannot verify which head actually RAN.** A brief is a statement of
  intent, and an in-harness dispatch is observed by nothing. A brief that says
  `tier: pi` and was run on Opus 5 passes green.
- **It cannot date a brief reliably.** `_build/` is never committed, so git
  cannot date these files and mtime is all there is. An edited old brief looks
  new.
- **It cannot tell an adversarial review from a brief that DISCUSSES one.** It
  reads the GOAL section and the tier line for one word. It is deliberately
  narrower than `dispatch.py`'s `brief_kind`, which scans the first 1,200
  characters: that heuristic classifies any brief citing DD25 as a review,
  which is harmless when it picks a rule bundle and not harmless when it fails
  a gate.
- **It cannot judge whether the choice was right.** Citation is not
  application.

All four limits are in the script's docstring and in `scripts/README.md`.

### The epoch, and why the gate is green on its first run

Checks 4 and 5 bind only briefs whose mtime is at or after **2026-08-13 11:00**,
which is `check-agents-guard.py`'s self-anchoring pattern: a brief from before
the rule is not judged by it. **MEASURED: 4 pre-epoch notes and 0 failures.**
The notes are three briefs with no `tier:` line
(`geology-legacy-brief.md`, `ideal-form-recon-brief.md`,
`revival-gch-probe-brief.md`) and one adversarial review carrying `opus`
(`l3.32-t147.md`), which was correct under the policy of its day.

**Without the epoch the gate would open red on 403 briefs**, none of which
anybody will retrofit, and a permanently red gate is a gate nobody reads.

## 4. The pane sweep

`dispatch.py status` now reports two lists and closes neither by default.

- **SWEEPABLE**: the herdr agent is idle or done, its name maps back to a
  registry task, that task's record is not alive, and it left a clean final
  message with no death marker in its log.
- **KEPT AS EVIDENCE**: everything else that maps to a task. **A pane whose
  task ended in a death is never closed.** This session read three deaths out
  of a pane that was still open.

`dispatch.py status --sweep-panes` closes the sweepable list and prints each
result. A pane holding a live agent is in neither list, and neither is a pane
whose agent name maps to no task: MEASURED, the orchestrator's own `w7:p1`
appears under a separate note as "1 herdr agent(s) outside this registry", not
as a violation, because the owner ruled the workspace is shared.

**Nothing was swept during this task: MEASURED, `herdr agent list` holds
exactly one agent, the orchestrator's own, and `[LJ-1.124]`'s pane was already
closed by hand.** So the sweep is verified on its report path and its
never-close path, and its close path is INFERRED from `herdr pane close`'s
exit status alone.

## 5. The audit: findings ranked worst first

**Method.** I read `dispatch.py` end to end, generated the herdr driver scripts
with a stubbed `Popen`, checked each with `bash -n`, and exercised the pane
selection against real `herdr pane list` output and three synthetic payloads. I
did not dispatch a live agent: the sibling holds the quiet machine and a live
test costs quota for evidence I could get another way.

### 1. A LIVE agent's pane could be closed by its own driver. FIXED

**Symptom.** `dispatch.py:748-760` (before the fix): the second wait's retry
loop ran ten times and fell through on exhaustion with no flag. The death guard
then passed, **because the agent was alive, which is the problem**, the driver
read a half-written pane, and `herdr pane close` killed a working agent.

**MEASURED that the loop can be entered:** `LJ-1.125`'s log ends with
`{"error":{"code":"agent_not_running",...},"id":"cli:agent:wait"}` followed by
`HERDR done`. That run predates the retry loop, so it exited after one failure;
with the loop it would have exhausted ten and closed the pane.

**Fix.** `STOPPED` records whether the agent really reached a stop state. The
driver now reads the pane, leaves it OPEN, and exits 1. **Verified** with
`bash -n` on the generated script and by reading the emitted control flow.

### 2. The resume driver carried three defects the fresh driver had already paid for. FIXED

**Symptom, `dispatch.py:773-812`.** The whole resume path was two lines.

- **One-phase wait.** `agent prompt --wait --until idle` is the exact form
  `SKILL.md:176-179` records as MEASURED to return at once, because `idle` is
  the state the agent is already in at submission. The driver would read a pane
  holding nothing but the prompt and exit 0. **The run would read as
  complete.**
- **No existence check.** With the agent gone, `agent prompt` fails,
  `agent read` writes the error into the final-message file, and the driver
  still exits 0.
- **Python `repr` is not shell quoting.** A note holding `'` produced a
  double-quoted shell word, so `$VAR` and backticks expanded. A note holding
  both quote characters produced a **shell syntax error**.

**Fix.** The resume driver now mirrors the fresh one: existence check, prompt,
two-phase wait, retry with `STOPPED`, and `shlex.quote` on every interpolated
value. **Verified MEASURED:** the note `it's a "tricky" note with $VAR and
` + "`tick`" + ` ` generates `'it'"'"'s a "tricky" note with $VAR and ` +
"`tick`" + `'` and `bash -n` returns 0.

### 3. A failed run was announced as a CLEAN return. FIXED

**Symptom.** The clean test was `final.exists() and size > 0`, at five sites.
On the herdr path `herdr agent read` writes its own error object into that
file. **MEASURED:** both `herdrtest1-resume` attempts failed with
`agent_not_found`, wrote 105 and 112 bytes, and `returns.log:364-365` records
both as `clean`.

**Fix.** `final_is_clean()` rejects a file holding only a herdr error object,
and all seven call sites route through it. **Verified MEASURED:** the two
failed resumes now return False and the two real finals return True; `status`
now prints `EXITED WITH NO FINAL MESSAGE` for `herdrtest1-resume`.

### 4. Every live herdr agent would have read as an UNMANAGED STRAY. FIXED

**Symptom, `strays()`.** Under setsid the codex process was the registry pid or
its child. Under herdr its parent is a herdr shell, so **neither its pid nor its
ppid is in the registry** and it matched the stray test. `cmd_status` returns 1
on a stray, so the census would have reported a violation for correct work.

**INFERRED, not measured:** no herdr agent is live now, so I could not observe
the false positive. The reasoning is from the code path and from the herdr
architecture, which the `agent list` output confirms (the agent's pane belongs
to the server, not to any dispatch).

**Fix.** Stray detection walks the process ancestry, bounded at 64 hops, and a
codex process with a herdr ancestor is herdr-managed. **The herdr-era shape of
the same violation is caught one level up**: a herdr agent whose name maps to
no registry task is reported, as a note rather than a failure, because the
workspace is shared with the owner by ruling.

### 5. Two safety alarms were DEAD for the entire live task series. FIXED

**5a. `unregistered_returns()`** matched `^\| L3\.32-<NAME> \|` only. The live
series row id is `| LJ-1.126 |`. **So the alarm reported all-clear for every
dispatch since 2026-08-09 while being unable to see one of them.**

**MEASURED, and the fix found a real defect on its first run:** with the regex
widened, `status` reports `LJ-1.125: the row still reads 'DISPATCHED'`. That is
a genuine dropped registration the broken alarm had hidden.

**5b. `stall_note()`** derived a task's report as
`_build/l3.32-<task>-report.md`. The live series names reports
`_build/lj-1.127-report.md`. The live shape is now tried first.

### 6. Stall detection is STRUCTURALLY BLIND on the herdr path. NOT FIXED

**Both halves of the detector are dead there, and 5b only repaired one input to
one half.**

- The repeat-diff half needs a log over 2,000,000 bytes. **MEASURED:** herdr
  driver logs are 955 to 2,105 bytes, because the log holds the driver's own
  JSON and not the agent's stream. The codex-path log `LJ-1.122` is 2,149,796
  bytes for comparison.
- The quiet-deliverable half needs `log.mtime > report.mtime`. **MEASURED:** a
  herdr log is written at launch and again at the end, so during the run its
  mtime is frozen near launch and the condition is false whenever the report
  has been touched since.

**What it would take.** The agent's stream lives in the pane, not the log. A
real cure polls `herdr agent read` periodically into the log, which changes the
driver from a two-command script into a loop. That is a rewrite of the
mechanism and the brief forbids one, so I stopped and priced it instead:
roughly 30 lines in the driver plus a decision about polling cost.

### 7. A herdr RESUME cannot work after a clean finish, by construction. DOCUMENTED, NOT FIXABLE HERE

**MEASURED from two logs.** The driver closes the pane on a clean finish, which
destroys the agent, so `agent prompt` returns `agent_not_found`. Both
`herdrtest1` resume attempts failed exactly that way: the first against
`herdrtest1-resume` (before the name fix) and the second against `herdrtest1`
(after it).

**So the herdr-by-name resume works in ONE case: the driver died and the agent
did not.** That is real but narrow. The driver now says so at the point of
failure instead of writing the error into a final message and exiting 0.

**The positive path remains UNTESTED, as the added scope suspected.** Testing it
needs a live agent whose driver is then killed, which costs a dispatch and a
kill on a machine a sibling is measuring on. I did not do it.

### 8. `herdr, then pi` was UNREACHABLE, and it is the policy's own head. FIXED

**Symptom.** `HERDR_KIND = {"herdr": "codex", "pi": "pi"}` with
`kind = HERDR_KIND.get(HARNESS, "codex")` computed **inside** the
`HARNESS == "herdr"` branch. The lookup could only return `codex`, and
`--harness pi` took the separate direct-exec branch. **The one combination the
map promised was the one combination the tool could not run**, and it is
exactly the head both policy versions name.

**Fix.** `--harness herdr-pi`. **MEASURED on herdr 0.8.0:** `herdr agent start
--kind` lists `pi` among its possible values. **Verified:** the generated
command is `herdr agent start <name> --kind pi --pane "$PANE" -- --provider
deepseek --model deepseek-v4-pro`, and `bash -n` returns 0.

### 9. A transient `herdr pane list` failure created a SECOND WORKSPACE. FIXED

**Symptom.** `herdr pane list | python3 -c ...`: a herdr server that is down, or
any JSON shape change, threw inside the one-liner, left `BASE` empty, and an
empty `BASE` meant `workspace create`. **That is the `w8` failure arriving
through a second door**, and `LJ-1.125` ran in `w8` while
`.state/herdr-workspace` now holds `w7`.

**Fix.** The two cases are separated. `pane list` failing is an abort; a
workspace with no panes is still a create. **Verified MEASURED** against three
payloads: real herdr output gives `w7:p1`; `garbage` exits 1 so the driver
stops; `{"result":{"panes":[]}}` gives an empty base so the driver creates.

**And the base pane was whatever came first.** MEASURED: the only pane in `w7`
is the orchestrator's own claude pane, so every dispatch splits it; once agents
exist, `m[0]` can be a live agent's pane, which a clean finish is about to
close, and splitting a closing pane is a race that kills the new dispatch with
`agent_pane_busy`. The selection now prefers a pane with no agent. **Verified
MEASURED** on a synthetic two-pane payload: it picks the agent-free pane.

### 10. Answers to the added scope's remaining questions

- **Does a killed driver free the Agda slot correctly?** **It frees the slot and
  the agent keeps running.** INFERRED from the architecture: the herdr server
  owns the pane, so killing the bash driver cannot reach the agent. Under
  setsid, killing the process killed the agent. **So the slot ceiling can now
  UNDERCOUNT**, which C-12 cares about. NOT FIXED: the honest cure is for the
  driver to kill its herdr agent when it is itself terminated, which needs a
  trap and a decision about whether a killed driver should kill a working
  agent. That is a ruling, not a bug fix.
- **Does a driver that exits early leave the slot held?** No. INFERRED: the slot
  keys on the driver pid, and a dead pid holds nothing.
- **Does `status` read cleanly with the test records in the registry?**
  MEASURED yes, exit 0, and **nothing is reported live that is not**:
  `agents live: 0` while `herdr agent list` shows only the orchestrator.
- **What if `.state/herdr-workspace` holds a malformed value?** MEASURED: the
  file holds `w7` with no newline; `cat` in a command substitution strips
  trailing newlines anyway; a value matching no pane now means create, and an
  unreadable pane list means stop.
- **Two herdr dispatches at once.** Both read the pane list and can pick the
  same base. INFERRED safe: two splits of one pane produce two panes at
  narrower widths, which costs display space and nothing else. The dangerous
  case was picking a CLOSING agent pane, which finding 9 removes.
- **`agent wait --timeout` units.** MEASURED from `herdr agent wait --help`:
  milliseconds. `--timeout 120000` is 120 seconds, as intended.
- **A name collision drove the WRONG agent.** Found by me and FIXED. If
  `agent start` fails because the name exists, the retry loop burns 20 seconds
  and `agent get` then SUCCEEDS, because it finds the OLD agent; the driver
  would prompt the previous run's agent in the previous run's pane and close
  the new empty pane. The driver now compares the pane herdr reports against
  the pane it split. **The comparison is best effort and says so at its site:**
  `agent get`'s success shape is INFERRED from `agent start`'s, so an
  unreadable shape skips the comparison rather than failing every dispatch on a
  guess. MEASURED: the extractor returns `w7:p9`, `''` and `''` on a valid, an
  error and a garbage payload.
- **`launch()` printed ONE defect and returned.** The `return 1` sat inside the
  `for` loop, so a brief with four defects cost four round trips. FIXED.
- **`main()` forced `HARNESS = "codex"` for every subcommand without
  `--harness`.** `cmd_resume` overwrote it from the record, which hid the
  defect; nothing else did. FIXED to fall back to the policy default.
- **`status` prints all 344 registry records.** NOT FIXED. The dead
  `if ... : pass` at the top of the loop says the full listing is deliberate. A
  cure that hides an old record could hide a real signal, so it is a decision
  for the orchestrator rather than a bug for me.

## 6. Verification, and what still needs a run

| Check | Result |
|---|---|
| `make dispatchpolicy` | MEASURED clean: 406 briefs, 4 notes, 0 failures |
| `scripts/check-dev-docs.py` | MEASURED clean, 6 subchecks |
| `scripts/check-rule-ids.py` | MEASURED clean: 44 files, 141 lessons, 66 decisions |
| `scripts/check-task-index.py` | MEASURED clean: 428 codes, 444 rows |
| `scripts/lint-prose.py --check` on every document I touched | MEASURED clean |
| `.claude/skills/codex-dispatch/tests/test_territory.py` | MEASURED 13/13 |
| `dispatch.py status`, `check`, `gate-ready` | MEASURED, all run |
| Generated herdr drivers, all three shapes | MEASURED `bash -n` rc 0 |
| `make check` | **NOT RUN.** The brief forbids it. The orchestrator must run it |

**`test_deletion_test.py` and `test_dev_docs.py` each fail one assertion, and
both failures are PRE-EXISTING.** They are a suspended ledger threshold and an
`AGENTS.md` word-cap fixture. I touched neither script.

## 7. DD4

**Maximize the code the two proofs share, and write it generic.** This task
wrote no Agda, so DD4 binds it only by analogy, and I applied the analogy
rather than skipping the line. The policy is written ONCE, in one module, and
every consumer derives from it: the checker imports it, `dispatch.py` imports
it, and the documents point at it instead of restating it. **The alternative,
a table in ORCHESTRATION and a second in PLAN and a third in `AGENTS.md`, is
the fixed shape** that DD4 refuses in code and that DD19 refuses in prose, and
`check-dispatch-policy.py` gates it: a governed document naming the head model
without pointing at the switch fails.

## ARCHIVE USED

- `archive/dev/DECISIONS-archived.md`: NOT read. The dispatch policy is DD17
  and DD25, both live rows in `dev/PLAN.md` section 3. The archived `D` series
  covers the retired route and bears nothing on which head runs a dispatch.
- `archive/dev/TASKS-archived.md`: NOT read directly. Its rows resolve through
  `check-task-index.py`, which I ran, and the tasks this work cites
  (`[LJ-1.121]`, `[LJ-1.124]`, `[LJ-1.125]`, `[LJ-1.126]`) are all live-series.
- The forensic corpus I DID read is `.claude/skills/codex-dispatch/.state/`,
  which is not an archive but is where the measurements are: `registry.json`
  (344 records), `returns.log:364-365`, and the logs named at each finding.

## LITERATURE USED

**`dev/literature/` holds nothing on dispatch policy, and I read none of it.**
That corpus is the digested mathematics: `digest.md`, `j-hierarchy.md`,
`fine-structure.md`, `rudimentary-functions.md`, `devlin-errata.md`,
`primary-sources.md`, `BIBLIOGRAPHY.md`, `formalizations-landscape.md`. This
task writes tooling and process rules and touches no mathematics.
