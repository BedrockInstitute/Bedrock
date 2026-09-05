# LJ-1.190 report: reconcile `dispatch.py` against the dispatch SKILL

## The headline

- **Contradictions: 3 material, between the script and the skill.** The canon
  settled two of them and the script now carries the fixes. One stays open:
  the read-only refusal never fires for the modern report home, and its fix is
  an addition this brief did not authorize.
- **Lines deleted: 7. Lines added: 13. Net: +6.** The file is 2276 lines
  after the edit, from 2270. `py_compile` passed after the edit.
- **The model-flag finding of [LJ-1.188] is confirmed, not contradicted.** The
  script never reads the model from the brief's `tier:` line, and its comments
  do not claim it does.
- **The acceptance test is byte-identical before and after.** Six live briefs,
  the exact command from the brief, exit codes and outputs unchanged.

## The before and after check table

Command: `python3 .claude/skills/codex-dispatch/dispatch.py check <brief>`.
Each result below is the full output; `before == after` is byte-for-byte for
all six.

| # | brief | kind | era | exit | output |
|---|---|---|---|---|---|
| 1 | LJ-1.147 | build | override | 1 | `dispatch: brief is kind \`build\` (derived from its write scope) and does not cite 6 mandatory rule(s): P-h, P-k, P-n, R-35, R-38, R-40. Run \`python3 scripts/rules.py --for build\` and paste the bundle into SCOPE (read). This is a refusal, not a reminder: the orchestrator's memory is what drifted.` |
| 2 | LJ-1.100 | probe | pre-epoch | 1 | `dispatch: brief is kind \`recon\` (derived from its write scope) and does not cite 1 mandatory rule(s): C-42. Run \`python3 scripts/rules.py --for recon\` and paste the bundle into SCOPE (read). This is a refusal, not a reminder: the orchestrator's memory is what drifted.` |
| 3 | LJ-1.186 | recon | current | 0 | `dispatch: LJ-1.186.md is well formed for sandbox workspace-write` |
| 4 | LJ-1.139 | rewrite | override | 1 | `dispatch: brief is kind \`recon\` (derived from its write scope) and does not cite 2 mandatory rule(s): P-l, C-42. ...` plus `dispatch: brief does not carry DD4. It is the route's core constraint and it has NO metric and no checker by the owner's ruling, so being stated in every brief IS its enforcement. Add both halves: maximize the code the two proofs share, and write it generic. This is a refusal because the same mechanism already drifted once, uncited in 102 of 112 briefs over five days.` |
| 5 | LJ-1.181 | adversarial review | override | 0 | `dispatch: LJ-1.181.md is well formed for sandbox workspace-write` |
| 6 | LJ-1.91 | pre-epoch | pre-epoch | 1 | `dispatch: brief is kind \`recon\` (derived from its write scope) and does not cite 1 mandatory rule(s): C-42. Run \`python3 scripts/rules.py --for recon\` and paste the bundle into SCOPE (read). This is a refusal, not a reminder: the orchestrator's memory is what drifted.` |

The full outputs are saved at `/tmp/lj1190/before-*.out` and
`/tmp/lj1190/after-*.out`. The before copy of the script is at
`/tmp/lj1190/dispatch.py.before`. A diff of the six pairs is empty.

## The contradictions, and which side the canon settles

**C1. The tier refusal message asserted a fixed default. CONTRADICTION. The
script was wrong. The canon is DD17 plus `scripts/dispatch_policy.py`, and
the script now follows it.** The old message (`dispatch.py:676-678` before
the edit) said: "ORCHESTRATION section 1: codex is the default and an opus
tier must name its exception. If the sentence will not write, the tier is
codex." Three of its claims are false today. Under the version in force,
`deepseek-subagent-mode`, the default head is pi and not codex
(`dispatch_policy.py:117-131`). Opus is a legal token in both tables
(`dispatch_policy.py:118,132`), never an exception. The fallback is codex,
but "take the head the table gives" means the case's head, not a fixed one
(`dev/PLAN.md` DD17 row, line 254). The old message also cited ORCHESTRATION
section 1 for a claim section 1 no longer makes: section 1 says the head
lives in the switch and "does NOT restate the tables"
(`dev/ORCHESTRATION.md:15-18`). The refusal still fires; the message now
names the switch as the head's home and states DD17's fallback rule
(`dispatch.py:680-684`). The acceptance test is unchanged because all six
briefs carry a `tier:` line, so the message never prints in the test.

**C2. The read-only refusal never fires for the modern report home.
CONTRADICTION. The script's trigger is stale. The canon is silent on the
refusal's exact trigger, so this is a finding for the owner.** The skill
says: "a brief that orders a written deliverable under read-only is
REFUSED: the agent cannot write its own report", and its refusals table
repeats it. The script's triggers are `WRITE_ORDER`
(`dispatch.py:600-602`), which demands a write verb within 80 characters of
`_build/`, and `scope_names_path` (`dispatch.py:686`), which matches
`_build/|src/` inside SCOPE (write). Both are keyed to the retired homes.
MEASURED 2026-08-14: `check agents/tasks/LJ-1-186/LJ-1.186.md --sandbox
read-only` exits 0, and the same for `LJ-1.190.md`, although both briefs
order written deliverables in `agents/tasks/`. A legacy-style brief whose
scope names `_build/...-report.md` (LJ-1.100) IS refused under read-only,
so the refusal works only for the paths it knows. The fix is to widen the
patterns to the modern homes (`agents/tasks/`, `dev/`, `scripts/`,
`.claude/`). That is an addition and changes behavior by refusing more
briefs, so this brief does not authorize it. The guard stays, with this
reason. KEPT.

**C3. The `_build/briefs/` pin acceptance contradicted ORCHESTRATION
section 3. CONTRADICTION. Resolved by deletion.** ORCHESTRATION section 3
pins every brief in `agents/tasks/<TASK>/` so it survives a reboot and the
owner can read it. `_build/` is a temporary folder by AGENTS.md's own
words, git-ignored (`.gitignore:2`), and `make clean` empties it
(`Makefile:202`). The disjunct accepted a home the rule forbids. The skill
records both homes as current ("a brief not pinned in `agents/tasks/<CODE>/`
(or legacy `_build/briefs/`)" and mistake 5's "(Both homes are now
accepted...)"). I did not edit the skill. The orchestrator rules where
those two skill statements land.

**C4. The skill says `--agda` "also answers the model rule (`model_for`)".
CONTRADICTION, minor. The script's behavior is right.** The script's
`--agda` flag only books an Agda slot (`dispatch.py:217-218`, the
`agda_holders` accounting in `launch()`). It never calls `model_for()`.
The skill's own model-rule section says the orchestrator overrides with
`--model` and the default is `deepseek-v4-pro`, which matches the script
(`dispatch.py:82`, `dispatch.py:2206`). The phrase in the commands section
is loose and not harmful. KEPT.

**Non-contradiction, confirmed: the model is a command-line flag.** The
script's `--model` default is `DEFAULT_MODEL` (`dispatch.py:82,2206`), the
tier check only tests presence (`dispatch.py:679`), and no code path reads
a model from the tier line. The script's comments are silent on the point
and never claim the tier drives the model. The skill records the fact
correctly. KEPT, no edit.

## The deletions, with the reachability claim

**D1. The `_build/briefs/` disjunct in the pin check. DELETED. Claim:
nothing reaches it. INFERRED, on four measured facts.** The disjunct was
`real.parent == (ROOT / "_build" / "briefs").resolve()` (`dispatch.py:663`
before the edit). The facts: the directory does not exist (`ls _build/`
shows no `briefs/`); `_build/` is git-ignored (`.gitignore:2`); `make
clean` empties `_build/` except `literature` (`Makefile:202`); and the
registry's 350 records whose brief path starts with `_build/briefs/`
(`.claude/skills/codex-dispatch/.state/registry.json`) point at files that
no longer exist, because the briefs moved to `agents/tasks/`. The only way
to reach the disjunct is to recreate the exact workaround AGENTS.md
forbids and the skill records as an error (mistake 6). The reachability
claim is INFERRED, not MEASURED: the directory could in principle be
recreated. Measured flip: a fixture at `_build/briefs/lj1190-fixture.md`
passed `check` before the edit (exit 0, "well formed") and is refused
after (exit 1, "brief is not pinned", with the message naming the correct
home). The fixture was removed and `_build/briefs/` was deleted again;
nothing remains. The incident comments around the check are kept and
record the removal (`dispatch.py:659-665`).

**D2. The two comment lines "Both homes are accepted...". DELETED and
replaced.** They described a permission the deletion removes
(`dispatch.py:659-660` before the edit). The replacement is a removal
record that keeps the incident history: the home moved, the check did not,
and the in-harness mode hid it (`dispatch.py:659-665`). The narrative that
explains why the refusal exists is untouched.

**D3. The three message lines asserting the fixed default. DELETED and
replaced.** They carried C1's false claims (`dispatch.py:676-678` before
the edit). The replacement names the switch as the head's home and DD17's
fallback rule (`dispatch.py:680-684`).

## What I left, and why

**L1. The read-only refusal (C2). KEPT.** Removing the `_build/` and
`src/` terms would weaken the refusal until it never fires. Widening it is
an addition this brief does not authorize. A guard left with a reason is
the better return.

**L2. The stall_note report derivation. STALE comment, KEPT code.** It
tries `_build/<task>-report.md` and `_build/l3.32-<task>-report.md` as the
report homes (`dispatch.py:1519-1520`) and its comment calls the first
"the live shape". The live shape is now `agents/tasks/<TASK>/`; no
`_build/*-report.md` exists anywhere (measured), so the quiet-deliverable
half of the stall detector derives nothing for current records. The repair
is an addition (add the modern home). A deletion alone would make the
detector quieter without fixing it. This is an internal staleness; the
skill does not describe stall detection.

**L3. The incident record naming the retired mode.** "the DD17 override
sends every default dispatch in-harness" (`dispatch.py:653-656`). KEPT. It
is a dated record of why the pin defect hid, the mode it names was in
force when the incident happened, and the name resolves through `ALIASES`
(`dispatch_policy.py:104-112`), so C-41 holds. It does not present the
retired mode as current.

**L4. The script is silent on the model-flag fact.** KEPT. A comment
asserting the fact would be an addition; the code is already the evidence,
and the skill is the record.

## DD4

The question the brief asks: is any refusal written for one mode or one
head when it should be written for both? Answer: no refusal is mode-keyed.
The read-only refusal is HOME-keyed: its triggers name the retired `_build/`
home and `src/`, so it is blind to `agents/tasks/`. That is the same shape
class as the pin defect, but the axis is the report home, not the mode. The
pin, tier, SCOPE, RETURN, evidence, ARCHIVE, LITERATURE, DD4 and rule-bundle
refusals are mode-independent. The herdr-specific guards exist because herdr
adds the pane abstraction the other two harnesses lack, and the fresh and
resume drivers have carried the same guards since [LJ-1.127].

## The searches I ran (the 2026-08-14 trap)

- Read the file whole (2270 lines), not by grep.
- Greps: `_build` (11 hits), `normal` (1, unrelated), `override` (1, the
  incident record), `flash` (2, both historical), `model_for` (0), `tier`
  (4), `DEFAULT_MODEL` (4).
- The wrapped-phrase hunt: the tier message splits "codex is the " and
  "default" across two source lines, so a line grep for "codex is the
  default" misses it. It was found by reading the file whole. This is the
  same shape the trap warns about.

## ARCHIVE USED, at file:line

- `.claude/skills/codex-dispatch/dispatch.py`, read whole. Sites: module
  docstring 1-60; the D17 model comment 76-84; `DEFAULT_MODEL` 82;
  `HARNESS` from the policy 106-116; `HERDR_KIND` 154;
  `HERDR_WORKSPACE_LABEL` 180; `HERDR_WS_FILE` 188; `AGDA_HEAP` and
  `AGDA_SLOTS` 217-218; `SESSION_RE` 231; `WRITE_ORDER` 600-602;
  `check_model` 604-616; `launch_defects` 618-635; `validate` 637-731, with
  the pin 643-674, the tier 679-684, the read-only and Agda checks 686-704,
  the SCOPE, RETURN and evidence checks 705-729; `launch` 733; `cmd_run`
  1218; `cmd_queue` 1233; `brief_in_flight` 1318; `write_paths` 1337;
  `territory_in_flight` 1376; `cmd_resume` 1427; `stall_note` 1508, with
  the `_build/` candidates 1519-1520; `cmd_status` 1626; `cmd_wait` 1842;
  `cmd_gate_ready` 1960; `dd4_defects` 1982; `survey_defects` 2020;
  `brief_kind` 2077; `rule_bundle_defects` 2146; `cmd_check` 2183; `main`
  2195.
- `.claude/skills/dispatch-herdr/SKILL.md`, read whole. Taken: the two mode
  tables, the model rule, the tier section, the refusals table, mistakes 5
  and 6, the waiter contract, the herdr facts. The before copy of the
  script, `/tmp/lj1190/dispatch.py.before`, for the diff and the
  before-test.
- `scripts/dispatch_policy.py`, read whole. Sites: `VERSION_IN_FORCE` 52;
  `MODEL` 91; `FLASH` 105; `model_for` 108-110; `ALIASES` 114-116; both
  tables 117-171; `LEGAL_TOKENS` 178; `default_harness` 216-236.
- `dev/PLAN.md`: DD0 row 244; DD4 row 247; DD17 row 254; DD18 row 255; DD25
  row 260.
- `dev/ORCHESTRATION.md`: section 1, 13-66; section 1.1, 67-115; section 2,
  117-139; section 2.1, 139-167; section 3, 167-241.
- `agents/tasks/LJ-1-188/lj-1.188-report.md`, read whole. Taken: the
  model-flag finding and the measured evidence for the ten mistakes.
- `.claude/skills/codex-dispatch/.state/registry.json`, read-only. Taken:
  the 354 records and the `_build/briefs/` string paths that no longer
  resolve.
- `.gitignore:2` and `Makefile:202`, read. Taken: the two measured facts
  for D1.

## LITERATURE

Not this task's subject. Nothing in `dev/literature/` bears on a
dispatch-tooling reconciliation; DD18 is satisfied by this one line.

## What was run and what was not

- Ran: `check` on the six briefs before and after (byte-identical);
  `check --sandbox read-only` on three briefs (the C2 measurement); the
  transient `_build/briefs/` fixture test for D1, removed after; `py_compile`
  after the edit (passed).
- Did not run: `run`, `queue`, `resume`, `wait`, Agda, `make check`.
  Nothing was launched. Nothing was committed. The two scope files are the
  only ones I wrote. The `dev/PLAN.md` modification in the working tree
  belongs to a sibling task (LJ-1.186) and was not touched. `_build/`
  gained `literature`, `README.md` and `tools` during this session from a
  sibling's work (LJ-1.187 re-organizes `dev/`); my fixture left no trace.
