# LJ-1.188 report: the dispatch and herdr knowledge, written as a project SKILL

## The deliverable

**Skill path:** `.claude/skills/dispatch-herdr/SKILL.md` (401 lines, local only,
not committed, because `.gitignore:19` ignores `.claude/`; MEASURED).

**Its `description:` line, quoted whole:**

> "How to dispatch, queue, resume, wait on, stop and inspect Bedrock's coding
> agents through .claude/skills/codex-dispatch/dispatch.py and the herdr pane
> server: the DD17 head tables and both modes in scripts/dispatch_policy.py,
> the model rule (deepseek-v4-flash for pure natural-language work,
> deepseek-v4-pro for Agda), the brief's tier: line, the refusals dispatch.py
> enforces, the waiter contract (one report, then re-arm), C-12's Agda slots,
> and the herdr agent commands. Load when about to dispatch, queue, resume,
> stop or kill an agent; read dispatch status; arm or re-arm a waiter; choose
> a head or a model; write a tier: line; or touch a herdr pane, agent name or
> send-keys. Triggers: dispatch, queue, resume, stop agent, kill agent,
> status, waiter, arm waiter, re-arm, tier, head, model, herdr, agent name,
> send-keys, 派子agent, 派agent."

The trigger works from the model side. The `description:` field is the
mechanism the two sibling skills use (`asd-ste100/SKILL.md` frontmatter,
`codex-dispatch/SKILL.md` frontmatter). The description names the actions and
the keywords, and the body has no slash command and no magic word. The
trigger requirement is met.

## The ten mistakes of 2026-08-14, present or absent in the skill

| # | Mistake | In the skill | Where |
|---|---|---|---|
| 1 | `pkill` does not kill a herdr agent | PRESENT | "herdr, the pane server" and mistake list item 1. The `agent_name_taken` refusal is now MEASURED from the launch log, not taken on account |
| 2 | A `RUNNING` row is not proof the launch worked | PRESENT | mistake list item 2. The launch log's third line being the error is now MEASURED from the log itself |
| 3 | One waiter reports once | PRESENT | "The waiter contract" and item 3 |
| 4 | The tool shouts and the orchestrator filtered it out | PRESENT | "The waiter contract" and item 4 |
| 5 | A broken path stays green while nothing walks it | PRESENT | item 5, with the `agents/tasks/` pinning rule and the `_build/briefs/` episode |
| 6 | The refusal cited the rule that contradicted it | PRESENT | item 6, with the rule to open the cited rule |
| 7 | An in-harness dispatch bypasses every refusal | PRESENT | "What an in-harness mode changes" and item 7 |
| 8 | Two agents in one cluster collide | PRESENT | item 8, with the sibling-redness brief line and the same-report-path episode |
| 9 | The head and the model are two different choices | PRESENT | "The model rule" and item 9, plus the new measured finding below |
| 10 | Taking an exception's head without its conditions is invisible | PRESENT | item 10 and the DD0 section, with the fable episode and the test sentence |

## The mechanics, present or absent

| Mechanic | In the skill | Where |
|---|---|---|
| Register the task row before dispatching (PLAN 6.0 rule 6) | PRESENT | "The dispatch commands" |
| `dispatch.py check <brief>` validates without launching | PRESENT | "The dispatch commands" and the refusals table |
| `queue` waits and detaches; `run` launches now; `--wait` blocks | PRESENT | "The dispatch commands" |
| `--agda` declares an Agda process, which C-12 caps | PRESENT | "The dispatch commands" and the C-12 section |
| `resume <task> --note` continues a killed or exhausted agent | PRESENT | "The dispatch commands" |
| The refusals and what each one is for | PRESENT | the full refusals table |
| Both mode tables, the invariant, `ALIASES` | PRESENT | "The two modes, both tables" |
| `model_for()` and its blind spot | PRESENT | "The model rule" |
| The six-step mode-switch checklist | PRESENT | "The mode-switch checklist" |
| The emergency tier's two conditions | PRESENT | "The rules that bind the dispatcher" |
| DD25, DD0, DD18, DD4, C-12, PLAN 6.0 | PRESENT | "The rules that bind the dispatcher" |
| The herdr subcommand list and its two absences | PRESENT | "herdr, the pane server" |

## What this brief and the code contradict, with the evidence

**1. The tier line does not drive the model. The code contradicts the brief's
framing of mistake 9, and the skill now says so.** The brief says a tier line
"names the head, the mode, and the model when it is not the default". The
code shows that `dispatch.py` never reads the model from the brief:
`cmd_run` takes `a.model`, whose default is `DEFAULT_MODEL` =
`deepseek-v4-pro` (`dispatch.py:144`), and the brief is used only as the
prompt text. The tier line is a record for the audit; the model is a
command-line flag. MEASURED, 2026-08-14: the first LJ-1.187 launch ran
`--model deepseek-v4-pro` (the agent-start `argv` in
`.claude/skills/codex-dispatch/.state/logs/LJ-1.187-20260814-101302.log`
line 3), while `agents/tasks/LJ-1-187/LJ-1.187.md` names flash. The skill now
carries a line: "THE MODEL IS A COMMAND-LINE FLAG, AND THE BRIEF DOES NOT
CHANGE IT." This was the most valuable thing the sweep found.

**2. The episode claims measured true from the surviving logs.** The brief
said the re-dispatch was refused with `agent_name_taken` and that the launch
log's third line was the error. Both are now MEASURED from
`.claude/skills/codex-dispatch/.state/logs/LJ-1.187-20260814-101353.log`:
line 1 is `HERDR base=w7:p1`, line 2 is `HERDR pane=w7:pG`, line 3 is the
first `{"error":{"code":"agent_name_taken",...}}`, and the error names the
old agent's pane `w7:pF` with `status=Working`. The old agent kept running
and kept its name. The queue log for that dispatch reads "EXITED IMMEDIATELY
(rc 1)". Nothing in the brief is contradicted here; the claims are confirmed
with the evidence in hand.

**3. A refinement to mistake 2, INFERRED from the same logs.** "That row was
the OLD agent" is not quite the registry mechanics. `launch()` writes the
new record before the driver runs, and the re-dispatch's driver lived about
twenty-five seconds while it retried `agent start`, so a `RUNNING LJ-1.187`
row in that window was the re-dispatch's own fresh record, not the old one.
The old agent's herdr listing (`status=Working` in the error) is the second
candidate. Either way the lesson is the same and it stands: only the launch
log tells whether a launch worked. The skill states the lesson and not the
contested mechanism.

**4. The herdr subcommand list is confirmed exactly.** `herdr agent --help`
(MEASURED 2026-08-14) lists `list, get, read, send-keys, prompt, rename,
focus, wait, attach, start, explain`, with no stop and no kill. The skill
repeats the list and the two absences.

**5. `send-keys C-c` stopping a pi agent is UNMEASURED.** The episode that
two C-c did not stop a working pi agent is recorded in the skill as an
episode; the positive claim is marked UNMEASURED and the skill does not
recommend it. The only known-working stop is closing the pane
(`herdr pane close`), MEASURED 2026-08-13: agents die with their pane or
workspace. The skill says the close is irreversible.

## The abort criteria, checked

- **WRITTEN.** The skill exists at `.claude/skills/dispatch-herdr/SKILL.md`,
  its description names the triggers, and every item in the brief is in it.
  The description is quoted whole above.
- **A CLAIM ABOVE IS WRONG.** Yes: the tier-line-drives-the-model framing.
  The code wins; the skill is corrected and the correction is reported above.
- **THE TRIGGER CANNOT BE MADE TO WORK FROM THE MODEL SIDE.** It can. The
  `description:` field is the standard mechanism, used by both sibling
  skills. No owner-typed command was substituted.

## Operational claims, classified

All herdr CLI facts: MEASURED 2026-08-14 via `herdr agent --help`,
`herdr agent start --help` (possible values include `pi`), `herdr agent
wait --help` (states `idle, working, blocked, done, unknown`), `herdr agent
rename --help` (`--clear`), `herdr agent prompt --help` (`--wait`,
`--until`). The `.claude/` ignore: MEASURED at `.gitignore:19`. The
`agent_name_taken` refusal, the third-line error, and the launch-log rule:
MEASURED from the surviving LJ-1.187 logs. The model-flag gap: MEASURED
from the same logs. The tier-line/checker behavior (a brief is judged by the
mode it names): MEASURED 2026-08-14 in `check-dispatch-policy.py` and its
own comment. The fable episode, the 52 frozen briefs, the broken-pinning
episode, and the pkill episode: the orchestrator's recorded accounts,
confirmed where the code comments or the logs speak. `send-keys C-c`:
UNMEASURED. Nothing is presented as measured that was not observed.

## ARCHIVE USED

- `.claude/skills/codex-dispatch/dispatch.py`, read whole (2270 lines). The
  primary source. Sites taken: the launch funnel and its refusals
  (`validate` at line 637, `launch_defects` at line 618,
  `dd4_defects` at line 1976, `survey_defects` at line 2014), the pinning
  check's two homes inside `validate` (around lines 640 to 660), the waiter
  contract at `cmd_wait` ("One waiter reports once; that is the whole
  contract.", line 1950), the `status` banners in `cmd_status` and
  `warn_if_unarmed` (the `!! RETURN(S) NEVER REPORTED` line at 1656, the
  `!! NO WAITER IS ARMED` line at 1829), the herdr driver and its
  guards around lines 700 to 900, the model block and `DEFAULT_MODEL` at
  line 82, the herdr workspace and name facts in the header comments.
- `.claude/skills/codex-dispatch/SKILL.md`: the harness history, the pane
  sweep, the three trial findings, the launch-log and model facts. Taken for
  the herdr section and the mistake list.
- `.claude/skills/asd-ste100/SKILL.md`: the frontmatter shape and how a
  description names triggers. Taken for the description.
- `scripts/dispatch_policy.py`, read whole: the switch, `ALIASES`,
  `model_for()`, both tables, the invariant, `EMERGENCY_TOKEN = "fable"`,
  `LEGAL_TOKENS`, the honest limit. Taken for the modes section.
- `scripts/check-dispatch-policy.py`: the tier token rule, the epoch, the
  brief-is-judged-by-the-named-mode rule (its own comment, 2026-08-14).
  Taken for the tier section.
- `scripts/check-dd4-stated.py`: the heading-only gate and the frozen
  twelve. Taken for the DD4 section.
- `dev/ORCHESTRATION.md` sections 1 to 3: the switch-is-one-home rule, DD25
  operational form, slots, section 2.1's quiet-machine rule, section 3's
  brief clauses. Taken for the rules section.
- `dev/PLAN.md`: DD0, DD4, DD17 (including the six-step checklist), DD18,
  DD19, DD25, section 6.0, section 11. Taken for the rules section.
- `dev/LESSONS.md`: C-43, C-41, C-12, C-22, C-42, D-10, P-l, D-26 and the
  rest of the mandated list. Taken for the rules and the classification
  discipline.
- `dev/JOURNAL.md` 2026-08-14: the DD0 fable episode, the DD17 entry
  confirming "it had refused EVERY dispatch since the briefs moved into
  `agents/tasks/`". Taken for mistake 5 and mistake 10.
- `.claude/skills/codex-dispatch/.state/logs/LJ-1.187-*.log` and
  `.state/registry.json`: the surviving evidence of the 2026-08-14 episode.
  Taken for the measured confirmations above. Read-only.

Why not the archives of the retired route: the retired route's dispatch
mechanics predate herdr and the switch, and nothing in them bears on this
task's subject; `archive/dev/TASKS-archived.md`, `JOURNAL-archived.md` and
`DECISIONS-archived.md` were not opened.

## LITERATURE

Not this task's subject. Nothing in `dev/literature/` bears on a
tooling-and-prose skill; DD18 is satisfied by this one honest line.

## DD4

The skill itself follows the rule it encodes. It is written generic: it
carries both mode tables, so it serves any head and any mode, and its
description fires on the model's own keywords, so it loads for any dispatch
context rather than only for the cases that bit one week. The mode tables
are the shared carrier; the mistakes and the rules are the per-case
instances. No fixed shape was written for the week's mode.
