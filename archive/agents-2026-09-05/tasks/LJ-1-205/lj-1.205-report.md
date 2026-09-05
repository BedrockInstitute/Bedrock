# LJ-1.205 report: reconcile the dispatch skill against herdr's official skill

## The counts

- **Lines deleted as duplication: 7.** The frozen subcommand snapshot, 5;
  the `--until` state list, 2.
- **Lines added as gaps: 59.** Pointers to the official skill, plus the
  facts that belong to Bedrock's use. Net +52: the skill is 500 lines now,
  from 448.
- **Contradictions found: 4 disagreements examined.** 3 resolved on close
  reading, with no fact changed. 1 is a real difference, LEFT OPEN.
- **Abort criterion: RECONCILED.** Ours was not "already right": two
  duplications existed and are gone. It was not superseded either: the
  official skill covers only the tool, and Bedrock's half (dispatch.py, the
  modes, the refusals, the waiter, the ten mistakes, the rules) has no
  counterpart in it, so ours could not shrink to "the Bedrock-specific
  half" alone. The honest result is a middle: 7 lines of duplication
  removed, 59 lines of pointer-plus-measurement added.

## Deletions, with what each pointer now says

| Deleted | Lines | What the pointer now says |
|---|---|---|
| The subcommand snapshot: "The agent subcommands, MEASURED 2026-08-14 via `herdr agent --help`: `list`, `get`, `read`, `send-keys`, `prompt`, `rename <target> --clear`, `focus`, `wait`, `attach`, `start`, `explain`." | 5 | The official skill's CLI-discovery doctrine is the rule: the installed binary is the authority for command syntax, so print `herdr --help` and the command group (`herdr agent`, `herdr pane`) instead of trusting a snapshot. A frozen list drifts; the binary does not. The measured finding stays: there is NO `agent stop` and NO `agent kill` subcommand, and the official skill documents none either (it documents `herdr server stop` only as a prohibition, `.claude/skills/herdr/SKILL.md:193`), so the finding stands. |
| The `--until` state list: "takes `idle`, `working`, `blocked`, `done`, `unknown` (MEASURED 2026-08-14)" | 2 | The official skill documents the five lifecycle states and their meanings (`.claude/skills/herdr/SKILL.md:54,58`) and `--until` (`.claude/skills/herdr/SKILL.md:132-138`). The unique measured content, the TWO PHASE wait, stays with its dates. |

Both deletions are classified DOCUMENTED by the official skill (the states
and the discovery doctrine), so the duplication risk the brief names is
gone: the fact now lives in one place, and that place is the regenerable
official file, which `herdr --skill` rewrites byte-identically (measured,
this run).

## Additions, as gaps or pointers

| Added | Class | Why |
|---|---|---|
| Authority pointer: `.claude/skills/herdr/SKILL.md` is the authority on the TOOL, regenerates from the binary, and this section keeps only what Bedrock measured or what `dispatch.py` does. | DOCUMENTED | The DD4 spine: a fact maintained in both is paid for twice, and the one that drifts is ours. |
| CLI-discovery doctrine pointer. | DOCUMENTED | Official `.claude/skills/herdr/SKILL.md:19-38`. |
| `HERDR_ENV=1` requirement; `dispatch.py` assumes a herdr-managed session and does not check it. | DOCUMENTED and INFERRED | Official `.claude/skills/herdr/SKILL.md:11-16`; the absence of a check in the driver. |
| Name grammar `[a-z][a-z0-9_-]{0,31}` and name-clearing on exit. | DOCUMENTED | Official `.claude/skills/herdr/SKILL.md:56`. Agrees with the measured lowercase mapping, kept. |
| `agent start` requirement: the pane at its interactive prompt, never creates layout, 30-second startup timeout. | DOCUMENTED | Official `.claude/skills/herdr/SKILL.md:54,120`. Complements the measured fresh-pane retry, kept. |
| `agent prompt` semantics: `--wait` waits for the first settled state; `agent_prompt_stalled` returns after five seconds without a lifecycle change. The driver never passes `--wait` to `agent prompt`. | DOCUMENTED, then INFERRED | Official `.claude/skills/herdr/SKILL.md:128-130`. The driver sends a bare prompt and waits itself, so the stalled rule never fires on Bedrock's path. |
| `blocked` is an approval or question UI; the driver counts `blocked` as a stop. | DOCUMENTED, then INFERRED | Official `.claude/skills/herdr/SKILL.md:58,154`; the driver's stop loop at `dispatch.py:948-949`. LEFT OPEN, contradiction C4 below. |
| Read sources (`visible`, `recent`, `recent-unwrapped`, `detection`), `--format ansi`, `--lines` limits, alternate-screen limit and its file fallback. | DOCUMENTED | Official `.claude/skills/herdr/SKILL.md:176-185`. Bedrock reports are files in `agents/tasks/`, so the file fallback is already the norm. |
| Manual-pane-work safety rules: `--no-focus`, explicit pane IDs or `--current`, IDs from JSON, nothing closed that the dispatch did not create, no `herdr server stop`, never kill the main process, CLI errors exit 1 and syntax errors exit 2. | DOCUMENTED | Official `.claude/skills/herdr/SKILL.md:187-195`. The driver already follows them: explicit pane IDs from JSON, `--no-focus` on the split. |
| Environment scope clarification: herdr injects the caller's CONTEXT variables, not the shell environment. | DOCUMENTED and MEASURED | Contradiction C1 below, resolved. |
| `send-keys` no-contradiction note. | DOCUMENTED and UNMEASURED | Contradiction C3 below, resolved. |
| Model `--` slot agreement. | DOCUMENTED | Official `.claude/skills/herdr/SKILL.md:124-126`. The exact args are Bedrock's instance. |

Every kept measured fact is untouched: the no-stop/no-kill finding, the
`pkill` episode, the pane-close stop, `send-keys C-c` UNMEASURED, the
two-phase wait, name lowercasing, pane-close-on-finish, the fresh-pane
race, the workspace label rule, the environment handover, the model
pass-through, and the driver's final read.

## Contradictions, with which side won

**C1. "Herdr injects the caller's context into each managed pane"
(official `.claude/skills/herdr/SKILL.md:70-73`) against "a herdr pane
does not inherit the launcher's environment" (ours, MEASURED 2026-08-13;
the `--env GHCRTS` handover at `dispatch.py:835`). RESOLVED, no side
lost.** The official names the context it injects: `HERDR_WORKSPACE_ID`,
`HERDR_TAB_ID`, `HERDR_PANE_ID`. Ours names the shell environment, which
does not cross. Context variables and environment are different things;
both statements are true. Ours now says so in the same bullet.

**C2. The bare-wait semantics. RESOLVED, the official's rule PREDICTS
ours' measurement; no side lost.** Ours measured that a bare wait or a
one-phase `--until idle` returns AT ONCE, because the agent is already
idle at submission (MEASURED 2026-08-13, twice). The official says
standalone `agent wait` "uses the same settled-state defaults as `agent
prompt --wait`" and that `--wait` "waits for the first settled `idle`,
`done`, or `blocked` state" (`.claude/skills/herdr/SKILL.md:128,138`).
Idle is a settled state, so an already-idle agent satisfies the wait at
once. The two agree; the official's wording explains the measurement. The
two-phase pattern (wait for `working` first, then for
`idle`/`done`/`blocked`, `dispatch.py:928-949`) is Bedrock's own design
and the official documents nothing that contradicts it.

**C3. `send-keys C-c`. RESOLVED, no side lost.** The official documents
logical keys and validation (`.claude/skills/herdr/SKILL.md:140-147`); it
never claims C-c stops an agent. Ours' finding, that two `send-keys C-c`
did not stop a working pi agent, stays UNMEASURED as a method. No
contradiction exists to settle.

**C4. `blocked` as a stop state. LEFT OPEN, DOCUMENTED against INFERRED.**
The official defines `blocked` as "Herdr recognized an approval or
question UI" and says a blocked wait is a cue to inspect `agent get` and
`agent read` and send input (`.claude/skills/herdr/SKILL.md:58,154`). The
driver's stop loop is `--until idle --until done --until blocked`
(`dispatch.py:948-949`), so a pi agent that stops at an approval question
reads as FINISHED: the driver reads the pane, closes it, and records a
return. That consequence is INFERRED from the code, never measured. The
skill carries both readings and names the owner as the decider. This is
the one finding of the whole reconciliation that is worth a decision.

No contradiction required changing a measured fact. The two facts the
brief flagged as the trap, the absent `agent stop`/`agent kill` and the
`pkill` failure, survive: the official skill is silent on both (its only
stop/kill mentions are the `HERDR_ENV` gate at `.claude/skills/herdr/SKILL.md:16`
and the `herdr server stop` prohibition at `:193`, neither an agent
command), and silence is not contradiction.

## The trigger-philosophy difference, and the gap it leaves

The official skill's `description` fires only on explicit user mention:
"Use only when the user explicitly mentions Herdr or asks to use Herdr to
inspect or control..." (`.claude/skills/herdr/SKILL.md:3`). Ours fires
from the model side, on the model's own keywords, with no user mention
required. That was the owner's requirement for ours, and it is kept; the
official trigger was NOT copied into ours.

The gap analysis: a model needs herdr facts when either description
matches. Ours' triggers are dispatch, queue, resume, stop, kill, status,
waiter, arm waiter, re-arm, tier, head, model, herdr, agent name,
send-keys. The official's trigger is the user naming herdr. The uncovered
case is a user asking to inspect panes or agents in vocabulary that is
neither herdr's nor dispatch's: "what is that other agent doing?", "read
me the output of the second pane". No skill fires, and the model guesses.
For Bedrock's own workflow the gap is empty: every dispatch action sits on
a dispatch word. And when the user DOES say herdr, both descriptions can
match at once, which is harmless because ours now points at the official
for every tool fact instead of carrying a copy. The residual gap is
inspection questions phrased without any herdr or dispatch word, and the
cure is the user saying herdr or asking for dispatch status.

## ARCHIVE USED

- `.claude/skills/herdr/SKILL.md`, read whole (195 lines). Sites: `:3`
  (description and its trigger), `:11-16` (the `HERDR_ENV=1` gate), `:19-38`
  (CLI-discovery doctrine), `:54` (pane-versus-agent primitives and
  `agent start` layout rule), `:56` (name grammar and name-clearing),
  `:58` (lifecycle-state meanings, `blocked`), `:70-73` (caller context
  injection), `:103` (`--no-focus` split), `:120` (30-second startup
  timeout), `:124-126` (native args after `--`), `:128-130` (prompt `--wait`
  and `agent_prompt_stalled`), `:132-138` (standalone `agent wait`), `:140-147`
  (send-keys and validation), `:151,169,176-185` (read sources,
  alternate-screen limit, file fallback), `:187-195` (safety rules and exit
  codes).
- `.claude/skills/dispatch-herdr/SKILL.md`, read whole (448 lines before
  the edit, 500 after). The object of the reconciliation.
- `.claude/skills/codex-dispatch/dispatch.py`, the herdr driver, read
  whole around lines 800 to 1020. Sites: `:835` (the `--env GHCRTS`
  handover), `:886-896` (the fresh-pane retry loop), `:922-928` (two-phase,
  one phase is not enough), `:948-949` (the stop loop that names `blocked`),
  `:965` and `:1013` (the final `agent read --source recent --lines 400`).
  The header comments `:91-92` and `:137-152` for the harness kinds and the
  bare-wait measurement.
- `agents/tasks/LJ-1-188/lj-1.188-report.md`, read whole. How ours was
  built, the ten mistakes, and the classification discipline (MEASURED,
  INFERRED, UNMEASURED) that this report reuses.
- `agents/tasks/LJ-1-190/lj-1.190-report.md`, read whole. The previous
  script-versus-skill reconciliation, the read-only refusal it left open,
  and the confirmed model-flag finding.
- Why not the retired route's archives: the retired dispatch mechanics
  predate herdr and the switch; nothing there bears on this task.

## LITERATURE USED

The herdr documentation is this task's literature, and its local copy is
the installed skill. The comparison:

- **`herdr --skill` output against the installed file: byte-identical
  (MEASURED, this run).** The installed skill is the version the binary
  ships, as the brief says.
- **GitHub `herdrdev/herdr` tag `v0.8.0`, `skills/herdr/SKILL.md`: byte-
  identical to the installed file (MEASURED, this run).** The site's raw
  path `https://herdr.dev/skills/herdr/SKILL.md` serves HTML, not the file,
  so the GitHub tag is the site's authoritative copy.
- **`https://herdr.dev/docs/agent-skill/`: a meta-documentation page
  (what the skill does, how to install it, its safety rule), NOT the skill
  text.** It cannot be diffed against `herdr --skill`, because it is a
  different artifact, and it contains no tool fact that contradicts the
  installed skill. So the binary and the site are in step: the docs page
  describes the same v0.8.0 file the binary emits.
- WHY NOT the rest of `dev/literature/`: nothing there bears on a
  tooling-and-prose reconciliation; DD18 is satisfied by this section.

## DD4

The two skills no longer share a single duplicated tool fact. The official
skill is the one home for tool documentation and regenerates from the
binary; ours holds only Bedrock's measurements and Bedrock's use, and
points at the official for everything else. The fact that would drift, the
one the brief names, now lives in exactly one place, and that place is the
regenerable one. The measured facts are the shared generic carrier; the
pointers are the per-skill instances. No fact is maintained in both.
