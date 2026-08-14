# LJ-1.203: can herdr's Agent Automation replace `dispatch.py` and its SKILL?

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-flash`**, by the owner's
rule of 2026-08-14: work that touches no Agda code takes flash.

## GOAL

**The owner asks whether more of herdr's features, especially Agent Automation,
could REPLACE, OPTIMIZE or COMPLETE the dispatch machinery this project
maintains, so the whole is more robust.**

**Read the documentation: https://herdr.dev/docs/agent-automation/** and
whatever it links to.

**Deliverable: an INVESTIGATION REPORT. You build nothing and change nothing.**

## THE PIPELINE, so you know who reads this

**Three stages, ruled by the owner.** You write the investigation report. **The
orchestrator reviews it and gatekeeps.** Then the final proposal goes to the
owner, **who decides.**

**So write for a reviewer who will check your claims, not for a decision-maker
who will act on them.** Every capability claim needs its source.

## THE QUESTION THAT MAKES THIS USEFUL, and it is not a feature tour

**`.claude/skills/codex-dispatch/dispatch.py` is 2,276 lines.**

**Split those lines into two kinds:**

1. **Lines that exist because HERDR LACKED SOMETHING.** A retry loop around a
   race, a registry that tracks what herdr does not, a name mapping, a wait
   protocol. **These are candidates for replacement, and Agent Automation is
   exactly where to look.**
2. **Lines that exist because BEDROCK NEEDS SOMETHING.** Every REFUSAL: the DD4
   gate, the DD18 archive and literature sections, C-12's Agda slot ceiling, the
   write-territory intersection, the brief-pinning rule, the kind derivation.
   **These encode this project's rulings and no general tool can supply them.**

**A proposal that moves kind 2 into herdr is wrong. A proposal that keeps kind 1
hand-rolled when herdr does it better is waste.**

**Give the split with counts, and say which side each subsystem falls on.**

## WHAT THE FILE ITSELF TELLS YOU, and read it before the docs

**Its header records the three failures that built it:** a dead model that
killed two agents SILENTLY, a read-only sandbox that blocked an agent's report,
and a killed watcher that took two live agents down with it. **It was then
hardened against an adversarial review that found 18 defects with
reproductions.**

**So for every capability you propose adopting, ask: does it prevent the failure
the hand-rolled code prevents?** A herdr feature that does 80 percent of a
refusal is not a replacement; it is a regression with a nicer API.

## WHAT IS ALREADY MEASURED, so you do not re-derive it

| fact | source |
|---|---|
| `herdr agent` has NO `stop` and NO `kill` subcommand; the list is `list get read send-keys prompt rename focus wait attach start explain` | MEASURED 2026-08-14 |
| `pkill` does NOT kill a herdr agent: herdr owns the pane, so it reaches only the launcher | MEASURED 2026-08-14, an agent kept running AND kept its name |
| `send-keys C-c` did not stop a working pi agent | UNMEASURED as a method, observed to fail twice |
| closing the pane kills the agent, irreversibly | MEASURED 2026-08-13 |
| `agent wait --until` takes `idle working blocked done unknown`, and the wait is TWO PHASE | MEASURED 2026-08-13, twice |
| `queue --wait` ACCEPTS the flag and IGNORES it; `run --wait` honours it | MEASURED 2026-08-14 |
| names are lowercased: `LJ-1.123` becomes `lj-1-123` | MEASURED 2026-08-13 |
| a freshly split pane is not yet a shell, so `agent start` retries | MEASURED 2026-08-13 |
| a herdr pane does not inherit the launcher's environment | MEASURED |

**Every one of those is a line in the skill. If Agent Automation supersedes any
of them, say which and how.**

## THE FIVE QUESTIONS TO ANSWER

1. **What IS Agent Automation?** In three sentences, from the docs, with the URL
   of each claim.
2. **Which of our hand-rolled mechanisms does it supersede?** Name them: the
   registry, the waiter, the slot accounting, the retry loops, the resume path,
   the status census.
3. **Which of our REFUSALS could it carry?** Probably none, and saying so
   plainly is a real answer.
4. **What does it give us that we do not have at all?** This is where the value
   may be, and it is the question most likely to be skipped.
5. **What would BREAK if we adopted it?** Name the migration cost and the
   failure modes. **A proposal with no cost section is not a proposal.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **A PROPOSAL EXISTS.** Report it with the split, the counts, the costs and
  what you could not settle. STOP.
- **THE DOCS ARE UNREACHABLE.** **Say so immediately and stop.** Do NOT
  reconstruct the feature set from the CLI's `--help` and present it as the
  documentation. **An investigation built on a guessed feature set is worse than
  none**, and this project measured that exact failure yesterday: a claim marked
  MEASURED on the strength of a `--help` listing when the claim was about
  BEHAVIOUR.
- **AGENT AUTOMATION IS NOT RELEVANT.** If it turns out to solve a different
  problem, **say so in the first line.** That is a complete answer and it saves
  a migration.
- **IT SUPERSEDES EVERYTHING.** If the honest answer is that most of the 2,276
  lines could go, say so with the evidence. **Do not soften a strong finding to
  seem balanced.**

## WHAT YOU MUST NOT DO

- **Change nothing.** No edit to `dispatch.py`, the skills, `scripts/`, `dev/`
  or `src/`. **This is an investigation.**
- **Do not dispatch an agent and do not run Agda.** Two siblings hold both Agda
  slots. **`dispatch.py check` and `status` launch nothing and are allowed.**
- **Do not run `herdr agent start`, `prompt`, `send-keys` or `rename` against a
  LIVE agent.** Four are running. **`herdr agent list` and `get` are read-only
  and allowed.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`.

## THE CLASSIFICATION I WANT ON EVERY CAPABILITY CLAIM

**DOCUMENTED, MEASURED or INFERRED, in those words.**

- **DOCUMENTED** means the herdr docs say it, with the URL.
- **MEASURED** means you observed it on this machine, with the command.
- **INFERRED** means neither, and you say so.

**A capability the docs promise is DOCUMENTED and not MEASURED**, and the
difference matters: this project shipped a wrong claim yesterday by reading a
`--help` line and calling it measured.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Here it applies to the tooling: a mechanism we hand-roll that herdr maintains
is a mechanism we pay for twice.** **But the converse binds harder: a REFUSAL
that encodes a Bedrock ruling cannot be delegated to a general tool, because the
tool does not know the ruling.** Say which of our mechanisms are generic
infrastructure and which are project law.

## ARCHIVE (DD18)

- **`.claude/skills/codex-dispatch/dispatch.py`**, read WHOLE. **Its header and
  its per-defect comments are the record of why each guard exists, and they are
  better evidence than any summary.**
- **`.claude/skills/dispatch-herdr/SKILL.md`**, read WHOLE: what we currently
  believe about herdr, including the measured limits above.
- `scripts/dispatch_policy.py`: the switch, the modes, `model_for()`.
- `dev/ORCHESTRATION.md` sections 1 to 3, and `dev/PLAN.md` DD17, DD18, DD25.
  **Read them; do not edit them.**
- `agents/tasks/LJ-1-190/lj-1.190-report.md`: the last reconciliation of the
  script against the skill, and the one contradiction it left open.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**The herdr documentation IS this task's literature.** Return a **LITERATURE
USED** section listing every page you read, with its URL, and say WHY NOT for
any page you skipped.

## SCOPE (read)

https://herdr.dev/docs/agent-automation/ FIRST, then
`.claude/skills/codex-dispatch/dispatch.py`.

## SCOPE (write)

`agents/tasks/LJ-1-203/lj-1.203-report.md` ONLY.

## MANDATORY RULES

Run `python3 scripts/rules.py --for recon` and read every statement.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-42.** A refutation measures the site it names, never its extent.
- **C-43.** An escape hatch is the shape a wrong choice hides in.
- **P-l.** A capability measured elsewhere is a hypothesis here.
- **D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-36, C-37, C-39, C-40.
  I-5. DD0.**

## CONSTRAINTS

- Run `python3 scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is a URL, a `file:line`, or a command and its output. Write
  ASD-STE100.

## RETURN

**Lead with one sentence: does Agent Automation replace, optimize, complete, or
not apply?** Then the two-kind split of the 2,276 lines with counts. Then the
five questions, each answered. Then the migration cost and what would break.
Then what you could not settle. **Mark every capability claim DOCUMENTED,
MEASURED or INFERRED.**
