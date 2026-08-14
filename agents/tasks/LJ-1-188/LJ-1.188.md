# LJ-1.188: write the dispatch and `herdr` knowledge into a project SKILL

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-flash`**, by the rule
the owner set 2026-08-14: a task that is pure natural-language work and touches
no Agda code takes flash. `scripts/dispatch_policy.py` holds that rule as
`model_for()`, and the head is the switch's default row.

## GOAL

**Write one project-local SKILL that holds everything an agent needs to drive
`dispatch.py` and `herdr` correctly, and make it load ITSELF when the model
needs it.**

**The orchestrator learned this set by making the mistakes, on 2026-08-14, in
one session. Every one of them goes into the skill.**

## THE TRIGGER REQUIREMENT, and it is the part most likely to be got wrong

**The skill must auto-load from the MODEL side, on the model's own keywords,
never from something the owner types.**

**So: NOT a slash command. NOT an instruction telling the owner to say a magic
word.** The `description:` field in the skill's frontmatter is what a model
matches against when it decides whether to load a skill. **That field is the
trigger, and writing it is the task's most load-bearing sentence.**

**Read `.claude/skills/asd-ste100/SKILL.md`'s frontmatter for the shape in
use.** Its description names what the skill DOES and then lists trigger phrases.

**Your description must fire when the model is about to**: dispatch an agent,
queue or resume one, stop or kill one, read a dispatch status, arm or re-arm a
waiter, pick a head or a model, write a `tier:` line, or touch a `herdr` pane,
agent name, or send-keys. **Name those keywords in the description.**

## WHERE IT GOES

`.claude/skills/<name>/SKILL.md`, beside the four that exist. **Pick the name
yourself; it should say what it covers.**

**`.claude/` IS GIT-IGNORED, verified at `.gitignore:19`.** So the skill is a
local file and NOT committed, exactly like its four siblings. **Do not try to
commit it and do not report it as a tracked deliverable.**

## THE KNOWLEDGE, and this is the substance

**Read `.claude/skills/codex-dispatch/dispatch.py` WHOLE.** It is 2,200 lines
and its comments already record why each refusal exists. **The skill is the
short form of that file plus the operational knowledge that is nowhere written.**

### The mistakes, all made on 2026-08-14, all by the orchestrator

**1. `pkill` DOES NOT KILL A HERDR AGENT.** `herdr` owns the pane, so `pkill`
reaches only the launcher. The agent kept running AND kept its name, the
re-dispatch was refused with `agent_name_taken`, and the orchestrator did not
notice. **`herdr agent` has NO stop and NO kill subcommand.** It has `list`,
`get`, `read`, `send-keys`, `prompt`, `rename <target> --clear`, `focus`,
`wait`, `attach`, `start`, `explain`. **Two `send-keys C-c` did not stop a
working pi agent.** Say what IS known to work and mark what is UNMEASURED.

**2. A `RUNNING` ROW IS NOT PROOF YOUR LAUNCH WORKED.** The orchestrator read
`RUNNING LJ-1.187` after a re-dispatch and concluded it had succeeded. That row
was the OLD agent. **The launch log's third line was the error.** The rule:
after a dispatch, read the launch log, not the status table.

**3. ONE WAITER REPORTS ONCE. That is the whole contract**, and the tool says so
in those words. The orchestrator armed one, it reported a single return and
exited, and three later returns sat unread. **Re-arm after every reported
return.**

**4. THE TOOL SHOUTS AND THE ORCHESTRATOR FILTERED IT OUT.** `status` prints
`!! N RETURN(S) NEVER REPORTED` and `!! NO WAITER IS ARMED`. The orchestrator
ran `status | grep RUNNING` repeatedly, which removes exactly those lines.
**Never grep the status output down to the rows you expect.**

**5. A BROKEN PATH STAYS GREEN WHILE NOTHING WALKS IT.** `dispatch.py` had
refused EVERY brief since the owner merged briefs into `agents/tasks/`, because
its pinning check still demanded `_build/briefs/`. Nobody saw it, because the
dispatch mode in force sent every default in-harness and an in-harness dispatch
touches this tool at all. **Verify the incoming path BEFORE changing which path
is live.**

**6. THE REFUSAL MESSAGE CITED THE RULE THAT CONTRADICTED IT.** That same
refusal named `dev/ORCHESTRATION.md` section 3, and section 3 line 169 already
read that a brief is pinned in `agents/tasks/<TASK>/`. **The orchestrator
believed the CODE over the RULE it cited, and built a workaround by creating
`_build/briefs/`** which `AGENTS.md` forbids in as many words: `_build/` is a
temporary folder and not a rubbish bin, it is git-ignored, and `make clean`
empties it. **When a tool and the rule it cites disagree, open the rule.**

**7. AN IN-HARNESS DISPATCH BYPASSES EVERY REFUSAL.** It passes through no tool,
so `dispatch.py`'s DD4 and DD18 gates do not fire and C-12's Agda slot
accounting counts nothing. **Under a mode that leads in-harness, those gates are
review-only whether or not their rows say so.**

**8. TWO AGENTS IN ONE CLUSTER COLLIDE, and the orchestrator did it more than
once.** One found all four target masters dirty and its file RED, and stopped
correctly. Another lost about fifteen minutes and said the cure plainly: **a
brief line saying the sibling's file may be red, so build generic first, would
have cost nothing.** Two dispatches were also pointed at the SAME report path;
the agent that arrived second refused to overwrite and wrote a new file, which
was better than the orchestrator had planned.

**9. THE HEAD AND THE MODEL ARE TWO DIFFERENT CHOICES.** The switch's `cases`
table picks the HEAD. `--model` picks the model, and `model_for()` in
`scripts/dispatch_policy.py` now rules it: pure natural-language work takes
flash, Agda work takes pro. **A `tier:` line names the head, the mode, and the
model when it is not the default.**

**10. TAKING AN EXCEPTION'S HEAD WITHOUT ITS CONDITIONS IS INVISIBLE.** The
orchestrator sent four adversarial reviews to `fable` because the owner had once
named fable for one review. `check-dispatch-policy.py` passed all four, because
DD17's emergency tier makes fable a legal token. **DD0 and `dev/LESSONS.md`
C-43 are the rules; the skill states the operational form: if the sentence
justifying another head will not write, take the head the table gives.**

### THE COMPLETE RULE SET. Every dispatch rule lands in the skill, not a summary

**The owner's instruction: ALL rules about dispatch go into the skill.** A skill
that holds the mistakes and not the rules is half a skill. Read each rule at its
home and state it, with the home named so a reader can go and check.

**THE TWO MODES, DD17.** `deepseek-subagent-mode` and `in-harness-subagent-mode`,
**each named for the head it LEADS with**, renamed by the owner on 2026-08-14
because the retired names, `normal` and `override`, said which one was the
EXCEPTION and never which head leads.

- **`scripts/dispatch_policy.py` IS THE ONLY PLACE THE TABLES LIVE.** Run it to
  see which mode is in force, when it was set, why, and what reverts it. **A
  head restated anywhere else is canonical twice, which DD19 forbids**, and
  `[LJ-1.183]` found exactly that in `dev/ORCHESTRATION.md` this week.
- **Give the table for BOTH modes**: which head takes `default`, which takes
  `adversarial`, which takes `fallback`, and on which harness.
- **THE INVARIANT UNDER BOTH: the critic is never the same head as the author.**
  That is why the two modes swap exactly the default and adversarial rows.
- **The retired names still RESOLVE**, through `ALIASES`, because 52 frozen
  briefs carry one. C-41.
- **WHAT A MODE CHANGES BEYOND THE TABLE**, and this is the half nobody expects:
  which CODE PATH is live. Under a mode leading in-harness, `dispatch.py`'s
  refusals never fire and C-12's slot accounting counts nothing.
- **The six-step mode-switch checklist is in DD17's own row.** Point at it, and
  state its two sharpest steps: expect the gate to redden on frozen briefs, and
  **when it does, the defect is in the GATE and never in the record**; and a
  running agent keeps the head that was correct when it was sent.

**THE MODEL RULE, ruled 2026-08-14 and SEPARATE from the head.** `model_for()`
in the same file: **pure natural-language work takes `deepseek-v4-flash`; work
that touches Agda takes `deepseek-v4-pro`.**

- **It hangs on the existing `--agda` flag**, so it costs no new declaration.
- **State what it CANNOT see**: a task that runs no Agda but READS and reasons
  about Agda source. `--agda` is about holding a process, not about subject
  matter, so the orchestrator overrides with `--model` and the brief records why.
- **The model name has NO date suffix**, and `dispatch.py` refuses a model the
  backend rejects. Two agents died that way before the refusal existed.

**DD25, THE ADVERSARIAL RULE.** A negative return is adversarially reviewed at
maximum effort, IMMEDIATELY, and the two are then read together. **The trigger:**
a refusal, a NO-GO, a RED gate, a stop taken as the deliverable, a refutation of
the brief's premise, or a landed result that misses its band floor. **The head
comes from the switch's adversarial row, never from a head written elsewhere.**
**The index row for a negative return must NAME its review's code**, which is
DD25's own declared enforcement point and which had lapsed on every negative
return for twenty-odd dispatches.

**DD0, AND IT BINDS THE DISPATCHER HARDEST.** The owner's temporary instructions
are not an interpretation of the rules and not permission to disobey them.
**Never derive a standing head choice from a one-off owner instruction.** The
test: **would the sentence justifying this choice write, citing the RULING rather
than the owner's past act?** If not, take the head the table gives.

**THE EMERGENCY TIER, DD17.** It binds TWO conditions and the second is scarce:
a return that does not do its task well, AND a point where the loop cannot
advance. **A stop, a refutation and a RED are GOOD returns and never a trigger.**
Each use names its trigger in the brief and records the escalation.

**DD18, WHAT EVERY BRIEF MUST CARRY.** An ARCHIVE section and a LITERATURE
section, and every return carries ARCHIVE USED and LITERATURE USED at
`file:line`. **`dispatch.py` REFUSES a brief missing either.**

**DD4, AND ITS ONLY ENFORCEMENT IS REPETITION.** Stated in EVERY brief whatever
the kind, answered in every return. **`scripts/check-dd4-stated.py` now gates
that a brief SAYS it**, reading the heading and never the content, because DD4's
row rules out a metric.

**C-12, THE AGDA QUOTA.** One process per agent, `GHCRTS="-A64m -I0 -M8g"`, cap
NEVER raised, and a heap exhaustion is reported as a wall. **The quota is
per-agent and not machine-wide** (owner's correction, 2026-08-07), **but a task
that MEASURES check time gets a quiet machine**, and that is the orchestrator's
to arrange.

**PLAN SECTION 6.0.** Register the task row BEFORE dispatching, one row per
code, 200 characters.

**THE BRIEF'S `tier:` LINE.** It names the head AND the mode, and the model when
that is not the default. **`check-dispatch-policy.py` reads every brief against
the switch, and judges a brief by the mode the brief NAMES**, never by today's
switch position.

### The mechanics that are already right and must be stated

- **Register the task row BEFORE dispatching** (`dev/PLAN.md` section 6.0 rule
  6). The orchestrator got this backwards once and had to fix it after.
- `dispatch.py check <brief>` validates without launching. **Use it every
  time.**
- `queue` waits for a slot and detaches; `run` launches now; `--wait` blocks and
  removes the need to arm a waiter separately.
- `--agda` declares the task will hold an Agda process, which C-12 caps.
- `resume <task> --note` continues a killed or exhausted agent.
- The refusals it already enforces, and what each one is for.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **WRITTEN.** The skill exists, its description names the triggers, and every
  item above is in it. Report where it is and quote the description. STOP.
- **A CLAIM ABOVE IS WRONG.** Some of this is the orchestrator's account of its
  own errors. **If the code says otherwise, the code wins: correct it in the
  skill and say so in your report.** That is the most valuable thing you can
  return.
- **THE TRIGGER CANNOT BE MADE TO WORK FROM THE MODEL SIDE.** Say so plainly,
  with what you checked. **Do not substitute an owner-typed command and call it
  done.**

## WHAT YOU MUST NOT DO

- **Do not change `dispatch.py`, `dispatch_policy.py` or any checker.** This
  task documents them.
- **Do not touch `dev/`, `src/`, or any brief or report other than your own.**
  A sibling is rewriting `dev/`.
- **Do not run Agda. Do not dispatch an agent.** Reading and writing only.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`.

## THE CLASSIFICATION I WANT

**MEASURED, INFERRED or UNMEASURED, in those words**, on every operational claim
the skill makes. **`send-keys C-c` stopping a pi agent is UNMEASURED and the
skill must say so rather than recommending it.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Here DD4 applies to the skill itself: write it so it serves ANY task kind and
any head, not the cases that happened to bite this week.** A skill that only
covers one mode is paid for twice when the mode flips.

## ARCHIVE (DD18)

- **`.claude/skills/codex-dispatch/dispatch.py`**, read WHOLE. **Its comments
  are the primary source and they are better than my summary.**
- **`.claude/skills/asd-ste100/SKILL.md`**, for the frontmatter shape and how a
  description names its triggers.
- `scripts/dispatch_policy.py` WHOLE: the switch, the modes, `ALIASES`,
  `model_for()`.
- `dev/ORCHESTRATION.md` sections 1 to 3: dispatch, slots and briefs.
- `dev/PLAN.md` DD0, DD17, DD25 and section 6.0. **Do not edit them.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Not this task's subject. Say so in one line.**

## SCOPE (read)

`.claude/skills/codex-dispatch/dispatch.py` FIRST, whole.

## SCOPE (write)

`.claude/skills/<your-name>/` and
`agents/tasks/LJ-1-188/lj-1.188-report.md`. **Nothing else.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for recon` and read every statement.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-36.** Write the term you could not write.
- **C-43.** An escape hatch is the shape a wrong choice hides in.
- **C-42.** A refutation measures the site it names, never its extent. **So when
  you find one mistake in this brief's list, sweep for its shape in the code.**
- **P-l.** A measured cure does not transfer by analogy. **An operational claim
  measured on one harness is not measured on the other.**
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **DD0, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37, C-39, C-40. I-5.**

## CONSTRAINTS

- Run `python3 scripts/lint-prose.py --check` on your report. **The skill file
  is exempt, like the other skills, but write it in ASD-STE100 anyway.**
- **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the skill's path and its `description:` line, quoted whole**, so the
trigger can be judged without opening the file. Then a checklist of the ten
mistakes and the mechanics, each marked present or absent. Then anything in this
brief that the CODE contradicts. **Mark every operational claim MEASURED,
INFERRED or UNMEASURED.**
