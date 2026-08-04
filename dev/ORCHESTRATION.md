# ORCHESTRATION: the orchestrator's operating rules

How work is dispatched, audited and landed. Developer doc, English only, not
translated. **This file is canonical for everything on it.** It exists because
these rules used to live only in the orchestrator's session memory, where the
owner could neither read nor amend them, and where their execution depended on
one party remembering.

**Enforcement.** Rules here are enforced by the orchestrator at named points,
listed per rule. A rule with no enforcement point is a wish, not a rule: if you
add one here, name where it fires.

## 1. Who does the work

**Codex is the default for every dispatch.** The orchestrator uses an in-harness
Opus subagent in exactly two cases: the owner says so for that task (a past
override never carries forward), or the orchestrator judges the task
very-very-heavy, a deliberately high bar meaning whole-campaign synthesis or
wall-class mathematics beyond measured scale. Ordinary probes, recons, polish
passes and implementation batches are codex work, and codex has delivered all
of those green.

*Enforcement:* the brief header carries a `tier:` line before dispatch.
`tier: codex (default)` needs no justification; `tier: opus` must name which
exception applies and, for the second, why codex cannot carry it. **If that
sentence will not write, the tier is codex.**

## 2. Slots

Concurrency and heap ceilings are LESSONS C-12: agent Agda runs at
`GHCRTS=-M8g` with at most four concurrent, or `-M12g` with at most two; the
orchestrator's own runs at `-M16g`; one Agda process per agent, always. Agents
that run no Agda do not consume a slot.

**An idle slot is a defect** (PLAN D23). At every return, before writing the
report: name what is unblocked, name what blocks the rest, and dispatch into
the free slots. Blocked means waiting on an owner ruling, on a sibling's write
territory, on a measurement that would make the work fundable, or on the
ceilings above. Auditing a return is not a reason to idle.

*Enforcement:* the return-handling checklist in section 5.

## 3. The brief

Every brief is pinned in `_build/briefs/` before dispatch, so it survives a
reboot and the owner can read what was actually asked. A brief carries:

- **`tier:`** (section 1) and a one-line GOAL.
- **CWD**, and **SCOPE (write)** naming every file the agent may write.
  Territories must be disjoint across concurrent agents, and the brief names
  the files siblings own so the agent knows what not to touch.
- **SCOPE (read), in order**, with the load-bearing documents first. This is
  how the law book actually reaches an agent: `dev/LESSONS.md` binds, and the
  brief must say so and name the hot entries.
- **CONSTRAINTS**: the heap cap, one Agda process, no git, never
  `src/Everything.lagda.md`, never `.claude/`, the stop-line, and the wall
  protocol.
- **RETURN**: the exact deliverable, evidence as `file:line`, and the
  measurements that decide the next ruling.

Standing clauses that go in every build or probe brief:

- **D-1**: probes are never committed; the verdict goes in a report under
  `_build/`; write the deliverable incrementally, never at the end (C-22).
- **D-10**: check the target's truth at the intended generality before proving
  it, and record any correction beside the original.
- **D22**: name the block's widest unmeasured term and the probe that would
  measure it; a brief that cannot is not ready to send.
- **A stop is a deliverable.** Say so explicitly, so an agent that finds the
  target false reports instead of forcing it.
- **Adversarial honesty**, named in the direction the brief is biased: if the
  brief argues for a rewrite, say that over-optimism about rewrite cost is the
  failure mode to guard against.

*Enforcement:* the brief is written to `_build/briefs/` and re-read before the
dispatch command is issued.

## 4. Registration

A task is registered in `dev/PLAN.md` **before** the work starts, never
backfilled (PLAN section 6.0 rule 6). This was breached once, for four tasks,
and the breach is recorded in the row rather than tidied away.

*Enforcement:* the PLAN commit precedes the dispatch command in the same turn.

## 5. Handling a return

In this order, every time:

1. **Read the final message**, then the report if the finding is load-bearing.
2. **Verify independently.** Re-run the agent's own typecheck under the
   orchestrator's cap. Spot-check the load-bearing claims at `file:line`,
   especially absence claims (grep them) and any claim that a wall is gone.
3. **Fill the free slots** (section 2) before writing anything up.
4. **Wire** `src/Everything.lagda.md` (agents never touch it) and any catalog
   prose the change makes stale.
5. **Gate**: `make check`, or the individual checks when a sibling holds the
   Agda slot, saying which was run.
6. **Commit** with the goal code, recording what was measured and what was
   refuted. Never push.
7. **Record** in PLAN (the ruling and the number) and, if a law was learned, in
   `dev/LESSONS.md`.

## 6. The owner's instructions

An instruction from the owner is executed or explicitly deferred with a reason,
never silently dropped. A single message often carries more than one; the
second is the one that gets lost, especially when the first opens a topic
interesting enough to absorb the turn.

*Enforcement:* before writing the closing report of any turn, re-read the
owner's last message and account for EVERY instruction in it: done, dispatched,
or deferred-with-a-reason. This rule exists because on 2026-08-05 a message
carried a terminology ruling and a dispatch instruction, the ruling was
executed, the dispatch was dropped, and the owner had to ask three times.

**Committing.** The orchestrator commits; dispatched agents never do. Commit
after the audit and the gate, with the goal code in brackets, recording what
was measured and what was refuted. **Never push** without the owner's word: one
push is one CI run and one deploy.

## 7. Research and translation

**Web research always goes to a sub-agent** and comes back as a dossier with
sources, never inline in the orchestrator's loop; the owner rules on the
presented evidence.

**A term not in `dev/glossary.toml` is not invented.** Search the Chinese
literature for the established rendering first; if there is none, draft
multiple candidates by analogy, present them with the reasoning, and let the
owner rule. Confirmed renderings are added to `dev/glossary.toml`, which is
machine-enforced, and nowhere else.

*Enforcement:* section 5 step 7, and `check-glossary.py` in `make check`.

## 8. What stays out of the repository

Owner-private context (private sibling repositories, local machine paths,
anything the owner marked private) lives only in the orchestrator's session
memory and never reaches `AGENTS.md`, `CONTRIBUTING.md`, the README, this file
or the site.
