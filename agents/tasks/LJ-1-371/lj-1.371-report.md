# LJ-1.371 report: can anything see an in-harness dispatch?

Status: COMPLETE. Recon. It lands nothing. Evidence is `file:line`, and every
rate names the command that produced it.

## One-line answer

**A cheap mechanism exists, but it is INFERENCE and not registration: read the
tree, not the dispatcher.** A rule of "no young write in any live task's
declared scope, and no gated report mid-write" sees an in-harness agent at the
only moment that matters, which is when it writes. It costs about 30 lines in
`gate-ready` as a second opinion. It caught both live agents at N=15 minutes
and made no false positive, MEASURED on the live corpus now. Its false negative
is the agent that stays silent, and that silence is itself safe for a gate,
because a silent agent writes nothing. The false red needs no registry at all,
and its cheap fix should land first.

## The three defects, checked independently

The brief warned that the shared root cause was the premise most likely wrong.
**It is wrong. Two defects share the registry cause. The third does not.**

### Defect 1, FALSE GREEN from `gate-ready`. CONFIRMED, with timestamps.

The cause is exactly the stated one. `cmd_gate_ready`
(`.claude/skills/codex-dispatch/dispatch.py:2218`) answers from
`running(load())` at `:2229`, which filters `registry.json` records by pid at
`:417`. An in-harness dispatch has no record, so it is invisible. The episode
has a durable trace in the orchestrator session transcript
(`~/.claude/projects/-Users-alsg-Agentic-Bedrock/f843d526-afbf-4371-b097-d7426ab93ba3.jsonl`):

- 2026-08-16T01:29:05Z, the orchestrator ran `dispatch.py gate-ready`.
- 01:29:08Z, it answered `no agent is live; a full-tree gate will read a
  settled tree`.
- 01:29:15Z, the orchestrator ran `make check`.

That is 09:29 local time. `[LJ-1.357]` ran in-harness from 09:26 to 09:39,
evidenced by its brief mtime 09:26 and report mtime 09:39, and by its absence
from `registry.json`. The gate ran over a live agent's tree. MEASURED.

### Defect 3, FALSE RED from `check-dd18-survey.py`. Episode CONFIRMED.
**Stated cause REFUTED.**

The episode is real and has a timestamp. The transcript shows make check red at
2026-08-16T04:57:33Z, that is 12:57:33 local: `1 gated return(s) fail B2:
LJ-1-368: no-heading: the return carries no ARCHIVE USED section`. The report
existed by then and was finished only at 13:15. The agent was still writing.

**But the checker never asks the registry.** Its imports are `re`, `sys`,
`pathlib`, `agents_tree`, `repo_root` (`scripts/gate/check-dd18-survey.py:87-105`).
No registry read exists in the file. The "in progress, not judged" path is a
TEXT rule: the regex `IN_PROGRESS` at `:181`, applied to the report's first 15
lines at `:482`. It fired for `[LJ-1.370]`, whose report head reads
`Status: IN PROGRESS`. It could not fire for `[LJ-1.368]`, whose report head
carries no status line at all, in its final state and at 12:57:33, because a
checker that red-flagged it proves no skip fired.

The convention has no home any dispatched agent reads. It appears only in the
checker's own comment at `:179`. Neither brief asked for it: both carry the
same C-22 sentence, `agents/tasks/LJ-1-368/LJ-1.368.md:118` and
`agents/tasks/LJ-1-370/LJ-1.370.md:94`, and neither names a status line. My own
first skeleton wrote `STATUS: SKELETON`, which does not match the regex. I
corrected it within the hour. A marker nobody specifies is luck, not a
mechanism. MEASURED.

### Defect 2, SILENT refusals. CONFIRMED.

`launch_defects` (`dispatch.py:737-755`) holds the DD4, DD18 and rule-bundle
refusals. It is called only at `:958` (`run`), `:1436` (`queue`), `:1464`
(`resume`) and `:2454` (`check`). All four are `dispatch.py` entry points. An
in-harness dispatch calls none of them, and nothing at dispatch time says so.
`dispatch.py:2307` states the limit itself: "THIS BINDS THE CODEX PATH ONLY."

The rule-bundle refusal fired twice today, at 09:10:50 and 10:42:03 local,
MEASURED from the transcript by counting its distinctive output text. It has
NO post-hoc substitute: no gate checker under `scripts/gate/` reads a brief's
rule citations, verified by grep. For an in-harness dispatch it is a rule with
no enforcement point, which DD19 calls a wish.

The DD4 and DD18 refusals lose only TIMING, not enforcement: `make check` runs
`dd4` and `dd18survey` tree-wide over the landed briefs and returns. The agent
has already spent its budget by then, but the record is still gated.

## The fraction of dispatches that bypass the refusals

MEASURED by `agents/tasks/LJ-1-371/probe_registry_inference.py`, part 1. A
dispatch bypassed when its task is absent from `registry.json` AND no dispatch
log names it. Ground truth is registry membership, because a dispatch through
`dispatch.py` always writes a record.

- Live corpus: 275 dispatch-bearing task dirs. 3 ruling-only dirs excluded.
- **126 of 275, that is 46 percent, never passed through `dispatch.py`.**
- By era: override era 55 of 76, deepseek-mode adversarial rows 18 of 81,
  in-harness mode 50 of 71, pi mode today 3 of 14, that is 21 percent.

The registry is complete only where the old single path existed: 0 of 33
bypassed before the override era.

## The tree-inference candidate, priced

MEASURED by the probe, part 2, against ground truth assembled three ways:
registry pids with start-time check, `herdr agent list`, and this agent itself.
Both live agents now are `[LJ-1.370]` and `[LJ-1.371]`.

Rule: a task is live when its report mtime is younger than N minutes and its
PLAN section 11 row reads DISPATCHED.

- N=5: both live agents missed. 0 false positives.
- N=10: `[LJ-1.370]` missed. It was live, `working` in herdr, holding the Agda
  slot, and its report had sat untouched for 14 minutes. 0 false positives.
- N=15: both caught. 0 false positives.

**The false negative is structural and it is the safe error.** A cold typecheck
takes about twelve minutes (`AGENTS.md:68`, DD15's rule at `dev/PLAN.md:613`), so every build task has a
silent window longer than N=10. Raising N to 15 covers the median typecheck,
and the cost of a miss is small for `gate-ready`, because an agent that writes
nothing cannot leave a half-written master behind. What a gate must fear is
recent writes, and recent writes are exactly what the rule sees.

**The false positive is the unaudited return.** After an agent finishes, its
row still reads DISPATCHED until the orchestrator audits. MEASURED by the
probe, part 3, over 157 landed returns: audit delay median 3.3 minutes, 30 of
157 over 10 minutes, maximum 195 minutes. So each return reads as live for up
to N minutes after death. At roughly 17 dispatches a day, that is an
availability cost of about 18 percent of wall clock at N=15. It refuses gates
that would have been safe. It never authorises one that is not.

**The signal should watch the write scope, not only the task dir.** A build
agent writes masters under `src/` and probes in its dir. The brief already
names the write scope in its SCOPE (write) section. A `gate-ready` second
opinion that scans the live briefs' declared scopes for files younger than N
minutes sees `[LJ-1.370]`'s `src/L/Choice/` work with no registry at all. The
orchestrator's own writes are the false-positive source, and the orchestrator
does not write masters, except when it wires `Everything.lagda.md`, which it
does while no gate runs. About 30 lines, read-only, proposed not landed.

## The narrow fix for the false red, priced alone

It needs no registry and it should land first.

1. **Give the marker a home.** Add one sentence to the brief template and to
   `dev/ORCHESTRATION.md`: the report's first line reads
   `Status: IN PROGRESS` until it is finished. Zero code. The checker already
   implements the skip at `:482`. This alone would have prevented today's red.
2. **Add an mtime backstop.** About 6 lines in `main()`: skip a gated report
   whose mtime is younger than 10 minutes while its PLAN row still reads
   DISPATCHED. At 12:57:33 the report was seconds old, so the backstop fires
   where the marker was missing. Its own false positive is one orchestrator
   turn: the skip dies the moment the row carries its verdict, which happens in
   the audit turn, before the commit that lands the report.

Cost of the defect it cures: today, one red `make check` on a defect that did
not exist, plus the orchestrator's diagnosis time. INFERRED from the episode:
every gated report is mid-write for 16 to 26 minutes of its run, MEASURED from
birth-to-last-write times of today's gated reports, so a make check during a
build day hits a mid-write report often.

## Can an in-harness dispatch be registered at all?

- **By hand before dispatching**: a discipline. DD19 already forces half of it,
  because `check-task-index.py` requires the PLAN row before the dispatch
  starts. The missing half is a return timestamp, and today's three defects all
  happened while the orchestrator was busy. Priced by the day: low.
- **A marker file**: the same discipline, one step cheaper. No.
- **Tree inference**: yes, priced above. It needs no cooperation, which is its
  whole appeal, and its errors are the safe directions for the consumers named.
- **Something else**: the PLAN row itself IS the registration. It is written
  before dispatch by an existing gate and flipped at audit. A consumer needs
  only the row plus mtimes. This is the tree inference with a name, and it
  should be the recommended shape.

## What the silent shape costs, in one number

46 percent of all dispatches, and under the mode in force today every
adversarial row, which DD25 makes mandatory for every negative return. The
rule-bundle refusal, which caught the orchestrator twice today, has no other
enforcement point. MEASURED above.

## ARCHIVE USED

Four corpora, one line each, cited or declined.

- `archive/dev/DECISIONS-archived.md`: READ. The retired route had no dispatch
  registry. Every "registry" in its rulings is the code archive (`:42`, D20's
  `dev/ARCHIVE.md`) or the size ledger (`:49`, D27). Quote, `:49`:
  "standing is COMPUTED from the tree by `scripts/ledger.py` and written down
  nowhere, so it can never be stale". That is the same shape this report
  recommends: compute liveness from the tree, do not write it down. No rule
  died here, because no such rule existed.
- `archive/dev/JOURNAL-archived.md`: READ, grepped for lost returns and
  unwatched agents. The registry episodes are records LOST inside a registry
  that existed, `:1991`: "reproduced, and with them the registry's unlocked
  read-modify-write, which oversubscribed the slot ceiling and lost 7 of 10
  records under the tool's own documented fan-out". And `:2161`: the waiter
  episode, `[T70]` and `[T72]` unannounced because "the watch set was
  snapshotted at start (so an agent dispatched later was never watched at
  all)". A registry blind spot never cost the retired route anything MEASURED,
  because every dispatch then passed the one tool.
- `archive/dev/TASKS-archived.md`: READ for dispatch-tooling dispatches.
  `:154`: "| L3.32-T119 | Adversarial review of the dispatch mechanism |
  DELIVERED | `_build/l3.32-t119-report.md` |". The report itself is gone with
  `_build/`; its findings survive as the T-numbered lessons inside
  `dispatch.py`'s own comments.
- `archive/src/2026-08-09-rud-route/`: CHECKED and DECLINED. It holds only
  Agda modules and a path note, `README.md:3`: "THE OLD PATH OF THIS DIRECTORY
  WAS `archive/rud-route/`". Nothing there bears on dispatch tooling, as the
  brief predicted.

## LITERATURE USED

Nothing in `dev/literature/` bears on process mechanisms. MEASURED twice
already, by `[LJ-1.356]` and verified by `[LJ-1.357]`. This return spent no
third pass, per the brief.

## DD4

My axis is not the two towers. Say so plainly. My axis is the instruments: the
gates are what make the DD4 relationship visible, because a shared-line claim
is audited, not counted. A blind gate reports the DD4 relationship wrongly and
silently, so a gate defect is an instrument defect first. Two of today's three
defects damaged gates commissioned this morning to serve DD18 and DD24, which
are DD4's own instruments.

## Verdict for the orchestrator

Land the narrow fix first: the marker home, then the mtime backstop. It is
independent of the registry and it cures the false red completely. Then wire
the tree inference into `gate-ready` as a second opinion, about 30 lines, with
N=15. Do not build a registration discipline. The row already exists. Read the
tree.
