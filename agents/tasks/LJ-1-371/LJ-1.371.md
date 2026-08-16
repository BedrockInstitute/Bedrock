# LJ-1.371: recon. The registry cannot see an in-harness dispatch, and it cost three defects today

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** No Agda. **RECON. Price it; do not build it.**

## THE DEFECT, and it is not a hypothesis

**An in-harness dispatch passes through NO tool.** `dev/PLAN.md` DD17 states
it and `[LJ-1.356]` measured it. **So `dispatch.py`'s registry never learns
that such an agent exists.** **Every consumer of that registry is therefore
blind to a live in-harness agent, and「blind」takes three different shapes.**

**ALL THREE FIRED TODAY, 2026-08-16, MEASURED by me:**

| shape | what happened |
|---|---|
| **FALSE GREEN** | `dispatch.py gate-ready` answered「no agent is live; a full-tree gate will read a settled tree」while `[LJ-1.357]` was live in-harness. I ran the gate anyway, judging its write scope safe. **The tool told me something false and I was right by luck rather than by it.** |
| **SILENT** | `dispatch.py`'s DD18 refusal, its DD4 refusal and its rule-bundle refusal **do not fire at all** for an in-harness dispatch. Under a mode that leads in-harness, the project's only hard brief gates are DEAD and nothing says so at dispatch time. |
| **FALSE RED** | `scripts/gate/check-dd18-survey.py` judged `[LJ-1.368]`'s report a B2 failure **while the agent was still writing it**. The checker has a「live report in progress, not judged」path and it could not use it, because it asks the registry and the registry had never heard of `[LJ-1.368]`. **`make check` went red on a defect that did not exist.** |

**The two gates I commissioned TODAY both inherited this blind spot, because
the specifications I wrote did not mention it.** **That is the strongest
argument that this needs a structural answer rather than care.**

## THE QUESTION TO PRICE

**1. CAN AN IN-HARNESS DISPATCH BE REGISTERED AT ALL?** **The orchestrator
calls the harness's own agent tool; no project code runs.** **So the honest
candidates are all AFTER the fact, and you must say which are real:**

- **the orchestrator registers by hand before dispatching**, which is a
  discipline and not a mechanism, and this session shows what discipline is
  worth;
- **a marker file the orchestrator writes**, same objection, one step cheaper;
- **the registry INFERS liveness from the tree**: a task directory holding a
  brief and a report younger than N minutes, with no return recorded. **This
  needs no cooperation from the dispatcher at all, which is its whole
  appeal.** **Price its false-positive and false-negative rates against the
  live corpus.**
- **something you think of that I did not.**

**2. WHICH CONSUMERS MUST CHANGE, and can any be fixed WITHOUT solving the
registry?** **The false red is the cheapest of the three: a checker could skip
a report whose file changed in the last N minutes, with no registry at all.**
**Price that separately, because it may be worth landing alone.**

**3. WHAT DOES THE SILENT SHAPE COST?** **`dispatch.py` holds refusals that
have each caught a real defect: the rule-bundle refusal caught me twice
today.** **Say what fraction of dispatches currently bypass them.** **Count
in-harness dispatches from the task index and the logs; do not guess.**

## THE ABORT CRITERION (D-1)

- **A CHEAP MECHANISM EXISTS.** Name it, price it, and give its false
  positives and negatives with numbers. **Best.**
- **ONLY THE FALSE RED IS CHEAPLY FIXABLE.** **Then say so and price that
  alone.** **A narrow fix that lands beats a wide one that does not.**
- **NOTHING MECHANICAL WORKS.** **Then say it, and name the review step or
  the discipline that must carry it, because `AGENTS.md` requires a rule with
  no machine to NAME its enforcement point.** **A wish is not an answer.**
- **THE PREMISE IS WRONG.** **If the registry CAN see in-harness agents and
  today's three defects have another cause, say so; that would be the most
  valuable return and it would mean I misdiagnosed three failures.**

## CONSTRAINTS

- **PROPOSE, DO NOT LAND.** Write only in `agents/tasks/LJ-1-371/`. **You may
  write and RUN a prototype there for real numbers; do not wire anything into
  `Makefile`, `scripts/` or `.claude/`.** `src/` is forbidden (I-5).
- **`.claude/skills/codex-dispatch/dispatch.py` is READ-ONLY for you.** It is
  2,500 lines and it is the orchestrator's tool. **Read it; do not edit it.**
- **`[LJ-1.370]` is live and writes `src/L/Choice/` and `dev/ARCHIVE.md`.** No
  collision.
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-371/lj-1.371-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check`. **No em dash.**
  ASD-STE100. **Evidence is `file:line`, and for a rate, the command that
  produced it.** Mark every negative **MEASURED** or **INFERRED**.

## PREMISES

- **An in-harness dispatch passes through no tool**, at `dev/PLAN.md` DD17 and
  measured by `[LJ-1.356]`.
- **`gate-ready` gave a false green today**, at
  `.claude/skills/codex-dispatch/dispatch.py`, the `gate-ready` command.
- **`check-dd18-survey.py` gave a false red today** on `LJ-1-368`, at
  `scripts/gate/check-dd18-survey.py`.
- **`dispatch.py`'s refusals are dead for an in-harness dispatch.**

**Mark each VERIFIED or REFUTED at `file:line`.**

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last thirty-five briefs carried a claim an agent measured
FALSE.** **The one at risk: that all three of today's defects share ONE
cause.** **I diagnosed them in the minutes after each fired, while doing
something else, and a shared root cause is exactly the kind of tidy story a
hurried diagnosis produces.** **Check each independently. If one has a
different cause, the fix I am asking you to price may not fix it.**

## THE RULES

**C-48: a policy that only a document states is not enforced.** **C-59: a
gate you do not run is worth what a gate you do not have is worth, and this
task is its sibling: a gate that cannot SEE is worth the same.** **C-28: a
stale figure reports exactly like a live one.** **C-45, C-57, D-10, C-42,
C-44, C-53, P-l, P-k.** **C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD17, DD18, DD19, DD23, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for recon` and
`--grep dispatch`, and read every statement.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. **NAME YOUR AXIS** (C-46).

**Your axis is not the two towers; say so plainly rather than force the
section.** **What IS live: this defect makes every gate the project builds
less trustworthy, and two of the gates it damaged were commissioned TODAY to
protect DD18 and DD24, both of which serve DD4's own instruments.** **A
blind gate reports the DD4 relationship wrongly, and it does so silently.**

## ARCHIVE (DD18)

**`scripts/gate/check-dd18-survey.py` GATES your return: name each of the four
corpora, cited or declined in ONE line, and QUOTE one line per archived file
you read, at its real line number.**

- **`archive/dev/DECISIONS-archived.md`**: **did the retired route have a
  dispatch registry, and did it have this problem?** **A rule that already
  died once is the strongest evidence you can bring.**
- **`archive/dev/JOURNAL-archived.md`**: **grep for lost returns and unwatched
  agents.** **The waiter contract exists because four returns were lost behind
  one slow agent; find whether a registry blind spot ever cost anything.**
- **`archive/dev/TASKS-archived.md`**: dispatch-tooling dispatches.
- **`archive/src/2026-08-09-rud-route/`**: **almost certainly nothing bears on
  dispatch tooling. Say so in one line naming what you checked.**

## LITERATURE (DD18)

**MEASURED TWICE ALREADY, by `[LJ-1.356]` and verified by `[LJ-1.357]`:
nothing in `dev/literature/` bears on process mechanisms.** **Cite that and
move on; do not spend a third pass.** Return a **LITERATURE USED** section
saying exactly that.

## SCOPE (read)

`.claude/skills/codex-dispatch/dispatch.py`, its `status`, `gate-ready` and
registry code, FIRST. Then `scripts/gate/check-dd18-survey.py`'s liveness
path, which is the false red.

## SCOPE (write)

`agents/tasks/LJ-1-371/` only.

## RETURN

**Lead with ONE line: is there a mechanism that sees an in-harness dispatch,
and what does it cost.** Then each of the three defects, confirmed
independently or not. Then the tree-inference candidate with its false
positive and negative rates, measured. Then the cheap narrow fix for the false
red, priced alone. Then what fraction of dispatches bypass `dispatch.py`'s
refusals. **Mark every negative MEASURED or INFERRED.**
