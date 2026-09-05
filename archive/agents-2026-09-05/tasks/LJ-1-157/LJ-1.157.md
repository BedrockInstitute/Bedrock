# LJ-1.157: what did the new route rebuild, re-price or re-probe that the archives already held?

tier: fable 5, maximum effort, **owner's word 2026-08-13**. Under the override
version an adversarial review does not go to the in-harness Opus; the owner
named this head directly.

## GOAL

**Audit the orchestrator, not the mathematics.**

**Find every place where the new route probed, priced, walled on or built
something that the retired route ALREADY HELD, and that no brief pointed at.**

**This is an adversarial review and the target is my archive discipline.**

## WHY YOU WERE SENT, and the trigger is one hour old

`AGENTS.md` states the rule and its enforcement in the same breath:

> **FOUR ARCHIVES, and surveying them is a brief section rather than a hope.**
> Every brief carries an **ARCHIVE** section naming what may bear on the task;
> every return carries an **ARCHIVE USED** section naming what it read and
> took, at `file:line`.

**Its enforcement is REVIEW ONLY. Nothing mechanical notices a brief whose
ARCHIVE section points at the wrong place.**

**It failed one hour ago and the OWNER caught it, not me.** I dispatched
`[LJ-1.156]` to settle whether Route A-prime needs `CSB`. Its ARCHIVE section
named four reports and one archived probe. **It did not name
`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md`, which holds a
DELIVERED, GREEN `CSB` at 299 in-fence lines**, built by `[L3.32-T71]`,
including a `module Graph` that upgrades the index-level bijection to a
carrier-level set of Kuratowski pairs and proves all five clauses. Its own
prose states the design intent I was about to have re-derived.

**One miss is an accident. The question this task answers is how many there
are.**

## WHAT TO AUDIT

**The new route, from the route change on 2026-08-09 to now.** That is
`[LJ-1.1]` onward, and most densely `[LJ-1.129]` to `[LJ-1.156]`, which is 38
task directories under `agents/tasks/`.

**Against the four archives:**

| | |
|---|---|
| `archive/src/` | **101 files in 8 archival events.** `2026-08-09-rud-route/` is 74 of them |
| `archive/dev/` | 14: `DECISIONS-archived.md`, `JOURNAL-archived.md`, `STATUS-archived.md`, `TASKS-archived.md`, and `measurements/` |
| `agents/tasks/archive/` | **1,043 files**, 495 task directories |
| `dev/memos/` | 21 memos of the retired era, whose STATUS headers `[LJ-1.139]` repaired today |

## THE FOUR SHAPES OF MISS, so you look for the right thing

1. **A THEOREM already proved.** The `CSB` case. Something the new route
   treats as unbuilt that the archive holds green.
2. **A PRICE already measured.** A band the new route re-derived by analogy
   when a measurement existed. **This project's own P-l says a price from a
   comparable elsewhere is a hypothesis, so a re-derived band is not merely
   wasteful, it is weaker evidence than the measurement it ignored.**
3. **A WALL already hit.** A term the new route is walking toward that the
   retired route already proved impossible, or already got past. **`[LJ-1.146]`
   found `levelIn`'s wall had been named TWICE by two methods and four
   dispatches went around it. That was found inside the LIVE record. Look for
   the archived equivalent.**
4. **A DESIGN already settled.** A shape the new route is choosing between when
   the archive records the choice and its reason.

## WHAT IS **NOT** A MISS, and this is the trap

**The retired route's CLAIMS are not admissible.** `[LJ-1.11]` ruled its
condensation target classically FALSE. **Take SHAPE from the archive, never a
claim.** So:

- **A theorem the archive proves about the rud tower is not a theorem about
  the L tower.** Say what would transfer and what would not.
- **A price measured on the retired tree is not a price on this one.** The same
  P-l cuts both ways.
- **A design settled for a route that was abandoned may have been settled
  BECAUSE of that route.**

**So every finding needs two parts: what the archive holds, and what it would
actually be worth here.** A finding that only says 「this exists over there」 is
half a finding.

## THE ABORT CRITERION

- **You complete the census**: report it, ranked by what it would have saved.
  STOP.
- **You find nothing beyond the `CSB` case**: **SAY SO PLAINLY.** That is a
  real and valuable result: it would mean the discipline is working and one
  miss was an accident. **Do not manufacture findings to fill a table.**
- **The census is larger than you can complete**: say how far you got, by what
  method, and what is left. **A partial census that names its own boundary is
  worth more than a complete-sounding sample.**

## THE STANDARD I WILL HOLD YOU TO

**Evidence is `file:line` on BOTH sides**: the archive file that holds the
thing, and the new-route brief or report that did not name it.

**Mark every negative MEASURED or INFERRED.** 「No brief pointed at this」 is
MEASURED only if you searched every brief and say which search.

**Rank by what it would have saved**, in dispatches or in lines or in seconds,
whichever the evidence supports. **A miss that would have saved nothing is
still a miss but it is not the same finding.**

## WHAT YOU MUST NOT DO

- **Do not edit any master and do not edit any brief or report.** Briefs and
  reports are frozen records. **You write your own report and nothing else.**
- **Do not run Agda.** Two siblings are running and one is measuring seconds.
- **Do not re-litigate the route.** DD2 rules the endpoint and `[LJ-2.5]` rules
  the architecture. **You audit whether the archives were surveyed, not whether
  the route is right.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## WHERE TO START, and I am naming my own likely blind spots

**These are the new-route threads where I would look first, because they are
the ones whose subject matter the retired route also touched. This list is
mine and it may be exactly wrong; build your own.**

- **`CSB` and cardinal arithmetic.** The known miss. **Check whether the rest
  of `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md` holds more:
  Cantor, the equality half of 5.4.**
- **`levelIn` and `cover`**, `[LJ-1.146]`, `[LJ-1.151]`. The condensation
  transfer. **The retired route had a condensation chapter.**
- **The square law**, `[LJ-1.107]`, A5. `archive/` may hold the ambient chain.
- **The bounding device**, `[LJ-1.152]`, `[LJ-1.154]`. Separation against
  replacement, `boundingOrd`, the stage as an element of L.
- **The code set and satisfaction**, `[LJ-1.83]`, `[LJ-1.113]`, the 25 closure
  facts, `KFacts`.
- **The twelve-row agreement**, `[LJ-1.76]`, `[LJ-1.144]`, `[LJ-1.150]`.
- **The refutable frame hypotheses**, `[LJ-1.151]`, `[LJ-1.153]`. **36 refuted
  and repaired today. Did the retired route hit this class?**

## ARCHIVE (DD18)

**The whole point of this task is the archives, so the section is the task.**
But read these first, because they tell you what the new route THINKS it knows:

- `dev/PLAN.md` section 0.0 and section 11, the live status and the task index.
- `agents/tasks/LJ-1-131/lj-1.131-report.md`: the route pricing that split
  A-prime into seven blocks.
- `agents/tasks/LJ-1-146/lj-1.146-report.md`: the wall named twice.
- `archive/dev/TASKS-archived.md` and `STATUS-archived.md`: **what the retired
  route said it had delivered.** That is your index into `archive/src/`.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Not this task's subject. Say so in one line.**

## SCOPE (read)

Everything under `archive/` and `agents/tasks/archive/`, and every brief and
report from `[LJ-1.1]` onward.

## SCOPE (write)

`agents/tasks/LJ-1-157/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for review` and read every statement.

- **DD18.** The archive survey is a brief section rather than a hope. **This
  task is DD18's enforcement.**
- **P-l.** A price from a comparable elsewhere is a hypothesis.
- **C-36.** Write the term you could not write.
- **C-31, C-32, C-33, C-34, C-37, C-39, C-40, D-10, D-26, D-29, D-30. I-5.**

## CONSTRAINTS

- Run `.venv/bin/python scripts/lint-prose.py --check` on anything you write.
- Evidence is `file:line` on both sides. Write ASD-STE100.

## RETURN

**Lead with the count: how many misses, and what the largest one would have
saved.** Then the table, ranked: what the archive holds at `file:line`, which
new-route task did not name it at `file:line`, what it would have been worth
here, and what would NOT transfer. Then your method and its coverage. Then
anything you could not settle. **Mark every negative MEASURED or INFERRED.**

**If the answer is 「one, and it was the `CSB` case」, say that in the first
line.**
