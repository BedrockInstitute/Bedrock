# LJ-1.347: settle the arity-numeral conjunct, marked INFERRED FALSE

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## THE CLAIM, and its author refused to overclaim it

**`[LJ-1.344]` reports:**

> `wCodesK`'s premise carries NO shapedness, MEASURED by reading
> `src/L/Condensation.lagda.md:7130-7136`, **so any bounded set with any
> pair-shaped member is legal.** I built the countermodel (`Residue344.agda`)
> from the same `KFacts` fields the supply uses. **`Bisect344B.agda` proves the
> key step for every positive numeral, exit 0 in 2.01 s.** The `m = 0` clause
> is a **WALL by two independent routes** (`empty-spec` transport, and
> `regularityV` at a concrete numeral), bisected across four interrupted runs at
> **330 s, 400 s, 160 s and 300 s**.
>
> **So the verdict is INFERRED FALSE, not MEASURED FALSE, and I do not claim
> more.**

**That refusal is why this task exists.** **The positive numerals are done. One
clause is missing and it is a wall.**

## AND IT FOUND TWO SITES NOBODY HAD COUNTED

> I also found the same conjunct at two sites the prior sweeps did not count,
> **`ShapesAgree`'s `compK` and `unCompK`** at
> `src/L/Condensation.lagda.md:6157-6175`, **whose subject carries no hypothesis
> at all.**

**`[LJ-1.345]` swept for the FATAL shape and found two.** **This is a THIRD
shape and its count is unknown.** **C-42: a refutation measures the site it
names.**

## THE TASK

**1. SETTLE `m = 0`.** Two routes walled. **A third may not.** **Or bisect the
wall itself: `[LJ-1.345]` showed how to get an honest figure past a cache hit,
and `[LJ-1.344]` interrupted four runs without isolating which sub-term
explodes.** **C-56: when a truncated or heavy proof walls, the cost is in the
ASSEMBLY. Write the cheapest control first.**

**2. SWEEP THE THIRD SHAPE.** **How many ties carry a conjunct whose subject has
NO hypothesis at all?** **Read them; do not grep for a token** (C-52). **Say the
count and name every one.**

**3. IF IT IS FALSE, SAY WHAT THE REPAIR IS.** `[LJ-1.343]`'s repair moved a
bound from one slot to another and cost 20 insertions. **The same shape may
apply.** **Do not land it; price it.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **`m = 0` SETTLES FALSE.** **Then the conjunct is false and the sweep's count
  says how much of the chapter it touches.** **This is the valuable outcome.**
- **`m = 0` SETTLES TRUE.** **Then the conjunct is TRUE and `[LJ-1.344]`'s
  INFERRED verdict is overturned by the branch it could not reach.** **Equally
  real; say so plainly.**
- **THE WALL SURVIVES A THIRD ROUTE.** **Then report the wall with its bisection
  and the verdict stays INFERRED.** **Naming which sub-term explodes is worth
  the task on its own.**
- **A WALL.** 30 minutes on one invocation is a wall: interrupt, report ELAPSED
  SECONDS, bisect. **NEVER raise the cap.** **Four runs already died here, so
  budget from the start and bisect early rather than late.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-347/`. **`src/` is forbidden** (I-5).
- **Do not touch `witK` or `graphWitK`.** A sibling has them.
- **Do not edit another task directory.** You may READ and RE-RUN the probes in
  `agents/tasks/LJ-1-344/`, especially `Residue344.agda` and `Bisect344B.agda`.
  **`Residue344.agda`, `Bisect344A.agda` and `Bisect344D.agda` do NOT return
  inside budget and its report says so at the top.**
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO and a sibling is live. Use exactly:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **The two obvious alternatives both OVER-COUNT, MEASURED 2026-08-15.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended).
- **RUN A NEGATIVE CONTROL that MEASURES, and include NON-VACUITY.** This whole
  chain exists because a hypothesis that typechecks says nothing about its
  truth, and `[LJ-1.341]` and `[LJ-1.345]` both answered non-vacuity explicitly.
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-347/lj-1.347-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Nine of my last nineteen briefs carried a claim an agent measured FALSE.**
**The one at risk: 「the two new sites carry the same conjunct」.** **That is
`[LJ-1.344]`'s reading, and `[LJ-1.346]` measured that its own first count of a
different thing was too narrow.** **Read `:6157-6175` yourself before you build
on it.**

## THE RULES

**D-10** is the frame: price the TRUTH before the proof. **C-42** is the sweep.
**C-56** is the wall. **C-45, C-44, C-52, C-53, C-57, C-36, P-l, P-i.**
**C-12, C-22, C-32, C-39, C-40, C-49, C-50, C-51, C-55.** I-5.
**D-1, D-26. DD0, DD4, DD8, DD18, DD23, DD24.**

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), which is
AC-against-GCH, fixed at `scripts/measure/ledger.py:50`. **Every term on this
chain has been class-free; say whether yours is.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-344/lj-1.344-report.md`, read WHOLE.** It funds you and
  its own top matter names which of its probes do not return.
- **`agents/tasks/LJ-1-341/lj-1.341-report.md`** and
  **`agents/tasks/LJ-1-345/lj-1.345-report.md`**, the refutation and its review,
  for what a settled falsity looks like here.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** **`[LJ-1.345]` confirmed against the primary
source that Devlin binds every unbounded quantifier by a set built from the
members of its argument.** **Say in one line whether a conjunct whose subject
carries no hypothesis at all has any counterpart in his text.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`src/L/Condensation.lagda.md:7130-7136` FIRST, then `:6157-6175`.

## SCOPE (write)

`agents/tasks/LJ-1-347/` only.

## RETURN

**Lead with ONE word: FALSE, TRUE or STILL-WALLED.** Then the `m = 0` clause,
settled or bisected to a named sub-term. Then the third shape's count, with
every site named. Then whether the two new sites really carry it. Then the
repair priced, if it is false. Then your negative control including
non-vacuity. **Mark every negative MEASURED or INFERRED.**
