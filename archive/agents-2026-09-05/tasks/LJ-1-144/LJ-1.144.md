# LJ-1.144: the three `*Agree` masters have no consumer, and their bridge is owed

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**Settle whether `src/L/Condensation/{Twelve,Upper,Lower}Agree.lagda.md` earn
their place.** 842 in-fence lines, **56.06 seconds, 27 percent of the GCH
wing's whole cold-check cost, and NOTHING imports them except the reading
catalog.**

**Decide it, and say what it costs either way. Do NOT rewrite them.**

## WHAT IS MEASURED, and I verified every line myself

**The import graph, MEASURED today:**

| master | imported by |
|---|---|
| `L/Condensation/TwelveAgree` | `src/Everything.lagda.md` ONLY |
| `L/Condensation/UpperAgree` | `TwelveAgree`, `Everything` |
| `L/Condensation/LowerAgree` | `TwelveAgree`, `Everything` |

**So the cluster's ONLY external consumer is the reading catalog.** No proof
uses it.

**C-35 is exactly this: a delivered block with no consumer is UNTESTED.**

**The DD24 verdict, measured 2026-08-13 against the re-selected baseline
0.011828 and a bar of 0.0136:**

| master | s/line | lines | seconds |
|---|---:|---:|---:|
| `TwelveAgree` | **0.0819** | 309 | 25.32 |
| `LowerAgree` | **0.0731** | 265 | 19.38 |
| `UpperAgree` | **0.0424** | 268 | 11.36 |

**All three OVER, at 6.9x, 6.2x and 3.6x the baseline.** The wing as a whole is
1.56x; **the Condensation family is 84 percent of its seconds.**

## THE OWED BRIDGE, and it is the reason the consumer is missing

**`dev/PLAN.md:548`, the `[LJ-1.76-A]` audit row, records this and it has
stood since 2026-08-12:**

> `SatGraphB.twelveB` is one right-nested chain of twelve; the composer proves
> `sixB` and `sixB`. **Different `Formula` terms.**

**That is the missing bridge. Until it is built, nothing can consume the
cluster.**

**`[LJ-1.76]` itself returned THREE MASTERS GREEN at 53.20 seconds** and
reported them five times cheaper than the probe price. **The masters are real
and they typecheck. The question is whether the thing they prove is the thing a
consumer needs.**

## WHAT TO DECIDE, and I want the reasoning

1. **What would the consumer be?** Name the theorem that would import
   `TwelveAgree`, and where it lives or would live. **If no such theorem exists
   on the current route, that is the answer and you should say so plainly.**
2. **Is the bridge buildable?** `SatGraphB.twelveB` against `sixB` composed
   with `sixB`. **Are the two `Formula` terms provably equal, propositionally
   or definitionally? Price it. If they are NOT equal, say what that means for
   the cluster.**
3. **Does the route still need this at all?** `[LJ-1.129]` found the wing's
   theorem carries ambient hypotheses the ambient universe cannot pay, and the
   owner ruled Route A-prime. **Check whether A-prime consumes the twelve-row
   agreement or routes around it.** `agents/tasks/LJ-1-131/` and
   `agents/tasks/LJ-1-136/` hold the route work.
4. **Then recommend ONE of three**, with its price:
   - **BUILD the bridge**, and the cluster gets a consumer.
   - **RETIRE the cluster** to `archive/src/<date>-<slug>/`, and the wing loses
     842 lines and 56 seconds. **Retirement is priced from the REWRITE side**
     (DD13): price the ideal form of the content written fresh today FIRST,
     then compare. 「We already paid for it」 decides nothing in either
     direction.
   - **KEEP it unconsumed**, and say what that buys and what C-35 costs.

## THE PERFORMANCE QUESTION IS **NOT** YOURS

**A sibling task owns why the Condensation family is slow.** Do not diagnose
`P-x`, do not optimize, do not touch `src/L/Condensation.lagda.md`.

**But the two answers interact and you must say how.** If the cluster retires,
56 of the family's 176.67 seconds go with it. **State that dependency in your
return so the orchestrator can order the two.**

## THE ABORT CRITERION

- **A recommendation with a price**: report and STOP.
- **The bridge is provably unbuildable**: **STOP AND SAY SO.** That decides the
  cluster and it is the most valuable return here.
- **A-prime turns out to consume the cluster after all**: that decides it the
  other way. Report it.
- **Anything walls**: STOP, report it with its seconds.

## WHAT YOU MUST NOT DO

- **Do not rewrite the three masters.** This is a decision task.
- **Do not retire anything.** You price the retirement; the owner rules it.
- **Do not touch `src/L/Condensation.lagda.md`.** A sibling owns it.
- **Do not touch `src/ProbeLJ1134A.agda` or `src/ProbeLJ1136*.agda`.**
- **A probe goes in `agents/tasks/LJ-1-144/`, beside this brief**, never in
  `src/`, and it is tracked and never deleted. **That rule changed today; read
  `AGENTS.md` fresh, and `dev/LESSONS.md` D-1.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.** A sibling
  may be measuring; **report the load beside every figure and say whether the
  machine was quiet.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker, so it is stated in every brief and answered in
every return.

**Here it is sharp: if the twelve-row agreement is template content that BOTH
trophies need, retiring it costs twice. If it serves only the GCH side on a
route the owner has now replaced, keeping it buys nothing.** Answer that.

## ARCHIVE (DD18)

- **`agents/tasks/archive/LJ-1-76/`**, read WHOLE: the brief, the report and
  the audit that recorded the owed bridge.
- **`agents/tasks/LJ-1-131/lj-1.131-report.md`** and
  **`agents/tasks/LJ-1-136/lj-1.136-report.md`**, for what A-prime consumes.
- `agents/tasks/LJ-1-129/lj-1.129-report.md`: why the route changed.
- `dev/PLAN.md:548`, the audit row. `dev/PLAN.md:513`, `[LJ-1.57-A]`, which
  predicted this family's cost before it was measured.
- **`dev/LESSONS.md` C-35, C-38 as extended, P-x, D-1**, read WHOLE.
- `dev/ARCHIVE.md` and `archive/README.md`, for what a retirement record
  carries, **if you recommend one**.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md` for what the condensation argument actually
needs, and `devlin-errata.md`. **Say whether Devlin's proof needs a twelve-row
agreement at all, or whether that is an artifact of our encoding.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`src/L/Condensation/TwelveAgree.lagda.md` FIRST, then `UpperAgree` and
`LowerAgree`, then `agents/tasks/archive/LJ-1-76/`.

## SCOPE (write)

`agents/tasks/LJ-1-144/` only, for your report and any probe. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and `--for probe`, and read
every statement.

- **C-35.** A delivered block with no consumer is UNTESTED. **This task IS
  C-35 firing.**
- **DD13.** Plan a retirement from the REWRITE side.
- **DD8.** Name the widest unmeasured term.
- **D-1.** The probe doctrine, as it now reads.
- **P-l, P-x, C-36, C-38 as extended, C-39, C-40, C-12, C-22.**
- **C-31, C-32, C-33, C-34, C-37, D-10, D-26, D-29, D-30. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with your recommendation and its price.** Then the consumer question:
what would import this, and does it exist. Then the bridge: buildable or not,
with the evidence. Then whether A-prime needs it. Then the DD4 answer. Then the
seconds that move under each option. **Mark every negative MEASURED or
INFERRED.**
