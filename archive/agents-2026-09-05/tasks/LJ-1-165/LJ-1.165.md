# LJ-1.165: BUILD the crossing face and close `levelIn` and `cover`

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**This is the BUILD. Every piece of it has been gated and every gate is green.**

**`[LJ-1.7]` is STRUCTURE ONLY because `levelIn` and `cover` are hypotheses.
Discharge them.**

## WHAT IS GATED, and every figure below is somebody's measurement

| piece | state | source |
|---|---|---|
| **the route** | both hypotheses close in **16 in-fence lines** from a crossing face at the collapse image, and the wall term appears NOWHERE | `[LJ-1.160]`, probe green |
| `CrossOut` leg 1, the transfer | **20 in-fence lines** | `[LJ-1.161]`, probe green |
| leg 2, the moved formula means the delivered one | **18** | `[LJ-1.161]` |
| leg 3, the identification | **125**, and the chain typechecks WHOLE | `[LJ-1.162]`, probe green |
| **`CrossOut` total** | **163** | |
| `HasLevels` and `Covered` | their transport machine is **DELIVERED**, `src/L/BoundedSubset.lagda.md:195-196` and `:250-251`, every formula, both directions | `[LJ-1.161]` |
| `ElemDown` | **0 lines, DELIVERED, and now reachable** at `src/L/BoundedSubset.lagda.md:1551` | `[LJ-1.163]`, `[LJ-1.164]` |

**Four probes are on disk and green. Read them before you write anything:**
`agents/tasks/LJ-1-160/ProbeLJ1160A.agda`, `LJ-1-161/ProbeLJ1161A.agda`,
`LJ-1-162/ProbeLJ1162A.agda`, `LJ-1-164/ProbeLJ1164A.agda`.

## THE MECHANISM, so you build the right thing

**The wall `π (Lset m') ≡ Lset (π m')` is an artifact of WHERE the argument
runs.** A hull is not transitive, so a value proved there must be CARRIED
across the collapse, and carrying it is the term `[LJ-1.51]` could not write.

**The collapse image is transitive** (`C.πX-trans`, `src/V/Collapse.lagda.md:89`),
**so absoluteness applies directly and nothing needs carrying.** Devlin works at
the transitive collapse and never commutes it with the level construction.

## THE ORDER

1. **Build the crossing face**: `CrossOut`, `HasLevels`, `Covered`.
2. **Then close `levelIn` and `cover` from it**, the 16 lines `[LJ-1.160]`
   measured.
3. **Then check that `Devlin55.BoundedSubsetAt`'s `theorem` still derives**,
   which `[LJ-1.164]`'s probe already showed it does once the pair is
   discharged.

**Build in that order and typecheck after each step, not at the end.**

## THE ABORT CRITERION, fixed BEFORE you start (D-1, DD8)

- **It lands and `theorem` derives**: report and STOP. **That completes
  `[LJ-1.7]`.**
- **Any piece exceeds its gated figure by more than 50 percent**: **STOP and
  report the overage with its cause.** 163 becoming 250 is a re-price and the
  owner decides whether to continue; 163 becoming 400 means a gate was wrong
  and that is the finding.
- **The obligation nothing supplies bites.** `[LJ-1.162]` MEASURED that the
  bounded step's backward direction needs the definable power of the recorded
  value to be IN `K`, that this operator occurs ZERO times in `Condensation`
  and all three `*Agree` masters, and that `KFacts` has no such field. **If you
  reach it and cannot pay it, STOP and say so. That is a complete answer and it
  re-opens the price.**
- **A wall**: STOP with its wall-clock. **`[LJ-1.161]` measured one at 20
  minutes and 9.03 GB on the level-hood certificate, with NO heap exhaustion,
  and the tree already routes around it by splitting the twelve rows across
  masters.** Fix your own wall-clock criterion in writing before each run.
  **Never raise the cap.**

## THE THINGS THIS WING HAS MEASURED ABOUT ITSELF, which bind you

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
  **`[LJ-1.151]` found a delivered hypothesis that was outright FALSE and
  `[LJ-1.153]` repaired 36 of that class. `[LJ-1.161]` found three delivered
  definitions with NO consumer. `[LJ-1.163]` found a fourth.** **Do not add a
  fifth: everything you state, instantiate.**
- **C-40.** Typecheck EVERY consumer, not the master you edit. **I committed
  three RED trees in one day for omitting exactly this.**
- **No `postulate`, no hole, no unsolved meta.** Report all three as absent, as
  `[LJ-1.162]` did.
- **P-l.** Four cures at this cluster transferred to some sites and not others,
  all measured in the last day. **A gated figure is a price for the probe's
  site; re-measure at the master.**

## WHAT YOU MUST NOT DO

- **Do not delete lines to improve a ratio.** DD24's ratio exists so the
  content must be the same KIND of content.
- **Do not touch `src/L/Coding/Graph.lagda.md`**: 21 consumers are green on
  `[LJ-1.147]`'s seal.
- **Do not touch the three `*Agree` masters**: `[LJ-1.158]` collapsed their
  telescopes and `make check` is green.
- **Do not undo `[LJ-1.164]`'s move.** `elem-down` is at `:1551`, above `Co`,
  and the reachability was measured in BOTH directions.
- **A probe goes in `agents/tasks/LJ-1-165/`**, never in `src/`, tracked.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it. **Run `agda` on the master and every
  consumer after each step.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**MEASURED across the gates: `[LJ-1.160]` 73 percent shared, `[LJ-1.161]` 16 of
20 template, `[LJ-1.162]` 103 of 134 template with only 10 lines Def-tower
content.** **Say what fraction of what you build names a tower, and where the
fork point sits.**

## ARCHIVE (DD18)

**`[LJ-1.157]` measured 37 of 61 live briefs citing no archive. `[LJ-1.160]`
found the phase's bypass inside one. `[LJ-1.162]` looked and found nothing and
said so. `[LJ-1.164]` found the archive never had the defect it was repairing.
All four outcomes are real and this section is not a form.**

- **`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:160-257`**, the
  crossing face and `module Assembly`, whose SHAPE `[LJ-1.160]` took. **The
  archive states `CrossOut` and never proves it, MEASURED at nine places by
  `[LJ-1.162]`. You are building what it only stated.**
- `archive/src/2026-08-09-rud-route/L/Hull.lagda.md:248-249`, `:396-398`, the
  BUILT Tarski-Vaught theorem and `hull-closed`.
- **Take SHAPE, never a claim.** `[LJ-1.11]` ruled that route's condensation
  target classically FALSE.
- `agents/tasks/LJ-1-160/` through `LJ-1-164/`, all five reports, read WHOLE.
- **`dev/LESSONS.md` C-38 as extended, C-35, C-40, P-l, P-i, P-y, C-12, C-36**,
  read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md`. **`[LJ-1.162]` MEASURED that Devlin's step (a)
is stated at the BOUNDED matrix with only the outer existential unbounded, and
that the delivered `Lset-only` is NOT his (a).** **Follow Devlin's own form.**
Return a **LITERATURE USED** section.

## SCOPE (read)

The four green probes FIRST, then `src/L/BoundedSubset.lagda.md:900-930` and
`:1400-1560`.

## SCOPE (write)

`src/L/BoundedSubset.lagda.md`, and `src/L/Condensation.lagda.md` ONLY if the
face must live there. Your report and probes are `agents/tasks/LJ-1-165/`.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for build` and read every statement.

- **C-38 as extended, C-35, C-40, C-12, C-22, C-36, C-39.**
- **DD8, DD13, D-1, P-l, P-i, P-y, P-w, P-q, P-t.**
- **D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`, and **report in-fence lines
  against each gated figure.**
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- **Run `.venv/bin/python scripts/check-unbound-hyp.py` and report the count.**
  It stands at 2, and both are known false positives.
- DD23 freezes mathematical prose. **Code comments are not prose; write them.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with whether `levelIn` and `cover` are DISCHARGED and whether `theorem`
derives.** Then each piece against its gated figure. Then every consumer's
verdict. Then the checker counts. Then any wall. Then the DD4 answer. **Mark
every negative MEASURED or INFERRED.**
