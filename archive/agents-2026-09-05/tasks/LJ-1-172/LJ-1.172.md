# LJ-1.172: BUILD the supply, in dependency order, landing incrementally

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**Twelve gates have measured this chain end to end. Build it.**

**`[LJ-1.165]` built the assembly and REMOVED it because nothing supplied its
face. You build the face.**

## THE CHAIN, and every figure is somebody's measurement

| step | lines | evidence |
|---|---:|---|
| 1. pairing closure at an ARBITRARY limit | **35**, net +15 | `agents/tasks/LJ-1-166/ProbeLJ1166A.agda:113-136`, green; drop-in re-proves all three delivered `ω` lemmas with no adapter (`[LJ-1.167]`) |
| 2. the parameter key by the RE-KEY arm | **37** | `agents/tasks/LJ-1-170/ProbeLJ1170A.agda`, green |
| 3. the key's object-level reading, both directions | **56** | `agents/tasks/LJ-1-171/ProbeLJ1171A.agda`, green, 23 out and 21 in |
| 4. `powIter` from steps 1 to 3 | **12** | `[LJ-1.167]`, from the one missing fact |
| 5. `K(u)`'s closure layer, one `KFacts` VALUE | **88** | `agents/tasks/LJ-1-166/ProbeLJ1166A.agda`, green, and `KFactsCons` ACCEPTS it |
| 6. the satisfaction layer, 28 fields | **about 270** | survey on nine delivered comparables (`[LJ-1.168]`) |
| 7. `CrossOut`, three legs | **163** | `[LJ-1.161]` 20, `[LJ-1.161]` 18, `[LJ-1.162]` 125, chain typechecks whole |
| 8. the assembly, `levelIn` and `cover` | **17** | `[LJ-1.165]`, green, master exit 0 |

**Steps 1 to 5, 7 and 8 have GREEN PROBES ON DISK. Read them before you write.**

## THE ORDER, and it is a dependency order

**Build 1, then 2, then 3, then 4, then 5. Typecheck after EACH.** Steps 6, 7
and 8 come after, and **you may stop before them**: see the abort criteria.

**Land incrementally.** A master that typechecks after step 3 is worth more
than a whole chain that does not compile. **Do not hold everything back to the
end.**

## THE ABORT CRITERIA, graded and fixed BEFORE you start (D-1, DD8)

- **A step lands within 50 percent of its gated figure**: continue.
- **A step exceeds its figure by more than 50 percent**: **STOP THERE, keep
  what typechecks, and report the overage with its cause.** Do not push on.
- **Steps 1 to 5 land**: that alone is the deliverable if time runs short.
  **`KFacts` gets a value for the first time in this project.**
- **Anything walls**: STOP with its wall-clock. **Never raise the cap.**

## THE TWO THINGS THAT WILL BITE, both measured

**ONE: write the parameter component as `env`, NEVER as `finSet`.**
`[LJ-1.171]` MEASURED that a finite set keeps NO index, its out-direction
returns a truncated one, and at a constant family two arities give the same
set — **so it cannot be read back, and the reading substitutes BY POSITION.**
The environment is delivered with both directions:
`src/L/Coding/Environment.lagda.md:84-86`, `EnvSet.lagda.md:232-283` in and
`:315-379` out.

**TWO: the key lands at `sucIter 7`, not `sucIter 5`.** `[LJ-1.171]`'s second
probe measured it. **Still a fixed iterate, uniform in the formula and in the
parameter count**, which is the property the whole arm turns on.

## THE ONE TERM THAT STILL CARRIES AN INFERENCE

**The code half must run the decoder at the empty alphabet.** `[LJ-1.171]`
MEASURED that `Decode`, `InL`, `Closed` and `Shape` are all generic in the
alphabet, and that `src/L/Choice/Name.lagda.md:396-403` already writes the
bookkeeping — **then declined to instantiate and published NO figure.**

**Instantiate it and report its cost.** If it is dearer than the rest of step 2
put together, **stop and say so**: that would re-price the arm.

## WHAT THIS WING HAS MEASURED ABOUT ITSELF, and it binds you

- **C-38 as extended.** `[LJ-1.151]` found a delivered hypothesis that was
  outright FALSE; `[LJ-1.153]` repaired 36 of that class; `[LJ-1.161]`,
  `[LJ-1.163]` and `[LJ-1.165]` each found a delivered definition with NO
  consumer. **Everything you state, instantiate. No `postulate`, no hole, no
  unsolved meta — report all three as absent.**
- **C-40.** Typecheck EVERY consumer after each step. **I committed three RED
  trees in one day for omitting exactly this.**
- **SEARCH BEFORE YOU WRITE.** Five misses this phase, all mine, all in
  delivered live code, and two of them in `src/L/Choice/Name.lagda.md`. **The
  measured blind spots are `src/L/Choice/`, `src/L/Coding/`,
  `src/L/Axioms/Separation.lagda.md` and `src/L/Ordinal/StageArith.lagda.md`.**
- **P-l.** A gated figure is a price for the PROBE's site. Re-measure at the
  master and report both.

## WHAT YOU MUST NOT DO

- **Do not delete lines to improve a ratio.**
- **Do not weaken a statement to make it provable.**
- **Do not touch the three `*Agree` masters**, `src/L/Coding/Graph.lagda.md`,
  or `[LJ-1.164]`'s move of `elem-down` to `:1551`.
- **A probe goes in `agents/tasks/LJ-1-172/`**, never in `src/`, tracked.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised. Fix a
  wall-clock criterion in writing before each run.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it. **Run `agda` on each changed master and
  each consumer after each step.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**MEASURED across the gates: the re-key arm's two ingredients name no tower, the
key's reading has DELTA ZERO by token count, and the pairing-growth law
transfers whole.** **Report the tower-token count of what you actually write,
per step.**

## ARCHIVE (DD18)

**Five delivered zero-consumer files held part of an answer this phase; three
archive lookups changed a verdict; and ONE archive claim I put in a brief was
MEASURED FALSE, because the lemma I offered ASSUMES the bound it appears to
prove.**

- **`archive/src/2026-08-09-rud-route/L/Coding/`**: MEASURED by `[LJ-1.171]` to
  hold NO object-level parameter reading. **Check whether it holds anything for
  steps 4 or 5.**
- **Take SHAPE, never a claim.** `[LJ-1.11]` ruled that route's condensation
  target classically FALSE.
- `agents/tasks/LJ-1-166/`, `LJ-1-170/`, `LJ-1-171/`, all reports read WHOLE.
- **`dev/LESSONS.md` C-38 as extended, C-40, C-35, P-l, P-i, P-y, C-12, C-36**,
  read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`_build/literature/dev2.txt:593-640`. **`[LJ-1.171]` MEASURED the correspondence:
arity to one union member, code to another with sequences, parameters to a
third, and Devlin's fourth has NO analogue here because it bounds free
variables which this tree computes at the meta level.** **Follow that
correspondence.** Return a **LITERATURE USED** section.

## SCOPE (read)

The five green probes FIRST, in the order of the table.

## SCOPE (write)

`src/L/Coding/`, `src/L/Condensation.lagda.md`, `src/L/BoundedSubset.lagda.md`,
and `src/L/Choice/Name.lagda.md` ONLY if step 1's drop-in replaces its
`ω`-only lemma. Your report and probes are `agents/tasks/LJ-1-172/`.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for build` and read every statement.

- **C-38 as extended, C-40, C-35, C-12, C-22, C-36, C-39.**
- **DD8, DD13, D-1, P-l, P-i, P-y, P-w, P-q, P-t.**
- **D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`, **and report in-fence lines
  against each gated figure, per step.**
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- **Run `.venv/bin/python scripts/check-unbound-hyp.py` and report the count.**
  It stands at 2, both known false positives.
- DD23 freezes mathematical prose. **Code comments are not prose; write them.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with which steps LANDED and whether `KFacts` has a value.** Then each
step against its gated figure. Then every consumer's verdict after each step.
Then the decoder's cost. Then the checker counts. Then the DD4 answer. **Mark
every negative MEASURED or INFERRED.**
