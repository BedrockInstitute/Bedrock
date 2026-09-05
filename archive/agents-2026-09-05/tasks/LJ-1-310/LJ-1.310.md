# LJ-1.310: name every step of the composite's TERM, from φ₀ to `Graph*`

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## GOAL

**This is the largest UNPRICED piece on the GCH side, and `dev/PLAN.md` section
0.0 names it first of four.** `[LJ-1.7]`'s last open parameter is `amb`, its
only route is `q'`, and `q'` IS the composite.

**`[LJ-1.302]` proved the composite's type is WRITABLE and that a composite
FEEDS.** It did NOT prove one exists. Its own words, at
`agents/tasks/LJ-1-302/lj-1.302-report.md:9`:

> The composite's TYPE is `q'` itself, it is WRITABLE, and it FEEDS.

**The 470 hand-written lines in PLAN 0.0 price the INGREDIENTS**, not the
composite: the clean 23 modules, the dirty seven's ties, `StepAgree` and
`ApproxAgree`. **Nobody has said what the composite's own term is made of.**

## THE OBJECT, and it is a FUNCTION and not a record

**`ProbeLJ1302A.agda:72-75`, and I read it:**

```agda
  Composite : Type (ℓ-suc ℓ)
  Composite = (γ : Vec A.R.SC 2)
            → ⟨ A.ambient γ (embed P1241.φ₀) ⟩
            → ⟨ A.ambient γ (S.Graph* {2} zero (suc zero)) ⟩
```

**In words: given an environment of two class-carriers, transport an ambient
reading of `φ₀` into an ambient reading of `Graph*`.**

**That is one transport between two codings of one notion, at the ambient
carrier.** **It is the same SHAPE the thirty `Agree` modules prove at the L
carrier**, which is why the thirty are the ingredients.

**The two endpoints, both of which you must read before anything else:**

- **`φ₀` at `agents/tasks/LJ-1-241/ProbeLJ1241A.agda:145-146`**,
  `φ₀ = closeN 14 (pins ∧̇ renamed)`, arity two.
- **`S.Graph*`, from `module S = D.Supply DefAt DefAt-in DefAt-out`** at
  `ProbeLJ1302A.agda:70`. **Find `Supply` in the delivered tree and read what
  `Graph*` unfolds to.**

## THE TASK: A CHAIN, WITH A SUPPLIER PER STEP

**Produce ONE table. Each row is a step from `φ₀` to `Graph*`. Each row names
its supplier at `file:line` and carries exactly one of three marks:**

| mark | meaning |
|---|---|
| **SUPPLIED** | a delivered `src/` name proves this step today |
| **BUILT-AT-A-PROBE** | a term exists in `agents/tasks/`, never landed |
| **UNBUILT** | no term anywhere, and this is what the composite still costs |

**The UNBUILT rows are the deliverable.** They are the number PLAN 0.0 cannot
state. **Give each one a line estimate with its basis** (DD8: one number, and
it names whether the basis is a probe, a delivered comparable or a survey).

**DO NOT return「it decomposes into the thirty Agree modules」.** `[LJ-1.302]`
already said the composite decomposes; **this task asks WHICH steps, IN WHAT
ORDER, and WHO SUPPLIES EACH.** A decomposition with no supplier column
re-states what is known.

## PREMISES, each of which you must VERIFY or REFUTE

- **`[LJ-1.302]`'s `Fed.amb-from-composite = AS.amb` typechecks, exit 0.** So a
  composite term is sufficient for `amb`. **VERIFY that it is the ONLY thing
  missing**, or name what else is.
- **`[LJ-1.304]` BUILT `StepAgree` and `ApproxAgree` as terms**, about 190
  lines, and reported that neither module exists in `src/`. **They are
  BUILT-AT-A-PROBE, not SUPPLIED. Confirm at `file:line`.**
- **`[LJ-1.306]` ported the clean 23 modules generic at ZERO changed lines**,
  into `agents/tasks/LJ-1-306/GenAgree.agda`, exit 0. **It is under adversarial
  review as `[LJ-1.308]` right now, so treat its claims as UNSETTLED**, mark
  anything resting on it INFERRED, and say so.
- **`[LJ-1.298]` measured the port's rate at ONE site.** P-l: a judgement at one
  site is a hypothesis at another.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE CHAIN IS COMPLETE AND EVERY STEP HAS A SUPPLIER.** **Then the composite
  is assembly and PLAN 0.0's item 1 is wrong to call it unpriced.** Report the
  chain and the assembly cost. STOP. **That is the best outcome and I do not
  expect it.**
- **SOME STEPS ARE UNBUILT.** **The expected outcome.** Name them, price them,
  rank them by what blocks the most.
- **A STEP IS UNBUILDABLE HERE.** **Say which and why, at `file:line`.** That
  would re-price the route and the project must hear it before funding wave 2.
- **THE TYPE IS WRONG.** `[LJ-1.302]` wrote `Composite` at a probe. **If the
  delivered `AmbientStep` needs a different type in its `q'` slot, that is a
  refutation and it is the most valuable thing you can return** (C-36).

## WHAT YOU MUST NOT DO

- **RUN NO AGDA. This task is READING.** **C-12 caps this machine at TWO
  concurrent Agda processes and both are spoken for**: `[LJ-1.305]` holds one
  and `[LJ-1.308]` may take the other at any moment. **A third process is the
  crash the heap caps exist to prevent.** **If you believe a step needs a
  typecheck to settle, SAY WHICH STEP and I fund it separately.** **An honest
  「this needs a probe」beats a guess dressed as a reading.**
- **LAND NOTHING.** Write only in `agents/tasks/LJ-1-310/`. **`src/` is
  forbidden** (I-5). Do not touch another task directory.
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-310/lj-1.310-report.md` in your FIRST five
  minutes** and fill the chain table into it as rows land (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` on what you write.
  **No em dash in any language.** DD23 freezes mathematical prose in `src/`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE RULES THIS CHAIN EARNED

**C-38 as extended. A hypothesis is discharged when something SUPPLIES it.**
**This whole task is C-38 applied to one term: for each step, WHAT supplies
it.**

**C-45. `exit 0` is not a supply.** `[LJ-1.302]`'s probe exits 0 with `comp` as
a MODULE PARAMETER. **A parameter is an assumption, never a supply.** That is
precisely the gap this task measures.

**C-44. A brief's claim is a measurement until you check it.** Every claim above
is mine from a reading today, and I did not run Agda either.

**C-36. A failed substitution is not a proof of impossibility.** If a step will
not close, write the term you could not write.

**D-10. Price the TRUTH of a recorded residue before pricing its proof.** **The
recorded residue is「the composite is unwritten」. Check it is still true**:
three times this month a report called absent what the repository held.

**P-k. A read lemma is stated where its consumers use it.** Relevant to where
each UNBUILT step should eventually live.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **With no Agda, most of your positives
are INFERRED too, and you must mark those honestly.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**NAME YOUR AXIS** (C-46). **The composite lives on the L-against-ambient axis,
which is the Def tower's internal axis and NOT DD4's own.** DD4's axis is
AC-against-GCH, fixed in code at `scripts/measure/ledger.py:50`. **For each
UNBUILT step, say whether writing it generic would serve the AC end at all, or
whether it is GCH-only.** **A step that serves both is worth more and should be
written first, and that is the DD4 reading of this chain.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-302/lj-1.302-report.md`, read WHOLE.** It is the
  foundation and its section 4.1 discusses the composite term directly.
- **`agents/tasks/LJ-1-304/lj-1.304-report.md`**, the two built modules.
- **`agents/tasks/LJ-1-297/lj-1.297-report.md`**, six ambient readings supplied
  in 20 lines. **It is the nearest comparable for what an ambient supply costs.**
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route had a composite over the stems and its archived statement is on
  the record. **Say what would not transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** **Devlin's condensation argument transports
satisfaction between a structure and its collapse.** **Say in one line whether
he needs a composite of this shape at all**, because if the transport is free in
his setting then our composite is the PORT's price and not the mathematics, and
that changes what「unbuilt」means. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-302/ProbeLJ1302A.agda` FIRST, whole, then that task's report
whole.

## SCOPE (write)

`agents/tasks/LJ-1-310/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for recon` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **C-38, C-45, C-44, C-36, D-10, P-k.** Named above with what each governs.
- **P-l.** A judgement at one site is a hypothesis at another.
- **C-12.** No Agda in this task, and the reason is above.
- **C-22, C-32, C-39, C-40, C-42.** I-5. **D-26.**
- **DD0, DD4, DD8, DD18, DD24.**

## RETURN

**Lead with ONE number: how many steps the chain has, and how many are
UNBUILT.** Then the chain table, in order, each row with its supplier at
`file:line` and its mark. Then a line estimate with its basis for every UNBUILT
row. Then which step blocks the most. Then the DD4 reading, per UNBUILT step.
Then any step you believe needs a typecheck to settle, named. **Mark every
negative MEASURED or INFERRED.**
