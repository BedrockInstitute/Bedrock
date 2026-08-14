# LJ-1.252: can `ω ∈ lam` be supplied, and does step 6 become fundable?

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.251]` closed the pricing question: `[LJ-1.7]` costs about 400 lines,
being step 6's 28 fields at about 255 plus a 147-line delivered comparable.**
**`dev/PLAN.md` section 0.0 had carried that 255 all along.**

**So the question is no longer WHAT it costs. It is whether it can be BUILT,
and one earlier attempt says not yet.**

**`[LJ-1.199]` was dispatched to build step 6 and stopped at ZERO LINES, on a
join rather than a budget.** Its C-36 term:

```agda
ω∈λ : ⟨ ω ∈ lam ⟩
```

**`envSetNumeral∈`, the ONE delivered bound that supplies `envSetK`, takes
`⟨ ω ∈ σ ⟩` as a hypothesis (`src/L/Coding/Key.lagda.md:476`).** To use it at
`K = Lset lam` the supply must produce a `σ` with `ω ∈ σ`, `fst B ∈ Lset σ` and
`sucIter 4 σ ∈ lam`. **The first is `ω ∈ lam` or `ω ∈ gam`, and neither is in
the telescope.**

**`HullStage`'s telescope is `lam, ordλ, succλ, X, X⊆L, ∅∈λ`**
(`src/L/BoundedSubset.lagda.md:903-905`). **`KValue`, the step-5 analogue, takes
`∅∈λ` and NOT `ω∈λ`.**

**Answer whether `ω ∈ lam` can be supplied. That one question gates 255
lines.**

## THE THREE WAYS IT COULD GO, and I do not know which

1. **It is DERIVABLE from the telescope as it stands.** `∅∈λ` plus `succλ` plus
   `ordλ` may already give `ω ∈ lam` by the limit closure. **If so, step 6 is
   fundable today and this task costs a few lines.**
2. **It must be ADDED to the telescope.** Then say what that costs at every
   consumer of `HullStage` (C-40), because adding a hypothesis to a delivered
   module is a change with a blast radius.
3. **It is FALSE at the site.** **`[LJ-1.199]` did not run Agda; it found the
   join by reading.** **If `lam` can be a limit below `ω`, the whole layer
   needs a different bound and that is the most valuable outcome here** (D-10).

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **DERIVABLE.** Build it, report the lines and the seconds. **Then step 6's
  255 is fundable and I dispatch the build.** STOP.
- **MUST BE ADDED.** **Name every consumer of `HullStage` at `file:line` and
  say what each would have to supply** (C-40). **That is the price of the
  change and it is a complete answer.**
- **FALSE AT THE SITE.** **Say why, and name what bound the layer would need
  instead** (C-36). **`[LJ-1.199]` found this by reading and never ran Agda, so
  a measured refutation or confirmation is worth more than its reading either
  way.**
- **A FOURTH WAY.** **`envSetNumeral∈` is「the ONE delivered bound」by
  `[LJ-1.199]`'s reading.** **Check that.** **If a second bound exists that does
  not want `ω ∈ σ`, the join dissolves and the layer never needed this.**
  **Five items have dissolved this month by exactly that question.**
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **`sucK` is inside step 6's 28
  fields and is the known 8 GB waller; if you meet it, that is a finding and
  not your failure.**

## WHAT YOU MUST NOT DO

- **Do not build step 6.** **You gate it.** 255 lines is a separate dispatch
  and it is not funded until this answers.
- **Do not edit any master.** This is a probe. **Nothing lands in `src/`, and a
  probe under `src/` is forbidden by I-5.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not touch `agents/tasks/LJ-1-253/`.** A sibling is live there.
- **A probe goes in `agents/tasks/LJ-1-252/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure**, discard a warm-up, and take at least
  three kept runs for any figure a decision rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap. **`[LJ-1.234]`
  met one and it was R-34's unpinned `InfinitySet` level meta, cured by
  `module IS = InfinitySet {ℓ}`.**
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## SIX RULES THIS CHAIN EARNED

**SEARCH THE OPEN-WORK LIST BY CONTENT, NOT BY NAME.** Ten dispatches
re-derived a price that `dev/PLAN.md` section 0.0 already carried, because
「step 6」and「the leaf supply」share no word.

**THE ARCHIVE BEARS UNTIL YOU OPEN IT.**

**A FAILED SUBSTITUTION IS NOT A PROOF OF IMPOSSIBILITY** (C-36). **A
READING is even weaker, and `[LJ-1.199]` ran no Agda.**

**`exit 0` IS NOT A SUPPLY** (C-45).

**CARRY A CLAIM'S QUALIFIER OR CARRY NEITHER.**

**C-44: if THIS brief states anything you cannot find, say so and treat it as
unproven.** **Everything above is `[LJ-1.199]`'s reading and I have re-derived
only the telescope line.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.113]:219-239` split step 6's 28 fields into 25 coding machinery and 3
per-tower, so this layer is about 7 percent per-tower and the rest is shared.**

**`ω ∈ lam` is a statement about a stage and it names no tower.** **Say whether
whatever you build or find is tower-neutral**, because a neutral bound is paid
once for both towers.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-199/lj-1.199-report.md`**, read WHOLE. **It is your
  brief within this brief and it never ran Agda.**
- `agents/tasks/LJ-1-251/lj-1.251-report.md`: the price and what is still
  unpriced.
- `agents/tasks/LJ-1-113/lj-1.113-report.md`: the 28 fields and the 25-against-3
  split.
- `agents/tasks/LJ-1-173/lj-1.173-report.md:857`: step 6 IS the 28 fields.
- **`src/L/Coding/Key.lagda.md:476`, `src/L/BoundedSubset.lagda.md:903-905`,
  and `KValue` in `src/L/Condensation.lagda.md`: read the source, never a
  report about it.**
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **The retired route had a stage bound too. Take SHAPE from the archive, never
  a claim**, and say what would NOT transfer.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**Say in one line whether Devlin's construction needs `ω` inside the stage at
this point**, or whether he takes the bound differently. Return a **LITERATURE
USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-199/lj-1.199-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-252/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed above.
- **D-10.** **Price the truth of the target before pricing its proof. `ω ∈ lam`
  may be false at the site.**
- **C-36.** Write the term you could not write.
- **C-40.** **Verify the CONSUMERS of a changed telescope, never the module
  alone.** **That is branch 2 and it is the likeliest one.**
- **C-44, C-45.** A claim is unchecked until you check it; audit the
  instantiation.
- **C-38, C-42, C-39. P-l. I-5, R-34. P-i, P-k, P-m, P-t, P-y, R-40. C-12,
  C-22. DD0, DD8, DD18, DD24, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with which of the four ways it went, and with `ω ∈ lam`'s status in one
word.** Then the lines and seconds if you built it, or every `HullStage`
consumer if it must be added, or the term if it is false. Then whether a second
bound exists. Then the tower answer. **Mark every negative MEASURED or
INFERRED.**
