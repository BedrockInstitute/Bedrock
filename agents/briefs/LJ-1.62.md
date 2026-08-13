# LJ-1.62: change the content class, or price the wall for the owner

tier: codex (default)

## GOAL

The wing is over DD24 and **the gate itself says what to do**. Change the
content class of the leaf-chain placement, or return a measured price for the
owner to rule on.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, at `24ada39`.
**The working tree carries `[LJ-1.61]`'s uncommitted placement of
`ShapedAgree` and `WitnessAgree`** (`src/L/Condensation.lagda.md`, 5,727
in-fence lines against HEAD's 5,562). **That placement is over the bar and I
did not commit it. You may re-spell it.**

## THE WALL, and I re-ran the gate myself to confirm it

`[LJ-1.61]` reported the gate from a sandbox where its `pgrep` guard cannot
read the process list, so it bypassed the guard. **I re-ran the same gate
myself with the guard working. The verdict holds:**

```text
  OVER 0.0173   5,727 lines     99.07 s  src/L/Condensation.lagda.md
check-ratio: wing aggregate 0.0152 s/line over 7,695 lines and 117.33 s,
             OVER THE BAR (1.38x the AC side at the SAME caliber)
```

The arithmetic that matters:

| | seconds | lines | aggregate |
|---|---:|---:|---:|
| wing before the placement | 90.01 | 7,530 | 0.01195, within |
| wing after it | 117.33 | 7,695 | **0.0152, 1.20x over** |

**The wing's entire headroom was 5.74 s. The placement is 165 lines and it
cost 27.6 s, which is 4.8x that headroom.**

## WHAT THE GATE SAYS TO DO, in its own words

> DD24 is the only threshold on this wing and the wing is over it. There is
> no line cap and no seconds cap to trade against; **the content class has to
> change.** Read P-m, P-q and P-t before optimizing: **a line lever is not a
> seconds lever.**

## THE HYPOTHESIS I WANT TESTED, and it is a hypothesis

The profile puts the cost outside the proofs. Cold, total 103,924 ms:

| | ms |
|---|---:|
| **`Miscellaneous`** (header and instantiation elaboration) | **65,896** |
| every named new definition, summed | about 6,700 |

**63 percent of the cost is not in any definition.**

`WitnessAgree`'s telescope is **44 parameters**
(`src/L/Condensation.lagda.md:6151-6195`): 16 `Fin`, the environment, 12
`tagEq`, 12 `numK`, then `innerK`, `innerPairK`, `pairK`, `carrierK`,
`arityK`, `witK`, `codesK`, `unCodesK`, `entryK`.

**And `WitnessAgree` instantiates that core FOUR times.**

**So: is the cost the re-elaboration of that telescope at each instantiation
site?** If it is, bundling the fixed site-fact block, the 12 `tagEq` and 12
`numK` and the closure facts, into **ONE record parameter** should cut the
header cost at every site.

**P-q is the caution and I want it respected.** A line saving is not a
seconds saving, and this must not be priced by a rate. **Measure the seconds.**
The reason I think this one is a seconds lever is that it removes elaboration
work rather than duplicated text, but **that reasoning is mine and it is
INFERRED. Your measurement decides it.**

**If the bundle does not move it, try reducing the NUMBER of instantiations**:
instantiate the core once and share it, if the four sites differ only in
arguments that can be abstracted. **Say which you tried and what each cost.**

**I am asking, not instructing.** If you see a better content-class change,
take it and say why. `dev/LESSONS.md` C-33 and C-37 exist because my briefs
foreclosed answers, and three dispatches this phase returned better answers
than the question I asked.

## THE ABORT CRITERION, fixed in advance per D-1

`python3 scripts/check-ratio.py --check` is the gate, and its **AGGREGATE**
is the verdict. A per-module OVER is advice, not a stop.

- **Under the bar**: place the rest of the chain, running the gate after each
  step, and take `levelIn` and `cover`.
- **Over the bar after your best content-class change**: **STOP.** Report the
  measured price of BOTH spellings, the profile attribution for each, and
  what you would need. **Do not spend the rest of the budget pushing.**

**This is the last dispatch before the price goes to the owner**, so the
quality of the number matters more than the distance travelled.

**The gate's guard may refuse in your sandbox** (`pgrep` cannot read the
process list). If it does, say so, bypass it as `[LJ-1.61]` did, and **keep
every Agda invocation sequential** so the guard's intent (C-12) holds.

## WHAT IS PROVED AND IS NOT AT RISK

**The mathematics is done.** The leaf adequacy is proved in both directions
in the probes, and `src/ProbeLJ161A.agda` carries the whole remaining chain
against the master and typechecks. **Nothing here is a re-proof.** This is a
spelling and pricing question only.

**Do not delete `src/ProbeLJ157A.agda`, `ProbeLJ156A.agda`,
`ProbeLJ155B.agda`, `ProbeLJ154A.agda`, `ProbeLJ161A.agda`.** A probe is
never committed, so they are the only copies. Copy forward, never move.

## THE LAWS, each with the ACTION it prescribes (C-37)

- **P-m. The rate is a content-class certificate.** Instantiation is the
  expensive class. **Say which class your new spelling is in, measured.**
- **P-q. A line lever is not a seconds lever.** **Never convert a measured
  line saving into a seconds saving with a rate.**
- **P-t.** State an assembly as a telescope at abstract propositions.
  `Lift12Back` and `Lift12Out` are placed and are the measured precedent:
  they bought 4.28x.
- **P-l.** A measured cure does not transfer by analogy. **Re-measure at this
  site.**
- **P-c, R-36, R-38. Seal at the birth site**, and expose with a read lemma
  in its own `opaque unfolding` block. `[LJ-1.59]` argued sealing would move
  the walk's cost rather than remove it and classed that **INFERRED**. **The
  wrappers are a different site, so that inference does not cover them.**
- **P-v.** Give a proof a NAME and pass the name.
- **C-34. Build the cure or report the wall.**
- **C-36.** A failed substitution is not a proof of impossibility. **Write
  the term you could not write.** You may strengthen; you may not weaken.

## WHAT YOU MUST NOT DO

- **You may not weaken a statement to make it cheap, and you may not narrow a
  direction.** Both directions are needed and that is settled
  (`[LJ-1.59]` section 0).
- **Do not touch anything under `src/L/Coding/`.**
- All masters carry ZERO placement of `absFo` or a placed `Δ₀`. **If you need
  one, STOP and report it.**
- **Do not delete content to buy the ratio.** P-q says it does not buy
  seconds, and the compression patch is measured to RAISE the ratio.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**There is a real tension here and I want it named rather than resolved
quietly.** The shared parameterized core is the DD4 move, and its
instantiation cost is what is over the bar. **If your content-class change
reduces sharing, say so and say by how much.** Do not trade the J tower's
inheritance for seconds without naming the trade.

## ARCHIVE (DD18)

- **`_build/lj-1.61-report.md`**, read WHOLE. Sections 4 and 7 are the wall
  and its profile attribution; section 2 is the guard refusal.
- `_build/lj-1.60-report.md` sections 1 and 5, the `Lift12Out` spelling that
  is the measured precedent for a content-class change.
- `_build/lj-1.58-report.md` section 2, the `Lift12Back` kit and its 4.28x.
- **`src/ProbeLJ161A.agda`**, the whole remaining chain against the master,
  green. **This is your source and it must survive.**
- `src/ProbeLJ157A.agda`, `ProbeLJ156A.agda`, `ProbeLJ155B.agda`,
  `ProbeLJ154A.agda`, the rest of the sources.
- `dev/LESSONS.md` P-m, P-q, P-t, P-c, R-36, R-38, read WHOLE. **P-q is at
  `dev/LESSONS.md:2633` and the gate names it.**
- `_build/gch-compression-audit.md`, for what is known removable and why it
  does not help the ratio.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature prices a spelling.** Say so in one line and spend
nothing. Return a **LITERATURE USED** section saying that.

## SCOPE (read)

`_build/lj-1.61-report.md` sections 4 and 7 FIRST, then the placed
`WitnessAgree` at `src/L/Condensation.lagda.md:6151-6195`, then the placed
`Lift12Back`/`Lift12Out`, then `dev/LESSONS.md:2633` for P-q.

## SCOPE (write)

`src/L/Condensation.lagda.md`, `src/L/BoundedSubset.lagda.md`, and
`src/ProbeLJ162*.agda`. Your report is `_build/lj-1.62-report.md`. **No other
master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **D-1.** The probe doctrine; the abort criterion is fixed above.
- **P-i.** The conversion-explosion playbook: select the cure by its decision
  tree, not by trial.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-q, P-t, P-u, P-v** as above, each with its action.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **A heap exhaustion is a WALL with its seconds.**
- **C-22.** Write the deliverable incrementally, deleting each placeholder as
  you fill it.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-8, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **The tree carries uncommitted work that
  is not in HEAD; do not discard it.**
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours. Report the load
  average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.62-report.md` incrementally, skeleton first.

**Lead with the gate's aggregate verdict after your best spelling, quoted.**
Then the two spellings side by side: lines, seconds, marginal rate and the
profile split between named definitions and `Miscellaneous`. Then what you
tried that did not work, with its number. Then whether `levelIn` and `cover`
are discharged. **Mark every negative MEASURED or INFERRED.** Then the DD4
trade if there is one, and **the convergence answer.**
