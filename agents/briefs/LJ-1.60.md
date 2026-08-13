# LJ-1.60: build Lift12Out, then place the rest of the leaf chain

tier: codex (default)

## GOAL

`[LJ-1.59]` measured a price wall and named its cure without building it.
**Build the cure, then place the chain, then take `levelIn` and `cover`.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`e7c8f99`**. There are no working-tree edits.

## THE WALL, MEASURED

The `out` (machine to story) direction of the twelve-row walk **typechecks**
in the master. It is not a proof problem. It is a price:

| | lines | marginal rate |
|---|---:|---:|
| the walk `back`, at the `Lift12Back` kit spelling | 387 | **0.01765** |
| the walk `out`, hand-written `o1..o11` chain | 732 | **0.0788** |

At the hand-written spelling the file measures 0.01584 whole-file, **over
DD24's live bar of 0.012716**, so `[LJ-1.59]` reverted it. **I confirmed the
revert by counting in-fence lines: 5,355 in the tree against 5,027 before.**

**The cause is named and it is the same one P-t already cured once.** The
forward direction is a hand-written disjunction chain: each helper states a
concrete partial tree, and the elaborator normalizes it per helper. The
`back` direction had exactly that shape and the `Lift12Back` kit removed it,
measured at 4.28x.

## THE CURE TO BUILD

**`Lift12Out`, the mirror of `Lift12Back`**: state the forward twelve-row
assembly as a **generic lift kit at abstract propositions**, so each full
formula tree normalizes once per statement instead of once per helper.

`Lift12Back` is placed in `src/L/Condensation.lagda.md` and is your model.

**`[LJ-1.59]` classed this cure INFERRED, from the measured back-direction
analogue. It is a hypothesis, not a price** (P-l: a measured cure does not
transfer by analogy; re-measure at its own site). **Measure it.**

## THE ABORT CRITERION, fixed in advance per D-1

Build `Lift12Out`, place the forward walk with it, and measure the whole
file:

- **GO**: whole-file rate **at or under 0.012716**. Then place the rest of
  the chain, measuring after each step, and stop the moment a step would
  cross.
- **NO-GO**: still over. **Then STOP and report the measured price.** Do not
  spend the rest of the budget pushing. A measured NO-GO with a number is a
  full deliverable and it is what the owner needs to rule on.

**If it lands between, say so with the number rather than rounding to a
verdict.**

## THEN THE REST OF THE CHAIN

Once the walk's `out` exists, these are ports of green probe content, both
directions, priced by `[LJ-1.59]`'s measured classes:

- `ShapedAgree`, `WitnessAgree` (`ProbeLJ157A` sections 4 to 5)
- `KeyAgree`, `DefinesAgree` (`ProbeLJ154A`)
- the `TwelveAgree` composition (`ProbeLJ155B`)
- `SatGraphAgree` (`ProbeLJ156A` section 7)
- `LeafAgree` (`ProbeLJ157A` section 5)

**Measure the whole file after each and stop at the bar.** A partial
placement with an honest ledger is a full deliverable.

## THEN THE ACTUAL GOAL

`levelIn` and `cover` (`src/L/BoundedSubset.lagda.md:598-599`) have survived
**eight dispatches**. The post-leaf chain is `[LJ-1.57]` section 8's five
terms, restated in `[LJ-1.59]` section 2.

**Say in the ledger exactly where you stopped.**

## SOMETHING YOU MUST NOT DELETE

**`src/ProbeLJ157A.agda` holds the machine to story proofs.** It is untracked
and a probe is never committed. **Do not delete it, do not overwrite it, and
do not let a cleanup take it.** Copy content forward; never move it.

## THE THRESHOLD, and the margin is thin

DD24's live bar is **0.012716**. **Do not use 0.013193.**

`L.Condensation` at HEAD is **5,355 in-fence lines at 0.01239 whole-file**
(`[LJ-1.59]`, three cold runs). **The margin is 0.0003 s per line.**

**Re-measure the baseline yourself, in your own session, before you compare
anything to it.** `[LJ-1.58]` measured 53.58 s and `[LJ-1.59]` measured
62.60 s at overlapping states; **like for like at 5,027 lines the two agree
to 3.6 percent**, and `[LJ-1.59]` mis-attributed that gap to machine load by
comparing against a baseline at a different line count. **Do not repeat
that: compare only figures at the same line count, from your own session.**

**Check the machine load before you measure and report it.** If the load
average is above 2, say so beside every absolute figure.

Report the marginal rate, the whole-file rate and the cone separately, each
from three cold runs in ONE caliber with the spread.

## THE LAWS, each with the ACTION it prescribes (C-37)

- **P-t.** State an assembly as a telescope at abstract propositions, not as
  hand-written partial trees. **This is the whole cure.**
- **P-l.** A measured cure does not transfer by analogy. **Re-measure at the
  new site**, which is why `Lift12Out` is a hypothesis until you price it.
- **P-m.** Instantiation is the expensive class. Say which class each block
  you place is in.
- **P-v.** Give a proof a NAME and pass the name.
- **C-34. Build the cure or report the wall.** `[LJ-1.59]` reported the wall
  and named the cure; **this dispatch is the cure.**
- **C-36.** A failed substitution is not a proof of impossibility. **Write
  the term you could not write.** You may strengthen; you may not weaken.

## WHAT YOU MUST NOT DO

- **You may not weaken a statement to make it cheap**, and you may not narrow
  a direction again. `[LJ-1.58]` narrowed to one direction and `[LJ-1.59]`
  found the other one is owed. **Both directions are now known to be needed.**
- **Do not touch anything under `src/L/Coding/`.** If the machine looks
  wrong, STOP and report it.
- All masters carry ZERO placement of `absFo` or a placed `Δ₀`. **If you need
  one, STOP and report it.**

## WHAT IS SETTLED

- `fin-inj` and `Mext` are DISCHARGED. `sq` has a master whose parameter
  survives on a reshaping that is NOT your task.
- The whole leaf chain is PROVED, in both directions, in the probes. **This
  is a placement and pricing question, not a re-proof.** If you find yourself
  re-proving a piece, stop and say which.
- **Δ₀ IS the target.** Delivered `Σ₁`'s only base is `σ-Δ₀`.
- The direction question is SETTLED: both directions are needed
  (`[LJ-1.59]` section 0). **Do not re-open it.**

## SOMETHING YOU WILL SEE AND MUST NOT TOUCH

The superseded **Row layer** (`RowTransfer`, `RowDecode`, eleven `*Row`
modules, five `*Decode` kits), about 613 lines. **The compression patch is
NOT your task, and I measured that it would RAISE the ratio, not lower it.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.** This has produced something on each of the last four dispatches,
including the wall this brief exists to cure.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

Every placement so far kept the template shape: no placed type mentions a
concrete carrier. **Keep that and say so.** If `Lift12Out` needs a
tower-specific spelling, name the trade before you take it.

## ARCHIVE (DD18)

- **`_build/lj-1.59-report.md`**, read WHOLE. Sections 0, 1.4 and 2 are the
  direction answer, the measured wall and the remaining chain.
- **`_build/lj-1.58-report.md`** section 2, the `Lift12Back` spelling that
  bought 4.28x. **This is your model for the mirror.**
- **`src/ProbeLJ157A.agda`**, read WHOLE. Your source, and it must survive.
- `src/ProbeLJ156A.agda`, `ProbeLJ155B.agda`, `ProbeLJ154A.agda`, the rest
  of the content to port.
- `src/ProbeLJ152A.agda`, `ProbeLJ152B.agda`, the pinned consumers.
- `_build/lj-1.52-report.md` and `_build/lj-1.51-report.md` for what
  `levelIn` and `cover` each still need, written as terms.
- `archive/rud-route/` for SHAPE only; `[LJ-1.11]` showed its condensation
  target is classically FALSE.
- `dev/LESSONS.md` is NOT archived and still binds.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature prices a placement.** `[LJ-1.59]` already read
Devlin Step C and banked the answer: the elementarity step transfers the
bounded statement, and the production side is a tree fact, not a literature
fact. **Say so in one line and spend nothing.**

Return a **LITERATURE USED** section saying that.

## SCOPE (read)

`_build/lj-1.58-report.md` section 2 FIRST, then the placed `Lift12Back` in
`src/L/Condensation.lagda.md`, then `_build/lj-1.59-report.md` section 1.4,
then `src/ProbeLJ157A.agda` sections 1 to 3.

## SCOPE (write)

`src/L/Condensation.lagda.md`, `src/L/BoundedSubset.lagda.md`, and
`src/ProbeLJ160*.agda`. Your report is `_build/lj-1.60-report.md`. **No other
master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-t, P-u, P-v** as above, each with its action.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **A heap exhaustion is a WALL with its seconds.**
- **C-22.** Write the deliverable incrementally. **`[LJ-1.59]`'s report ended
  with a duplicated unfilled skeleton; delete yours as you fill it.**
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-1, D-8, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **The tree is clean; keep your work
  visible in it.**
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours. Confirm the load
  before you measure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.60-report.md` incrementally, skeleton first, and **delete
each placeholder as you fill it.**

**Lead with the verdict: GO or NO-GO, with the measured whole-file rate after
`Lift12Out`.** Then what else you placed, with the rate after each. Then
whether `levelIn` and `cover` are discharged, and for anything unbuilt **the
term you could not write**. **Mark every negative MEASURED or INFERRED.**
Then the rates with spreads in one caliber and the load average, the DD4
answer, and **the convergence answer.**
