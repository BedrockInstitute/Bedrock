# LJ-1.79: guard the closure facts across the band

tier: codex (default)

## GOAL

`[LJ-1.78]` showed the repair is mechanical on one row. **Do it on the whole
band, and on `KFacts`.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`6990d65`**. HEAD is green.

## WHAT IS SETTLED, so you repair rather than investigate

**The defect, machine-checked** (`src/ProbeLJ177A.agda:75-78`): closure facts
quantified over arbitrary sets are refuted by regularity. `KFacts` has no
inhabitant.

**The repair, machine-checked on `MemAgree`** (`src/ProbeLJ178A.agda`, and I
re-ran it myself at 1.63 s user): guard each closure fact with the
memberships of the components its conclusion mentions.

```agda
innerK : (a b : S) → ⟨ a ∈ K ⟩ → ⟨ b ∈ K ⟩ → ⟨ prʟ (numeralL k) (prʟ a b) ∈ K ⟩
pairK  : (a b : S) → ⟨ a ∈ K ⟩ → ⟨ b ∈ K ⟩ → ⟨ prʟ a b ∈ K ⟩
```

**And the supply point already exists.** `MemAgree`'s only use of the facts
is one `BinaryShape.in'` call in `back`, and the witnesses come from the
row's own `codesK`, which concludes `ar ∈ K × a ∈ K × b ∈ K` and is already a
telescope parameter. **No new hypothesis was added.** The forward direction
never mentions the facts.

**`carrierK` is SOUND** and needs no change: its premise ties `v` to the `A`
slot.

## WHAT TO REPAIR

**All of it, in `src/L/Condensation.lagda.md`:**

1. **`KFacts`** (`:5675-5708`): guard `innerK`, `innerPairK`, `pairK`, and
   bind `arityK` to a slot the way `carrierK` is bound to `A`, rather than
   quantifying over any `N`. **`arityK` is the one whose right form you must
   argue**: `[LJ-1.77]` refuted it because `N` was universal. Say what slot
   it should be bound to and why the consumers can supply it.
2. **The twenty modules that take a suspect field type directly**, listed at
   `_build/lj-1.77-report.md` section 3b with their line numbers:
   `BotAgree`, `PropAgree`, `AndAgree`, `OrAgree`, `TopAgree`, `NegAgree`,
   `ForallAgree`, `ExistAgree`, `ClauseAgree`, `MemAgree`, `AllInAgree`,
   `ExInAgree`, `ImpAgree`, `EqAgree`, `UnShapeClosed`, `BinShapeClosed`,
   `BinFormAgree`, `UnFormAgree`, `BinFrameAgree`, `UnFrameAgree`.
3. **The six masters that take `KFacts`**: `ShapesAgree`, `ClosedAgree`,
   `ShapedAgree`, `WitnessAgree`, `SatGraphAgree`, `LeafAgree`.
4. **The three new masters** under `src/L/Condensation/`, which take the same
   facts.

**Each use site must supply its premises from facts the module already has.**
**If any site cannot, STOP there and report it**: that site is where the
proof was using the falsity, and it is a mathematical finding rather than a
mechanical one.

## THE ACCEPTANCE TEST

**C-38: a hypothesis is discharged when something SUPPLIES it.** So:

- **Every master you touch must re-check GREEN**, and you report each one's
  seconds.
- **Say for every guarded fact where its premises come from**, at
  `file:line`. **A guard whose premise nothing supplies has moved the defect,
  not fixed it.**
- **`src/ProbeLJ177A.agda`'s refutation must FAIL to apply** to the repaired
  `KFacts`. **Adapt that probe and report that it no longer typechecks**,
  which is the direct evidence the record is now inhabitable in principle.

**Do not claim `KFacts` is inhabited.** Showing the refutation no longer
applies is not the same as exhibiting an inhabitant, and I want that
distinction kept.

## THE ABORT CRITERION, fixed in advance per D-1

- **Everything re-checks green**: report the seconds per master, the supply
  points, and the refutation's failure. Then STOP. Do not wire anything, do
  not touch `levelIn` or `cover`.
- **A site cannot supply its premises**: **STOP at that site**, write the
  term you could not write, and leave every master you already repaired in a
  GREEN state.
- **Anything walls**: STOP, revert to green, report the wall with its
  seconds.

**Leave the tree GREEN whatever happens.** `[LJ-1.72]` left a master
non-compiling and it cost a revert; do not repeat it.

## WHAT YOU MUST NOT DO

- **Do not weaken any conclusion.** Only hypotheses change.
- **Do not add a hypothesis that is itself unsatisfiable.** That moves the
  defect. **Every new premise must name its supplier.**
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12. This file has walled at the cap
  before.
- Name probes `src/Probe*.agda`, never `.lagda.md`.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**D-29 says a shared layer propagates a fix and a defect at the same rate,
and this defect is its proof.** The J tower would have inherited the
uninhabitable facts at every site at once. **Say whether the guarded forms
are still generic in the slots**, so it inherits the repair the same way.

## ARCHIVE (DD18)

- **`_build/lj-1.78-report.md`**, read WHOLE, and **`src/ProbeLJ178A.agda`**.
  The guarded forms and the supply argument you are generalizing.
- **`_build/lj-1.77-report.md`**, read WHOLE, and `src/ProbeLJ177A.agda`.
  The refutation and the blast-radius list, which is your work list.
- `_build/diag-twelve-row-math.md` section 4, the review that found it.
- `_build/lj-1.62-report.md` sections 2 and 3, where `KFacts` was introduced.
- `dev/LESSONS.md` **C-38 as extended**, C-35, D-29, D-30, read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Devlin's hull closure is what the guarded forms should match**: a Skolem
hull is closed under the operations for arguments already in it.
`dev/literature/devlin-II5.md` Step C. **Say in one line that the guarded
form is what the hull gives.** Spend little.

## SCOPE (read)

`src/ProbeLJ178A.agda` FIRST, then `_build/lj-1.77-report.md` section 3, then
`src/L/Condensation.lagda.md:5675-5708`.

## SCOPE (write)

`src/L/Condensation.lagda.md`, the three masters under
`src/L/Condensation/`, and `src/ProbeLJ179*.agda`. Your report is
`_build/lj-1.79-report.md`. **No other master. Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended.** A closure hypothesis over arbitrary sets is refuted
  by regularity; a hypothesis is discharged when something SUPPLIES it.
- **C-35.** A block with no consumer is UNTESTED.
- **D-29.** A shared layer propagates a fix and a defect at the same rate.
- **D-30.** Price what the CONSUMER needs.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle gives them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35.** State the membership at the SMALL index and climb.
- **R-40.** State a membership witness SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-36, C-37.**
- **D-1, D-8, D-10, D-26.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck every master you touch and every consumer. Do NOT run
  `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed**
  and say the master count.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check` on every file you touch.
- DD23 freezes mathematical prose. Code and its own comments only.
- **Report the load average beside every absolute figure**, and say if the
  machine was not quiet.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.79-report.md` incrementally, skeleton first.

**Lead with how far you got: which modules are repaired and green, with
seconds.** Then every guarded fact and its supplier at `file:line`. Then that
`ProbeLJ177A`'s refutation no longer applies, and the distinction between
that and exhibiting an inhabitant. Then, for any site that could not supply
its premises, **the term you could not write**. **Mark every negative
MEASURED or INFERRED.** Then the DD4 answer under D-29.
