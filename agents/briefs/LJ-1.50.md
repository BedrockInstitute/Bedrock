# LJ-1.50: the 150-second certificate transfer, and the one step with no price

tier: codex (default)

## GOAL

`[LJ-1.49]` landed both cures and priced the residue. **One number in that
residue decides whether the route is feasible**, and one step in it has no
price at all. Attack the number first; price the step second.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, plus the
uncommitted `src/L/BoundedSubset.lagda.md` and `src/L/Condensation.lagda.md`.

## THE NUMBER, and what is measured in it

`[LJ-1.49]` measured the **erase-to-Δ₀ certificate transfer at the concrete
`DefBodyB` leaf at 150.13 s**. The GCH side's whole seconds budget is 99.6 to
147.7 s. **So if that cost stands at the real site, one step exceeds the
budget.**

**Read the parts, because they are not all the same claim:**

- The count and the erasure are FAST: a 2.6 s probe. **MEASURED.**
- The statement-level connector is cheap: `embed (Cnt.erase Σ₂ refl)` at the
  hull checks in a 4.78 s probe. **MEASURED.**
- The certificate transfer at the CONCRETE leaf is 150.13 s. **MEASURED.**
- The full `LevelHood0.matrix` variant was **STOPPED after more than 2.5
  minutes.** **That is an interruption, not a wall**, and its "more than 150 s"
  is a lower bound from somebody stopping, not a measurement. **C-36: a stop is
  not a proof.**

## THE ACTION THE LAWS PRESCRIBE, stated as an action

**C-37 was admitted yesterday because my last brief stated a law as a
prohibition and hid its cure. Here is the action.**

**P-u: CERTIFY BEFORE YOU PLACE.** The move is to build the certificate at
VARIABLE SLOTS and instantiate ONCE at the end, so the elaborator never
normalizes a built tree at a concrete argument. The report itself says the cost
is "the instantiation-class cost", which is exactly the class that move
removes.

**This tree has beaten that class three times, each measured:**

| where | before | after |
|---|---:|---:|
| `[LJ-1.24]`, abstract the SOURCE | 29.1 s | 2.3 s |
| `[LJ-1.47]`, price what the consumer needs | 43.26 s | 7.94 s |
| `[LJ-1.45]`, one spelling at the leaves | 2,029 ms | 197 ms |

**And it has FAILED four times in five on transplants**
(`dev/LESSONS.md`, the transplant table). **So measure it; do not argue it.**
C-34: build the cure or report the wall that stopped you.

## THE SECOND TASK, once the number is settled

`[LJ-1.49]`'s uncertainty 2: **the adequacy's deepest step, the
collapse-of-the-level for `levelIn`, has NO price at all, because nothing in
the delivered tree measures it.**

**Price it.** If it is small, build it: `levelIn` is one of the two hypotheses
still standing between this master and the theorem.

**Do not start here.** If the 150 s stands, the price of `levelIn` does not
matter yet.

## WHAT IS SETTLED, so you do not re-open it

- **Both cures are landed and green**, and I verified them: `BoundedSubset` is
  976 in-fence lines at 10.55 s cold, `Condensation` is 4,632, both with ZERO
  placement and ZERO escape hatches, `check-fences` clean. `collapseCode` is
  deleted; only two comments naming it remain.
- **The surviving hypotheses are `levelIn`, `cover` and the new `Mext`.**
  `Mext` is provable from `hull-closed` and is priced at 120 to 250 lines;
  **that is not your task unless the first two go quickly.**
- **P-v's slot spelling is the file's own house style**
  (`src/L/Condensation.lagda.md:1111-1114`) and the twelve rows run it. **Do
  not introduce a second spelling.**
- **Δ₀ IS the target.** Delivered `Σ₁`'s only base is `σ-Δ₀`
  (`src/FOL/LevyHierarchy.lagda.md:73-75`).

## A CALIBER TRAP `[LJ-1.49]` FELL INTO AND FLAGGED

It measured with wall seconds from `scripts/check-timing.py` while its baselines
were user seconds, so its deltas are caliber-mixed and it said so. **Use ONE
caliber throughout, state which, and report at least three runs with the
spread.** The machine load was 4 to 6 during its runs.

## THE THRESHOLD

DD24's live bar is **0.012716**, from the AC baseline 0.011057 times the 1.15
tolerance. **Do not use 0.013193.** The GCH aggregate sits inside the
run-to-run band around the bar, so **there is no margin**.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker, so it is stated in every brief and answered in
every return.

**A certificate built at variable slots is template content; one built at a
concrete leaf is not.** So the cure, if it works, is also the DD4 move. Say what
the J tower inherits.

## ARCHIVE (DD18)

- **`_build/lj-1.49-report.md`**, the prices and the measured parts, read
  WHOLE. C-32 exists because a brief of mine named a section and hid the
  decisive probe.
- **`_build/lj-1.7-review.md`** and the probes `src/ProbeDD25G1.agda`, `G2`,
  `G3`, all green.
- `_build/lj-1.24-report.md` and `_build/lj-1.47-report.md` for the two cures
  of this class that worked.
- `archive/rud-route/` bears for SHAPE only; `[LJ-1.11]` showed its
  condensation target is classically FALSE.
- `dev/LESSONS.md` is NOT archived and still binds.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in `dev/literature/` bears.** This is an elaborator cost measurement
on this tree's own code; Devlin asserts absoluteness where this proves a
transfer. **Say so in one line and spend nothing.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## SCOPE (read)

`_build/lj-1.49-report.md` section 4 and its measurements FIRST, then
`src/L/BoundedSubset.lagda.md`'s `HullStage.Condense`, then the `DefBodyB` leaf
and `LevelHood0.matrix`.

## SCOPE (write)

`src/ProbeLJ150*.agda`, and `src/L/BoundedSubset.lagda.md` or
`src/L/Condensation.lagda.md` **only if a cure lands and you are placing it**.
Your report is `_build/lj-1.50-report.md`. **No other master. Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-t, P-u, P-v** as above, each with its action.
- **R-35.** State the membership at the SMALL index and climb.
- **R-38.** Seal at the birth site, and do NOT unseal.
- **R-40.** State a membership witness SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **A heap exhaustion is a WALL with its seconds; an interruption is
  not.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **Two masters are uncommitted.**
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.50-report.md` incrementally, skeleton first.

Lead with the verdict: what the certificate transfer costs at variable slots
against 150.13 s at the concrete leaf, with three runs and the spread in ONE
caliber. Then whether the full matrix finishes, and its real number or its wall
with the seconds. Then the price of the collapse-of-the-level step if you got
there. Then the DD4 answer and what you are not sure of.
