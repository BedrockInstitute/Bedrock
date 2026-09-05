# LJ-1.88: is the witness step circular, or does the theorem's own hypothesis supply it?

tier: codex (default)

## GOAL

**Settle the one INFERRED claim that decides the shape of the remaining
work.** Is the chain leaning on the theorem it proves, or is the appearance
already available from the theorem's own hypothesis?

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`8a7c40b`**. HEAD is green.

## WHAT IS SETTLED, machine-checked

`witK` does not follow from `w ⊆ AllCodes A` together with
`AllCodes A ∈ Lset lam`. Both premises bound the MEMBERS of `w`; the
conclusion needs `w` ITSELF in `Lset lam`, hence `w` DEFINABLE over a lower
stage. `src/ProbeLJ187B.agda` is red at exactly that step
(`defSet (Lset δ) ⊤̇ ≡ fst w`, `UnequalTerms`), and I re-ran it myself.

**The tree documents the gap in its own prose**
(`src/L/Axioms/Power.lagda.md:210-214`):

> It did not use condensation, and did not need to: the axiom asks for the
> constructible subsets to form a set, not for them to appear early.

**`witK` asks for them to appear early.**

## THE QUESTION, and it is the only one

**Devlin's 5.5 takes a hypothesis: `x ⊆ Lset α` and `x ∈ L`.** So `x` is
constructible and appears at SOME stage. The witness `w` is built from `x`:
`hasWitnessAt`'s subformula closure (`src/L/Coding/CodeSet.lagda.md:365-373`).

**So: can `w`'s appearance be obtained from `x`'s?**

1. **Read what the theorem's frame actually assumes about `x`**, at
   `file:line`, in `src/L/BoundedSubset.lagda.md`. Does it carry `x ∈ L`, a
   stage for `x`, or only `x ⊆ Lset α`?
2. **Is `w` obtainable from `x` by a construction that stays inside a
   stage?** The closure is built by separation over `AllCodes A`, and
   `[LJ-1.86]` showed `AllCodes A` has a stage. **A definable subset of a set
   that has a stage appears one level up. Does that route reach `w`?**
3. **If it does, the step is NOT circular** and `witK` should be replaced by
   the construction rather than assumed. Say what replaces it.
4. **If it does not**, say precisely what `w` needs that `x` does not give,
   and whether that is condensation itself.

**This is a reading and checking task. Do not redesign the layer.**

## THE ABORT CRITERION, fixed in advance per D-1

- **`w`'s appearance follows from `x`'s**: report the route at `file:line`,
  machine-check the decisive step if it is small, and STOP. **That would
  make the remaining work a wiring problem rather than a redesign, and it is
  the answer I most want checked rather than assumed.**
- **It does not follow**: STOP, say exactly what is missing, and whether it
  is condensation. **A clean negative here is what the owner needs to rule
  on the layer's design.**
- **Anything walls**: STOP, report the wall with its seconds.

**Work in `src/ProbeLJ188*.agda`.** If you touch a master it is GREEN when
you finish or you revert it.

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time. If a check does not return, KILL IT before you
start another, and report the wall with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken any statement, and do not redesign the layer.** This
  dispatch decides which of two shapes the remaining work has.
- **Do not assume a subset appears one level up.** The stages are the
  DEFINABLE power set, and that is the whole point of this question.
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.** This dispatch exists to move one inference of MINE to a verdict.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**If the route exists, say whether it is generic**, so the J tower's witness
appears the same way.

## ARCHIVE (DD18)

- **`_build/lj-1.87-report.md`**, read WHOLE, and `src/ProbeLJ187B.agda`.
  The red step and the definability gap.
- `_build/lj-1.86-report.md` and `src/ProbeLJ186A.agda`, the stage for
  `AllCodes A` and how it was obtained: by definability, not by rank.
- `_build/lj-1.85-report.md` and `src/ProbeLJ185B.agda`, the closure that is
  the real witness.
- **`src/L/Axioms/Power.lagda.md:16-22` and `:208-216`**, the tree's own
  statement of the gap. **Read both.**
- `src/L/Axioms/Separation.lagda.md`, `src/L/Stage.lagda.md`. **Read-only.**
- `dev/LESSONS.md` C-38 as extended, C-35, C-36, D-30, read WHOLE.
- `archive/rud-route/` for SHAPE only; `[LJ-1.11]` ruled its condensation
  target classically FALSE, so take no claim from it.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**This is the place it decides.** `dev/literature/devlin-II5.md` Step C and
`_build/literature/dev2.txt:1372-1385`. **Devlin's proof gets the witness
into a bounded stage somehow. Say in three lines how**, and whether that
route is available here. Return a **LITERATURE USED** section.

## SCOPE (read)

`src/L/Axioms/Power.lagda.md:208-216` FIRST, then
`src/L/BoundedSubset.lagda.md`'s theorem frame and what it assumes of `x`,
then `src/L/Coding/CodeSet.lagda.md:365-373`.

## SCOPE (write)

`src/ProbeLJ188*.agda`, and any master **only if you revert it before
finishing**. Your report is `_build/lj-1.88-report.md`. **Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it.
- **C-36.** Write the term you could not write.
- **C-35.** A block with no consumer is UNTESTED.
- **D-30.** Price what the CONSUMER needs.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle gives them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised, **kill a hung check before
  starting another.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-8, D-10, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck what you touch. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed**
  and say the master count.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.88-report.md` incrementally, skeleton first.

**Lead with whether `w`'s appearance follows from `x`'s**, at `file:line`.
Then, if it does, what replaces `witK`; if it does not, exactly what is
missing and whether it is condensation. **Mark every negative MEASURED or
INFERRED.** Then how Devlin bounds his witness. Then the DD4 answer. Confirm
every master is green or untouched.
