# LJ-1.78: make the closure facts conditional, on ONE row, and see if the proof survives

tier: codex (default)

## GOAL

**One row, one question.** The closure hypotheses are uninhabitable because
they quantify over arbitrary sets. Make them conditional on ONE row's
module, and find out **whether that row's proof still goes through**.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`b540478`**. HEAD is green.

## THE DEFECT, machine-checked

`KFacts` (`src/L/Condensation.lagda.md:5675-5708`) has no inhabitant.
`[LJ-1.77]` proved it in one step (`src/ProbeLJ177A.agda:75-78`, green,
2.47 s):

```agda
arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst v ∈ fst (lookup K γ) ⟩
```

Every set belongs to its own singleton, so this says every set belongs to
`K`, including `K`, and `∈-irrefl` refutes it.

The same shape, with no premise at all:

```agda
innerK     : (k : ℕ) (a : S)   → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup K γ) ⟩
innerPairK : (k : ℕ) (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup K γ) ⟩
pairK      : (a b : S)         → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩
```

**`carrierK` is SOUND** and is the model to copy: its premise ties `v` to a
slot, `(v : S) → ⟨ fst v ∈ fst (lookup A γ) ⟩ → ⟨ fst v ∈ fst (lookup K γ) ⟩`.

## THE REPAIR, and it is what a Skolem hull actually gives

**A closure hypothesis about a bounding set must be CONDITIONAL.** The
intended mathematics is that `K` is closed under the operations, for
arguments already in `K`:

```agda
pairK  : (a b : S) → ⟨ fst a ∈ fst K' ⟩ → ⟨ fst b ∈ fst K' ⟩
                   → ⟨ fst (prʟ a b) ∈ fst K' ⟩
innerK : (k : ℕ) (a : S) → ⟨ fst a ∈ fst K' ⟩
                   → ⟨ fst (prʟ (numeralL k) a) ∈ fst K' ⟩
```

and `arityK` bound to a specific slot rather than to any `N`, the way
`carrierK` is bound to the `A` slot.

**You choose the exact conditional forms and you justify each one.** The test
of a form is not that it typechecks; it is that the row proof can still use
it.

## THE QUESTION THIS DISPATCH ANSWERS

**Repair the facts for ONE row module and re-check that row's proof.**

Take **`MemAgree`** (`src/L/Condensation.lagda.md:4117`). It takes `innerK`
(`:4120`) and `pairK` (`:4121`) directly, and it is the row `TwelveAgree`'s
`mem-out`/`mem-back` come from.

- **If the row proof still goes through**: the repair is mechanical across
  the band, and you have shown it on the hardest available example. Report
  the diff shape and STOP.
- **If it does not**: the row proof was USING the falsity. **That is the more
  important answer.** Write the term you could not write, name the point
  where the proof needs a pair whose components it cannot place in `K`, and
  STOP.

**Do not repair the other rows. Do not touch `KFacts` itself yet.** One row
decides whether the repair is mechanical or mathematical.

## THE ABORT CRITERION, fixed in advance per D-1

- **`MemAgree` re-checks green with conditional facts**: report it at
  `file:line`, with the seconds, and STOP.
- **It does not**: STOP and write the term you could not write.

**Either way this dispatch ends after one row.** Do not touch
`SatGraphAgree`, `LeafAgree`, the three new masters, `levelIn` or `cover`.

**Work in `src/ProbeLJ178*.agda` if you can.** If you must edit
`src/L/Condensation.lagda.md`, **revert it before you finish and say the tree
is byte-identical to your start.** `[LJ-1.72]` left a master non-compiling
and it cost a revert.

## WHAT YOU MUST NOT DO

- **Do not weaken the row's CONCLUSION to make a hypothesis fit.** The
  conclusion is the agreement; only the hypotheses change. **Weakening the
  conclusion is the defect, not the repair.**
- **Do not make a hypothesis conditional on something that cannot be
  supplied either.** If the premise you add is itself unsatisfiable, you have
  moved the defect. **Say for each new premise where a real consumer would
  get it.**
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- Name probes `src/Probe*.agda`, never `.lagda.md`.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

D-29 says a shared layer propagates a fix and a defect at the same rate, and
this defect is the proof. **Say whether the conditional form is still generic
in the slots**, so the J tower inherits the repair rather than the defect.

## ARCHIVE (DD18)

- **`_build/lj-1.77-report.md`**, read WHOLE, and **`src/ProbeLJ177A.agda`**.
  The machine-checked refutation and the blast radius list.
- **`_build/diag-twelve-row-math.md`** section 4, read WHOLE. The review that
  found it, with its term recipes. **Its section 3 says `TwelveAgree` is the
  right theorem; that is not in question here.**
- `_build/lj-1.62-report.md` sections 2 and 3, where `KFacts` was introduced.
- `src/V/Hierarchy.lagda.md:130-160`, `regularityV` and `∈-irrefl`.
- `dev/LESSONS.md` **C-38 as extended today**, C-35, D-29, D-30, read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Devlin's hull closure is the mathematics your conditional forms should
match.** `_build/literature/dev2.txt:1372-1385` and
`dev/literature/devlin-II5.md` Step C. **Say in one line whether the
conditional form is what the hull gives.** Spend little.

## SCOPE (read)

`src/L/Condensation.lagda.md:5675-5708` (`KFacts`) FIRST, then `:4117-4210`
(`MemAgree`), then `src/ProbeLJ177A.agda`.

## SCOPE (write)

`src/ProbeLJ178*.agda`, and `src/L/Condensation.lagda.md` **only if you
revert it before finishing**. Your report is `_build/lj-1.78-report.md`.

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended today.** A hypothesis is discharged when something
  SUPPLIES it, and a closure hypothesis over arbitrary sets is refuted by
  regularity.
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
- Typecheck what you touch. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed**
  and say the master count.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours. Report the load
  average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.78-report.md` incrementally, skeleton first.

**Lead with whether `MemAgree` survives conditional facts**, at `file:line`,
with its seconds. Then each conditional form you chose and where a real
consumer supplies its premise. Then, if the proof broke, **the term you could
not write and the point where it needs a pair it cannot place in `K`.**
**Mark every negative MEASURED or INFERRED.** Then the DD4 answer under D-29.
Confirm the tree is byte-identical to your start.
