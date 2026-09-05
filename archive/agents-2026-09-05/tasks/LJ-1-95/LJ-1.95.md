# LJ-1.95: refute tmKeyK, or show it inhabitable

tier: codex (default)

## GOAL

**Decide one hypothesis by machine.** `[LJ-1.93]` reported that 39 of the
composer's 69 hypotheses have no supplier. **Reading its list, I believe at
least one of them is not merely unsuppliable but FALSE. That is a different
and much worse finding, and it must be measured, not inferred.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`a1f0e95`** except `dev/PLAN.md`. HEAD is green. **A sibling agent holds the
other Agda slot.**

## THE HYPOTHESIS, quoted from the source

`src/L/Condensation/TwelveAgree.lagda.md:96`:

```agda
(tmKeyK : (k : S) → ⟨ fst k ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
```

**It has no premise.** It says every `k` in `S` has its underlying set in the
`K` slot. `S` is the L-set structure here (`open hPropStructure 𝒮ʟ`, near
`:41`).

**My reading, which is INFERRED and sets no verdict:** a single set that
contains the underlying set of every L-set would contain its own, so the
usual foundation argument applies and the hypothesis is refutable.

**A second candidate, same shape**, `src/L/Condensation/TwelveAgree.lagda.md:86-88`:

```agda
(valK : (k : ℕ) (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
        → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
        → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
```

**`yc` is bound by nothing.** The premises constrain `c`, `ar`, `a` and `b`,
never `yc`, so the conclusion is universal in `yc` once any code exists.

## WHY THIS MATTERS MORE THAN A MISSING SUPPLIER

**All three split masters carry `tmKeyK`.** The composer passes it into both
sixes (`src/L/Condensation/TwelveAgree.lagda.md:253` and `:264`). **If it is
refutable, `LowerAgree`, `UpperAgree` and `TwelveAgree` are all vacuous**, in
the same way `TwelveAgree`'s old `tagEq` was, which `[LJ-1.71]` refuted and
which I had already committed as delivered.

**This is the fifth time this phase that a hypothesis may be false rather
than merely open. The four before it were all found by a consumer or a
refutation, never by a shape audit.**

## WHAT TO DO

**For `tmKeyK`, and then for `valK`:**

1. **Try to derive `Empty.⊥`** from the hypothesis alone, at the composer's
   own frame. Use the tree's foundation or `∈-induction`. `[LJ-1.77]` did
   exactly this for the old `KFacts` and its probe is the shape to copy.
2. **If ⊥ follows: the hypothesis is REFUTED.** Report the term at
   `file:line` with its seconds. **That is the finding and it is decisive.**
3. **If ⊥ does not follow, do not conclude the hypothesis is fine.** Say what
   blocked the refutation, and whether the block is a missing lemma or a real
   obstacle.
4. **Then scan the other 37 for the same shape**: a conclusion universally
   quantified over a variable that no premise constrains. **List them at
   `file:line`. Do not try to refute them all; name them.**

## THE ABORT CRITERION, fixed in advance per D-1

- **`tmKeyK` is refuted**: report the term and STOP. **Do not repair
  anything.** The repair is a separate dispatch and it needs this one
  audited first.
- **`tmKeyK` survives the attempt**: say what blocked it, then try `valK`,
  then STOP.
- **Anything walls**: STOP, report the wall with its seconds.

**Work in `src/ProbeLJ195*.agda`.** **Do not touch any master.** This
dispatch writes no repair.

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not repair, weaken or delete any hypothesis.** Measure only.
- **Do not accept `[LJ-1.93]`'s table as evidence for this question.** It
  measured that nothing SUPPLIES these facts. **Unsuppliable and false are
  different findings and this dispatch separates them.**
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers from the source, never from a report.** `[LJ-1.93]`
  cited the master import at `:31`; it is at `:30`. Small, but check
  everything you quote.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.** **My reading above is INFERRED. This dispatch exists to replace it
with a measurement, in either direction.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**A refutation is not shared code, so answer this one plainly:** say whether
the defect, if real, is in content the J tower would also inherit.

## ARCHIVE (DD18)

- **`_build/lj-1.93-report.md`**, read WHOLE, and `src/ProbeLJ193B.agda` and
  `src/ProbeLJ193C.agda`. The 39-fact table and the two machine-checked
  mismatches.
- **`_build/lj-1.77-report.md`**, read WHOLE. **It refuted the old `KFacts`
  and its probe is the shape to copy.**
- `_build/lj-1.71-report.md`, which refuted the old `tagEq`.
- `_build/lj-1.76-report.md`, the 69-fact frame and why it was chosen.
- `src/L/Condensation/TwelveAgree.lagda.md:45-243`, the whole frame.
- `dev/LESSONS.md` **C-38 as extended**, C-35, C-36, D-29, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** No source speaks to a hypothesis in our own
frame. Say so in one line.

## SCOPE (read)

`src/L/Condensation/TwelveAgree.lagda.md:45-243` FIRST, then
`_build/lj-1.77-report.md`, then the foundation or `∈-induction` the tree
delivers.

## SCOPE (write)

`src/ProbeLJ195*.agda` only. Your report is `_build/lj-1.95-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it. **A hypothesis that is FALSE is not open; it is a defect.**
- **C-35.** A block with no consumer is UNTESTED.
- **C-36.** Write the term you could not write.
- **D-29, D-26, D-10.**
- **D-1.** The probe doctrine: smallest decisive miniature, then throw away.
- **P-h, P-i, P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v, P-w** as the
  bundle gives them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-8, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.95-report.md` incrementally, skeleton first.

**Lead with whether `tmKeyK` is refuted**, with the term at `file:line` and
its seconds, in the word REFUTED or SURVIVED. Then the same for `valK`. Then
the list of the other hypotheses with the same shape, at `file:line`, named
and not refuted. **Mark every negative MEASURED or INFERRED.** Then the DD4
answer. Confirm no master was touched.
