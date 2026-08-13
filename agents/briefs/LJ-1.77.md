# LJ-1.77: machine-check whether KFacts is uninhabitable

tier: codex (default)

## GOAL

**One probe, one question.** An adversarial review claims `KFacts` has no
inhabitant. If that is right, a large part of what is committed proves
nothing. **Machine-check it.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`fc99a58`**. HEAD is green.

## THE CLAIM

`KFacts` (`src/L/Condensation.lagda.md:2588`, a record) has these fields
among others:

```agda
innerK     : (k : ℕ) (a : S)   → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup K γ) ⟩
innerPairK : (k : ℕ) (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup K γ) ⟩
pairK      : (a b : S)         → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩
arityK     : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst v ∈ fst (lookup K γ) ⟩
```

**None of the first three has a hypothesis.** They assert that every pair of
arbitrary sets is a member of `K`.

**`arityK` looks conditional and is not.** It says: if `v` belongs to ANY
set `N`, then `v` belongs to `K`. Every `v` belongs to its own singleton, so
it asserts that EVERY set belongs to `K`, including `K`.

**My own refutation, which is what I want checked:**

```text
arityK ⁅K⁆ K (K ∈ ⁅K⁆)  :  K ∈ K
∈-irrefl K that                 :  ⊥
```

`∈-irrefl` is at `src/V/Hierarchy.lagda.md:155` and `regularityV` at `:139`.
The singleton is `⁅_⁆s` from
`Cubical.HITs.CumulativeHierarchy.Constructions`, which
`src/L/BoundedSubset.lagda.md` already imports.

**`carrierK` is NOT under suspicion**: `(v : S) → v ∈ A → v ∈ K` is
conditional on membership of `A`, which is an ordinary closure fact.

## WHAT TO BUILD

`src/ProbeLJ177A.agda`, as small as you can make it.

1. **Refute `arityK`**: from a value of `KFacts`'s `arityK` field type at any
   `K` and `γ`, derive `⊥`. **This is the decisive one because it is one
   step.**
2. **Refute `pairK`** the same way if you can: `pairK K K` gives
   `pr K K ∈ K`, and `pr a b` is Kuratowski, so `⁅K⁆ ∈ pr K K` and
   `K ∈ ⁅K⁆`. That is a three-cycle and needs well-foundedness rather than
   `∈-irrefl` alone. **If the cycle lemma is not delivered, say so and stop
   at `arityK`;** one machine-checked refutation settles the record.
3. **Then state whether `KFacts` as a whole is uninhabitable**, and say
   which fields you machine-checked and which you argued.

**Do not repair anything.** This dispatch establishes a fact.

## THE ABORT CRITERION, fixed in advance per D-1

- **The refutation typechecks**: report it at `file:line` and **STOP**. Then
  list, at `file:line`, every master and module that takes `KFacts` or one
  of the suspect field types as a parameter, so the blast radius is on
  record. **That list is the deliverable's second half.**
- **The refutation does NOT typecheck**: **STOP** and say exactly which step
  fails. That would mean the review is wrong and the record is sound, which
  is the more valuable answer and I would rather have it than be right.

**Either way this dispatch ends there.** Do not touch
`src/L/Condensation.lagda.md`, the new masters, `SatGraphAgree`,
`LeafAgree`, `levelIn` or `cover`.

## WHY THIS MATTERS, so you do not soften it

`[LJ-1.71]` found `TwelveAgree`'s `tagEq` uninhabitable and I had committed
it claiming the hypotheses were discharged. C-38 was admitted for exactly
that. **This claim is the same shape and wider**: `KFacts` is committed, it
was `[LJ-1.62]`'s measured minus-30-second win, and `SatGraphAgree`,
`LeafAgree` and the three new masters all take it.

**If it is uninhabitable, none of them can ever be instantiated**, and the
seconds this campaign has spent optimizing them priced a statement that must
change.

## WHAT YOU MUST NOT DO

- **Do not weaken or repair a statement.** Establish the fact.
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Name the probe `src/ProbeLJ177A.agda`**, not `.lagda.md`.
- **Do not raise the heap cap.** C-12.
- Leave the tree byte-identical to your start and say so.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict**, and this dispatch exists to move one inference to MEASURED.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return. **If `KFacts` is uninhabitable, say what the J
tower would have inherited**, since D-29 says a shared layer propagates a
defect at the same rate it propagates a fix.

## ARCHIVE (DD18)

- **`_build/diag-twelve-row-math.md`** section 4, read WHOLE. It is the
  review that made this claim, with its term recipes. **Check it; do not
  trust it.**
- `_build/lj-1.71-report.md` and `src/ProbeLJ171A.agda`, the `tagEq`
  refutation, which is the shape you are repeating.
- `_build/lj-1.62-report.md` sections 2 and 3, where `KFacts` was introduced
  and measured.
- `src/V/Hierarchy.lagda.md:130-160`, `regularityV` and `∈-irrefl`.
- `dev/LESSONS.md` C-38, C-35, D-29, read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature bears on this**; it is a fact about this tree's
own statements. Say so in one line and spend nothing.

## SCOPE (read)

`src/L/Condensation.lagda.md:2588-2640` (the `KFacts` record) FIRST, then
`src/V/Hierarchy.lagda.md:130-160`, then
`_build/diag-twelve-row-math.md` section 4.

## SCOPE (write)

`src/ProbeLJ177A.agda` only. Your report is `_build/lj-1.77-report.md`.

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **C-38.** A hypothesis is discharged when something SUPPLIES it.
- **C-35.** A block with no consumer is UNTESTED.
- **D-29.** A shared layer propagates a fix and a defect at the same rate.
- **D-1.** The probe doctrine.
- **P-h, P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle gives
  them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35.** State the membership at the SMALL index and climb.
- **R-40.** State a membership witness SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-36, C-37.**
- **D-8, D-10, D-26, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`. You need not run `check-ratio`.
- **Run `scripts/check-fences.py --check` before you report anything closed**
  and say the master count.
- Run `scripts/lint-agda.py --check` on the probe.
- DD23 freezes mathematical prose.
- **The machine is quiet and both Agda slots are yours. Report the load
  average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.77-report.md` incrementally, skeleton first.

**Lead with whether the refutation typechecks**, at `file:line`, with its
seconds. Then which fields are machine-checked uninhabitable and which are
argued. Then the blast radius: every master and module taking `KFacts` or a
suspect field, at `file:line`. **Mark every negative MEASURED or INFERRED.**
Then the DD4 answer under D-29. Confirm the tree is byte-identical to your
start.
