# LJ-1.101: close the cardκ type gap, then price sq for every infinite ordinal

tier: codex (default)

## GOAL

**Turn a value supplied to a COPY of the type into a value supplied to the
type**, and then price the new blocker, which is narrower than the return
that found it said.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`7dec213` except `dev/PLAN.md`. HEAD is green. **A sibling agent holds the
other Agda slot.**

## WHAT `[LJ-1.94]` DELIVERED, and I verified the decisive parts

**`cardκ` receives a value.** `SiteAt.cardκ` at `src/ProbeLJ194A.agda:1196`,
with `κ = sett WO ot` the ambient Hartogs set. **The whole probe is GREEN**,
1058 non-blank lines, 27 s cold, one process at the C-12 cap. **I re-ran it:
exit 0.** That closes the blocker `[LJ-1.90]` found and `[LJ-1.91]` priced.
No choice anywhere; LEM only in the tree's standing form.

**But the probe states `IsCardinal` LOCALLY**, at
`src/ProbeLJ194A.agda:73-74`, with its own `_↪_` at `:67-68`, to avoid
importing the heavy consumer master. The comment says so honestly. **The
probe does open `hPropStructure 𝒮ᵥ` at `:66`, the same structure the master
opens at `src/L/BoundedSubset.lagda.md:56`, so the types should agree.**

**Should is not typechecked.** C-38: a hypothesis is discharged when
something SUPPLIES it. **A value at a copy of the type is one step short,
and this phase has lost work to exactly that distance four times.**

## STEP 1, MANDATORY: apply the term at the MASTER's type

Write a small probe that:

- imports `L.BoundedSubset`'s own `IsCardinal`
  (`src/L/BoundedSubset.lagda.md:1045-1046`) and its `↪`;
- imports `src/ProbeLJ194A.agda`'s `Hartogs` or `SiteAt`;
- **applies `cardκ` at the master's `IsCardinal` and typechecks.**

**Report GREEN with the term at `file:line`, or the mismatch.** If the two
`↪` definitions differ, **say exactly how**, and whether a transport closes
it or the difference is real.

**Report the seconds. The consumer master is heavy, so the import may cost
100 s or more. That is a measurement worth having and it is the first time
anything has paid it for this term.**

## STEP 2: price `sq`, and the return understated the tree

`[LJ-1.94]` reports the next blocker as `Devlin55`'s two hypotheses
(`src/L/BoundedSubset.lagda.md:1361-1367`):

```agda
(sq : (α : S) → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    → Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ] ((x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y))
(absorbs-subset : (α x : S) → ((z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
                → ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
```

It calls both "no instance in the tree", MEASURED by reading. **The `sq`
half of that is too strong and I checked it myself.** The tree delivers

```agda
via-col-square : (α : S) → Init α → sq α       -- src/L/Ordinal/SquareLaw.lagda.md:960
```

and `Init α` (`:692-698`) is: `IsOrd α`, `ω ∈ α`, closure under successor,
and **a cardinality clause**, that no injection `⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫`
exists for an infinite ordinal `β ∈ α`.

**So `sq` is not missing. What is missing is `Init α` for the ARBITRARY
infinite `α` that `Devlin55` quantifies over.**

Answer these, with evidence:

1. **How far does `[LJ-1.94]`'s own machinery reach `Init`?** It built
   `InitialSegment` (280 lines), `ordκ`, `cardκ` and a reverse collapse.
   **Does `Init κ` follow for the Hartogs `κ`?** The cardinality clause is
   close to `IsCardinal` but not the same shape: `IsCardinal` forbids an
   injection into `⟪ δ ⟫`, `Init` forbids one into `⟪ β ⟫ × ⟪ β ⟫`.
   **Say whether one gives the other and what it costs.**
2. **What is the route from `Init` at the cardinals to `sq` at EVERY
   infinite ordinal?** The standard step is that every infinite ordinal
   injects into an initial one. **Say whether that is choice-free here, and
   price it.**
3. **Price `absorbs-subset` separately.** It is about `Lset`, not about
   ordinals, so it is different content.

**Give ONE best-effort figure for each, with its basis named, and name the
widest unmeasured term.** DD8.

## THE ABORT CRITERION, fixed in advance per D-1

- **Step 1 goes green**: report it, then do step 2 as far as budget allows.
  **Step 1 alone is a good return.**
- **Step 1 does not typecheck**: STOP and report the mismatch exactly. **A
  type mismatch here would mean the phase's biggest positive is narrower
  than it reads, and that is worth more than step 2.**
- **Anything walls**: STOP, report the wall with its seconds. **The consumer
  master is heavy; a wall on its import is a real measurement, not a
  failure.**

**Work in `src/ProbeLJ1101*.agda`. Do not touch any master.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken `IsCardinal`, `sq` or `absorbs-subset`.** The consumer's
  statements are fixed.
- **Do not re-state a type to make a term fit.** That is the defect step 1
  exists to remove, not to repeat.
- **Do not build the square-law chapter.** Step 2 is a pricing task.
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and counts from the source, never from a report.**
  **`[LJ-1.94]` said `sq` has no instance in the tree; `via-col-square` at
  `SquareLaw.lagda.md:960` is one. Check everything you quote.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**`[LJ-1.94]` measured its whole chain generic: no tower object in any type
of its mathematics.** Say whether step 2's content keeps that, since the
square law is about ordinals and injections and should be the most shared
block of the wing.

## ARCHIVE (DD18)

- **`_build/lj-1.94-report.md`**, read WHOLE, and **`src/ProbeLJ194A.agda`**.
  The Hartogs build, the site table, and the local `IsCardinal`.
- **`src/L/Ordinal/SquareLaw.lagda.md:692-698` and `:938-964`**, read.
  **`Init` and `via-col-square`. This is the delivered content the return
  missed.**
- `src/L/BoundedSubset.lagda.md:1040-1050`, `:1361-1370`, `:1396-1402`.
- `src/L/StageCardinal.lagda.md`, which also takes `sq` at `:15`.
- `_build/lj-1.92-report.md` and `src/ProbeLJ192A.agda`, the order-type
  block `[LJ-1.94]` imports.
- `_build/lj-1.91-report.md`, the route and its five steps.
- `dev/LESSONS.md` **C-38 as extended**, C-35, C-36, D-8, D-30, P-l, read
  WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Devlin uses the square law at 5.5.** Say in two lines whether he proves it
or takes it from earlier, from `dev/literature/devlin-II5.md`. Spend little.

## SCOPE (read)

`src/ProbeLJ194A.agda:60-80` and `:1180-1240` FIRST, then
`src/L/BoundedSubset.lagda.md:1040-1050` and `:1361-1370`, then
`src/L/Ordinal/SquareLaw.lagda.md:692-698` and `:938-964`.

## SCOPE (write)

`src/ProbeLJ1101*.agda` only. Your report is `_build/lj-1.101-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it. **Step 1 is the difference between supplying the type and supplying a
  copy of it.**
- **C-35.** A block with no consumer is UNTESTED.
- **C-36.** Write the term you could not write.
- **D-8.** One best-effort figure with its basis, and the widest unmeasured
  term.
- **D-30.** Price what the CONSUMER needs.
- **P-l.** A price from a comparable elsewhere is a hypothesis.
- **P-h, P-i, P-k, P-m, P-n, P-o, P-q, P-t, P-u, P-v, P-w** as the bundle
  gives them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally. **`[LJ-1.94]` left its
  report unchanged for over an hour while it worked. Do not do that.**
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-10, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.101-report.md` incrementally, skeleton first.

**Lead with whether `cardκ` typechecks at the MASTER's `IsCardinal`**, with
the term at `file:line` and its seconds, in the word YES or NO. Then step
2's three answers with their prices and bases. Then the widest unmeasured
term. **Mark every negative MEASURED or INFERRED.** Then the DD4 answer.
Confirm no master was touched.
