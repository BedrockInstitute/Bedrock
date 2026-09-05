# LJ-1.91: gate the cardinal chapter, by pricing ONE cardinal

tier: codex (default)

## GOAL

**Price the cheapest route to a single `IsCardinal` instance.** That is the
whole remaining obstruction, and DD8 says gate a block before funding it.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`cc516ea`**. HEAD is green.

## WHAT IS SETTLED, machine-checked

`[LJ-1.90]` instantiated `BoundedSubsetAt` for the first time. **Every
hypothesis of the layer takes a value at a concrete site**, including the
`AllCodes A ∈ Lset lam` that `[LJ-1.89]` introduced. I re-ran that probe
myself, green at 0.96 s.

**The first hypothesis nothing can supply is `cardκ : IsCardinal κ`**
(`src/L/BoundedSubset.lagda.md:1397`).

**I checked how deep the gap is.** `IsCardinal` is defined at
`src/L/BoundedSubset.lagda.md:1045-1046`:

```agda
IsCardinal κ = (δ : S) → ⟨ δ ∈ˢ κ ⟩ → (⟪ κ ⟫ ↪ ⟪ δ ⟫ → Empty.⊥)
```

and it appears **exactly twice in `src/`**: its definition and that
hypothesis. **Nothing in the tree proves any set is a cardinal.**

`[LJ-1.90]`'s probe chose `κ = sucV ω`, which is `ω+1` and is not a cardinal
at all, since `ω+1` injects into `ω`. So its stop had a shallow cause on top
of the real one.

## THE QUESTION

**What is the cheapest route to ONE `κ` with `IsCardinal κ` and `κ ∉ ω`?**

The consumer needs an uncountable cardinal above the carrier's ordinal.

1. **Survey what the tree already has** toward it, at `file:line`:
   injections, Cantor, Schröder-Bernstein, Hartogs, the ordinal machinery,
   anything in `src/L/StageCardinal.lagda.md` or `src/L/Ordinal/`.
   **An earlier survey put the missing chapter at about seven hundred lines
   with no successor cardinal, no Cantor and no Schröder-Bernstein. Check
   that rather than repeat it.**
2. **Name the cheapest construction.** Hartogs' number is the usual answer
   and it needs no choice. Say what it needs here.
3. **Price it.** DD8: **one best-effort figure that names its basis**, in
   in-fence lines, and say whether the basis is a delivered comparable, a
   probe, or a survey.
4. **Name the widest unmeasured term in that price**, and the probe that
   would measure it. That is DD8's other half and it is the part briefs
   skip.

**This is a recon and pricing task. Do not build the chapter.**

## THE ABORT CRITERION, fixed in advance per D-1

- **A route exists and you can price it**: report the route, the figure, its
  basis and the widest unmeasured term, then STOP.
- **No route exists without choice or without a principle the tree lacks**:
  STOP and say which principle. **That would be a route-level finding and it
  goes to the owner.**
- **Anything walls**: STOP, report the wall with its seconds.

**You may build a small probe** in `src/ProbeLJ191*.agda` to price a step, but
**do not build the chapter**. If you touch a master it is GREEN when you
finish or you revert it.

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time. If a check does not return, KILL IT before you
start another, and report the wall with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken `IsCardinal`.** The consumer's statement is fixed.
- **Do not assume the axiom of choice.** The tree is `--safe` and classical
  only where it pays for it; say if a route needs choice.
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and counts from the source, never from a report**, and
  say where a module ends if you report a count.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**Cardinal arithmetic is template content**: it is about ordinals and
injections, not about definability. **Say whether the J tower inherits the
whole chapter unchanged**, since that would make this the most shared block
of the phase.

## ARCHIVE (DD18)

- **`_build/lj-1.90-report.md`**, read WHOLE, and `src/ProbeLJ190A.agda`.
  The instantiation and where it stops.
- **`_build/lj-1.1-recon.md`**, the survey that priced the wing's blocks
  before any build. **Its cardinal figures are what you are checking.**
- `_build/lj-1.47-report.md`, the square-law work, which is the nearest
  delivered cardinal-adjacent content.
- `src/L/StageCardinal.lagda.md`, `src/L/Ordinal/`, `src/L/Ordinal/SquareLaw.lagda.md`.
  **Read-only.**
- `dev/LESSONS.md` D-8, D-30, C-35, C-36, P-l, read WHOLE.
- `archive/rud-route/` for SHAPE only, and its `SquareLaw` for a delivered
  comparable if one exists there.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Devlin builds this chapter.** `dev/literature/devlin-II5.md` and the
surrounding sections. **Say in three lines what he assumes about cardinals
at 5.5**, and whether he proves it or takes it from earlier. Return a
**LITERATURE USED** section.

## SCOPE (read)

`src/L/BoundedSubset.lagda.md:1040-1050` and `:1390-1402` FIRST, then
`src/L/StageCardinal.lagda.md`, then `_build/lj-1.1-recon.md`'s cardinal
rows.

## SCOPE (write)

`src/ProbeLJ191*.agda`, and any master **only if you revert it before
finishing**. Your report is `_build/lj-1.91-report.md`. **Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for recon`, and read every
statement.

- **D-8.** Gate a block before funding it. One best-effort figure, its basis
  named, and the widest unmeasured term with its probe. **This brief IS
  D-8.**
- **D-1.** The probe doctrine.
- **C-35.** A block with no consumer is UNTESTED.
- **C-36.** Write the term you could not write.
- **D-30.** Price what the CONSUMER needs. **The consumer needs ONE cardinal,
  not a chapter.**
- **P-l.** A measured cure does not transfer by analogy; a price from a
  comparable elsewhere is a hypothesis.
- **P-h, P-k, P-m, P-n, P-t** as the bundle gives them.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-10, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed**
  and say the master count.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check` on anything you touch.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.91-report.md` incrementally, skeleton first.

**Lead with the cheapest route to one `IsCardinal` instance**, then its price
with the basis named, then **the widest unmeasured term and the probe that
would measure it**. Then what the tree already has, at `file:line`. **Mark
every negative MEASURED or INFERRED.** Then whether a route needs choice.
Then the DD4 answer.
