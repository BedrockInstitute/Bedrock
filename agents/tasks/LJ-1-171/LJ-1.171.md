# LJ-1.171: the last gate before the build

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`[LJ-1.170]` settled the architecture fork and named ONE unmeasured term with
its stop-line. Measure it.**

**Everything else in the supply chain is gated. This is the last gate before
the build.**

## THE STATE, and every figure is somebody's measurement

| piece | lines | state |
|---|---:|---|
| the assembly, `levelIn` and `cover` from one face | 17 | **MEASURED GREEN**, `[LJ-1.165]` |
| `K(u)`'s closure layer | 88 | **MEASURED GREEN**, `[LJ-1.166]` |
| pairing at an arbitrary limit | 35 | **MEASURED GREEN**, `[LJ-1.166]`, drop-in confirmed |
| the satisfaction layer | about 270 | nine delivered comparables, `[LJ-1.168]` |
| `powIter` by the re-key arm | 0.3 to 0.6k | 37 lines **MEASURED GREEN**, `[LJ-1.170]` |
| **the object-level reading of the key** | **?** | **the last unmeasured term** |

## THE OBLIGATION, in `[LJ-1.170]`'s own words, unchanged

> **The object-level reading of a three-component key, with its two
> directions.**
>
> **Probe: write ONE `paramSetAtL` conjunct against the delivered
> `arityNumAtL`** (`src/L/Coding/CodeSet.lagda.md:185-190`), **stop-line 60
> lines.**

**Do not move the stop-line after you see a number.** `[LJ-1.60]`'s PLAN row
reads 「NO-GO on a criterion I wrote wrong」, and every gate in this chain has
kept its criterion.

## WHAT THE KEY IS, and both halves are delivered

**`src/L/Choice/Name.lagda.md:381`:**

```agda
nameOf φ = countFo φ , (absFo φ , constantsFo φ)
```

**`constantsFo` is at `src/FOL/Manipulation/Parameters.lagda.md:105-108`, and
`[LJ-1.170]` MEASURED that it and `absFo` are generic in the constant type and
name no tower**, which is why the J tower gets the split free and why that arm
won on DD4.

**`arityNumAtL` (`src/L/Coding/CodeSet.lagda.md:185-190`) is the delivered
comparable**: an object-level reading of one component, with an `-out`
direction beside it. **Yours is the analogue for the parameter component.**

## SEARCH BEFORE YOU PRICE. THIS IS THE PHASE'S MOST EXPENSIVE LESSON

**Four misses, all mine, all in delivered live code:**

- `[LJ-1.163]`: `ElemDown` already supplied; my grep excluded the file.
- `[LJ-1.166]`: three of four closure classes already proved in
  `src/L/Choice/Name.lagda.md`.
- `[LJ-1.167]`: the pairing lemma was in the **immediately preceding
  dispatch's own green probe**.
- `[LJ-1.170]`: Devlin's split was already delivered, again in
  `src/L/Choice/Name.lagda.md`.

**`src/L/Choice/` has paid FOUR times. `src/L/Axioms/Separation.lagda.md` and
`src/L/Ordinal/StageArith.lagda.md` paid once each. Look there first and report
what you find before what you build.**

## THE ABORT CRITERION

- **GO at or below 60 lines**: report and STOP. **Then the whole supply chain
  is measured end to end and the build can be funded.**
- **NO-GO above it**: report the figure and what drove it. **That re-prices the
  re-key arm and the owner sees a number rather than a surprise.**
- **The reading needs a fact nothing supplies**: **STOP AND SAY SO.** That
  would be a second unsourced term in the same chain and it outranks the count.
- **Anything walls**: STOP with its wall-clock. **Never raise the cap.**

## THE PATTERN THIS CHAIN HAS MEASURED ABOUT ITSELF

**Two directions is where the cost sits.** `[LJ-1.162]` measured that its 125
lines were 59 lines of TWO nested extensionality frames, because an
extensionality is consumed with both directions and a membership fact.

**So price the `-in` and `-out` halves separately and say which is dearer.**

## WHAT YOU MUST NOT DO

- **Do not build the arm.** You gate its last term.
- **Do not edit any master.**
- **Do not touch the three `*Agree` masters**, `src/L/Coding/Graph.lagda.md`,
  or `[LJ-1.164]`'s move.
- **A probe goes in `agents/tasks/LJ-1-171/`**, never in `src/`, tracked. **You
  may extend a COPY of `[LJ-1.170]`'s probe; do not edit theirs in place.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised. Fix a
  wall-clock criterion in writing before each run.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**`[LJ-1.170]` MEASURED that this arm's two ingredients name no tower, so the J
tower gets the split free.** **Say whether your object-level reading keeps that
property or breaks it.** If it breaks it, say by how many lines: that is the
arm's DD4 cost and it was the reason the arm won.

## ARCHIVE (DD18)

**Three archive lookups changed a verdict this phase, and one archive claim was
MEASURED FALSE by `[LJ-1.170]`: the archived lemma I offered as ARM A's
comparable ASSUMES the bound it appears to prove, and runs on a basis this tree
does not have.**

- **`archive/src/2026-08-09-rud-route/L/Coding/`**: did the retired route give
  its code set an object-level reading of a parameter component? **At what
  size?**
- `archive/src/2026-08-09-rud-route/L/Definability.lagda.md`.
- **Take SHAPE, never a claim.** `[LJ-1.11]` ruled that route's condensation
  target classically FALSE.
- `agents/tasks/LJ-1-170/lj-1.170-report.md` and its probe, read WHOLE.
- **`dev/LESSONS.md` C-38 as extended, D-1, P-l, C-36**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`_build/literature/dev2.txt:593-640`. **Devlin's `K(u)` is finite sequences over
a fixed formula set, the variables and the members of `u`. Say which of your
three components corresponds to which, and whether any has no analogue.**
Return a **LITERATURE USED** section.

## SCOPE (read)

`src/L/Coding/CodeSet.lagda.md:185-210` FIRST, then
`src/L/Choice/Name.lagda.md:370-400`, then
`agents/tasks/LJ-1-170/ProbeLJ1170A.agda`.

## SCOPE (write)

`agents/tasks/LJ-1-171/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.

- **D-1, DD8, C-38 as extended, C-35, P-l, P-i, C-12, C-22, C-36, C-39, C-40.**
- **D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with what you found delivered, THEN with GO or NO-GO and the count.**
Then the two directions priced separately. Then whether the chain is now
measured end to end. Then the DD4 answer. **Mark every negative MEASURED or
INFERRED.**
