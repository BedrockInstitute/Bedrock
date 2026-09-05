# LJ-1.167: the definable power at a general argument, and the pairing closure at a general limit

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`[LJ-1.166]` priced `K(u)`'s closure layer at 88 lines and named TWO gaps by
risk. Close both.** They are the smallest open items in the phase and one of
them is a single declaration.

## THE TWO GAPS, MEASURED by `[LJ-1.166]`

**GAP 1, the definable power.** MEASURED: **the tree has NO lemma about
`𝒟ₒ x` for a general `x`.** Every delivered `𝒟ₒ` fact is at `𝒟ₒ (Lset δ)`.
`powK` needs the general form.

> Its probe is **ONE declaration added to the already-green
> `agents/tasks/LJ-1-166/ProbeLJ1166A.agda`**:
> `pow∈λ : x ∈ˢ Lset lam → 𝒟ₒ x ∈ˢ Lset lam`

**GAP 2, the pairing closure at a general limit.** MEASURED: the delivered
`pr∈limit` (`src/L/Choice/Name.lagda.md:123-124`) is **hard-coded to `ω`**,
because its recursion is indexed by `ℕ` through `inSome` and `raiseTo`. The
site needs an arbitrary limit.

> **Exactly ONE proved `κ → κ` pairing closure exists in the whole live tree.
> Every other pairing lemma SHIFTS the set** (`σ ↦ sucV (sucV σ)`), **and a
> shifted lemma cannot fill `pairK`.**

## WHERE TO LOOK FIRST, and this is the phase's own measured lesson

**Search `src/L/Choice/` BEFORE you write anything.**

**`[LJ-1.163]` found `ElemDown` already delivered after three dispatches had
priced it. `[LJ-1.166]` found three of four closure classes already PROVED at
`src/L/Choice/Name.lagda.md:120-135`, cited by no brief in this phase.** **Two
misses in four dispatches, both in `L/Choice/`.** `[LJ-1.166]`'s own words: the
pattern is in the SEARCH.

**So: grep for the general forms first, and report what you found before you
report what you built.**

## THE OBLIGATION, criteria fixed BEFORE the run (D-1)

**GAP 1:** prove `pow∈λ` at a general limit, or measure why it cannot be
proved.

- **GO at or below 40 lines.**
- **NO-GO above, or if it needs a fact nothing supplies**: name that fact.
- **It is FALSE at a general argument**: **STOP AND SAY SO FIRST.** That would
  re-open `K(u)`'s price and it is the most valuable negative here.

**GAP 2:** generalise the pairing closure from `ω` to an arbitrary limit, or
measure why the `ℕ`-indexed recursion cannot be lifted.

- **GO at or below 60 lines.**
- **NO-GO**: say exactly which step needs the naturals, and price the
  alternative.

**Do not move either criterion after you see a number.** `[LJ-1.60]`'s PLAN row
reads 「NO-GO on a criterion I wrote wrong」.

## THE REPAIR THAT HAS NOW FIRED TWICE

**P-i's implicit-index repair cured a wall in `[LJ-1.165]`** (171 s and heap
exhaustion to exit 0 in 4 s, one implicit index given explicitly) **and fired
again at two more sites in `[LJ-1.166]`.** Two consecutive tasks, same cure.

**If you meet a wall, try that FIRST, and say whether it worked.** If it fires
a third time I will admit it as a law with its measurement.

## WHAT YOU MUST NOT DO

- **Do not edit any master.** These are probes.
- **Do not touch the three `*Agree` masters**, `src/L/Coding/Graph.lagda.md`,
  or `[LJ-1.164]`'s move.
- **A probe goes in `agents/tasks/LJ-1-167/`**, never in `src/`, tracked. **You
  may extend a copy of `[LJ-1.166]`'s probe; do not edit theirs in place.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** A sibling
  is running. **Fix a wall-clock criterion in writing before each run.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**`[LJ-1.166]` MEASURED that the `KFacts` record is already tower-blind while
the SUPPLY is not, and that parameterising costs +6 lines now and saves 42 at
the J end.** **Say whether your two lemmas are template, and do not estimate a
variant you did not write.**

## ARCHIVE (DD18)

**`[LJ-1.157]` measured 37 of 61 live briefs citing no archive. This is not a
form: `[LJ-1.160]` found the phase's bypass inside one.**

- **`archive/src/2026-08-09-rud-route/L/Axioms/`**: the retired route's own
  closure lemmas. **Did it have a general-limit pairing closure? At what size?**
- `archive/src/2026-08-09-rud-route/L/Definability.lagda.md`, for the definable
  power on that route.
- **Take SHAPE, never a claim.** `[LJ-1.11]` ruled that route's condensation
  target classically FALSE.
- `agents/tasks/LJ-1-166/lj-1.166-report.md`, read WHOLE.
- **`dev/LESSONS.md` P-i, C-38 as extended, D-1, P-l, C-36**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md:240-260`. **Say what Devlin assumes about the
definable power at a general set, and whether he proves it.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`src/L/Choice/Name.lagda.md:95-140` FIRST, then grep `src/` for the general
forms, then `agents/tasks/LJ-1-166/ProbeLJ1166A.agda`.

## SCOPE (write)

`agents/tasks/LJ-1-167/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.

- **D-1, DD8, C-38 as extended, P-i, P-l, C-12, C-22, C-36, C-39, C-40.**
- **D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with what you found already delivered, THEN with GO or NO-GO on each
gap.** Then the line counts against each criterion. Then whether P-i's repair
fired. Then the DD4 answer. **Mark every negative MEASURED or INFERRED.**
