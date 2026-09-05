# review of `defines-cover`: the obligation is NOT inhabited

## VERDICT

**`Cert.DefinesCover` IS NOT SUPPLIED AT A GENERAL CODE, AND I DID NOT
INHABIT IT.** The meter says so: `agents/tasks/LJ-1-595/Probe595.agda::defines-cover`
returns `missing exit=42 ... [NotInScope]`, `1 UNRESOLVED of 1`,
`probe_red=False`. The probe itself is green
(`agents/tasks/LJ-1-595/runs/p-final.out`, `EXIT=0`).

**AND THE BRIEF'S RESEMBLANCE IS HALF TRUE, WHICH IS THE WHOLE FINDING.**
The brief says clause (ii) is the sibling of clause (i) because
`[LJ-1.578]` wrote "the covering ordinal of a hull member is defined the
same way" (`agents/tasks/LJ-1-578/Probe578.agda:242-243`). Measured:

- **In Devlin the two ARE siblings**, because they are two Σ₁ statements
  built from ONE Σ₀ matrix (`dev/literature/devlin-II5.md:95-99`), and the
  difference is only which variable is bound
  (`dev/literature/devlin-II5.md:102-103` against `:107-108`).
- **In the tree as `[LJ-1.578]` split it they are NOT**, because clause (i)
  (`Probe578.agda:234-240`) hides that matrix behind an existential ONE
  CODE AT A TIME. A family of index-fixed formulas cannot be put under a
  binder, so clause (ii) does not follow from clause (i), and neither one
  gives the other's formula.

## WHY THE OBLIGATION CANNOT BE DISCHARGED HERE

Clause (ii) asks, for every code `c`, for a formula over hull codes whose
every inner-world witness `a` satisfies BOTH
`IsOrd (HS.C.π (fst a))` and `⟨ fst (T.val c) ∈ˢ Lset (fst a) ⟩`
(`Probe578.agda:246-251`).

1. **The first conjunct is free.** `Probe595.agda:145` (`π-ord`) carries
   ordinal-hood across the collapse for ANY carrier, and
   `Probe595.agda:251` (`ord-out`) reads it off a Δ₀ atom at the stage's
   inner world. Neither costs a hypothesis.
2. **The object of the second conjunct is free too.**
   `Probe595.agda:270` (`cover-in-stage`) builds a covering ordinal of the
   inner world for every member of it, unconditionally, and
   `Probe595.agda:289` inhabits W3 with it.
3. **What is NOT free is a FORMULA that selects such an ordinal.** The
   only Δ₀ handle on "y is covered by x" is `y ∈ x` with both ordinals,
   which is why `Probe595.agda:324` (`cover-at-ordinal`) pays the clause
   outright when `fst (T.val c)` is an ordinal and cannot be pushed one
   step further. For a general value the covering relation is the level
   construction itself, and the tree proves the level graph AT `L`
   (`Lset-only`, `src/L/Hierarchy.lagda.md:334`, whose satisfaction is the
   class L: `module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans` at
   `src/L/Hierarchy.lagda.md:78`), never at a stage. The stage reading is `GraphAgree`, and
   `[LJ-1.578]` records it as "parts are terms in five probes, none in
   `src/`" (`agents/tasks/LJ-1-578/lj-1.578-report.md:50`).

**SO THE STOP IS NOT "IT IS HARD". IT IS: CLAUSE (ii) NEEDS THE LEVEL
FORMULA WITH ITS INDEX FREE, AND NO DELIVERED TERM HAS IT.**

## WHAT I DELIVERED INSTEAD, AND WHAT EACH ONE COSTS THE NEXT BRIEF

Every row typechecks; the seven names were metered and return
`0 UNRESOLVED of 7`.

| term | `Probe595.agda` | what it settles |
|---|---|---|
| `CollapseOrd.π-ord` | `:145` | the collapse sends an ordinal to an ordinal, ANY carrier |
| `CoverAt.covering-ordinal` | `:289` | W3: the covering ordinal EXISTS at the inner world |
| `CoverAt.cover-at-ordinal` | `:324` | clause (ii), UNCONDITIONAL, at an ordinal-valued code |
| `CoverAt.cover-from-coded-all` | `:380` | clause (ii) from a covering ordinal NAMED BY A CODE |
| `CoverAt.cover-from-internal` | `:418` | the ordinal half of clause (ii) is free; only the covering half is priced |
| `CoverAt.factC-from-hull` | `:439` | **Fact C needs no formula at all**: `Covered` is truncated |
| `Shared.shared-gives-clause-ii` | `:542` | Devlin's ONE matrix, with its two directions, gives clause (ii) |

## THE TWO THINGS THE NEXT BRIEF SHOULD DECIDE

1. **Clause (ii) is a detour for Fact C.** `Facts.Covered`
   (`Probe578.agda:130-136`) is TRUNCATED, so the covering ordinal never
   has to be selected by a formula: `factC-from-hull`
   (`Probe595.agda:439`) derives Fact C from "every hull member sits in a
   level indexed by an ordinal OF THE HULL", with no syntax anywhere.
   **If the certificate is only there to buy Facts A, B and C, clause (ii)
   should be replaced by that statement.**
2. **If the certificate is kept, it should be stated at the matrix and not
   at the three consequences.** `Shared` (`Probe595.agda:483-544`) is that
   shape, and clause (ii) falls out of it in 40 lines. Whether clause (i)
   also falls out of it I did NOT measure: it needs the index substituted
   by a constant, which is a renaming this task did not price. **That is
   the one open question this task leaves.**

## SCOPE

I wrote only inside `agents/tasks/LJ-1-595/`. Nothing is postulated, the
probe carries `--safe`, there is no hole, and nothing lands in `src/`.
No commit, no push.
