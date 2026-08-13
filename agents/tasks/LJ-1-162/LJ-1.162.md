# LJ-1.162: leg 3, the last unknown in `CrossOut`

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`CrossOut` is down to ONE unknown leg, and its repair is already delivered.**
Gate it.

## WHERE THIS SITS, and the phase turns on it

`[LJ-1.7]` is STRUCTURE ONLY because `levelIn` and `cover` are hypotheses.
`[LJ-1.160]` MEASURED that both close in 16 in-fence lines from a crossing face
at the collapse image, and that the wall term
`π (Lset m') ≡ Lset (π m')` appears NOWHERE on that route. The debt moved to
three open facts, and `CrossOut` is the first.

**`[LJ-1.161]` then split `CrossOut` into three legs and measured two:**

| leg | state |
|---|---|
| 1. inner to ambient | **MEASURED, 20 in-fence lines** |
| 2. the moved formula still means the delivered one | **MEASURED, 18 lines** |
| **3. ambient implies `v ≡ Lset b`** | **OPEN. This is you.** |

**Leg 3 is Devlin's own step (a).**

## WHY IT IS OPEN, MEASURED by `[LJ-1.161]`

The delivered `Lset-only` (`src/L/Hierarchy.lagda.md:334`) reads

```agda
Lset-only : ⟨ γ ⊨ LsetGraphAt w b ⟩ → IsOrd (fst (lookup b γ))
```

**It wants the INNER reading, at the L class, of the UNBOUNDED graph. The
transfer does not produce that.**

**And the graph is unbounded for a reason you can see:**
`src/L/Coding/Sequence.lagda.md:286-290` has `ApproxAt` carrying **two
unbounded `∀̇`**, so `LsetGraphAt` is neither `Δ₀` nor `Σ₁`.

**MEASURED: no Levy witness for `LsetGraphAt` exists anywhere in `src/`.**

## THE REPAIR IS ALREADY IN THE TREE

`src/L/Condensation.lagda.md:2489-2493`:

```agda
graphBndAt : Formula S m
graphBndAt = ∃̇∈ (var K) (A.approxBndAt ∧̇ S.stepBndAt)

Δ₀-graphBndAt : Δ₀ ψs → Δ₀ ψa → Δ₀ graphBndAt
```

**A bounded graph with a `Δ₀` certificate, delivered.** `[LJ-1.161]` named it
as leg 3's repair and did not run it.

## THE OBLIGATION, and its criterion fixed BEFORE the run (D-1)

**Close leg 3 with the bounded graph in place of the unbounded one: from the
transferred ambient reading, derive `v ≡ Lset b`. Report the in-fence line
count for THAT ONE LEG.**

- **GO at or below 60 lines.** Then `CrossOut` is fully priced at roughly
  20 + 18 + your figure, and `[LJ-1.7]`'s first open fact has a number.
- **NO-GO if the bounded graph does not carry the identification**, that is, if
  `Lset-only`'s content genuinely needs the unbounded form. **Then leg 3 needs
  its own Levy witness and that is a chapter. Say so; it is a complete
  answer.**
- **The bounded and unbounded graphs turn out not to agree**: **STOP AND SAY
  SO.** That would be the most valuable negative here, because the tree already
  uses the bounded form elsewhere.

**Do not move the criterion after you see a number.** `[LJ-1.60]`'s PLAN row
reads 「NO-GO on a criterion I wrote wrong」.

## THE WALL THAT IS ALREADY KNOWN, so you do not walk into it blind

**`[LJ-1.161]` MEASURED a wall on the level-hood certificate: 20 minutes, RSS
pinned at 9.03 GB, SIGTERM, no heap exhaustion.** Its INFERRED diagnosis is a
`refl` forcing a count over a graph that nests the twelve-row table twice.

**The tree already routes around it:** `src/L/Condensation/README.md:1-3` splits
the twelve rows across masters so that no single process elaborates all twelve.

**Fix a wall-clock criterion in writing BEFORE you run, as `[LJ-1.161]` did,
and report a timeout as a wall.** Never raise the cap.

## THE ONE THING THAT WOULD MAKE THE RETURN WORTHLESS

**Report the count for the ONE LEG, not for the file.** `[LJ-1.124]` was marked
MEASURED FALSE on exactly that distinction, and `[LJ-1.151]` and `[LJ-1.161]`
were both held to it. Say what you excluded and give the file total separately.

## THE C-38 GUARD

**Instantiate. An interface nothing satisfies is a restatement.**

**`[LJ-1.161]` found three delivered definitions with NO consumer anywhere**,
so by C-38's own test one of them was a restatement rather than a supply. **Do
not add a fourth.**

## WHAT YOU MUST NOT DO

- **Do not build `CrossOut`.** You gate leg 3.
- **Do not edit any master.**
- **Do not touch the three `*Agree` masters.** `[LJ-1.158]` landed there and
  `make check` is green.
- **A probe goes in `agents/tasks/LJ-1-162/`**, never in `src/`, tracked.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Three times this phase the generic form has come within two lines of the
fixed one**, most recently at `[LJ-1.161]`, where 16 of 20 gated lines were
template. **Say which of your lines name the Def tower.**

## ARCHIVE (DD18)

**`[LJ-1.157]` measured 37 of 61 live briefs citing no archive, and `[LJ-1.160]`
then found the phase's bypass inside one. This section is real.**

- **`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:160-257`**, the
  crossing face and `module Assembly`, which `[LJ-1.160]` took the SHAPE of.
  **Does it hold leg 3, and in what form?**
- `archive/src/2026-08-09-rud-route/L/InitialSegment.lagda.md`, 114 in-fence:
  an initial segment is what an ordinal identification wants.
- **Take SHAPE, never a claim.** `[LJ-1.11]` ruled that route's condensation
  target classically FALSE, and it ran on the rud tower.
- `agents/tasks/LJ-1-161/lj-1.161-report.md` and `agents/tasks/LJ-1-160/`, both
  read WHOLE.
- **`dev/LESSONS.md` C-38 as extended, D-1, P-l, P-i, C-36**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md`. **Leg 3 is Devlin's step (a). Say what he
proves there and whether he needs the unbounded graph.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`src/L/Condensation.lagda.md:2489-2493` FIRST, then
`src/L/Hierarchy.lagda.md:334`, then `agents/tasks/LJ-1-161/ProbeLJ1161A.agda`.

## SCOPE (write)

`agents/tasks/LJ-1-162/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.

- **D-1.** The criterion fixed BEFORE the run, wall-clock included.
- **C-38 as extended.** Instantiate.
- **P-i.** No surgery on a walling term.
- **DD8, P-l, P-y, C-12, C-22, C-36, C-39, C-40.**
- **D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with GO or NO-GO against 60 lines and the count for the ONE LEG.** Then
`CrossOut`'s full price, 20 plus 18 plus yours. Then whether the bounded graph
carried the identification, MEASURED. Then any wall with its wall-clock. Then
the DD4 answer. **Mark every negative MEASURED or INFERRED.**
