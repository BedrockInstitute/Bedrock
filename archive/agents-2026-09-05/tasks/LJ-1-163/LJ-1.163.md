# LJ-1.163: `ElemDown`, the residue common to all three open facts

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`[LJ-1.161]` MEASURED that what is left for `CrossOut`, `HasLevels` and
`Covered` alike is the hull's belief, `ElemDown`.** Gate it.

**One term, three facts, one phase blocker.**

## WHERE IT SITS, and the phase's whole remaining shape

`[LJ-1.7]` is STRUCTURE ONLY because `levelIn` and `cover` are hypotheses.
`[LJ-1.160]` bypassed the wall that had blocked them all phase and moved the
debt to three facts. `[LJ-1.161]` and `[LJ-1.162]` then priced the first:

| | |
|---|---|
| `CrossOut` leg 1, the transfer | **MEASURED, 20 in-fence lines** |
| leg 2, the moved formula means the delivered one | **MEASURED, 18** |
| leg 3, the identification | **MEASURED, 125**, and the chain typechecks whole |
| **`CrossOut` total** | **163** |
| `HasLevels` and `Covered` | their transport machine is **DELIVERED**, `src/L/BoundedSubset.lagda.md:195-196` and `:250-251` |
| **the residue of all three** | **`ElemDown`. You.** |

## WHAT IT IS, and I read it myself

`src/L/BoundedSubset.lagda.md:410-412`:

```agda
ElemDown : Type (ℓ-suc ℓ)
ElemDown = (n : ℕ) (φ : Formula SM n) (δ : SM ^ n)
         → ⟨ map inL δ ASt.AbsL.⊨ᵐ (mapFo inL φ) ⟩ → ⟨ δ ⊨ᵐ φ ⟩
```

**Downward elementarity: what the ambient L believes of the hull's members, the
hull believes too.**

**MEASURED: nothing in `src/` supplies it.** `ElemDown` appears only in
`BoundedSubset` itself, and `module _ (ed : ElemDown)` at `:414` takes it as a
hypothesis.

## THE ROUTE IS ALREADY NAMED IN THE MASTER'S OWN COMMENT

`src/L/BoundedSubset.lagda.md:455-461` states the plan in the tree's own words:

> the canonical code of each hull member (the `CodeSelect` least-of pattern,
> over the ordinal's own well-order and the code count), the generic close
> operation that replaces the top parameters by their codes as constants, its
> satisfaction adequacy, and **the `TarskiVaught` instance at every arity
> assembled from `hull-closed` through the two halves. `AtM.TV-thm` turns the
> instance into `Elementary`, hence `ElemDown`.**

**And pieces of it are delivered:** `down-reflect` at `:446` already runs
through `H.hull-closed`, and `CanonCode` at `:463` is the canonical-code module
that comment names.

**So the question is not 「what route」. It is 「how much of that route is
already built, and what does the rest cost」.**

## THE OBLIGATION, with its criterion fixed BEFORE the run (D-1)

**Supply `ElemDown` at ONE arity, by the route the comment names, and report
the in-fence line count for THAT supply.**

- **GO at or below 120 lines.** That is twice `[LJ-1.162]`'s leg-3 figure,
  because this is an induction over formulas rather than a single crossing, and
  because the comment says most of the machine is delivered. **Then all three
  open facts have a priced residue and `[LJ-1.7]` is fully gated.**
- **NO-GO above it, or if the Tarski-Vaught instance needs content nothing
  supplies.** **Then name what is missing and price it. That is a complete
  answer.**
- **`ElemDown` turns out to be FALSE at the hull, or to need a hypothesis the
  hull cannot pay**: **STOP AND SAY SO FIRST.** That would put the wall back by
  another door and it is the most valuable negative available in this phase.

**Do not move the criterion after you see a number.**

## THE C-38 GUARD, sharpened by what happened today

**Instantiate at ONE real arity. An interface nothing satisfies is a
restatement.**

**`[LJ-1.161]` found THREE delivered definitions with no consumer anywhere**,
so by C-38's own test one of them was a restatement rather than a supply.
**`[LJ-1.151]` found a delivered hypothesis that was outright FALSE**, and
`[LJ-1.153]` then repaired 36 of that class. **This wing has a measured history
of stating what it cannot supply. Do not add to it.**

## THE TWO WALLS ALREADY MEASURED, so you do not meet them blind

- **`[LJ-1.161]`**: the level-hood certificate, **20 minutes, RSS 9.03 GB,
  SIGTERM, no heap exhaustion.** Diagnosis INFERRED: a `refl` forcing a count
  over a graph that nests the twelve-row table twice.
- **The tree already routes around it**: `src/L/Condensation/README.md:1-3`
  splits the twelve rows across masters.

**Fix a wall-clock criterion in writing BEFORE you run. Report a timeout as a
wall. Never raise the cap.**

## WHAT YOU MUST NOT DO

- **Do not edit any master.** You gate.
- **Do not touch the three `*Agree` masters.** `[LJ-1.158]` landed there and
  `make check` is green on them.
- **Do not supply `ElemDown` by postulating it.** No `postulate`, no hole, no
  unsolved meta. `[LJ-1.162]` reported all three as absent and so must you.
- **A probe goes in `agents/tasks/LJ-1-163/`**, never in `src/`, tracked.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Elementarity is not tower content.** `[LJ-1.162]` measured 103 of 134 lines
template and was the FIRST site this phase where the generic form was not
within two lines of the fixed one. **Say which of your lines name the Def
tower, and do not estimate a variant you did not write.**

## ARCHIVE (DD18)

**`[LJ-1.157]` measured 37 of 61 live briefs citing no archive; `[LJ-1.160]`
found the phase's bypass inside one; `[LJ-1.162]` looked and found nothing, and
said so. All three outcomes are real.**

- **`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:160-257`**, the
  crossing face and `module Assembly`. **Does the archive hold an elementarity
  or a Tarski-Vaught instance? `[LJ-1.162]` found `CrossOut` there only as a
  hypothesis; check whether `ElemDown`'s analogue fares better.**
- **`archive/src/2026-08-09-rud-route/L/Hull.lagda.md`**, which is the archive's
  own hull.
- `archive/src/2026-08-09-rud-route/L/Definability.lagda.md`.
- **Take SHAPE, never a claim.** `[LJ-1.11]` ruled that route's condensation
  target classically FALSE and it ran on the rud tower.
- `agents/tasks/LJ-1-161/` and `LJ-1-162/`, read WHOLE.
- **`dev/LESSONS.md` C-38 as extended, C-35, D-1, P-l, P-i, C-36**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md`. **Devlin's 5.5 uses a Skolem hull and
condensation. Say what elementarity he assumes, at what level, and whether he
proves it or cites it.** Return a **LITERATURE USED** section.

## SCOPE (read)

`src/L/BoundedSubset.lagda.md:353-470` FIRST, whole, then `:660-700`.

## SCOPE (write)

`agents/tasks/LJ-1-163/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.

- **D-1.** The criterion fixed BEFORE the run, wall-clock included.
- **C-38 as extended.** Instantiate at one real arity.
- **C-35.** A delivered block with no consumer is untested.
- **P-i.** No surgery on a walling term.
- **DD8, P-l, P-y, C-12, C-22, C-36, C-39, C-40.**
- **D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with GO or NO-GO against 120 lines and the count for the supply.** Then
how much of the comment's route was already delivered. Then what the three open
facts cost once `ElemDown` is priced. Then any wall with its wall-clock. Then
the DD4 answer. **Mark every negative MEASURED or INFERRED.**
