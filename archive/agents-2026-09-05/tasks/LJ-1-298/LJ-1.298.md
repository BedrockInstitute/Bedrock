# LJ-1.298: price `q'` through the delivered class-carrier analogues

tier: pi (pi-subagent-mode), **model `glm-5.3`**. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the head
it gave.** **NOTE THE PATH: `[LJ-1.295]` reorganised `scripts/` into
subdirectories today.** `rules.py` is now `scripts/dispatch/rules.py`, the
linters are `scripts/gate/`, and `ledger.py` is `scripts/measure/ledger.py`.

## GOAL

**`[LJ-1.7]` is LJ-1's blocking row and `amb` is its last open parameter.**
`[LJ-1.293]` refuted `q` BY MACHINE and `[LJ-1.297]` upheld that refutation,
so the route through `q` is dead. **`[LJ-1.297]` then shrank the residue and
named the one term nobody has measured. Measure it.**

## WHAT `[LJ-1.297]` ALREADY DISCHARGED, so you do not redo it

- **All six of `AmbientStep`'s readings are SUPPLIED at the ambient carrier**,
  by machine, `agents/tasks/LJ-1-297/ProbeLJ1297D.agda`, exit 0, 22.81 s.
- **The `⊨ᵐ` to `⊨ᵛ` transport at the FULL class, for every formula**, 20
  lines, `ProbeLJ1297C.agda`, exit 0, 1.56 s. **It is free at the ambient
  carrier precisely because it is FALSE at the class carrier.**
- **So `AmbientStep` now carries ONE open hypothesis and it is `q`.**

## THE NAMED TERM, and this task is exactly it

`[LJ-1.297]`'s own words: **the widest unmeasured term and its probe is to
re-instantiate `TagAgree` at `src/L/Condensation.lagda.md:6670` generically and
diff it. Nobody has run it.**

**The obligation `q'` is the one-direction implication `go` actually spends:**

```agda
q' : (γ : Vec A.R.SC 2) → ⟨ A.ambient γ (embed φ₀) ⟩
   → ⟨ A.ambient γ (Graph {2} zero (suc zero)) ⟩
```

**Its delivered class-carrier analogue is THIRTY `Agree` modules, 3,871 agda
lines, at `src/L/Condensation.lagda.md:2774-7319`.** `[LJ-1.297]` measured
that. It also measured the comparable for a carrier substitution:
`[LJ-1.224]`'s **8 changed lines out of 338**, TAKEN.

**So the projection is: mechanical per line, chapter-scale by volume, about 25x
`[LJ-1.238]`'s one-dispatch port. `[LJ-1.297]` marked that a PROJECTION and P-l
says it stays one until somebody re-instantiates a module and counts.**

## WHAT TO BRING BACK

**1. RE-INSTANTIATE `TagAgree` GENERICALLY AND DIFF IT.** Copy it into your task
directory, make it generic in the class the way `[LJ-1.238]`'s `GenSequence`
is, and **report the CHANGED LINE COUNT against its 3,871-line family.**
**That number is the whole task.**

**2. THE EXTRAPOLATION, with its basis named** (DD8). One best-effort figure for
all thirty modules, and say whether the basis is this probe, `[LJ-1.224]`'s 8
of 338, or a survey.

**3. WHETHER `q'` FOLLOWS.** If the ambient instantiation of the `Agree` family
gives `q'`, say so and name the term. **If it does not, say what else is
needed.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE RE-INSTANTIATION IS MECHANICAL.** Report the changed-line count and the
  extrapolation. **Then `[LJ-1.7]` has a priced route for the first time.** STOP.
- **IT IS NOT MECHANICAL.** **Name the term that resists** (C-36). **That is
  worth more than the count**, because it would mean the 25x projection is
  wrong in kind and not in size.
- **`TagAgree` IS NOT REPRESENTATIVE.** If it is the easiest or the hardest of
  the thirty, say so and say which module you would measure instead.
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. Report a heap exhaustion as a
  wall and **NEVER raise the cap.**

## CONSTRAINTS

- **THIS IS A PROBE. LAND NOTHING.** Write and run in `agents/tasks/LJ-1-298/`.
  **`src/` is forbidden for probes** (I-5).
- **Do not edit `src/L/Condensation.lagda.md`.** Copy from it.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  load beside every absolute figure.
- **A SIBLING IS LIVE** in `agents/tasks/LJ-1-299/`. Do not touch it.
- Never `src/Everything.lagda.md`, never `dev/ledger.toml`, never
  `dev/PLAN.md`, never `src/L/Choice/Name.lagda.md` (DD23).
- **Create `agents/tasks/LJ-1-298/lj-1.298-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `scripts/gate/lint-agda.py --check`. **No em dash in any language.** DD23
  freezes mathematical prose.
- Count with `.venv/bin/python scripts/measure/ledger.py`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative MEASURED or
  INFERRED, in those words.

## THE RULES THIS CHAIN EARNED

**P-l. A construction delivered at one carrier is a HYPOTHESIS at another.**
**That is why this task exists: thirty delivered modules are a starting point,
not a price.**

**C-45. Audit the INSTANTIATION, never the telescope.** `[LJ-1.297]` corrected a
cited price on exactly this ground: `[LJ-1.244]`'s exit 42 was measured with
`Graph` ABSTRACT, which is the telescope.

**DD8. Name the widest unmeasured term and the probe that measures it.** You
are that probe.

**C-44.** Every figure here is `[LJ-1.297]`'s and you must re-derive each one.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.297]` measured that the generic port PAID: because `[LJ-1.238]` wrote
`GenSequence` generic in the class, the ambient supply cost six lines instead of
a coding chapter.** **Your task is the same bet at 30x the size.** Say whether
writing the `Agree` family generic would pay the same way, and **NAME YOUR
AXIS** (C-46): this is the port's L-against-ambient axis, which is the SUBJECT
here rather than a label.

## ARCHIVE (DD18)

`agents/tasks/LJ-1-297/lj-1.297-report.md` read WHOLE, and its four probes.
`agents/tasks/LJ-1-238/` for the generic port that paid.
`agents/tasks/LJ-1-224/` for the 8-of-338 carrier substitution.
`archive/dev/TASKS-archived.md`, taking SHAPE and never a claim. Return an
**ARCHIVE USED** section naming ONE line read per archived file.

## LITERATURE (DD18)

**`[LJ-1.297]` measured that Devlin needs no such equation: one formula and its
analogue, bridged by 1.9.15 at `dev/literature/devlin-II5.md:93-97`, so `q` is
the PORT's own artifact.** **Say whether the same is true of `q'`**, because if
it is, the right question may be why the port needs it at all. Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-297/lj-1.297-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-298/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-1.** The abort criterion is fixed above.
- **P-l.** The centre.
- **DD8.** The widest unmeasured term.
- **C-45, C-44, C-36, C-42, C-50. P-i, P-k, P-m, P-t, P-y, R-34, R-35, R-40,
  R-41. C-12, C-22, C-32, C-38, C-39, C-40, C-49. I-5. DD0, DD18, DD24, D-10,
  D-26.**

## RETURN

**Lead with the changed-line count from re-instantiating `TagAgree` generically,
against its family's 3,871 lines.** Then the extrapolation to all thirty with
its basis named. Then whether `q'` follows. Then whether `TagAgree` is
representative. Then the DD4 answer with its axis. **Mark every negative
MEASURED or INFERRED.**
