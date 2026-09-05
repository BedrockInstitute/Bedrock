# LJ-1.302: compose the thirty `Agree` modules into the bridge `q'` needs

tier: pi (pi-subagent-mode), **model `glm-5.3`**. I ran
`scripts/dispatch/dispatch_policy.py` and took the head it gave. **`scripts/`
was reorganised today**: `rules.py` is `scripts/dispatch/rules.py`, the linters
are `scripts/gate/`, `ledger.py` is `scripts/measure/ledger.py`.

## GOAL

**`[LJ-1.7]` is LJ-1's blocking row, `amb` is its last open parameter, and the
one route left is `q'`.** `[LJ-1.298]` priced the port and found the gap.

**Its measurement, and it is the reason this task exists:**

> **The composite term does not exist.** `src/L/Condensation.lagda.md` ends at
> line 7319 with `LeafAgree`'s closing fence. **No theorem composes the thirty
> `Agree` modules into a bridge at any formula.** MEASURED, by reading the
> file's end.

**Build that composite, or measure what stops it.**

## WHAT IS ALREADY MEASURED, so you do not redo it

- **The generic re-instantiation is FREE.** `[LJ-1.298]` re-instantiated
  `TagAgree` with the class as a module parameter and **ZERO of its 33 lines
  changed**. One scaffold serves a whole chapter.
- **23 of the 30 modules are clean**, 3,511 of 4,208 lines: their text names
  nothing outside `GenModel`'s deliveries. **Seven are dirty**, 697 lines, and
  they name committed formulas whose re-statements are short.
- **The dirty seven carry hypothesis telescopes.** `SatGraphAgree` alone takes
  eight parameters at `src/L/Condensation.lagda.md:6844-6900`, and **at the
  ambient carrier somebody must SUPPLY them. Nobody has measured that cost.**
- **`[LJ-1.297]` did the analogous supply once**: all six of `AmbientStep`'s
  readings, 20 lines, exit 0, 1.56 s. **That is the shape and the comparable.**

## THE TWO QUESTIONS

**1. WHAT WOULD THE COMPOSITE SAY?** Write its TYPE first, before any proof.
`q'` is

```agda
q' : (γ : Vec A.R.SC 2) → ⟨ A.ambient γ (embed φ₀) ⟩
   → ⟨ A.ambient γ (Graph {2} zero (suc zero)) ⟩
```

**Say what a composite over the thirty would have to state to give it.** **If
the thirty do not compose to that shape, that is the answer and it is worth
more than a term.**

**2. WHAT DO THE DIRTY SEVEN COST AT THE AMBIENT CARRIER?** Take ONE of them,
supply its telescope the way `[LJ-1.297]` supplied `AmbientStep`'s six
readings, and **report the lines and the seconds.** **One measured module beats
seven inferred ones.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE COMPOSITE'S TYPE IS WRITABLE AND ONE DIRTY MODULE IS PRICED.** Report
  both. **Then `q'` has a shape and a rate for the first time.** STOP.
- **THE THIRTY DO NOT COMPOSE TO `q'`'s SHAPE.** **Say what is missing.** That
  re-prices `[LJ-1.7]` and the owner should hear it.
- **A DIRTY MODULE'S TELESCOPE CANNOT BE SUPPLIED AT THE AMBIENT CARRIER.**
  **Name the parameter** (C-36). **That is the same wall `[LJ-1.299]` hit from
  the other side, and finding it twice would matter.**
- **THE COMPOSITE ALREADY EXISTS SOMEWHERE.** `[LJ-1.298]` read the file's end;
  **search the whole tree before you build** (C-44). Three times this month a
  report called absent what the repository held.
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## CONSTRAINTS

- **THIS IS A PROBE. LAND NOTHING.** Write and run in `agents/tasks/LJ-1-302/`.
  **`src/` is forbidden for probes** (I-5).
- **Do not edit `src/L/Condensation.lagda.md`.** It is 7,319 lines, delivered
  and green. **Copy from it.**
- **A SIBLING IS LIVE** in `agents/tasks/LJ-1-301/`. Do not touch it.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  load beside every absolute figure. **`Condensation` is 132 s cold on its own;
  budget for it and prefer a copied fragment to the whole chapter.**
- Never `src/Everything.lagda.md`, never `dev/ledger.toml`, never
  `dev/PLAN.md`, never `src/L/Choice/Name.lagda.md` (DD23).
- **Create `agents/tasks/LJ-1-302/lj-1.302-report.md` in your FIRST five
  minutes** (C-22).
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
**Thirty delivered modules are a starting point, not a bridge.**

**C-45. Audit the INSTANTIATION, never the telescope.** **The dirty seven ARE
telescopes; what they cost is an instantiation question.**

**DD8. Name the widest unmeasured term and the probe that measures it.** The
dirty seven's ambient supply is that term today.

**C-44.** Every figure here is `[LJ-1.298]`'s or `[LJ-1.297]`'s.

**R-41, written today.** **Depth is free and MIXED SPELLING costs**, and it is
depth-gated: 219 ms at depth 2, 9,286 at depth 3, 419,218 at depth 4. **If you
meet a slow conversion, look for a type and a body naming one object two ways
before you look anywhere else.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.297]` measured that the generic port PAID: because `[LJ-1.238]` wrote
`GenSequence` generic in the class, the ambient supply cost six lines instead of
a coding chapter.** **This is the same bet at thirty times the size.** Say
whether a generic `Agree` family would pay the same way, and **NAME YOUR AXIS**
(C-46): this is the port's L-against-ambient axis, the SUBJECT here rather than
a label.

## ARCHIVE (DD18)

`agents/tasks/LJ-1-298/lj-1.298-report.md` read WHOLE, and its
`GenTagAgree.agda`. `agents/tasks/LJ-1-297/lj-1.297-report.md`, the six readings
it supplied and how. `agents/tasks/LJ-1-238/` for the generic port that paid.
`archive/dev/TASKS-archived.md`, taking SHAPE and never a claim. Return an
**ARCHIVE USED** section naming ONE line read per archived file.

## LITERATURE (DD18)

**`[LJ-1.297]` MEASURED that Devlin needs no equation of `q`'s kind: one formula
and its analogue, bridged by 1.9.15 at `dev/literature/devlin-II5.md:93-97`.**
**Say whether the same is true of `q'`.** **If Devlin needs no bridge at all,
the right question may be why the port needs thirty modules.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-298/lj-1.298-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-302/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **OPEN the full entry for any law you act on.**

- **D-1, P-l, C-45, C-44, C-36, C-42, C-50, R-41.**
- **P-h, P-i, P-k, P-m, P-n, P-t, P-y, R-34, R-35, R-40. C-12, C-22, C-32,
  C-38, C-39, C-40, C-49. I-5. DD0, DD8, DD18, DD24, D-10, D-26.**

## RETURN

**Lead with the composite's TYPE, or the reason it cannot be written.** Then the
ONE dirty module you priced, with its lines and seconds. Then the extrapolation
to seven, with its basis named. Then whether `q'` follows. Then the DD4 answer
with its axis. **Mark every negative MEASURED or INFERRED.**
