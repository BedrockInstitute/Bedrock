# LJ-1.304: price `StepAgree` and `ApproxAgree` at the ambient carrier

tier: pi (pi-subagent-mode), **model `glm-5.3`**. I ran
`scripts/dispatch/dispatch_policy.py` and took the head it gave. **`scripts/`
moved today**: `rules.py` is `scripts/dispatch/rules.py`, the linters are
`scripts/gate/`, `ledger.py` is `scripts/measure/ledger.py`.

## GOAL

**`[LJ-1.7]` is LJ-1's blocking row, `amb` is its last open parameter, and
`q'` is the one route left. Three of its four costs are now measured. You price
the fourth, and `[LJ-1.302]` named it the LAST one.**

| part of `q'`'s route | price | measured by |
|---|---|---|
| the clean 23 `Agree` modules, generic | about 180 hand-written lines placing 6,900 | `[LJ-1.298]`, 0 changed lines at one site |
| the dirty seven's ambient TIES | about 100 lines, and the ties are ONE debt | `[LJ-1.302]`, 51 lines at one site |
| the composite's TYPE, and that it FEEDS | writable, and `amb-from-composite` typechecks | `[LJ-1.302]` |
| **`StepAgree` and `ApproxAgree`** | **UNPRICED** | **you** |

**`[LJ-1.302]`'s own words**: they are「mathematics, not site facts: the
bounded `∀̇`-closure of the approximation must become the unbounded one, and the
witnesses must survive the change of leaf. Nobody has priced those, and they are
the last unpriced term on `q'`'s route. DD8 names them as the next widest
term.」

## PREMISES

- **`StepAgree` and `ApproxAgree` live in the `Agree` family**, inside
  `src/L/Condensation.lagda.md:2774-7319`. **Find them and read them WHOLE
  before anything else.**
- **The two named obligations are: bounded `∀̇`-closure becoming unbounded, and
  witnesses surviving a change of leaf.** VERIFY that those are what the
  modules actually need (C-44); `[LJ-1.302]` read them, I did not.
- **The leaf-stem already exists.** `extAtB→extAt` and `extAt→extAtB` at
  `src/L/Condensation.lagda.md:2511-2529` take the leaf bridge as parameters,
  and `LeafAgree.out/back` at `:7231-7241` is that bridge. **So「change of
  leaf」may already be served; check before pricing it.**
- **The comparable for this kind of supply is `[LJ-1.297]`**: six readings
  supplied at the ambient carrier in 20 lines, exit 0, 1.56 s. **P-l says that
  is a comparable and not a price.**

## WHAT TO BRING BACK

**1. WHAT EACH MODULE ACTUALLY NEEDS AT THE AMBIENT CARRIER.** Not what the
class version assumes: what a reader must SUPPLY when the carrier is ambient.
Name each obligation at `file:line`.

**2. ONE OF THEM PRICED BY BUILDING.** Take whichever is smaller, supply its
obligations at a concrete environment the way `[LJ-1.302]` did for
`DomainAgree`, and **report the lines and the seconds.** **One built beats two
surveyed.**

**3. THE ONE NUMBER (DD8), with its basis named.** Both modules together, and
say whether the basis is this build, the `[LJ-1.297]` comparable, or a survey.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BOTH ARE PRICED AND ONE IS BUILT.** Report both. **Then `q'`'s route has no
  unpriced term left and `[LJ-1.7]` can be funded as a build.** STOP.
- **ONE OF THEM IS NOT MATHEMATICS AFTER ALL.** If the bounded-to-unbounded step
  is a site fact like the ties, **say so**: it would fold into `[LJ-1.302]`'s
  100 and the route gets cheaper.
- **THE BOUNDED-TO-UNBOUNDED STEP IS FALSE AT THE AMBIENT CARRIER.** **That is
  the most valuable outcome here.** The ambient class has no bound, so a
  closure stated with one may not transfer. **Give the countermodel or the term
  that fails** (C-36), and stop: it would mean `q'`'s route needs re-shaping and
  the owner must hear it before more is funded.
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **`Condensation` is 132 s cold
  on its own: prefer a copied fragment to the whole chapter.** NEVER raise the
  cap.

## CONSTRAINTS

- **THIS IS A PROBE. LAND NOTHING.** Write and run in `agents/tasks/LJ-1-304/`.
  **`src/` is forbidden for probes** (I-5).
- **Do not edit `src/L/Condensation.lagda.md`.** Copy from it.
- **A SIBLING IS LIVE** in `agents/tasks/LJ-1-301/`, building the descent for
  `[LJ-1.8]`. Do not touch it.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  load beside every absolute figure.
- Never `src/Everything.lagda.md`, never `dev/ledger.toml`, never
  `dev/PLAN.md`, never `src/L/Choice/Name.lagda.md` (DD23).
- **Create `agents/tasks/LJ-1-304/lj-1.304-report.md` in your FIRST five
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

**DD8. Name the widest unmeasured term and the probe that measures it.**
`[LJ-1.302]` named this one. **You are the probe.**

**P-l. A construction delivered at one carrier is a HYPOTHESIS at another.**
**The whole route rests on this, three times over, and each time so far the
transfer was cheaper than feared. Do not let that make you optimistic here.**

**C-45. Audit the INSTANTIATION, never the telescope.**

**C-36. A failed substitution is not a proof of impossibility.**

**C-44.** Every figure here is another report's.

**R-41, written today.** **Depth is free and MIXED SPELLING costs**, gated at
depth 4: 219 ms at 2, 9,286 at 3, 419,218 at 4. **If a conversion is slow, look
for a type and a body naming one object two ways first.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Three times now the generic port has paid**: `[LJ-1.238]`'s `GenSequence` made
`[LJ-1.297]`'s ambient supply six lines instead of a chapter; `[LJ-1.298]`
measured zero changed lines; `[LJ-1.302]` measured the seven ties as ONE debt.
**Say whether these two modules pay the same way or are the exception**, and
**NAME YOUR AXIS** (C-46): this is the port's L-against-ambient axis, the
SUBJECT here and not a label.

## ARCHIVE (DD18)

`agents/tasks/LJ-1-302/lj-1.302-report.md` read WHOLE, especially section 4 and
what its number does not cover. `agents/tasks/LJ-1-298/lj-1.298-report.md` for
the clean-family rate. `agents/tasks/LJ-1-297/lj-1.297-report.md` for the six
readings, the comparable. `archive/dev/TASKS-archived.md`, taking SHAPE and never
a claim: `[LJ-1.52]` drew this decomposition and proved its top. Return an
**ARCHIVE USED** section naming ONE line read per archived file.

## LITERATURE (DD18)

**`[LJ-1.297]` MEASURED that Devlin needs no bridge of this kind at all.**
**So say where the bounded-to-unbounded obligation comes from, if not the
mathematics**, and whether that means the port introduced it. Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-302/lj-1.302-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-304/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **OPEN the full entry for any law you act on.**

- **D-1, DD8, P-l, C-45, C-36, C-44, C-42, C-50, R-41.**
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **P-h, P-i, P-k, P-m, P-n, P-t, P-y, R-34, R-35, R-40. C-12, C-22, C-32,
  C-38, C-39, C-40, C-49. I-5. DD0, DD18, DD24, D-26.**

## RETURN

**Lead with the ONE number for both modules and its basis.** Then what each
needs at the ambient carrier, at `file:line`. Then the one you BUILT, with its
lines and seconds. Then whether either is a site fact rather than mathematics.
Then the DD4 answer with its axis. **Mark every negative MEASURED or INFERRED.**
