# LJ-1.72: repair TwelveAgree's telescope, and prove it by consuming it

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.72-report.md`.

## 0. THE VERDICT

**`SatGraphAgree` does NOT instantiate `TwelveAgree`. The master
heap-walls at the C-12 cap. The obstruction is cost, not
inhabitation. MEASURED.**

The statement repair is built and is sound in isolation. The per-row
telescope checks green at 133 s (cold, C-12 caliber, `src/ProbeLJ172CUT1.lagda.md`).
The union frame's forty new facts check green at about 130 s (`src/ProbeLJ172CUT2a.lagda.md`).
The instantiation walls: `module Twelve` applies `TwelveAgree` at
`(f ∷ e ∷ d ∷ γ)` (`src/L/Condensation.lagda.md:7040-7041`), and the
module application re-elaborates `TwelveAgree`'s where-block (the
twelve row applications) at the graph frame's cons-env. That
elaboration exhausts the 8 GB cap in about 210 s for the isolated
application (`src/ProbeLJ172CUT2c.lagda.md`) and in about 1003 s for
the full master. The where-block copy is the measured cause: an
empty-body copy of the same telescope, applied with the same
sixty-nine arguments, checks green in about 105 s
(`src/ProbeLJ172CUT2tel.lagda.md`).

`twelve-out` and `twelve-back` HAVE left `SatGraphAgree`'s telescope.
They are no longer parameters (`src/L/Condensation.lagda.md:6793-...`),
and `body-out`/`body-back` use `Twelve.out`/`Twelve.back`
(`:7115`, `:7167`). That part of the repair is present. The master
does not typecheck because the application walls; the acceptance test
does not go through.

Every fact of the repaired telescope IS inhabited at the frame that
uses it, as written. All sixty-nine facts are supplied by the frame:
twenty-seven by the lifted `KFacts` record, two by the frame's
existing parameters, forty by the new union parameters. The supply is
complete in the master's text; the machine cannot check it because
the application walls. The finding is the wall, not a missing fact.

Per the pre-fixed abort criterion (D-1): the instantiation does not go
through. This dispatch ends at the instantiation. No measurement of
the gate's ratio runs, because the master cannot typecheck
(`check-ratio` measures a green module). `levelIn`, `cover`, the
post-leaf five and `LeafAgree`'s own consumption are untouched.

The load average was 4 to 10 during the isolation measurements, and
43 at the start of the final master run. Every absolute figure
carries the caveat; the wall verdict does not depend on load.

## 1. THE REPAIR

### 1a. The per-row telescope (built, green)

`TwelveAgree`'s universal `tagEq` and `numK` are replaced by twelve
`tagEq0`..`tagEq11` fields and twelve `numK0`..`numK11` fields,
exactly the `KFacts` shape (`src/L/Condensation.lagda.md:6428-6451`).
Each row's numeral is hard-coded: `tagEq0` pins slot `N0` to
`numeralL 0`, `tagEq11` pins slot `N11` to `numeralL 11`, and the
twelve applications pass the per-row fields (`:6636-6667`). The
over-general `tagEq` type (`[LJ-1.71]`'s refutation) no longer
exists. `src/ProbeLJ172CUT1.lagda.md` checks green.

### 1b. The graph frame's union telescope

`SatGraphAgree`'s telescope gains the forty union facts
(`valK` at `src/L/Condensation.lagda.md:6803` through `consK-allin`
at `:6958`), stated at the graph frame `(f ∷ e ∷ d ∷ γ)` exactly as
`TwelveAgree`'s telescope states them at its own frame, so every
argument of the application is a definitional match. None is derived
from the frame's existing facts: they are site facts about arbitrary
values in `K`, and the frame's hypotheses do not constrain those
values (INFERRED absence, unchanged from `[LJ-1.71]`). The frame now
carries 75 fact parameters (35 before, 40 added). `LeafAgree` carries
the same forty as pass-through parameters and supplies them to its
`SatGraphAgree` application (`:7468-7480`); its own theorem statements
(`out`/`back`) are unchanged.

### 1c. The instantiation

`module Twelve (d e f : S)` applies `TwelveAgree` at
`(f ∷ e ∷ d ∷ γ)` with the sixty-nine facts
(`src/L/Condensation.lagda.md:7040-7086`), and exposes `out`/`back`
with written types. `body-out`/`body-back` use `Twelve.out`/`Twelve.back`
(`:7115`, `:7167`). This is the term that walls.

## 2. INHABITATION AT THE FRAME

The repaired telescope has sixty-nine facts. Each is supplied at the
frame:

| facts | supplier |
|---|---|
| `tagEq0`..`tagEq11`, `numK0`..`numK11`, `innerK`, `pairK`, `num1K` (27) | the lifted `KFacts` record `lift3 d e f` at the six-lifted slots |
| `codesK`, `codesK-un` (2) | the frame's existing `codesK`, `unCodesK` parameters |
| `valK` .. `consK-allin` (40) | the forty new frame parameters |

The suppliers' types are definitionally the telescope's types at
`(f ∷ e ∷ d ∷ γ)`: the frame states each fact at the graph frame, and
the telescope's type instantiated at `γ := (f ∷ e ∷ d ∷ γ)` is the
same term. The sixty-nine argument checks are definitional equalities
between the frame parameters' types and the instantiated telescope
types. No fact is missing. The inhabitation cannot be machine-checked
because the module application walls before the checks complete.

## 3. NEGATIVES AND THEIR STATUS

1. The instantiation goes through: **MEASURED FALSE**. The master and
   the isolated application heap-wall at `-M8g`. This negative sets
   the verdict.
2. The per-row telescope is unsound: **MEASURED FALSE**. It checks
   green (`src/ProbeLJ172CUT1.lagda.md`, 133 s).
3. The union frame statement is unsound: **MEASURED FALSE**. It
   checks green (`src/ProbeLJ172CUT2a.lagda.md`, about 130 s).
4. A telescope fact is uninhabited at the frame: **MEASURED FALSE**.
   All sixty-nine facts have suppliers in the frame's telescope; the
   argument types are definitional matches. The obstruction is cost.
5. The wall is the sixty-nine argument checks: **MEASURED FALSE**.
   An empty-body copy of the same telescope, applied with the same
   sixty-nine arguments at the same frame, checks green in about 105 s
   (`src/ProbeLJ172CUT2tel.lagda.md`).
6. The wall is the `someEnv` fact's `envHypB2` unfolding: **MEASURED
   FALSE**. Sealing `envHypB2` opaque and unfolding it at the eight
   row `out`/`back` definitions and the five `countFo` proofs did not
   cure the wall (`src/ProbeLJ172CUT2opq.lagda.md`).
7. The wall is the where-block copy at the cons-env: **MEASURED
   TRUE**. `TwelveAgree` with its body walls at the graph frame
   (`src/ProbeLJ172CUT2c.lagda.md`, about 210 s); the same telescope
   with an empty body is green. The row applications' satisfaction
   content at the concrete cons-env is the P-n floor.
8. `numK` is over-general in the repaired telescope: **MEASURED
   FALSE**. The universal `numK` is gone; the twelve per-row fields
   are the `KFacts` shape (`:6428-6451`).

The deciding claim of the verdict is item 1, MEASURED; its mechanism
is item 7, MEASURED.

## 4. MEASUREMENT

The abort criterion stops the dispatch at the wall, so the paired
three-run protocol of a green dispatch does not run. The measured
pieces are single cold runs, C-12 caliber
(`GHCRTS="-A64m -I0 -M8g"`, one process), warm dependencies, loads
4 to 10:

| configuration | result | seconds |
|---|---:|---:|
| per-row `TwelveAgree` (CUT1) | green | 133 |
| frame telescope only (CUT2a) | green | about 130 |
| frame + sixty-nine-argument application, body lazy (CUT2c) | **WALL** | about 210 |
| same application with empty body (CUT2tel) | green | about 105 |
| opaque `envHypB2` + application (CUT2opq) | **WALL** | about 220 |
| full master (first run) | **WALL** | about 1003 |
| full master (final timed run) | **WALL** | 757 |

The full master's pre-dispatch baseline was 122 s cold at the gate
caliber (`[LJ-1.70]`). The wall is allocation: the module application
re-elaborates the twelve row applications at the cons-env, and the
elaboration exceeds the cap. The wall is not a raiseable cap issue:
the brief fixes the cap and never raises it.

## 5. THE DD4 ANSWER

The J tower inherits the repaired telescope's shape whole: twelve
per-row `tagEq` fields, twelve per-row `numK` fields, and the
forty-fact union telescope, all stated per slot at the J tower's own
frame. The per-row shape is what lets a frame supply the facts: each
row's slot and numeral are stated separately, so a frame that carries
the twelve row facts (as `KFacts` does) can instantiate at its own
slots without a re-indexing shim. That part is measured at the L
tower (CUT1 green) and transfers by construction: the row modules are
slot-generic.

The J tower inherits the wall too, INFERRED: instantiating the
twelve-row conjunction at a concrete cons-env re-elaborates the row
applications' satisfaction content (the P-n floor), and that
elaboration walls at the L tower's own graph frame, MEASURED. A J
tower that instantiates at its own concrete frame pays the same cost.
The naming cure for `someEnv` (`someEnvDef`, `:6417`) does not change
the cost class; it was measured ineffective against the wall.

## 6. THE CONVERGENCE ANSWER

NOT CLOSING. The statement repair is built and sound in isolation:
the per-row telescope and the union frame both check green. The
instantiation does not go through: the module application's where-
block copy at the graph frame heap-walls at the C-12 cap, MEASURED.
`TwelveAgree` remains unconsumed, and this dispatch's first consumer
audit measured the cost of consuming it at the graph frame. The
repair's next step needs an owner ruling: either the where-block copy
is restructured so a consumer does not pay the twelve row
applications again at a concrete env, or the cap question is
re-opened, or the consumption moves to a variable frame with a
transport. This dispatch prices none of those; it reports the wall.

## 7. ARCHIVE USED

- `_build/lj-1.71-report.md`, read WHOLE. TOOK the refutation, the
  slot-fix confirmation and the 35-against-47 count.
- `src/ProbeLJ171A.agda`, read WHOLE. TOOK the frame shape and the
  `tagEq-refutes` evidence.
- `_build/lj-1.70-report.md`, read WHOLE. TOOK the telescope shape,
  the two heap walls and the aliases wall.
- `_build/lj-1.55-report.md`, read WHOLE, and
  `src/ProbeLJ155B.agda:788-979`, read. TOOK the slot convention.
- `_build/lj-1.62-report.md`, sections 2-3, read. TOOK `KFacts` and
  `SatGraphAgree`'s placement.
- `dev/LESSONS.md`, C-38 (`:3427-3477`), C-35 (`:3200-3242`), P-w as
  amended (`:3094-3256`), P-o (`:2509-2532`), P-t (`:2601-2632`),
  D-29 (`:3242-3284`), each read WHOLE.
- `archive/rud-route/`, SHAPE only. Took nothing.

## 8. LITERATURE USED

Nothing in the literature prices a spelling. One line, nothing spent.

## 9. GATES

`scripts/check-fences.py --check` clean (89 masters).
`scripts/lint-prose.py --check` exit 0 on the edited master.
`scripts/lint-agda.py --check` exit 0 (probe imports trimmed).
`scripts/ledger.py --brief`: standing 27,673 lines over 82 masters,
measured from HEAD.
`scripts/check-ratio.py --check` does not run: the master does not
typecheck (it walls), and the gate measures a green module.
The final timed master run: `real 757.00`, `user 753.14`, load 43 at
start (4 users). The earlier un-timed run walled at about 1003 s at
load 4 to 10. The wall is allocation, not load.
