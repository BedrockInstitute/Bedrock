# LJ-1.601 report: the finite base, measured

## Verdict

GO. The `Tally` route HAS a formula. The term
`finite-base-measured : (n : ℕ) → W3.TallyGraph n` is in
`agents/tasks/LJ-1-601/Probe601.agda` and it typechecks. The answer to the
question `[LJ-1.597]` item 2 asked is YES, and the witness is the finite table
the route itself hands over.

No file was written under `src/`. No postulate and no hole is in the probe. I
did not commit and I did not push.

## THE MEASUREMENT

The question, verbatim, is `agents/tasks/LJ-1-597/review-of-step-graph.md:167`:
"MEASURE THE FINITE BASE. No task has measured whether the `Tally` route
(`src/L/Choice/Finite`) has a formula."

What I measured: whether the graph of the finite base
`finite-stage-inj` (`src/L/StageCardinal.lagda.md:485`) is definable, stated
in the campaign's own internalization shape. That shape is `[LJ-1.597]`'s
`Graph` (`agents/tasks/LJ-1-597/Probe597.agda:269`): a `Formula S 2`, value
variable first and index variable second, with both directions, at the
function part of the route's delivered injection, read on the members of the
finite stage. The type alone is `agents/tasks/LJ-1-601/runs/W3.agda`
(`TallyGraph`), written first and typechecked alone.

The number: the statement alone states at 2.22 s cold
(`runs/w3-1.out`, exit 0). The floor, which is the same probe with the
obligation assembly as a hole and every other row complete, is 11.57 s
(`runs/floor-3.out`, exit 42 at the hole and nowhere else). The delivered term
is green at 13.43 s cold and 1.44 s and 1.16 s warm (`runs/final-7.out` to
`final-9.out`, exit 0 each). The proof assembly cost nothing over the floor:
the floor is the frame, and the frame is the whole price.

The cap I set and ran under: 120 s for the statement alone, 300 s for the
floor and for every final run (`runs/run.sh` records the cap in each `.out`
file). No run reached a cap. No run hit the heap cap. The caliber on every run
was the program's `-A64m -I0 -M2g`. I did not set `GHCRTS` at any point.

Two runs are on record as events. `runs/floor-1.out` is exit 42 at a real
error of mine: I composed one path in the wrong order in `only-side` (a `sym`
too many), and one edit fixed it. `runs/floor-2.out` is a signal death at
11.62 s with no RTS message and no crash report of today. A direct diagnostic
run of the same command passed at once, and the recorded floor-3 and every
later run passed. I treat floor-2 as a machine transient, not a wall: nothing
was restructured for it and the identical input was not rerun in the hope of a
different result. The diagnostic run identified the signal question first.

## WHAT IT RETIRES OR RE-PRICES

This removes `[LJ-1.597]`'s reopener item 2 from the unmeasured list: the
finite base is now measured, and the answer is that the route has a formula,
given by the table term in `Probe601.agda` section 2. Ingredient (iv) of
`[LJ-1.594]`'s table is thereby re-priced downward at its base only: the
`ω`-base no longer blocks, so what remains unmeasured in (iv) is the recursion
at infinite member stages, and ingredients (iii), the pairing, and (v), the
coded copy, are untouched by this task.

## D-10, the statement's truth, priced before the proof

The reopener sentence names a route and a question. It does not name a type,
so I state what it asks at the carrier the campaign already fixed, and I say
the one choice I made. `[LJ-1.597]`'s own obligation was the graph of the
step's function part in the `Definition` shape
(`src/L/Recursion.lagda.md:272`: `dom`, `fn`, `graph : Formula S 2`, `defines`,
`only`). The same reading at the finite base gives `TallyGraph n`: the
formula's index variable ranges over members of `Lset (# n)`, its value
variable over members of `ω`, and the two directions are `defines` and `only`.
If the mathematician intended a different shape, the term delivered here is at
the stated one, and the type is eight lines to restate.

The truth was priced before the term was built, and the price said GO. The
route's tally enumerates the finite stage (`record Tally`,
`src/L/Choice/Finite.lagda.md:120`, field `onto` hits every member). A formula
may carry any element of `L` as a constant, and the internalization chapter
asks no bound on their number or grade. So the finite disjunction of "index
equals this entry and value equals that numeral" is the graph. The tree states
the dual reading itself: a stage with finitely many members has no subsets
beyond the definable ones, which is the prose under `finDisj`
(`src/L/Axioms/Basic.lagda.md:299` and the section above it). The measured
surprise is none: the term went through at the price the reading predicted.

## The term, in one line each

`Probe601.agda` imports `runs/W3.agda` for the statement, so the stated type
and the discharged type are one and cannot drift. Section 1 is three `refl`
rows that pin the value equation at this site, in `[LJ-1.594]`'s discipline:
the function part at a presentation is `FinInj.h` at the member
(`src/L/StageCardinal.lagda.md:458`), `h` is the numeral of `least`
(`:459`), and the lift reads through the `ω` presentation. Section 2 builds
the table: the tally named once, its entries and their values as constants,
the clause `(var 1 ≐ entry) ∧̇ (var 0 ≐ value)`, and the finite disjunction,
which is `finDisj` at arity 2. Section 3 is one congruence, `h` at equal
members, proved by `cong` and `J` over proof-irrelevant membership. Section 4
is the obligation: `defines` by the tally's `onto`, `only` by the same
congruence read backwards.

One design fact carries the price, and the next brief may want it: no row
forces the route. `leastOf`, the mask enumeration and `PowerStep` never
normalize in any proof row. The congruence rows move propositional equality
through proof-irrelevant membership, so the tally is read through its
specification fields and never through its construction. The elaboration frame,
which is `L.StageCardinal` instantiated at this pane's parameters plus the W3
import, is the entire 11.5 s floor.

A reading, not a proved row: the value path of the finite base names no `sq`.
`finite-stage-inj` is `FinInj.stage-inj` (`:485`), whose value is `h` (`:458`),
whose value is `numeralω (least x x∈)` (`:459`), and `least` is `leastOf
natOrder` (`:452-453`). The pairing parameter enters the step only through
`LimitStep` (`:277`, applied at `:396`), which the finite base never reaches.
The whole step's graph carries ingredient (iii). Its own base carries none of
it.

## The boundary of the measurement

1. The statement is at every numeral stage: `(n : ℕ)`. The wrapper `fin-inj`
   at a `δ ∈ ω` (`src/L/StageCardinal.lagda.md:488-489`) is the same route
   transported along the numeral witness, and it is not re-measured here.
2. The branch's value at a finite member stage is the composition
   `comp-inj (fin-inj δ δ∈ω) (WOEmb.ω-inj α oα infα)` (`:548`). The
   composition with the `ω`-embedding into `α` is not measured by this task.
3. The arity-2 `Formula S 2` shape and `[LJ-1.568]`'s arity-3 `Def` are not
   converted by any row here. The syntax carries no substitution and no
   weakening, so no such row exists to write. No equivalence between the two
   shapes is claimed, which is `[LJ-1.597]`'s own caveat, carried unchanged.
4. The formula exists for each `n` and its size is the tally's size, which
   grows with `n`. Uniform boundedness is not claimed and the chapter asks
   for none.

## What the next brief needs

The re-price of ingredient (iv) is now concrete. Its finite base is measured
GO at a 13 s cold price with no wall and no forced unfolding. What remains of
(iv) is the count at infinite member stages only, and that residue now stands
alone: `[LJ-1.597]`'s value equation at an infinite `δ` reads `cnt m φ`
through the branch, and the branch's finite case is discharged by this table.
If the next brief wants the same question at the composition (`:548`) or at
the `fin-inj` wrapper, each is one more measurement of the same shape, and
neither is priced yet.

What the shape resisted: nothing. One error of mine, one transient signal
death, no heap event, no restructure. What I had to weaken: nothing. The
statement was taken whole and inhabited whole.

## W2

The rule: write the mathematics once at a generic carrier and instantiate it.
The table machinery is generic: `bigDisj`, `bigDisj-in` and `bigDisj-out`
(section 2.4 to 2.6) are polymorphic in the clause family and are stated at no
carrier. What is at this carrier is the statement itself, which is the
campaign's fixed `Graph` shape at the site the reopener named, and the
constants `X` and `Y`, which name this route's tally. Both proofs that will
ever consume a finite table, if a second one appears, share the same three
generic rows and pay only new constants. No deadline forced a fixed form, so
no conflict is reported.

## ARCHIVE USED

The corpus search named five candidates. This task consumed none of them: its
statement came from the live reopener, its machinery from live `src/` chapters
and live predecessor probes. Each decline is below.

- `archive/dev/LJ-dispatch-index.md`: not read. The dispatch index serves
  brief-build retrieval. This task's statement came from
  `agents/tasks/LJ-1-597/review-of-step-graph.md:167`, and no archived episode
  was needed to state or to discharge it.
- `archive/dev/JOURNAL.md`: not read. It is a retired record and no live duty
  of this task pointed at it.
- `dev/ARCHIVE.md`: not read. This task retires no module, so no archive row
  was written and none was consulted.
- `archive/dev/JOURNAL-archived.md`: not read, same reason as `JOURNAL.md`.
- `archive/dev/DECISIONS-archived.md`: not read. The rulings that bind this
  task were given in the standing instructions, and no decision history was
  needed.

## LITERATURE USED

The corpus search named five candidates. This task used none of them: the
measurement is a term in the tree, and the reading that predicted GO is stated
by the tree's own chapter prose. Each decline is below.

- `dev/literature/truncation-and-selection.md`: not read. `[LJ-1.597]`'s
  reopener item 3 cites it for the truncated route, and this task took
  item 2, which names no literature.
- `dev/literature/devlin-II5.md`: declined. The finite-table fact is proved
  here as a term, not cited. The tree's own statement of the dual reading is
  the prose over `finDisj` at `src/L/Axioms/Basic.lagda.md:299`.
- `dev/literature/digest.md`: not read. No digest entry was needed to state,
  to prove or to price the table.
- `dev/literature/level-formula-slot-roles.md`: not read. The task fixes no
  Levy grade and no level slot.
- `dev/literature/geology.md`: not read. No layering question arose.

## Run ledger

Every run below is one Agda process at a time, under the program's
`GHCRTS=-A64m -I0 -M2g`, with the cap recorded inside each `.out` file.

| run | what | exit | price |
|---|---|---|---|
| `runs/w3-1.out` | statement alone, cold | 0 | 2.22 s |
| `runs/w3-2.out` | statement alone, warm | 0 | 1.19 s |
| `runs/floor-1.out` | hole, plus my path-order error | 42 | 12.10 s |
| `runs/floor-2.out` | hole, transient signal death | 1 | 11.62 s |
| `runs/floor-3.out` | hole only, the floor | 42 | 11.57 s |
| `runs/final-1.out` | term, cold | 0 | 11.56 s |
| `runs/final-2.out` | term, warm | 0 | 1.25 s |
| `runs/final-3.out` | term, warm | 0 | 1.24 s |
| `runs/final-4.out` | term after import trim, cold | 0 | 12.07 s |
| `runs/final-5.out` | warm | 0 | 1.26 s |
| `runs/final-6.out` | warm | 0 | 1.25 s |
| `runs/final-7.out` | delivered content, cold | 0 | 13.43 s |
| `runs/final-8.out` | delivered content, warm | 0 | 1.44 s |
| `runs/final-9.out` | delivered content, warm | 0 | 1.16 s |

`final-4` to `final-6` follow the removal of three unused imports. `final-7`
to `final-9` follow the last edit of the probe's header prose, which changed
no code. The probe is frozen at the content those three runs checked.

The write scope holds `Probe601.agda` (300 lines), `runs/W3.agda` (120
lines), `runs/run.sh`, fourteen `.out` files, and this report. The scope's
`review-of-finite-base.md` is not written: that name is the stop path, and
this return is GO, so no stop is stated.
