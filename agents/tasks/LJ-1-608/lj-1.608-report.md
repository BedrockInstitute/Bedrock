# LJ-1.608 report: ingredient (iv) at the limit, in a frame that fits under the cap

## Verdict

GO. The term `rec-graph-at-infinite` is in
`agents/tasks/LJ-1-608/Probe608.agda` and it typechecks. At a strictly
infinite member stage, ingredient (iv)'s recursion has a graph exactly
when the member stage's own recursion does, and the graph is the SAME
formula, verbatim. The branch adds no atom of its own: its value is
the composed IH at the member stage, embedded by the membership-fiber
embedding, and the object language cannot see the embedding, because
its equality and membership read underlying sets.

This report was written as a skeleton before any Agda ran, and filled
as runs landed (C-22). No file was written under `src/`. No postulate
and no hole is in the delivered probe. I did not commit and I did not
push.

## THE OBLIGATION, AND THE ONE CHOICE I MADE

The brief names a route and a question, not a type, exactly as
`[LJ-1.601]`'s brief did. The type is stated in
`agents/tasks/LJ-1-608/runs/W3.agda` and discharged in
`agents/tasks/LJ-1-608/Probe608.agda`, in `[LJ-1.597]`'s `Graph`
shape (`agents/tasks/LJ-1-597/Probe597.agda:269`): a `Formula S 2`,
value variable first and index second, both directions.

The one choice: the type takes the member stage's OWN graph as a
hypothesis (`W3.Site.At.IHGraph`), and the obligation returns the
branch's graph from it (`W3.Site.At.RecGraph∞`). The subject is the
branch's value at a strictly infinite member stage, which the source
itself states as `comp-inj (IH δ δ∈α oδ δ∈suc infδ)
(Emb.emb α oα δ δ∈α)`, the `inr (inr)` row of the branch's
trichotomy (`src/L/StageCardinal.lagda.md:555-556`). "Strictly
infinite" means `ω ∈ˢ δ`, which is the hypothesis `W3.InfIdx` carries.
Why this choice, and not an unconditional graph: the value equation's
only handle on `IH` is its type, the arity-2 syntax cannot name an
arbitrary function's graph (terms are variables and constants only,
no substitution and no weakening, `src/FOL/Syntax.lagda.md:157`), and
the arity-3 `Def` route that `V = L` gives does not convert to
arity-2 (`agents/tasks/LJ-1-597/review-of-step-graph.md:70-74`). The conditional form is the strongest statement the tree can
build at this site, and it is the measurement the ingredient needs:
it prices what (iv) CONTRIBUTES at the limit, which is nothing.

## THE FLOOR

Peak RSS first, seconds second. Every run under the program's
`GHCRTS=-A64m -I0 -M2g`, one Agda process at a time, caps recorded
inside each `.out` file. No run hit a cap. No run hit the heap cap.
The highest peak RSS of the whole task is 388,956,160 bytes
(370.8 MiB), which is 18 percent of the 2 g caliber.

| stage | peak RSS | seconds | run |
|---|---|---|---|
| the index type alone, cold | 268,943,360 B (256.5 MiB) | 0.79 | `runs/w3idx-1.out` |
| the statement alone, cold | 342,507,520 B (326.6 MiB) | 1.12 | `runs/w3-1.out` |
| the floor: every row complete, the obligation a hole, exit 42 at the hole and nowhere else | 320,503,808 B (305.7 MiB) | 1.05 | `runs/floor-1.out` |
| the delivered term, cold | 349,011,968 B (332.8 MiB) | 1.18 | `runs/final-2.out` |
| the delivered term, warm | 312,246,272 B (297.8 MiB) | 0.96 | `runs/final-3.out` |
| the delivered term, warm | 312,246,272 B (297.8 MiB) | 0.99 | `runs/final-4.out` |
| the delivered content after the last prose edit, cold | 388,956,160 B (370.8 MiB) | 1.32 | `runs/final-5.out` |
| the statement alone after its last prose edit, cold | 305,184,768 B (291.0 MiB) | 0.94 | `runs/final-6.out` |

The floor is the whole price. The obligation's assembly over the floor
costs 0.13 s and 27.2 MiB, and the term went through on the first
complete attempt. The frame is the price, and this frame is small
because it imports no predecessor probe at all: the three one-line
lifts are re-typed in `runs/W3.agda` per `[LJ-1.561]`'s discipline,
which `[LJ-1.597]` measured as the cheap move
(`agents/tasks/LJ-1-597/Probe597.agda:89-92`).

`[LJ-1.603]` hit the heap wall on this same obligation at 27.18 s,
exit 251, and left no probe and no report
(`dev/pod/transitions/2026-08.jsonl:3592`, heap_wall true; its
directory holds the brief and an empty `runs/` only). That wall was
the frame, not the term: nothing in this obligation needs a
predecessor probe's elaboration, and a frame that pulls none fits
under the same caliber with the whole term green. This is the
restructure the owner's ruling of 2026-08-23 orders, tested under the
same cap, and it is the difference between the two dispatches.

The caps I set and ran under: 120 s for the index type alone (the
brief's two-minute W3 cap), 300 s for the statement, the floor, every
final run, and the witness check.

## DOES (iv) REACH sq

No, at (iv)'s own rows: the branch's value at a strictly infinite
member stage is two calls, `IH` at the member stage and the
membership-fiber embedding, and `sq` is applied in neither
(`src/L/StageCardinal.lagda.md:555-560`); the probe's whole value
equation is one `fiber` equation and names no `sq`. Yes, one unroll
down, and that arrival is `[LJ-1.594]`'s already-counted ingredient
(iii), not a new one: with `IH` the real `∈`-induction, the
recursion this term hands to is the step at `δ`, whose value equation
packs `B.pair m (cnt m φ) ≡ y` with `B = Bound α oα infα
(sq α α∈suc infα)` (`src/L/StageCardinal.lagda.md:283`, `:322`), and
that reading is a reading of the source, not a proved row of this
probe, which keeps `IH` abstract.

So this is not a sixth arrival at the parameter. (iv) is transparent
at the limit, and the circle `[LJ-1.605]` closed is still reached
only through ingredient (iii) at each stage's own step.

## THE MEASUREMENT

What I measured: whether the graph of ingredient (iv)'s recursion at
an infinite member stage reduces to what the member stage's own
recursion carries. The answer is yes, with the strongest possible
shape: the formula transfers VERBATIM. The reason is in the object
language: satisfaction reads equality and membership on underlying
sets, and the embedding changes presentations only, so the branch's
value and the member stage's own value have the same underlying set
(`Probe608.agda` section 1.2, one `fiber α ... .snd` row).

The term, in one line each. `comp-fst` (section 1.1) reads the
composed pair's function part by casing, the campaign's discipline
for projections of computed pairs. `val-eq` (section 1.2) is the one
value row: `⟪ α ⟫↪` of the branch's value equals `⟪ δ ⟫↪` of the
member stage's own value, by `comp-fst` and the fiber equation. The
obligation (sections 2 and 3) returns the hypothesis's own `ψ` with
`defines` transported along `val-eq` and `only` along its `sym`.

No row puts `step`, `branch`, `stage-card-upper` or `ord-tri` into a
conversion problem, and no row computes a `leastOf`, a tally, a
`defSet` or any `sq`. The delivered probe carries no hole and no
postulate, `--safe` is on, and the witness meter's own construction
resolves the obligation: I built the meter's witness file the way
`scripts/pod/witness.py` derives it, ran it once under the same
caliber and cap, and it is green (`runs/witness-1.out`, exit 0,
1.04 s, 328,253,440 B), and green again on the frozen content
(`runs/witness-2.out`, exit 0, 1.07 s, 328,237,056 B). The test
witness files themselves were removed after each check; the program
writes its own under `.pod-state/witness/`.

Estimates against actuals: the brief estimated about 170 lines in the
probe, of which about 45 the obligation. Actual: `Probe608.agda` is
184 lines, of which the obligation assembly is 48 (section 2's 29 and
section 3's 19). The W3 index type is 2 lines of code in a 30-line
file with the pane, and it typechecked alone in 0.79 s under the
120 s cap. The heap, not the line count, was the risk, and the high
water mark is 18 percent of the caliber.

## WHAT IT RETIRES OR RE-PRICES

Ingredient (iv) of `[LJ-1.594]`'s table is now fully accounted at both
of its layers, as `[LJ-1.597]`'s review split them: the tally at
finite member stages is `[LJ-1.601]`'s GO table, and the recursion at
strictly infinite member stages is this task's GO verbatim transfer.
The ingredient contributes no atom of its own anywhere. What remains
of the step's graph is ingredients (i) and (ii), already internal,
(iii), inside the circle, and (v), the coded copy, untouched by this
task.

This also re-prices `[LJ-1.597]`'s reopener route for the owner: the
order it names, (v) first then (iv) through `L.Recursion`'s
`Definition`, now meets an (iv) that is paid at both ends and a
remaining price that is (v) and (iii) alone.

## D-10, the statement's truth, priced before the proof

Three readings of the brief's obligation were priced before any term
was built. The unconditional reading, an arity-2 graph of the branch's
value for abstract `IH`, has no building route in the tree: the
syntax cannot name an arbitrary function's graph, and the arity-3
`Def` that `V = L` gives does not convert to arity-2, so this reading
is not false but unbuilt, the same gap `[LJ-1.597]` measured. The
real-recursion reading, `IH` the `∈`-induction, reduces to the step's
graph at the member stage, which is `[LJ-1.597]`'s NO-GO shape with
ingredient (iii) blocking. The reduction reading, this task's, is true
and provable, and the proof is one fiber equation. I stated the third
and say the choice here; if the mathematician intended one of the
other two, the type is eight lines to restate and the boundary below
names what each would cost.

## The boundary of the measurement

1. The subject is the branch's VALUE at the strictly infinite member
   stage, the `inr (inr)` row's own term. The tie from
   `fst (branch α oα α∈suc infα IH m)` to that term is not writable in
   the tree: `ord-tri` is a well-founded induction
   (`src/L/Ordinal/Linear.lagda.md:136-137`) and no row eliminates it,
   which is why `[LJ-1.597]` kept `branch` type-only. The probe states
   the subject as the row's term, with the source's own reading
   (`src/L/StageCardinal.lagda.md:495-496`) as the warrant.
2. "Infinite member stage" has a second case, `δ = ω`, whose value is
   a `subst`-transported composition
   (`src/L/StageCardinal.lagda.md:549-554`). Strict infinitude
   excludes it, and it is not measured here. It is one more
   measurement of the same shape, at a transport, and it is not
   priced.
3. The hypothesis is the member stage's own graph at exactly the call
   the source's row makes, `IH δ δ∈α oδ δ∈suc infδ` with `infδ`
   derived from the strict-infinitude witness. The composed injection
   with the `ω`-embedding, which `[LJ-1.601]`'s boundary item 2 names
   at finite stages, is likewise not this task's term.
4. `IH` stays abstract. Nothing here is measured about the real
   `∈`-induction's graph, and the one-unroll reading in the `sq`
   section is marked as a reading for that reason.
5. No equivalence between the arity-2 shape and `[LJ-1.568]`'s arity-3
   `Def` is claimed, and none exists to write
   (`src/FOL/Syntax.lagda.md:157`).

## What the next brief needs

What the statement cost: one fiber equation over a frame that imports
no predecessor probe, 1.05 s floor and 1.18 s delivered, 332.8 MiB
peak. What the shape resisted: nothing. One bracket typo of mine (a
wrong Unicode closing bracket) and one application-arity error (the
`P δ` telescope) were the only failures, both mine, both fixed in
place; the three intermediate failed invocations wrote their errors
into `runs/w3-1.out` before the green run on the fixed content
overwrote it, so those failures are recorded here and not on disk.
What I had to weaken: nothing. The reduction statement was taken
whole and inhabited whole.

What could not close: the `δ = ω` case of the limit, and the tie from
`branch` itself, both in the boundary above with their prices named as
unmeasured. If the next brief wants (iv) closed over the whole
trichotomy, it needs the `δ = ω` transport row, and that is the only
piece left.

## W2

The rule: write the mathematics once at a generic carrier and
instantiate it. `comp-fst` is polymorphic in all three types. The
obligation is stated at every `(α, IH, m, ω∈δ)` with no
carrier-specific constant anywhere: the formula is the hypothesis's,
whatever it is, and the term is pure transport along one equation.
Any second site that ever consumes this reduction consumes this same
term. No deadline forced a fixed form, so no conflict is reported.

## ARCHIVE USED

The corpus search named five candidates. One was read, four declined.

- `archive/dev/LJ-dispatch-index.md`: READ, line 142, the `[LJ-1.75]`
  row: "| LJ-1.75 | Give each partial only the facts its rows use |
  43 of 69; 122.45 s | Better than proportional: 41.6 pc cheaper for
  a 37.7 pc smaller telescope. Two partials plus composer, 273.88 s
  |". It is the trimmed-telescope premise the brief's TRIM paragraph
  cites, and this task applied the method by importing no predecessor
  probe at all.
- `archive/dev/JOURNAL-archived.md`: not read. This task retires no
  module and writes no archive row, and no live duty pointed at a
  retired journal.
- `archive/dev/JOURNAL.md`: not read, same reason.
- `archive/dev/ORCHESTRATION.md`: not read. It is a retired rulebook;
  the rules that bind this task are in `AGENTS.md` and the slot file.
- `archive/dev/DECISIONS-archived.md`: not read. The rulings that
  bind this task were given in the standing instructions and the
  brief, and no decision history was needed to state or discharge the
  type.

## LITERATURE USED

The corpus search named five candidates. This task used none of them:
the measurement is a term in the tree, and the reading that predicted
GO is the tree's own source and probes. Each decline is below.

- `dev/literature/devlin-II5.md`: declined. The reduction is proved
  here as a term, not cited, and no external construction was needed
  for a one-equation transport.
- `dev/literature/digest.md`: not read. No digest entry was needed to
  state, prove or price the transfer.
- `dev/literature/terms-2026-08.md`: not read. This task fixes no
  translation term.
- `dev/literature/truncation-and-selection.md`: not read. It serves
  `[LJ-1.597]`'s reopener item 3, the truncated route, and this task
  took the remainder of item 2, which names no literature.
- `dev/literature/level-formula-slot-roles.md`: not read. This task
  fixes no Levy grade and no level slot.

## Run ledger

Every run below is one Agda process at a time, under the program's
`GHCRTS=-A64m -I0 -M2g`, with the cap recorded inside each `.out`
file. `w3idx-1` ran on `runs/W3.agda` while that file held the index
type only. Three earlier invocations of the statement-alone run on
intermediate contents failed at my own parse and type errors and
their output was overwritten by the green run recorded here; no
measurement of the term's price was affected.

| run | what | exit | peak RSS | seconds |
|---|---|---|---|---|
| `runs/w3idx-1.out` | W3 index type alone, cold, cap 120 s | 0 | 268,943,360 B | 0.79 |
| `runs/w3-1.out` | full statement alone, cold, cap 300 s | 0 | 342,507,520 B | 1.12 |
| `runs/floor-1.out` | every row complete, obligation a hole, cap 300 s | 42 | 320,503,808 B | 1.05 |
| `runs/final-1.out` | term, cold, obligation inside `Rows`, an intermediate shape | 0 | 345,899,008 B | 1.17 |
| `runs/final-2.out` | delivered content, cold, cap 300 s | 0 | 349,011,968 B | 1.18 |
| `runs/final-3.out` | delivered content, warm | 0 | 312,246,272 B | 0.96 |
| `runs/final-4.out` | delivered content, warm | 0 | 312,246,272 B | 0.99 |
| `runs/final-5.out` | delivered content after the last prose edit, cold, cap 300 s | 0 | 388,956,160 B | 1.32 |
| `runs/final-6.out` | statement alone after its last prose edit, cold, cap 300 s | 0 | 305,184,768 B | 0.94 |
| `runs/witness-1.out` | the witness meter's own derivation, cap 300 s | 0 | 328,253,440 B | 1.04 |
| `runs/witness-2.out` | the same, on the frozen content | 0 | 328,237,056 B | 1.07 |

`final-1` was green with the obligation inside `Rows`; the witness
meter resolves obligations from the probe's top level, so the
obligation was lifted to a top-level declaration delegating to
`Rows.the-graph`, and `final-2` to `final-4` are that content.
`final-5` and `final-6` follow the last edit of the two files' header
prose, which corrected source line citations and changed no code.
The probe is frozen at the content `final-5` checked, and the
statement at the content `final-6` checked.

The write scope holds `Probe608.agda` (184 lines), `runs/W3.agda`
(158 lines), `runs/run.sh` (19 lines), eleven `.out` files, and this
report. The scope's `review-of-rec-graph-at-infinite.md` is not
written: that name is the stop path, and this return is GO, so no
stop is stated.
