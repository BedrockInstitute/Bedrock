# LJ-1.603 report: ingredient (iv) at the infinite member stages

## HEAD

head_slot: coder
machine: shared

verdict: NO-GO (a stop, stated as the brief prices it: the limit case
reaches `sq`, and the two ingredients merge)

obligation: agents/tasks/LJ-1-603/Probe603.agda::rec-graph-at-infinite
(NOT INHABITED; the name appears in the probe's comments only)
stop: agents/tasks/LJ-1-603/review-of-rec-graph-at-infinite.md

The report was written as a skeleton before any Agda and filled as each
run landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-603/`. Agda ran under the caliber the program set on
this pane, `GHCRTS="-A64m -I0 -M2g"` (`runs/w3-2.out:2`), ONE Agda
process at a time, every typecheck capped by the perl alarm in
`runs/run.sh` (the cap is recorded inside every `.out`). I did not set
`GHCRTS`. Nothing is postulated, the probe carries no hole, `--safe` is
on, and nothing landed in `src/`. Every file of this task is a raw
`.agda`, a `.sh` or a `.md`, so none carries an ` ```agda ` fence, all
count 0 in-fence lines, and the ratio bar cannot fire on them.

## VERDICT

**NO-GO on `rec-graph-at-infinite`, and
`agents/tasks/LJ-1-603/review-of-rec-graph-at-infinite.md` states it.**
The probe is GREEN, EXIT 0, cold at 110.14 s and warm at 1.27 s
(`runs/final-8.out`, `runs/final-9.out`, cap 300 s, peak 898 MB under
the pane's 2 GB). No term named `rec-graph-at-infinite` is in it, and
no weaker term is offered under that name.

**THE NO-GO IS THE ONE THE BRIEF PRICED AS EQUAL IN VALUE: the limit
case REACHES `sq`.** The value equation of ingredient (iv)'s recursion
at an infinite member stage carries the bare pairing parameter at that
stage in the ONLY occurrences of the value, TWICE: the outer pack and
the count's inner packs. That is the FOURTH arrival at `sq`, now from
the member stages, and it MERGES ingredients (iii) and (iv) into one
problem: the count IS ingredient (iv), and its own packing is an
application of ingredient (iii)'s parameter. A definable pairing at the
ordinal stages is the one route that serves both.

`[LJ-1.601]`'s GO stands, at the finite member stages only. The two
halves do not join, and the probe's section 2 is the honest record of
that: `[LJ-1.601]`'s table term, imported, at its own type, beside this
task's finding that the other half is `sq`-bound.

## D-10, THE TARGET'S TRUTH, PRICED BEFORE ANY AGDA

The brief asks first what the recursion does at an infinite member
stage that it does not do at the finite base, and says: if the answer
is nothing but the index, finish early as a transcription. **The answer
was priced BEFORE any Agda was written, and it is NOT the index. It is
the PACKING.** At the finite base the value at a member is `numeralω
(least x x∈)`, a numeral, no `sq` in the value equation
(`src/L/StageCardinal.lagda.md:459`). At an infinite member stage the
value is the ordinal-least `y` with `class-pred x y`
(`src/L/StageCardinal.lagda.md:349-351`), and `class-pred`'s second
conjunct is `B.pair m (cnt m φ) ≡ y` with `B = Bound δ oδ infδ
(sq δ δ∈suc infδ)` (`:283`, `:319-323`), while `cnt` packs the code of
the formula through the same `pair` (`:124-128`). The prediction from
this reading was NO-GO, and the seven `refl` rows of the probe's
section 1 confirmed it at the predicted shape. The truth of the wider
target is not in question: `V = L` gives it
(`agents/tasks/LJ-1-594/Probe594.agda:135-152`), and this task re-runs
none of that.

## WHAT CHANGES AT THE LIMIT

At `src/L/StageCardinal.lagda.md:459`, the finite base's value is the
numeral of the least tally index: `h x x∈ = numeralω (least x x∈)`. At
`src/L/StageCardinal.lagda.md:319-323`, the infinite member stage's
value is selected by `class-pred`, whose every witness is packed
through `B.pair m (cnt m φ)` with `B` instantiated at `sq δ δ∈suc infδ`
by `src/L/StageCardinal.lagda.md:283`. At `src/L/StageCardinal.lagda.md:124-128`,
`cnt`'s own value is `pair (numeral k) (pair (pair (numeral (code ψ))
(numeral n)) (tuple-g g k cs))`, the same `pair` again. **So the move
from the finite base to the limit is a move in the VALUE EQUATION's
packing, from a numeral to a double `sq`-application, and not a move in
the index.** The probe measures this chain by `refl` at the member
stage: rows `class-pred-at-member` (the outer pack, with the value on
the `sq`-application side only), `pair-is-sq-at-member` (the pack IS
`sq` applied), and `count-bound-is-sq-packs` with `formula-bound-is-count`
(the inner packs).

## DOES (iv) REACH sq

YES. The recursion's value equation at an infinite member stage reaches
`sq δ δ∈suc infδ` at `src/L/StageCardinal.lagda.md:322` (the outer pack)
and at `:124-128` through `:283` (the count's inner packs), measured by
rows 1.3, 1.4 and 1.7 of the probe. This is the fourth arrival at the
bare parameter `src/L/StageCardinal.lagda.md:17-20`, after `[LJ-1.572]`,
`[LJ-1.594]` and `[LJ-1.597]`, and the first from inside the count.

## THE MEASUREMENT

The statement was written FIRST and typechecked ALONE: `runs/W3.agda`
carries `InfStage` (the limit case's own index, the widest unmeasured
term), the lifts, the subject `val`, and `RecGraphInf`, the obligation's
type in `[LJ-1.597]`'s fixed `Graph` shape. It is GREEN at 1.42 s, cap
120 s (`runs/w3-2.out`).

**ONE HEAP WALL WAS MET AND ROUTED IN THIS DISPATCH, NOT REPORTED AS A
FINDING.** The first spelling of the index, a five-field RECORD, walls
the pane's 2 GB cap: `runs/w3-1.out` (the full slice), `runs/bisect-a.out`
(record, statement removed), `runs/bisect-b.out` (record + the branch
type + the step function), `runs/bisect-c.out` (the record ALONE), all
"Heap exhausted" at 2048 MB, 24 to 28 s. The restructure the clause
orders was built and tested under the same cap: the SAME five components
spelled as a Sigma, projections named once, GREEN at 1.32 s
(`runs/bisect-d.out`), and the delivered slice GREEN at 1.42 s. **The
record spelling of a statement's index is a presentation cost the pane
cannot carry; the Sigma is the atom.** That is this dispatch's own
measurement at its own site (P-l read here), and it is why
`runs/W3.agda` carries the Sigma.

**THE FLOOR WAS MEASURED BEFORE THE ROWS**, per the owner's ruling of
2026-08-23: `runs/floor-1.out` is the probe's frame without the
value-equation rows (imports, `[LJ-1.601]`'s term, the type rows),
GREEN at 11.27 s. The delivered probe runs 110.14 s cold, and the rows
1.1 to 1.3 carry the cost: alone on the same frame they run 113.22 s
(`runs/bisect-g.out`). So the price is the written-out `class-pred`
type at the member stage, exactly as it was at the ambient stage for
`[LJ-1.594]`. The imports were then trimmed to the rows' own use
(`FOL.Absoluteness`, `V.Presentation`, `isL`, `isL-trans`, `S` removed):
the trim saved 40 MB and no time, and the delivered content is green
after it (`runs/final-8.out`, `runs/final-9.out`).

One error of mine is on record: `runs/final-1.out`, exit 42, a missing
module argument to `SC.Bound.numeral` in row 1.7 (the argument slid
into the pairing slot and left a function behind). The isolated arm
`runs/bisect-e.out` found it (with the hole arm `runs/bisect-f.out`
reading the goal), and one edit fixed it. No run was repeated unchanged
in the hope of a different result; every retry followed an edit.

The caps I set: 120 s for every W3 and bisect arm, 300 s for the floor
and every run of the full probe. No run reached a cap.

## WHAT THE NEXT BRIEF NEEDS

The merge is the deliverable. Ingredient (iv) at the infinite member
stages is not a separate debt from ingredient (iii): its value equation
applies (iii)'s parameter at every pack, outer and inner. So the
cheapest next dispatch is NOT another half of (iv) (there is none left:
the base is `[LJ-1.601]`'s GO, the limit is this file's `sq`), and not
(v) alone, but the ONE object that serves (iii) and (iv) together: a
definable pairing at the ordinal stages, `[LJ-1.584]`'s route 2
(`agents/tasks/LJ-1-584/lj-1.584-report.md:195-197`). With it, the
probe's rows 1.3 and 1.7 become formula-expressible and the residue is
`[LJ-1.594]`'s order: (v) the coded copy at the carrier first, which
must name the STAGE that holds `AllCodes`
(`archive/dev/LJ-dispatch-index.md:160`), then (i) and (ii), already
internal.

Two operational facts for that dispatch. First, the statement's index is
now `W3.InfStage` (`runs/W3.agda:113-131`), Sigma-spelled: a brief that
restates it as a record re-buys the 2 GB wall. Second, the value
equation rows at the member stage cost about 101 s over the frame under
this pane's caliber, all of it in the `class-pred` type's elaboration;
a probe that needs those rows twice should import them, not restate
them.

What the shape resisted: the index, not the equation. The equation went
through at the price the reading predicted. What I had to weaken:
nothing. The statement was taken whole and the stop is stated against
it, with no weaker term under the obligation's name.

## BRIEF DEFECTS, REPORTED WITH EVIDENCE

1. **Premise 11 cites a rule that does not exist.** "R-42 rules the
   respelling cost. Basis: dev/LESSONS.md:4404." `grep -rn "R-42" dev/`
   returns nothing; the highest R-number in `dev/LESSONS.md` is R-41
   (`dev/LESSONS.md:41-42`), and line 4404 is C-53's related-names
   line. The numbers the brief attaches to it, "1.74 s against
   155.02 s", appear as a pair nowhere in the tree. The instruction the
   premise carried (import, do not restate) stands on its own and was
   obeyed; the citation does not check.
2. **The first of the three prior `sq` arrivals has no directory.**
   `agents/tasks/LJ-1-572/` does not exist at this tree. This was
   already measured by `[LJ-1.584]`
   (`agents/tasks/LJ-1-584/lj-1.584-report.md:205-210`), whose rows are
   in `dev/pod/table.toml` today at `:21970-21987` (the table has shifted
   since `[LJ-1.584]` cited `:19146-19160`). My "fourth arrival" claim rests
   on the two arrivals I could open, `[LJ-1.594]` and `[LJ-1.597]`, and
   on the brief's word for the first.

## W2

The brief's rule: write the mathematics once at a generic carrier and
instantiate it. The probe's section 1 is generic in everything the site
allows: every row is stated at an ARBITRARY member stage δ with `D`,
`inv` and the branch `ih` abstract, and rows `formula-bound-is-count`
and `count-bound-is-sq-packs` are polymorphic in the carrier `K`. The
same rows serve any stage, ambient or member, and both proofs that will
ever consume them. The statement itself is the campaign's fixed `Graph`
shape at the site the brief named, which is not mine to generalize. No
deadline forced a fixed form, so no conflict is reported.

## ARCHIVE USED

The corpus search named five candidates. Two were read and are cited in
this task's records; three are declined below.

- `archive/dev/LJ-dispatch-index.md`: READ, at `:160`, quoted in the
  stop file's reopen section: "`| LJ-1.86 | Is there a stage containing
  AllCodes A | EXISTS; proof cannot choose it | AllCodes-stage is green.
  But lam is a module parameter at every frame, so the obligation moves
  to the frame |`". A brief that orders ingredient (v) must name the
  stage, and this row is the measured reason.
- `archive/dev/JOURNAL.md`: READ, at `:1366`: "pricing. **That endomap
  on `sq δ` is now the widest unmeasured term, and". The JOURNAL's
  `sq δ` residue record is the predecessor of the arrival this task
  measures; it confirmed the atom's history before the probe was
  written.
- `archive/dev/JOURNAL-archived.md`: not read. No duty of this task
  pointed at a retired journal volume beyond the live one above.
- `archive/dev/ORCHESTRATION.md`: not read. The dispatch protocol is
  `dev/memos/LJ-4-pod-program-design.md` and the standing instructions;
  no orchestration history was needed to state or to stop this
  obligation.
- `archive/dev/DECISIONS-archived.md`: not read. The rulings that bind
  this task were given in the standing instructions and the screen.

## LITERATURE USED

The corpus search named five candidates. One was read, at one line, to
carry a predecessor's citation forward; four are declined.

- `dev/literature/truncation-and-selection.md`: READ, at `:83`:
  "**So a proof that only needs cardinal arithmetic never needs an
  injection as data, and the untruncation question does not arise in
  the classical texts.**" The stop file's reopen section carries
  `[LJ-1.597]`'s pointer to this line; the line was checked at its
  source.
- `dev/literature/devlin-II5.md`: not read. The merge this task reports
  rests on measured `refl` rows in the tree, and no Devlin fact was
  needed to state, to prove or to price them.
- `dev/literature/digest.md`: not read. No digest entry was needed; the
  stop's atoms are the campaign's own four arrivals.
- `dev/literature/geology.md`: not read. No layering question arose:
  this task measured one ingredient at one site.
- `dev/literature/terms-2026-08.md`: not read. No term was proposed and
  none is missing from the records this task wrote.

## Run ledger

Every run below is one Agda process at a time, under the program's
`GHCRTS=-A64m -I0 -M2g`, with the cap recorded inside each `.out` file.

| run | what | exit | price |
|---|---|---|---|
| `runs/w3-1.out` | W3, record spelling | 251 | 24.69 s, heap wall |
| `runs/bisect-a.out` | record, statement removed | 251 | 26.22 s, heap wall |
| `runs/bisect-b.out` | record + Ih + step-fn | 251 | 28.49 s, heap wall |
| `runs/bisect-c.out` | the record ALONE | 251 | 24.97 s, heap wall |
| `runs/bisect-d.out` | the Sigma spelling + Ih + step-fn | 0 | 1.32 s |
| `runs/w3-2.out` | W3 delivered, cold | 0 | 1.42 s |
| `runs/floor-1.out` | probe frame, no section 1 rows | 0 | 11.27 s |
| `runs/bisect-e.out` | row 1.7 isolated, after the fix | 0 | 1.64 s |
| `runs/bisect-f.out` | row 1.7 with a hole, goal read | 42 | 1.44 s |
| `runs/bisect-g.out` | rows 1.1 to 1.3 alone | 0 | 113.22 s |
| `runs/final-1.out` | full probe, my numeral-argument error | 42 | 111.30 s |
| `runs/final-2.out` | full probe after the fix, cold | 0 | 112.49 s |
| `runs/final-3.out` | warm | 0 | 1.37 s |
| `runs/final-4.out` | after the import trim, cold | 0 | 112.67 s |
| `runs/final-5.out` | warm | 0 | 1.27 s |
| `runs/final-6.out` | after a header-comment edit, cold | 0 | 110.14 s |
| `runs/final-7.out` | warm | 0 | 1.27 s |
| `runs/final-8.out` | delivered content, cold | 0 | 111.89 s |
| `runs/final-9.out` | delivered content, warm | 0 | 1.44 s |

`final-8` and `final-9` postdate every edit to every file of this task.
The probe is frozen at the content those two runs checked. The edits
between `final-7` and `final-8` touched one comment's citation only
(`[LJ-1.597]`'s `pair-is-sq` line range, corrected to
`Probe597.agda:180-184`), which is `[LJ-1.601]`'s own precedent for
comment-only edits. `bisect-e`
and `bisect-f` carry intermediate states of the row-1.7 arm (the
`.out` files record their last run); the error itself is preserved in
`final-1.out`.

## The write scope, as it stands

`agents/tasks/LJ-1-603/` holds `Probe603.agda` (the delivered probe,
green, no hole, no postulate), `review-of-rec-graph-at-infinite.md`
(the stop), this report, `runs/W3.agda` (the statement slice, green
alone), `runs/Floor.agda` and `runs/BisectA.agda` to `runs/BisectG.agda`
(the bisection arms, tracked), `runs/run.sh`, and nineteen `.out`
files. Nothing else in the tree was touched.
