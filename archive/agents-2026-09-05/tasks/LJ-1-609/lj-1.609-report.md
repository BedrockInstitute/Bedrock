# LJ-1.609 report: face E built at the six slots

## VERDICT

**GO.** The obligation is delivered. `elem-down-at` inhabits face E of
`[LJ-1.606]`'s crossing at the six slots of that probe's own Frame
(`agents/tasks/LJ-1-606/Probe606.agda:104-109`, target at `:147-148`).
The delivered file is `agents/tasks/LJ-1-609/Probe609.agda`, and it
typechecks cold at exit 0, 6.15 s, peak 823,541,760 bytes
(`agents/tasks/LJ-1-609/runs/final-4.out`, the interface deleted first).
The term sits at the probe's
top level (`Probe609.agda:357-365`), so the witness meter's dotted name
`Probe609.agda::elem-down-at` reaches it.

Nothing is postulated. Nothing lands in `src/`. No hole remains in the
delivered file.

## THE PRICE

All runs under the program's caliber `GHCRTS=[-A64m -I0 -M2g]`, which I
did not set. One Agda process at a time. Every typecheck ran under a
wall clock I set: 150 s for W3, 180 s for the floor, 400 s for the probe
runs. One run hit the cap and was killed by it (`runs/p-9.out`, see the
laws below).

| run | what | exit | time | peak RSS |
|---|---|---:|---:|---:|
| `runs/w3-1.out` | W3, type only, alone, first | 0 | 4.40 s | 778,125,312 |
| `runs/floor-2.out` | frame with the obligation at one designed hole | 42 | 3.11 s | 574,324,736 |
| `runs/floor-1.out` | same frame plus the seventeen's import | 42 | 9.43 s | 1,691,172,864 |
| `runs/p-9.out` | implicit-`ΣPathP` spelling, killed at the 300 s cap | killed | >300 s | not reached |
| `runs/p-11.out` | the probe, first full green | 0 | 5.58 s | 823,541,760 |
| `runs/seventeen-2.out` | the seventeen imported and recovered (W2) | 0 | 4.45 s | 724,418,560 |
| `runs/final-4.out` | delivered file, interface deleted first | 0 | 6.15 s | 823,541,760 |

The floor was measured before the proof, as the owner ruled on
2026-08-23. The frame costs 3.11 s and 574 MB. The term adds about
3 s and about 249 MB on top of it. The heap never approached the
wall: the peak stays under 40 percent of the 2 g cap.

The probe is 362 lines, of which 271 are non-comment and non-blank. The
brief estimated about 180 lines. The estimate was short by about a
factor of two, and the surplus is measured, not padding: the encoding
and its injectivity are about 100 lines (`Probe609.agda:192-292`), the
selection about 30 (`:309-336`), and the stage-closure lemmas about 60
(`:125-190`).

## THE SIX, NAMED

D-10 was done before any Agda beyond W3. The two objects the brief
named were read: `elem-down-taken`
(`agents/tasks/LJ-1-578/Probe578.agda:413-427`) and face E's statement
(`agents/tasks/LJ-1-606/Probe606.agda:147-148`). **The number I measured
is six, and it agrees with the brief.** The six are `[LJ-1.606]`'s Frame
parameters (`Probe606.agda:104-109`), and all six are now built:

| slot | at `file:line` | status | what it needed |
|---|---|---|---|
| 1 `lam`, the limit stage | `Probe606.agda:104` | built | nothing beyond the slot itself |
| 2 `ordλ`, its ordinality | `Probe606.agda:104` | built | `mem-ord`, `suc-ord`, `ord-tri`, `Lset-cumul` (`src/L/Ordinal.lagda.md:221`, `:96`; `src/L/Ordinal/Linear.lagda.md:136`; `src/L/Ordinal/Stages.lagda.md:164`) |
| 3 `succλ`, sucV-closure | `Probe606.agda:105` | built | this slot pays the whole stage closure: numerals climb it, and `pr∈Lset-suc` lands back inside it (`Probe609.agda:125-190`) |
| 4 `X`, the carrier, general | `Probe606.agda:106` | built | **the slot that differed in kind**: see the finding below |
| 5 `X⊆Lλ`, boundedness | `Probe606.agda:107` | built | feeds the base encoding directly (`Probe609.agda:203`) |
| 6 `∅∈λ`, nonempty base | `Probe606.agda:108` | built | starts the numeral climb (`Probe609.agda:128-130`) |

The seventeen's hull sits at the same six names, with slot 4 forced to
`UK.X = Lset α ∪ ⁅ x ⁆s` (`src/L/BoundedSubset.lagda.md:1150`, applied
at `:1405` and `:1549`). So the missing dimension was exactly slot 4's
generality, and it is now closed.

## THE FINDING: THE SQUARE LAW WAS NOT NEEDED

The brief, following `[LJ-1.606]`'s own comment
(`Probe606.agda:146`, "where the code count needs the square law"),
expected the six to differ from the seventeen by the square law. **They
do not, and the expectation is refuted as a term.** The square law is
needed only to count codes into the presentation of an ordinal. That is
what the seventeen did: `CodeCount` at `src/L/BoundedSubset.lagda.md:1409`
packs codes with `Bound`'s pairing, which wants `sq` and `α ∉ ω`
(`src/L/StageCardinal.lagda.md:64`), and the base injection
`code-inj` is bought from `absorbs` and `stage-card-upper`
(`src/L/BoundedSubset.lagda.md:1513`).

The route delivered here counts into the **stage itself**, and the tree
already carries every piece of it:

- each code is a Kuratowski-nested set of stage members, with tags
  `# 0`, `# 1`, `# 2` and formula codes as numerals
  (`Probe609.agda:192-204`), injective by `pr-inj` and `#-inj`
  (`src/V/Coding.lagda.md:175-179`, `:106`) and by Count's own
  injectivity (`src/FOL/Count.lagda.md:211-213`);
- the limit stage is closed under that nesting: `pr∈Lset-suc`
  (`src/L/Axioms/Basic.lagda.md:596-598`) plus `succλ`, `Lset-out`,
  trichotomy and monotonicity (`Probe609.agda:140-190`);
- the selection is `CanonCode`'s least-of-the-class pattern
  (`src/L/BoundedSubset.lagda.md:463-507`), restated at the stage's
  member type under the stage's own delivered L-order `wL = orderAt`
  (`src/L/Hull.lagda.md:158-159`;
  `src/L/Choice/Step.lagda.md:730`), which needs no square law and no
  cardinal;
- the consumer is the tree's own six-slot converter
  `HullElemDown.WithCode` (`src/L/BoundedSubset.lagda.md:667-682`): one
  section `f` of the code evaluation, and `ElemDown` follows in one line
  (`Probe609.agda:345-348`).

So face E is **one object and not two**: the NO-GO the brief priced as
equally valuable ("it would say face E is two objects and not one") did
not materialize, and this GO closes the face at the wider frame
outright.

## THE SEVENTEEN, IMPORTED AND RECOVERED (W2)

The brief ordered the seventeen imported and not restated. They are
imported at `runs/SEVENTEEN.agda`: `elem-down-taken` there is
`P550.Tele.BSA.elem-down` taken as is
(`agents/tasks/LJ-1-550/Probe550.agda:88-102` for the telescope), the
same object `[LJ-1.578]` ascribed at `Probe578.agda:413-427`. The lines
I took from the seventeen's side are `src/L/BoundedSubset.lagda.md:463-507`
(CanonCode's pattern), `:1409-1500` (the count and its arity alignment),
and `:1532-1552` (the assembly into `DR54.ElemDown` at the forced
carrier). None of them is importable at six slots, because all of them
sit inside the seventeen-slot telescope; the pattern was restated at the
new carrier, and the restatement is the about 100 measured lines named
above.

W2 asked the mathematics to be written once at a generic carrier and
instantiated. It is, and the instantiation is checked, not asserted:
`elem-down-taken-recovered` applies this task's six-slot term at the
seventeen's own forced carrier and lands in the seventeen's own type
`Tele.BSA.DR54.ElemDown` with no coercion
(`runs/SEVENTEEN.agda:64-81`, green at `runs/seventeen-2.out`). The
six-slot term subsumes the seventeen-slot delivery.

## WHAT THE CROSSING NOW WANTS

Of the three faces of `[LJ-1.606]`'s crossing, **face E is now paid at
the frame the crossing consumes**. What remains is the level-graph
adequacy, both halves:

- **G+ `GraphStage`**, UNBUILT (`Probe606.agda:156-159`): the stage
  carries the graph matrix at the tower's own values; the
  witness-in-carrier half of Devlin 5.2 (b).
- **G- `GraphAmbient`**, UNBUILT (`Probe606.agda:168-172`): any ambient
  witness of the carried matrix at an ordinal index pins the tower's
  level; Devlin 5.2 (a).

Nothing above reads a discharge into either unbuilt face. The kit's
non-vacuity still stands as `[LJ-1.606]` measured it
(`Probe606.agda:260-285`): no true matrix and no false matrix fills the
crossing, so G+ and G- remain real obligations. Once a `Crossing` is
inhabited, `inner-to-ambient` (`Probe606.agda:303-313`) consumes it and
face E together into the commute, with no further input.

For the next brief: the commute's residue is now exactly the two
adequacy faces, and the square law is no longer on face E's bill. Any
future task that counts codes at a limit stage can use the
stage-carried count of this probe in place of a square-law ordinal; the
obvious candidate is `CodeCount` inside `src/`, which this task did not
touch because the brief forbade landing in `src/`.

## MEASURED SPELLING LAWS, AT THIS SITE ONLY

- **Implicit `ΣPathP` arguments hang the elaborator.** With
  `ΣPathP (pk , ΣPathP (qψ , qcs))` left implicit, the run passed 300 s
  under the cap and was killed (`runs/p-9.out`). With the explicit
  `{A}`/`{B}` arguments that the tree's own seventeen-slot proof
  carries (`src/L/BoundedSubset.lagda.md:1483-1500`), the same clause
  checks as part of a 6.59 s file (`runs/p-10.out`). Take the delivered
  spelling; this is R-42's rule with a new measurement.
- **`mem-ord` wants its carrier explicit at this site.** Left implicit,
  it left constraints blocked on a metavariable and unsolved metas in
  `common` (`runs/p-10.out`); `mem-ord {A = lam}` closes them
  (`runs/p-11.out`).

## ARCHIVE USED

- `archive/dev/JOURNAL-archived.md`: not read, declined. This task built
  from delivered lemmas in `src/`, each cited at `file:line` above; the
  archived journal was not needed to find or price any of them.
- `archive/dev/LJ-dispatch-index.md`: not read, declined. The task's
  predecessors were reached through the brief's own citations, not
  through the index.
- `archive/dev/JOURNAL.md`: not read, declined, same reason as the
  archived journal.
- `dev/ARCHIVE.md`: not surveyed, declined. No module was retired and
  nothing moved to `archive/` in this task, so no archive row was owed.
- `archive/dev/DECISIONS-archived.md`: not used, declined. No decision
  record was consulted; the rulings that bound this task arrived in the
  slot file and the brief.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: not read, declined. Face E's route
  consumed no Devlin material; the Devlin 5.2 references in the section
  above belong to faces G+ and G- and are quoted from the brief and
  from `Probe606.agda`, not from the literature file.
- `dev/literature/truncation-and-selection.md`: not read, declined. The
  selection here is `leastOf` over a delivered strict well-order, cited
  from `src/L/WellOrder/Base.lagda.md:158-161` by way of its consumers.
- `dev/literature/terms-2026-08.md`: not read, declined.
- `dev/literature/digest.md`: not read, declined.
- `dev/literature/geology.md`: not read, declined.

## TREE STATEMENT

The working tree holds, beside the brief: `Probe609.agda` (delivered),
`lj-1.609-report.md` (this report), and `runs/` with `W3.agda`,
`FLOOR.agda`, `SEVENTEEN.agda`, `run.sh`, and the `.out` files named in
the price table plus the iteration records `p-1` through `p-11`,
`final-1` through `final-4`, `floor-1`, `floor-2`, `w3-1`,
`seventeen-1`, `seventeen-2`. A bisect scratch from the `ΣPathP` hang
was deleted after its evidence landed in `p-9.out` and `p-10.out`.
No `review-of-*.md` is written, because the stop form was not taken.
Nothing is committed and nothing is pushed.
