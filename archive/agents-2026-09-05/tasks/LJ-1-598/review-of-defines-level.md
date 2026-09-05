# review of `defines-level`: the obligation is NOT inhabited

## VERDICT

**`Cert.DefinesLevel` IS NOT SUPPLIED AT TODAY'S TREE, AND I DID NOT
INHABIT IT.** The meter says so:
`agents/tasks/LJ-1-598/Probe598.agda::defines-level` returns
`missing exit=42 ... [NotInScope]`, `1 UNRESOLVED of 1`,
`probe_red=False`. The probe itself is green
(`agents/tasks/LJ-1-598/runs/p-final.out`, `EXIT=0`, 3.07 s), and its
sixteen landed names each return `pass` under the same meter.

**THIS IS A NO-GO OF SUPPLY AND A CORRECTION OF THE TARGET, AND THE
CORRECTION IS THE DELIVERABLE.** The clause is not refused because it is
hard. It is refused because the type's own hypothesis and the tree's own
level formula disagree about the index, and no formula the tree has can
close that distance.

## WHAT THE TYPE ASKS, READ AT ITS OWN LINES

Clause (i) (`agents/tasks/LJ-1-578/Probe578.agda:234-240`): for every code
`c` with `IsOrd (HS.C.π (fst (T.val c)))`, a formula over hull codes whose
inner-world solution set is exactly `{Lset (fst (T.val c))}`.

## WHY NO TERM OF THAT TYPE CAN BE BUILT FROM THE DELIVERED TREE

**1. THE EQUATION ROUTE NEEDS A CODE FOR THE LEVEL, WHICH IS THE
CONCLUSION CLAUSE (i) EXISTS TO BUY.** `eqF`, `eq-sat` and `eq-uniq`
(`agents/tasks/LJ-1-598/Probe598.agda:157-164`) pay everything except one
hypothesis: `CodedLevels` (`:167`), a code `d` with
`fst (T.val d) ≡ Lset (fst (T.val c))`. `coded-gives-level` (`:171`) buys
the clause from it outright. That hypothesis is `Facts.HasLevels`'s own
conclusion (`agents/tasks/LJ-1-578/Probe578.agda:120-122`), which
`cert-gives-A` (`:254-273`) derives FROM clause (i). The route is circular
for the certificate and I did not take it.

**2. THE GRAPH ROUTE NEEDS A STAGE READING NOBODY HAS BUILT, AND AT THE
INDEXES THE TYPE ADMITS IT WOULD ANSWER WITH THE WRONG SET.** The route is
`inF ψ c = ∃̇ (ψ ∧̇ (var zero ≐ con c))` (`Probe598.agda:217`), and it needs
`Det` and `Wit` (`:209`, `:213`): determination and existence for a
two-slot formula at an ORDINAL index. `graph-gives-level` (`:220`) is that
implication in full. `Det` is the inner-world reading of `Lset-only`
(`src/L/Hierarchy.lagda.md:334-337`), which the tree proves only at the
CLASS `L`, behind `GraphAgree` (`agents/tasks/LJ-1-570/Probe570.agda:289`),
whose parts are "terms in five probes, none in `src/`"
(`agents/tasks/LJ-1-570/lj-1.570-report.md:96-100`).

And the type does not give the ordinal index. It hypothesizes
`IsOrd (HS.C.π (fst (T.val c)))`, the ordinal-hood of the COLLAPSE. At a
NON-ordinal index the tree's graph formula is satisfied by a set that is
not the level: at `δ = {{∅}}`, an approximation on `δ` is defined exactly on
`δ`'s one member `{∅}`, the step condition forces the record at `{∅}` to
be `∅`, because `{∅}`'s own member `∅` lies outside the approximation's
domain (`StepOf`,
`src/L/Coding/Sequence.lagda.md:126-131`), so the graph's value at `δ` is
`𝒟ₒ ∅ = {∅}`, while the tower's value is
`Lset δ = 𝒟ₒ (𝒟ₒ ∅) = {∅, {∅}}` (`Lset-compute`,
`src/L/Constructible.lagda.md:227`). Graph value `1`, tower value `2`. Such
a `δ` is a code value in every hull, being the unique satisfier of a closed
formula the algebra's `search` lands (`src/L/Hull.lagda.md:79-90`), and its
collapse is an ordinal. **So the natural supplier cannot meet the type at
the codes the type admits, and the gap is in the HYPOTHESIS and not in the
reading.** This paragraph is a READING of the two cited definitions and is
not machine-checked; the two-line computation is in the report.

## THE CORRECTED TARGET

State clause (i) at `IsOrd (fst (T.val c))`, the index's own ordinal-hood.
Then section 4 of the probe is the exact shape of the residue: build one
two-slot formula over codes with `Det` and `Wit`, and clause (i) follows at
every ordinal-valued code in 24 code lines already written. The same
correction lands on `Facts.HasLevels`, `Facts.LevelsCommute` and clause
(iii) (`agents/tasks/LJ-1-578/Probe578.agda:120-128`, `:503-510`), the
other three statements that conclude at `Lset` of a possibly non-ordinal
preimage. `PreimageOrd` (`Probe598.agda:257`) is the bridge if the owner
prefers to keep the hypothesis; it is not built anywhere and I could see no
route to it.

## WHAT THE PROBE DELIVERS INSTEAD

Sixteen green, metered names (`agents/tasks/LJ-1-598/Probe598.agda`), every
declaration in the probe among them: the W3
type and its vacuity witness (`:87`, `:104`), the restated clause and the
body identity (`:118`, `:134`), the equation route (`:157-171`), the graph
route (`:209-220`), and the bridge composition (`:257-263`). Plus two
measured floors: the import frame WALLS at the wide cap
(`agents/tasks/LJ-1-598/runs/floor-1.out`, exit 251 at 57.90 s, inside the
chain; `runs/chain-578.out`, exit 251 at 15.92 s for
`[LJ-1.578]`'s own file with warm dependencies), and the trimmed frame
costs 2.48 s and 723,271,680 bytes (`runs/floor2-1.out`).

## SCOPE

I wrote only inside `agents/tasks/LJ-1-598/`. Nothing is postulated, the
probe carries `--safe`, there is no hole, and nothing lands in `src/`. No
commit, no push.
