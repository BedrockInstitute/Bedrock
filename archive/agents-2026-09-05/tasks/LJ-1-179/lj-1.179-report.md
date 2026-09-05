# LJ-1.179: adversarial review of `[LJ-1.169]`

This file declares rule series DD unless a `D-` code is written.

## VERDICT

**OVERTURNED.** The negative is a fixed-shape negative: it is right for the
`⌜_⌝` coding and wrong for the tree, because the tree already carries the
parameter split at `src/L/Choice/Name.lagda.md:381`.

## QUESTION 1: is the refusal correct on its own numbers?

**No.** The measurements are correct. The verdict over-reaches them.

The report measures the `⌜_⌝` coding. It cites the right sites:

- `⌜ con x ⌝ᵗ = mkTag 0 x`, `src/FOL/Coding.lagda.md:105`. The parameter is a
  leaf of the code tree.
- `⌜ φ ∧̇ ψ ⌝ = mkTag 2 (pr ⌜ φ ⌝ ⌜ ψ ⌝)`, `src/FOL/Coding.lagda.md:124-136`.
- `pr∈Lset-suc` shifts a stage by two, `src/L/Axioms/Basic.lagda.md:596-599`.

I re-derived these. They are correct. The probe's BLOCK 2 proves the growth and
the `+ω` absorption. The 12-line assembly is correct.

But the verdict says more than the measurements. The report writes:

- "THE RANK ACCOUNTING DOES NOT WORK IN THIS TREE'S `𝒟ₒ`",
  `lj-1.169-report.md:216`.
- "this tree: at the LEAVES of the code tree", `:303`.
- "the rank accounting works in this tree's `𝒟ₒ`: MEASURED FALSE", `:532`.

These are tree-wide claims. They are false. The tree has a second coding.
`nameOf φ = countFo φ , (absFo φ , constantsFo φ)`,
`src/L/Choice/Name.lagda.md:380-381`. In that coding the parameters leave the
syntax. Its own prose says so, `:5-9`. Its parameter-free code is in `Lset ω`,
uniformly in depth, `code∈limit`, `:153-165`. Its adequacy is delivered,
`denote-defSet`, `:438`.

So the refusal is correct for the `⌜_⌝` coding and incorrect for the tree.

## QUESTION 2: is the measurement sound?

**Yes, and the noise band does not bear.**

The protocol is sound. One process, `GHCRTS="-A64m -I0 -M8g"`, a 10-minute wall
criterion fixed before the runs. Three runs, exit 0. The longest wall time is
12.17 s. The resident set is 489 to 492 MB. The report logs this,
`lj-1.169-report.md:8`.

The run count is enough. The probe proves three blocks. Exit 0 on three runs
confirms it typechecks.

The noise band is `±12.8%`. It measures check-time ratios,
`scripts/check-ratio.py:80-87`. The verdict rests on a mathematical obstruction
and a static line count. It does not rest on a timing delta. So no figure the
decision rests on sits inside the band. The report declines DD24 for the same
reason, `:8`, and that is correct.

## QUESTION 3: did the brief cause the outcome?

**No.** The brief's premise was a hypothesis. The brief anticipated the stop and
pointed at the cure's location.

The brief presented the finite bump as the route, `LJ-1.169.md`. It marked it
INFERRED. It told the agent to look at `src/L/Choice/` first. It gated the
"rank accounting does NOT work" outcome as the deepest finding.

The agent looked and missed the cure. The report writes "I looked. The
load-bearing miss this time is elsewhere", `lj-1.169-report.md:136-137`. The
miss was in `src/L/Choice/Name.lagda.md:381`, which the report never cites. A
grep for `Name.lagda`, `nameOf`, `absFo`, `constantsFo` or `code∈limit` in the
report returns nothing.

So the brief did not cause the NO-GO. The agent's incomplete search caused it.

## QUESTION 4: is there a cure the return missed?

**Yes.** The cure is the delivered parameter split. The report names it as its
own Fork A, but does not see that it is already in the tree.

The split is delivered:

- `nameOf`, `src/L/Choice/Name.lagda.md:380-381`.
- `code∈limit`, `:153-165`. The parameter-free code is in `Lset ω`, uniformly.
- `env`, the sequence with the index inside the pair,
  `src/L/Coding/Environment.lagda.md:84-86`.
- `envOverAt`, the object-level reading of an environment,
  `src/L/Coding/Model.lagda.md:483-485`.
- `envCloses`, the environment at a fixed `sucIter 3 δ`,
  `src/L/Ordinal/StageArith.lagda.md:92-96`.

The report's Fork A says "re-code. Split the code from its parameters",
`lj-1.169-report.md:348`. That re-code is not needed. The split is delivered.

The report's Fork B says move the carrier to `+ω`. That is also not needed. The
split gives a finite iterate. `[LJ-1.170]` measured the split key at
`Lset (sucIter 5 σ)` in 37 lines, `agents/tasks/LJ-1-170/lj-1.170-report.md:0`.

## C-42 BOTH DIRECTIONS

**The negative reaches FURTHER than it claims.** It measured the `⌜_⌝` coding
and claimed the whole tree. The tree's second coding refutes the tree-wide
claim.

**The negative reaches LESS far than it claims.** The split route is not
affected. The rank accounting works there. So the negative's tree-wide wording
claims more than it measures, and its true site is one coding, not the tree.

## DD4: did the negative price a fixed shape?

**Yes.** The report priced the fixed shape, `⌜_⌝`, and refused it. The generic
shape, the split, prices differently. `[LJ-1.170]` measured it at a finite
iterate. A NO-GO on a fixed shape is not a NO-GO.

The report's BLOCK 2, the growth law, is tower content and stands. `dbl`,
`prTower` and `prTower-ω` name no tower. That part of the report is correct and
generic.

## WHAT THIS CONFIRMS OR UNBLOCKS

The overturn unblocks the finite-bump route to `powIter` through the split. The
campaign has taken this route. `[LJ-1.170]` found the split. `[LJ-1.171]` found
the sequence that reads back. `[LJ-1.172]` and `[LJ-1.173]` build the supply.

The 12-line assembly stands. The BLOCK 2 growth law stands and transfers to the
J tower.

The overturn does not establish that `powIter` is provable in 80 lines or fewer.
It establishes that the line is not closed by a "rank accounting fails" finding.
A correct NO-GO above 80 lines may still be the outcome. That is a pricing
question for a future brief, not this review.

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/L/Rud/SatTable.lagda.md:119`, `:143-145`,
  `:210-220`. Read. The retired route's `+ω` bound is a hypothesis,
  `BlockPowLim` at `:210-212`. It is never a theorem. The report read this and
  took `+ω` as the shape, `lj-1.169-report.md:6`. That shape does not settle the
  negative. The archive never saw the current tree's split. The split is in the
  current tree, not the archive.

## LITERATURE USED

- `_build/literature/dev2.txt:600-632`. Read. `K(u)` is finite sequences over a
  fixed set and the members of `u`. 2.4's proof says "left as an exercise for
  the reader", `:632`.
- `dev/literature/devlin-II5.md:250-258`. Read. The digest says the bound needs
  "some bounded description with a bound inside the carrier", any shape,
  `:254-255`. The split satisfies this. The `⌜_⌝` coding does not.
- `dev/literature/devlin-errata.md`: not read. `[LJ-1.136]` measured that the
  errata touch no part of II.5.

## EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| the `⌜_⌝` code set sits at `+ω`, not a finite bump | MEASURED TRUE |
| the 12-line assembly is correct | MEASURED TRUE |
| the rank accounting fails in this tree's `𝒟ₒ` | MEASURED FALSE |
| this tree's codes carry the parameters inside the code tree | MEASURED FALSE. The split does not |
| `Describes` needs a coding decision, not a lemma | MEASURED FALSE. The split is delivered |
| Fork A, re-code, is required | MEASURED FALSE |
| the report looked at `src/L/Choice/` and the miss was elsewhere | MEASURED FALSE. The miss was `Name.lagda.md:381` |
| the brief caused the NO-GO | MEASURED FALSE. The agent's search miss caused it |
