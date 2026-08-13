# LJ-1.36 report: is the leaf reading really 2 seconds per clause?

Status: COMPLETE. Written incrementally per C-22. Untracked probes, no
commit, no push. The report uses ASD-STE100.

## 1. THE VERDICT

**GO. The per-clause band is [under 0.01, 1.94] seconds, top at or
below 3 seconds.** The 1.94 figure belongs to ONE clause: the
`DefBody` leaf reading, reproduced in the same session. Every other
measured clause reading is at or below 0.02 seconds.

The 2-seconds-per-clause projection does NOT survive as a per-row
figure. It priced one deep leaf reading and multiplied it by twelve.
The twelve rows of the satisfaction table read at the conjunction-walk
class, below 10 milliseconds each. The block funds with wide room.

The evidence is `src/ProbeLJ136.agda` and `src/ProbeLJ136Ctrl.agda`,
both untracked. The machine was quiet. One Agda process ran at a time,
at `GHCRTS="-A64m -I0 -M8g"`.

## 2. THE CLAUSES YOU PICKED

The brief demands clauses of DIFFERENT body shapes, expected worst,
not soft clauses. I picked five shapes beyond the anchor.

1. **The step clause.** `StepAt` read through the delivered `StepAt-out`
   (`src/L/Coding/Sequence.lagda.md:217-219`). This is the outer layer
   of the measured clause. It reads the whole built step, three
   existentials and the `DefAt` leaf, from the satisfaction.
2. **The atom row.** `memClauseAt`, read out of the built `twelveAt`
   conjunction at depth 1. Its body is `extAt` over two unbounded
   existentials and two term-value atoms.
3. **The implication row.** `impClauseAt`, depth 4. Its relation has
   THREE nested unbounded universals, two subvalue lookups and an
   ambient-set frame. This is the deepest row relation.
4. **The negation row.** `negClauseAt`, depth 5. Its relation has TWO
   nested unbounded universals, a subvalue lookup and a difference
   leaf.
5. **The bounded-existential row.** `exInClauseAt`, depth 12, the last
   conjunct of `twelveAt`. Its body mixes a term-value lookup with a
   bounded existential and an environment extension.

The rows share the machine's built table. I read each row out of the
built `twelveAt` conjunction (`src/L/Coding/Graph.lagda.md:94-105`).
The projection's type conversion walks the built conjunction. The
projection depth is a real shape difference: row 1 is one projection,
row 12 is eleven.

I also measured the negation shape re-derived with public names,
through the delivered `unClause-out` frame. The delivered row
relations are private (`src/L/Coding/Model.lagda.md:1153-1168`,
`:1244-1256`), so an outside reading never unfolds them. The
re-derived row measures the substrate's fresh-write option.

Eight of the twelve rows have no public whole-row reader. The atom and
propositional rows need private comparators or private indices. The
quantifier rows need private bodies. An outside consumer cannot
instantiate `atomClause-out`, `propClause-out`, `quantClause-out` or
`bndClause-out` at the delivered rows
(`src/L/Coding/Model.lagda.md:1082-1108`, `:1630-1644`,
`:1793-1810`, `:1955-1969`). That is a finding for the substrate
design, not a measurement.

## 3. SECONDS PER CLAUSE

The control file imports the probe's modules and has no content. Two
cold runs give 1.02 and 1.02 seconds of user time. The cone is
1.02 seconds.

The probe file checks in 3.09 and 3.11 seconds of user time. The pair
is flat under the noise rule: the delta is 0.02 seconds, under 0.5.
The mean gross is 3.10 seconds. The mean net is 2.08 seconds.

The per-definition rows come from `agda --profile=definitions`, cold,
with the probe's own interface moved aside. Dependencies were warm.

| clause reading | net s | gross s |
|---|---:|---:|
| the `DefBody` leaf, `graph-read` | 1.59 | 1.67 |
| the `DefBody` leaf, `code-read` | 0.38 | 0.46 |
| the step clause, `StepAt-out` | under 0.01 | under 0.10 |
| the atom row, depth 1 | under 0.01 | under 0.10 |
| the implication row, depth 4 | under 0.01 | under 0.10 |
| the negation row, depth 5 | under 0.01 | under 0.10 |
| the bounded-existential row, depth 12 | under 0.01 | under 0.10 |
| the re-derived negation shape | 0.01 | 0.10 |

The net figure is the profile row, which excludes the cone. The gross
figure adds the cone share of 0.085 seconds, the control divided by
twelve. The cone is a per-FILE cost, not a per-clause cost, so the
gross allocation is a convention.

The profile prints definitions at or above about 10 milliseconds. The
step reading and the variable-slot row projections never appear, so
they sit below that threshold. Three profile runs agree:
`graph-read` at 1,578, 1,580 and 1,594 milliseconds, `code-read` at
362, 371 and 397.

The anchor reproduces `[LJ-1.35]` exactly. My cold re-run of
`src/ProbeLJ135.agda` gives 3.41 seconds of user time, and a profile
puts `graph-read` at 1,702 and `code-read` at 395 milliseconds. The
same-session anchor is 1.94 to 1.99 seconds net.

## 4. DOES 2 SECONDS SURVIVE?

NO, not as a per-clause figure for the twelve rows. The 1.94-second
reading is the cost of ONE deep built leaf, the `DefBody` satisfaction
through `codeAt-out` and `graphAt-out`. The rows' readings are the
conjunction-walk class, below 10 milliseconds each.

The projection error is visible in `[LJ-1.35]`'s own numbers. The
measured site was the `DefBody` leaf, the deepest public leaf of the
Def tower. The twelve rows of the satisfaction table live INSIDE that
leaf, inside the graph witness. One `graphAt-out` reading extracts the
whole witness. The rows then project out of the witness's `twelveAt`
conjunction, and each projection is below 10 milliseconds.

The band's top is the anchor itself. It is at or below 3 seconds, so
the GO condition holds. Twelve clauses cost about 2.1 seconds of
reading at the measured site, not 24.

## 5. THE THREE WITNESS MEMBERSHIPS

The graph witness's own existentials, the code set C, the table T and
the carrier b, extract at 11 to 12 milliseconds each. The three
extractions are `wcode-in-K`, `wtable-in-K` and `wcarrier-in-K` in
`src/ProbeLJ136.agda`. Each is a projection of the witness discharged
by a site fact.

They behave like the story's own quantifiers. The story's quantifier
assembly measured 41 milliseconds in `[LJ-1.35]`. The witness
extractions are the same class, three rows at about 11 milliseconds.
The row extractions from the graph witness, the substrate's actual
shape, measure the same: `wit-exIn` at 12 milliseconds, `wit-mem`
below the profile threshold. The gap closes: the extraction is nearly
free once the graph reading is paid. What remains is the site facts,
which are substrate content, still unpriced in seconds.

## 6. AMORTIZING OR NOT

The leaf reading follows BOTH classes, at different layers.

The row level follows `[LJ-1.33-R]`. The `twelveAt` conjunction and
the frame readers are written once. Each row's extraction is below 10
milliseconds. The measured class is at or below the 0.08 seconds per
clause that `[LJ-1.33-R]` recorded.

The deep-leaf level follows `[LJ-1.35]`. The `graphAt-out` reading is
a fixed cost of about 1.94 seconds per graph occurrence. It does not
amortize, and it does not multiply either: it is paid once per graph,
not once per row.

The 12 times 2 seconds projection multiplied a one-time cost. No cure
is needed, because there is no per-row tax to cure. The measured
construction is: one deep reading, twelve cheap extractions.

## 7. THE PRICE OF THE NEXT BLOCK

On my numbers, with every row measured:

| piece | seconds | class |
|---|---:|---|
| the deep `DefBody` leaf reading, one graph | 1.94 | MEASURED, this probe, same-session |
| eleven rows of the table, extraction and reading | under 0.12 | MEASURED, this probe |
| the witness memberships, three extractions | 0.03 | MEASURED, this probe |
| the assembly from site facts | 0.04 | MEASURED, `[LJ-1.35]` |
| the clause certificate from the leaf | 0.76 | MEASURED, `[LJ-1.34-R]` |
| the bounded code-set description, the substrate's half | 1.6-4.0 | SURVEY, `_build/lj-1.12-report.md:30` |

The bound-fact construction lands at about 2.1 seconds at the measured
site. `[LJ-1.35]` projected 22 to 31 seconds for the other eleven
clauses. The measured figure for those rows is under 0.2 seconds.

The block funds inside the GCH budget of 99.6 to 147.7 seconds
(`dev/ledger.toml:305`) with wide room. The bound-fact construction
is no longer a wide term.

## 8. DD4

Each piece falls on one side.

| piece | side |
|---|---|
| the deep leaf reading, `code-read` and `graph-read` | PER-TOWER (Def). It reads the Def tower's built syntax through Def-specific delivered readers. Measured: 1.94 seconds per graph |
| the twelve-row extraction from `twelveAt` | TEMPLATE SHAPE. The conjunction walk and the frame readers are generic. Measured: under 10 milliseconds per row |
| the witness extractions | TEMPLATE. Three projections and three site facts. Measured: 11 to 12 milliseconds each |
| the site facts: codes, values, witnesses, carrier in K | PER-TOWER CONTENT, TEMPLATE SHAPE. The facts are the Def tower's content; the shape is a K-membership at a sealed carrier |
| the story certificate | PER-TOWER (Def) |
| the assembly | TEMPLATE. Measured: 41 milliseconds in `[LJ-1.35]` |

D-26's prediction holds. The expensive half, the deep leaf reading, is
keyed on the Def tower's built syntax. The J tower's bound facts are
structural, generation data with no satisfaction to read. The
expensive half does not reach it.

## 9. LITERATURE USED

`dev/literature/devlin-II5.md`, Step C (`:209-256`, summary `:299-302`).
Took the requirement: bind every quantifier of the Def step by the
concrete set K(u), inside the matrix. Devlin writes the description
ONCE and says nothing about a per-clause cost.

His single-description shape IS available here. The twelve rows are a
formalization artefact of the machine's satisfaction table. All twelve
rows live inside one built graph formula, `satGraphAt` with its
`twelveAt`. The bound-fact construction reads that formula once and
projects the rows. The per-clause cost in `[LJ-1.35]`'s projection
only exists if the substrate restates each row with its own reading,
and the measured rows show that reading is cheap.

`dev/literature/devlin-errata.md`. NOT read. WHY NOT: `[LJ-1.14]`
verified it does not cover Chapter II section 5, and the brief rules
out re-checking it.

## 10. ARCHIVE USED

`_build/lj-1.35-report.md`, whole. Took the measured site at `:92-105`,
the projection at `:165`, the uncertainty 2 at `:252-256`, the
uncertainty 4 at `:261-264`, and the DD4 split at `:176-191`.

`src/ProbeLJ135.agda`, whole. Copied the anchor's `code-read` and
`graph-read` verbatim into `src/ProbeLJ136.agda:83-107` for a
same-session comparison. Re-ran the file cold: 3.41 seconds of user
time, flat against the report's 3.21 and 3.16 under the noise rule.

`_build/lj-1.34-review.md`, whole. Took the D5 content figure at
`:141-143`, the instantiation cost at `:383`, and the bound-fact
construction as the widest term at `:390` and `:403`.

`src/ProbeDD25D5.agda`, whole. Took the `LeafBnd` shape at `:226-231`
and the generic layer that amortizes at `:53-102`.

`_build/lj-1.33-review.md`, whole. Took the amortized layer at `:29`,
the 0.08 seconds per clause at `:102`, the six-instantiation slope at
`:93-104`, and the 2x2 at `:70-84`.

`src/L/Condensation.lagda.md`, whole. Took the delivered clause's
memberships at `:253-263` and the decode at `:273-343`.

`_build/lj-1.5-report.md`, whole. Took the block-1 rate at `:8-13`.

`src/L/Coding/Powerset.lagda.md`, the coding sections. Took `DefBody`
at `:437-440`, `codeAt-out` at `:308-314`, and the readers at
`:297-325` and `:440-470`.

`src/L/Coding/Graph.lagda.md`, whole. Took `twelveAt` at `:94-105`,
`GraphWitAt` at `:194-195` and `graphAt-out` at `:202-206`.

`src/L/Coding/Model.lagda.md`, the coding sections. Took the row
clauses and their readers at `:1171-1372`, the private relation blocks
at `:1153-1168`, `:1244-1256`, `:1550-1619`, `:1736-1790` and
`:2025-2055`, and the generic frames at `:897-1023`.

`src/L/Coding/Sequence.lagda.md`, whole. Took `StepAt` at `:119-120`
and `StepAt-out` at `:217-219`.

`_build/lj-1.2-gate.md`, whole. Took the twelve-clause note at
`:27-45` and the substrate figures at `:126-128`.

`dev/LESSONS.md` is not archived and binds. P-l decided what could and
could not be measured from outside Model. P-m named the content
classes. P-v decided the spelling. D-1, D-10, C-12, C-22, C-32, C-33
and C-34 were followed. D-26 decided the DD4 split.

## 11. WHAT I AM NOT SURE OF

1. The eight rows without public whole-row readers are unmeasured at
   their in-module cost. Their relations are private, so an outside
   reading never unfolds them. The substrate must either export new
   readers, make the relations public, or re-derive them. The
   re-derived negation shape measured 10 milliseconds, but P-l forbids
   pricing the other rows by that analogy.
2. The anchor's 1.94 seconds is a per-GRAPH cost, not a per-row cost.
   How many times the next block pays it depends on how many graph
   occurrences the substrate reads. The natural design reads one.
3. The profile hides definitions below about 10 milliseconds. I report
   those rows as "under 0.01 seconds", which is an upper bound, not an
   exact figure.
4. The site facts remain unpriced in seconds. They are the substrate's
   code-set half, surveyed at 0.2 to 0.5 thousand lines. The
   extraction cost is measured; the content cost is not.
5. Cold discipline: dependencies were warm through
   `_build/2.8.0/agda/src/`. Only each probe's own interface was cold.
   That matches the lineage protocol, so the comparisons hold.
