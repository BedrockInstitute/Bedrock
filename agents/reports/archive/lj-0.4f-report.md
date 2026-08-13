# LJ-0.4f: the recursion assembly, probed first and landed only on a GO

Status: COMPLETE. NO-GO on measurement. No commit, no push. The main
tree's three files are untouched. The kit is preserved at
`_build/kits/lj-0.4f-recassembly.lagda.md`.

## 1. THE VERDICT

**NO-GO. Lines: the pair cannot reach minus 60. Seconds: flat.**

The measured one-site anchor is minus 96. The kit costs 208. The
break-even is 208 divided by 96, which is 2.17. The site count is two.
Break-even exceeds the site count, so the standing gate stops the build
before the second site.

The projection misses the floor. Two sites at the measured rate give
plus 16. The floor is minus 60. Even Table's whole realistic surface,
about minus 116, leaves the pair at about minus 4.

The seconds are flat. Hierarchy moved from 23.75 s to 23.48 s. The
delta is 0.27 s, which is noise under the rule.

## 2. THE STEP 1 MEASUREMENT

Date: 2026-08-10.

The step 1 probe folds one pair. The pair is `L.Hierarchy`'s assembly and
`L.Choice.Table`'s assembly. I measure the pair delta and the cold seconds
before I touch a third file.

The measurement runs on a clone of HEAD at `/tmp/lj04f-clone`. The main
tree's dependency cone was under the sibling's live edit. The sibling edits
`L.Coding.Environment` and `L.Axioms.Separation`, which sit in the cone of
both files. The cone did not typecheck twice during my first attempts. The
clone gives a stable, green baseline. My three files are unmodified, so the
clone content equals the main tree content for them. The orchestrator
committed the sibling's work while I measured. My three files are unchanged
between the clone's HEAD and the new HEAD.

The probe builds the kit and wires one site. I wired `L.Hierarchy` first.
I measured the one-site net and the seconds. The projection missed the
floor. The standing gates then stopped the build before `L.Choice.Table`.

## 2a. THE STEP 1 GATES

The break-even gate stops the build. The kit is 208 lines. The measured
saving per site is 96 lines. The break-even is 2.17 sites. Two sites
cannot cover the kit. The three numbers are 208, 96, and 2.17.

The staging gate stops the build too. The projection is the kit plus two
sites at the measured rate. It is plus 16. The floor is minus 60. The
projection misses the floor by 76 lines.

The realistic pair bound also misses the floor. Table's replaceable
surface is its machinery, its approximation block, its graph block, and
its pair graph. That is about 130 lines before glue. With glue it is
about minus 116. The pair is then about minus 4.

## 3. THE NUMBER

The counts are the ledger caliber. They are non-blank lines inside
` ```agda ` fences, counted by `scripts/ledger.py` with `at_head=False`.

| File | Before | After | Delta |
|---|---:|---:|---:|
| L/RecAssembly.lagda.md (new kit) | 0 | 208 | +208 |
| L/Hierarchy.lagda.md (wired) | 350 | 254 | -96 |
| **one-site net** | 350 | 462 | **+112** |
| L/Choice/Table.lagda.md (not wired) | 463 | about 367 | about -96, projected |
| **pair net, projected** | 813 | about 829 | **about +16** |
| L/Choice/Before.lagda.md | 1110 | 1110 | 0 |

The pair net is the kit plus the two sites. At the measured per-site rate
the pair net is plus 16. Table's realistic maximum is about minus 116,
which gives the pair about minus 4. Neither reaches the floor.

The shape check (D-10) comes before the build. The t208 residue names three
regions and claims they share one shape. I verified the regions by reading
the code. The pair shares a pipeline. The named triples do not.

`Hierarchy`'s triple at `src/L/Hierarchy.lagda.md:116-124` is three table
conditions over `h : S` and `B : V ℓ`. `Table`'s triple at
`src/L/Choice/Table.lagda.md:158-167` is a class predicate and a realizing
set. The two triples have different types and different shapes.

`Table` has its own `Values`/`Entries`/`Domain` at
`src/L/Choice/Table.lagda.md:295-304`. That triple shares the shape of
`Hierarchy`'s triple. The conclusions differ. `Hierarchy`'s `Values`
concludes `fst z ≡ Lset (fst c)`. `Table`'s concludes `IsRel (fst c) r`.
`Hierarchy`'s `Entries` carries the tower value. `Table`'s `Entries` is a
truncated existential.

The pipeline below the triples shares its shape. Both files have a step
pair, an approximation induction, a graph reading pair, a pair graph, a
realized class, and a sealed construction. Every component has site-specific
content. The step proofs differ. `Hierarchy` reads `StepAt` from
`L.Coding.Sequence` and discharges `PowOK`. `Table` reads an `extAt` step
against its `Described` condition. The approximation motives differ. The
construction differs. `Table` separates the relation at the ordinal out of a
bound, which `Hierarchy` does not need.

`Before`'s region at `src/L/Choice/Before.lagda.md:229-398` is a different
mechanism. It is a direct recursion over `ℕ` with separation. It has no
graph, no approximation, and no replacement. Its overlap with the pair is
the membership characterization pattern only. The third copy claim is false
at the mechanism level.

The probe still runs on the pair. The pipeline skeleton is genuinely
shared, so the fold question is live. The fold must parameterize every
difference. That parameter surface is where the arithmetic will be decided.

## 4. SECONDS

One Agda process at a time under `GHCRTS="-A64m -I0 -M8g"`. Each row
deletes the file's own interface and keeps the dependencies' interfaces.

| File | Before (s) | After (s) | Exit |
|---|---:|---:|---:|
| L/Hierarchy.lagda.md | 23.75 | 23.48 | 0 |
| L/Choice/Table.lagda.md | 2.97 | not wired | 0 |
| L/RecAssembly.lagda.md (kit) | n/a | 1.50 | 0 |

The Hierarchy and Table rows checked with warm dependencies and a cold
target interface. Only the target file appears in the check output.
The numbers are wall seconds.

The Hierarchy delta is 0.27 s. The noise rule sets the floor at the
larger of 0.5 s and five percent. Five percent of 23.75 s is 1.19 s. The
delta is below the floor, so it is noise. The fold is seconds-flat at
the wired site.

The Table after-row is empty because the line gate stopped the build
before the second site. The kit row is the parameterized class. It
checks near the P-m parameterized rate.

## 5. WHAT I FOLDED

I built `L.RecAssembly`, a module-parameterized assembly. It holds the
shared pipeline: the `Values` and `Domain` predicates, the `ApproxAt`
and `GraphAt` machinery, the approximation induction, the graph reading
pair, and the pair graph. The value property, the entries predicate,
the step pair, and the entries-to-exists conversions are parameters.

The kit is generic in the value. `P : V ℓ → S → Type` is the value
property at an argument. `Hierarchy` instantiates it with
`fst z ≡ Lset (fst c)`. `Table` would instantiate it with `IsRel`. The
module does not name a concrete stage or a concrete relation.

I wired `Hierarchy`. The file keeps its own `Values`/`Entries`/`Domain`
definitions and its step pair. The file replaces its approximation
block, its `Lset-only` block, its `graph-table` block, and its pair
graph block with the kit's instances. The file typechecks. The linters
pass. The file went from 350 lines to 254.

I left the site mathematics in place. The step proofs stay at the
sites. `Hierarchy` reads `StepAt` from `L.Coding.Sequence`. `Table`
reads an `extAt` step against its `Described` condition. The class
readings stay. `hier-out` and `hier-in` differ from `table-out` and
`table-in`. The sealed constructions stay. `hierAt` and `tableAt`
differ in the class, the payload, and the separation.

The P-r reasoning applies to the fold shape. The kit shares the
statement shape. It does not store a structure that consumers unfold.
The consumers see the same types as before.

The arithmetic fails on the kit's price, not on the fold's mechanism.
The kit needs 11 parameters. The parameter declarations and the glue
cost about 40 lines. The two sites' shared surface is not big enough
to pay that cost and still reach the floor.

The `Table` triple stays at the site. `Described`'s condition
hypotheses are stated at the top-level triple. The kit's `Step`
parameter is defined inside `Described`. The two cannot both be opened
at the top level. This is a module-order constraint, not a choice.

## 6. WHAT THE GCH WING COULD INSTANTIATE (DD4)

The kit is wing-bearing work. The GCH wing builds a recorded-graph
assembly over a stage. It would open `Assembly` with its own value
property, its own entries predicate, and its own step pair.

The wing's recursion values are sets, like `Table`'s. The wing would
instantiate `P` with its realized-class predicate. It would pass its
`Step` formula and its two step lemmas. It would not re-derive the
approximation induction, the graph pair, or the pair graph.

The kit stays generic in the stage and in the recorded relation. A
later task can revive it from `_build/kits/lj-0.4f-recassembly.lagda.md`
and move it to `src/L/RecAssembly.lagda.md`.

The revival trigger is a third site. The kit pays only when the shared
surface across sites exceeds the kit and the floor. The block refused
the kit on arithmetic. The refusal does not change the DD4 value.

## 7. CONSUMERS RE-VERIFIED

| Consumer | Exit |
|---|---:|
| L/Hierarchy (wired, clone) | 0 |
| L/RecAssembly (kit, clone) | 0 |

The main tree is untouched. No consumer in the main tree changed. The
consumers of `L.Hierarchy` are `Order`, `Before`, `Limit`, `Faithful`,
`Internal`, and `Everything`. They were not re-checked because the fold
was refused at the gate and never landed. The clone's wired `Hierarchy`
checks with exit 0.

## 8. LITERATURE USED

I read `dev/literature/digest.md` section 3 and `dev/literature/j-hierarchy.md`
section 3. The literature treats the hierarchy and the order as two
objects. The canonical well-order is built from the hierarchy, but it
is a separate recursive object. A unified type for the two recorded
objects would be a category error.

The mechanical unification is a different question. The literature does
not address it. The shared assembly is a project-internal device. The
literature cannot decide whether the fold pays. The measurement
decides it.

Why not the rest of the literature: the fold question is about code
shape, not about mathematics. The digest's section 3 is the only
section that bears on it.

## 9. ARCHIVE USED

I read `_build/l3.32-t208-report.md` section 3.6 and lines 316-320. I
took the triplication claim and the named probe. I verified the region
line numbers against the code.

I read `_build/lj-0.8-review.md` sections 7.1 and 7.3. I took the six
standing gates and the probe brief. I applied the gates in the order
they bind.

I read `_build/lj-0.4b-report.md` first. I took the one-site anchor
protocol from lines 13-16 and the seconds protocol from section 3. I
read `_build/lj-0.4e-report.md` for the refused-kit pattern and the
record sign correction.

I read `dev/memos/simplification-register.md` lines 33-38. S13 to S18
do not propose this fold's shape. I did not re-propose them.

I read `dev/LESSONS.md`. P-q sets the seconds expectation to zero. P-r
shapes the fold as a statement-shape share. P-l and P-m set the
parameterized content class. P-m's rate matches the kit's check time.

Why not the rest of the archives: the four archives were surveyed in
the brief. The retired-route records do not bear on this fold.

## 10. WHAT I AM NOT SURE OF

I did not wire `L.Choice.Table`. The standing gates stop the build
before the second site. The Table delta is a projection, not a
measurement. The projection is at the measured per-site rate.

The construction fold is unbuilt. I priced it on the shared skeleton
only. The shared skeleton is about 20 lines per site. The parameter
surface for it is large. I do not have a measured number for it.

The absolute seconds may shift on the new HEAD. The orchestrator
committed the sibling's work while I measured. My three files are
unchanged. The before and after runs share the same clone, so the
delta is internally consistent.

The theoretical pair maximum sits near the floor. Table's whole region
and pair graph are about 176 lines. At zero glue that gives the pair
about minus 64. The realistic surface is about 116, which gives about
minus 4. I did not build the zero-glue case because it contradicts the
measured content structure.
