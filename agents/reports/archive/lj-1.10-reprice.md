# LJ-1.10 re-price: the crossing on today's tree, and the route the wing takes

Status: COMPLETE. Read-only. No tree edit, no git write, no Agda, no make
check. Written incrementally per C-22.

## 1. RECOMMENDATION

**Take the third route. Do not build the bounded satisfaction substrate.
Do not take the cone abstraction fork. Port the archived structural level
story and prove its equivalence against the delivered description.**

The third route is the archived condensation design
(`archive/rud-route/src/L/Condensation.lagda.md`). The plan's own Block 3
already prices it (`_build/lj-1.1-recon.md` section 4, sub-blocks 3a to 3e).
The LJ-1.2 NO-GO does not refute it. The NO-GO refutes one implementation
of the crossing, the direct certification of the delivered description.

The recorded price of 5,047 lines is the price of the coded satisfaction
machine. Today's tree delivers that machine. The bounded substrate is a
fresh layer over it, and it is smaller than 5,047. Section 2 prices it.
The third route does not need it at all. Section 4 explains why.

The wing stays in its booked band on the third route. It grows on the
other two. Section 5 gives the arithmetic.

## 2. CANDIDATE A RE-PRICED

**The recorded price of 5,047 lines is a false anchor for today's tree.**
The figure measures the coded satisfaction machine. The machine is
delivered. The substrate is the bounded formula layer over the machine.
That layer is fresh content. Its price is 1.7 to 3.8 thousand naive
lines.

### 2.1 What the 5,047 measures, and that it stands delivered

The 5,047 is the rud route's `crossing-rebuild` row. T257 re-summed its
four terms at 676 + 1,866 + 2,378 + 127
(`_build/l3.32-t257-routes.md:227-236`). T257 then measured that the
internalization route owns 5,047 of 5,047 of that content
(`_build/l3.32-t257-routes.md:240-263`). The homes are named there:
`Table`, `Slot`, `Sound`, `Unique`, `Closed`, `InL`, `Recover`, `Descent`,
`Model`, `Shape`, the eleven per-conjunct readings, and
`L.Hierarchy:105-356`.

I re-verified the homes on today's tree. The in-fence line counts match
the census. `Model` is 1,289, `Sound` 801, `Unique` 630, `Table` 248,
`Shape` 354, `InL` 330, `Slot` 187, `Closed` 171, `Recover` 190, `Descent`
44, `EnvSet` 229, `Bridge` 294, `CodeSet` 200. `Lset-only` stands at
`src/L/Hierarchy.lagda.md:333`, `Lset-defines` at `:678`. The machine
stands.

The two missing facts also stand, verified at the same sites LJ-1.2
names. `CodesAt` is `extAt c (isCodeAnyAt zero (suc w))`
(`src/L/Choice/Faithful.lagda.md:334-335`). `isCodeAnyAt` carries
`hasWitnessAt`, which has the unbounded existential
(`src/L/Choice/Faithful.lagda.md:287-288`,
`src/L/Coding/CodeSet.lagda.md:250-251`). `satTable` is a meta-level
function to elements of `S`, not an object-level formula
(`src/L/Coding/Table.lagda.md:103-104`). The graph binds index set, table
and carrier with three unbounded existentials
(`src/L/Coding/Graph.lagda.md:104-112`). `atomRel` carries an unbounded
universal (`src/L/Coding/Model.lagda.md:1766-1769`), `propRel` carries two
(`:1073-1077`), `extAt` carries two (`:662-664`).

### 2.2 The D-10 correction

The recorded residue says the substrate is the archived crossing-rebuild
content, measured at 5,047 (`_build/lj-1.2-gate.md:123-126`). The target
is wrong for this tree. The rebuild content is the machine. The machine
stands. The substrate is the bounded object-level description of the code
set and of the twelve-clause table, with adequacy against the machine.
That description is new and unmeasured. T263 records the same shape on
the J side: sixteen fresh bounded clauses, "new and unmeasured"
(`_build/l3.32-t263-fof.md` section 4).

### 2.3 The re-priced band

Basis: survey, with probe-measured per-clause rates.

| component | band (naive) | basis |
|---|---:|---|
| bounded code-set description and adequacy | 0.2-0.5k | survey. The delivered code block is 2,378 in-fence. The bounded face is a fraction of it |
| bounded twelve-clause table and adequacy | 0.7-1.6k | survey. 12 to 16 clause shapes at LJ-1.2's measured 10-23 formula lines each, and the archive's measured decode rate near 40 lines per clause |
| bounded step, approximation, graph, and witnesses | 0.3-0.6k | probe. LJ-1.2 measured the top-level rewrites at 10-11 lines each and the step formula at 23 (`_build/lj-1.2-gate.md:27-45`) |
| equivalence against the delivered machine | 0.3-0.8k | survey. T51's row (c) (`_build/l3.32-t51-report.md:208`) |
| transport certificate (`BoundedFo`) | 0.15-0.30k | survey. R2p's census, 20-40 combinators at 4-8 lines (`_build/l3.31-r2probe-report.md:199`) |
| **Candidate A total** | **1.7-3.8k** | |

The band sits inside the W1p band plus the step bounds. W1p was booked at
1.00-2.55k naive (`_build/l3.31-ivprobe-report.md:478-493`). The NO-GO
re-prices row (b) upward. The deep combinators need bounded rewrites
before certification (`_build/l3.32-t51-report.md:113-119`). The band is
far below 5,047 because the machine stands.

The probe that closes the band: write one bounded table clause with its
Delta-0 witness and its two-way decode, at a stop-line. That measures the
deep rate. The plan should gate the substrate on that probe before
funding it.

## 3. CANDIDATE B RE-PRICED IN FULL

**Candidate B costs 2.45 to 5.1 thousand naive lines in full.** The source
verdict holds: B is comparable to A at the low end, not three times
cheaper, and it is not a saving.

### 3.1 The source's own arithmetic

R2p priced the re-run half at 1.0-1.7k naive. The figure is 68 readings
at 15-25 lines each (`_build/l3.31-r2probe-report.md:200`). R2p flagged
the rest as "C-6-class re-typing across 21 delivered masters"
(`_build/l3.31-r2probe-report.md:133-136`). The ivprobe records the same
line and adds the verdict: "Comparable at the low end, with a larger
blast radius. Carried as a fork, not a saving"
(`_build/l3.31-ivprobe-report.md:488-491`).

The re-typing is the abstraction of the cone over the restriction class.
D-16 prescribed it. The tree did not do it. The cone is monomorphic in
`𝒮ʟ` (`src/L/Coding/Sequence.lagda.md:61-62`).

### 3.2 All 21 masters still exist

The census list is `Sequence`, `Hierarchy`, `Powerset`, `Model`,
`CodeSet`, `Graph`, `Table`, `Slot`, `Sound`, `Unique`, `Bridge`,
`Uniform`, `Sat`, `Recover`, `EnvSet`, `Closed`, `InL`, `Shape`, plus
`Base`, `Environment`, `Descent` (`_build/l3.31-r2probe-report.md:106-120`).
I verified every name on today's tree. `src/L/Coding/` holds 20 masters.
`src/L/Hierarchy.lagda.md` holds the twenty-first. All 21 exist.

The cone measures the same today. The `𝒮ʟ`-bound portion is 6,219
in-fence lines carrying 134 readings. The reusable layer is 576. The
total is 6,795, matching R2p's layer sum of 492 + 400 + 5,327 + 576. The
abstraction sites number 216 (`_build/l3.31-r2probe-report.md:119-122`).

### 3.3 The re-typing price

The re-typing is unmeasured. I price it at 1.2 to 3.0k naive, survey.
The basis is the cone's size: 6,219 in-fence lines, 134 readings, 216
sites. The edits are mechanical. The proof repairs are not. Every proof
that used a constructibility fact must take it as a parameter. Every
consumer of `L.Coding` re-elaborates. That is the blast radius the source
names.

The three reusable masters need no re-typing. The 18 bound masters do.

### 3.4 The full band

| component | band (naive) | basis |
|---|---:|---|
| re-typing across 21 masters | 1.2-3.0k | survey. 18 masters, 6,219 in-fence lines, 216 sites |
| re-run of the readings at a second carrier | 1.0-1.7k | survey. R2p's 68-reading census at the measured rate |
| transport certificate (`BoundedFo`) | 0.15-0.30k | survey. R2p |
| limit case | 0.1k | probe. T261 measured 124 lines closing L-natively (`_build/l3.32-t261-report.md:32-47`) |
| **Candidate B total** | **2.45-5.1k** | |

The equivalence row (c) may be absorbed into the re-run or may stay. If
it stays, add 0.3-0.8k. B does not remove the Levy content by itself.
The reconciliation against the delivered description must carry the
transfers (`_build/l3.32-t51-report.md:113-119`).

The low end of B is comparable to the low end of A. The top of B exceeds
the top of A by about 1.3k. The blast radius is the deciding difference.

## 4. A THIRD ROUTE

**A third route exists. It is the archived structural-story design.**
The wing does not have to certify the level story through the delivered
coded satisfaction. The archived condensation already certifies a
structural story and proves its transfers. What remains is the
equivalence against the delivered description.

### 4.1 What the archive already delivers

The archived chapter builds the parameter-free level story
`levelStory = Ap ∧̇ (Cl ∧̇ Rg)` (`archive/rud-route/src/L/Condensation.lagda.md:600-607`).
The level story has six structural clauses: pair, singleton, zero,
domain, limit, range. Each carries a Delta-0 witness
(`:474-607`). The Def-step entry collapses to `⊤̇`
(`:477-482`, `:598-599`). Every set is definable in itself
(`defSet⊤≡A`, `src/L/Definability.lagda.md:182-183`).

The chapter embeds the story at the set carrier and at the class carrier.
`σᴹ` and `σL` carry Delta-0, Sigma-1 and Pi-1 witnesses
(`:768-776`, `:823-834`). The two readings agree at both carriers by
`abs₀` (`:781-782`, `:839-840`). The transfers for the story hold by
`σ₁-up` and `π₁-down` (`:786-787`, `:845-852`).

The recap names what remains: the crossing's application, the equivalence
with the delivered description, the two factors of the ambient form, and
the limit case (`:865-885`). D32 deleted the crossing section and moved
its obligations to the GCH resume (`:857-861`).

### 4.2 Why the NO-GO does not refute it

The probe certified the delivered description's clauses directly. The
step clause failed because its code and table existentials are unbounded
(`_build/lj-1.2-gate.md:27-45`). The structural story has no such
clauses. Its step entry is `⊤̇`. No code bound and no table bound enter
the story. The NO-GO kills one implementation of the crossing, not the
crossing.

The probe's statement 2, the equivalence, was never reached
(`_build/lj-1.2-gate.md:16-21`). That statement is the third route's
load-bearing leg.

### 4.3 The equivalence is grounded in delivered facts

The equivalence compares two satisfactions at a carrier. Both sides
decode to meta-level statements. The delivered graph theorems give the
coded side: `graphAt-holds` (`src/L/Coding/Powerset.lagda.md:354`),
`graphAt-unique` (`:379`), `DefAt-in` and `DefAt-out` (`:648-666`),
`Lset-only` (`src/L/Hierarchy.lagda.md:333`), `Lset-defines` (`:678`).
The archive's clause decodes give the structural side
(`archive/rud-route/src/L/Condensation.lagda.md:610-746`). No bounded
satisfaction substrate enters.

### 4.4 Price

The crossing stays at its booked band. That band is 700-1,720 naive for
the transfers and the equivalence, and 180-390 for the limit case and
the transport certificate (`_build/lj-1.1-recon.md:140-164`). The story
port is sub-blocks 3a to 3c, already booked at 2,488-2,747 naive. The
equivalence legs are the only unmeasured piece. They are class x3,
survey, per T51's row (c).

The next probe should be one equivalence leg at one carrier. The
stop-line should price row (c). A green gate moves it from x3 to about
x1.3.

## 5. THE WHOLE WING RE-PRICED

The base is LJ-1.1's projection: 8.0 to 10.8 thousand naive lines
(`_build/lj-1.1-recon.md:262-279`). The crossing sits inside it at
700-1,720. Each route replaces that crossing and leaves the rest booked.

| route | crossing (naive) | wing total (naive) | center |
|---|---:|---:|---:|
| A, bounded substrate | 1.7-3.8k | 8.0-13.9k | about 11.0k |
| B, cone abstraction in full | 2.45-5.1k | 8.7-15.2k | about 12.0k |
| C, structural story | 0.7-1.72k | 8.0-10.8k | about 9.4k |

The arithmetic: the wing is the base minus the old crossing plus the new
crossing. Route A low end is 8.0 minus 1.72 plus 1.7, which is 7.98k.
Route A high end is 10.8 minus 0.7 plus 3.8, which is 13.9k. Route B low
end is 8.0 minus 1.72 plus 2.45, which is 8.73k. Route B high end is 10.8
minus 0.7 plus 5.1, which is 15.2k.

The A and B bands are surveys. Their width is the honest uncertainty of
the unmeasured deep layer. The C band is the booked projection, and its
uncertainty lives in the equivalence legs.

**The ceiling does not move.** DD5 keeps the a-priori ceiling at LJ-1.1's
projection (`dev/PLAN.md:163`, measure 1). Route A crosses it. Route B
crosses it. The gap is the finding, not a new ceiling. Route C stays
inside it.

The seconds dimension is untouched. DD24's ratio risk, the square law,
belongs to the counting block. No route change moves it.

## 6. DOES THIS BEAR ON THE ARCHITECTURE

**Yes. The NO-GO is architecture-level evidence, not only a wing-level
pricing finding.** The measurement is the Def tower paying D-26's bill.

### 6.1 The law and the measured fact

D-26 says a stage that carries generation data needs no syntax for a
well-founded key. A definable-power stage carries nothing. Its only key
is the defining formula, which drags in codes, an order on codes, and
satisfaction (`dev/LESSONS.md:1662-1688`). T203 measured both towers:
`Sset (α+1)` holds values of sixteen finitary operations, so a key exists
with no syntax. `Lset (α+1)` is the definable power, so its members carry
no generation data (`dev/ledger.toml:579`, the `retirement-surgery` row).

### 6.2 Where the measured cost comes from

The Def tower's level-hood sentence is `LsetGraphAt`
(`src/L/Coding/Sequence.lagda.md:361-364`). It is written through coded
satisfaction. The coded satisfaction's object-level description is
unbounded at the leaves. The two missing facts from the probe are exactly
that: the code predicate carries an unbounded witness existential, and
the satisfaction table is meta-level, not a formula. Certification then
needs bounded rewrites or a story equivalence. That is the tax the tower
structure imposes.

### 6.3 The J tower pays less

The J-side level story is the structural story with the Def-step
collapsed to `⊤̇` (`archive/rud-route/src/L/Rud/LevelSigma.lagda.md:89-106`).
It is the five-clause assembly `aSt1` with two-way adequacy
(`:598-618`). The kit's clause formulas are not Delta-0 as delivered.
T84 measured that gap. The bounded clause layer is a fresh addition,
priced at 470-610 lines (`_build/l3.32-t84-report.md:30-31`). No code
set and no satisfaction table enter the story. That is the whole
difference.

The D-26 mechanism explains it. The J tower's stage members carry their
generation data. The level-hood description can be structural, and the
op-graph sets are classically Delta-0. T263 records that as a set-level
conditional pass (`_build/l3.32-t263-fof.md:87-96`). The Def tower's
stage members carry nothing. Their level-hood description must go
through codes and satisfaction. The satisfaction leaves are unbounded,
and the probe's two missing facts are exactly those leaves.

### 6.4 Limits of the claim

The J tower is not free. Its equivalence against its delivered
description still needs fresh bounded clauses, priced at 470-610 by T84
and confirmed conditional by T263. The bridge direction, `LsetGraph` at
a J carrier, was itself measured at the 6,219-line cone re-run
(`_build/l3.31-r2probe-report.md:106-122`). The shared costs, the hull,
the collapse and the counting, are the same on both towers. This report
does not re-open DD2's ruling. It gives LJ-2.5 a measurement: the
level-story certification is a few hundred lines on the J tower and a
substrate-scale tax on the Def tower.

## 7. DD4 SCORING

**The structural story wins on DD4. It is the content both proofs share,
written once and embedded at every carrier.**

The story is parameter-free. It lives at the empty constant domain. It
carries no constants, so it means the same at every carrier. `embed` and
`mapΔ₀` carry it and its witnesses to any carrier
(`archive/rud-route/src/L/Condensation.lagda.md:768-787`). The
equivalence legs are the same content at both carriers. The two-tower
route would still want this story. It is the archived condensation core.

Candidate A scores second. The bounded-rewrite technique and the measured
clause rates transfer to both towers. The substrate itself describes
Def-specific content: codes and the coded satisfaction table. The
two-tower route would need it only if the bridge requires the Def cone at
a J carrier. R2p suggests the bridge pays the cone re-run either way
(`_build/l3.31-r2probe-report.md:133-137`).

Candidate B scores lowest for phase 1. It re-types monomorphic content
that already works. It is the D-16 move the two-tower route would want
if the bridge needs satisfaction at a J carrier. The wing should not pay
for it now. The source's own verdict is "carried as a fork, not a
saving" (`_build/l3.31-ivprobe-report.md:490-491`).

The DD4 answer for the two-tower route: the story port is the shared
content. The cone abstraction is a phase-3 decision, priced when the
bridge is funded. The substrate is a Def-only expense.

## 8. ARCHIVE USED

- `archive/rud-route/src/L/Condensation.lagda.md:297-607`: the
  parameter-free structural story, its six clauses and their Delta-0
  witnesses, the collapsed Def step `Cl = ⊤̇` at `:598-599`.
- `archive/rud-route/src/L/Condensation.lagda.md:610-746`: the clause
  decodes at the ambient reading, the structural meta-level reads.
- `archive/rud-route/src/L/Condensation.lagda.md:768-787`: `σᴹ`, its
  witnesses, the two readings' agreement, `level-transfer`.
- `archive/rud-route/src/L/Condensation.lagda.md:823-852`: `σL`, its
  Delta-0, Sigma-1 and Pi-1 witnesses, both transfers.
- `archive/rud-route/src/L/Condensation.lagda.md:857-885`: the D32
  deletion note and the recap naming the remaining obligations.
- `archive/rud-route/src/L/Rud/LevelSigma.lagda.md:89-106`, `:598-618`:
  the J-side story, its collapsed Def step and the five-clause `aSt1`.
- `archive/dev/TASKS-archived.md:86` (`[T51]`), `:165` (`[T130]`),
  `:262` (`[T257]`), `:264` (`[T259]`), `:266` (`[T261]`), `:268`
  (`[T263]`).
- `_build/lj-1.2-gate.md:1-162`: the NO-GO, the per-clause table, the two
  missing facts, the 5.0-5.1k re-price and its candidate names.
- `_build/lj-1.1-recon.md:262-279`: the block table and the 8.0-10.8k
  projection. `:140-164`: sub-blocks 3d and 3e, the crossing bands.
- `_build/l3.32-t51-report.md:52-55`: the four transfer obligations.
  `:201-208`: the W1' rows and row (c). `:113-119`: the red branch and
  Route B's invocation.
- `_build/l3.31-ivprobe-report.md:478-493`: the W1p rows.
  `:488-491`: Route B's original pricing and its verdict.
- `_build/l3.31-r2probe-report.md:106-122`: the cone census, 6,219
  lines, 134 readings, 216 sites. `:133-137`: the two routes and the
  21-master re-typing. `:199-200`: the transport certificate and the
  re-run half.
- `_build/l3.32-t257-routes.md:227-263`: the 5,047 re-sum and the
  ownership measurement.
- `_build/l3.32-t263-fof.md:1-115`: the sixteen-graph pre-gate, its fail
  at the delivered formulas and its set-level conditional pass.
- `_build/l3.32-t84-report.md:30-31`: the kit's Delta-0 gap and the
  470-610 line bounded-clause layer.
- `_build/l3.32-t261-report.md:32-47`: the limit case probe, 124 lines,
  L-native, no bridge facts.
- `dev/LESSONS.md:1271-1336` (D-10), `:1662-1688` (D-26),
  `:1763` (C-6).
- `dev/PLAN.md:161-164` (DD2, DD5), `:164` (DD8), `:173-174` (DD23,
  DD24), `:417-419` (the LJ-1.1, LJ-1.2 and LJ-1.10 rows), `:432`
  (LJ-2.5).
- `dev/ledger.toml:824-856` (the `crossing-rebuild` row and T257's
  correction), `:503-505` (the W1p row), `:2093-2096` (the ownership
  claim).

## 9. WHAT I AM NOT SURE OF

1. The Candidate A band is a survey. The deep clause rate is unmeasured.
   A probe of one bounded table clause with its witness and decode closes
   it.
2. Whether row (c) is absorbed into Candidate B's re-run or stays
   separate. The band includes the possibility.
3. Whether the equivalence legs ride the delivered graph theorems
   directly. The archived decodes must be ported first. Their adaptation
   cost is inside sub-block 3a.
4. Whether `isL (satTable φ)` and `isL (AllCodes A)` are exported. The
   bound terms of Candidate A need them.
5. The T261 limit-case measurement ran against the pre-archival face.
   The port may adjust its 124 lines.
6. The square law's seconds risk is untouched. It is not this task's
   scope.

The one fact I am confident of: the 5,047 anchor prices the machine, and
the machine stands. A re-price that adds it to today's tree double-counts
delivered content.
