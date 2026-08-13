# Independent compression audit: everything outside the Gödel route

Analysis-only. Metric throughout: non-blank lines inside ` ```agda ` fences on
whole masters. Measured on the working tree (25,837 lines at final
measurement; HEAD `a896bf2` is 25,460, matching the prior audit's 25,460; the
two mid-edit files shrank by ~40 lines during this audit as M5a landed). The two mid-edit files
(`L.Godel.Name`, `L.WellOrder.Base`) were read via `git show HEAD:` only, and
their M5a in-flight deltas are attributed explicitly. The post-M7 cone is
computed from the recorded rulings: trophy roots (`Landmarks`, `L.Model`), the
whole Gödel route (`L.Godel.*`, `L.WellOrder.Base`), and the recorded survivors,
with the recorded re-pointings applied (Transversal drops its old `Order`/`Step`
edges; Name drops `WellOrder.Tree` at M5a; one Step copy retires). Every
import edge below was read from the files, not from the documents.

## 1. Verdict summary

The post-M7 orphan total, never counted before, is **9,909** non-blank Agda
lines across 27 modules outside the Gödel route, plus 440 in-route retirements
(`NormalForm`, `Tree`), and the dying cluster additionally leaves roughly
1,800-1,920 lines of dead name surface inside the *surviving* chapters that
only seems alive because the dying cluster imports it. The realistic
cone-compression total is **~1,900-2,140 lines**: delete that residue
(~1,600-1,700), Finite's tally machinery plus Stage's bound residue
(~200-220), the manipulation fold (~60-120), and the recursion unification
(~50-100). Everything else in the surviving cone measured tight: the axioms
chapters already share one frame (`defSet→isL`/`isL-directed`/`mere→uniqueL`,
`Axioms/Basic.lagda.md:130-133, 385-388, 469-470`), absoluteness is stated once
(`FOL.Absoluteness.Single`), and the ordinal/rank and reflection chapters are
load-bearing content with no ≥200-line duplication found. Stacked on the prior
reports' recommended route levers (re-priced −1,035 to −1,345 after M7, since
the Step-copy retirement is already inside the orphan count), the whole tree
lands at **≈12.6-13.7k** non-blank lines from 25,837 today, with the delivered
cone GREEN under every lever except B2/B4, which land only behind the route's
own before-and-after bisect discipline. The one rejected item is the
`DefOf`/`Describes` unification: two description disciplines survive M7, but
they state different things and unifying them churns the definitional base of
the delivered trophy, so it is not a lever.

## 2. Sweep A: the post-M7 orphan analysis

### 2.1 The final cone, computed

Final roots (post-M7 loaded set): the trophy (`Landmarks`, `L.Model`), the
Gödel route (`L.Godel.Operations/Tuples/Satisfaction/Terms/Codes/Definable/
InL/Table/Tower/Name/Step`, `L.WellOrder.Base`), and the recorded survivors
(`L.Choice.Transversal`, `L.Choice.Stage`, `L.Choice.Finite`, `L.Coding.Model`,
`L.Coding.Base`, `L.Coding.Environment`, `L.Coding.InL`, `L.Absoluteness`,
`L.Recursion`). The recorded cuts are applied as edges: `Transversal → {Order,
Step}` re-pointed at the new route's scaffold and M5d Bound assembly
(`dev/PLAN.md:1123`, N3 and M5d rulings); `Name → Tree` cut at M5a
(`PLAN.md:1123`, "slating L.WellOrder.Tree for retirement at M7"); one Step
copy retires (`PLAN.md:1123`). The closure has **58 modules, 15,399 lines**
(ZF cone 37 modules, 4,199 lines; route ex `NormalForm` 7,943 including
`WellOrder.Base` 349; survivors 3,257 full-module), plus the rewired index
`Everything` (89).

The record's dying list (`dev/memos/L3.28-ac-route.md:112`, `PLAN.md:1123`)
verifies against the import graph with four corrections already recorded
elsewhere and re-verified here: `Choice.Finite` survives (M5 ruling, its
`limitOrder` consumed at working-tree `Name.lagda.md:48,550`), `Parameters`
and `Sequence` die (their only consumers are `L.Choice.Name` and the old
cluster, respectively), and exactly one Step copy (`L.Choice.Step`) dies while
`L.Godel.Step` survives. `L.Godel.NormalForm` (199) has zero consumers even
today; `L.WellOrder.Tree` (241) has exactly one, `L.Godel.Name`, which the
M5a re-cut removes.

### 2.2 The module table

Every non-Gödel module, with size (non-blank Agda lines), current consumers
(excluding the catalog importer `Everything`, which today imports all 87
modules and after M7 will import exactly the survivors), post-M7 consumers,
and verdict. Consumers are module-level import edges; "dying" means a consumer
in the 27-module orphan set below.

**ORPHANED at M7: 27 modules, 9,909 lines. Every current consumer retires with
the cluster; post-M7 consumers: none.**

| module | size | current consumers | verdict |
|---|---:|---|---|
| L.Choice.Before | 1114 | Choice.Order | ORPHANED |
| L.Choice.Internal | 817 | Adequate, Limit, Order | ORPHANED |
| L.Coding.Sound | 801 | Internal, Powerset, Uniform, Unique | ORPHANED |
| L.Coding.Unique | 630 | Internal, Powerset, Uniform | ORPHANED |
| L.Choice.Adequate | 573 | Order | ORPHANED |
| L.Choice.Faithful | 521 | Order | ORPHANED |
| L.Choice.Table | 472 | Faithful, Order | ORPHANED |
| L.Choice.Limit | 458 | Before | ORPHANED |
| L.Choice.Name | 410 | Adequate, Internal, Order, Step | ORPHANED |
| L.Coding.Powerset | 400 | Faithful, Order, Sequence | ORPHANED |
| L.Choice.Step | 362 | Faithful, Order, Table, Transversal (edge cut) | ORPHANED |
| L.Choice.Order | 359 | Transversal (edge cut) | ORPHANED |
| L.Coding.Shape | 354 | CodeSet, Recover | ORPHANED |
| L.Hierarchy | 354 | Before, Faithful, Internal, Limit, Order | ORPHANED |
| L.Coding.Bridge | 294 | Adequate, Internal, Name, Powerset, Uniform | ORPHANED |
| L.Coding.Table | 248 | Internal, Powerset, Slot, Sound, Uniform, Unique | ORPHANED |
| L.Coding.EnvSet | 229 | Adequate, Bridge, Sat, Sound, Uniform, Unique | ORPHANED |
| L.Coding.CodeSet | 200 | Adequate, Faithful, Internal, Name, Order, Powerset, Uniform | ORPHANED |
| L.Coding.Recover | 190 | CodeSet, Powerset | ORPHANED |
| L.Coding.Slot | 187 | Internal, Powerset, Uniform | ORPHANED |
| FOL.Manipulation.Parameters | 179 | Choice.Name | ORPHANED |
| L.Coding.Sat | 179 | Adequate, Internal, Bridge, Powerset, Sound, Table, Uniform, Unique | ORPHANED |
| L.Coding.Closed | 171 | CodeSet, Shape | ORPHANED |
| L.Coding.Sequence | 138 | Before, Faithful, Internal, Limit, Order, Hierarchy | ORPHANED |
| L.Coding.Uniform | 126 | Adequate, Internal, Name, Powerset | ORPHANED |
| L.Coding.Graph | 99 | Adequate, Internal, Powerset, Uniform | ORPHANED |
| L.Coding.Descent | 44 | Recover | ORPHANED |

**SURVIVES LOADED: 46 modules plus the index.** Every survivor has at least one
post-M7 consumer; the category "survives as infrastructure nobody loads" is
**empty at module level**, and the reason is stated in §2.3: the "nobody
loads" phenomenon is real but lives at the name level, inside the loaded
survivors.

Landmarks (19 lines) is the entrance, zero-consumer by design, and is loaded
as a root of the cone.

| module | size | post-M7 consumers | still-dying current importers |
|---|---:|---|---|
| L.Coding.Model | 1289 | Transversal, Coding.InL, Godel.Codes/Definable/Table/Tower | Adequate, Before, Faithful, Internal, Limit, Order, Table, Bridge, Closed, CodeSet, EnvSet, InL, Powerset, Recover, Sat, Sequence, Shape, Slot, Sound, Table, Uniform, Unique, Hierarchy |
| L.Choice.Finite | 619 | Godel.Name, Godel.Step | Adequate, Before, Internal, Limit, Name, Step |
| L.Axioms.Basic | 355 | Full, Infinity, Numerals, Power, Separation, Finite, Stage, Transversal, Coding.InL, Godel.InL/Name/Step/Table/Tower, Model, Recursion, ReflectFo | Adequate, Before, Faithful, Internal, Limit, Name, Order, Step, Table, Coding.EnvSet, Powerset, Hierarchy |
| L.Axioms.Separation | 351 | Full, ReflectFo | none |
| L.Coding.Environment | 345 | Coding.InL, Coding.Model, Godel.InL/Satisfaction/Tuples | Adequate, Internal, Bridge, EnvSet, InL, Powerset |
| L.Coding.InL | 330 | Godel.Definable/InL/Table | Closed, CodeSet, EnvSet, Shape, Table, Model |
| V.Model | 285 | Basic, Numerals, Power, Stage, Coding.Environment/InL/Model, Godel.Definable/InL/Name/Operations/Step/Tower/Tuples, Ordinal, Ordinal.Stages, Rank, Landmarks, V.Coding | Faithful, Name, Step, Coding.* cluster |
| L.ReflectFo | 268 | Axioms.Full | none |
| L.Ordinal.Stages | 241 | Infinity, Choice.Stage, Godel.Name/Step/Tower | Faithful, Name, Order, Step |
| L.Reflect | 219 | ReflectFo | none |
| FOL.Coding | 205 | Coding.Model, V.Coding | none (see §2.3) |
| V.Smallness | 192 | Definability, V.Model | none |
| L.Choice.Transversal | 190 | L.Model | none |
| L.Coding.Base | 187 | Coding.Environment, Coding.Model, Godel.Definable/InL | none |
| L.Axioms.Full | 164 | Power, Model, Recursion | Before, Limit, Table, CodeSet, EnvSet, Sat, Hierarchy |
| L.Constructible | 162 | Absoluteness, Basic, Full, Infinity, Numerals, Power, Separation, Finite, Stage, Transversal, Coding.InL/Model, Godel.Codes/Definable/InL/Name/Step/Table/Tower, Model, Ordinal(+Linear/Stages), Rank, Recursion, Reflect/Fo, L.Stage, Landmarks | Adequate, Before, Faithful, Internal, Limit, Name, Order, Step, Table, Bridge, Closed, CodeSet, EnvSet, Graph, Powerset, Recover, Sat, Sequence, Shape, Slot, Sound, Table, Uniform, Unique, Hierarchy |
| L.Choice.Stage | 155 | Transversal, Godel.Step | Faithful, Order, Step |
| L.Definability | 122 | Basic, Separation, Constructible, Godel.InL/Satisfaction/Terms/Tower, Ordinal.Stages | Name, Bridge, Powerset, Uniform |
| L.Ordinal | 116 | Basic, Full, Infinity, Power, Separation, Finite, Stage, Godel.Definable/InL/Name/Step/Tower/Tuples, Ordinal.Linear, Ordinal.Stages, Rank, Recursion, Reflect/Fo | Adequate, Before, Faithful, Internal, Limit, Name, Order, Step, Table, Coding.EnvSet, Shape, Hierarchy |
| FOL.Manipulation.Relabelling | 108 | Bounding, Absoluteness, Separation, Coding.Base/InL/Model, Definability, Godel.InL, Ordinal.Stages | Adequate, Internal, Name, Bridge, Closed, CodeSet, InL, Powerset, Recover, Shape, Uniform |
| L.Recursion | 108 | Godel.Table | Before, Limit, Table, CodeSet, Uniform, Hierarchy |
| FOL.Manipulation.Bounding | 107 | Absoluteness, Separation, Coding.Model, ReflectFo | none |
| FOL.ZFModel | 106 | Basic, Full, Infinity, Numerals, Power, Separation, Transversal, Model, Recursion, Landmarks, V.Model | Before, Table, CodeSet, Hierarchy |
| L.Rank | 101 | Ordinal.Stages | Descent, Recover |
| V.Coding | 93 | Basic, Transversal, Coding.Base/Environment/InL/Model, Godel.Codes/Definable/InL/Name/Operations/Satisfaction/Table/Tower/Tuples, Ordinal | Adequate, Before, Faithful, Internal, Limit, Name, Order, Table, Bridge, Closed, CodeSet, Descent, EnvSet, Graph, Powerset, Recover, Sat, Sequence, Shape, Slot, Sound, Table, Uniform, Unique, Hierarchy |
| FOL.Absoluteness | 87 | Absoluteness, Full, Power, Separation, Transversal, Coding.Model, Definability, Godel.Definable/Table/Tower, Recursion, Reflect/Fo | Adequate, Before, Faithful, Internal, Limit, Order, Table, Bridge, Closed, CodeSet, EnvSet, Graph, Powerset, Recover, Sat, Sequence, Shape, Slot, Sound, Uniform, Unique, Hierarchy |
| L.Axioms.Numerals | 86 | Infinity, Coding.InL/Model, Godel.Codes/Definable/InL/Table/Tower, Model | CodeSet, EnvSet, Recover, Shape, Slot, Sound, Table, Uniform, Unique |
| Base.Choice | 84 | Landmarks, V.Model | none |
| L.Axioms.Power | 79 | L.Model | none |
| L.Ordinal.Linear | 77 | Godel.Step, Ordinal.Stages, L.Stage | Faithful, Step |
| FOL.Manipulation.Relativize | 76 | Full, ReflectFo | none |
| L.Stage | 70 | Full, Power, Separation, Choice.Stage, Godel.Step, Recursion, Reflect | Before, Faithful, Step, Coding.EnvSet |
| FOL.Manipulation.Renaming | 67 | Full, Godel.Satisfaction, Godel.Terms | NormalForm (in-route, deleted) |
| Base.Classical | 59 | Base.Choice, Full, Infinity, Power, Separation, Finite, Stage, Transversal, Godel.Name/Satisfaction/Step/Table/Terms/Tower, Model, Ordinal.Linear, Ordinal.Stages, Recursion, Reflect/Fo, L.Stage, WellOrder.Base, Landmarks, V.Model | Adequate, Before, Faithful, Internal, Limit, Name, Order, Step, Table, Coding.Bridge/CodeSet/EnvSet/Graph/Powerset/Sat/Sequence/Slot/Sound/Table/Uniform/Unique, Hierarchy |
| V.Hierarchy | 44 | Absoluteness, Basic, Full, Power, Separation, Finite, Stage, Transversal, Coding.Base/Environment/Model, Constructible, Definability, Godel.Definable/InL/Name/Operations/Satisfaction/Step/Table/Terms/Tower/Tuples, Ordinal(+Linear/Stages), Rank, Recursion, Reflect/Fo, L.Stage, Landmarks, V.Coding, V.Model, V.Smallness | Adequate, Before, Faithful, Internal, Limit, Name, Order, Step, Table, Bridge, Closed, CodeSet, Descent, EnvSet, Graph, Powerset, Recover, Sat, Sequence, Shape, Slot, Sound, Table, Uniform, Unique, Hierarchy |
| L.Axioms.Infinity | 36 | L.Model | Before, Internal, Limit, CodeSet |
| FOL.ZFStructure | 35 | FOL.Absoluteness/Coding/Manipulation.*/Semantics/ZFModel, L.Absoluteness, Basic, Full, Infinity, Numerals, Power, Separation, Finite, Stage, Transversal, Coding.InL/Model, Constructible, Definability, Godel.Codes/Definable/Name/Step/Table/Tower, Model, Ordinal(+Linear/Stages), Rank, Recursion, Reflect/Fo, L.Stage, V.Coding, V.Hierarchy, V.Model, V.Smallness | Adequate, Before, Faithful, Internal, Limit, Name, Order, Step, Table, Bridge, Closed, CodeSet, Descent, EnvSet, Graph, Powerset, Recover, Sat, Sequence, Shape, Slot, Sound, Table, Uniform, Unique, Hierarchy |
| L.Model | 35 | Landmarks | none |
| L.Absoluteness | 34 | Coding.Model | none |
| FOL.LevyHierarchy | 32 | FOL.Absoluteness, Bounding, Relabelling, Relativize, L.Absoluteness, Full, Separation, Coding.Base/Environment, Definability, Godel.InL, Ordinal.Stages, V.Smallness | Coding.Base (old), Environment (old), Name, Adequate, Internal, Limit, Order, Table, Bridge, Closed, CodeSet, EnvSet, Graph, Powerset, Recover, Sat, Sequence, Shape, Slot, Sound, Uniform, Unique, Hierarchy |
| FOL.Semantics | 31 | FOL.Absoluteness, Relabelling, Relativize, Renaming, ZFModel, L.Absoluteness, Separation, Coding.Base/Environment, Godel.InL, V.Model, V.Smallness | Parameters, Name, Bridge |
| Base.Prelude / Base.Truth | 28 / 28 | every surviving module (shared leaves) | all dying modules |
| FOL.Syntax | 17 | every surviving module except Landmarks/Model/Operations (shared leaf) | all dying modules |
| Base.Impredicativity | 14 | Classical, Power, Landmarks, V.Model, V.Smallness | none |
| Landmarks | 19 | none (entrance, zero-consumer by design) | none |
| Everything | 89 | index; rewired at M7 to import the survivors | n/a |

### 2.3 The attention items, answered from the graph

**`FOL.Manipulation.*` after M7.** Renaming survives: `L.Axioms.Full` swaps two
variables for the model record's replacement order (`Full.lagda.md:109-117`),
and the route's `Terms`/`Satisfaction` use `renameTm` for the bounded-composite
constructions (`Terms.lagda.md:284-301`). Relabelling survives as the cone's
constant-replacement workhorse (`mapFo`/`⊨-map`, consumed by Definability,
Separation, Ordinal.Stages, the route's `Godel.InL`, and the coding survivors).
Relativize survives as the reflection engine (`Correct`/`relativize` at
`ReflectFo.lagda.md:48`, `Full.lagda.md:151,288`). Bounding survives as the Δ₀
certificate layer (Separation, L.Absoluteness, ReflectFo, Coding.Model).
**Parameters dies**: its only consumer is `L.Choice.Name`
(`FOL/Manipulation/Parameters.lagda.md`, import graph), one of the 27 orphans;
179 lines.

**`FOL.Coding` and `V.Coding`'s `VCode`.** The final tree consumes **zero**
formula-coding names: `VCode`, `LCode`, `codeBridge`, `⌜_⌝`, and `⌜_⌝ᵗ` occur
nowhere in `L/Godel/*` (whole-tree grep), and the ZF cone consumes none either.
`FOL.Coding` is 205 lines; its formula-specific content (`⌜_⌝`/`⌜_⌝ᵗ` codes,
the `Codes` relation, and the decode direction,
`FOL/Coding.lagda.md:90-139, 140-273, 275-end`) is 182 of them, with no
post-M7 consumer at any level. The module survives only because `V.Coding`
instantiates it on one line (`V/Coding.lagda.md:231`) and the surviving
`Coding.Model`/`Base`/`InL` import it for sections that retire. `V.Coding`
itself (93 lines) survives for the pairing and numerals (`pr`, `pr-inj`,
`#_`, `#-inj′`, plus `#mono` consumed by `Godel.Definable`), which the route
uses at nine sites (`Codes.lagda.md:24`, `Tower.lagda.md:35`,
`Table.lagda.md:33`, `Tuples.lagda.md:33`, and five more); the formula-coding
machinery beyond that surface, `VCode` included, is dead post-M7. The old
route coded formulas; the Gödel route codes terms as raw pair-chains, and
nothing left standing reads a formula code.

**Reflection and rank.** `L.Rank` (101) has exactly one post-M7 consumer,
`L.Ordinal.Stages`; it is load-bearing for the delivered **Infinity** axiom
(`ord∈Lset-suc` consumed at `Axioms/Infinity.lagda.md:24,67`) and for the
route (`Tower.lagda.md:430`, `Name.lagda.md:50`, `Step.lagda.md:34`).
`L.Reflect` (219) feeds only `L.ReflectFo` (268), which feeds only
`L.Axioms.Full` (`mkReflect` at `Full.lagda.md:55,151,288`); Full supplies the
model record's separation/replacement fields (`Full.lagda.md:144, 277`;
consumed at `Model.lagda.md:40-41`) and Power's separation
(`hasSeparationL` at `Axioms/Power.lagda.md:60,192`). So the reflection pair
is load-bearing for a delivered axiom (Power) and for the trophy
`L⊨ZFC`; neither is free-standing, and no duplication between them was found
(ReflectFo reuses Reflect's ladder and Single frames by import, not by copy).

**"Survives as infrastructure nobody loads".** The category is empty at module
level: `L.Absoluteness` is loaded by `Coding.Model`, `L.Recursion` by
`Godel.Table`, `Coding.Base`/`Environment`/`InL` by the route's own imports,
`Choice.Stage`/`Finite` by `Godel.Step`/`Name`/`Transversal`. The phenomenon is
real only at the name level, and it is quantified in Sweep B: the loaded
survivors carry ~1,800-1,920 lines that no final consumer references.

**Sum.** 27 orphaned modules: **9,909 lines**. In-route retirements:
`NormalForm` 199 (zero consumers even now) and `Tree` 241. Full-module total
retired at M7: **10,349 lines** (29 modules, plus the index rewire), against a whole tree
of 25,837. This is the largest single retirement in the tree and it has never
been counted at module granularity; the memo's "dies ≈ 11,950"
(`L3.28-ac-route.md:112`) and the prior audit's "≈12,138 gross / ≈11,663 net"
were bucket estimates on a looser metric that also folded in the partial
survivors' dead halves, which this audit instead counts separately below.

## 3. Sweep B: structural compression inside the surviving cone

Levers are listed largest first. Risk classes: (a) mechanical, (b) re-prove
same statements, (c) statement or interface change with a consumer list,
(d) touches a measured performance law (`PLAN.md:1122-1123`, memo §9).

### B1. Delete the formula-coding residue inside the survivors: ~1,600-1,700 lines, risk (b)/(c)

**Mechanism.** Delete names with zero post-M7 consumers from the modules that
survive: `FOL.Coding`'s formula side (182 of 205 lines), `V.Coding`'s `VCode`
instantiation (`V/Coding.lagda.md:231`), and the formula-reading halves of the
four coding survivors. The consumed surfaces are small and verified:
`Coding.Model` contributes the ~11 names the route imports (`prʟ`, `prAtL`,
`appAt`, `sucAtL`, `numL`, `extAt`, `envOverAt`, `svAt`, `domAt`,
`valuesInAt`, `pairsInAt`; `Godel/Definable.lagda.md:45-49`,
`Godel/Codes.lagda.md:27`) plus `appAt`/`appAt-adequate` for Transversal
(`Choice/Transversal.lagda.md:64`); `Coding.Base` contributes
`∈pair-introL/R` (`Godel/Definable.lagda.md:44`); `Coding.InL` contributes
`sglL` (`Godel/Definable.lagda.md:53`, `Godel/Table.lagda.md:60`,
`Godel/InL.lagda.md:43`); `Coding.Environment` contributes `env`/`cons`/
`lookup-spec`/`sucAt-adequate` (`Godel/Tuples.lagda.md:36`,
`Godel/Satisfaction.lagda.md:40`, `Godel/InL.lagda.md:42`).

**Measured sizes.** `FOL.Coding` formula side 182; `Coding.Model` dead half
~850 (prior audit measured the surviving surface at ~425/1,289,
`_build/deep-levers.md` §2); `Coding.InL` ~300 of 330 (dead = everything past
`sglL`, sections `InL.lagda.md:195-226` and 320-end); `Coding.Base` ~130-150
of 187 (AllCodes and the meta pair/readers/adequacy machinery, sections
`Base.lagda.md:75-114, 179-380`); `Coding.Environment` ~150-200 of 345
(quantifier, sequence, and extension machinery, sections
`Environment.lagda.md:167-233, 396-547`); `V.Coding` ~1-2. Sum:
**~1,600-1,700**.

**Honest saving.** Same. **Risk.** (b)/(c): pure deletion of zero-consumer
names, but the boundary inside `Coding.Model` is not typechecker-verified: the
~11 surviving names' transitive dependencies inside the module are unmeasured,
so the deletion must land as a bisect (delete a section, re-check the route).
**Verdict: pursue, first.** Decisive reason: it converts Sweep A's "only
seems alive" finding into lines at zero statement risk, and it is the only
≥500-line lever in the surviving tree.

### B2. Finite's tally machinery plus Stage's bound residue: ~200-220 lines, risk (c)

**Mechanism.** Delete the dead half of the recorded survivor `L.Choice.Finite`
and the flagged dead names in `L.Choice.Stage`. Post-M7 consumers of Finite
are `Godel.Name` (`Limit`, `inSome`, `limitOrder`; worktree `Name.lagda.md:48,
550`) and `Godel.Step` (`Tri-map`; `Step.lagda.md:38`); the tally family
(Tallies, splitting, masks, sub-family selection, truth-to-bit, definable
subsets of a tallied stage, `Finite.lagda.md:96-436`) served the old order
cluster and is unreferenced by either consumer. The PLAN survey already flagged
`Finite`'s `stageOrder`/`natOrder` and `Stage`'s `Lset-μ` plus the three
`bound-*` at zero consumers (`PLAN.md:1122`).

**Measured sizes.** Finite's tally family: 176 non-blank lines (96-129: 6,
129-168: 17, 168-212: 20, 212-293: 52, 293-323: 9, 323-436: 72). Stage's
dead names: ~20-40. Sum **~200-220**. **Risk.** (c): the reachability of the
tally sections from the limitOrder spine (`finiteStage`/`before`) is a
dependency question a bisect must settle before deletion. **Verdict: pursue
behind that bisect.** Decisive reason: zero-consumer content in a module that
otherwise stays green.

### B3. One fold for the surviving `FOL.Manipulation` chapters: ~60-120 lines, risk (c)

**Mechanism.** The PLAN survey's lever (e), re-priced on the post-M7 set:
`Renaming` (67), `Relabelling` (108), `Relativize` (76), `Bounding` (107)
hand-walk the `Formula`/`Term` syntax (358 surviving lines; Parameters 179
dies). A shared fold covers the traversals; the correctness lemmas mostly do
not share, per the survey's own note (`PLAN.md:1122`, lever (e)).
**Honest saving.** ~60-120, not the recorded 120-200. **Risk.** (c) plus the
seal discipline: the fold must take unsealed bodies and never name a sealed
description (P-c, `PLAN.md:1123`). **Verdict: marginal; land only if B1/B2
land.** Decisive reason: the traversals are ~third of the priced mass, and the
rest is per-chapter correctness that does not share.

### B4. `L.Recursion` against the route's recursion assembly: ~50-100 lines, risk (d)

**Mechanism.** The survey's triplication lever (f), post-M7 residue.
`L.Recursion` (108) survives with exactly one consumer, `L.Godel.Table`
(`Table.lagda.md:31, 1506-1507`), which uses `Recursion`/`mereFunct`/`Of`
alongside its own bespoke `Describes`-based approximation assembly. The other
two copies of the shape (Hierarchy, Choice.Table, Before; ~1,141 lines) die at
M7, so the remaining question is one consumer against one generic module.
The prior audit capped the unification at −150-250 (`_build/deep-levers.md`
L4); the post-M7 honest residue is ~50-100. **Risk.** (d): rule 13 measured
that abstraction over the recursion's value is not the cure (>400 s with the
order a module parameter, `PLAN.md:1122`). **Verdict: pursue only behind a
before/after bisect.** Decisive reason: 108 lines of infrastructure for one
consumer justify folding the generic into the site, but the wall class is
measured, not speculative.

### Rejected and measured-not-a-lever

**Reject: unify `DefOf` and the route's `Describes`.** After M7 two description
disciplines coexist: `L.Definability.DefOf` defines the definable powerset
(`Definability.lagda.md:108-141`, `defSet`/`Def`, consumed per formula by the
axioms at `Basic.lagda.md:130-133`, Separation at `Separation.lagda.md:119+`,
and named by the trophy's `𝒮ʟ`) and `Godel.Definable.Describes` identifies a
slot's set with a target through an extension formula
(`Godel/Definable.lagda.md:108-141`). They state different things: subset
carving at one binder, versus slot identification in an environment of
parameters. Unifying them means re-baseing `𝒟ₒ` or re-writing the route's
clauses, which is the deep-levers L6 rejection (`deep-levers.md` §5, L6).
**Verdict: reject.** Decisive reason: the satisfaction-side `defSet` is the
delivered definitional base, and the equivalence as a theorem already costs
~55 lines.

**Measured, not a lever: the axioms-chapter ceremony.** The shared frame
already exists: `defSet→isL` (`Basic.lagda.md:130-133`), `isL-directed`
(385-388), `uniqueL`/`mere→uniqueL` (469-470), and the per-axiom residue is
genuine content: empty 19 (474-515), pairing 64 (515-639, of which the
`pair∈𝒟ₒ` carve is ~35), union 68 (639-736, dominated by the `defSet≡`
extensionality), Separation's sealed five-step bridge `AtStage` 84
(`Separation.lagda.md:119-260`) plus the 12-clause stage-finding recursion 71
(394-494), Full 164, Power 79. The only measurable ceremony is the
`module XOf` close (Q/build/mere→uniqueL) repeated at Basic:617-635,
657-732 and the `bound2` merge repeated six times inside `mkBoundedFo`
(`Separation.lagda.md:437-489`); honest total ~60-90, below the 200-line bar.
Absoluteness is likewise stated once (`FOL.Absoluteness.Single`,
`FOL/Absoluteness.lagda.md:55-100`) with `L.Absoluteness.transferFo` as the
one transfer (`L/Absoluteness.lagda.md:87-93`) and per-chapter uses as
one-liners, not re-derivations. The ordinal/rank cluster (Ordinal 116, Linear
77, Stages 241, Rank 101) measured tight: `Linear`'s `ord-tri` is consumed at
`Stages.lagda.md:139` and `Godel/Step.lagda.md:34`; Stages' comparison pair
(76-173) and rank direction (173-272) are consumers of Rank, not copies of it.

## 4. Combined landing arithmetic

All figures are non-blank Agda lines, my metric, working tree. The prior
reports' lever set (L2 dead code −360, L3 unionK −180-250, L8 Step copy −362,
L1 compression bundle −695-935) is re-stacked with L8 already inside the M7
retirement and L2 reduced to its in-route residue, so nothing is counted
twice.

| step | delta | running total |
|---|---:|---:|
| whole tree today (worktree; HEAD 25,460) | — | 25,837 |
| M7 retirement: 27 orphans (9,909) + NormalForm (199) + Tree (241) | −10,349 | 15,488 |
| Sweep B1 (formula-coding residue in survivors) | −1,600 to −1,700 | 13,788-13,888 |
| Sweep B2 (Finite tally + Stage residue) | −200 to −220 | 13,588-13,668 |
| M5-internal still unbuilt (M5b/M5c/M5d + glue, recorded `PLAN.md:1123`) | +550 to +1,150 | 14,138-14,818 |
| prior route levers, post-M7: L2 residue (product/memberGraph ~160) + L3 unionK (−180-250) + L1 bundle (−695-935) | −1,035 to −1,345 | 12,793-13,783 |
| Sweep B3 (manipulation fold) + B4 (recursion unification) | −110 to −220 | **≈12,573-13,673** |

**Post-compression landing: ≈12.6-13.7k non-blank lines**, against the prior
audit's 13.1-13.7k on the same metric. The difference is honest: the prior
reports folded the Model/InL residue into "net of partial survivors" without
pricing it, and this audit's B2/B3/B4 add ~310-440 it did not count. The
plan's own tripwire is stated on its looser "code-line" metric (16.5k
post-compression, `PLAN.md:1123`); on that convention the landing reads
~14.0-15.2k. If the skeleton-order internalization cannot fit the recorded M5
budget (the prior audit's decisive ruling, `deep-levers.md` §5), add
+1,000-1,600: **≈13.6-15.3k** on this metric.

## 5. What cannot be determined without ruling or prototyping

1. **B1's exact boundary inside `L.Coding.Model`.** Whether the ~11 consumed
   names transitively depend on the formula-reading sections (connectives,
   subcode domains, code bridges) is a typechecker question; the ~850 dead-line
   figure is the prior audit's measured estimate (425/1,289 surviving surface),
   not a verified deletion.
2. **B2's reachability question.** Whether Finite's tally sections
   (96-436) are reachable from the limitOrder spine (`finiteStage`/`before`)
   needs a dependency trace or a deletion bisect; the consumer list
   (`Name`: Limit/inSome/limitOrder; `Step`: Tri-map) says no, the code's
   internal edges are unverified.
3. **B4's wall class.** Whether folding `L.Recursion`'s generic machinery into
   `Godel.Table` survives rule 13 (module-parameterized recursion >400 s); the
   route's own method requires a before/after bisect, and no Agda runs were
   allowed for this audit.
4. **B3's seal boundary.** Whether a shared manipulation fold can be written
   without naming sealed descriptions (P-c), and at what cold-time cost.
5. **The M5-internal budget.** Whether M5b/M5c/M5d fit the recorded 550-1,150
   (the deep-levers ruling); if the skeleton order's internal side needs a
   Limit/Before-class recursion, the floor moves +1,000-1,600 and the landing
   becomes ≈13.6-15.3k.
6. **The M5a state of the two mid-edit files.** This audit read
   `L.Godel.Name` and `L.WellOrder.Base` at HEAD per the brief; the post-M7
   cone assumes the recorded M5a re-cut (Name drops Tree and consumes
   `limitOrder`; Base gains the list combinator). If the working-tree re-cut
   ships differently, the Finite/WellOrder.Base rows move by tens of lines,
   not hundreds.
7. **Metric reconciliation.** Chapter-level "code-line" figures in the records
   run ~10-12% above the non-blank count used here (the prior audit measured
   the same gap); the landing band above is this audit's metric, and the
   plan's 16.5k tripwire reads on its own convention.
