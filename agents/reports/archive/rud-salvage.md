# Rud salvage inventory (L3.30-S1)

Inventory of what the three built routes offer for salvage under the
prospective rud-functions rebuild, as a checkable catalog. Deliverable of the
`[L3.30-S1]` preparatory task (PLAN row L3.30, `dev/PLAN.md:847`). Read-only
survey of `src/**`, `dev/LESSONS.md`, `dev/memos/L3.29-b-pivot.md`, and
`dev/PLAN.md` row L3.29 (`dev/PLAN.md:846`).

## Method and verdicts

Every entry carries file:line evidence and a measured size: the count of
non-blank lines inside ```agda fences of the cited region, produced with `awk`
over the fences (prose lines, blank lines, and fence markers excluded). Line
numbers are 1-based file lines. Verdicts:

- **reuse-as-is**: the module or region can be imported or copied unchanged;
  nothing in it is basis-specific.
- **reuse-pattern**: the shape, architecture, or discipline transfers, but the
  code re-derives because it is written against the delivered basis (arity
  indexing, certificates, or the operation stock).
- **retire**: no role in the rud design; named and given the reason.

The bins overlap on two files. `L.Godel.Closure` (3,742 Agda lines) holds both
the sat-equation stock claimed in bin B and the level-family heart claimed in
bin C. `L.Godel.Levels` (2,775 Agda lines) holds the determination discipline
claimed in bins B and C and the arity-indexed table machinery retired in bin D.
A module's whole size is reported once in the module table below; the bin
entries cite the regions they claim.

Whole-module Agda sizes measured (non-blank, inside fences):

| module | agda lines |
|---|---:|
| `L.WellOrder.Base` | 349 |
| `L.WellOrder.Tree` | 241 |
| `FOL.Syntax` | 17 |
| `FOL.Semantics` | 31 |
| `FOL.LevyHierarchy` | 32 |
| `FOL.ZFStructure` | 35 |
| `FOL.Manipulation.Relabelling` | 108 |
| `FOL.Coding` | 205 |
| `V.Coding` | 93 |
| `V.Model` (numeral-chain region only) | 49 |
| `L.Definability` | 122 |
| `L.Constructible` | 162 |
| `L.Ordinal` | 116 |
| `L.Stage` | 70 |
| `L.Reflect` | 219 |
| `L.ReflectFo` | 268 |
| `L.Axioms.Basic` | 355 |
| `L.Godel.Tuples` | 153 |
| `L.Godel.Satisfaction` | 527 |
| `L.Godel.Terms` | 214 |
| `L.Godel.InL` | 1,517 |
| `L.Godel.Operations` | 413 |
| `L.Godel.Definable` | 1,032 |
| `L.Godel.Closure` | 3,742 |
| `L.Godel.Levels` | 2,775 |
| `L.Godel.Codes` | 172 |
| `L.Godel.Table` | 1,261 |
| `L.Godel.Tower` | 1,562 |
| `L.Godel.NormalForm` | 199 |
| `L.Godel.Step` | 362 |
| `L.Godel.Name` | 315 |

## The three routes and the design being inventoried

Route 1, the delivered certificate route (option C of D15): the Gödel route
with the certificate architecture and the skeleton order, `L.Godel.{Terms,
Codes, Definable, Table, Tower, InL, Operations, NormalForm, Tuples,
Satisfaction, Name, Step}` plus `L.WellOrder.{Base, Tree}` (PLAN
`dev/PLAN.md:846`, M2 to M5 records; the A-versus-B table at
`dev/memos/L3.29-b-pivot.md:232`). Route 2, the kinded closure tower (option B):
`L.Godel.{Closure, Levels}` on top of the same route-1 stock (PLAN
`dev/PLAN.md:846`, B ledger; ruling at `dev/memos/L3.29-b-pivot.md:244`).
Route 3, the pre-Gödel internalization development on old main: `L.Coding/*`,
`L.Hierarchy`, `L.Ordinal.*`, the satisfaction-internalization chapters, 9,909
non-blank Agda lines in 27 modules by the cone audit
(`dev/memos/L3.29-b-pivot.md:76`).

The rud design the inventory is judged against, taken from the L3.30 row
(`dev/PLAN.md:847`): an untyped rudimentary basis of about nine operations, an
S/J-hierarchy with one operation per step, no arity-indexed tuple calculus, no
kinded slices, no certificate; `Def` keeps its satisfaction definition with the
equivalence as a named theorem; the internal step is an extensionally
determined level table; the order is the stratified producer order on the
S-hierarchy; and a small vocabulary-generic set-model satisfaction module
serves future wings.

## A. Generic infrastructure, likely reusable as-is

### A1. The well-order combinator kit

`src/L/WellOrder/Base.lagda.md`, whole module 349 Agda lines, combinator
section (`## Combinators`, lines 183 to 595) 287.

Evidence: `Tri` at `:87`, the `SWO` bundle at `:108`, `isPropLeastOf` at `:143`,
`leastOf` at `:165`; the kit: `connex` `:199`, `natSWO` `:218`, `unitSWO`
`:241`, `sumSWO` `:312`, `prodSWO` `:369`, `listSWO` `:549`, `pullSWO` `:585`.
The carrier and the relation take separate universe levels (`:108`), so the
bundle is level-generic. The chapter's own prose records that reflection is not
a consumer: "delivered with no order at all" (`:5` to `:9`).

Verdict: **reuse-as-is**. The kit is basis-independent and is the realized half
of the stratified-producer-order design (see C2): `leastOf` is the least-element
search the order's trichotomy and the choice endgame consume, and both route 1
(`L.Godel.Name` imports it at `:50` to `:54`) and the cone (via `Transversal`)
already consume the same interface.

### A2. The FOL vocabulary-generic core

The prospective "small vocabulary-generic set-model satisfaction module" exists
already as a five-file core, all small and all parameterized over the constant
domain and the structure.

- `src/FOL/Syntax.lagda.md`, 17 Agda lines. `Term` at `:41`, `Formula` at
  `:88`; the constant domain `K` is a parameter of both, and the prose at `:73`
  to `:87` states the three instantiations (carrier, parameter-free, restricted
  carrier). Verdict: **reuse-as-is**.
- `src/FOL/Semantics.lagda.md`, 31 Agda lines. Satisfaction is a structural
  recursion over the twelve constructors, generic in the truth algebra and the
  structure (`_⊨_` at `:84` to `:104`), with the constant interpretation fixed
  once in the inner module `At` (`:70`). Verdict: **reuse-as-is**.
- `src/FOL/LevyHierarchy.lagda.md`, 32 Agda lines. The `Δ₀` witness at `:46`,
  `Σ₁`/`Π₁` at `:72`, the alternating `Σₙ`/`Πₙ` tower at `:98`; the data are
  portable across constant domains by construction ("absence is the
  classification", `:33`). Verdict: **reuse-as-is**.
- `src/FOL/ZFStructure.lagda.md`, 35 Agda lines. The structure record at `:42`,
  substructure restriction `_↾_` at `:115`. This is the model interface the
  satisfaction module is parameterized over. Verdict: **reuse-as-is**.
- `src/FOL/Manipulation/Relabelling.lagda.md`, 108 Agda lines. The
  constant-transformation kit: syntax level `mapFo` at `:80`, meaning level
  `⊨-map` at `:137`, Levy-witness level at `:208`. This is the entry map that
  moves formulas between constant domains, including the parameter-free
  formulas into any syntax (`FOL.Syntax.lagda.md:122`). Verdict:
  **reuse-as-is**.

### A3. V-side pairing and numerals machinery

- `src/V/Coding.lagda.md`, 93 Agda lines. Numerals injective: `#mono` `:88`,
  `#-inj` `:106`; Kuratowski pairing: `pr` `:175`, `pr-inj` `:178`; the
  discharged instance `module VCode` at `:231`. The pairing and numeral
  injection are exactly the two parameters `FOL.Coding` asks for
  (`src/FOL/Coding.lagda.md:14` to `:18`). Verdict: **reuse-as-is**.
- `src/V/Model.lagda.md`, numeral-chain region 155 to 244, 49 Agda lines:
  `pair-singleton` `:173`, `numeralV` `:185`, `numeralV≡#` `:189`, the `sucV`
  case analysis `∈sucV-elim` `:218`. These are the library-numeral alignment
  and the successor-membership readings every internal chapter spends. Verdict:
  **reuse-as-is**.

### A4. The reflection-based ZF cone edges the rud route keeps

The cone (the `L ⊨ ZFC` proof) is basis-independent: it speaks through
satisfaction, the tower, and reflection, and never through the internal step.

- `src/L/Definability.lagda.md`, 122 Agda lines. `module DefOf` at `:78`,
  `defSet` `:111`, `Def` `:114`, `defSet-mem` `:150`. This is the
  satisfaction-defined face of `Def` the rud design keeps by ruling
  (PLAN `dev/PLAN.md:847`). Verdict: **reuse-as-is**.
- `src/L/Constructible.lagda.md`, 162 Agda lines. `data isLayer` `:175`,
  `LsetStep` `:215`, `Lset` `:222`, `isL` `:376`, the structure `𝒮ʟ` `:410`.
  The tower over `𝒟` and the class `L` are the cone's own. Verdict:
  **reuse-as-is**.
- `src/L/Ordinal.lagda.md`, 116 Agda lines (`∅-ord` `:77`, `boundingOrd`
  `:154`, `bound2` `:185`, `numeral-ord` `:244`, `#∈ω` `:248`). Verdict:
  **reuse-as-is**.
- `src/L/Stage.lagda.md`, 70 Agda lines (`LeastOrd` at `:91`, `isLeastOrd`
  `:88`, the stage function `:155`). Verdict: **reuse-as-is**.
- `src/L/Reflect.lagda.md`, 219 Agda lines, and `src/L/ReflectFo.lagda.md`,
  268 Agda lines. The reflection theorem chooses a least ordinal, not a least
  element (`src/L/Reflect.lagda.md:16` to `:18`), so it needs no order at all.
  Verdict: **reuse-as-is**.
- `src/L/Axioms/Basic.lagda.md`, 355 Agda lines: `defSet→isL` at `:130`, the
  common-stage provider `isL-directed` at `:385`. These are the
  constructibility door and the stage join every InL-style proof spends.
  Verdict: **reuse-as-is**.

Bin A total: 2,026 Agda lines across the sixteen modules and one region listed.

## B. Meta patterns whose shape transfers but whose code is basis-specific

### B1. The InL definability idiom

`src/L/Godel/InL.lagda.md`, whole module 1,517 Agda lines. The reusable shape
is: stage from `isL-directed` plus the per-argument fiber paths and membership
atoms (`module Stage` at `:98` to `:117`, 13 lines), one defining formula over
the stage, the extensional identification against the operation's laws, and
the `defSet→isL` closer (`:1808` to `:1914`, "Back into the class", 82 lines,
with the uniform closer shape at `:1815` to `:1826`), plus the fixed-stage
climb `mkUp` at `:784`.

Verdict: **reuse-pattern**. The choreography (stage, formula, door, climb)
transfers to every rud operation's constructibility proof; the formulas, the
fiber paths, and the identification are operation-specific and re-derive for
the rud basis.

### B2. The walk module-parameterization discipline

Measured law P-h (`dev/LESSONS.md:171`): a definability walk takes its set
arguments as module parameters, never as function arguments. Instances:
`module SelMem` at `src/L/Godel/InL.lagda.md:409` (region 409 to 527, 109
lines), `module Vals` at `:673` (region 673 to 790, 88 lines), and the closure
chapter's `module ValsWalk` at `src/L/Godel/Closure.lagda.md:2093` (region
2093 to 2179, 83 lines, with `valsWalk` at `:2178`).

Verdict: **reuse-pattern**. The module-parameterization itself is the law and
carries over verbatim; each walk body is an image-specific `defSet` equation
and re-derives with the rud operations.

### B3. Tuples' pair algebra

`src/L/Godel/Tuples.lagda.md`, 153 Agda lines. `suc#-inj` `:68`;
`tuple-extend` `:137`, `tupleTail` `:166`, `tuple-empty` `:210`, the entrywise
injectivity `tuple-entry` `:222`; the all-assignments family `allTuples` `:248`
with its zero and stepping equations `:279` (region 212 to 268, 36 lines).

Verdict: **reuse-pattern**. The graph-of-an-assignment algebra (extension and
shift of the coded tuple against the operations) is generic pair algebra the
set-model satisfaction module still needs. The arity-indexed family
`allTuples` and its stepping equation are the arity-slice reading and retire
with it (D1); the rud level table has no tuple shelves.

### B4. The sat-equation stock

`src/L/Godel/Satisfaction.lagda.md`, 527 Agda lines. `satSet` `:120` with its
two readings `sat-in` `:125` and `sat-out` `:130`; the constructive case
equations `sat-⊥` `:155`, `sat-⊤` `:162`, `sat-∧` `:169`, `sat-∈vv` `:267`,
`sat-∃` `:330`, `sat-≐vv` `:377`, `sat-≐vc` `:440`; the respect lemma with
direction-paired hypotheses `sat-resp` `:535`; the seven reductions `red-∈cv`
`:597` through `red-∀∈` `:669`; the classical cases `sat-⇒` `:704` and
`sat-∀` `:715`; the values bridge `sat-defSet` `:744`. `L.Godel.Closure`
restates a private copy of the same stock (see C1) because "Satisfaction's
tabulation is private, so its stock cannot be reused by import"
(`src/L/Godel/Closure.lagda.md:3899` to `:3901`).

Verdict: **reuse-pattern**. This is the engine behind "Def stays
satisfaction-defined with the equivalence as a theorem" (PLAN
`dev/PLAN.md:847`). The equations change shape under an untyped basis: the
complement bound becomes the previous level, not `allTuples A n`, so the stock
is re-stated, not imported.

### B5. The mirror architecture in Terms

`src/L/Godel/Terms.lagda.md`, 214 Agda lines. The combinator syntax `data KT`
at `:75` (four leaves, four nodes, arity-indexed, declared at an abstract
parameter type per P-e, `dev/LESSONS.md:112`), the mirror formula `toFormula`
`:119`, soundness `sound` `:145`, the packaged equivalence `termDef` `:161`,
`Mirror` `:181`, completeness `mirror` `:304`, and the payoff `termDef≡Def`
`:336`.

Verdict: **reuse-pattern**. The architecture (a term syntax mirroring the
formula constructors, soundness plus completeness, and an extensional
identification making the values of arity-one terms the definable powerset) is
the one-time comprehension-theorem analog, and the rud route needs exactly this
architecture for its own Def-equivalence theorem. The syntax, the mirror, and
the equations are basis-specific and re-derive.

### B6. The extensional-determination junk-exclusion discipline

`src/L/Godel/Levels.lagda.md`, 2,775 Agda lines. The discipline: an internal
object is a finite prefix table described by functionality, base clauses, a
successor clause, and domain adequacy (`PrefixAt` at `:449` to `:458`), and any
satisfying table is pinned into the meta level family by induction on the level
numeral (`prefix-pins` at `:2382`; region 2370 to 2640, 259 lines; the
description and its readers, region 449 to 1277, 783 lines). Prose statement at
`:3030` to `:3073`. Nothing is certified: "functionality plus the base clauses
plus the successor clause determine every entry from the entries below"
(`src/L/Godel/Levels.lagda.md:9` to `:13`).

Verdict: **reuse-pattern**. This is the "extensionally determined level table"
of the rud design (PLAN `dev/PLAN.md:847`). The determination discipline, the
definite-description successor clause, and the pinning induction transfer; the
arity-indexed composite key, the disjuncts, and the combined bound are
basis-specific and re-cast untyped (see C3, C4, D1).

Bin B total: 5,471 Agda lines (whole modules InL 1,517, Tuples 153,
Satisfaction 527, Terms 214; the Closure stock region 285; Levels whole 2,775,
whose full total is split with bins C and D as noted above).

## C. Design artifacts with direct rud analogs

### C1. B's level family and invariant

`src/L/Godel/Closure.lagda.md`. The kinded level family: `data StepTag` `:1119`,
`slice` `:1128`, `step` `:1133`, `StepPayload` `:1137` with per-clause
`slice-in`/`slice-out` laws (section 1064 to 1307, 165 Agda lines); the kinded
invariant `slice-inv` `:4070`, every positive-arity slice member a satisfaction
set by induction on the level (section 3880 to 4213, 285 Agda lines, including
the restated sat-equation stock, B4); terms-to-levels with the computable
witness `levelOf` `:4235` and `terms-in-levels` `:4245` (section 4213 to 4273,
33 lines); the cut theorem `cut-sound` `:4302` and `cut-complete` `:4313`
(section 4273 to 4333, 32 lines).

Verdict: **reuse-pattern**. The level-cumulative closure family with one round
of operation images per level and the invariant-by-level-induction are exactly
the S/J-hierarchy step of the rud design: the shape transfers, the arity
indexing drops (D1), and the invariant becomes "every level member is
definable" without the shelf parameter.

### C2. The stratified producer order design

Recorded in `dev/memos/L3.29-b-pivot.md` §3.2 (`:187` to `:243`): candidate 1,
the stratified producer order, is GO. The level-indexed induction is honest
because producers draw from the previous level (`:190` to `:194`), the least
producer triple exists under LEM by a lexicographic strict well-order (`:192`),
and equal least triples give equal members, so trichotomy follows by pullback
(`:201` to `:211`, stress points s1 and s2). The internal side needs no
certificate: the successor clause is a definite description over the level
tables (`:215` to `:219`). Candidate 2, the skeleton-directed evaluation table,
is NO-GO because it converges back to the certificate (`:222` to `:229`). The
A-versus-B table is at `:232`; the ruling is §4 (`:244` to `:278`); the order
side is re-priced in §5.2 (`:296` to `:313`). The realized meta kit is the
SWO/leastOf half of `L.WellOrder.Base` (A1: `:108`, `:165`, combinators 287
lines).

Verdict: **reuse-pattern**. The rud design's order is candidate 1 re-based to
the untyped rud step: same least-producer comparison, same definite-description
table, no skeleton. The in-scope code realization is the well-order kit (A1);
the order-family and Cond suppliers were never delivered as code.

### C3. The layer guards story

`src/L/Godel/Levels.lagda.md`: the step's layer disjunction over nine operation
images, `LayerAt` at `:262`, with two guards: the values disjunct pins the layer
arity to the zero numeral (`tagValues : StepTag 0`, prose at `:2987` to
`:3030`; guard region 190 to 280, 83 Agda lines), and the extension disjunct
pins its source slot away from zero. The guards exist because the meta step's
images exist only on the shelves the clauses read; both over-descriptions are
refuted by numeral injectivity, "refuted rather than untypeable"
(`:3006` to `:3026`). The two guard defects were caught by the mandated
meta-match table, not by the readers (PLAN `dev/PLAN.md:846`, B4b/B4c ledger;
lesson D-5, `dev/LESSONS.md:860`).

Verdict: **reuse-pattern**. The meta-match-table discipline and the
refuted-not-untypeable guard pattern transfer to the rud internal step's
description; the specific guards are arity artifacts and vanish with the
shelves.

### C4. The prefix-pins statement shape

`src/L/Godel/Levels.lagda.md`: the pinning statement quantifies all keys at
once with a combined bound `n₀ + suc k₀ < b₀` (`prefix-pins` `:2382`; prose
`:3045` to `:3073`), because the successor clause's disjuncts shop on
neighboring shelves and the combined bound stays constant down each of them.
The per-column formulation is uncompileable (lesson R-32,
`dev/LESSONS.md:696`).

Verdict: **reuse-pattern**. The rud level table still needs the all-keys
pinning statement (functionality, base, successor, domain adequacy imply the
meta level family), but with a level-only bound; the arity component of the
combined bound and the shelf-hopping reasoning retire.

Bin C total: 1,144 Agda lines (Closure regions 515, WellOrder/Base combinators
287, Levels guard region 83 and pinning region 259; the memo spans in C2 are
design record, not Agda).

## D. Retires with no rud role

### D1. Arity slices

The kinded, arity-indexed level table and the arity-indexed tuple calculus.
Evidence: `slice A n k` with per-shelf payloads in
`src/L/Godel/Closure.lagda.md` (`StepTag` `:1119`, `slice` `:1128`,
`StepPayload` `:1137`; section 1064 to 1307, 165 Agda lines); the
arity-indexed `allTuples` family and its stepping in
`src/L/Godel/Tuples.lagda.md` (`:248` to `:283`; region 212 to 268, 36 lines);
the arity-carried subterm enumeration in `src/L/Godel/Codes.lagda.md` (`:48` to
`:146`, 68 lines); the arity-indexed prefix table in
`src/L/Godel/Levels.lagda.md` (whole module 2,775 Agda lines, of which the
B6/C3/C4 regions claim 1,125). Why no role: the rud basis is untyped and the
S/J-hierarchy applies operations to the previous level directly; junk is
excluded by extensional determination, not by shelf kinding
(`dev/memos/L3.29-b-pivot.md:215` to `:219`; the cut probe's four junk cases,
`:146` to `:186`, frame the problem the kinding solved).

### D2. Certificates

The certificate cluster, `L.Godel.{Codes, Table, Tower}` (1,995 Agda lines
together: 172 + 1,261 + 1,562; the memo prices the same cluster at "277 +
1,562 + 2,130 file lines", `dev/memos/L3.29-b-pivot.md:315`). Evidence of the
certificate shape: the honest annotation table
(`src/L/Godel/Tower.lagda.md:343`), the packaged omega (`:448`), the
certificate branches (`:558` to `:1198`, 502 lines), the certificate formula
`CertAt` (`:1216` to `:1221`), and the honesty induction (`module Honest`
`:1279`; "the honesty proof recurses on the accessibility", `:89`); the
approximation formula and its family in `src/L/Godel/Table.lagda.md` (`:820` to
`:1144`, 234 lines). Why no role: the rud internal step is a definite
description; "functionality plus the base and successor clauses determine the
table uniquely by meta-induction on the level number"
(`dev/memos/L3.29-b-pivot.md:215` to `:219`), which is exactly the honesty job
the certificate did.

### D3. Codes

Term codes, `src/L/Godel/Codes.lagda.md`, 172 Agda lines: hereditarily finite
tag-and-pair codes over the sealed numeral chain (`:1` to `:22`), the code data
at `:146` (75 lines), discrimination at `:255`. Formula codes,
`src/FOL/Coding.lagda.md`, 205 Agda lines: the `Codes` relation at `:140` and
`⌜⌝-inj` at `:275`. Why no role: under rud, satisfaction stays host-level and
the level table quantifies sets, not coded terms or coded formulas; nothing
inside the model needs formulas as data (PLAN `dev/PLAN.md:847`; the order
probe already found "the deleted `Codes` chapter, unpinnable under route C",
`dev/memos/L3.29-b-pivot.md:225` to `:227`).

### D4. Skeleton order

The skeleton/parameter split naming and its alphabet tree:
`src/L/Godel/Name.lagda.md`, 315 Agda lines (`toTree` `:129`, the two-key order
at `:213` to `:491`, 207 lines, assembled at `:491`; the skeleton/parameter
prose at `:213` to `:228`), and `src/L/WellOrder/Tree.lagda.md`, 241 Agda lines
(`data Tree` `:59`, the shortlex order `:89`). Why no role: candidate 1 "never
mentions skeletons" (`dev/memos/L3.29-b-pivot.md:251` to `:252`); the tree
order "steps aside, and the trees keep only their role as the injectivity
picture" (`src/L/Godel/Name.lagda.md:226` to `:228`), and the rud order
replaces names by producer triples (memo `:296` to `:313`).

### D5. Scaffolds

`src/L/Godel/Step.lagda.md`, 362 Agda lines, is the deliberate parallel
scaffold copy (chapter prose `:1` to `:13`; the spine `birth` `:90`, `byName`
`:213`, `stepAt` `:238`). Why no role: it exists only for route coexistence
under the scaffold-copy pattern (D-3, `dev/LESSONS.md:821`); the rud build
re-implements the naming interface once, against producer triples (memo `:296`
to `:313`), so the copy is retired with the old cluster. The pattern itself is
process, not code, and stays available.

Also retiring with the third route: `src/L/Godel/NormalForm.lagda.md`, 199 Agda
lines, superseded by `Terms.mirror` (`dev/memos/L3.29-b-pivot.md:318`), and the
27-module internalization orphan set, 9,909 non-blank Agda lines per the cone
audit (`dev/memos/L3.29-b-pivot.md:76` to `:109`), which retires in every
variant including rud.

Bin D total, in-scope measured: 4,518 Agda lines (Codes 172, Table 1,261,
Tower 1,562, Name 315, Tree 241, Step 362, NormalForm 199, FOL.Coding 205,
Closure slice region 165, Tuples stepping region 36). The third route's 9,909
lines are the memo's audit figure, not re-measured here.

## E. LESSONS entries that bind a rud rebuild from day one

The entries below shape the architecture or the proof discipline of the rud
build itself, and each is cited at its `dev/LESSONS.md` location.

Performance laws:

- **P-b** (`:52`): the rud operation basis must be union-free at the definition
  level; binds the nine step definitions.
- **P-c** (`:68`): any rud operation or level-table image whose index carries a
  `⋃`-tower is sealed `opaque` at birth; binds the step's index-carrying
  operations.
- **P-d** (`:90`): the rud Def-equivalence and every satisfaction equation
  travel as direction pairs, never as hProp paths; binds the equivalence
  theorem and the successor clause.
- **P-e** (`:112`): syntax or payload data declared at a presentation type is
  declared at an abstract type parameter; binds the vocabulary-generic module
  and any rud term syntax.
- **P-f** (`:132`) and **P-g** (`:151`): at concrete presentation-carrying
  types, transports and congruences are direct path lambdas, never `subst` over
  sigma motives or `cong` with function lambdas; binds every adequacy proof
  over concrete level tables.
- **P-h** (`:171`): definability walks are module-parameterized; binds every
  constructibility walk in the rud closure (B2).

Conversion rules:

- **Rule 1** (`:278`): discharge adequacy substitutions at variable arguments.
- **Rule 2** (`:294`): seal constructions `opaque` at the build site; binds the
  level table and its entries.
- **Rule 3** (`:311`): compute one side of a two-indexed dispatch from the tag;
  binds the untyped step's tag dispatch.
- **Rule 5** (`:340`): frames generic in a constructor or sentence take the
  defining equation as a hypothesis; binds the level-table frames.
- **Rule 8** (`:379`): name the payload type in `PT.rec` over object-language
  existentials.
- **Rule 10** (`:417`): splits concluding in a membership hProp are named
  helpers; binds the order's trichotomy branches.
- **Rule 13** (`:464`): locality; recursion values are defined in the module
  whose telescope binds the parameter; binds the level table and the order
  family.
- **Rule 14** (`:483`): concrete elements at satisfaction slots are sealed;
  binds the constant-atom clauses.
- **R-21** (`:540`) and **R-22** (`:553`): the frame's conclusion type is
  sealed where built, and a computed least name's property is the exported
  least-element predicate; binds the stratified order's `leastName`.
- **R-31** (`:683`): overlapping branch goals are truncated sums; binds the
  untyped step's "old member OR new image" goals.
- **R-32** (`:696`): pin cross-reading tables at all keys at once with a
  combined bound; binds the rud level-table pinning (C4).
- **R-33** (`:712`): pass clause environments as pieces and rebuild them
  concretely; binds the successor-clause readers.

Termination and inference:

- **T-1** (`:727`) and **T-2** (`:742`): nested accessibility nests and the
  transitive-closure accessibility pattern; the stratified order's
  least-producer recursion is the expected consumer.
- **I-1** (`:760`): formula-typed metavariables at mirror call sites are
  passed explicitly; binds the rud Def-equivalence mirror.

Design doctrines:

- **D-1** (`:781`): the probe doctrine; binds every rud milestone.
- **D-2** (`:798`): the junk-table lesson; the four junk cases frame why the
  naive untyped cut fails and where the rud determination discipline must
  answer instead.
- **D-5** (`:860`): readers do not validate a description; the meta-match table
  does; binds the rud internal step's description.
- **D-6** (`:878`): probe prices multiply by three; binds the calibrated
  budget.

Craft lessons that apply but are general hygiene rather than architecture:
C-1 (`:896`), C-2 (`:910`), C-3 (`:924`), C-4 (`:940`), C-5 (`:955`), C-6
(`:969`), C-7 (`:986`), C-8 (`:1001`), C-9 (`:1019`), C-10 (`:1036`), and the
remaining R-series entries (`:566` onward).

### Candidates for lessons the rud design should add

Two recorded facts are not yet in LESSONS and are candidates:

1. The order probe's no-certificate finding: the successor clause of an
   order-family table is a definite description, so functionality plus base and
   successor clauses determine the table by meta-induction
   (`dev/memos/L3.29-b-pivot.md:215` to `:219`). The rud rebuild is the first
   consumer of this as a standing design rule, and a D-series entry stating it
   positively (junk exclusion by extensional determination, not by kinding or
   certificates) would generalize D-2.
2. The B4e walk-transparency datum: the PLAN row records that "the B4e
   walk-transparency datum enters `dev/LESSONS.md` regardless"
   (`dev/PLAN.md:847`), the P-h sibling hypothesis that walk arguments must
   also be abstract (`dev/LESSONS.md:185` to `:186`). It should land as a P-h
   extension once confirmed.

## Totals by bin

| bin | verdict | measured agda lines |
|---|---|---:|
| A. Generic infrastructure | reuse-as-is | 2,026 |
| B. Meta patterns | reuse-pattern | 5,471 |
| C. Design artifacts | reuse-pattern | 1,144 |
| D. Retires | retire | 4,518 (plus the third route's 9,909 per the memo audit) |

Bins B, C, and D are not disjoint: `L.Godel.Levels` (2,775) contributes the
determination discipline to B and C and the arity-indexed table to D;
`L.Godel.Closure` (3,742) contributes the stock region to B, the level-family
heart to C, and the slice region to D. The whole-module sizes are reported
once in the module table; the bin figures are the sums of the region claims as
listed in the entries.
