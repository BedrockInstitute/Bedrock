# GCH design audit: does the tree read as designed, or as engineered?

Status: COMPLETE. Read-only audit at `f7314af`, branch `two-tower-bridge`.
Method: code and book first, history second, per the brief. Evidence is
`file:line`. No `agda` run. This report is ASD-STE100.

## 1. THE VERDICT

**Engineered into shape, with the seams honest but visible.** The
mathematical core is sound and mostly natural: the Mostowski collapse
(`src/V/Collapse.lagda.md`), the Skolem hull on a meta term algebra
(`src/L/Hull.lagda.md`), the formula count (`src/FOL/Count.lagda.md`) and
the square-law collapse (`src/L/Ordinal/SquareLaw.lagda.md`) would each
pass a set theorist's reading alone. But the assembly does not read as one
design. Half of the largest master has no consumer
(`src/L/Condensation.lagda.md:2479-5071`); a superseded first draft of one
table row stands beside its replacement with a lemma that glues them
(`:106-260` beside `:1405-1444`, glued at `:3883`); the central theorems
are conditional on four module hypotheses, one of which demands strictly
more than the tree can prove (`sq`); and the two file names cross: the
file named `Condensation` holds no condensation statement, and the
condensation theorem lives in the file named `BoundedSubset`. A reader who
knows Devlin II.5 will recognize every step. The same reader will ask
"why is it laid out like this?" at least eight times, and for five of
those questions the answer is an accident of the build order, not a
decision.

## 2. WHAT A READER WOULD ASK "WHY IS IT LIKE THIS?" ABOUT

Ranked by how much the reader's understanding improves per unit of
change. For each item: the question, the answer from the record, and
whether the answer is a decision or a patch.

### 2.1 Why does the twelve-row table exist twice, with 2,500 lines of glue?

The satisfaction clauses exist in the machine's spelling
(`memClauseAt`, `eqClauseAt`, ... imported at
`src/L/Condensation.lagda.md:29-46` from `L.Coding.Model`) and again in a
bounded "story" spelling (`Bot` through `Exist`,
`src/L/Condensation.lagda.md:1116-1444`). Row agreements reconcile the two
(`:2479-5071`). Each agreement carries ten to twenty site-fact
hypotheses; `ImpAgree` alone takes fifteen (`:4891-4927`).

The book's counterpart is one paragraph: Devlin binds the unbounded
quantifiers of `D(v,u)` by the concrete set `K(u)` and notes the meaning
does not change (`dev2.txt:593-630`, digest
`dev/literature/devlin-II5.md:246-255`). So a bounded restatement is
genuine mathematics, not an artifact. What has no counterpart in the book
is the SIZE of the reconciliation: each of twelve rows needs its own
two-way proof against the machine, under a wall of carrier-closure
hypotheses.

The record explains the size: the machine's clauses were written before
this route with unbounded quantifiers, and the project's own law now says
"where the story is yours to write, write it in the machine's spelling
from the start" (P-v, `dev/LESSONS.md:3037-3045`; measured 499x at this
site). The agreement layer is the price of NOT owning the machine's
spelling. **Verdict: the bounded table is right; the agreement layer is a
patch on the machine's spelling.** The ideal form rewrites the
`L.Coding.Model` clauses bounded (one spelling), which deletes most of
the agreement layer. DD13 applies: plan that from the rewrite side; the
2,500 lines already paid decide nothing.

### 2.2 Why does block 1 survive beside the Exist row?

`module Clause` (`src/L/Condensation.lagda.md:106-260`) is the bounded
existential clause. `module Exist` (`:1405-1444`) is the same clause in
the generic frame family; the file's own comment says so ("block 1's
clause at the generic layout", `:1403-1404`). `ClauseAgree` (`:3876-3929`)
proves the machine's clause against block 1's matrix by instantiating the
Exist agreement. Block 1's own deliverables `existCertAt`, `Σ₁-cert`,
`ClauseDecode` and `CertTransfer` (`:255-259`, `:304`, `:398`) have no
consumer: `L.BoundedSubset` imports only `DefBodyB`, `Δ₀-DefBodyB` and
`GraphB` (`src/L/BoundedSubset.lagda.md:29-32`), and no other master
imports `L.Condensation` at all.

History: block 1 was `[LJ-1.5]`'s first delivery; the generic rows came
with `[LJ-1.37]`/`[LJ-1.40]` (`dev/PLAN.md` task index rows). **Verdict:
patch.** A fresh writer writes the Exist row once and instantiates it.
The ideal form archives block 1 and its decode; nothing in the delivered
chain moves.

### 2.3 Why is the condensation theorem conditional on `levelIn` and `cover`?

`Condense` takes both as module parameters
(`src/L/BoundedSubset.lagda.md:597-601`), and `Devlin55`'s `Co` threads
them through to `theorem` (`:1090-1093`, `:1271-1272`). They are the
level-hood transfer, Devlin's (h) and (n)-(p): the heart of 5.2's proof
(digest section 2.3). The comment above `HullStage` says so plainly
(`:576-583`), and the record prices the residue (`[LJ-1.7]` row: "levelIn
and cover are HYPOTHESES: the semantic transfer is assumed";
`_build/lj-1.48-report.md` measures the skeleton around them). **Verdict:
debt, honestly labeled.** See section 5.

### 2.4 Why does `sq` demand what the tree cannot prove?

`L.StageCardinal` takes the square law at EVERY infinite ordinal as its
module parameter (`src/L/StageCardinal.lagda.md:14-17`), and `Devlin55`
repeats that shape (`src/L/BoundedSubset.lagda.md:1045-1046`). The
delivered square law proves it only at `Init` ordinals
(`src/L/Ordinal/SquareLaw.lagda.md:692-698`, `via-col-square` at
`:959-961`), and `via-col-square` has zero consumers. The induction in
`Upper.stage-card-upper` consumes `sq` at every infinite ordinal below
the target (`src/L/StageCardinal.lagda.md:657-662` through `limit-step`
at `:497-504`), including non-initial ordinals such as `ω + ω`, where
`Init` fails by construction.

The record knows: `[LJ-1.21]` chose the every-infinite shape "because it
was convenient" (D-30, `dev/LESSONS.md:3255-3280`), and
`_build/lj-1.47-report.md:86-112` names both the mismatch and the cure:
restate the level size as a fixed-target theorem, `⟪ Lset β ⟫ ↪ ⟪ κ ⟫`
for every `β ≤ κ`, with every square-law call at the initial `κ`.
**Verdict: the socket is a patch; the cure is already on the record and
not yet built.** This is also the one place where the tree's statement is
at the WRONG generality in the brief's sense: the per-ordinal injection
form is stronger than Devlin 1.1(vii)'s consumer needs, and the surplus
is exactly what cannot be proved.

### 2.5 Why does half of the biggest file do nothing?

The row agreements (`src/L/Condensation.lagda.md:2479-5071`) have no
consumer in the delivered tree. The assembly probe consumed only
`GraphB`, `DefBodyB` and the certificates, and "never opens the row
agreement modules" (`_build/lj-1.48-report.md:60-64`). The agreements are
staged for the `levelIn`/`cover` discharge, which will need the bounded
graph to agree with the machine's `LsetGraphAt` (`ride-only` at `:408`).
The repository's own law says a block with no consumer is untested
(C-35, `dev/LESSONS.md:3123`), and this exact table was once false of its
own machine while green (`[LJ-1.37]`, C-35's measured episode).
**Verdict: right mathematics, staged; but a reader cannot tell the load-
bearing half of the file from the stockpile.** A section comment naming
the future consumer would fix the reading at zero code cost; DD23 does
not block code comments.

### 2.6 Why is Devlin 5.1 proved and then not used?

`TV-thm`, the Tarski-Vaught equivalence at a set carrier inside a stage,
is delivered (`src/L/Hull.lagda.md:174-181`, `:306-307`) and consumed by
nothing. `DownReflect` instead takes `ElemDown`, the downward half, as a
bare hypothesis (`src/L/BoundedSubset.lagda.md:406-410`). The missing
glue is the bridge from formulas over `Code` to formulas over the hull
carrier (`_build/lj-1.46-report.md:83-91`, priced at about 120 lines).
**Verdict: debt.** The engine exists; the belt between the engine and the
wheel does not. A reader sees 5.1 proved as an ornament.

### 2.7 Why do 28 de Bruijn indices arrive as module parameters?

`LevelHood` takes twelve row tags, two term slots, and their doubles at a
second arity, every one a `Fin` parameter
(`src/L/BoundedSubset.lagda.md:70-101`), and instantiates `DefBodyB`
twice with hand-written `suc`-towers five and seven deep. The same wall
pattern repeats in every `Δ₀` certificate (for example
`src/L/Condensation.lagda.md:2240-2273`).

The record shows this is a measured house style, not an accident: slots
as parameters keep every formula constant-free, so the erase route to the
parameter-free axis is `refl` (P-u, `dev/LESSONS.md:2908`;
`[LJ-1.39]` measured de-padding), and satisfaction-level renaming is the
alternative that P-v priced at 499x. **Verdict: right, but it looks
wrong.** The cost is real: the reader must verify index arithmetic by
eye, and index arithmetic not machine-checked is exactly what D-29 calls
a residue (`dev/LESSONS.md:3195-3199`). Named offset helpers (`lift5`,
`lift7` for the two frame depths) would keep the measured behavior and
delete the towers from the page.

### 2.8 Why are there two cardinal notions, and no bridge?

`IsCardinal κ` is "κ injects into no member"
(`src/L/BoundedSubset.lagda.md:729-730`). `Init α` adds `ω ∈ α`,
successor closure, and "the index injects into no infinite member's
SQUARE" (`src/L/Ordinal/SquareLaw.lagda.md:692-698`). No lemma connects
them. The record knows: "`Init κ` must be verified for each cardinal, or
`Init` adopted as the cardinal notion"
(`_build/lj-1.47-report.md:111-112`). **Verdict: debt, known.** A set
theorist reads `Init`'s fourth clause and asks where it comes from; the
honest answer is "it is what the exclusion chase consumes", which is a
consumer's shape leaking into a definition.

### 2.9 Smaller questions, one line each

- `Σ₂ : Formula CS.S 1` carries the certificate `Σ₁-Σ₂ : Σ₁ Σ₂`
  (`src/L/BoundedSubset.lagda.md:537-541`): a formula named after a Levy
  class it does not belong to. Rename.
- `LevelHood0.reverse` (`:546-551`) is defined and never consumed.
- `OrderAt`/`OrderAtom`/`OrderAtStage` and the atom `φ<`
  (`src/L/Hull.lagda.md:433-524`, about 90 lines) have zero consumers;
  DD27 removed the definable well-order from the chain
  (`dev/PLAN.md` DD27), and this is its orphaned remainder. Archive it.
- `Collapse.Inj` (`src/V/Collapse.lagda.md:118-214`) duplicates
  `InjExt` (`:220-312`) almost line for line, and only `InjExt` is
  consumed (`src/L/BoundedSubset.lagda.md:319`, `:743`). The keep was a
  ruling (`[LJ-1.13]` row, D-27), but the ideal form derives `Inj` from
  `InjExt` in a few lines: for a transitive carrier, global
  extensionality yields `isExt`.
- Duplicated small mathematics: `CodeCount`
  (`src/L/BoundedSubset.lagda.md:1108-1209`) re-plays the
  pair/numeral/tuple injectivity dance of `Bound`
  (`src/L/StageCardinal.lagda.md:94-175`) including a re-proved
  `code-stable`; `OrdSWO` (`src/L/StageCardinal.lagda.md:228-264`)
  duplicates the inline ordinal SWO of
  `src/L/Ordinal/SquareLaw.lagda.md:146-178`; `_↪_` and `comp-inj` are
  each defined twice (`src/L/BoundedSubset.lagda.md:726`, `:1058`;
  `src/L/StageCardinal.lagda.md:221`, `:601`); `dne` twice
  (`src/L/Hull.lagda.md:229`, `src/L/StageCardinal.lagda.md:517`).

## 3. THE THREE VERDICTS APPLIED

### 3.1 Right, and it looks right

- **The Mostowski collapse** (`src/V/Collapse.lagda.md`). By
  ∈-recursion, with the uniqueness law (`:314-332`) and Devlin 5.2(ii)
  as `fixes` (`:334-380`). The comments name the book. This is the
  cleanest master in the subject.
- **The hull as a meta term algebra** (`src/L/Hull.lagda.md:56-142`).
  Codes are base points plus least-witness constructors; `val` searches
  the meta well-order; `closed` is the Skolem-closure step. This is
  Jech's Skolem-function presentation of Devlin 5.3, and the module is
  generic in the structure, the order and the junk, which is DD4 kept
  honestly. The `junk` split and `sum-stuck` (`:97-108`) are
  formalization artifacts a reader will accept.
- **Tarski-Vaught** (`src/L/Hull.lagda.md:174-307`): Devlin 5.1 at the
  right generality (any subset of a stage, both directions).
- **The formula count** (`src/FOL/Count.lagda.md`): square pairing,
  constructor codes, `Match`/`peel` injectivity. Standard and tight.
- **Hull extensionality** (`src/L/BoundedSubset.lagda.md:917-1040`):
  the difference-formula witness through `hull-closed` is exactly
  Devlin's step A (extensionality from one Σ₁ reflection, digest 2.1)
  transplanted to the criterion. The long comment (`:905-916`) says so.
- **The level size** (`src/L/StageCardinal.lagda.md`): 1.1(vii)'s upper
  half by ∈-induction with a real ω-base (`fin-inj`, `:589-591`) and a
  generic union step. The injection form (no bijections) is the honest
  constructive reading. The statement's TARGET is wrong (section 2.4),
  but the proof's architecture is right.
- **The square-law collapse** (`src/L/Ordinal/SquareLaw.lagda.md`): the
  Gödel pairing by collapsing the max-lex order and excluding escape by
  trichotomy. The header prose states the `Init` restriction and its
  reason before the code does (`:13-17`).

### 3.2 Right, but it looks wrong

- **The slot-parameter house style** (section 2.7). Measured and
  correct; unreadable at the call sites. Named lifts would cure the
  page without touching the measurement.
- **The bounded story table itself** (`src/L/Condensation.lagda.md:
  419-1444`). A Σ₁-with-Δ₀-matrix restatement of the Def step is
  exactly what Devlin's engine requires (digest 2.8). It reads as
  machinery because the frame family (`unFullAt`, `binFullAt`, ...) is
  five layouts deep; a two-line comment per frame naming the Devlin
  clause it restates would carry a reader through.
- **The staged agreement layer** (section 2.5): right content, no
  consumer yet, no signpost saying who will consume it.
- **`Devlin55`'s name** (`src/L/BoundedSubset.lagda.md:1044`). The
  module states 5.5's statement shape, but under four hypotheses. The
  name promises the book's theorem; the type delivers a conditional. An
  honest header comment listing the four debts would remove the sting.
- **`Collapse.Inj` kept beside `InjExt`** (section 2.9): a ruled keep,
  but the derivation of one from the other is missing, so it reads as
  copy-paste.

### 3.3 A patch

Each with the ideal form and the DD13 note.

1. **The machine's unbounded spelling, and the agreement layer it
   forces** (section 2.1). Ideal form: the coding layer's clauses
   bounded from birth, one spelling; the agreements shrink to
   instantiations. DD13 applies: price the rewrite of `L.Coding.Model`'s
   clause layer fresh; the agreement layer's sunk 2,500 lines argue
   nothing.
2. **Block 1 beside the Exist row** (section 2.2). Ideal form: one
   Exist row; block 1 and its decode archived. Cheap, self-contained.
3. **The `sq` socket at every infinite ordinal** (section 2.4). Ideal
   form: the fixed-target level size at `κ`, already specified at
   `_build/lj-1.47-report.md:97-106`. DD13 applies to `StageCardinal`'s
   induction shape.
4. **The orphaned order atom** (`src/L/Hull.lagda.md:433-524`). Ideal
   form: archive; DD27 removed its consumer class.
5. **The dead names**: `LevelHood0.reverse`, `existCertAt`, `Σ₁-cert`,
   `ClauseDecode`, `CertTransfer`, `Collapse.Inj`,
   `LevelHood0.Σ₂`'s name. Each is one small deletion or rename.

## 4. THE MODULE STRUCTURE

**The split does not follow the mathematics, and the names do not tell
the truth.**

- `src/L/Condensation.lagda.md` holds no condensation statement. Its
  content is Devlin II.2.2-2.7: the bounded description of the Def step
  and the level graph, plus its adequacy against the machine. Its honest
  name is a level-formula or level-certificate module.
- `src/L/BoundedSubset.lagda.md` holds THREE chapters: the Σ₁ level-hood
  formula and its transfer skeleton (sections 1-4A, `:61-551`), the
  condensation theorem (`Condense.condenses`, `:704-715`), and Devlin
  5.5 (`:1044-1272`). The first chapter belongs beside the engine; the
  second IS the condensation lemma and should carry that name; the
  third is the only content the file's name describes.
- The boundary is a build accident: the engine file is `[LJ-1.5]`'s and
  `[LJ-1.37]`-`[LJ-1.45]`'s dispatch series; the theorem file is
  `[LJ-1.7]`'s. The mathematics would put the certificate with the
  engine, the theorem under the theorem's name, and 5.5 where it is.
- What IS right: `V.Collapse`, `FOL.Count`, `L.Hull`,
  `L.Ordinal.SquareLaw`, `L.Ordinal.StageArith` and `V.Presentation`
  each hold one mathematical object, correctly named, at the right
  layer (the collapse and the count are V-level and FOL-level, not
  L-level, and that placement is the DD4-honest one: the J tower
  consumes them unchanged).
- A rename plus a one-cut re-split is import churn, not mathematics,
  and DD23 does not freeze module names. It is the cheapest large
  legibility win in the subject after the signpost comments.

## 5. THE SURVIVING HYPOTHESES, ONE BY ONE

| hypothesis | site | debt or design | basis |
|---|---|---|---|
| `levelIn` | `src/L/BoundedSubset.lagda.md:598` | **DEBT** | It stands for Devlin's (h)-(i) leg: the collapse contains every level at its own ordinals. The digest (2.3) shows the book proves this; the tree assumes it. The record prices it as the residue (`[LJ-1.7]`, `[LJ-1.48]`). Not a parametrization: no second instance exists or is planned. |
| `cover` | `src/L/BoundedSubset.lagda.md:599-600` | **DEBT** | Devlin's (n)-(p) leg, same status. |
| `ElemDown` | `src/L/BoundedSubset.lagda.md:406-410` | **DEBT** | Devlin 5.3's content. The engine (`TV-thm`) is delivered; the Code-to-carrier bridge is owed (`_build/lj-1.46-report.md:83-91`). |
| `sq` | `src/L/StageCardinal.lagda.md:14-17`, `src/L/BoundedSubset.lagda.md:1045-1046` | **DEBT, and mis-shaped** | The only hypothesis that demands MORE than the mathematics: every-infinite-ordinal pairing, where the book needs cardinal-site pairing and the tree proves `Init`-site pairing. Section 2.4. |
| `hotel` | `src/L/BoundedSubset.lagda.md:1047-1048` | **DEBT** | The one-point absorption `⟪Lset α ∪ {x}⟫ ↪ ⟪Lset α⟫`. Real content of 5.5's counting; surveyed at 40-80 lines (`_build/lj-1.46-report.md:354-355`), unbuilt. |
| `lem` | every master | **DESIGN** | The classical frame, declared once at each module head. Genuine parametrization. |
| `TermAlgebra`'s `𝒮`, `wo`, `junk`, `emb` | `src/L/Hull.lagda.md:58-62` | **DESIGN** | The genuine two-tower parametrization; the J tower instantiates the same core. This is DD4 done right. |
| `IsoInv`'s seven collapse facts | `src/L/BoundedSubset.lagda.md:148-159` | **DESIGN** | Generic iso-invariance, instantiated at once by `CollapseIso` (`:317-346`). The hypothesis list is the theorem's honest interface. |
| `LimitStep`'s `D`, `inv` | `src/L/StageCardinal.lagda.md:379-382` | **DESIGN** | Abstracting the definability operator for the union step; instantiated immediately at `:497-504`. |

The pattern: the parametrizations that are design are instantiated
within a page of their declaration. The debts are instantiated nowhere.
That is the test a reader can apply without the record.

## 6. WHAT I WOULD WRITE INSTEAD, FOR THE WORST ITEM

The worst item is 3.3.1: the two-spelling table and its agreement layer.

Concretely: `L.Coding.Model` states each satisfaction clause with the
machine's unbounded quantifiers, and `L.Condensation` restates all
twelve bounded, then proves twelve two-way agreements under site-fact
walls. I would instead make the BOUNDED form the only form:

1. Define one clause former, `clauseAt : (frame data) → Formula S m`,
   in the coding layer, with the bound `K` a slot from birth, exactly as
   `extAtB` and `envSetB` already do
   (`src/L/Condensation.lagda.md:89-95`, `:553-559`).
2. Prove ONE lemma, once: at a carrier that contains its own `K`-bound
   witnesses (the closure facts the agreements now take as fifteen
   hypotheses, stated once as one record), the bounded clause and the
   unbounded clause agree. This is Devlin's own single remark
   (`dev2.txt:593-630`), and it is one lemma about `extAtB` against
   `extAt`, not twelve.
3. Let the recursion (`LsetGraphAt`) consume the bounded clauses
   directly, so `ride-only`/`ride-defines` (`:408-417`) hold of the
   bounded graph with no translation.

The delivered `PropAgree`/`EnvSet`/`AtomLeaf` modules show the authors
converging on this themselves: each is "one generic transfer, N
instantiations". The step not taken is moving the generic transfer to
the definition site, which deletes the transfer. The record's own P-v
states the principle; the tree applies it inside `L.Condensation` but
not across the module boundary where it matters most.

Priced honestly: this is a rewrite of the coding layer's clause family
plus re-checking its consumers, against the deletion of roughly half of
`L.Condensation`. I did not price it and it needs its own gate; DD13
says to price the ideal form fresh, and that is what a rewrite brief
should do.

## 7. WHAT I COULD NOT JUDGE

1. **Whether the agreements are exactly the lemmas the `levelIn`/`cover`
   discharge will need.** That wiring does not exist yet. If the
   discharge needs only one direction per row, half of each agreement is
   surplus; I cannot tell without building it.
2. **Whether the slot-parameter style beats named-lift helpers on
   seconds.** P-u and `[LJ-1.39]` measured neighboring questions, not
   this one. My 2.7 recommendation is legibility-only until measured.
3. **The J tower's real reuse of the "template" modules.** The DD4
   annotations (`TermAlgebra`, `IsoInv`, `EraseTransfer`, `prodSWO`)
   claim tower-genericity. No J-side consumer exists in the tree, so
   the claim is untested in C-35's sense. I read the types as generic;
   I could not verify a second instantiation.
4. **Whether `Formula`'s `∀̇∈`/`∃̇∈` primitives make the Δ₀ class
   match Devlin's Σ₀.** The digest itself flags the convention question
   (`dev/literature/devlin-II5.md:616-619`). Settling it needs a read
   of `FOL.LevyHierarchy` against the book's I.9, outside this
   subject's file list.
5. **Anything that requires running Agda**: no rate, no profile, no
   typecheck claim in this report is mine; every figure cited is the
   record's.

## ARCHIVE USED

- `dev/PLAN.md` task index rows `[LJ-1.1]` to `[LJ-1.48]` and DD27:
  took the build order, the hull re-index ruling, and the residue
  statuses.
- `dev/LESSONS.md`: P-u (`:2908`), P-v (`:3037`), C-35 (`:3123`),
  D-29 (`:3165`), C-36 (`:3207`), D-30 (`:3255`), D-27 (`:1703`),
  R-36 (`:808`), R-38 (`:829`): took the measured reasons behind the
  house style, the false-table episode, and the consumer doctrine.
- `_build/lj-1.46-report.md` (`:83-91`, `:340-355`),
  `_build/lj-1.47-report.md` (`:86-112`),
  `_build/lj-1.48-report.md` (`:40-72`): took the residue prices, the
  `sq` mismatch and its named cure, and the assembly's consumption
  list.
- `dev/literature/devlin-II5.md` in full, as the book reference; spot
  checks against `_build/literature/dev2.txt` citations therein.
